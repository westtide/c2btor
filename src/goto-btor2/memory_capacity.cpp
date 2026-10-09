#include "memory_capacity.h"

#include <util/arith_tools.h>
#include <util/bitvector_expr.h>
#include <util/bitvector_types.h>
#include <util/c_types.h>
#include <util/config.h>
#include <util/find_symbols.h>
#include <util/pointer_expr.h>
#include <util/pointer_offset_size.h>
#include <util/std_expr.h>
#include <util/symbol.h>

#include "btor2_type_utils.h"

#include <algorithm>
#include <deque>
#include <optional>
#include <set>
#include <vector>

namespace
{
struct ranget
{
  mp_integer lower, upper;
  bool operator==(const ranget &other) const
  {
    return lower == other.lower && upper == other.upper;
  }
};
struct statet
{
  bool reachable = false;
  // Missing entries mean the full range of the symbol's machine type.
  std::map<exprt, ranget> values;
};

// Forward integer intervals over the final (inlined/lowered) CFG. Joins take
// the union; expanding back edges widen to the full machine range. Guards and
// existing assumes only narrow reachable states. Unsupported operations lose
// precision, never reachable inputs. The result sizes backing storage only;
// runtime object size/lifetime and validity checks stay in heap_modelt.
class capacity_analysist
{
  const namespacet &ns;
  std::set<irep_idt> escaped;

  std::optional<ranget> type_range(const typet &original) const
  {
    const auto type = follow_tag_type(original, ns);
    if(type.id() == ID_bool)
      return ranget{0, 1};
    // C _Bool has a target-sized byte representation in the memory model.
    // Unknown/aliased reads must cover those bits, not assume normalization.
    if(
      type.id() != ID_signedbv && type.id() != ID_unsignedbv &&
      type.id() != ID_c_enum && type.id() != ID_c_bool)
      return {};
    if(type.id() == ID_c_enum)
      return type_range(to_c_enum_type(type).underlying_type());
    const auto width = to_bitvector_type(type).get_width();
    if(type.id() == ID_signedbv)
      return ranget{
        -(mp_integer(1) << (width - 1)), (mp_integer(1) << (width - 1)) - 1};
    return ranget{0, (mp_integer(1) << width) - 1};
  }

  static irep_idt root_id(const exprt &location)
  {
    const exprt *root = &location;
    while(root->id() == ID_member || root->id() == ID_index ||
          root->id() == ID_object_size || root->id() == ID_pointer_offset)
      root = &root->operands()[0];
    return root->id() == ID_symbol ? to_symbol_expr(*root).get_identifier()
                                   : irep_idt{};
  }

  void forget(statet &state, const irep_idt &id) const
  {
    for(auto it = state.values.begin(); it != state.values.end();)
      if(root_id(it->first) == id)
        it = state.values.erase(it);
      else
        ++it;
  }

  void put(statet &state, const exprt &location, const ranget &value) const
  {
    const auto full = type_range(location.type());
    if(!full || value == *full)
      state.values.erase(location);
    else
      state.values.insert_or_assign(location, value);
  }

  // Singleton arithmetic uses CBMC's machine representation, including wrap.
  // Non-singleton arithmetic is mathematical only when the interval fits;
  // otherwise use the full range, never the unwrapped endpoints.
  std::optional<ranget> fit(const ranget &value, const typet &type) const
  {
    const auto full = type_range(type);
    if(!full)
      return {};
    if(value.lower >= full->lower && value.upper <= full->upper)
      return value;
    if(value.lower == value.upper)
    {
      const auto constant = from_integer(value.lower, type);
      if(const auto folded = numeric_cast<mp_integer>(constant))
        return ranget{*folded, *folded};
    }
    return full;
  }

  void find_escaped(const exprt &expr)
  {
    if(expr.id() == ID_address_of)
    {
      const exprt *root = &expr.operands()[0];
      while(root->id() == ID_index || root->id() == ID_member)
        root = &root->operands()[0];
      if(root->id() == ID_symbol)
        escaped.insert(to_symbol_expr(*root).get_identifier());
    }
    for(const auto &op : expr.operands())
      find_escaped(op);
  }

  void havoc_memory(statet &state) const
  {
    // Aggregate roots always live in byte memory, including roots without an
    // explicit address_of. Unknown pointer stores must forget their fields.
    // Non-address-taken scalar locals remain independent of byte memory.
    for(auto it = state.values.begin(); it != state.values.end();)
    {
      const symbolt *symbol;
      const bool found = !ns.lookup(root_id(it->first), symbol);
      const auto type = found ? follow_tag_type(symbol->type, ns) : typet{};
      if(
        escaped.count(root_id(it->first)) ||
        (found && symbol->is_static_lifetime) || type.id() == ID_struct ||
        type.id() == ID_union || type.id() == ID_array)
        it = state.values.erase(it);
      else
        ++it;
    }
  }

  exprt measure(const exprt &pointer, bool size) const
  {
    return size ? exprt(object_size_exprt(pointer, size_type()))
                : exprt(pointer_offset_exprt(
                    pointer, signedbv_typet(config.ansi_c.pointer_width)));
  }

  std::optional<ranget>
  pointer_measure(const exprt &raw, const statet &state, bool size) const
  {
    const auto pointer = simplify_expr(raw, ns);
    const auto known = state.values.find(measure(pointer, size));
    if(known != state.values.end())
      return known->second;
    if(
      pointer.id() == ID_typecast &&
      pointer.operands()[0].type().id() == ID_pointer)
      return pointer_measure(pointer.operands()[0], state, size);
    if(
      pointer.id() == ID_side_effect &&
      pointer.get(ID_statement) == ID_allocate)
      return size ? evaluate(pointer.operands()[0], state)
                  : std::optional<ranget>{{0, 0}};
    if(pointer.id() == ID_address_of)
    {
      if(!size)
        if(
          const auto offset = compute_pointer_offset(pointer.operands()[0], ns))
          return ranget{*offset, *offset};
      const exprt *root = &pointer.operands()[0];
      bool base = true;
      while(root->id() == ID_member || root->id() == ID_index)
      {
        // A zero index preserves the base offset; other subobject offsets
        // require layout/stride information and are conservatively unknown.
        base = base && root->id() == ID_index && root->operands()[1].is_zero();
        root = &root->operands()[0];
      }
      if(root->id() == ID_dereference)
        return size ? pointer_measure(root->operands()[0], state, true)
                    : std::optional<ranget>{};
      if(root->id() == ID_symbol)
      {
        if(!size)
          return base ? std::optional<ranget>{{0, 0}} : std::optional<ranget>{};
        const auto bytes = size_of_expr(root->type(), ns);
        return bytes ? evaluate(*bytes, state) : std::optional<ranget>{};
      }
    }
    if(pointer.id() == ID_plus || pointer.id() == ID_minus)
      for(const auto &op : pointer.operands())
        if(op.type().id() == ID_pointer)
        {
          if(size)
            return pointer_measure(op, state, true);
          auto off = pointer_measure(op, state, false);
          const auto stride =
            pointer_offset_size(to_pointer_type(op.type()).base_type(), ns);
          if(!off || !stride || *stride <= 0)
            return {};
          // C pointer arithmetic scales by the pointee's target layout.
          // Overflow loses precision through fit(), just like integer sizes.
          for(const auto &index : pointer.operands())
            if(index.type().id() != ID_pointer)
            {
              const auto value = evaluate(index, state);
              if(!value)
                return {};
              off = pointer.id() == ID_plus
                      ? fit(
                          {off->lower + value->lower * *stride,
                           off->upper + value->upper * *stride},
                          measure(pointer, false).type())
                      : fit(
                          {off->lower - value->upper * *stride,
                           off->upper - value->lower * *stride},
                          measure(pointer, false).type());
            }
          return off;
        }
    return {};
  }

  void assign(statet &state, const exprt &raw_lhs, const exprt &rhs) const
  {
    const exprt *lhs = &raw_lhs;
    // A store to &x is exact. General pointer stores still havoc escaped roots.
    if(lhs->id() == ID_dereference && lhs->operands()[0].id() == ID_address_of)
    {
      const auto &object = lhs->operands()[0].operands()[0];
      if(object.type() == lhs->type())
        lhs = &object;
    }
    if(lhs->id() != ID_symbol && lhs->id() != ID_member)
    {
      havoc_memory(state);
      return;
    }
    const auto type = follow_tag_type(lhs->type(), ns);
    if(type.id() == ID_pointer)
    {
      // Allocation extents and base offsets are latched with pointer values,
      // including copies/casts. This bounds OBJECT_SIZE in copy/realloc IR.
      const auto bytes = pointer_measure(rhs, state, true),
                 offset = pointer_measure(rhs, state, false);
      forget(state, root_id(*lhs));
      const bool union_member =
        lhs->id() == ID_member &&
        follow_tag_type(to_member_expr(*lhs).compound().type(), ns).id() !=
          ID_struct;
      if(!union_member)
      {
        if(bytes)
          put(state, measure(*lhs, true), *bytes);
        if(offset)
          put(state, measure(*lhs, false), *offset);
      }
    }
    else if(type.id() == ID_struct)
    {
      std::vector<std::pair<exprt, ranget>> fields;
      for(const auto &component : to_struct_type(type).components())
      {
        const member_exprt source(rhs, component.get_name(), component.type());
        if(const auto value = evaluate(source, state))
          fields.emplace_back(
            member_exprt(*lhs, component.get_name(), component.type()), *value);
      }
      forget(state, root_id(*lhs));
      for(const auto &field : fields)
        put(state, field.first, field.second);
    }
    else if(type.id() == ID_union)
      forget(state, root_id(*lhs));
    else
    {
      const auto value = evaluate(rhs, state);
      if(lhs->id() == ID_symbol)
        forget(state, root_id(*lhs));
      // Union field writes can affect every other field; do not track them.
      if(
        lhs->id() == ID_member &&
        follow_tag_type(to_member_expr(*lhs).compound().type(), ns).id() !=
          ID_struct)
        forget(state, root_id(*lhs));
      else if(value)
        put(state, *lhs, *fit(*value, lhs->type()));
      else
        state.values.erase(*lhs);
    }
  }

public:
  explicit capacity_analysist(const namespacet &ns) : ns(ns)
  {
  }

  std::optional<ranget> evaluate(const exprt &raw, const statet &state) const
  {
    const auto expr = simplify_expr(raw, ns);
    const auto full = type_range(expr.type());
    if(!full)
      return {};
    if(expr.id() == ID_object_size || expr.id() == ID_pointer_offset)
    {
      const auto value =
        pointer_measure(expr.operands()[0], state, expr.id() == ID_object_size);
      return value ? fit(*value, expr.type()) : full;
    }
    if(expr.is_true() || expr.is_false())
      return ranget{expr.is_true() ? 1 : 0, expr.is_true() ? 1 : 0};
    if(expr.id() == ID_constant)
    {
      mp_integer value;
      if(!to_integer(to_constant_expr(expr), value))
        return ranget{value, value};
    }
    if(expr.id() == ID_symbol || expr.id() == ID_member)
    {
      const auto it = state.values.find(expr);
      if(it != state.values.end())
        return it->second;
      if(expr.id() == ID_symbol)
        return full;
      const auto &member = to_member_expr(expr);
      const auto &compound = member.compound();
      const auto compound_type = follow_tag_type(compound.type(), ns);
      if(compound_type.id() != ID_struct)
        return full;
      const auto &components = to_struct_type(compound_type).components();
      if(compound.id() == ID_struct)
        for(std::size_t i = 0; i < components.size(); ++i)
          if(components[i].get_name() == member.get_component_name())
            return evaluate(compound.operands()[i], state);
      if(overflow_result_exprt::valid_id(compound.id()))
      {
        auto constant_pair = compound;
        bool constant = true;
        for(auto &op : constant_pair.operands())
        {
          const auto value = evaluate(op, state);
          if(!value || value->lower != value->upper)
          {
            constant = false;
            break;
          }
          op = from_integer(value->lower, op.type());
        }
        if(constant)
        {
          const auto folded = simplify_expr(constant_pair, ns);
          if(folded.id() == ID_struct)
            return evaluate(
              member_exprt(folded, member.get_component_name(), expr.type()),
              state);
        }
        if(member.get_component_name() != ID_value)
          return full;
        exprt arithmetic(
          compound.id() == ID_overflow_result_plus          ? ID_plus
          : compound.id() == ID_overflow_result_minus       ? ID_minus
          : compound.id() == ID_overflow_result_mult        ? ID_mult
          : compound.id() == ID_overflow_result_unary_minus ? ID_unary_minus
                                                            : ID_shl,
          expr.type());
        arithmetic.operands() = compound.operands();
        return evaluate(arithmetic, state);
      }
      return full;
    }
    if(expr.id() == ID_typecast)
    {
      const auto source = evaluate(expr.operands()[0], state);
      if(!source)
        return full;
      if(source->lower == source->upper)
      {
        // Constant integer casts use CBMC's own machine-width simplifier.
        const auto folded = simplify_expr(
          typecast_exprt(
            from_integer(source->lower, expr.operands()[0].type()),
            expr.type()),
          ns);
        mp_integer value;
        if(folded.is_constant() && !to_integer(to_constant_expr(folded), value))
          return ranget{value, value};
      }
      return fit(*source, expr.type());
    }
    if(expr.id() == ID_if)
    {
      auto yes = state, no = state;
      assume(yes, expr.operands()[0], true);
      assume(no, expr.operands()[0], false);
      const auto a = evaluate(expr.operands()[1], yes),
                 b = evaluate(expr.operands()[2], no);
      if(!yes.reachable)
        return b;
      if(!no.reachable)
        return a;
      if(a && b)
        return ranget{
          std::min(a->lower, b->lower), std::max(a->upper, b->upper)};
      return full;
    }
    if(expr.id() == ID_unary_minus)
    {
      const auto a = evaluate(expr.operands()[0], state);
      return a ? fit({-a->upper, -a->lower}, expr.type()) : full;
    }
    if(expr.operands().size() < 2)
      return full;
    auto value = evaluate(expr.operands()[0], state);
    if(!value)
      return full;
    for(std::size_t i = 1; i < expr.operands().size(); ++i)
    {
      const auto right = evaluate(expr.operands()[i], state);
      if(!right)
        return full;
      const auto a = *value, b = *right;
      if(expr.id() == ID_plus)
        value = fit({a.lower + b.lower, a.upper + b.upper}, expr.type());
      else if(expr.id() == ID_minus)
        value = fit({a.lower - b.upper, a.upper - b.lower}, expr.type());
      else if(expr.id() == ID_mult)
      {
        const mp_integer products[] = {
          a.lower * b.lower,
          a.lower * b.upper,
          a.upper * b.lower,
          a.upper * b.upper};
        value = fit(
          {*std::min_element(products, products + 4),
           *std::max_element(products, products + 4)},
          expr.type());
      }
      else if(expr.id() == ID_bitand && b.lower == b.upper && b.lower >= 0)
        value = fit({0, b.upper}, expr.type());
      else if(expr.id() == ID_mod && b.lower == b.upper && b.lower > 0)
        value = fit(
          {a.lower < 0 ? -(b.upper - 1) : mp_integer(0), b.upper - 1},
          expr.type());
      else if(
        expr.id() == ID_div && a.lower >= 0 && b.lower == b.upper &&
        b.lower > 0)
        value = fit({a.lower / b.lower, a.upper / b.lower}, expr.type());
      else
        return full;
      if(!value)
        return full;
    }
    return value;
  }

  void assume(statet &state, const exprt &raw, bool truth) const
  {
    const auto expr = simplify_expr(raw, ns);
    const auto condition = evaluate(expr, state);
    if(condition && condition->lower == condition->upper)
    {
      if((condition->lower != 0) != truth)
        state.reachable = false;
      return;
    }
    if(expr.id() == ID_not)
      return assume(state, expr.operands()[0], !truth);
    if((expr.id() == ID_and && truth) || (expr.id() == ID_or && !truth))
    {
      for(const auto &op : expr.operands())
        assume(state, op, truth);
      return;
    }
    auto id = expr.id();
    if(
      id != ID_equal && id != ID_notequal && id != ID_lt && id != ID_le &&
      id != ID_gt && id != ID_ge)
      return;
    if(!truth)
    {
      if(id == ID_equal)
        id = ID_notequal;
      else if(id == ID_notequal)
        id = ID_equal;
      else if(id == ID_lt)
        id = ID_ge;
      else if(id == ID_le)
        id = ID_gt;
      else if(id == ID_gt)
        id = ID_le;
      else
        id = ID_lt;
    }
    if(id == ID_notequal)
      return;
    const auto a = evaluate(expr.operands()[0], state),
               b = evaluate(expr.operands()[1], state);
    if(!a || !b)
      return;
    auto refine =
      [&](const exprt &side, const ranget &other, const irep_idt &relation)
    {
      const exprt *symbol = &side;
      if(side.id() == ID_typecast && side.operands()[0].id() == ID_symbol)
      {
        const auto source = evaluate(side.operands()[0], state),
                   converted = evaluate(side, state);
        // Only value-preserving casts may transfer a bound to their source.
        if(!source || !converted || !(*source == *converted))
          return;
        symbol = &side.operands()[0];
      }
      if(symbol->id() != ID_symbol)
        return;
      auto narrowed = *evaluate(*symbol, state);
      if(relation == ID_equal || relation == ID_le || relation == ID_lt)
        narrowed.upper = std::min(
          narrowed.upper,
          mp_integer(other.upper - (relation == ID_lt ? 1 : 0)));
      if(relation == ID_equal || relation == ID_ge || relation == ID_gt)
        narrowed.lower = std::max(
          narrowed.lower,
          mp_integer(other.lower + (relation == ID_gt ? 1 : 0)));
      if(narrowed.lower > narrowed.upper)
        state.reachable = false;
      else
        put(state, *symbol, narrowed);
    };
    refine(expr.operands()[0], *b, id);
    // Refine both sides, so n <= maximum uses a tracked variable maximum too.
    const auto reversed = id == ID_lt   ? ID_gt
                          : id == ID_le ? ID_ge
                          : id == ID_gt ? ID_lt
                          : id == ID_ge ? ID_le
                                        : id;
    refine(expr.operands()[1], *a, reversed);
  }

  memory_capacity_boundst
  run(const goto_programt &program, const std::map<irep_idt, exprt> &sizes)
  {
    std::vector<goto_programt::const_targett> instructions;
    std::map<const goto_programt::instructiont *, std::size_t> indices;
    find_symbols_sett symbols;
    for(auto it = program.instructions.begin();
        it != program.instructions.end();
        ++it)
    {
      indices.emplace(&*it, instructions.size());
      instructions.push_back(it);
      find_escaped(it->code());
      find_symbols(it->code(), symbols);
      if(it->has_condition())
      {
        find_escaped(it->condition());
        find_symbols(it->condition(), symbols);
      }
    }
    std::vector<statet> before(instructions.size());
    before.front().reachable = true;
    for(const auto &id : symbols)
    {
      const symbolt *symbol;
      if(
        !ns.lookup(id, symbol) && symbol->is_static_lifetime &&
        symbol->value.is_not_nil())
        assign(before.front(), symbol->symbol_expr(), symbol->value);
    }
    std::deque<std::size_t> queue{0};
    std::vector<bool> queued(instructions.size(), false);
    queued[0] = true;
    auto merge = [&](std::size_t from, std::size_t to, const statet &incoming)
    {
      if(!incoming.reachable)
        return;
      auto &dest = before[to];
      bool changed = !dest.reachable;
      if(!dest.reachable)
        dest = incoming;
      else
      {
        for(auto it = dest.values.begin(); it != dest.values.end();)
        {
          const auto other = incoming.values.find(it->first);
          if(other == incoming.values.end())
          {
            it = dest.values.erase(it);
            changed = true;
            continue;
          }
          ranget joined{
            std::min(it->second.lower, other->second.lower),
            std::max(it->second.upper, other->second.upper)};
          if(to <= from)
          {
            const auto full = type_range(it->first.type());
            if(joined.lower < it->second.lower)
              joined.lower = full->lower;
            if(joined.upper > it->second.upper)
              joined.upper = full->upper;
          }
          if(!(joined == it->second))
          {
            it->second = joined;
            changed = true;
          }
          ++it;
        }
      }
      if(changed && !queued[to])
      {
        queue.push_back(to);
        queued[to] = true;
      }
    };
    while(!queue.empty())
    {
      const auto index = queue.front();
      queue.pop_front();
      queued[index] = false;
      const auto &ins = *instructions[index];
      auto next = before[index];
      if(ins.is_assign())
        assign(next, ins.assign_lhs(), ins.assign_rhs());
      else if(ins.is_decl())
        forget(next, ins.decl_symbol().get_identifier());
      else if(ins.is_dead())
        forget(next, ins.dead_symbol().get_identifier());
      else if(ins.is_function_call())
      {
        havoc_memory(next);
        if(ins.call_lhs().id() == ID_symbol || ins.call_lhs().id() == ID_member)
          forget(next, root_id(ins.call_lhs()));
      }
      else if(ins.is_assume())
        assume(next, ins.condition(), true);
      else if(ins.is_other())
        havoc_memory(next);
      if(ins.is_goto())
      {
        auto taken = next;
        assume(taken, ins.condition(), true);
        for(const auto &target : ins.targets)
          merge(index, indices.at(&*target), taken);
        assume(next, ins.condition(), false);
      }
      if(!ins.is_end_function() && index + 1 < instructions.size())
        merge(index, index + 1, next);
    }

    memory_capacity_boundst bounds;
    std::set<irep_idt> unreachable_declarations;
    for(const auto instruction : instructions)
      if(instruction->is_decl())
        unreachable_declarations.insert(
          instruction->decl_symbol().get_identifier());
    for(std::size_t i = 0; i < instructions.size(); ++i)
    {
      const auto &ins = *instructions[i];
      if(!before[i].reachable)
        continue;
      if(ins.is_decl())
      {
        const auto id = ins.decl_symbol().get_identifier();
        unreachable_declarations.erase(id);
        const auto object = sizes.find(id);
        if(object != sizes.end())
          if(const auto size = evaluate(object->second, before[i]))
            bounds.objects[id] = std::max(bounds.objects[id], size->upper);
      }
      auto allocations = [&](const auto &self, const exprt &expr) -> void
      {
        if(
          expr.id() == ID_side_effect &&
          expr.get(ID_statement) == ID_allocate && expr.operands().size() == 2)
          if(const auto size = evaluate(expr.operands()[0], before[i]))
            bounds.allocation = std::max(bounds.allocation, size->upper);
        for(const auto &op : expr.operands())
          self(self, op);
      };
      allocations(allocations, ins.code());
    }
    // An overapproximated CFG with no reachable declaration needs no backing
    // bytes for that object. Missing *reachable* size information still falls
    // back to the representation ceiling. Do not conflate the two cases.
    for(const auto &id : unreachable_declarations)
      if(sizes.find(id) != sizes.end())
        bounds.objects[id] = 0;
    return bounds;
  }
};
} // namespace

memory_capacity_boundst infer_memory_capacity(
  const goto_programt &program,
  const namespacet &ns,
  const std::map<irep_idt, exprt> &object_sizes)
{
  return capacity_analysist(ns).run(program, object_sizes);
}
