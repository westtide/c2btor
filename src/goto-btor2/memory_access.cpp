#include "memory_access.h"

#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/c_types.h>
#include <util/config.h>
#include <util/pointer_expr.h>
#include <util/pointer_offset_size.h>
#include <util/simplify_expr.h>
#include <util/std_expr.h>
#include <util/string_constant.h>
#include <util/symbol.h>

#include <ansi-c/padding.h>

#include "btor2_type_utils.h"
#include "expr_to_btor2.h"

#include <algorithm>

memory_accesst::memory_accesst(
  btor2_buildert &b,
  expr_to_btor2t &e,
  const namespacet &ns,
  messaget &log,
  unsigned budget,
  array_encoding_optionst array_encoding)
  : heap(b, ns, budget, array_encoding), b(b), expressions(e), ns(ns), log(log)
{
}
void memory_accesst::error(const std::string &message)
{
  failed = true;
  log.error() << "Unsupported byte memory: " << message << messaget::eom;
}
void memory_accesst::collect_expr(const exprt &e, bool addressed)
{
  if(e.id() == ID_side_effect && e.get(ID_statement) == ID_allocate)
    heap.has_dynamic_allocations = true;
  const auto type = follow_tag_type(e.type(), ns);
  if(e.id() == ID_string_constant && !strings.count(e))
  {
    const irep_idt id = "__c2btor_string$" + std::to_string(strings.size());
    strings.emplace(e, id);
    heap.objects.emplace(
      id,
      heap_modelt::objectt{
        id,
        type,
        *size_of_expr(type, ns),
        to_string_constant(e).to_array_expr(),
        true,
        0,
        true});
  }
  if(e.id() == ID_symbol)
  {
    const auto id = to_symbol_expr(e).get_identifier();
    const symbolt *symbol = nullptr;
    if(
      initializer_symbols.insert(id).second && !ns.lookup(id, symbol) &&
      symbol && symbol->is_static_lifetime && symbol->value.is_not_nil())
      collect_expr(symbol->value);
  }
  if(
    e.id() == ID_symbol && (addressed || type.id() == ID_array ||
                            type.id() == ID_struct || type.id() == ID_union))
  {
    const auto id = to_symbol_expr(e).get_identifier();
    const symbolt *symbol = nullptr;
    if(!ns.lookup(id, symbol) && symbol)
    {
      auto size = size_of_expr(type, ns);
      if(type.id() == ID_code)
        size = from_integer(0, size_type());
      const auto *record =
        type.id() == ID_struct ? &to_struct_type(type) : nullptr;
      const bool overflow_pair =
        record && record->components().size() == 2 &&
        record->components()[0].get_name() == ID_value &&
        record->components()[1].type().id() == ID_bool &&
        id2string(record->components()[1].get_name()).find("overflow-") == 0;
      if(!size && overflow_pair && !addressed)
        logical_records.insert(id);
      else if(!size)
        error("unknown object layout for " + id2string(id));
      else
      {
        const exprt size_expr = fold_size_expr(*size);
        heap.objects.emplace(
          id,
          heap_modelt::objectt{
            id,
            type,
            size_expr,
            symbol->value,
            symbol->is_static_lifetime,
            0});
      }
    }
  }
  // Only the root of an address expression is promoted. Index expressions
  // and pointer operands are values, not additional addressed objects.
  if(e.id() == ID_address_of)
    collect_expr(to_address_of_expr(e).object(), true);
  else if(e.id() == ID_member)
    collect_expr(to_member_expr(e).compound(), addressed);
  else if(e.id() == ID_index)
  {
    collect_expr(to_index_expr(e).array(), addressed);
    collect_expr(to_index_expr(e).index());
  }
  else
    for(const auto &op : e.operands())
      collect_expr(op);
}
void memory_accesst::collect_const_bindings(const goto_programt &program)
{
  // A C const-qualified local cannot be reassigned through its name, so a
  // single constant assignment fixes its value for every read in scope.
  // Folding such symbols into array sizes keeps fixed-size arrays declared
  // through `const int N = ...; T a[N];` at their real byte capacity instead
  // of the runtime-object fallback (which silently truncates and freezes).
  std::set<irep_idt> conflicting;
  for(const auto &ins : program.instructions)
  {
    if(!ins.is_assign())
      continue;
    const auto &lhs = ins.assign_lhs();
    if(lhs.id() != ID_symbol || !lhs.type().get_bool(ID_C_constant))
      continue;
    const exprt value = simplify_expr(ins.assign_rhs(), ns);
    if(value.id() != ID_constant)
      continue;
    const irep_idt id = to_symbol_expr(lhs).get_identifier();
    const auto inserted = const_bindings.emplace(id, value);
    if(!inserted.second && inserted.first->second != value)
      conflicting.insert(id);
  }
  for(const auto &id : conflicting)
    const_bindings.erase(id);
}

exprt memory_accesst::fold_size_expr(const exprt &expr) const
{
  if(expr.id() == ID_symbol)
  {
    const irep_idt id = to_symbol_expr(expr).get_identifier();
    const auto found = const_bindings.find(id);
    if(found != const_bindings.end())
      return found->second;
    // Static const globals carry their initializer in the symbol table; the
    // C type system forbids modifying them through their declared name.
    const symbolt *symbol = nullptr;
    if(
      !ns.lookup(id, symbol) && symbol &&
      symbol->type.get_bool(ID_C_constant) && symbol->value.is_not_nil())
    {
      const exprt value = simplify_expr(symbol->value, ns);
      if(value.id() == ID_constant)
        return value;
    }
    return expr;
  }
  exprt result = expr;
  for(auto &op : result.operands())
    op = fold_size_expr(op);
  return simplify_expr(result, ns);
}

void memory_accesst::collect(const goto_programt &program)
{
  collect_const_bindings(program);
  for(const auto &ins : program.instructions)
  {
    collect_expr(ins.code());
    if(ins.has_condition())
      collect_expr(ins.condition());
  }
  // Global initializer addresses can introduce otherwise unreferenced roots.
  std::size_t previous;
  do
  {
    previous = heap.objects.size();
    for(const auto &entry : heap.objects)
      if(entry.second.static_lifetime)
        collect_expr(entry.second.initializer);
  } while(previous != heap.objects.size());
  unsigned tag = 3;
  for(auto &entry : heap.objects)
    entry.second.tag = tag++;
  heap.plan_capacity(program);
}
bool memory_accesst::owns_symbol(const irep_idt &id) const
{
  if(heap.objects.count(id))
    return true;
  const auto name = id2string(id);
  for(const auto &entry : heap.objects)
  {
    const auto root = id2string(entry.first);
    if(
      name.compare(0, root.size() + 1, root + ".") == 0 ||
      name.compare(0, root.size() + 6, root + "$elem$") == 0)
      return true;
  }
  return name.rfind("__heap_malloc$", 0) == 0;
}
bool memory_accesst::owns_lvalue(const exprt &e) const
{
  if(e.id() == ID_symbol)
    return heap.objects.count(to_symbol_expr(e).get_identifier()) != 0;
  if(e.id() == ID_dereference)
    return true;
  if(e.id() == ID_member)
    return owns_lvalue(to_member_expr(e).compound());
  if(e.id() == ID_index)
    return owns_lvalue(to_index_expr(e).array());
  if(
    e.id() == ID_byte_extract_little_endian ||
    e.id() == ID_byte_extract_big_endian)
    return owns_lvalue(to_binary_expr(e).op0());
  return false;
}
void memory_accesst::create_states()
{
  heap.create_states();
  if(heap.failed)
    error(
      heap.failure_reason.empty() ? "object identity capacity exceeded"
                                  : heap.failure_reason);
}
void memory_accesst::initialize_static()
{
  for(const auto &entry : heap.objects)
  {
    const auto &object = entry.second;
    if(!object.static_lifetime || object.type.id() == ID_code)
      continue;
    auto size = numeric_cast<mp_integer>(simplify_expr(object.size, ns));
    if(!size || *size < 0 || *size >= (mp_integer(1) << (heap.offset_bits - 1)))
    {
      error("static object size outside representable range");
      continue;
    }
    heap.activate(object, b.constd(heap.pointer_sort, *size), true);
    if(
      object.initializer.is_not_nil() &&
      !assign_at(heap.base(object.tag), object.type, object.initializer, true))
      error("static initializer for " + id2string(object.id));
  }
  heap.finish_initialization();
}
btor2_nid_t memory_accesst::pointer_integer(const exprt &value)
{
  return expressions.convert(
    typecast_exprt::conditional_cast(
      value, unsignedbv_typet(heap.pointer_bits)));
}
btor2_nid_t memory_accesst::size_value(const typet &type)
{
  auto size = size_of_expr(type, ns);
  if(!size)
  {
    error("cannot compute access size");
    return 0;
  }
  return pointer_integer(*size);
}
btor2_nid_t memory_accesst::add_bytes(btor2_nid_t p, const exprt &amount)
{
  auto bytes = pointer_integer(amount);
  return p && bytes ? heap.add_offset(p, bytes) : 0;
}
btor2_nid_t memory_accesst::address(const exprt &e)
{
  if(e.id() == ID_string_constant)
  {
    const auto it = strings.find(e);
    if(it != strings.end())
      return heap.base(heap.objects.at(it->second).tag);
  }
  if(e.id() == ID_symbol)
  {
    auto it = heap.objects.find(to_symbol_expr(e).get_identifier());
    if(it != heap.objects.end())
      return heap.base(it->second.tag);
  }
  else if(e.id() == ID_dereference)
  {
    auto p = expressions.convert(to_dereference_expr(e).pointer());
    const auto align = alignment(e.type(), ns);
    if(p && align > 1)
      heap.require(b.eq(
        b.get_bool_sort(),
        b.urem(
          heap.offset_sort, heap.offset(p), b.constd(heap.offset_sort, align)),
        b.zero(heap.offset_sort)));
    return p;
  }
  else if(e.id() == ID_member)
  {
    const auto &member = to_member_expr(e);
    const auto root_type = follow_tag_type(member.compound().type(), ns);
    if(root_type.id() == ID_struct)
    {
      auto offset = member_offset_expr(member, ns);
      if(offset)
        return add_bytes(address(member.compound()), *offset);
    }
    else if(root_type.id() == ID_union)
      return address(member.compound());
  }
  else if(e.id() == ID_index)
  {
    const auto &index = to_index_expr(e);
    auto size = size_of_expr(index.type(), ns);
    if(size)
    {
      auto type = signedbv_typet(2 * heap.pointer_bits);
      exprt bytes = mult_exprt(
        typecast_exprt::conditional_cast(index.index(), type),
        typecast_exprt::conditional_cast(*size, type));
      auto full = expressions.convert(bytes);
      auto p = address(index.array());
      if(!full || !p)
        return 0;
      auto narrow = b.slice(heap.pointer_sort, full, heap.pointer_bits - 1, 0);
      heap.require(
        b.eq(
          b.get_bool_sort(),
          full,
          b.sext(expressions.convert_type(type), narrow, heap.pointer_bits)),
        true);
      return heap.add_offset(p, narrow);
    }
  }
  else if(
    e.id() == ID_byte_extract_little_endian ||
    e.id() == ID_byte_extract_big_endian)
    return add_bytes(address(to_binary_expr(e).op0()), to_binary_expr(e).op1());
  error("cannot normalize lvalue " + e.id_string());
  return 0;
}

std::optional<btor2_nid_t> memory_accesst::convert(const exprt &e)
{
  if(e.id() == ID_typecast)
  {
    const auto &operand = to_typecast_expr(e).op();
    const bool from_pointer = operand.type().id() == ID_pointer;
    const bool to_pointer = e.type().id() == ID_pointer;
    const bool to_boolean =
      e.type().id() == ID_bool || e.type().id() == ID_c_bool;
    if(from_pointer || to_pointer)
    {
      const auto integer = [](const typet &type) {
        return type.id() == ID_signedbv || type.id() == ID_unsignedbv ||
               type.id() == ID_c_enum || type.id() == ID_c_enum_tag ||
               type.id() == ID_bool || type.id() == ID_c_bool;
      };
      if(
        (from_pointer && (to_pointer || integer(e.type()))) ||
        (to_pointer && integer(operand.type())))
      {
        // Match bv_pointerst's implementation-defined address representation:
        // pointer/integer casts preserve low bits and ZERO-extend, even when
        // the source integer is signed. This also preserves CIL's integer
        // byte-offset arithmetic and container_of round trips. Dereferences
        // still pass the ordinary identity, lifetime and bounds checks.
        auto value = expressions.convert(operand);
        const auto from = expressions.get_width(operand.type());
        const auto to = expressions.get_width(e.type());
        if(!value || !from || !to)
          return 0;
        const auto sort = expressions.convert_type(e.type());
        if(to_boolean)
        {
          value = b.neq(
            b.get_bool_sort(), value,
            b.zero(expressions.convert_type(operand.type())));
          return *to == 1 ? value : b.uext(sort, value, *to - 1);
        }
        if(*from < *to)
          return b.uext(sort, value, *to - *from);
        if(*from > *to)
          return b.slice(sort, value, *to - 1, 0);
        return value;
      }
      if(operand.type().id() != ID_array)
      {
        error("pointer cast requires an integer or pointer operand/result");
        return 0;
      }
    }
  }
  if(e.id() == ID_member)
  {
    const auto &member = to_member_expr(e);
    if(
      member.compound().id() == ID_symbol &&
      logical_records.count(to_symbol_expr(member.compound()).get_identifier()))
    {
      const auto id =
        id2string(to_symbol_expr(member.compound()).get_identifier()) + "." +
        id2string(member.get_component_name());
      auto value = expressions.lookup_symbol(id);
      if(!value)
        error("missing logical overflow pair field");
      return value.value_or(0);
    }
  }
  if(
    e.id() == ID_typecast && e.type().id() == ID_pointer &&
    to_typecast_expr(e).op().type().id() == ID_array)
    return address(to_typecast_expr(e).op());
  if(
    e.id() == ID_prophecy_r_ok || e.id() == ID_prophecy_w_ok ||
    e.id() == ID_prophecy_rw_ok)
  {
    const auto &ok = to_prophecy_r_or_w_ok_expr(e);
    auto p = expressions.convert(ok.pointer());
    auto n = pointer_integer(ok.size());
    return p && n ? heap.accessible(p, n, e.id() != ID_prophecy_r_ok) : 0;
  }
  if(e.id() == ID_side_effect && e.get(ID_statement) == ID_allocate)
    return allocation(to_side_effect_expr(e));
  if(e.id() == ID_address_of)
    return address(to_address_of_expr(e).object());

  if(e.id() == ID_if)
  {
    // Guards must follow expression evaluation, including conditional loads.
    const auto &value = to_if_expr(e);
    auto cond = expressions.convert(value.cond());
    if(!cond)
      return 0;
    auto saved = heap.path_guard;
    heap.path_guard = b.land(b.get_bool_sort(), saved, cond);
    auto yes = expressions.convert(value.true_case());
    heap.path_guard =
      b.land(b.get_bool_sort(), saved, b.lnot(b.get_bool_sort(), cond));
    auto no = expressions.convert(value.false_case());
    heap.path_guard = saved;
    auto sort = expressions.convert_type(e.type());
    return yes && no && sort ? b.ite(sort, cond, yes, no) : 0;
  }

  if(
    e.id() == ID_minus && e.operands().size() == 2 &&
    e.operands()[0].type().id() == ID_pointer &&
    e.operands()[1].type().id() == ID_pointer)
  {
    auto left = expressions.convert(e.operands()[0]);
    auto right = expressions.convert(e.operands()[1]);
    auto stride = pointer_offset_size(
      to_pointer_type(e.operands()[0].type()).base_type(), ns);
    if(!left || !right || !stride || *stride <= 0)
    {
      error("pointer difference layout");
      return 0;
    }
    heap.require(b.eq(b.get_bool_sort(), heap.tag(left), heap.tag(right)));
    heap.require(heap.accessible(left, b.zero(heap.pointer_sort), false));
    heap.require(heap.accessible(right, b.zero(heap.pointer_sort), false));
    auto difference = b.sub(
      heap.pointer_sort,
      b.sext(
        heap.pointer_sort,
        heap.offset(left),
        heap.pointer_bits - heap.offset_bits),
      b.sext(
        heap.pointer_sort,
        heap.offset(right),
        heap.pointer_bits - heap.offset_bits));
    auto result = b.sdiv(
      heap.pointer_sort, difference, b.constd(heap.pointer_sort, *stride));
    auto width = expressions.get_width(e.type());
    if(!width || *width > heap.pointer_bits)
    {
      error("pointer difference width");
      return 0;
    }
    auto sort = expressions.convert_type(e.type());
    auto narrow = *width == heap.pointer_bits
                    ? result
                    : b.slice(sort, result, *width - 1, 0);
    if(*width < heap.pointer_bits)
      heap.require(b.eq(
        b.get_bool_sort(),
        result,
        b.sext(heap.pointer_sort, narrow, heap.pointer_bits - *width)));
    return narrow;
  }

  if((e.id() == ID_plus || e.id() == ID_minus) && e.type().id() == ID_pointer)
  {
    if(e.operands().size() != 2)
    {
      error("nonbinary pointer arithmetic");
      return 0;
    }
    const exprt *pointer = &e.operands()[0], *index = &e.operands()[1];
    if(pointer->type().id() != ID_pointer && e.id() == ID_plus)
      std::swap(pointer, index);
    if(pointer->type().id() != ID_pointer || index->type().id() == ID_pointer)
    {
      error("pointer arithmetic operands");
      return 0;
    }
    auto size = size_of_expr(to_pointer_type(pointer->type()).base_type(), ns);
    if(!size)
    {
      error("pointer arithmetic stride");
      return 0;
    }
    // Use twice the pointer width before narrowing: multiplication overflow
    // must be a model limit, never a silently wrapped displacement.
    auto wide_type = signedbv_typet(2 * heap.pointer_bits);
    exprt delta = mult_exprt(
      typecast_exprt::conditional_cast(*index, wide_type),
      typecast_exprt::conditional_cast(*size, wide_type));
    if(e.id() == ID_minus)
      delta = unary_minus_exprt(delta);
    auto full = expressions.convert(delta);
    auto p = expressions.convert(*pointer);
    if(!full || !p)
      return 0;
    auto narrow = b.slice(heap.pointer_sort, full, heap.pointer_bits - 1, 0);
    auto wide_sort = b.get_or_create_bitvec_sort(2 * heap.pointer_bits);
    heap.require(
      b.eq(
        b.get_bool_sort(), full, b.sext(wide_sort, narrow, heap.pointer_bits)),
      true);
    return heap.add_offset(p, narrow);
  }

  if(
    e.id() == ID_pointer_object || e.id() == ID_pointer_offset ||
    e.id() == ID_object_size || e.id() == ID_is_dynamic_object ||
    e.id() == ID_is_invalid_pointer)
  {
    auto p = expressions.convert(e.operands()[0]);
    if(!p)
      return 0;
    btor2_nid_t value;
    unsigned width = heap.pointer_bits;
    if(e.id() == ID_pointer_object)
    {
      value = heap.tag(p);
      width = config.bv_encoding.object_bits;
    }
    else if(e.id() == ID_pointer_offset)
    {
      value = heap.offset(p);
      width = heap.offset_bits;
    }
    else if(e.id() == ID_object_size)
      value = heap.size(p);
    else if(e.id() == ID_is_dynamic_object)
      return heap.is_dynamic(p);
    else
      return b.land(
        b.get_bool_sort(),
        b.neq(b.get_bool_sort(), p, b.zero(heap.pointer_sort)),
        b.lnot(b.get_bool_sort(), heap.is_live(p)));
    auto dest = expressions.get_width(e.type());
    if(!dest)
      return 0;
    auto sort = expressions.convert_type(e.type());
    if(*dest < width)
      return b.slice(sort, value, *dest - 1, 0);
    if(*dest > width)
      return e.id() == ID_pointer_offset ? b.sext(sort, value, *dest - width)
                                         : b.uext(sort, value, *dest - width);
    return value;
  }

  if(owns_lvalue(e))
  {
    auto width = expressions.get_width(e.type());
    if(!width)
    {
      error("aggregate value requires structural assignment");
      return 0;
    }
    const auto type = follow_tag_type(e.type(), ns);
    if(type.id() == ID_c_bit_field)
    {
      error("bitfield byte access");
      return 0;
    }
    auto p = address(e);
    return p ? heap.load(p, *width) : 0;
  }
  return {};
}

bool memory_accesst::assign_at(
  btor2_nid_t p,
  const typet &raw_type,
  const exprt &rhs,
  bool zero_initialized)
{
  if(!p)
    return false;
  auto type = follow_tag_type(raw_type, ns);
  // Static storage is already zeroed by activate(). Omit only literal
  // all-zero bit patterns, not floating negative zero or runtime writes.
  if(
    zero_initialized && rhs.id() == ID_constant &&
    (type.id() == ID_signedbv || type.id() == ID_unsignedbv ||
     type.id() == ID_c_bool) && rhs.is_zero())
    return true;
  if(type.id() == ID_struct)
  {
    const auto &structure = to_struct_type(type);
    unsigned i = 0;
    const auto fields = std::count_if(
      structure.components().begin(),
      structure.components().end(),
      [](const auto &field) { return !field.get_bool(ID_C_is_padding); });
    for(const auto &field : structure.components())
    {
      if(field.get_bool(ID_C_is_padding))
      {
        if(rhs.operands().size() != static_cast<std::size_t>(fields))
          ++i;
        continue;
      }
      const auto operand = i++;
      auto off = member_offset(structure, field.get_name(), ns);
      if(!off)
        return false;
      exprt value = member_exprt(rhs, field.get_name(), field.type());
      if(rhs.id() == ID_struct && operand < rhs.operands().size())
        value = rhs.operands()[operand];
      auto q = add_bytes(p, from_integer(*off, size_type()));
      if(!assign_at(q, field.type(), value, zero_initialized))
        return false;
    }
    return true;
  }
  if(type.id() == ID_array)
  {
    const auto &array = to_array_type(type);
    auto count = numeric_cast<mp_integer>(array.size());
    auto stride = pointer_offset_size(array.element_type(), ns);
    // Literal static initializers need no transition-time unrolling. Their
    // implicit zero tail is represented by the object's zeroed metadata.
    const bool static_literal =
      zero_initialized && (rhs.id() == ID_array || rhs.id() == ID_array_of);
    if(!count || !stride || *count < 0 || (!static_literal && *count > 4096))
    {
      error("aggregate assignment needs bounded or loop lowering");
      return false;
    }
    if(
      static_literal && rhs.id() == ID_array_of &&
      to_array_of_expr(rhs).op().id() == ID_constant &&
      (array.element_type().id() == ID_signedbv ||
       array.element_type().id() == ID_unsignedbv) &&
      to_array_of_expr(rhs).op().is_zero())
      return true;
    for(mp_integer i = 0; i < *count; ++i)
    {
      exprt value = index_exprt(rhs, from_integer(i, array.index_type()));
      if(rhs.id() == ID_array_of)
        value = to_array_of_expr(rhs).op();
      else if(rhs.id() == ID_array && i < rhs.operands().size())
        value = rhs.operands()[numeric_cast_v<std::size_t>(i)];
      if(
        zero_initialized && value.id() == ID_constant &&
        (array.element_type().id() == ID_signedbv ||
         array.element_type().id() == ID_unsignedbv ||
         array.element_type().id() == ID_c_bool) && value.is_zero())
        continue;
      if(!assign_at(
           add_bytes(p, from_integer(i * *stride, size_type())),
           array.element_type(),
           value,
           zero_initialized))
        return false;
    }
    return true;
  }
  auto width = expressions.get_width(type);
  if(!width || type.id() == ID_c_bit_field)
  {
    error("unsupported store type " + type.id_string());
    return false;
  }
  auto value =
    expressions.convert(typecast_exprt::conditional_cast(rhs, raw_type));
  if(!value)
    return false;
  heap.store(p, value, *width);
  return true;
}
bool memory_accesst::assign(const exprt &lhs, const exprt &rhs)
{
  if(!owns_lvalue(lhs))
    return false;
  if(!assign_at(address(lhs), lhs.type(), rhs))
    error("assignment could not be lowered");
  return true;
}
void memory_accesst::declaration(const symbol_exprt &symbol, bool dead)
{
  auto it = heap.objects.find(symbol.get_identifier());
  if(it == heap.objects.end())
    return;
  if(dead)
    heap.deactivate(it->second);
  else
  {
    auto size = pointer_integer(it->second.size);
    if(size)
      heap.activate(it->second, size, false);
    else
      error("object size at declaration");
  }
}
btor2_nid_t memory_accesst::allocation(const side_effect_exprt &allocation)
{
  if(allocation.operands().size() != 2)
  {
    error("allocate operands");
    return 0;
  }
  auto bytes = pointer_integer(allocation.operands()[0]);
  auto zero = expressions.convert(allocation.operands()[1]);
  return bytes && zero ? heap.allocate(bytes, zero) : 0;
}
