// SPDX-License-Identifier: BSD-4-Clause
// SPDX-FileCopyrightText: 2026 C2BTOR contributors

#include "logical_arrays.h"

#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/c_types.h>
#include <util/config.h>
#include <util/ieee_float.h>
#include <util/simplify_expr.h>
#include <util/std_code.h>
#include <util/std_expr.h>
#include <util/symbol.h>
#include <util/symbol_table_base.h>

#include "expr_to_btor2.h"
#include "memory_access.h"
#include "memory_capacity.h"

#include <algorithm>
#include <functional>
#include <limits>

namespace
{
bool signed_type(const typet &raw, const namespacet &ns)
{
  const auto type = follow_tag_type(raw, ns);
  return type.id() == ID_signedbv ||
         (type.id() == ID_c_enum &&
          to_c_enum_type(type).underlying_type().id() == ID_signedbv);
}

bool qualified(const typet &raw, const namespacet &ns)
{
  const auto type = follow_tag_type(raw, ns);
  return raw.get_bool(ID_C_volatile) || raw.get_bool(ID_C_atomic) ||
         type.get_bool(ID_C_volatile) || type.get_bool(ID_C_atomic) ||
         (type.id() == ID_array &&
          qualified(to_array_type(type).element_type(), ns));
}

bool integral_dimension(const typet &raw, const namespacet &ns)
{
  const auto type = follow_tag_type(raw, ns);
  return type.id() == ID_signedbv || type.id() == ID_unsignedbv ||
         type.id() == ID_bool || type.id() == ID_c_bool ||
         type.id() == ID_c_enum;
}

bool dimension_side_effect(const exprt &expr)
{
  return expr.id() == ID_side_effect ||
         std::any_of(
           expr.operands().begin(),
           expr.operands().end(),
           [](const exprt &operand) { return dimension_side_effect(operand); });
}

bool literal(const exprt &expr, const namespacet &ns)
{
  if(expr.id() == ID_array)
    return std::all_of(
      expr.operands().begin(),
      expr.operands().end(),
      [&](const exprt &e) { return literal(e, ns); });
  if(expr.id() == ID_array_of)
    return expr.operands().size() == 1 && literal(expr.operands()[0], ns);
  // Constant scalar leaves avoid dependencies on other arrays, arbitrary
  // aggregate operations, and input-dependent static initializers.
  if(expr.id() == ID_constant)
    return true;
  return expr.id() != ID_side_effect && !expr.operands().empty() &&
         std::all_of(
           expr.operands().begin(),
           expr.operands().end(),
           [&](const exprt &e) { return literal(e, ns); }) &&
         simplify_expr(expr, ns).id() == ID_constant;
}

bool nondet(const exprt &expr)
{
  return expr.id() == ID_side_effect && expr.get(ID_statement) == ID_nondet;
}

const exprt *uniform_leaf(const exprt &expr, const namespacet &ns)
{
  const exprt *leaf = &expr;
  while(leaf->id() == ID_array_of && leaf->operands().size() == 1)
    leaf = &leaf->operands()[0];
  return follow_tag_type(leaf->type(), ns).id() != ID_array &&
             literal(*leaf, ns)
           ? leaf
           : nullptr;
}

bool supported_initializer(
  const exprt &expr,
  const namespacet &ns,
  bool top = true)
{
  if(const auto leaf = uniform_leaf(expr, ns))
    if(
      top || follow_tag_type(expr.type(), ns).id() != ID_array ||
      simplify_expr(*leaf, ns).is_zero())
      return true;
  if(expr.id() == ID_array)
    return std::all_of(
      expr.operands().begin(),
      expr.operands().end(),
      [&](const exprt &operand)
      { return supported_initializer(operand, ns, false); });
  if(expr.id() == ID_array_of && expr.operands().size() == 1)
  {
    const auto type = follow_tag_type(expr.type(), ns);
    const auto size =
      numeric_cast<mp_integer>(simplify_expr(to_array_type(type).size(), ns));
    return size && *size >= 0 && *size <= 4096 &&
           supported_initializer(expr.operands()[0], ns, false);
  }
  return false;
}
} // namespace

logical_arrayst::logical_arrayst(
  btor2_buildert &builder,
  expr_to_btor2t &converter,
  const namespacet &name_space,
  array_encoding_optionst options,
  bool enable)
  : b(builder),
    expressions(converter),
    ns(name_space),
    encoding(options),
    enabled(enable)
{
}

void logical_arrayst::error(const std::string &reason)
{
  if(!failed)
    failure_reason = reason;
  failed = true;
}

std::optional<logical_arrayst::accesst>
logical_arrayst::access(const exprt &expr)
{
  const exprt *root = &expr;
  accesst result;
  while(root->id() == ID_index && root->operands().size() == 2)
  {
    result.indices.push_back(to_index_expr(*root).index());
    root = &to_index_expr(*root).array();
  }
  if(root->id() != ID_symbol)
    return {};
  result.id = to_symbol_expr(*root).get_identifier();
  std::reverse(result.indices.begin(), result.indices.end());
  return result;
}

void logical_arrayst::collect(const goto_programt &program)
{
  if(!enabled || failed)
    return;
  // A raw pointer can legally name an otherwise unaddressed object. Keep the
  // existing single byte store whenever the storage universe is open.
  if(has_arbitrary_pointer_input(program, ns))
    return;

  std::set<irep_idt> referenced;
  std::vector<exprt> initializers;
  std::function<void(const exprt &)> gather = [&](const exprt &expr)
  {
    if(expr.id() == ID_symbol)
    {
      const auto id = to_symbol_expr(expr).get_identifier();
      const symbolt *symbol = nullptr;
      if(referenced.insert(id).second && !ns.lookup(id, symbol) && symbol)
      {
        if(symbol->is_static_lifetime && symbol->value.is_not_nil())
        {
          initializers.push_back(symbol->value);
          gather(symbol->value);
        }
        auto type = follow_tag_type(symbol->type, ns);
        while(type.id() == ID_array)
        {
          gather(to_array_type(type).size());
          type = follow_tag_type(to_array_type(type).element_type(), ns);
        }
      }
    }
    for(const auto &operand : expr.operands())
      gather(operand);
  };
  for(const auto &instruction : program.instructions)
  {
    gather(instruction.code());
    if(instruction.has_condition())
      gather(instruction.condition());
  }

  for(const auto &id : referenced)
  {
    const symbolt *symbol = nullptr;
    if(
      ns.lookup(id, symbol) || !symbol || !is_c_source_object(*symbol, ns) ||
      qualified(symbol->type, ns) ||
      follow_tag_type(symbol->type, ns).id() != ID_array)
      continue;
    arrayt array;
    array.id = id;
    array.type = symbol->type;
    array.static_lifetime = symbol->is_static_lifetime;
    array.initializer = symbol->value;
    std::vector<array_dimt> dimensions;
    get_array_dimensions(array.type, ns, dimensions, array.leaf);
    const auto leaf_id = array.leaf.id();
    if(
      leaf_id != ID_signedbv && leaf_id != ID_unsignedbv &&
      leaf_id != ID_bool && leaf_id != ID_c_bool && leaf_id != ID_c_enum &&
      leaf_id != ID_floatbv)
      continue;
    const auto width = expressions.get_width(array.leaf);
    if(!width || *width == 0)
      continue;
    array.source_width = *width;
    array.boolean = leaf_id == ID_bool || leaf_id == ID_c_bool;
    array.element_width = array.boolean ? 1 : *width;
    bool complete = true;
    for(const auto &dimension : dimensions)
    {
      const auto w = expressions.get_width(dimension.size.type());
      if(
        dimension.size.is_nil() ||
        !integral_dimension(dimension.size.type(), ns) ||
        dimension_side_effect(dimension.size) || !w || *w == 0 ||
        *w > std::numeric_limits<unsigned>::max() - array.index_width)
      {
        complete = false;
        break;
      }
      array.dimensions.push_back({dimension.size, *w, 0, 0});
      array.index_width += *w;
    }
    if(
      complete && !array.dimensions.empty() &&
      (!array.static_lifetime || array.initializer.is_nil() ||
       (literal(array.initializer, ns) &&
        supported_initializer(array.initializer, ns))))
      arrays.emplace(id, std::move(array));
  }

  std::set<irep_idt> rejected;
  std::set<irep_idt> declarations;
  std::set<irep_idt> read_roots;
  std::vector<std::pair<irep_idt, irep_idt>> certified_copies;
  auto reject_tree = [&](const auto &self, const exprt &expr) -> void
  {
    if(expr.id() == ID_symbol)
      rejected.insert(to_symbol_expr(expr).get_identifier());
    for(const auto &operand : expr.operands())
      self(self, operand);
  };
  std::function<void(const exprt &)> inspect = [&](const exprt &expr)
  {
    if(
      expr.id() == ID_address_of ||
      expr.id() == ID_byte_extract_little_endian ||
      expr.id() == ID_byte_extract_big_endian ||
      expr.id() == ID_byte_update_little_endian ||
      expr.id() == ID_byte_update_big_endian)
    {
      reject_tree(reject_tree, expr);
      return;
    }
    if(expr.id() == ID_index)
    {
      const auto path = access(expr);
      if(path && arrays.count(path->id))
      {
        if(
          path->indices.size() != arrays.at(path->id).dimensions.size() ||
          follow_tag_type(expr.type(), ns).id() == ID_array)
          rejected.insert(path->id);
        read_roots.insert(path->id);
        for(const auto &subscript : path->indices)
          inspect(subscript);
        return;
      }
    }
    if(
      expr.id() == ID_symbol &&
      arrays.count(to_symbol_expr(expr).get_identifier()))
      rejected.insert(to_symbol_expr(expr).get_identifier());
    for(const auto &operand : expr.operands())
      inspect(operand);
  };
  for(const auto &instruction : program.instructions)
  {
    if(instruction.is_decl() || instruction.is_dead())
    {
      const auto &symbol = instruction.is_decl()
                             ? instruction.decl_symbol()
                             : to_code_dead(instruction.code()).symbol();
      if(instruction.is_decl())
        declarations.insert(symbol.get_identifier());
      continue;
    }
    if(instruction.is_assign())
    {
      const auto &lhs = instruction.assign_lhs();
      const auto &rhs = instruction.assign_rhs();
      if(
        instruction.code().get_bool("c2btor_certified_array_copy") &&
        lhs.id() == ID_symbol && rhs.id() == ID_symbol &&
        lhs.type() == rhs.type())
      {
        const auto destination = to_symbol_expr(lhs).get_identifier();
        const auto source = to_symbol_expr(rhs).get_identifier();
        if(arrays.count(destination) && arrays.count(source))
        {
          certified_copies.emplace_back(destination, source);
          // The source storage is observed even if it has no scalar reads.
          read_roots.insert(source);
          continue;
        }
      }
      if(
        lhs.id() == ID_symbol &&
        arrays.count(to_symbol_expr(lhs).get_identifier()) &&
        ((literal(rhs, ns) && supported_initializer(rhs, ns)) || nondet(rhs)))
      {
        inspect(rhs);
        continue;
      }
      const auto path = access(lhs);
      if(
        path && arrays.count(path->id) &&
        path->indices.size() == arrays.at(path->id).dimensions.size())
      {
        for(const auto &subscript : path->indices)
          inspect(subscript);
      }
      else
        inspect(lhs);
      inspect(rhs);
      continue;
    }
    inspect(instruction.code());
    if(instruction.has_condition())
      inspect(instruction.condition());
  }
  for(const auto &init : initializers)
    // Physical initializers run before this backend's final literal states.
    // C normally forbids object reads in static initializers; decline such
    // synthetic cross-object dependencies rather than read a seed state.
    reject_tree(reject_tree, init);
  // Inspect all dimensions before erasing any candidates, so references to a
  // candidate inspected earlier cannot escape a later rejection.
  for(const auto &entry : arrays)
    for(const auto &dimension : entry.second.dimensions)
      inspect(dimension.size);
  // A storage-wide copy must never cross the logical/byte-memory boundary.
  // Propagate every rejection before removing candidates, including chains.
  for(bool changed = true; changed;)
  {
    changed = false;
    for(const auto &copy : certified_copies)
      if(
        rejected.count(copy.first) || rejected.count(copy.second) ||
        (!arrays.at(copy.first).static_lifetime &&
         !declarations.count(copy.first)) ||
        (!arrays.at(copy.second).static_lifetime &&
         !declarations.count(copy.second)))
      {
        changed |= rejected.insert(copy.first).second;
        changed |= rejected.insert(copy.second).second;
      }
  }
  for(auto it = arrays.begin(); it != arrays.end();)
  {
    if(
      rejected.count(it->first) ||
      (!it->second.static_lifetime && !declarations.count(it->first)))
      it = arrays.erase(it);
    else
      ++it;
  }

  std::vector<std::map<irep_idt, exprt>> dimension_sizes;
  std::map<irep_idt, std::vector<std::optional<mp_integer>>> maxima;
  for(auto &entry : arrays)
  {
    auto &array = entry.second;
    array.unused = read_roots.count(entry.first) == 0;
    if(array.unused)
      continue;
    if(dimension_sizes.size() < array.dimensions.size())
      dimension_sizes.resize(array.dimensions.size());
    auto &upper = maxima[entry.first];
    for(std::size_t i = 0; i < array.dimensions.size(); ++i)
    {
      const auto &dimension = array.dimensions[i];
      upper.push_back(
        numeric_cast<mp_integer>(simplify_expr(dimension.size, ns)));
      if(upper.back() && *upper.back() < 0)
        upper.back() = 0; // Invalid dimensions have no in-bounds accesses.
      if(
        !upper.back() &&
        (encoding.bitvectors || encoding.mixed || encoding.max_object_bytes))
      {
        // The byte-capacity analysis casts sizes to pointer width. Never feed
        // it a wider dimension or a product that can wrap at that boundary.
        if(dimension.width <= config.ansi_c.pointer_width)
          dimension_sizes[i].emplace(entry.first, dimension.size);
        else
          upper.back() = (mp_integer(1) << dimension.width) - 1;
      }
    }
  }
  for(std::size_t i = 0; i < dimension_sizes.size(); ++i)
    if(!dimension_sizes[i].empty())
    {
      const auto bounds =
        infer_memory_capacity(program, ns, dimension_sizes[i]);
      for(const auto &bound : bounds.objects)
        maxima.at(bound.first)[i] = bound.second;
    }
  for(auto &entry : arrays)
  {
    auto &array = entry.second;
    roots.insert(entry.first);
    if(array.unused)
      continue;
    array.upper_elements = 1;
    for(const auto &maximum : maxima.at(entry.first))
    {
      if(!maximum)
      {
        array.upper_elements.reset();
        break;
      }
      *array.upper_elements *= *maximum;
    }
    const bool bounded = array.upper_elements && *array.upper_elements >= 0;
    const mp_integer bits =
      bounded ? *array.upper_elements * array.element_width : mp_integer(-1);
    if(
      encoding.max_object_bytes &&
      (!bounded || *array.upper_elements * ((array.source_width + 7) / 8) >
                     *encoding.max_object_bytes))
      error(
        "array " + id2string(entry.first) +
        " has no element bound within the explicit storage limit");
    array.native =
      !encoding.bitvectors &&
      (!encoding.mixed || !bounded || bits > encoding.mixed_threshold_bits);
    if(!array.native)
    {
      if(!bounded || bits > std::numeric_limits<int>::max())
        error(
          "array " + id2string(entry.first) +
          " exceeds the packed bitvector width limit or has no bound");
      else
        array.packed_width =
          std::max<std::size_t>(1, numeric_cast_v<std::size_t>(bits));
    }
  }
}

bool logical_arrayst::owns_lvalue(const exprt &expr) const
{
  const auto path = access(expr);
  if(!path || !owns_symbol(path->id))
    return false;
  return path->indices.empty() ||
         path->indices.size() == arrays.at(path->id).dimensions.size();
}

btor2_nid_t logical_arrayst::add_state(
  btor2_nid_t sort,
  const std::string &name,
  const std::string &source)
{
  const auto state = b.state(sort, name, source);
  updates.emplace(state, updatet{sort, state, state});
  sorts.emplace(state, sort);
  return state;
}

void logical_arrayst::create_states()
{
  if(failed)
    return;
  for(auto &entry : arrays)
  {
    auto &array = entry.second;
    if(array.unused)
      continue;
    array.element_sort = b.get_or_create_bitvec_sort(array.element_width);
    array.index_sort = b.get_or_create_bitvec_sort(array.index_width);
    array.storage_sort = array.native
                           ? b.sort_array(array.index_sort, array.element_sort)
                           : b.get_or_create_bitvec_sort(array.packed_width);
    const auto zero =
      array.static_lifetime
        ? b.zero(array.native ? array.element_sort : array.storage_sort)
        : 0;
    array.state = add_state(
      array.storage_sort,
      "__c2btor_elements$" + id2string(array.id),
      id2string(array.id));
    if(array.static_lifetime)
      b.init(array.storage_sort, array.state, zero);
    for(std::size_t i = 0; i < array.dimensions.size(); ++i)
    {
      auto &dimension = array.dimensions[i];
      const auto constant =
        numeric_cast<mp_integer>(simplify_expr(dimension.size, ns));
      const auto sort = b.get_or_create_bitvec_sort(dimension.width);
      if(constant)
        dimension.constant = b.constd(sort, *constant);
      else
        dimension.state = add_state(
          sort,
          "__c2btor_dimension$" + id2string(array.id) + "$" +
            std::to_string(i));
    }
  }
}

btor2_nid_t logical_arrayst::local(btor2_nid_t state) const
{
  return updates.at(state).local;
}

void logical_arrayst::set_local(btor2_nid_t state, btor2_nid_t value)
{
  if(!value)
    error("expression conversion failed for logical array");
  else
    updates.at(state).local = value;
  expressions.clear_caches();
}

btor2_nid_t logical_arrayst::resize(
  btor2_nid_t value,
  std::size_t from,
  std::size_t to,
  bool sign)
{
  if(!value || from == to)
    return value;
  const auto sort = b.get_or_create_bitvec_sort(to);
  if(from > to)
    return b.slice(sort, value, to - 1, 0);
  return sign ? b.sext(sort, value, to - from) : b.uext(sort, value, to - from);
}

std::pair<btor2_nid_t, btor2_nid_t>
logical_arrayst::index(const arrayt &array, const std::vector<exprt> &indices)
{
  const auto boolean = b.get_bool_sort();
  auto valid = b.one(boolean);
  auto result = b.zero(array.index_sort);
  for(std::size_t i = 0; i < indices.size(); ++i)
  {
    const auto &dimension = array.dimensions[i];
    const auto source_width = expressions.get_width(indices[i].type());
    const auto value = expressions.convert(indices[i]);
    if(!source_width || !value)
    {
      error("logical array subscript conversion");
      return {0, 0};
    }
    const auto size =
      dimension.state ? local(dimension.state) : dimension.constant;
    const auto compare_width = std::max(*source_width, dimension.width);
    const auto compare_sort = b.get_or_create_bitvec_sort(compare_width);
    const auto extended_index = resize(
      value, *source_width, compare_width, signed_type(indices[i].type(), ns));
    const auto extended_size = resize(
      size,
      dimension.width,
      compare_width,
      signed_type(dimension.size.type(), ns));
    auto in_range = b.ult(boolean, extended_index, extended_size);
    const auto zero = b.zero(compare_sort);
    if(signed_type(indices[i].type(), ns))
      in_range =
        b.land(boolean, in_range, b.sgte(boolean, extended_index, zero));
    if(signed_type(dimension.size.type(), ns))
      in_range =
        b.land(boolean, in_range, b.sgte(boolean, extended_size, zero));
    valid = b.land(boolean, valid, in_range);
    result = b.add(
      array.index_sort,
      b.mul(
        array.index_sort,
        result,
        resize(size, dimension.width, array.index_width)),
      resize(value, *source_width, array.index_width));
  }
  return {result, valid};
}

btor2_nid_t logical_arrayst::element(const arrayt &array, const exprt &rhs)
{
  const auto value = expressions.convert(rhs);
  const auto width = expressions.get_width(rhs.type());
  if(!value || !width)
  {
    error("logical array element conversion");
    return 0;
  }
  if(array.boolean)
    return b.neq(
      b.get_bool_sort(), value, b.zero(b.get_or_create_bitvec_sort(*width)));
  return resize(
    value, *width, array.element_width, signed_type(rhs.type(), ns));
}

btor2_nid_t
logical_arrayst::read(const arrayt &array, btor2_nid_t storage, btor2_nid_t at)
{
  if(array.native)
    return b.read(array.element_sort, storage, at);
  const auto shifted_index = resize(at, array.index_width, array.packed_width);
  const auto shift = b.mul(
    array.storage_sort,
    shifted_index,
    b.constd(array.storage_sort, array.element_width));
  return resize(
    b.srl(array.storage_sort, storage, shift),
    array.packed_width,
    array.element_width);
}

btor2_nid_t logical_arrayst::write(
  const arrayt &array,
  btor2_nid_t storage,
  btor2_nid_t at,
  btor2_nid_t value)
{
  if(array.native)
    return b.write(array.storage_sort, storage, at, value);
  const auto shift = b.mul(
    array.storage_sort,
    resize(at, array.index_width, array.packed_width),
    b.constd(array.storage_sort, array.element_width));
  const auto mask = b.sll(
    array.storage_sort,
    resize(b.ones(array.element_sort), array.element_width, array.packed_width),
    shift);
  return b.lor(
    array.storage_sort,
    b.land(array.storage_sort, storage, b.lnot(array.storage_sort, mask)),
    b.sll(
      array.storage_sort,
      resize(value, array.element_width, array.packed_width),
      shift));
}

std::optional<btor2_nid_t> logical_arrayst::convert(const exprt &expr)
{
  const auto path = access(expr);
  if(!path || !owns_symbol(path->id))
    return {};
  if(failed)
    return 0;
  const auto &array = arrays.at(path->id);
  if(array.unused)
  {
    error("unexpected read of discarded logical array");
    return 0;
  }
  if(path->indices.size() != array.dimensions.size())
  {
    error("partial logical array value");
    return 0;
  }
  const auto location = index(array, path->indices);
  if(failed)
    return 0;
  auto value = read(array, local(array.state), location.first);
  value = b.ite(
    array.element_sort, location.second, value, b.zero(array.element_sort));
  return resize(value, array.element_width, array.source_width);
}

btor2_nid_t logical_arrayst::fill(const arrayt &array, const exprt &raw)
{
  const auto expr = simplify_expr(raw, ns);
  if(expr.id() != ID_constant)
  {
    error("nonconstant whole-array fill");
    return 0;
  }
  auto number = numeric_cast<mp_integer>(expr);
  if(expr.type().id() == ID_bool)
    number = expr.is_true() ? 1 : 0;
  else if(expr.type().id() == ID_floatbv)
    number = ieee_float_valuet(to_constant_expr(expr)).pack();
  if(!number)
  {
    error("unsupported constant whole-array fill");
    return 0;
  }
  if(array.boolean)
    *number = *number != 0 ? 1 : 0;
  const mp_integer modulus = mp_integer(1) << array.element_width;
  const mp_integer pattern = ((*number % modulus) + modulus) % modulus;
  // Array init's scalar broadcast operand must be a literal constant, not a
  // normalization or resizing expression, even when that expression is pure.
  const auto value = b.constd(array.element_sort, pattern);
  if(array.native)
  {
    const auto state = add_state(
      array.storage_sort, "__c2btor_element_fill$" + id2string(array.id));
    b.init(array.storage_sort, state, value);
    return state;
  }
  if(pattern == 0)
    return b.zero(array.storage_sort);
  // Nonzero constant replication does not create per-element expressions.
  const mp_integer repeated =
    ((mp_integer(1) << array.packed_width) - 1) / (modulus - 1) * pattern;
  return b.constd(array.storage_sort, repeated);
}

btor2_nid_t logical_arrayst::initializer(
  const arrayt &array,
  const exprt &expr,
  btor2_nid_t storage,
  mp_integer &offset)
{
  if(expr.id() == ID_array)
  {
    for(const auto &operand : expr.operands())
    {
      storage = initializer(array, operand, storage, offset);
      if(failed)
        return 0;
    }
    return storage;
  }
  if(expr.id() == ID_array_of)
  {
    const auto type = follow_tag_type(expr.type(), ns);
    const auto count =
      numeric_cast<mp_integer>(simplify_expr(to_array_type(type).size(), ns));
    if(!count || *count < 0)
    {
      error("nested runtime whole-array initializer");
      return 0;
    }
    // Large all-zero initializers need no explicit writes into zero backing.
    if(
      uniform_leaf(expr, ns) &&
      simplify_expr(*uniform_leaf(expr, ns), ns).is_zero())
    {
      mp_integer leaves = *count;
      auto element_type =
        follow_tag_type(to_array_type(type).element_type(), ns);
      while(element_type.id() == ID_array)
      {
        const auto size = numeric_cast<mp_integer>(
          simplify_expr(to_array_type(element_type).size(), ns));
        if(!size || *size < 0)
        {
          error("incomplete nested initializer");
          return 0;
        }
        leaves *= *size;
        element_type =
          follow_tag_type(to_array_type(element_type).element_type(), ns);
      }
      offset += leaves;
      return storage;
    }
    if(*count > 4096)
    {
      error("large nested nonuniform array initializer");
      return 0;
    }
    for(mp_integer i = 0; i < *count; ++i)
      storage = initializer(array, expr.operands()[0], storage, offset);
    return storage;
  }
  const auto value = element(array, expr);
  if(!value)
    return 0;
  storage = write(array, storage, b.constd(array.index_sort, offset), value);
  ++offset;
  return storage;
}

bool logical_arrayst::assign(const exprt &lhs, const exprt &rhs)
{
  return assign_impl(lhs, rhs, nullptr);
}

bool logical_arrayst::assign(
  const exprt &lhs,
  const exprt &rhs,
  btor2_nid_t &assigned_leaf)
{
  assigned_leaf = 0;
  return assign_impl(lhs, rhs, &assigned_leaf);
}

bool logical_arrayst::assign_impl(
  const exprt &lhs,
  const exprt &rhs,
  btor2_nid_t *assigned_leaf)
{
  nondet_input = 0;
  const auto path = access(lhs);
  if(!path || !owns_symbol(path->id))
    return false;
  if(failed)
    return true;
  const auto &array = arrays.at(path->id);
  if(array.unused)
  {
    for(const auto &subscript : path->indices)
      if(!expressions.convert(subscript))
        error("discarded array subscript conversion");
    if(!path->indices.empty())
    {
      if(assigned_leaf)
      {
        const auto value = element(array, rhs);
        if(!failed)
          *assigned_leaf =
            resize(value, array.element_width, array.source_width);
      }
      else if(!expressions.convert(rhs))
        error("discarded array value conversion");
    }
    return true;
  }
  if(path->indices.empty())
  {
    btor2_nid_t value = 0;
    if(nondet(rhs))
    {
      value = b.input(
        array.storage_sort,
        "__c2btor_elements_nondet$" + id2string(array.id) + "$" +
          std::to_string(current_pc));
      nondet_input = value;
    }
    else if(
      rhs.id() == ID_symbol &&
      owns_symbol(to_symbol_expr(rhs).get_identifier()) &&
      rhs.type() == lhs.type())
    {
      const auto &source = arrays.at(to_symbol_expr(rhs).get_identifier());
      if(
        source.unused || source.native != array.native ||
        source.index_width != array.index_width ||
        source.element_width != array.element_width ||
        (!array.native && source.packed_width != array.packed_width))
        error("incompatible certified logical array copy");
      else
        // Read the current block-local storage node exactly once. Later
        // source writes create new nodes and cannot alter this snapshot.
        value = local(source.state);
    }
    else if(rhs.id() == ID_array_of && uniform_leaf(rhs, ns))
      value = fill(array, *uniform_leaf(rhs, ns));
    else if(rhs.id() == ID_array)
    {
      const auto zero = from_integer(0, array.leaf);
      value = fill(array, zero);
      mp_integer offset = 0;
      value = initializer(array, rhs, value, offset);
    }
    else
      error("unsupported whole logical array assignment");
    if(value)
      set_local(array.state, value);
    return true;
  }
  if(path->indices.size() != array.dimensions.size())
  {
    error("partial logical array assignment");
    return true;
  }
  const auto location = index(array, path->indices);
  const auto value = element(array, rhs);
  if(!failed)
  {
    if(assigned_leaf)
      *assigned_leaf = resize(value, array.element_width, array.source_width);
    set_local(
      array.state,
      b.ite(
        array.storage_sort,
        location.second,
        write(array, local(array.state), location.first, value),
        local(array.state)));
  }
  return true;
}

void logical_arrayst::initialize_static()
{
  if(failed)
    return;
  for(auto &entry : arrays)
  {
    auto &array = entry.second;
    if(array.unused || !array.static_lifetime || array.initializer.is_nil())
      continue;
    auto value = local(array.state);
    if(
      array.initializer.id() == ID_array_of &&
      uniform_leaf(array.initializer, ns))
      value = fill(array, *uniform_leaf(array.initializer, ns));
    else
    {
      mp_integer offset = 0;
      value = initializer(array, array.initializer, value, offset);
    }
    if(failed)
      return;
    // Keep the initial expression before the final state, as BTOR2 requires.
    array.state = add_state(
      array.storage_sort,
      "__c2btor_elements_initial$" + id2string(array.id),
      id2string(array.id));
    b.init(array.storage_sort, array.state, value);
  }
}

void logical_arrayst::declaration(const symbol_exprt &symbol, bool dead)
{
  const auto found = arrays.find(symbol.get_identifier());
  if(found == arrays.end() || failed || dead || found->second.static_lifetime)
    return;
  auto &array = found->second;
  if(array.unused)
    return;
  for(auto &dimension : array.dimensions)
    if(dimension.state)
      set_local(dimension.state, expressions.convert(dimension.size));
  if(!failed)
    set_local(
      array.state,
      b.input(
        array.storage_sort,
        "__c2btor_elements_fresh$" + id2string(array.id) + "$" +
          std::to_string(current_pc)));
}

void logical_arrayst::begin(unsigned pc, btor2_nid_t guard)
{
  current_pc = pc;
  current_guard = guard;
  for(auto &entry : updates)
    entry.second.local = entry.first;
  expressions.clear_caches();
}

logical_arrayst::valuest logical_arrayst::values() const
{
  valuest result;
  for(const auto &entry : updates)
    result.emplace(entry.first, entry.second.local);
  return result;
}

void logical_arrayst::bind(const valuest &environment)
{
  for(const auto &entry : environment)
  {
    const auto found = updates.find(entry.first);
    if(found != updates.end())
      found->second.local = entry.second;
  }
  expressions.clear_caches();
}

void logical_arrayst::commit(btor2_nid_t guard, const valuest &environment)
{
  if(failed)
    return;
  for(const auto &entry : environment)
  {
    const auto found = updates.find(entry.first);
    if(found != updates.end() && entry.second != entry.first)
      found->second.next =
        b.ite(found->second.sort, guard, entry.second, found->second.next);
  }
}

void logical_arrayst::end()
{
  commit(current_guard, values());
}

void logical_arrayst::finish()
{
  if(!failed)
    for(const auto &entry : updates)
      b.next(entry.second.sort, entry.first, entry.second.next);
}

void logical_arrayst::record_reserved_tag(const irep_idt &id, unsigned tag)
{
  const auto found = arrays.find(id);
  if(found != arrays.end())
    found->second.tag = tag;
}

json_arrayt logical_arrayst::metadata() const
{
  json_arrayt result;
  for(const auto &entry : arrays)
  {
    const auto &array = entry.second;
    json_objectt object;
    object["symbol"] = json_stringt(id2string(array.id));
    object["tag"] = json_numbert(std::to_string(array.tag));
    object["storage"] = json_stringt(
      array.unused   ? "unused"
      : array.native ? "array"
                     : "bitvector");
    object["unused_storage"] = jsont::json_boolean(array.unused);
    object["element_width"] = json_numbert(std::to_string(array.element_width));
    object["source_element_width"] =
      json_numbert(std::to_string(array.source_width));
    object["index_width"] = json_numbert(std::to_string(array.index_width));
    object["rank"] = json_numbert(std::to_string(array.dimensions.size()));
    object["static_lifetime"] = jsont::json_boolean(array.static_lifetime);
    object["semantics"] = json_stringt(
      array.unused ? "unused-element-storage" : "independent-element-storage");
    if(b.contains_node(array.state))
      object["data_state"] = json_numbert(std::to_string(array.state));
    if(array.upper_elements)
      object["upper_elements"] =
        json_numbert(integer2string(*array.upper_elements));
    json_arrayt dimensions;
    for(const auto &dimension : array.dimensions)
    {
      json_objectt info;
      info["width"] = json_numbert(std::to_string(dimension.width));
      if(dimension.state && b.contains_node(dimension.state))
        info["state"] = json_numbert(std::to_string(dimension.state));
      if(
        const auto size =
          numeric_cast<mp_integer>(simplify_expr(dimension.size, ns)))
        info["constant"] = json_numbert(integer2string(*size));
      dimensions.push_back(std::move(info));
    }
    object["dimensions"] = std::move(dimensions);
    result.push_back(std::move(object));
  }
  return result;
}
