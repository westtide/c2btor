// SPDX-License-Identifier: BSD-4-Clause
// SPDX-FileCopyrightText: 2026 C2BTOR contributors

#include "memory_access.h"
#include "automatic_lifetimes.h"

#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/c_types.h>
#include <util/config.h>
#include <util/pointer_expr.h>
#include <util/pointer_offset_size.h>
#include <util/simplify_expr.h>
#include <util/std_code.h>
#include <util/std_expr.h>
#include <util/string_constant.h>
#include <util/symbol.h>
#include <util/symbol_table_base.h>

#include <ansi-c/padding.h>
#include <goto-programs/cfg.h>

#include "btor2_type_utils.h"
#include "expr_to_btor2.h"

#include <algorithm>
#include <iterator>
#include <limits>

namespace
{
bool contains_pointer(const typet &raw_type, const namespacet &ns)
{
  const auto &type = follow_tag_type(raw_type, ns);
  if(type.id() == ID_pointer)
    return true;
  if(type.id() == ID_array)
    return contains_pointer(to_array_type(type).element_type(), ns);
  if(type.id() == ID_struct || type.id() == ID_union)
    for(const auto &field : to_struct_union_type(type).components())
      if(contains_pointer(field.type(), ns))
        return true;
  return false;
}
}

bool is_c_source_object(const symbolt &symbol, const namespacet &ns)
{
  // Frontend bookkeeping and architecture constants are not source C
  // objects. Explicit address-of expressions still collect such symbols.
  const auto file = id2string(symbol.location.get_file());
  return symbol.mode == ID_C && symbol.is_lvalue && !symbol.is_type &&
    !symbol.is_macro && !symbol.is_auxiliary &&
    (file.empty() || file.front() != '<') &&
    follow_tag_type(symbol.type, ns).id() != ID_code;
}

bool has_arbitrary_pointer_input(
  const goto_programt &program, const namespacet &ns)
{
  std::set<irep_idt> initializers;
  std::set<irep_idt> supplied_parameters;
  for(auto instruction = program.instructions.begin();
      instruction != program.instructions.end(); ++instruction)
  {
    if(!instruction->is_decl())
      continue;
    const auto &id = instruction->decl_symbol().get_identifier();
    const auto next = std::next(instruction);
    // Inlining materializes each formal as DECL followed by its actual
    // argument assignment. The actual expression is scanned below; the
    // formal itself is not an additional external address input.
    if(next != program.instructions.end() && next->is_assign() &&
       next->assign_lhs().id() == ID_symbol &&
       to_symbol_expr(next->assign_lhs()).get_identifier() == id)
      supplied_parameters.insert(id);
  }
  const auto arbitrary = [&](const auto &self, const exprt &e) -> bool {
    if(e.id() == ID_side_effect && e.get(ID_statement) == ID_nondet &&
       contains_pointer(e.type(), ns))
      return true;
    const auto &type = follow_tag_type(e.type(), ns);
    if(type.id() == ID_pointer)
    {
      if(e.id() == ID_constant &&
         !to_constant_expr(e).is_null_pointer())
        return true;
      if(e.id() == ID_typecast)
      {
        const auto &operand = to_typecast_expr(e).op();
        const auto &source_type = follow_tag_type(operand.type(), ns);
        if(source_type.id() != ID_pointer && source_type.id() != ID_array &&
           !(operand.is_constant() && to_constant_expr(operand).is_zero()))
          return true;
      }
      // A pointer representation read from memory may have been supplied
      // through byte operations or an aggregate input.
      if(e.id() == ID_dereference || e.id() == ID_member || e.id() == ID_index ||
         e.id() == ID_byte_extract_little_endian ||
         e.id() == ID_byte_extract_big_endian)
        return true;
    }
    if(e.id() == ID_symbol)
    {
      const auto &id = to_symbol_expr(e).get_identifier();
      const symbolt *symbol = nullptr;
      if(!ns.lookup(id, symbol) && symbol)
      {
        if(symbol->is_parameter && !supplied_parameters.count(id) &&
           contains_pointer(symbol->type, ns))
          return true;
        if(symbol->is_static_lifetime && initializers.insert(id).second &&
           symbol->value.is_not_nil() && self(self, symbol->value))
          return true;
      }
    }
    for(const auto &operand : e.operands())
      if(self(self, operand))
        return true;
    return false;
  };
  for(const auto &instruction : program.instructions)
  {
    if(instruction.is_function_call() &&
       instruction.call_function().id() == ID_symbol)
    {
      const auto name = id2string(
        to_symbol_expr(instruction.call_function()).get_identifier());
      if((name.rfind("__VERIFIER_nondet_", 0) == 0 ||
          name.rfind("__CPROVER_nondet_", 0) == 0) &&
         contains_pointer(instruction.call_lhs().type(), ns))
        return true;
    }
    if(arbitrary(arbitrary, instruction.code()) ||
       (instruction.has_condition() &&
        arbitrary(arbitrary, instruction.condition())))
      return true;
  }
  return false;
}

memory_accesst::memory_accesst(
  btor2_buildert &b,
  expr_to_btor2t &e,
  const namespacet &ns,
  messaget &log,
  unsigned budget,
  array_encoding_optionst array_encoding,
  bool enable_logical_arrays)
  : heap(b, ns, budget, array_encoding),
    logical_arrays(b, e, ns, array_encoding, enable_logical_arrays),
    b(b), expressions(e), ns(ns), log(log)
{
}
void memory_accesst::error(const std::string &message)
{
  failed = true;
  log.error() << "Unsupported byte memory: " << message << messaget::eom;
}
void memory_accesst::check_logical_arrays()
{
  if(logical_arrays.failed && !logical_failure_reported)
  {
    logical_failure_reported = true;
    error("logical array: " + logical_arrays.failure_reason);
  }
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
  const symbolt *source_symbol = nullptr;
  const bool promote = e.id() == ID_symbol && promote_unaddressed_objects &&
    !ns.lookup(to_symbol_expr(e).get_identifier(), source_symbol) &&
    source_symbol && is_c_source_object(*source_symbol, ns);
  if(
    e.id() == ID_symbol && (addressed || promote || type.id() == ID_array ||
                            type.id() == ID_struct || type.id() == ID_union))
  {
    const auto id = to_symbol_expr(e).get_identifier();
    const symbolt *symbol = nullptr;
    if(logical_arrays.owns_symbol(id))
    {
      // Classification precedes collection. A logical root has no byte data,
      // but keeps its identity position and its initializer/type dependencies.
      if(addressed || promote)
        error(
          "logical array unexpectedly requires addressable storage: " +
          id2string(id));
      for(auto dimension = type; dimension.id() == ID_array;
          dimension =
            follow_tag_type(to_array_type(dimension).element_type(), ns))
        collect_expr(to_array_type(dimension).size());
    }
    else if(!ns.lookup(id, symbol) && symbol)
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
        // Preserve the runtime size expression. Const qualification does not
        // make assignments from distinct CFG paths or lifetimes interchangeable.
        // Capacity analysis may bound this expression without rewriting it.
        const exprt size_expr = simplify_expr(*size, ns);
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
void memory_accesst::collect(const goto_programt &program)
{
  logical_arrays.collect(program);
  check_logical_arrays();
  if(failed)
    return;
  heap.reserved_root_ids = logical_arrays.symbols();
  promote_unaddressed_objects = has_arbitrary_pointer_input(program, ns);
  for(const auto &ins : program.instructions)
  {
    collect_expr(ins.code());
    if(ins.has_condition())
      collect_expr(ins.condition());
  }
  if(promote_unaddressed_objects)
    for(const auto &entry : ns.get_symbol_table().symbols)
    {
      const auto &symbol = entry.second;
      if(is_c_source_object(symbol, ns) && symbol.is_static_lifetime &&
         (!symbol.is_extern || symbol.value.is_not_nil()))
        collect_expr(symbol.symbol_expr());
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
  // Reserving logical roots preserves other objects' numeric tags and the
  // object/offset split; only their physical byte storage is omitted.
  auto identities = heap.reserved_root_ids;
  for(const auto &entry : heap.objects)
    identities.insert(entry.first);
  unsigned tag = 3;
  for(const auto &id : identities)
  {
    const auto object = heap.objects.find(id);
    if(object != heap.objects.end())
      object->second.tag = tag;
    else
      logical_arrays.record_reserved_tag(id, tag);
    ++tag;
  }
  check_logical_arrays();
  if(failed)
    return;

  // Re-entry needs a storage-reuse certificate. Capacity planning rejects
  // unsupported lifetimes before emission, without altering source properties.
  if(std::any_of(heap.objects.begin(), heap.objects.end(),
       [](const auto &entry) { return !entry.second.static_lifetime; }))
  {
    struct payloadt {};
    cfg_baset<payloadt> cfg;
    cfg(program);
    std::vector<cfg_baset<payloadt>::entryt> components;
    const auto count = cfg.SCCs(components);
    std::vector<std::size_t> sizes(count, 0);
    for(const auto component : components)
      ++sizes[component];
    std::set<irep_idt> declared, memory_objects;
    for(const auto &entry : heap.objects)
      memory_objects.insert(entry.first);
    for(auto instruction = program.instructions.begin();
        instruction != program.instructions.end(); ++instruction)
    {
      if(!instruction->is_decl())
        continue;
      auto object = heap.objects.find(instruction->decl_symbol().get_identifier());
      if(object == heap.objects.end() || object->second.static_lifetime)
        continue;
      const auto node = cfg.get_node_index(instruction);
      object->second.recurrent |= !declared.insert(object->first).second ||
        sizes[components[node]] > 1 || cfg[node].out.count(node) != 0;
    }
    for(auto &entry : heap.objects)
      if(entry.second.recurrent)
      {
        const auto size = numeric_cast<mp_integer>(entry.second.size);
        const auto &symbol = ns.lookup(entry.first);
        const bool internal_snapshot = symbol.is_auxiliary &&
          symbol.type.id() == ID_array &&
          symbol.type.get_bool("C_c2btor_copy_snapshot");
        entry.second.reuse_certified =
          ((size && *size >= 0) || heap.supports_runtime_object_reset()) &&
          automatic_object_reuse_is_safe(
            program, ns, entry.first, memory_objects, internal_snapshot);
      }
  }
  heap.plan_capacity(program);
  if(heap.failed)
    error(heap.failure_reason);
  else if(heap.uses_wide_pointer_offsets())
    validate_wide_pointer_representation(program);
}

bool memory_accesst::check_wide_pointer_expression(const exprt &e)
{
  if(!heap.uses_wide_pointer_offsets())
    return true;
  const auto reject = [&](const std::string &reason) {
    error("wide-offset pointer representation " + reason);
    return false;
  };
  const auto type = follow_tag_type(e.type(), ns);
  if(e.id() == ID_constant && type.id() == ID_pointer &&
     !to_constant_expr(e).is_null_pointer())
    return reject("cannot represent a non-null machine pointer constant");
  if(e.id() == ID_side_effect &&
     (e.get(ID_statement) == ID_nondet || e.get(ID_statement) == ID_va_start) &&
     contains_pointer(e.type(), ns))
    return reject("cannot import arbitrary machine pointer values");
  if(e.id() == ID_typecast)
  {
    const auto &operand = to_typecast_expr(e).op();
    const auto source_type = follow_tag_type(operand.type(), ns);
    const bool from_pointer = source_type.id() == ID_pointer;
    const bool to_pointer = type.id() == ID_pointer;
    const bool to_boolean = type.id() == ID_bool || type.id() == ID_c_bool;
    if(from_pointer && !to_pointer && !to_boolean)
      return reject("cannot export hidden object tags through a scalar cast");
    if(to_pointer && !from_pointer && source_type.id() != ID_array)
    {
      const auto value = simplify_expr(operand, ns);
      if(!value.is_constant() || !to_constant_expr(value).is_zero())
        return reject("cannot import a non-null integer-to-pointer cast");
    }
  }
  if(e.id() == ID_address_of &&
     contains_pointer(to_address_of_expr(e).object().type(), ns))
    return reject("cannot serialize an addressable pointer-bearing object");
  const bool byte_view = e.id() == ID_byte_extract_little_endian ||
                        e.id() == ID_byte_extract_big_endian ||
                        e.id() == ID_byte_update_little_endian ||
                        e.id() == ID_byte_update_big_endian;
  const bool bit_view = e.id() == ID_extractbits || e.id() == ID_concatenation ||
                       e.id() == ID_bswap;
  if(byte_view || bit_view)
  {
    if(contains_pointer(e.type(), ns) ||
       std::any_of(e.operands().begin(), e.operands().end(),
         [&](const exprt &operand) {
           return contains_pointer(operand.type(), ns);
         }))
      return reject("cannot expose pointer values as byte or bit sequences");
  }
  // Checking only the root object's type misses casts such as
  // *(void **)char_buffer. The accessed value itself must fit the C layout.
  if(contains_pointer(e.type(), ns) && owns_lvalue(e))
    return reject("cannot load or store pointer values through byte memory");
  return true;
}

void memory_accesst::validate_wide_pointer_representation(
  const goto_programt &program)
{
  for(const auto &entry : heap.objects)
    if(contains_pointer(entry.second.type, ns))
    {
      error("wide-offset pointer representation cannot serialize "
            "pointer-bearing object " + id2string(entry.first));
      return;
    }
  const auto inspect = [&](const auto &self, const exprt &e) -> void {
    if(failed || !check_wide_pointer_expression(e))
      return;
    for(const auto &operand : e.operands())
      self(self, operand);
  };
  for(const auto &instruction : program.instructions)
  {
    if(instruction.is_function_call() &&
       instruction.call_function().id() == ID_symbol &&
       contains_pointer(instruction.call_lhs().type(), ns))
    {
      const auto name = id2string(
        to_symbol_expr(instruction.call_function()).get_identifier());
      if(name.rfind("__VERIFIER_nondet_", 0) == 0 ||
         name.rfind("__CPROVER_nondet_", 0) == 0)
      {
        error("wide-offset pointer representation cannot import "
              "arbitrary machine pointer values");
        return;
      }
    }
    inspect(inspect, instruction.code());
    if(instruction.has_condition())
      inspect(inspect, instruction.condition());
    if(failed)
      return;
  }
}
bool memory_accesst::owns_symbol(const irep_idt &id) const
{
  if(logical_arrays.owns_symbol(id) || heap.objects.count(id))
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
  if(logical_arrays.owns_lvalue(e))
    return true;
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
  if(!failed)
  {
    logical_arrays.create_states();
    check_logical_arrays();
  }
}
void memory_accesst::initialize_static()
{
  for(const auto &entry : heap.objects)
  {
    const auto &object = entry.second;
    if(!object.static_lifetime || object.type.id() == ID_code)
      continue;
    auto size = numeric_cast<mp_integer>(simplify_expr(object.size, ns));
    const unsigned extent_bits = heap.offset_bits -
      (heap.uses_wide_pointer_offsets() ? 0u : 1u);
    if(!size || *size < 0 || *size >= (mp_integer(1) << extent_bits))
    {
      error("static object size outside representable range");
      continue;
    }
    heap.activate(object, b.constd(heap.size_sort, *size), true);
    if(
      object.initializer.is_not_nil() &&
      !assign_at(
        heap.base(object.tag), object.type, object.initializer, true,
        initial_lvaluet{object.tag, 0}))
      error("static initializer for " + id2string(object.id));
  }
  heap.finish_initialization();
  logical_arrays.initialize_static();
  check_logical_arrays();
}
void memory_accesst::begin(unsigned pc, btor2_nid_t guard)
{
  heap.begin(pc, guard);
  logical_arrays.begin(pc, guard);
  check_logical_arrays();
}
void memory_accesst::end()
{
  heap.end();
  logical_arrays.end();
  check_logical_arrays();
}
void memory_accesst::finish()
{
  heap.finish();
  logical_arrays.finish();
  check_logical_arrays();
}
json_objectt memory_accesst::metadata() const
{
  auto result = heap.metadata();
  auto logical = logical_arrays.metadata();
  if(!logical.empty())
    result["logical_arrays"] = std::move(logical);
  return result;
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
      auto narrow = b.slice(heap.size_sort, full, heap.pointer_bits - 1, 0);
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
  if(!check_wide_pointer_expression(e))
    return 0;
  auto logical = logical_arrays.convert(e);
  check_logical_arrays();
  if(logical.has_value())
    return logical;
  if(logical_arrays.failed)
    return 0;
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
    // Hidden offsets cover the full unsigned machine address domain. Extend
    // them before subtraction, so crossing its sign bit retains the actual
    // byte difference (e.g. 0x80000000 - 0x7fffffff == 1 on ILP32).
    const unsigned arithmetic_bits =
      heap.pointer_bits + (heap.uses_wide_pointer_offsets() ? 1u : 0u);
    const auto arithmetic_sort = b.get_or_create_bitvec_sort(arithmetic_bits);
    const auto widen_offset = [&](btor2_nid_t pointer) {
      return heap.uses_wide_pointer_offsets()
               ? b.uext(arithmetic_sort, heap.offset(pointer),
                   arithmetic_bits - heap.offset_bits)
               : b.sext(arithmetic_sort, heap.offset(pointer),
                   arithmetic_bits - heap.offset_bits);
    };
    auto difference = b.sub(
      arithmetic_sort, widen_offset(left), widen_offset(right));
    auto result = b.sdiv(
      arithmetic_sort, difference, b.constd(arithmetic_sort, *stride));
    auto width = expressions.get_width(e.type());
    if(!width || *width > heap.pointer_bits)
    {
      error("pointer difference width");
      return 0;
    }
    auto sort = expressions.convert_type(e.type());
    auto narrow = *width == arithmetic_bits
                    ? result
                    : b.slice(sort, result, *width - 1, 0);
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
    // CBMC pointer arithmetic retains the object and performs modular offset
    // arithmetic (bv_pointerst::offset_arithmetic).
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
    auto narrow = b.slice(heap.size_sort, full, heap.pointer_bits - 1, 0);
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
      width = heap.object_bits;
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
    if(heap.uses_wide_pointer_offsets() && contains_pointer(e.type(), ns))
    {
      error("wide-offset pointer representation cannot load pointer values "
            "from byte memory");
      return 0;
    }
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
  bool zero_initialized,
  std::optional<initial_lvaluet> initial_location)
{
  if(!p)
    return false;
  auto type = follow_tag_type(raw_type, ns);
  if(heap.uses_wide_pointer_offsets() && contains_pointer(type, ns))
  {
    error("wide-offset pointer representation cannot store pointer values "
          "in byte memory");
    return false;
  }
  const bool aggregate = type.id() == ID_struct || type.id() == ID_union ||
    type.id() == ID_array;
  const bool nondet = rhs.id() == ID_side_effect &&
    rhs.get(ID_statement) == ID_nondet;
  if(aggregate && (nondet || owns_lvalue(rhs)))
  {
    const auto bytes = pointer_offset_size(type, ns);
    if(!bytes || *bytes < 0 ||
       *bytes > std::numeric_limits<int>::max() / heap.byte_bits)
    {
      error("aggregate value needs a fixed layout within BTOR2 bit-vector width");
      return false;
    }
    if(*bytes == 0)
      return true;
    const auto width = numeric_cast_v<unsigned>(*bytes * heap.byte_bits);
    if(owns_lvalue(rhs))
    {
      // Snapshot the complete source representation before updating any
      // destination field. This includes padding and overlapping aliases.
      const auto source = address(rhs);
      if(!source)
        return false;
      heap.store(p, heap.load(source, width), width);
      return true;
    }
    // Padding is a fresh arbitrary part of this aggregate value. Typed
    // fields overwrite this seed below, including canonical C booleans.
    heap.store(
      p, b.input(b.get_or_create_bitvec_sort(width), "__aggregate_nondet"),
      width);
    if(type.id() == ID_union)
      return true;
  }
  const auto fresh_value = [&](const typet &field_type) -> exprt {
    const bool c_boolean = follow_tag_type(field_type, ns).id() == ID_c_bool;
    return typecast_exprt::conditional_cast(
      side_effect_expr_nondett(
        c_boolean ? static_cast<typet>(bool_typet()) : field_type,
        rhs.source_location()), field_type);
  };
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
      exprt value = nondet
        ? fresh_value(field.type())
        : static_cast<exprt>(member_exprt(rhs, field.get_name(), field.type()));
      if(rhs.id() == ID_struct && operand < rhs.operands().size())
        value = rhs.operands()[operand];
      auto q = add_bytes(p, from_integer(*off, size_type()));
      auto child_location = initial_location;
      if(child_location)
        child_location->offset += *off;
      if(!assign_at(q, field.type(), value, zero_initialized, child_location))
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
      exprt value = nondet
        ? fresh_value(array.element_type())
        : static_cast<exprt>(index_exprt(
            rhs, from_integer(i, array.index_type())));
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
      auto child_location = initial_location;
      if(child_location)
        child_location->offset += i * *stride;
      if(!assign_at(
           add_bytes(p, from_integer(i * *stride, size_type())),
           array.element_type(),
           value,
           zero_initialized,
           child_location))
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
  if(!initial_location || !heap.try_initialize_store(
       initial_location->tag, initial_location->offset, value, *width))
    heap.store(p, value, *width);
  return true;
}
bool memory_accesst::assign(const exprt &lhs, const exprt &rhs)
{
  const auto logical = logical_arrays.assign(lhs, rhs);
  check_logical_arrays();
  if(logical || logical_arrays.failed)
    return true;
  if(!owns_lvalue(lhs))
    return false;
  if(!assign_at(address(lhs), lhs.type(), rhs))
    error("assignment could not be lowered");
  return true;
}
void memory_accesst::declaration(const symbol_exprt &symbol, bool dead)
{
  if(logical_arrays.owns_symbol(symbol.get_identifier()))
  {
    logical_arrays.declaration(symbol, dead);
    check_logical_arrays();
    return;
  }
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
  const auto zero_initializer = simplify_expr(allocation.operands()[1], ns);
  return bytes && zero
           ? heap.allocate(
               bytes,
               zero,
               zero_initializer != false && zero_initializer != 0,
               &allocation.operands()[0])
           : 0;
}
