// SPDX-License-Identifier: BSD-4-Clause
// SPDX-FileCopyrightText: 2026 C2BTOR contributors

#include "heap_model.h"

#include <util/arith_tools.h>
#include <util/config.h>
#include <util/invariant.h>
#include <util/json_irep.h>
#include <util/message.h>
#include <util/simplify_expr.h>

#include "goto_btor2_unroll.h"

#include <algorithm>
#include <limits>

heap_modelt::heap_modelt(
  btor2_buildert &builder,
  const namespacet &ns,
  unsigned allocation_budget,
  array_encoding_optionst array_encoding)
  : pointer_bits(config.ansi_c.pointer_width),
    pointer_value_bits(config.ansi_c.pointer_width),
    object_bits(config.bv_encoding.object_bits),
    offset_bits(pointer_bits - object_bits),
    byte_bits(config.ansi_c.char_width),
    b(builder),
    ns(ns),
    array_encoding(array_encoding),
    budget(allocation_budget),
    storage_slots(allocation_budget)
{
}

void heap_modelt::plan_capacity(const goto_programt &program)
{
  if(array_encoding.symbolic_heap_arrays &&
     (!array_encoding.symbolic_heap || !array_encoding.object_memory))
  {
    failed = true;
    failure_reason = "symbolic heap Arrays require symbolic heap and object memory";
    return;
  }
  if((array_encoding.symbolic_heap_wide_offsets ||
      array_encoding.symbolic_heap_bv_array_fallback ||
      array_encoding.symbolic_heap_compact) &&
     !array_encoding.symbolic_heap_arrays)
  {
    failed = true;
    failure_reason = "wide symbolic offsets and BV Array fallback require symbolic heap Arrays";
    return;
  }
  if(object_bits == 0 ||
     (!array_encoding.symbolic_heap_wide_offsets &&
      object_bits + 1 >= pointer_bits))
  {
    failed = true;
    failure_reason = "unsupported object/offset pointer widths";
    return;
  }
  // Static initialization runs before the CFG. Do not apply a CFG-only bound
  // if an initializer can itself allocate (ordinary C initializers cannot).
  auto allocates = [&](const auto &self, const exprt &expr) -> bool
  {
    if(expr.id() == ID_side_effect && expr.get(ID_statement) == ID_allocate)
      return true;
    return std::any_of(
      expr.operands().begin(),
      expr.operands().end(),
      [&](const exprt &operand) { return self(self, operand); });
  };
  const bool initializer_allocates = std::any_of(
    objects.begin(),
    objects.end(),
    [&](const auto &entry)
    {
      return entry.second.static_lifetime &&
             allocates(allocates, entry.second.initializer);
    });
  if(initializer_allocates)
  {
    failed = true;
    failure_reason = "allocation in a static initializer is not supported";
    return;
  }
  // A path with no allocating cycle cannot execute more allocate nodes than
  // occur syntactically. Use that finite saturation threshold for cycle
  // detection, independently of the pointer tag width or a CLI budget.
  bool slot_count_outside_representation = false;
  mp_integer capacity_observed_weight = 0;
  unsigned capacity_allocation_sites = 0;
  const auto finite_slots =
    [&](const goto_programt &body) -> std::optional<unsigned>
  {
    mp_integer total_weight = 0;
    for(const auto &instruction : body.instructions)
      total_weight += allocation_evaluation_weight(instruction);
    // The fresh-identity implementation and its object tags use unsigned IDs.
    // A larger bound is a representation limit, not an analysis unwind budget.
    if(total_weight >= std::numeric_limits<unsigned>::max())
    {
      slot_count_outside_representation = true;
      capacity_observed_weight = total_weight;
      return std::nullopt;
    }
    const unsigned total = numeric_cast_v<unsigned>(total_weight);
    capacity_allocation_sites = total;
    const auto bound = infer_allocation_slots(body, total + 1);
    return bound <= total ? std::optional<unsigned>(bound) : std::nullopt;
  };
  auto slots = has_dynamic_allocations ? finite_slots(program)
                                       : std::optional<unsigned>(0);
  if(!slots)
  {
    // Only the sizing copy is summarized; emitted loops and PC stay unchanged.
    goto_programt sizing_program;
    sizing_program.copy_from(program);
    null_message_handlert handler;
    messaget quiet(handler);
    if(unroll_malloc_counted_loops(sizing_program, ns, quiet))
      slots = finite_slots(sizing_program);
  }
  if(!slots || (budget && *slots > budget))
  {
    failed = true;
    failure_reason =
      slot_count_outside_representation
        ? "allocation count " + integer2string(capacity_observed_weight) +
          " exceeds the unsigned fresh-identity representation"
      : slots
        ? "finite allocation count " + std::to_string(*slots) +
          " exceeds the explicit --goto-btor2-heap-objects limit " +
          std::to_string(budget)
        : "cannot establish a finite allocation count for fresh identities; "
          "an allocating cycle remains in the capacity analysis (" +
          std::to_string(capacity_allocation_sites) + " allocation sites)";
    return;
  }
  storage_slots = *slots;
  // Static roots, dynamic identities, reserved tags, and the final fresh
  // counter value all need distinct encodings. The default 8 bits is not a
  // limit on the number of C objects. Keep the target pointer byte width.
  const mp_integer largest_tag =
    mp_integer(static_identity_count()) + 3 + storage_slots;
  if(config.bv_encoding.is_object_bits_default)
  {
    object_bits = 1;
    while((mp_integer(1) << object_bits) <= largest_tag)
      ++object_bits;
  }
  std::map<irep_idt, exprt> sizes;
  for(const auto &entry : objects)
    sizes.emplace(entry.first, entry.second.size);
  capacity_bounds = infer_memory_capacity(program, ns, sizes);
  // Widen only when the old offset domain cannot hold the allocation extent.
  // Ordinary bounded allocations retain their existing machine-pointer bytes
  // and serialization rules even when symbolic-heap support is enabled.
  const mp_integer narrow_limit = object_bits + 1 >= pointer_bits
                                    ? mp_integer(0)
                                    : (mp_integer(1) <<
                                       (pointer_bits - object_bits - 1)) - 1;
  const bool wide_offsets = array_encoding.symbolic_heap_wide_offsets &&
    has_dynamic_allocations &&
    (!capacity_bounds.allocation_complete ||
     capacity_bounds.allocation > narrow_limit);
  if(
    (!wide_offsets && object_bits + 1 >= pointer_bits) ||
    largest_tag >= (mp_integer(1) << object_bits))
  {
    failed = true;
    failure_reason =
      "object identities do not fit the target pointer representation";
    return;
  }
  offset_bits = wide_offsets ? pointer_bits : pointer_bits - object_bits;
  pointer_value_bits = object_bits + offset_bits;
  budget = storage_slots;
  storage_slots_policy = "cfg-path-bound";
  const bool has_symbolic_size = std::any_of(
    capacity_bounds.allocation_sizes.begin(),
    capacity_bounds.allocation_sizes.end(),
    [](const memory_capacity_boundst::allocation_size_infot &site)
    { return !site.interval || site.interval->first != site.interval->second; });
  // Keep exact constant capacities and Mixed's certified small bound path.
  // A fresh slot can receive different source allocation sites, so an admitted
  // symbolic representation applies to every dynamic slot in this program.
  symbolic_allocation_storage = array_encoding.symbolic_heap_arrays &&
    ((has_symbolic_size && !array_encoding.bitvectors &&
      (!array_encoding.mixed || !capacity_bounds.allocation_complete ||
       capacity_bounds.allocation * byte_bits >
         mp_integer(array_encoding.mixed_threshold_bits))) ||
     (array_encoding.bitvectors && array_encoding.symbolic_heap_bv_array_fallback &&
      has_dynamic_allocations &&
      (!capacity_bounds.allocation_complete || has_symbolic_size ||
       capacity_bounds.allocation > representation_capacity())));
  if(array_encoding.symbolic_heap_compact && symbolic_allocation_storage)
  {
    symbolic_cells = certify_symbolic_heap_cells(program, ns);
    if(symbolic_cells.word64 && offset_bits <= 3)
    {
      symbolic_cells.word64 = false;
      symbolic_cells.reason =
        "object offset domain is too narrow for an indexed 64-bit cell";
    }
  }
  if(has_dynamic_allocations && !capacity_bounds.allocation_complete &&
     !symbolic_allocation_storage)
  {
    failed = true;
    failure_reason = "cannot determine storage size for an allocation";
    return;
  }
  const mp_integer pointer_limit =
    (mp_integer(1) << (offset_bits - (wide_offsets ? 0 : 1))) - 1;
  auto supported = [&](const mp_integer &bytes, const std::string &what,
                       bool native_symbolic = false)
  {
    mp_integer limit = pointer_limit;
    if(array_encoding.bitvectors && !native_symbolic)
      limit = std::min(limit, mp_integer(representation_capacity()));
    if(bytes < 0 || bytes > limit)
    {
      failed = true;
      failure_reason =
        what + " upper bound " + integer2string(bytes) + " bytes exceeds " +
        (bytes > pointer_limit ? (wide_offsets ? "the object-offset range ("
                                              : "the signed object-offset range (")
                               : "the packed bitvector width limit (") +
        integer2string(limit) + " bytes)";
    }
    if(
      array_encoding.max_object_bytes &&
      bytes > *array_encoding.max_object_bytes)
    {
      failed = true;
      failure_reason = what + " exceeds the explicit storage limit";
    }
  };
  for(const auto &entry : objects)
  {
    const auto &object = entry.second;
    if(object.recurrent && !object.reuse_certified)
    {
      failed = true;
      failure_reason =
        "automatic object re-entry needs an unsupported fresh "
        "identity: " +
        id2string(entry.first);
      return;
    }
    if(!numeric_cast<mp_integer>(simplify_expr(object.size, ns)))
    {
      const auto found = capacity_bounds.objects.find(entry.first);
      if(found == capacity_bounds.objects.end())
      {
        failed = true;
        failure_reason = "no storage size bound for " + id2string(entry.first);
        return;
      }
      supported(found->second, "runtime object " + id2string(entry.first));
    }
  }
  if(has_dynamic_allocations)
    supported(
      capacity_bounds.allocation_complete
        ? capacity_bounds.allocation
        : (mp_integer(1) << pointer_bits) - 1,
      "allocation size",
      symbolic_allocation_storage);
}

std::size_t heap_modelt::representation_capacity() const
{
  // Packed BV storage has a format width limit. Native arrays only need an
  // index sort; their logical byte extent is not a packed bitvector width.
  const mp_integer pointer_limit =
    (mp_integer(1) << (offset_bits - (uses_wide_pointer_offsets() ? 0 : 1))) - 1;
  const mp_integer width_limit =
    array_encoding.bitvectors
      ? mp_integer(std::numeric_limits<int>::max() / byte_bits)
      : pointer_limit;
  return numeric_cast_v<std::size_t>(std::min(pointer_limit, width_limit));
}

mp_integer heap_modelt::object_capacity(const objectt &object) const
{
  const auto fixed = numeric_cast<mp_integer>(simplify_expr(object.size, ns));
  if(fixed)
    return *fixed;
  if(array_encoding.max_object_bytes)
    return *array_encoding.max_object_bytes;
  const auto found = capacity_bounds.objects.find(object.id);
  // plan_capacity rejects missing bounds. Never clamp or round down a bound:
  // that would silently drop bytes of an admitted object. The backing builder
  // checks the rounded cell width and rejects representations that do not fit.
  INVARIANT(
    found != capacity_bounds.objects.end(), "runtime object size bound");
  return found->second;
}

std::size_t heap_modelt::allocation_capacity() const
{
  if(array_encoding.max_object_bytes)
    return *array_encoding.max_object_bytes;
  return numeric_cast_v<std::size_t>(capacity_bounds.allocation);
}

heap_modelt::updatet &heap_modelt::update(btor2_nid_t state)
{
  for(auto &u : updates)
    if(u.state == state)
      return u;
  UNREACHABLE;
}

void heap_modelt::create_states()
{
  if(failed)
    return;
  if(object_bits == 0 || object_bits + offset_bits != pointer_value_bits)
  {
    failed = true;
    return;
  }
  bool_sort = b.get_bool_sort();
  pointer_sort = b.get_or_create_bitvec_sort(pointer_value_bits);
  size_sort = b.get_or_create_bitvec_sort(pointer_bits);
  offset_sort = b.get_or_create_bitvec_sort(offset_bits);
  tag_sort = b.get_or_create_bitvec_sort(object_bits);
  byte_sort = b.get_or_create_bitvec_sort(byte_bits);
  first_heap_tag = static_cast<unsigned>(static_identity_count()) + 3;
  // Leave room for the exhausted counter value as well as all live identities.
  if(mp_integer(first_heap_tag) + budget >= (mp_integer(1) << object_bits))
  {
    failed = true;
    return;
  }
  auto state = [&](btor2_nid_t sort, const char *name, btor2_nid_t initial)
  {
    auto s = b.state(sort, name);
    if(initial)
      b.init(sort, s, initial);
    updates.push_back({sort, s, s, s});
    return s;
  };
  if(array_encoding.object_memory)
  {
    create_object_states();
    if(failed)
      return;
  }
  else
  {
    const std::size_t object_slots =
      static_cast<std::size_t>(first_heap_tag) + storage_slots;
    if(array_encoding.bitvectors)
    {
      if(
        object_slots >
        static_cast<std::size_t>(std::numeric_limits<int>::max()) /
          pointer_bits)
      {
        failed = true;
        failure_reason =
          "--array bv object metadata exceeds representable width";
        return;
      }
      if(!prepare_packed_objects())
        return;
      memory_sort = b.get_or_create_bitvec_sort(packed_bytes * byte_bits);
      flags_sort = b.get_or_create_bitvec_sort(object_slots);
      sizes_sort = b.get_or_create_bitvec_sort(object_slots * pointer_bits);
    }
    else
    {
      memory_sort = b.sort_array(pointer_sort, byte_sort);
      written_sort = b.sort_array(pointer_sort, bool_sort);
      flags_sort = b.sort_array(tag_sort, bool_sort);
      sizes_sort = b.sort_array(tag_sort, size_sort);
    }
    memory = state(memory_sort, "__initial_memory_bytes", 0);
    const auto flags_zero = array_encoding.bitvectors ? flags_sort : bool_sort;
    const auto sizes_zero =
      array_encoding.bitvectors ? sizes_sort : size_sort;
    if(uses_lazy_zero_initialization())
    {
      // A flat native Array cannot replace a whole object's address range
      // atomically. These two states implement its lazy zero data value;
      // they do not track validity or create an additional property.
      written =
        state(written_sort, "__initial_memory_written", b.zero(bool_sort));
      zeroed = state(flags_sort, "__initial_object_zeroed", b.zero(bool_sort));
    }
    live = state(flags_sort, "__initial_object_live", b.zero(flags_zero));
    sizes = state(sizes_sort, "__initial_object_size", b.zero(sizes_zero));
    readonly =
      state(flags_sort, "__initial_object_readonly", b.zero(flags_zero));
    if(array_encoding.bitvectors)
    {
      packed_arrays.emplace(
        memory, packed_arrayt{byte_bits, packed_bytes, true});
      for(auto s : {live, readonly})
        packed_arrays.emplace(s, packed_arrayt{1, object_slots, false});
      packed_arrays.emplace(
        sizes, packed_arrayt{pointer_bits, object_slots, false});
    }
    for(const auto s : {memory, written, live, zeroed, sizes, readonly})
      if(s)
        b.next(update(s).sort, s, s);
  }
  fresh =
    state(tag_sort, "__next_heap_object", b.constd(tag_sort, first_heap_tag));
  path_guard = b.one(bool_sort);
  initial_path_guard = path_guard;
  initializing = true;
}

void heap_modelt::finish_initialization()
{
  initializing = false;
  std::vector<btor2_nid_t *> states;
  if(array_encoding.object_memory)
  {
    for(auto &object : local_objects)
      for(auto &field : object.fields)
        if(field)
          states.push_back(&field);
  }
  else
  {
    states = {&memory, &live, &sizes, &readonly};
    if(uses_lazy_zero_initialization())
    {
      states.push_back(&written);
      states.push_back(&zeroed);
    }
  }
  for(auto *s : states)
  {
    auto &u = update(*s);
    if(deferred_initial_next.erase(*s))
    {
      // A fresh dynamic slot has no static initializer effects. Its existing
      // arbitrary data and zero metadata can be the runtime state directly.
      if(u.local == u.state)
        continue;
      // If an initializer did modify this field, preserve the seed and old
      // initialization pipeline rather than assuming it was untouched.
      b.next(u.sort, u.state, u.state);
    }
    auto state = b.state(u.sort, "__memory_state_" + std::to_string(*s));
    b.memory_init(u.sort, state, u.local);
    if(array_encoding.bitvectors && !array_encoding.object_memory)
      packed_arrays.emplace(state, packed_arrays.at(*s));
    u.state = u.local = u.next = state;
    *s = state;
  }
}

btor2_nid_t heap_modelt::base(unsigned t)
{
  const auto result = b.constd(pointer_sort, mp_integer(t) << offset_bits);
  pointer_tags[result] = {mp_integer(t)};
  return result;
}
btor2_nid_t heap_modelt::tag(btor2_nid_t p)
{
  const auto result = b.slice(tag_sort, p, pointer_value_bits - 1, offset_bits);
  const auto known = pointer_tags.find(p);
  if(known != pointer_tags.end())
    identity_tags[result] = known->second;
  return result;
}

bool heap_modelt::may_select_object(
  btor2_nid_t term,
  unsigned identity,
  bool pointer) const
{
  const auto &known = pointer ? pointer_tags : identity_tags;
  const auto found = known.find(term);
  return found == known.end() || found->second.count(mp_integer(identity));
}

btor2_nid_t heap_modelt::byte_address(btor2_nid_t p, unsigned delta)
{
  if(uses_wide_pointer_offsets())
    return add_offset(p, b.constd(size_sort, delta));
  const auto result = b.add(pointer_sort, p, b.constd(pointer_sort, delta));
  const auto known = pointer_tags.find(p);
  if(known != pointer_tags.end())
  {
    // This is full-pointer modular addition, unlike add_offset below. Keep
    // both possible carries out of the offset, including tag wraparound.
    // Thus dispatch pruning is valid even for invalid/out-of-range pointers;
    // it does not assume that a preceding access guard has succeeded.
    const mp_integer offset_modulus = mp_integer(1) << offset_bits;
    const mp_integer tag_modulus = mp_integer(1)
                                   << (pointer_bits - offset_bits);
    const mp_integer advance = mp_integer(delta) / offset_modulus;
    const bool may_carry = mp_integer(delta) % offset_modulus != 0;
    auto &tags = pointer_tags[result];
    for(const auto &identity : known->second)
    {
      tags.insert((identity + advance) % tag_modulus);
      if(may_carry)
        tags.insert((identity + advance + 1) % tag_modulus);
    }
  }
  return result;
}
btor2_nid_t heap_modelt::offset(btor2_nid_t p)
{
  return b.slice(offset_sort, p, offset_bits - 1, 0);
}
btor2_nid_t heap_modelt::size(btor2_nid_t p)
{
  return read_field(fieldt::size, tag(p));
}
btor2_nid_t heap_modelt::is_live(btor2_nid_t p)
{
  return read_field(fieldt::live, tag(p));
}
btor2_nid_t heap_modelt::is_dynamic(btor2_nid_t p)
{
  auto t = tag(p);
  return b.land(
    bool_sort,
    b.ugte(bool_sort, t, b.constd(tag_sort, first_heap_tag)),
    b.ult(bool_sort, t, fresh));
}

void heap_modelt::begin(unsigned pc, btor2_nid_t guard)
{
  current_pc = pc;
  current_guard = guard;
  path_guard = b.one(bool_sort);
  for(auto &u : updates)
    u.local = u.state;
}

void heap_modelt::end()
{
  for(auto &u : updates)
    if(u.local != u.state)
      u.next = b.ite(u.sort, current_guard, u.local, u.next);
  current_guard = 0;
}

void heap_modelt::finish()
{
  for(const auto &u : updates)
    b.next(u.sort, u.state, u.next);
}

btor2_nid_t heap_modelt::add_offset(btor2_nid_t p, btor2_nid_t delta)
{
  // Match CBMC's object-preserving modular offset arithmetic.
  const auto narrowed = b.add(
    offset_sort, offset(p), b.slice(offset_sort, delta, offset_bits - 1, 0));
  const auto result = b.concat(pointer_sort, tag(p), narrowed);
  const auto known = pointer_tags.find(p);
  if(known != pointer_tags.end())
    pointer_tags[result] = known->second;
  return result;
}
btor2_nid_t heap_modelt::accessible(btor2_nid_t p, btor2_nid_t n, bool write)
{
  if(uses_wide_pointer_offsets())
  {
    const auto wide_sort = b.get_or_create_bitvec_sort(pointer_bits + 1);
    const auto end = b.add(
      wide_sort,
      b.uext(wide_sort, offset(p), 1),
      b.uext(wide_sort, n, 1));
    const auto result = b.land(
      bool_sort,
      is_live(p),
      b.ulte(bool_sort, end, b.uext(wide_sort, size(p), 1)));
    return write
             ? b.land(bool_sort, result,
                      b.lnot(bool_sort, read_field(fieldt::readonly, tag(p))))
             : result;
  }
  auto off = b.sext(pointer_sort, offset(p), pointer_bits - offset_bits);
  auto sz = size(p);
  auto result = b.land(
    bool_sort,
    is_live(p),
    b.land(
      bool_sort,
      b.sgte(bool_sort, off, b.zero(pointer_sort)),
      b.land(
        bool_sort,
        b.ugte(bool_sort, sz, n),
        b.ulte(bool_sort, off, b.sub(pointer_sort, sz, n)))));
  return write ? b.land(
                   bool_sort,
                   result,
                   b.lnot(bool_sort, read_field(fieldt::readonly, tag(p))))
               : result;
}
btor2_nid_t heap_modelt::byte_value(btor2_nid_t p)
{
  if(!uses_lazy_zero_initialization())
    return read_field(fieldt::data, p);
  auto initialized = read_field(fieldt::written, p);
  auto zero = read_field(fieldt::zeroed, tag(p));
  // Initial object bytes are arbitrary state, stable until overwritten.
  // Lazy zero initialization applies only to unwritten static/calloc bytes.
  return b.ite(
    byte_sort,
    b.land(bool_sort, b.lnot(bool_sort, initialized), zero),
    b.zero(byte_sort),
    read_field(fieldt::data, p));
}
btor2_nid_t heap_modelt::load(btor2_nid_t p, unsigned bits)
{
  const unsigned bytes = (bits + byte_bits - 1) / byte_bits;
  btor2_nid_t result = use_bv_word_access()      ? load_bv_word(p, bytes)
                       : use_array_word_access() ? load_array_word(p, bytes)
                                                 : 0;
  for(unsigned i = 0;
      !use_bv_word_access() && !use_array_word_access() && i < bytes;
      ++i)
  {
    auto address = byte_address(p, i);
    auto value = byte_value(address);
    if(!result)
      result = value;
    else
    {
      auto sort = b.get_or_create_bitvec_sort((i + 1) * byte_bits);
      result =
        config.ansi_c.endianness == configt::ansi_ct::endiannesst::IS_BIG_ENDIAN
          ? b.concat(sort, result, value)
          : b.concat(sort, value, result);
    }
  }
  if(bits != bytes * byte_bits)
    result = b.slice(b.get_or_create_bitvec_sort(bits), result, bits - 1, 0);
  return result;
}
void heap_modelt::store(btor2_nid_t p, btor2_nid_t value, unsigned bits)
{
  const unsigned bytes = (bits + byte_bits - 1) / byte_bits;
  if(bits != bytes * byte_bits)
    value = b.uext(
      b.get_or_create_bitvec_sort(bytes * byte_bits),
      value,
      bytes * byte_bits - bits);
  if(use_bv_word_access())
  {
    store_bv_word(p, value, bytes);
    return;
  }
  if(use_array_word_access())
  {
    store_array_word(p, value, bytes);
    return;
  }
  for(unsigned i = 0; i < bytes; ++i)
  {
    auto address = byte_address(p, i);
    const unsigned part =
      config.ansi_c.endianness == configt::ansi_ct::endiannesst::IS_BIG_ENDIAN
        ? bytes - 1 - i
        : i;
    auto byte =
      b.slice(byte_sort, value, (part + 1) * byte_bits - 1, part * byte_bits);
    write_meta(fieldt::data, address, byte);
    if(uses_lazy_zero_initialization())
      write_meta(fieldt::written, address, b.one(bool_sort));
  }
}
void heap_modelt::copy_byte(btor2_nid_t destination, btor2_nid_t source)
{
  const auto value = byte_value(source);
  write_meta(fieldt::data, destination, value);
  if(uses_lazy_zero_initialization())
    write_meta(fieldt::written, destination, b.one(bool_sort));
}
btor2_nid_t heap_modelt::allocate(
  btor2_nid_t bytes,
  btor2_nid_t zero,
  bool may_zero_initialize,
  const exprt *alloc_size_expr)
{
  const auto identity = update(fresh).local;
  json_objectt site;
  site["pc"] = json_numbert(std::to_string(current_pc));
  site["size_node"] = json_numbert(std::to_string(bytes));
  site["zero_initialize_node"] = json_numbert(std::to_string(zero));
  site["object_counter_state"] = json_numbert(std::to_string(fresh));
  if(array_encoding.symbolic_heap && alloc_size_expr)
  {
    site["alloc_size_expr"] =
      json_irept(false).convert_from_irep(*alloc_size_expr);
    site["size_snapshot_width"] = json_numbert(std::to_string(pointer_bits));
    site["size_semantics"] = json_stringt("allocation-time-snapshot");
  }
  allocation_sites.push_back(std::move(site));
  write_meta(fieldt::live, identity, b.one(bool_sort));
  write_meta(fieldt::size, identity, bytes);
  if(!uses_lazy_zero_initialization())
  {
    if(may_zero_initialize)
      initialize_object_data(identity, zero);
  }
  else
    write_meta(fieldt::zeroed, identity, zero);
  update(fresh).local = b.ite(
    tag_sort, path_guard, b.add(tag_sort, identity, b.one(tag_sort)), identity);
  return b.concat(pointer_sort, identity, b.zero(offset_sort));
}
void heap_modelt::deallocate(btor2_nid_t p)
{
  // The lowered release event updates the object's lifetime. NULL is a no-op.
  // Source checks of dynamic/base/live status remain independent predicates;
  // do not silently turn their failure into suppression of this event.
  auto nonnull = b.neq(bool_sort, p, b.zero(pointer_sort));
  auto previous = path_guard;
  path_guard = b.land(bool_sort, previous, nonnull);
  write_meta(fieldt::live, tag(p), b.zero(bool_sort));
  path_guard = previous;
}
void heap_modelt::activate(const objectt &o, btor2_nid_t bytes, bool zero)
{
  const auto t = known_identity(o.tag);
  if(o.recurrent)
    reset_automatic_object(o);
  write_meta(fieldt::live, t, b.one(bool_sort));
  write_meta(fieldt::size, t, bytes);
  if(!uses_lazy_zero_initialization())
  {
    if(zero)
      initialize_object_data(t, b.one(bool_sort));
  }
  else
    write_meta(fieldt::zeroed, t, zero ? b.one(bool_sort) : b.zero(bool_sort));
  write_meta(
    fieldt::readonly, t, o.read_only ? b.one(bool_sort) : b.zero(bool_sort));
}
void heap_modelt::deactivate(const objectt &o)
{
  write_meta(fieldt::live, known_identity(o.tag), b.zero(bool_sort));
}
btor2_nid_t heap_modelt::known_identity(unsigned tag)
{
  const auto identity = b.constd(tag_sort, tag);
  // Lifetime events name one object. Preserve this fact for object-local
  // dispatch just as for activation, instead of updating every object's live.
  identity_tags[identity] = {mp_integer(tag)};
  return identity;
}
json_objectt heap_modelt::metadata() const
{
  json_objectt result;
  result["representation"] = json_stringt(
    array_encoding.object_memory ? "object-local-memory-v1"
                                 : "object-byte-memory-v1");
  result["memory_encoding"] =
    json_stringt(array_encoding.object_memory ? "object" : "global");
  result["array_encoding"] = json_stringt(
    array_encoding.mixed        ? "mixed"
    : array_encoding.bitvectors ? "bv"
                                : "array");
  if(array_encoding.mixed)
    result["array_mixed_threshold_bits"] =
      json_numbert(std::to_string(array_encoding.mixed_threshold_bits));
  result["initialization_semantics"] = json_stringt("stable-arbitrary-bytes");
  result["initialization_representation"] = json_stringt(
    uses_lazy_zero_initialization() ? "lazy-global-array" : "direct-data");
  if(array_encoding.object_memory)
  {
    result["max_object_bytes"] =
      array_encoding.max_object_bytes
        ? jsont(json_numbert(std::to_string(*array_encoding.max_object_bytes)))
        : jsont(json_nullt());
    json_arrayt layout;
    for(const auto &object : local_objects)
    {
      json_objectt entry;
      entry["tag"] = json_numbert(std::to_string(object.tag));
      entry["capacity_bytes"] =
        object.symbolic_capacity
          ? jsont(json_nullt())
          : jsont(json_numbert(std::to_string(object.capacity)));
      if(array_encoding.mixed)
        entry["capacity_bits"] =
          object.symbolic_capacity
            ? jsont(json_nullt())
            : jsont(json_numbert(
                integer2string(mp_integer(object.capacity) * byte_bits)));
      entry["element_bits"] =
        json_numbert(std::to_string(object.element_bytes * byte_bits));
      entry["elements"] =
        object.symbolic_capacity
          ? jsont(json_nullt())
          : jsont(json_numbert(std::to_string(object.elements)));
      if(object.symbolic_capacity)
      {
        entry["capacity_semantics"] =
          json_stringt("allocation-size-snapshot");
        entry["index_domain"] = json_stringt("fixed-bitvector-domain");
      }
      entry["index_bits"] = json_numbert(std::to_string(object.index_bits));
      entry["data_encoding"] =
        json_stringt(object.native_array ? "array" : "bv");
      entry["bitmap_encoding"] = json_stringt("none");
      const char *names[] = {"data", "live", "size", "readonly"};
      json_objectt states;
      for(std::size_t i = 0; i < object.fields.size(); ++i)
        if(object.fields[i] && b.contains_node(object.fields[i]))
          states[names[i]] = json_numbert(std::to_string(object.fields[i]));
      entry["states"] = std::move(states);
      layout.push_back(std::move(entry));
    }
    result["object_storage"] = std::move(layout);
  }
  else if(array_encoding.bitvectors)
  {
    result["max_object_bytes"] =
      array_encoding.max_object_bytes
        ? jsont(json_numbert(std::to_string(*array_encoding.max_object_bytes)))
        : jsont(json_nullt());
    result["packed_bytes"] = json_numbert(std::to_string(packed_bytes));
    json_arrayt layout;
    for(const auto &object : packed_objects)
    {
      json_objectt entry;
      entry["tag"] = json_numbert(std::to_string(object.tag));
      entry["byte_start"] = json_numbert(std::to_string(object.start));
      entry["capacity_bytes"] = json_numbert(std::to_string(object.capacity));
      layout.push_back(std::move(entry));
    }
    result["packed_layout"] = std::move(layout);
  }
  json_arrayt automatic_objects;
  // plan_capacity rejects uncertified re-entry before any state is emitted,
  // so emitted models only contain certified storage reuse.
  for(const auto &entry : objects)
    if(entry.second.recurrent && entry.second.reuse_certified)
    {
      json_objectt object;
      object["symbol"] = json_stringt(id2string(entry.first));
      object["semantics"] = json_stringt("certified-local-storage-reuse");
      automatic_objects.push_back(std::move(object));
    }
  if(!automatic_objects.empty())
    result["automatic_lifetimes"] = std::move(automatic_objects);
  result["allocation_budget"] = json_numbert(std::to_string(budget));
  result["allocation_storage_slots"] =
    json_numbert(std::to_string(storage_slots));
  result["allocation_storage_policy"] = json_stringt(storage_slots_policy);
  if(array_encoding.symbolic_heap)
  {
    json_objectt symbolic;
    symbolic["size_snapshot_width"] =
      json_numbert(std::to_string(pointer_bits));
    symbolic["size_semantics"] = json_stringt("allocation-time-snapshot");
    symbolic["allocation_count_analysis"] =
      json_stringt("unchanged-cfg-path-bound");
    symbolic["native_array_storage"] =
      jsont::json_boolean(symbolic_allocation_storage);
    symbolic["wide_pointer_offsets"] =
      jsont::json_boolean(uses_wide_pointer_offsets());
    symbolic["bv_array_fallback_enabled"] =
      jsont::json_boolean(array_encoding.symbolic_heap_bv_array_fallback);
    if(array_encoding.symbolic_heap_compact)
    {
      symbolic["compact_enabled"] = jsont::json_boolean(true);
      symbolic["word64_certified"] = jsont::json_boolean(symbolic_cells.word64);
      symbolic["cell_certificate_accesses"] =
        json_numbert(std::to_string(symbolic_cells.accesses));
      symbolic["cell_certificate_reason"] = json_stringt(symbolic_cells.reason);
    }
    json_arrayt expressions;
    for(const auto &site : capacity_bounds.allocation_sizes)
    {
      json_objectt entry;
      entry["alloc_size_expr"] =
        json_irept(false).convert_from_irep(site.alloc_size_expr);
      entry["symbolic"] = jsont::json_boolean(
        !site.interval || site.interval->first != site.interval->second);
      if(site.interval)
      {
        entry["lower_bytes"] =
          json_numbert(integer2string(site.interval->first));
        entry["upper_bytes"] =
          json_numbert(integer2string(site.interval->second));
      }
      expressions.push_back(std::move(entry));
    }
    symbolic["allocation_expressions"] = std::move(expressions);
    result["symbolic_heap"] = std::move(symbolic);
  }
  result["first_heap_tag"] = json_numbert(std::to_string(first_heap_tag));
  if(!reserved_root_ids.empty())
  {
    result["static_identity_count"] =
      json_numbert(std::to_string(static_identity_count()));
    json_arrayt reserved;
    for(const auto &id : reserved_root_ids)
      reserved.push_back(json_stringt(id2string(id)));
    result["reserved_logical_array_identities"] = std::move(reserved);
  }
  if(!array_encoding.object_memory && b.contains_node(memory))
    result["memory_state"] = json_numbert(std::to_string(memory));
  result["byte_width"] = json_numbert(std::to_string(byte_bits));
  if(array_encoding.object_memory || array_encoding.bitvectors)
  {
    result["capacity_policy"] =
      json_stringt(array_encoding.max_object_bytes ? "explicit" : "automatic");
    result["representation_capacity_bytes"] =
      json_numbert(std::to_string(representation_capacity()));
    result["allocation_capacity_bytes"] =
      symbolic_allocation_storage
        ? jsont(json_nullt())
        : jsont(json_numbert(std::to_string(allocation_capacity())));
  }
  else
    result["capacity_policy"] = json_stringt("pointer-addressed");
  result["object_id_width"] = json_numbert(std::to_string(object_bits));
  result["pointer_width"] = json_numbert(std::to_string(pointer_bits));
  if(uses_wide_pointer_offsets())
    result["internal_pointer_width"] =
      json_numbert(std::to_string(pointer_value_bits));
  result["offset_width"] = json_numbert(std::to_string(offset_bits));
  // Empty compatibility fields for existing witness readers. No hidden
  // queries, diagnostic bads, or memory-dependent execution gating exist.
  result["proof_obligations"] = json_arrayt{};
  result["frozen_on_violation"] = jsont::json_boolean(false);
  result["allocation_sites"] = allocation_sites;
  result["properties"] = json_arrayt{};
  json_arrayt roots;
  for(const auto &p : objects)
  {
    json_objectt root;
    root["symbol"] = json_stringt(id2string(p.first));
    root["tag"] = json_numbert(std::to_string(p.second.tag));
    roots.push_back(std::move(root));
  }
  result["objects"] = std::move(roots);
  return result;
}

// Compact only the storage, never the C pointer representation. Each object
// retains its identity, runtime size, lifetime, and byte/alias semantics.
bool heap_modelt::prepare_packed_objects()
{
  auto reject = [&](const std::string &reason)
  {
    failed = true;
    failure_reason = reason;
    return false;
  };
  auto append = [&](unsigned identity, const mp_integer &capacity)
  {
    // BTOR2 parser widths are signed 32-bit. Check before narrowing or adding.
    const auto max_bits = std::numeric_limits<int>::max();
    if(
      capacity < 0 || capacity >= (mp_integer(1) << (offset_bits - 1)) ||
      capacity > max_bits / byte_bits ||
      mp_integer(packed_bytes) + capacity > max_bits / byte_bits)
      return reject(
        "--array bv object/storage capacity exceeds representable width");
    const auto count = numeric_cast_v<std::size_t>(capacity);
    packed_objects.push_back({identity, packed_bytes, count});
    packed_bytes += count;
    return true;
  };
  for(const auto &entry : objects)
  {
    const auto &object = entry.second;
    const mp_integer size = object_capacity(object);
    if(!append(object.tag, size))
      return false;
  }
  if(has_dynamic_allocations && storage_slots != 0)
  {
    for(unsigned i = 0; i < storage_slots; ++i)
      if(!append(first_heap_tag + i, mp_integer(allocation_capacity())))
        return false;
  }
  // A zero-byte program still needs a legal (positive-width) dummy BV state.
  packed_bytes = std::max<std::size_t>(packed_bytes, 1);
  return true;
}

btor2_nid_t heap_modelt::packed_index(btor2_nid_t index, bool byte_addressed)
{
  if(!byte_addressed)
    return b.uext(pointer_sort, index, pointer_bits - object_bits);
  const auto cached = packed_indices.find(index);
  if(cached != packed_indices.end())
    return cached->second;
  const auto identity = tag(index);
  const auto off =
    b.uext(pointer_sort, offset(index), pointer_bits - offset_bits);
  auto result = b.constd(pointer_sort, packed_bytes); // out-of-storage sentinel
  for(const auto &object : packed_objects)
  {
    if(object.capacity == 0)
      continue;
    const auto matches = b.land(
      bool_sort,
      b.eq(bool_sort, identity, b.constd(tag_sort, object.tag)),
      b.ult(bool_sort, off, b.constd(pointer_sort, object.capacity)));
    const auto dense =
      b.add(pointer_sort, off, b.constd(pointer_sort, object.start));
    result = b.ite(pointer_sort, matches, dense, result);
  }
  packed_indices.emplace(index, result);
  return result;
}

btor2_nid_t
heap_modelt::packed_shift(btor2_nid_t index, const packed_arrayt &layout)
{
  const auto bits = layout.elements * layout.element_bits;
  const auto sort = b.get_or_create_bitvec_sort(bits);
  // Packed bit offsets can exceed the C pointer width (e.g. on a 16-bit
  // target). Width validation above bounds every valid bit offset by INT_MAX.
  const auto arithmetic_bits = std::max<unsigned>(pointer_bits, 32);
  const auto arithmetic_sort = b.get_or_create_bitvec_sort(arithmetic_bits);
  if(arithmetic_bits > pointer_bits)
    index = b.uext(arithmetic_sort, index, arithmetic_bits - pointer_bits);
  auto shift = b.mul(
    arithmetic_sort, index, b.constd(arithmetic_sort, layout.element_bits));
  if(bits < arithmetic_bits)
    shift = b.slice(sort, shift, bits - 1, 0);
  else if(bits > arithmetic_bits)
    shift = b.uext(sort, shift, bits - arithmetic_bits);
  return shift;
}

btor2_nid_t heap_modelt::read_storage(
  btor2_nid_t element_sort,
  btor2_nid_t state,
  btor2_nid_t index)
{
  if(!array_encoding.bitvectors)
    return b.read(element_sort, state, index);
  const auto &layout = packed_arrays.at(state);
  const auto bits = layout.elements * layout.element_bits;
  const auto sort = b.get_or_create_bitvec_sort(bits);
  const auto dense = packed_index(index, layout.byte_addressed);
  auto value = b.srl(sort, state, packed_shift(dense, layout));
  if(bits != layout.element_bits)
    value = b.slice(element_sort, value, layout.element_bits - 1, 0);
  // Guard before narrowing the shift: a large/negative index must never wrap
  // around to another element. Invalid C accesses are diagnosed separately.
  return b.ite(
    element_sort,
    b.ult(bool_sort, dense, b.constd(pointer_sort, layout.elements)),
    value,
    b.zero(element_sort));
}

btor2_nid_t heap_modelt::write_storage(
  btor2_nid_t state,
  btor2_nid_t value,
  btor2_nid_t index,
  btor2_nid_t element)
{
  if(!array_encoding.bitvectors)
    return b.write(update(state).sort, value, index, element);
  const auto &layout = packed_arrays.at(state);
  const auto bits = layout.elements * layout.element_bits;
  const auto sort = b.get_or_create_bitvec_sort(bits);
  const auto element_sort = b.get_or_create_bitvec_sort(layout.element_bits);
  const auto dense = packed_index(index, layout.byte_addressed);
  const auto shift = packed_shift(dense, layout);
  auto mask = b.ones(element_sort);
  if(bits != layout.element_bits)
  {
    mask = b.uext(sort, mask, bits - layout.element_bits);
    element = b.uext(sort, element, bits - layout.element_bits);
  }
  mask = b.sll(sort, mask, shift);
  const auto changed = b.lor(
    sort, b.land(sort, value, b.lnot(sort, mask)), b.sll(sort, element, shift));
  return b.ite(
    sort,
    b.ult(bool_sort, dense, b.constd(pointer_sort, layout.elements)),
    changed,
    value);
}
