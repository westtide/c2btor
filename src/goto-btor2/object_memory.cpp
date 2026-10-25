// SPDX-License-Identifier: BSD-4-Clause
// SPDX-FileCopyrightText: 2026 C2BTOR contributors

#include <util/arith_tools.h>
#include <util/std_expr.h>
#include <util/config.h>
#include <util/invariant.h>
#include <util/pointer_offset_size.h>
#include <util/simplify_expr.h>
#include <util/std_types.h>

#include "btor2_type_utils.h"
#include "heap_model.h"

#include <algorithm>
#include <limits>

// One authoritative backing per root object. Typed arrays are accessed through
// byte lanes of their elements, so character aliases never get a second copy.
unsigned heap_modelt::storage_element_bytes(const typet &type) const
{
  auto leaf = follow_tag_type(type, ns);
  while(leaf.id() == ID_array)
    leaf = follow_tag_type(to_array_type(leaf).element_type(), ns);
  const bool scalar = leaf.id() == ID_signedbv || leaf.id() == ID_unsignedbv ||
                      leaf.id() == ID_c_bool || leaf.id() == ID_bool ||
                      leaf.id() == ID_floatbv || leaf.id() == ID_fixedbv ||
                      leaf.id() == ID_pointer || leaf.id() == ID_c_enum;
  if(scalar)
  {
    const auto size_expr = size_of_expr(leaf, ns);
    const auto size =
      size_expr ? numeric_cast<mp_integer>(simplify_expr(*size_expr, ns))
                : std::optional<mp_integer>{};
    if(
      size && *size > 0 && *size <= std::numeric_limits<int>::max() / byte_bits)
      return numeric_cast_v<unsigned>(*size);
  }
  return 1;
}

void heap_modelt::create_object_states()
{
  auto append =
    [&](unsigned identity, const mp_integer &capacity, const typet &type,
        unsigned requested_cell_bytes = 0, bool symbolic_capacity = false)
  {
    const unsigned extent_bits =
      offset_bits - (uses_wide_pointer_offsets() ? 0u : 1u);
    if(
      !symbolic_capacity &&
      (capacity < 0 || capacity >= (mp_integer(1) << extent_bits)))
    {
      failed = true;
      failure_reason = "--memory object capacity exceeds representable width";
      return;
    }
    const auto count =
      symbolic_capacity ? 0 : numeric_cast_v<std::size_t>(capacity);
    auto leaf = follow_tag_type(type, ns);
    const bool array = leaf.id() == ID_array;
    while(leaf.id() == ID_array)
      leaf = follow_tag_type(to_array_type(leaf).element_type(), ns);
    const bool scalar = leaf.id() == ID_signedbv ||
                        leaf.id() == ID_unsignedbv || leaf.id() == ID_c_bool ||
                        leaf.id() == ID_bool || leaf.id() == ID_floatbv ||
                        leaf.id() == ID_fixedbv || leaf.id() == ID_pointer ||
                        leaf.id() == ID_c_enum;
    const auto element_bytes = symbolic_capacity
                                 ? (symbolic_cells.word64 ? 8u : 1u)
                                 : requested_cell_bytes
                                     ? requested_cell_bytes
                                     : storage_element_bytes(type);
    const auto elements = symbolic_capacity
                            ? 0
                            : std::max<std::size_t>(
                                1, (count + element_bytes - 1) / element_bytes);
    unsigned index_bits = offset_bits;
    if(symbolic_capacity && element_bytes == 8)
      index_bits -= 3;
    if(!symbolic_capacity)
    {
      index_bits = 0;
      for(auto n = elements - 1; n; n >>= 1)
        ++index_bits;
      index_bits = std::max(1u, index_bits);
    }
    // Choose bounded backing from the full logical capacity in target bytes.
    // Rounded tail lanes do not change the threshold or any validity bound.
    // A single backing cell has only index zero on every in-capacity access.
    // Scalarize it exactly, retaining the same byte lanes and validity guards.
    const bool native_array = symbolic_capacity ||
      (!array_encoding.bitvectors &&
       (!array_encoding.mixed ||
        capacity * byte_bits > mp_integer(array_encoding.mixed_threshold_bits)) &&
       (array || !scalar) && elements > 1);
    if(!native_array &&
       mp_integer(elements) * element_bytes * byte_bits >
         std::numeric_limits<int>::max())
    {
      failed = true;
      failure_reason = "object BV storage exceeds representable width";
      return;
    }
    local_objectt object{
      identity,
      element_bytes,
      index_bits,
      count,
      elements,
      native_array,
      symbolic_capacity,
      b.get_or_create_bitvec_sort(index_bits),
      b.get_or_create_bitvec_sort(element_bytes * byte_bits),
      {}};
    const auto data_sort =
      native_array
        ? b.sort_array(object.index_sort, object.element_sort)
        : b.get_or_create_bitvec_sort(elements * element_bytes * byte_bits);
    const btor2_nid_t sorts[] = {
      data_sort, bool_sort, size_sort, bool_sort};
    const char *names[] = {"data", "live", "size", "readonly"};
    for(std::size_t i = 0; i < object.fields.size(); ++i)
    {
      const auto initial =
        i == static_cast<std::size_t>(fieldt::data)
          ? 0
          : b.zero(sorts[i]);
      auto state = b.state(
        sorts[i],
        "__initial_object_" + std::to_string(identity) + "_" + names[i]);
      // Data has no initializer: each byte is arbitrary and stable until a
      // source write or an explicit zero/reset operation changes its backing.
      if(initial)
        b.init(sorts[i], state, initial);
      if(symbolic_capacity && array_encoding.symbolic_heap_compact)
        deferred_initial_next.insert(state);
      else
        b.next(sorts[i], state, state);
      updates.push_back({sorts[i], state, state, state});
      object.fields[i] = state;
    }
    local_objects.push_back(std::move(object));
  };
  for(const auto &entry : objects)
  {
    const auto &object = entry.second;
    append(object.tag, mp_integer(object_capacity(object)), object.type);
    if(failed)
      return;
  }
  if(has_dynamic_allocations)
  {
    if(uses_symbolic_allocation_storage())
    {
      // Every fresh slot has its own byte Array. Its index domain is fixed;
      // only the existing allocation-time size state records its extent.
      for(unsigned i = 0; i < storage_slots; ++i)
      {
        append(first_heap_tag + i, 0, typet{}, 1, true);
        if(failed)
          return;
      }
      return;
    }
    const mp_integer capacity = allocation_capacity();
    unsigned cell_bytes = 1;
    if(
      use_array_word_access() &&
      (!array_encoding.mixed ||
       capacity * byte_bits > mp_integer(array_encoding.mixed_threshold_bits)) &&
      config.ansi_c.int_width % byte_bits == 0)
    {
      const unsigned proposed = config.ansi_c.int_width / byte_bits;
      if(proposed && (proposed & (proposed - 1)) == 0)
      {
        const mp_integer rounded =
          ((capacity + proposed - 1) / proposed) * proposed;
        if(rounded * byte_bits <= std::numeric_limits<int>::max())
          cell_bytes = proposed;
      }
    }
    for(unsigned i = 0; i < storage_slots; ++i)
    {
      // One packed backing, regardless of the allocation's typed views.
      // Logical size and capacity remain in bytes; rounded tail lanes are
      // inaccessible. Character aliases use local_read/local_write below.
      append(first_heap_tag + i, capacity, typet{}, cell_bytes);
      if(failed)
        return;
    }
  }
}

void heap_modelt::initialize_object_data(
  btor2_nid_t identity, btor2_nid_t zero)
{
  PRECONDITION(!uses_lazy_zero_initialization());
  if(!array_encoding.object_memory)
  {
    const auto arithmetic_sort =
      b.get_or_create_bitvec_sort(std::max(pointer_bits, 32u));
    auto &u = update(memory);
    for(const auto &object : packed_objects)
    {
      if(object.capacity == 0 ||
         !may_select_object(identity, object.tag, false))
        continue;
      const auto changed = replace_bits(
        u.local, packed_bytes * byte_bits,
        b.constd(arithmetic_sort, object.start * byte_bits),
        b.zero(b.get_or_create_bitvec_sort(object.capacity * byte_bits)),
        object.capacity * byte_bits);
      const auto guard = b.land(
        bool_sort, b.land(bool_sort, path_guard, zero),
        b.eq(bool_sort, identity, b.constd(tag_sort, object.tag)));
      u.local = b.ite(u.sort, guard, changed, u.local);
    }
    return;
  }
  // Dynamic heap identities are fresh. Certified automatic re-entry resets
  // storage in reset_automatic_object instead. A malloc slot therefore
  // already holds its own arbitrary initial data. Never choose a new value
  // on each read. Zero-initialized allocations overwrite that data atomically.
  for(const auto &object : local_objects)
  {
    if(!may_select_object(identity, object.tag, false))
      continue;
    auto &u = update(object.fields[static_cast<std::size_t>(fieldt::data)]);
    btor2_nid_t zero_data;
    if(object.native_array)
    {
      auto &constant = zero_arrays[u.sort];
      if(!constant)
      {
        const auto element_zero = b.zero(object.element_sort);
        constant = b.state(u.sort, "__zero_object_array_" + std::to_string(u.sort));
        b.init(u.sort, constant, element_zero);
        b.next(u.sort, constant, constant);
      }
      zero_data = constant;
    }
    else
      zero_data = b.zero(u.sort);
    const auto guard = b.land(
      bool_sort,
      b.land(bool_sort, path_guard, zero),
      b.eq(bool_sort, identity, b.constd(tag_sort, object.tag)));
    u.local = b.ite(u.sort, guard, zero_data, u.local);
  }
}

void heap_modelt::reset_automatic_object(const objectt &o)
{
  if(array_encoding.object_memory)
  {
    for(const auto &object : local_objects)
    {
      if(object.tag != o.tag)
        continue;
      auto &u = update(object.fields[static_cast<std::size_t>(fieldt::data)]);
      const auto initial = b.input(
        u.sort, "__automatic_initial_" + std::to_string(o.tag));
      u.local = b.ite(u.sort, path_guard, initial, u.local);
    }
  }
  else if(array_encoding.bitvectors)
  {
    const auto found = std::find_if(
      packed_objects.begin(), packed_objects.end(),
      [&](const packed_objectt &object) { return object.tag == o.tag; });
    INVARIANT(found != packed_objects.end(), "automatic object backing");
    if(found->capacity == 0)
      return;
    auto &u = update(memory);
    const auto initial = b.input(
      b.get_or_create_bitvec_sort(found->capacity * byte_bits),
      "__automatic_initial_" + std::to_string(o.tag));
    const auto arithmetic_sort =
      b.get_or_create_bitvec_sort(std::max(pointer_bits, 32u));
    const auto changed = replace_bits(
      u.local, packed_bytes * byte_bits,
      b.constd(arithmetic_sort, found->start * byte_bits), initial,
      found->capacity * byte_bits);
    u.local = b.ite(u.sort, path_guard, changed, u.local);
  }
  else
  {
    const auto bytes = numeric_cast_v<unsigned>(to_constant_expr(o.size));
    const auto pointer = base(o.tag);
    for(unsigned i = 0; i < bytes; ++i)
    {
      const auto address = byte_address(pointer, i);
      write_meta(fieldt::data, address,
        b.input(byte_sort, "__automatic_initial_" + std::to_string(o.tag) +
                           "_" + std::to_string(i)));
      write_meta(fieldt::written, address, b.zero(bool_sort));
    }
  }
}

btor2_nid_t heap_modelt::global_field(fieldt field) const
{
  switch(field)
  {
  case fieldt::data:
    return memory;
  case fieldt::written:
    return written;
  case fieldt::live:
    return live;
  case fieldt::zeroed:
    return zeroed;
  case fieldt::size:
    return sizes;
  case fieldt::readonly:
    return readonly;
  }
  UNREACHABLE;
}

bool heap_modelt::try_initialize_store(
  unsigned identity, const mp_integer &off, btor2_nid_t value, unsigned bits)
{
  if(!array_encoding.object_memory || !initializing ||
     path_guard != initial_path_guard)
    return false;
  const auto found = std::find_if(
    local_objects.begin(), local_objects.end(),
    [&](const local_objectt &object) { return object.tag == identity; });
  const unsigned bytes = (bits + byte_bits - 1) / byte_bits;
  if(found == local_objects.end() || off < 0 || off + bytes > found->capacity)
  {
    failed = true;
    failure_reason = "static initializer outside object storage";
    return true;
  }
  const auto &object = *found;
  if(bits != bytes * byte_bits)
    value = b.uext(
      b.get_or_create_bitvec_sort(bytes * byte_bits), value,
      bytes * byte_bits - bits);
  auto &data = update(object.fields[static_cast<unsigned>(fieldt::data)]);
  const bool whole_cell =
    bytes == object.element_bytes && off % object.element_bytes == 0;
  const bool little_endian =
    config.ansi_c.endianness == configt::ansi_ct::endiannesst::IS_LITTLE_ENDIAN;
  const auto arithmetic_sort =
    b.get_or_create_bitvec_sort(std::max(pointer_bits, 32u));
  if(object.native_array && whole_cell)
    data.local = b.write(
      data.sort, data.local,
      b.constd(object.index_sort, off / object.element_bytes), value);
  else if(!object.native_array && (little_endian || whole_cell))
    data.local = replace_bits(
      data.local, object.elements * object.element_bytes * byte_bits,
      b.constd(arithmetic_sort, off * byte_bits), value, bytes * byte_bits);
  else
    for(unsigned i = 0; i < bytes; ++i)
    {
      const auto part = little_endian ? i : bytes - 1 - i;
      const auto byte = b.slice(
        byte_sort, value, (part + 1) * byte_bits - 1, part * byte_bits);
      data.local = local_write(
        object, fieldt::data, data.local, b.constd(size_sort, off + i), byte);
    }
  return true;
}

btor2_nid_t
heap_modelt::resize_unsigned(btor2_nid_t value, unsigned from, unsigned to)
{
  auto sort = b.get_or_create_bitvec_sort(to);
  if(from < to)
    return b.uext(sort, value, to - from);
  if(from > to)
    return b.slice(sort, value, to - 1, 0);
  return value;
}

// bit_offset uses an arithmetic sort wide enough for every supported packed
// bit offset, independently of the target's pointer width.
btor2_nid_t heap_modelt::extract_bits(
  btor2_nid_t value,
  unsigned bits,
  btor2_nid_t bit_offset,
  unsigned width)
{
  auto sort = b.get_or_create_bitvec_sort(bits);
  auto shifted = b.srl(
    sort,
    value,
    resize_unsigned(bit_offset, std::max(pointer_bits, 32u), bits));
  return bits == width
           ? shifted
           : b.slice(b.get_or_create_bitvec_sort(width), shifted, width - 1, 0);
}

btor2_nid_t heap_modelt::replace_bits(
  btor2_nid_t value,
  unsigned bits,
  btor2_nid_t bit_offset,
  btor2_nid_t element,
  unsigned width)
{
  auto sort = b.get_or_create_bitvec_sort(bits);
  auto shift = resize_unsigned(bit_offset, std::max(pointer_bits, 32u), bits);
  auto mask =
    resize_unsigned(b.ones(b.get_or_create_bitvec_sort(width)), width, bits);
  mask = b.sll(sort, mask, shift);
  return b.lor(
    sort,
    b.land(sort, value, b.lnot(sort, mask)),
    b.sll(sort, resize_unsigned(element, width, bits), shift));
}

btor2_nid_t heap_modelt::local_read(
  const local_objectt &object,
  fieldt field,
  btor2_nid_t value,
  btor2_nid_t off)
{
  if(field != fieldt::data)
    return value;
  const auto arithmetic_bits = std::max(pointer_bits, 32u);
  const auto arithmetic_sort = b.get_or_create_bitvec_sort(arithmetic_bits);
  auto wide_off = resize_unsigned(off, pointer_bits, arithmetic_bits);
  if(!object.native_array &&
     config.ansi_c.endianness == configt::ansi_ct::endiannesst::IS_LITTLE_ENDIAN)
  {
    // A BV byte view is directly addressed by off*byte_bits. Decomposing it
    // into cell/lane division and reconstructing the same offset creates
    // unnecessary divider circuits, especially for dynamically indexed heaps.
    const auto bit = b.mul(arithmetic_sort, wide_off,
                           b.constd(arithmetic_sort, byte_bits));
    return extract_bits(value, object.element_bytes * byte_bits * object.elements,
                        bit, byte_bits);
  }
  auto element = b.udiv(
    arithmetic_sort, wide_off, b.constd(arithmetic_sort, object.element_bytes));
  auto lane = b.urem(
    arithmetic_sort, wide_off, b.constd(arithmetic_sort, object.element_bytes));
  if(config.ansi_c.endianness == configt::ansi_ct::endiannesst::IS_BIG_ENDIAN)
    lane = b.sub(
      arithmetic_sort,
      b.constd(arithmetic_sort, object.element_bytes - 1),
      lane);
  auto bit = b.mul(arithmetic_sort, lane, b.constd(arithmetic_sort, byte_bits));
  unsigned bits = object.element_bytes * byte_bits;
  if(object.native_array)
    value = b.read(
      object.element_sort,
      value,
      resize_unsigned(element, arithmetic_bits, object.index_bits));
  else
  {
    bit = b.add(
      arithmetic_sort,
      bit,
      b.mul(arithmetic_sort, element, b.constd(arithmetic_sort, bits)));
    bits *= object.elements;
  }
  return extract_bits(value, bits, bit, byte_bits);
}

btor2_nid_t heap_modelt::local_write(
  const local_objectt &object,
  fieldt field,
  btor2_nid_t value,
  btor2_nid_t off,
  btor2_nid_t byte)
{
  if(field != fieldt::data)
    return byte;
  const auto arithmetic_bits = std::max(pointer_bits, 32u);
  const auto arithmetic_sort = b.get_or_create_bitvec_sort(arithmetic_bits);
  auto wide_off = resize_unsigned(off, pointer_bits, arithmetic_bits);
  if(object.native_array && object.element_bytes == 1)
    return b.write(
      update(object.fields[0]).sort, value,
      resize_unsigned(off, pointer_bits, object.index_bits), byte);
  if(!object.native_array &&
     config.ansi_c.endianness == configt::ansi_ct::endiannesst::IS_LITTLE_ENDIAN)
  {
    const auto bit = b.mul(arithmetic_sort, wide_off,
                           b.constd(arithmetic_sort, byte_bits));
    return replace_bits(value, object.element_bytes * byte_bits * object.elements,
                        bit, byte, byte_bits);
  }
  auto element = b.udiv(
    arithmetic_sort, wide_off, b.constd(arithmetic_sort, object.element_bytes));
  auto lane = b.urem(
    arithmetic_sort, wide_off, b.constd(arithmetic_sort, object.element_bytes));
  if(config.ansi_c.endianness == configt::ansi_ct::endiannesst::IS_BIG_ENDIAN)
    lane = b.sub(
      arithmetic_sort,
      b.constd(arithmetic_sort, object.element_bytes - 1),
      lane);
  auto bit = b.mul(arithmetic_sort, lane, b.constd(arithmetic_sort, byte_bits));
  const unsigned bits = object.element_bytes * byte_bits;
  if(object.native_array)
  {
    auto index = resize_unsigned(element, arithmetic_bits, object.index_bits);
    auto old = b.read(object.element_sort, value, index);
    auto changed = replace_bits(old, bits, bit, byte, byte_bits);
    return b.write(update(object.fields[0]).sort, value, index, changed);
  }
  bit = b.add(
    arithmetic_sort,
    bit,
    b.mul(arithmetic_sort, element, b.constd(arithmetic_sort, bits)));
  return replace_bits(value, bits * object.elements, bit, byte, byte_bits);
}

btor2_nid_t heap_modelt::local_capacity_guard(
  const local_objectt &object,
  btor2_nid_t off,
  unsigned bytes,
  bool byte_dispatch)
{
  if(!object.symbolic_capacity)
  {
    if(object.capacity < bytes)
      return b.zero(bool_sort);
    if(byte_dispatch)
      return b.ult(
        bool_sort, off, b.constd(size_sort, object.capacity));
    return b.ulte(
      bool_sort, off, b.constd(size_sort, object.capacity - bytes));
  }
  // Preserve the complete machine-width offset and the allocation-time size
  // snapshot. Extending before addition prevents a wrapped end from passing.
  const auto wide_sort = b.get_or_create_bitvec_sort(pointer_bits + 1);
  const auto end = b.add(
    wide_sort, b.uext(wide_sort, off, 1), b.constd(wide_sort, bytes));
  const auto size = object.fields[static_cast<std::size_t>(fieldt::size)];
  return b.ulte(bool_sort, end, b.uext(wide_sort, size, 1));
}

btor2_nid_t heap_modelt::read_field(fieldt field, btor2_nid_t index)
{
  const auto sort = field == fieldt::data   ? byte_sort
                    : field == fieldt::size ? size_sort
                                            : bool_sort;
  if(!array_encoding.object_memory)
    return read_storage(sort, global_field(field), index);
  PRECONDITION(field <= fieldt::readonly);
  const bool byte_addressed = field == fieldt::data;
  auto identity = byte_addressed ? tag(index) : index;
  auto off = byte_addressed
               ? resize_unsigned(offset(index), offset_bits, pointer_bits)
               : b.zero(size_sort);
  auto result = b.zero(sort);
  for(const auto &object : local_objects)
  {
    if(!may_select_object(index, object.tag, byte_addressed))
      continue;
    auto guard = b.eq(bool_sort, identity, b.constd(tag_sort, object.tag));
    if(byte_addressed)
      guard = b.land(
        bool_sort,
        guard,
        local_capacity_guard(object, off, 1, true));
    auto value = local_read(
      object, field, object.fields[static_cast<std::size_t>(field)], off);
    result = b.ite(sort, guard, value, result);
  }
  return result;
}

void heap_modelt::write_meta(fieldt field, btor2_nid_t index, btor2_nid_t value)
{
  if(!array_encoding.object_memory)
  {
    auto state = global_field(field);
    auto &u = update(state);
    auto changed = write_storage(state, u.local, index, value);
    u.local = b.ite(u.sort, path_guard, changed, u.local);
    return;
  }
  PRECONDITION(field <= fieldt::readonly);
  const bool byte_addressed = field == fieldt::data;
  auto identity = byte_addressed ? tag(index) : index;
  auto off = byte_addressed
               ? resize_unsigned(offset(index), offset_bits, pointer_bits)
               : b.zero(size_sort);
  for(const auto &object : local_objects)
  {
    if(!may_select_object(index, object.tag, byte_addressed))
      continue;
    auto guard = b.land(
      bool_sort,
      path_guard,
      b.eq(bool_sort, identity, b.constd(tag_sort, object.tag)));
    // Check the full byte offset before compact indexing, including spare cells
    // in non-power-of-two arrays and the unused tail of rounded VLA capacity.
    if(byte_addressed)
      guard = b.land(
        bool_sort,
        guard,
        local_capacity_guard(object, off, 1, true));
    auto &u = update(object.fields[static_cast<std::size_t>(field)]);
    auto changed = local_write(object, field, u.local, off, value);
    u.local = b.ite(u.sort, guard, changed, u.local);
  }
}

bool heap_modelt::use_bv_word_access() const
{
  return array_encoding.object_memory && array_encoding.bitvectors &&
    !uses_symbolic_allocation_storage() &&
    config.ansi_c.endianness == configt::ansi_ct::endiannesst::IS_LITTLE_ENDIAN;
}

bool heap_modelt::use_array_word_access() const
{
  return array_encoding.object_memory &&
    (!array_encoding.bitvectors || uses_symbolic_allocation_storage());
}

heap_modelt::array_windowt heap_modelt::array_window(
  const local_objectt &object, btor2_nid_t data, btor2_nid_t off, unsigned bytes)
{
  PRECONDITION(
    object.native_array && bytes > 1 && bytes <= 2 * object.element_bytes &&
    object.element_bytes <= std::numeric_limits<int>::max() / byte_bits / 3);
  const unsigned arithmetic_bits = std::max(pointer_bits, 32u);
  const auto arithmetic_sort = b.get_or_create_bitvec_sort(arithmetic_bits);
  const auto wide_off = resize_unsigned(off, pointer_bits, arithmetic_bits);
  const auto cell_bytes = b.constd(arithmetic_sort, object.element_bytes);
  const auto cell = b.udiv(arithmetic_sort, wide_off, cell_bytes);
  const auto lane = b.urem(arithmetic_sort, wide_off, cell_bytes);
  // Include enough cells for the largest possible byte lane, without assuming
  // that the pointer is aligned merely because its access has a scalar type.
  const unsigned cells =
    (bytes + 2 * object.element_bytes - 2) / object.element_bytes;
  const bool little_endian =
    config.ansi_c.endianness == configt::ansi_ct::endiannesst::IS_LITTLE_ENDIAN;
  array_windowt result;
  result.data = 0;
  result.bits = cells * object.element_bytes * byte_bits;
  result.sort = b.get_or_create_bitvec_sort(result.bits);
  const auto end = b.add(arithmetic_sort, lane, b.constd(arithmetic_sort, bytes));
  for(unsigned i = 0; i < cells; ++i)
  {
    const auto index = resize_unsigned(
      b.add(arithmetic_sort, cell, b.constd(arithmetic_sort, i)),
      arithmetic_bits, object.index_bits);
    result.indices.push_back(index);
    result.active.push_back(
      i == 0 ? b.one(bool_sort)
             : b.ugt(bool_sort, end,
                     b.constd(arithmetic_sort, i * object.element_bytes)));
    const auto value = b.read(object.element_sort, data, index);
    if(i == 0)
      result.data = value;
    else
    {
      const auto sort =
        b.get_or_create_bitvec_sort((i + 1) * object.element_bytes * byte_bits);
      result.data = little_endian ? b.concat(sort, value, result.data)
                                  : b.concat(sort, result.data, value);
    }
  }
  const auto byte_shift = little_endian ? lane : b.sub(
    arithmetic_sort,
    b.constd(arithmetic_sort, cells * object.element_bytes - bytes), lane);
  result.shift =
    b.mul(arithmetic_sort, byte_shift, b.constd(arithmetic_sort, byte_bits));
  return result;
}

btor2_nid_t heap_modelt::load_array_word(btor2_nid_t p, unsigned bytes)
{
  PRECONDITION(use_array_word_access());
  const auto off = resize_unsigned(offset(p), offset_bits, pointer_bits);
  const auto word_sort = b.get_or_create_bitvec_sort(bytes * byte_bits);
  auto result = b.zero(word_sort);
  for(const auto &object : local_objects)
  {
    if((!object.symbolic_capacity && object.capacity < bytes) ||
       !may_select_object(p, object.tag, true))
      continue;
    const auto guard = b.land(bool_sort,
      b.eq(bool_sort, tag(p), b.constd(tag_sort, object.tag)),
      local_capacity_guard(object, off, bytes));
    btor2_nid_t value = 0;
    if(object.symbolic_capacity && symbolic_cells.word64 && bytes == 8)
    {
      const auto index = b.slice(
        object.index_sort, off, object.index_bits + 2, 3);
      value = b.read(word_sort, object.fields[0], index);
    }
    else if(
      object.native_array && bytes > 1 && bytes <= 2 * object.element_bytes &&
      object.element_bytes <= std::numeric_limits<int>::max() / byte_bits / 3)
    {
      const auto window = array_window(object, object.fields[0], off, bytes);
      const auto shifted = b.srl(window.sort, window.data,
        resize_unsigned(window.shift, std::max(pointer_bits, 32u),
                        window.bits));
      value = b.slice(word_sort, shifted, bytes * byte_bits - 1, 0);
    }
    else
      for(unsigned i = 0; i < bytes; ++i)
      {
        const auto byte = local_read(object, fieldt::data, object.fields[0],
          b.add(size_sort, off, b.constd(size_sort, i)));
        if(!value)
          value = byte;
        else
        {
          const auto sort = b.get_or_create_bitvec_sort((i + 1) * byte_bits);
          value = config.ansi_c.endianness == configt::ansi_ct::endiannesst::IS_BIG_ENDIAN
                    ? b.concat(sort, value, byte) : b.concat(sort, byte, value);
        }
      }
    result = b.ite(word_sort, guard, value, result);
  }
  return result;
}

void heap_modelt::store_array_word(btor2_nid_t p, btor2_nid_t value, unsigned bytes)
{
  PRECONDITION(use_array_word_access());
  const auto off = resize_unsigned(offset(p), offset_bits, pointer_bits);
  const bool little_endian =
    config.ansi_c.endianness == configt::ansi_ct::endiannesst::IS_LITTLE_ENDIAN;
  for(const auto &object : local_objects)
  {
    if((!object.symbolic_capacity && object.capacity < bytes) ||
       !may_select_object(p, object.tag, true))
      continue;
    const auto guard = b.land(bool_sort, path_guard, b.land(bool_sort,
      b.eq(bool_sort, tag(p), b.constd(tag_sort, object.tag)),
      local_capacity_guard(object, off, bytes)));
    auto &data = update(object.fields[0]);
    auto changed = data.local;
    if(object.symbolic_capacity && symbolic_cells.word64 && bytes == 8)
    {
      const auto index = b.slice(
        object.index_sort, off, object.index_bits + 2, 3);
      changed = b.write(data.sort, changed, index, value);
    }
    else if(
      object.native_array && bytes > 1 && bytes <= 2 * object.element_bytes &&
      object.element_bytes <= std::numeric_limits<int>::max() / byte_bits / 3)
    {
      const auto window = array_window(object, data.local, off, bytes);
      const unsigned cell_bits = object.element_bytes * byte_bits;
      const auto merged = replace_bits(
        window.data, window.bits, window.shift, value, bytes * byte_bits);
      for(unsigned i = 0; i < window.indices.size(); ++i)
      {
        const auto position =
          little_endian ? i : window.indices.size() - 1 - i;
        const auto part = b.slice(object.element_sort, merged,
          (position + 1) * cell_bits - 1, position * cell_bits);
        const auto written =
          b.write(data.sort, changed, window.indices[i], part);
        // Ignore cells beyond the accessed byte range, including a narrowed
        // index that wraps to the first cell. Every active cell is protected
        // by the full byte-capacity guard before the update is committed.
        changed = i == 0 ? written
                        : b.ite(data.sort, window.active[i], written, changed);
      }
    }
    else
      for(unsigned i = 0; i < bytes; ++i)
      {
        const auto part = little_endian ? i : bytes - 1 - i;
        changed = local_write(object, fieldt::data, changed,
          b.add(size_sort, off, b.constd(size_sort, i)),
          b.slice(byte_sort, value, (part + 1) * byte_bits - 1, part * byte_bits));
      }
    data.local = b.ite(data.sort, guard, changed, data.local);
  }
}

btor2_nid_t heap_modelt::load_bv_word(btor2_nid_t p, unsigned bytes)
{
  const auto arithmetic_bits = std::max(pointer_bits, 32u);
  const auto arithmetic_sort = b.get_or_create_bitvec_sort(arithmetic_bits);
  const auto off = resize_unsigned(offset(p), offset_bits, arithmetic_bits);
  const auto bit = b.mul(arithmetic_sort, off, b.constd(arithmetic_sort, byte_bits));
  const auto word_sort = b.get_or_create_bitvec_sort(bytes * byte_bits);
  auto result = b.zero(word_sort);
  for(const auto &object : local_objects)
  {
    if(object.capacity < bytes || !may_select_object(p, object.tag, true))
      continue;
    const auto guard = b.land(bool_sort,
      b.eq(bool_sort, tag(p), b.constd(tag_sort, object.tag)),
      b.ulte(bool_sort, off, b.constd(arithmetic_sort, object.capacity - bytes)));
    const auto data = extract_bits(object.fields[0],
      object.element_bytes * byte_bits * object.elements, bit, bytes * byte_bits);
    result = b.ite(word_sort, guard, data, result);
  }
  return result;
}

void heap_modelt::store_bv_word(btor2_nid_t p, btor2_nid_t value, unsigned bytes)
{
  const auto arithmetic_bits = std::max(pointer_bits, 32u);
  const auto arithmetic_sort = b.get_or_create_bitvec_sort(arithmetic_bits);
  const auto off = resize_unsigned(offset(p), offset_bits, arithmetic_bits);
  const auto bit = b.mul(arithmetic_sort, off, b.constd(arithmetic_sort, byte_bits));
  for(const auto &object : local_objects)
  {
    if(object.capacity < bytes || !may_select_object(p, object.tag, true))
      continue;
    const auto guard = b.land(bool_sort, path_guard,
      b.land(bool_sort, b.eq(bool_sort, tag(p), b.constd(tag_sort, object.tag)),
        b.ulte(bool_sort, off, b.constd(arithmetic_sort, object.capacity - bytes))));
    auto &data = update(object.fields[0]);
    data.local = b.ite(data.sort, guard,
      replace_bits(data.local, object.element_bytes * byte_bits * object.elements,
                   bit, value, bytes * byte_bits), data.local);
  }
}
