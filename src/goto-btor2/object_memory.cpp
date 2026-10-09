#include <util/arith_tools.h>
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
    [&](unsigned identity, const mp_integer &capacity, const typet &type)
  {
    if(
      capacity < 0 || capacity >= (mp_integer(1) << (offset_bits - 1)) ||
      capacity > std::numeric_limits<int>::max() / byte_bits)
    {
      failed = true;
      failure_reason = "--memory object capacity exceeds representable width";
      return;
    }
    const auto count = numeric_cast_v<std::size_t>(capacity);
    auto leaf = follow_tag_type(type, ns);
    const bool array = leaf.id() == ID_array;
    while(leaf.id() == ID_array)
      leaf = follow_tag_type(to_array_type(leaf).element_type(), ns);
    const bool scalar = leaf.id() == ID_signedbv ||
                        leaf.id() == ID_unsignedbv || leaf.id() == ID_c_bool ||
                        leaf.id() == ID_bool || leaf.id() == ID_floatbv ||
                        leaf.id() == ID_fixedbv || leaf.id() == ID_pointer ||
                        leaf.id() == ID_c_enum;
    const auto element_bytes = storage_element_bytes(type);
    const auto elements =
      std::max<std::size_t>(1, (count + element_bytes - 1) / element_bytes);
    if(
      mp_integer(elements) * element_bytes * byte_bits >
      std::numeric_limits<int>::max())
    {
      failed = true;
      failure_reason =
        "--memory object rounded storage exceeds representable width";
      return;
    }
    unsigned index_bits = 0;
    for(auto n = elements - 1; n; n >>= 1)
      ++index_bits;
    index_bits = std::max(1u, index_bits);
    const bool native_array = !array_encoding.bitvectors && (array || !scalar);
    local_objectt object{
      identity,
      element_bytes,
      index_bits,
      count,
      elements,
      native_array,
      b.get_or_create_bitvec_sort(index_bits),
      b.get_or_create_bitvec_sort(element_bytes * byte_bits),
      {}};
    const auto data_sort =
      native_array
        ? b.sort_array(object.index_sort, object.element_sort)
        : b.get_or_create_bitvec_sort(elements * element_bytes * byte_bits);
    const auto bitmap_sort =
      b.get_or_create_bitvec_sort(std::max<std::size_t>(count, 1));
    const btor2_nid_t sorts[] = {
      data_sort,
      bitmap_sort,
      bitmap_sort,
      bool_sort,
      bool_sort,
      pointer_sort,
      bool_sort};
    const char *names[] = {
      "data", "written", "defined", "live", "zeroed", "size", "readonly"};
    for(std::size_t i = 0; i < object.fields.size(); ++i)
    {
      const auto initial =
        i == static_cast<std::size_t>(fieldt::data) ? 0 : b.zero(sorts[i]);
      auto state = b.state(
        sorts[i],
        "__initial_object_" + std::to_string(identity) + "_" + names[i]);
      // Only BV metadata is zero-initialized. No constant-array term is needed.
      if(initial)
        b.init(sorts[i], state, initial);
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
    for(unsigned i = 0; i < budget; ++i)
    {
      // Allocation sites may have different typed uses: keep a local byte view.
      append(first_heap_tag + i, mp_integer(allocation_capacity()), typet{});
      if(failed)
        return;
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
  case fieldt::defined:
    return defined;
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
  if(
    field != fieldt::data && field != fieldt::written &&
    field != fieldt::defined)
    return value;
  const auto arithmetic_bits = std::max(pointer_bits, 32u);
  const auto arithmetic_sort = b.get_or_create_bitvec_sort(arithmetic_bits);
  auto wide_off = resize_unsigned(off, pointer_bits, arithmetic_bits);
  if(field != fieldt::data)
    return extract_bits(
      value, std::max<std::size_t>(object.capacity, 1), wide_off, 1);
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
  if(
    field != fieldt::data && field != fieldt::written &&
    field != fieldt::defined)
    return byte;
  const auto arithmetic_bits = std::max(pointer_bits, 32u);
  const auto arithmetic_sort = b.get_or_create_bitvec_sort(arithmetic_bits);
  auto wide_off = resize_unsigned(off, pointer_bits, arithmetic_bits);
  if(field != fieldt::data)
    return replace_bits(
      value, std::max<std::size_t>(object.capacity, 1), wide_off, byte, 1);
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

btor2_nid_t heap_modelt::read_field(fieldt field, btor2_nid_t index)
{
  const auto sort = field == fieldt::data   ? byte_sort
                    : field == fieldt::size ? pointer_sort
                                            : bool_sort;
  if(!array_encoding.object_memory)
    return read_storage(sort, global_field(field), index);
  const bool byte_addressed = field == fieldt::data ||
                              field == fieldt::written ||
                              field == fieldt::defined;
  auto identity = byte_addressed ? tag(index) : index;
  auto off = byte_addressed
               ? resize_unsigned(offset(index), offset_bits, pointer_bits)
               : b.zero(pointer_sort);
  auto result = b.zero(sort);
  for(const auto &object : local_objects)
  {
    auto guard = b.eq(bool_sort, identity, b.constd(tag_sort, object.tag));
    if(byte_addressed)
      guard = b.land(
        bool_sort,
        guard,
        b.ult(bool_sort, off, b.constd(pointer_sort, object.capacity)));
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
  const bool byte_addressed = field == fieldt::data ||
                              field == fieldt::written ||
                              field == fieldt::defined;
  auto identity = byte_addressed ? tag(index) : index;
  auto off = byte_addressed
               ? resize_unsigned(offset(index), offset_bits, pointer_bits)
               : b.zero(pointer_sort);
  for(const auto &object : local_objects)
  {
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
        b.ult(bool_sort, off, b.constd(pointer_sort, object.capacity)));
    auto &u = update(object.fields[static_cast<std::size_t>(field)]);
    auto changed = local_write(object, field, u.local, off, value);
    u.local = b.ite(u.sort, guard, changed, u.local);
  }
}

bool heap_modelt::use_bv_word_access() const
{
  return array_encoding.object_memory && array_encoding.bitvectors &&
    config.ansi_c.endianness == configt::ansi_ct::endiannesst::IS_LITTLE_ENDIAN;
}

btor2_nid_t heap_modelt::load_bv_word(btor2_nid_t p, unsigned bytes)
{
  const auto arithmetic_bits = std::max(pointer_bits, 32u);
  const auto arithmetic_sort = b.get_or_create_bitvec_sort(arithmetic_bits);
  const auto off = resize_unsigned(offset(p), offset_bits, arithmetic_bits);
  const auto bit = b.mul(arithmetic_sort, off, b.constd(arithmetic_sort, byte_bits));
  const auto word_sort = b.get_or_create_bitvec_sort(bytes * byte_bits);
  const auto flags_sort = b.get_or_create_bitvec_sort(bytes);
  auto result = b.zero(word_sort), defined_ok = b.zero(bool_sort);
  for(const auto &object : local_objects)
  {
    if(object.capacity < bytes)
      continue;
    const auto guard = b.land(bool_sort,
      b.eq(bool_sort, tag(p), b.constd(tag_sort, object.tag)),
      b.ulte(bool_sort, off, b.constd(arithmetic_sort, object.capacity - bytes)));
    const auto written = extract_bits(object.fields[1], object.capacity, off, bytes);
    const auto defined_bytes = extract_bits(object.fields[2], object.capacity, off, bytes);
    const auto valid_written = b.eq(bool_sort,
      b.land(flags_sort, written, defined_bytes), written);
    const auto initialized = b.lor(bool_sort, object.fields[4],
      b.eq(bool_sort, written, b.ones(flags_sort)));
    defined_ok = b.lor(bool_sort, defined_ok,
      b.land(bool_sort, guard, b.land(bool_sort, valid_written, initialized)));
    // The same per-byte written flags that select byte_value() form a word
    // mask. Unwritten calloc bytes are zero; copied undefined bytes still
    // require the independent definedness guard above.
    btor2_nid_t mask = 0;
    for(unsigned i = 0; i < bytes; ++i)
    {
      const auto flag = b.slice(bool_sort, written, i, i);
      const auto lane = b.ite(byte_sort, flag, b.ones(byte_sort), b.zero(byte_sort));
      mask = mask ? b.concat(b.get_or_create_bitvec_sort((i + 1) * byte_bits), lane, mask) : lane;
    }
    const auto data = extract_bits(object.fields[0],
      object.element_bytes * byte_bits * object.elements, bit, bytes * byte_bits);
    result = b.ite(word_sort, guard, b.land(word_sort, data, mask), result);
  }
  require(defined_ok, true);
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
    if(object.capacity < bytes)
      continue;
    const auto guard = b.land(bool_sort, path_guard,
      b.land(bool_sort, b.eq(bool_sort, tag(p), b.constd(tag_sort, object.tag)),
        b.ulte(bool_sort, off, b.constd(arithmetic_sort, object.capacity - bytes))));
    auto &data = update(object.fields[0]);
    data.local = b.ite(data.sort, guard,
      replace_bits(data.local, object.element_bytes * byte_bits * object.elements,
                   bit, value, bytes * byte_bits), data.local);
    for(unsigned field : {1u, 2u})
    {
      auto &flags = update(object.fields[field]);
      flags.local = b.ite(flags.sort, guard,
        replace_bits(flags.local, object.capacity, off,
                     b.ones(b.get_or_create_bitvec_sort(bytes)), bytes), flags.local);
    }
  }
}
