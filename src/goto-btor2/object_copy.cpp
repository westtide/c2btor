#include <util/invariant.h>

#include "heap_model.h"

#include <algorithm>

// Atomic prefix/range copy for packed, little-endian object storage. Read all
// source fields from the pre-state, then update destination fields together.
// This is the same snapshot relation as the two byte loops, including copying
// indeterminate bytes without treating their later typed reads as initialized.
void heap_modelt::copy_range(
  btor2_nid_t destination,
  btor2_nid_t source,
  btor2_nid_t bytes)
{
  PRECONDITION(use_bv_word_access());
  const auto empty = b.eq(bool_sort, bytes, b.zero(pointer_sort));
  require(b.lor(bool_sort, empty, accessible(source, bytes, false)));
  require(b.lor(bool_sort, empty, accessible(destination, bytes, true)));
  const unsigned arithmetic_bits = std::max(pointer_bits, 32u);
  const auto arithmetic_sort = b.get_or_create_bitvec_sort(arithmetic_bits);
  const auto src_off =
    resize_unsigned(offset(source), offset_bits, arithmetic_bits);
  const auto dst_off =
    resize_unsigned(offset(destination), offset_bits, arithmetic_bits);
  const auto count = resize_unsigned(bytes, pointer_bits, arithmetic_bits);
  const auto src_bit =
    b.mul(arithmetic_sort, src_off, b.constd(arithmetic_sort, byte_bits));
  const auto dst_bit =
    b.mul(arithmetic_sort, dst_off, b.constd(arithmetic_sort, byte_bits));
  const auto count_bits =
    b.mul(arithmetic_sort, count, b.constd(arithmetic_sort, byte_bits));

  auto range_guard =
    [&](const local_objectt &object, btor2_nid_t pointer, btor2_nid_t off)
  {
    const auto capacity = b.constd(arithmetic_sort, object.capacity);
    return b.land(
      bool_sort,
      b.eq(bool_sort, tag(pointer), b.constd(tag_sort, object.tag)),
      b.land(
        bool_sort,
        b.ulte(bool_sort, off, capacity),
        b.ulte(bool_sort, count, b.sub(arithmetic_sort, capacity, off))));
  };
  auto src_capacity = empty, dst_capacity = empty;
  for(const auto &object : local_objects)
  {
    src_capacity =
      b.lor(bool_sort, src_capacity, range_guard(object, source, src_off));
    dst_capacity =
      b.lor(bool_sort, dst_capacity, range_guard(object, destination, dst_off));
  }
  require(b.land(bool_sort, src_capacity, dst_capacity), true);

  // Resolving unwritten bytes once per source avoids dispatching every byte
  // over every object. calloc supplies zero and definedness; malloc does not.
  struct snapshott
  {
    btor2_nid_t guard, data, defined;
    unsigned bits, flags;
  };
  std::vector<snapshott> snapshots;
  for(const auto &object : local_objects)
  {
    const unsigned flags = std::max<std::size_t>(object.capacity, 1);
    const unsigned bits = object.element_bytes * byte_bits * object.elements;
    const auto flags_sort = b.get_or_create_bitvec_sort(flags);
    btor2_nid_t byte_mask = 0;
    for(unsigned i = 0; i < flags; ++i)
    {
      const auto lane = b.ite(
        byte_sort,
        b.slice(bool_sort, object.fields[1], i, i),
        b.ones(byte_sort),
        b.zero(byte_sort));
      byte_mask =
        byte_mask
          ? b.concat(
              b.get_or_create_bitvec_sort((i + 1) * byte_bits), lane, byte_mask)
          : lane;
    }
    const auto data = b.land(
      b.get_or_create_bitvec_sort(bits),
      object.fields[0],
      resize_unsigned(byte_mask, flags * byte_bits, bits));
    const auto initialized = b.lor(
      flags_sort,
      b.land(flags_sort, object.fields[1], object.fields[2]),
      b.ite(
        flags_sort,
        object.fields[4],
        b.lnot(flags_sort, object.fields[1]),
        b.zero(flags_sort)));
    snapshots.push_back(
      {range_guard(object, source, src_off),
       b.srl(
         b.get_or_create_bitvec_sort(bits),
         data,
         resize_unsigned(src_bit, arithmetic_bits, bits)),
       b.srl(
         flags_sort,
         initialized,
         resize_unsigned(src_off, arithmetic_bits, flags)),
       bits,
       flags});
  }
  for(const auto &object : local_objects)
  {
    const unsigned flags = std::max<std::size_t>(object.capacity, 1);
    const unsigned bits = object.element_bytes * byte_bits * object.elements;
    const auto data_sort = b.get_or_create_bitvec_sort(bits);
    const auto flags_sort = b.get_or_create_bitvec_sort(flags);
    auto data = b.zero(data_sort), defined_flags = b.zero(flags_sort);
    for(const auto &snapshot : snapshots)
    {
      data = b.ite(
        data_sort,
        snapshot.guard,
        resize_unsigned(snapshot.data, snapshot.bits, bits),
        data);
      defined_flags = b.ite(
        flags_sort,
        snapshot.guard,
        resize_unsigned(snapshot.defined, snapshot.flags, flags),
        defined_flags);
    }
    auto merge = [&](
                   unsigned field,
                   unsigned width,
                   btor2_nid_t shift,
                   btor2_nid_t length,
                   btor2_nid_t value)
    {
      auto &u = update(object.fields[field]);
      const auto sort = u.sort;
      // BV shifts by the full width produce zero: subtracting one therefore
      // produces the full mask when the copied range fills the object.
      auto mask = b.sub(
        sort,
        b.sll(
          sort, b.one(sort), resize_unsigned(length, arithmetic_bits, width)),
        b.one(sort));
      mask = b.sll(sort, mask, resize_unsigned(shift, arithmetic_bits, width));
      const auto changed = b.lor(
        sort,
        b.land(sort, u.local, b.lnot(sort, mask)),
        b.land(
          sort,
          mask,
          b.sll(sort, value, resize_unsigned(shift, arithmetic_bits, width))));
      u.local = b.ite(
        sort,
        b.land(
          bool_sort, path_guard, range_guard(object, destination, dst_off)),
        changed,
        u.local);
    };
    merge(0, bits, dst_bit, count_bits, data);
    merge(1, flags, dst_off, count, b.ones(flags_sort));
    merge(2, flags, dst_off, count, defined_flags);
  }
}
