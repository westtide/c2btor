// SPDX-License-Identifier: BSD-4-Clause
// SPDX-FileCopyrightText: 2026 C2BTOR contributors

#ifndef CPROVER_GOTO_BTOR2_HEAP_MODEL_H
#define CPROVER_GOTO_BTOR2_HEAP_MODEL_H

#include <util/expr.h>
#include <util/json.h>
#include <util/namespace.h>

#include "array_encoding.h"
#include "btor2_builder.h"
#include "memory_capacity.h"
#include "symbolic_heap_cells.h"

#include <array>
#include <map>
#include <set>
#include <vector>

/// Byte-addressed object storage. All views of an object share these states.
/// Object identities are never reused. Storage/identity support is checked
/// before model emission; memory operations never add properties or stop PC.
class heap_modelt
{
public:
  struct objectt
  {
    irep_idt id;
    typet type;
    exprt size;
    exprt initializer;
    bool static_lifetime;
    unsigned tag;
    bool read_only = false;
    bool recurrent = false;
    bool reuse_certified = false;
  };
  heap_modelt(
    btor2_buildert &,
    const namespacet &,
    unsigned allocation_budget,
    array_encoding_optionst = {});
  std::map<irep_idt, objectt> objects;
  // Logical arrays retain holes in the original static identity namespace,
  // without byte storage or byte-capacity/lifetime planning.
  std::set<irep_idt> reserved_root_ids;
  std::size_t static_identity_count() const
  {
    return objects.size() + reserved_root_ids.size();
  }
  // pointer_bits is always the source machine width, used for byte counts.
  unsigned pointer_bits, pointer_value_bits, object_bits, offset_bits, byte_bits;
  btor2_nid_t pointer_sort = 0, size_sort = 0, offset_sort = 0, tag_sort = 0;
  bool failed = false;
  std::string failure_reason;
  bool has_dynamic_allocations = false;
  bool uses_symbolic_allocation_storage() const
  {
    return symbolic_allocation_storage;
  }
  bool uses_wide_pointer_offsets() const
  {
    return pointer_value_bits != pointer_bits;
  }
  bool supports_runtime_object_reset() const { return array_encoding.object_memory; }
  void plan_capacity(const goto_programt &program);
  void create_states();
  void finish_initialization();
  void begin(unsigned pc, btor2_nid_t guard);
  void end();
  void finish();
  btor2_nid_t base(unsigned tag);
  btor2_nid_t tag(btor2_nid_t pointer);
  btor2_nid_t offset(btor2_nid_t pointer);
  btor2_nid_t size(btor2_nid_t pointer);
  btor2_nid_t is_live(btor2_nid_t pointer);
  btor2_nid_t is_dynamic(btor2_nid_t pointer);
  btor2_nid_t accessible(btor2_nid_t pointer, btor2_nid_t bytes, bool write);
  btor2_nid_t add_offset(btor2_nid_t pointer, btor2_nid_t signed_bytes);
  btor2_nid_t load(btor2_nid_t pointer, unsigned bits);
  void store(btor2_nid_t pointer, btor2_nid_t value, unsigned bits);
  // Constant-layout stores during static initialization, before any CFG step.
  // Returns false if the normal guarded store path must be used instead.
  bool try_initialize_store(
    unsigned tag, const mp_integer &offset, btor2_nid_t value, unsigned bits);
  void copy_byte(btor2_nid_t destination, btor2_nid_t source);
  void copy_range(
    btor2_nid_t destination, btor2_nid_t source, btor2_nid_t bytes);
  btor2_nid_t allocate(
    btor2_nid_t bytes,
    btor2_nid_t zero,
    bool may_zero_initialize = true,
    const exprt *alloc_size_expr = nullptr);
  void deallocate(btor2_nid_t pointer);
  void activate(const objectt &, btor2_nid_t bytes, bool zero);
  void deactivate(const objectt &);
  btor2_nid_t path_guard = 0;
  json_objectt metadata() const;

private:
  btor2_buildert &b;
  const namespacet &ns;
  array_encoding_optionst array_encoding;
  memory_capacity_boundst capacity_bounds;
  bool symbolic_allocation_storage = false;
  symbolic_heap_cell_certificatet symbolic_cells;
  std::set<btor2_nid_t> deferred_initial_next;
  btor2_nid_t known_identity(unsigned tag);
  std::size_t representation_capacity() const;
  mp_integer object_capacity(const objectt &) const;
  unsigned storage_element_bytes(const typet &) const;
  std::size_t allocation_capacity() const;
  struct packed_objectt
  {
    unsigned tag;
    std::size_t start, capacity;
  };
  struct packed_arrayt
  {
    unsigned element_bits;
    std::size_t elements;
    bool byte_addressed;
  };
  std::vector<packed_objectt> packed_objects;
  std::map<btor2_nid_t, packed_arrayt> packed_arrays;
  std::size_t packed_bytes = 0;
  std::map<btor2_nid_t, btor2_nid_t> packed_indices;
  unsigned budget, storage_slots, first_heap_tag = 0;
  std::string storage_slots_policy = "allocation-budget";
  unsigned current_pc = 0;
  btor2_nid_t current_guard = 0;
  bool initializing = false;
  btor2_nid_t initial_path_guard = 0;
  btor2_nid_t bool_sort = 0, byte_sort = 0;
  btor2_nid_t memory_sort = 0, written_sort = 0, flags_sort = 0, sizes_sort = 0;
  btor2_nid_t memory = 0, written = 0, live = 0, zeroed = 0, sizes = 0,
              fresh = 0;
  btor2_nid_t readonly = 0;
  struct updatet
  {
    btor2_nid_t sort, state, local, next;
  };
  std::vector<updatet> updates;
  json_arrayt allocation_sites;
  updatet &update(btor2_nid_t state);
  enum class fieldt
  {
    data,
    live,
    size,
    readonly,
    // Only a global native Array needs lazy range-zero data bookkeeping.
    written,
    zeroed
  };
  struct local_objectt
  {
    unsigned tag, element_bytes, index_bits;
    std::size_t capacity, elements;
    bool native_array, symbolic_capacity;
    btor2_nid_t index_sort, element_sort;
    std::array<btor2_nid_t, 4> fields{};
  };
  std::vector<local_objectt> local_objects;
  // Sound finite tag sets for immutable pointer terms constructed here.
  // Absence means unknown: runtime pointer states always retain full dispatch.
  using tag_sett = std::set<mp_integer>;
  std::map<btor2_nid_t, tag_sett> pointer_tags, identity_tags;
  bool may_select_object(btor2_nid_t term, unsigned tag, bool pointer) const;
  btor2_nid_t byte_address(btor2_nid_t pointer, unsigned delta);
  void create_object_states();
  void initialize_object_data(btor2_nid_t identity, btor2_nid_t zero);
  bool uses_lazy_zero_initialization() const
  {
    return !array_encoding.object_memory && !array_encoding.bitvectors;
  }
  void reset_automatic_object(const objectt &);
  std::map<btor2_nid_t, btor2_nid_t> zero_arrays;
  bool use_bv_word_access() const;
  btor2_nid_t load_bv_word(btor2_nid_t pointer, unsigned bytes);
  void store_bv_word(btor2_nid_t pointer, btor2_nid_t value, unsigned bytes);
  bool use_array_word_access() const;
  btor2_nid_t load_array_word(btor2_nid_t pointer, unsigned bytes);
  void store_array_word(btor2_nid_t pointer, btor2_nid_t value, unsigned bytes);
  struct array_windowt
  {
    std::vector<btor2_nid_t> indices, active;
    btor2_nid_t data, sort, shift;
    unsigned bits;
  };
  array_windowt array_window(
    const local_objectt &, btor2_nid_t data, btor2_nid_t offset, unsigned bytes);
  btor2_nid_t global_field(fieldt) const;
  btor2_nid_t read_field(fieldt, btor2_nid_t index);
  void write_meta(fieldt, btor2_nid_t index, btor2_nid_t value);
  btor2_nid_t local_read(
    const local_objectt &,
    fieldt,
    btor2_nid_t value,
    btor2_nid_t offset);
  btor2_nid_t local_write(
    const local_objectt &,
    fieldt,
    btor2_nid_t value,
    btor2_nid_t offset,
    btor2_nid_t element);
  // off has the machine pointer width. This is a storage-selection condition,
  // independent of live/readonly predicates or source verification properties.
  btor2_nid_t local_capacity_guard(
    const local_objectt &,
    btor2_nid_t off,
    unsigned bytes,
    bool byte_dispatch = false);
  btor2_nid_t resize_unsigned(btor2_nid_t, unsigned from, unsigned to);
  btor2_nid_t extract_bits(
    btor2_nid_t value,
    unsigned bits,
    btor2_nid_t bit_offset,
    unsigned width);
  btor2_nid_t replace_bits(
    btor2_nid_t value,
    unsigned bits,
    btor2_nid_t bit_offset,
    btor2_nid_t element,
    unsigned width);
  btor2_nid_t byte_value(btor2_nid_t pointer);
  bool prepare_packed_objects();
  btor2_nid_t packed_index(btor2_nid_t index, bool byte_addressed);
  btor2_nid_t packed_shift(btor2_nid_t index, const packed_arrayt &);
  btor2_nid_t
  read_storage(btor2_nid_t element_sort, btor2_nid_t state, btor2_nid_t index);
  btor2_nid_t write_storage(
    btor2_nid_t state,
    btor2_nid_t value,
    btor2_nid_t index,
    btor2_nid_t element);
};
#endif
