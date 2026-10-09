#ifndef CPROVER_GOTO_BTOR2_HEAP_MODEL_H
#define CPROVER_GOTO_BTOR2_HEAP_MODEL_H

#include <util/expr.h>
#include <util/json.h>
#include <util/namespace.h>

#include "array_encoding.h"
#include "btor2_builder.h"
#include "memory_capacity.h"

#include <array>
#include <map>
#include <vector>

/// Byte-addressed object storage. All views of an object share these states.
/// Object identities are never reused; exceeding the allocation budget is a
/// model-limit property, not allocation failure and not a source violation.
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
  };
  struct propertyt
  {
    unsigned pc;
    btor2_nid_t node;
    std::string kind;
    btor2_nid_t condition;
    btor2_nid_t output_node;
  };
  heap_modelt(
    btor2_buildert &,
    const namespacet &,
    unsigned allocation_budget,
    array_encoding_optionst = {});
  std::map<irep_idt, objectt> objects;
  std::vector<propertyt> properties;
  // Proof obligations survive suppression of user-facing auxiliary bads.
  struct obligationt
  {
    unsigned pc;
    btor2_nid_t condition;
    std::string kind;
  };
  std::vector<obligationt> proof_obligations;
  bool emit_bad_properties = true;
  unsigned pointer_bits, offset_bits, byte_bits;
  btor2_nid_t pointer_sort = 0, offset_sort = 0, tag_sort = 0;
  btor2_nid_t halted = 0;
  bool failed = false;
  std::string failure_reason;
  bool has_dynamic_allocations = false;
  /// Emit memory_validity/model_limit guard bad states. The halting semantics
  /// (all_faults -> halted) is unaffected by this flag; only the reporting
  /// bad lines and map entries are suppressed.
  bool emit_guard_properties = true;

  void plan_capacity(const goto_programt &program);
  void create_states();
  void finish_initialization();
  void begin(unsigned pc, btor2_nid_t guard);
  void end();
  void finish();
  btor2_nid_t valid_at(unsigned pc) const;
  btor2_nid_t faults() const
  {
    return all_faults;
  }
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
  void copy_byte(btor2_nid_t destination, btor2_nid_t source);
  void copy_range(
    btor2_nid_t destination, btor2_nid_t source, btor2_nid_t bytes);
  btor2_nid_t allocate(btor2_nid_t bytes, btor2_nid_t zero);
  void deallocate(btor2_nid_t pointer);
  void activate(const objectt &, btor2_nid_t bytes, bool zero);
  void deactivate(const objectt &);
  void require(btor2_nid_t condition, bool capacity = false);
  btor2_nid_t path_guard = 0;
  json_objectt metadata() const;

private:
  btor2_buildert &b;
  const namespacet &ns;
  array_encoding_optionst array_encoding;
  memory_capacity_boundst capacity_bounds;
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
  unsigned budget, first_heap_tag = 0;
  unsigned current_pc = 0;
  btor2_nid_t current_guard = 0, memory_ok = 0, capacity_ok = 0;
  bool memory_checked = false, capacity_checked = false;
  btor2_nid_t bool_sort = 0, byte_sort = 0;
  btor2_nid_t memory_sort = 0, written_sort = 0, flags_sort = 0, sizes_sort = 0;
  btor2_nid_t memory = 0, written = 0, live = 0, zeroed = 0, sizes = 0,
              fresh = 0;
  btor2_nid_t readonly = 0;
  btor2_nid_t defined = 0;
  struct updatet
  {
    btor2_nid_t sort, state, local, next;
  };
  std::vector<updatet> updates;
  btor2_nid_t all_faults = 0;
  std::map<unsigned, btor2_nid_t> valid;
  json_arrayt allocation_sites;
  updatet &update(btor2_nid_t state);
  enum class fieldt
  {
    data,
    written,
    defined,
    live,
    zeroed,
    size,
    readonly
  };
  struct local_objectt
  {
    unsigned tag, element_bytes, index_bits;
    std::size_t capacity, elements;
    bool native_array;
    btor2_nid_t index_sort, element_sort;
    std::array<btor2_nid_t, 7> fields{};
  };
  std::vector<local_objectt> local_objects;
  void create_object_states();
  bool use_bv_word_access() const;
  btor2_nid_t load_bv_word(btor2_nid_t pointer, unsigned bytes);
  void store_bv_word(btor2_nid_t pointer, btor2_nid_t value, unsigned bytes);
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
  btor2_nid_t access_valid(btor2_nid_t pointer, unsigned bytes);
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
