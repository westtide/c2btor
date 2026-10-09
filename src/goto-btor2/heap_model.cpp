#include "heap_model.h"

#include <util/arith_tools.h>
#include <util/config.h>
#include <util/invariant.h>
#include <util/simplify_expr.h>

#include <algorithm>
#include <limits>

heap_modelt::heap_modelt(
  btor2_buildert &builder,
  const namespacet &ns,
  unsigned allocation_budget,
  array_encoding_optionst array_encoding)
  : pointer_bits(config.ansi_c.pointer_width),
    offset_bits(pointer_bits - config.bv_encoding.object_bits),
    byte_bits(config.ansi_c.char_width),
    b(builder),
    ns(ns),
    array_encoding(array_encoding),
    budget(allocation_budget)
{
}

void heap_modelt::plan_capacity(const goto_programt &program)
{
  if(
    array_encoding.max_object_bytes ||
    (!array_encoding.bitvectors && !array_encoding.object_memory))
    return;
  std::map<irep_idt, exprt> sizes;
  for(const auto &entry : objects)
    sizes.emplace(entry.first, entry.second.size);
  capacity_bounds = infer_memory_capacity(program, ns, sizes);
}

std::size_t heap_modelt::representation_capacity() const
{
  // Pure BV storage and byte-definedness metadata have fixed BTOR2 widths.
  // This ceiling comes from the target pointer and the format, not an
  // arbitrary default object size. The runtime size guard remains active.
  const mp_integer pointer_limit = (mp_integer(1) << (offset_bits - 1)) - 1;
  const mp_integer width_limit = std::numeric_limits<int>::max() / byte_bits;
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
  auto ceiling = representation_capacity();
  if(array_encoding.object_memory)
  {
    // A typed cell must fit too. Rounding INT_MAX/byte_bits up to an int
    // cell would otherwise reject an unconstrained LP64 VLA at this ceiling.
    const auto cell = storage_element_bytes(object.type);
    ceiling = ceiling / cell * cell;
  }
  const mp_integer limit = ceiling;
  return found == capacity_bounds.objects.end()
           ? limit
           : std::min(limit, found->second);
}

std::size_t heap_modelt::allocation_capacity() const
{
  if(array_encoding.max_object_bytes)
    return *array_encoding.max_object_bytes;
  const mp_integer limit = representation_capacity();
  return numeric_cast_v<std::size_t>(
    std::min(limit, capacity_bounds.allocation));
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
  if(
    config.bv_encoding.object_bits == 0 ||
    config.bv_encoding.object_bits + 1 >= pointer_bits)
  {
    failed = true;
    return;
  }
  bool_sort = b.get_bool_sort();
  pointer_sort = b.get_or_create_bitvec_sort(pointer_bits);
  offset_sort = b.get_or_create_bitvec_sort(offset_bits);
  tag_sort = b.get_or_create_bitvec_sort(config.bv_encoding.object_bits);
  byte_sort = b.get_or_create_bitvec_sort(byte_bits);
  first_heap_tag = static_cast<unsigned>(objects.size()) + 3;
  // Leave room for the exhausted counter value as well as all live identities.
  if(
    mp_integer(first_heap_tag) + budget >=
    (mp_integer(1) << config.bv_encoding.object_bits))
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
    const std::size_t object_slots = static_cast<std::size_t>(first_heap_tag) +
                                     (has_dynamic_allocations ? budget : 0);
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
      written_sort = b.get_or_create_bitvec_sort(packed_bytes);
      flags_sort = b.get_or_create_bitvec_sort(object_slots);
      sizes_sort = b.get_or_create_bitvec_sort(object_slots * pointer_bits);
    }
    else
    {
      memory_sort = b.sort_array(pointer_sort, byte_sort);
      written_sort = b.sort_array(pointer_sort, bool_sort);
      flags_sort = b.sort_array(tag_sort, bool_sort);
      sizes_sort = b.sort_array(tag_sort, pointer_sort);
    }
    memory = state(memory_sort, "__initial_memory_bytes", 0);
    const auto written_zero =
      array_encoding.bitvectors ? written_sort : bool_sort;
    const auto flags_zero = array_encoding.bitvectors ? flags_sort : bool_sort;
    const auto sizes_zero =
      array_encoding.bitvectors ? sizes_sort : pointer_sort;
    written =
      state(written_sort, "__initial_memory_written", b.zero(written_zero));
    defined =
      state(written_sort, "__initial_memory_defined", b.zero(written_zero));
    live = state(flags_sort, "__initial_object_live", b.zero(flags_zero));
    zeroed = state(flags_sort, "__initial_object_zeroed", b.zero(flags_zero));
    sizes = state(sizes_sort, "__initial_object_size", b.zero(sizes_zero));
    readonly =
      state(flags_sort, "__initial_object_readonly", b.zero(flags_zero));
    if(array_encoding.bitvectors)
    {
      packed_arrays.emplace(
        memory, packed_arrayt{byte_bits, packed_bytes, true});
      for(auto s : {written, defined})
        packed_arrays.emplace(s, packed_arrayt{1, packed_bytes, true});
      for(auto s : {live, zeroed, readonly})
        packed_arrays.emplace(s, packed_arrayt{1, object_slots, false});
      packed_arrays.emplace(
        sizes, packed_arrayt{pointer_bits, object_slots, false});
    }
    for(const auto s :
        {memory, written, defined, live, zeroed, sizes, readonly})
      b.next(update(s).sort, s, s);
  }
  fresh =
    state(tag_sort, "__next_heap_object", b.constd(tag_sort, first_heap_tag));
  halted = state(bool_sort, "__memory_halted", b.zero(bool_sort));
  all_faults = b.zero(bool_sort);
  path_guard = b.one(bool_sort);
}

void heap_modelt::finish_initialization()
{
  std::vector<btor2_nid_t *> states;
  if(array_encoding.object_memory)
  {
    for(auto &object : local_objects)
      for(auto &field : object.fields)
        states.push_back(&field);
  }
  else
    states = {&memory, &written, &defined, &live, &zeroed, &sizes, &readonly};
  for(auto *s : states)
  {
    auto &u = update(*s);
    auto state = b.state(u.sort, "__memory_state_" + std::to_string(*s));
    b.init(u.sort, state, u.local);
    if(array_encoding.bitvectors && !array_encoding.object_memory)
      packed_arrays.emplace(state, packed_arrays.at(*s));
    u.state = u.local = u.next = state;
    *s = state;
  }
}

btor2_nid_t heap_modelt::base(unsigned t)
{
  return b.constd(pointer_sort, mp_integer(t) << offset_bits);
}
btor2_nid_t heap_modelt::tag(btor2_nid_t p)
{
  return b.slice(tag_sort, p, pointer_bits - 1, offset_bits);
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
  current_guard = b.land(bool_sort, guard, b.lnot(bool_sort, halted));
  memory_ok = capacity_ok = path_guard = b.one(bool_sort);
  memory_checked = capacity_checked = false;
  for(auto &u : updates)
    u.local = u.state;
}
void heap_modelt::require(btor2_nid_t condition, bool capacity)
{
  if(!current_guard)
    return;
  (capacity ? capacity_checked : memory_checked) = true;
  auto &ok = capacity ? capacity_ok : memory_ok;
  ok = b.land(
    bool_sort, ok, b.lor(bool_sort, b.lnot(bool_sort, path_guard), condition));
}

void heap_modelt::end()
{
  auto ok = b.land(bool_sort, memory_ok, capacity_ok);
  valid[current_pc] = b.land(bool_sort, ok, b.lnot(bool_sort, halted));
  auto guard = b.land(bool_sort, current_guard, ok);
  for(auto &u : updates)
    if(u.local != u.state)
      u.next = b.ite(u.sort, guard, u.local, u.next);
  for(const auto &item : std::vector<std::pair<btor2_nid_t, std::string>>{
        {memory_ok, "memory_validity"}, {capacity_ok, "model_limit"}})
  {
    if(item.second == "memory_validity" ? !memory_checked : !capacity_checked)
      continue;
    auto bad = b.land(bool_sort, current_guard, b.lnot(bool_sort, item.first));
    // Suppressing diagnostic properties never disables fault halting.
    all_faults = b.lor(bool_sort, all_faults, bad);
    proof_obligations.push_back({current_pc, bad, item.second});
    b.comment("c2btor-proof-obligation " + item.second + " " +
              std::to_string(bad));
    if(emit_guard_properties)
    {
      const auto name = item.second + "_at_" + std::to_string(current_pc);
      auto node = emit_bad_properties ? b.bad(bad, name) : 0;
      auto output = emit_bad_properties ? 0 : b.output(bad, name);
      properties.push_back({current_pc, node, item.second, bad, output});
    }
  }
  current_guard = 0;
}
void heap_modelt::finish()
{
  update(halted).next = b.lor(bool_sort, halted, all_faults);
  for(const auto &u : updates)
    b.next(u.sort, u.state, u.next);
}
btor2_nid_t heap_modelt::valid_at(unsigned pc) const
{
  const auto it = valid.find(pc);
  return it == valid.end() ? 0 : it->second;
}

btor2_nid_t heap_modelt::add_offset(btor2_nid_t p, btor2_nid_t delta)
{
  // Extended signed arithmetic prevents offset carry from changing the tag.
  auto wide = b.get_or_create_bitvec_sort(pointer_bits + 1);
  auto sum = b.add(
    wide,
    b.sext(wide, offset(p), pointer_bits + 1 - offset_bits),
    b.sext(wide, delta, 1));
  auto narrowed = b.slice(offset_sort, sum, offset_bits - 1, 0);
  require(
    b.eq(
      bool_sort, sum, b.sext(wide, narrowed, pointer_bits + 1 - offset_bits)),
    true);
  return b.concat(pointer_sort, tag(p), narrowed);
}
btor2_nid_t heap_modelt::access_valid(btor2_nid_t p, unsigned bytes)
{
  return accessible(p, b.constd(pointer_sort, bytes), false);
}
btor2_nid_t heap_modelt::accessible(btor2_nid_t p, btor2_nid_t n, bool write)
{
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
  auto initialized = read_field(fieldt::written, p);
  auto zero = read_field(fieldt::zeroed, tag(p));
  // Indeterminate bytes require representation/effective-type reasoning that
  // is not implemented here. Report a model boundary, not invented zero data.
  require(
    b.ite(bool_sort, initialized, read_field(fieldt::defined, p), zero), true);
  return b.ite(
    byte_sort, initialized, read_field(fieldt::data, p), b.zero(byte_sort));
}
btor2_nid_t heap_modelt::load(btor2_nid_t p, unsigned bits)
{
  const unsigned bytes = (bits + byte_bits - 1) / byte_bits;
  const auto access_ok = access_valid(p, bytes);
  require(access_ok);
  // An invalid load is already a source memory fault. Its bytes need not
  // have a defined value; only valid loads require indeterminate-byte support.
  // Keep earlier address-representation limits independent of this guard.
  const auto saved_path_guard = path_guard;
  path_guard = b.land(bool_sort, path_guard, access_ok);
  btor2_nid_t result = use_bv_word_access() ? load_bv_word(p, bytes) : 0;
  for(unsigned i = 0; !use_bv_word_access() && i < bytes; ++i)
  {
    auto address = b.add(pointer_sort, p, b.constd(pointer_sort, i));
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
  path_guard = saved_path_guard;
  if(bits != bytes * byte_bits)
    result = b.slice(b.get_or_create_bitvec_sort(bits), result, bits - 1, 0);
  return result;
}
void heap_modelt::store(btor2_nid_t p, btor2_nid_t value, unsigned bits)
{
  const unsigned bytes = (bits + byte_bits - 1) / byte_bits;
  require(accessible(p, b.constd(pointer_sort, bytes), true));
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
  for(unsigned i = 0; i < bytes; ++i)
  {
    auto address = b.add(pointer_sort, p, b.constd(pointer_sort, i));
    const unsigned part =
      config.ansi_c.endianness == configt::ansi_ct::endiannesst::IS_BIG_ENDIAN
        ? bytes - 1 - i
        : i;
    auto byte =
      b.slice(byte_sort, value, (part + 1) * byte_bits - 1, part * byte_bits);
    write_meta(fieldt::data, address, byte);
    write_meta(fieldt::written, address, b.one(bool_sort));
    write_meta(fieldt::defined, address, b.one(bool_sort));
  }
}
void heap_modelt::copy_byte(btor2_nid_t destination, btor2_nid_t source)
{
  require(access_valid(source, 1));
  require(accessible(destination, b.one(pointer_sort), true));
  const auto source_written = read_field(fieldt::written, source);
  const auto source_defined = b.ite(
    bool_sort,
    source_written,
    read_field(fieldt::defined, source),
    read_field(fieldt::zeroed, tag(source)));
  const auto value = b.ite(
    byte_sort,
    source_written,
    read_field(fieldt::data, source),
    b.zero(byte_sort));
  write_meta(fieldt::data, destination, value);
  write_meta(fieldt::written, destination, b.one(bool_sort));
  write_meta(fieldt::defined, destination, source_defined);
}
btor2_nid_t heap_modelt::allocate(btor2_nid_t bytes, btor2_nid_t zero)
{
  const auto identity = update(fresh).local;
  if(array_encoding.bitvectors || array_encoding.object_memory)
    require(
      b.ulte(bool_sort, bytes, b.constd(pointer_sort, allocation_capacity())),
      true);
  json_objectt site;
  site["pc"] = json_numbert(std::to_string(current_pc));
  site["size_node"] = json_numbert(std::to_string(bytes));
  site["zero_initialize_node"] = json_numbert(std::to_string(zero));
  site["object_counter_state"] = json_numbert(std::to_string(fresh));
  allocation_sites.push_back(std::move(site));
  require(
    b.ult(bool_sort, identity, b.constd(tag_sort, first_heap_tag + budget)),
    true);
  require(
    b.ult(
      bool_sort,
      bytes,
      b.constd(pointer_sort, mp_integer(1) << (offset_bits - 1))),
    true);
  write_meta(fieldt::live, identity, b.one(bool_sort));
  write_meta(fieldt::size, identity, bytes);
  write_meta(fieldt::zeroed, identity, zero);
  update(fresh).local = b.ite(
    tag_sort, path_guard, b.add(tag_sort, identity, b.one(tag_sort)), identity);
  return b.concat(pointer_sort, identity, b.zero(offset_sort));
}
void heap_modelt::deallocate(btor2_nid_t p)
{
  auto nonnull = b.neq(bool_sort, p, b.zero(pointer_sort));
  require(b.lor(
    bool_sort,
    b.lnot(bool_sort, nonnull),
    b.land(
      bool_sort,
      is_live(p),
      b.land(
        bool_sort,
        is_dynamic(p),
        b.eq(bool_sort, offset(p), b.zero(offset_sort))))));
  auto previous = path_guard;
  path_guard = b.land(bool_sort, previous, nonnull);
  write_meta(fieldt::live, tag(p), b.zero(bool_sort));
  path_guard = previous;
}
void heap_modelt::activate(const objectt &o, btor2_nid_t bytes, bool zero)
{
  auto t = b.constd(tag_sort, o.tag);
  if(array_encoding.object_memory)
  {
    const auto slot = std::find_if(
      local_objects.begin(),
      local_objects.end(),
      [&](const local_objectt &object) { return object.tag == o.tag; });
    INVARIANT(slot != local_objects.end(), "local object exists");
    require(
      b.ulte(bool_sort, bytes, b.constd(pointer_sort, slot->capacity)), true);
  }
  else if(array_encoding.bitvectors)
  {
    const auto slot = std::find_if(
      packed_objects.begin(),
      packed_objects.end(),
      [&](const packed_objectt &object) { return object.tag == o.tag; });
    INVARIANT(slot != packed_objects.end(), "packed object exists");
    require(
      b.ulte(bool_sort, bytes, b.constd(pointer_sort, slot->capacity)), true);
  }
  require(
    b.ult(
      bool_sort,
      bytes,
      b.constd(pointer_sort, mp_integer(1) << (offset_bits - 1))),
    true);
  // A static slot cannot be reused as a fresh C lifetime in this first version.
  // Repeated DECL is diagnosed rather than retaining old initialized bytes.
  if(!o.static_lifetime)
    require(
      b.eq(bool_sort, read_field(fieldt::size, t), b.zero(pointer_sort)), true);
  write_meta(fieldt::live, t, b.one(bool_sort));
  write_meta(fieldt::size, t, bytes);
  write_meta(fieldt::zeroed, t, zero ? b.one(bool_sort) : b.zero(bool_sort));
  write_meta(
    fieldt::readonly, t, o.read_only ? b.one(bool_sort) : b.zero(bool_sort));
}
void heap_modelt::deactivate(const objectt &o)
{
  write_meta(fieldt::live, b.constd(tag_sort, o.tag), b.zero(bool_sort));
}
json_objectt heap_modelt::metadata() const
{
  json_objectt result;
  result["representation"] = json_stringt(
    array_encoding.object_memory ? "object-local-memory-v1"
                                 : "object-byte-memory-v1");
  result["memory_encoding"] =
    json_stringt(array_encoding.object_memory ? "object" : "global");
  result["array_encoding"] =
    json_stringt(array_encoding.bitvectors ? "bv" : "array");
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
      entry["capacity_bytes"] = json_numbert(std::to_string(object.capacity));
      entry["element_bits"] =
        json_numbert(std::to_string(object.element_bytes * byte_bits));
      entry["elements"] = json_numbert(std::to_string(object.elements));
      entry["index_bits"] = json_numbert(std::to_string(object.index_bits));
      entry["data_encoding"] =
        json_stringt(object.native_array ? "array" : "bv");
      const char *names[] = {
        "data", "written", "defined", "live", "zeroed", "size", "readonly"};
      json_objectt states;
      for(std::size_t i = 0; i < object.fields.size(); ++i)
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
  result["allocation_budget"] = json_numbert(std::to_string(budget));
  result["first_heap_tag"] = json_numbert(std::to_string(first_heap_tag));
  if(!array_encoding.object_memory)
    result["memory_state"] = json_numbert(std::to_string(memory));
  result["byte_width"] = json_numbert(std::to_string(byte_bits));
  if(array_encoding.object_memory || array_encoding.bitvectors)
  {
    result["capacity_policy"] =
      json_stringt(array_encoding.max_object_bytes ? "explicit" : "automatic");
    result["representation_capacity_bytes"] =
      json_numbert(std::to_string(representation_capacity()));
    result["allocation_capacity_bytes"] =
      json_numbert(std::to_string(allocation_capacity()));
  }
  else
    result["capacity_policy"] = json_stringt("pointer-addressed");
  result["offset_width"] = json_numbert(std::to_string(offset_bits));
  json_arrayt obligations;
  for(const auto &p : proof_obligations)
  {
    json_objectt entry;
    entry["pc"] = json_numbert(std::to_string(p.pc));
    entry["condition_node"] = json_numbert(std::to_string(p.condition));
    entry["property_class"] = json_stringt(p.kind);
    obligations.push_back(std::move(entry));
  }
  result["proof_obligations"] = std::move(obligations);
  result["frozen_on_violation"] = jsont::json_boolean(true);
  result["allocation_sites"] = allocation_sites;
  json_arrayt props;
  for(const auto &p : properties)
  {
    json_objectt entry;
    entry["pc"] = json_numbert(std::to_string(p.pc));
    entry["bad_node"] = json_numbert(std::to_string(p.node));
    entry["condition_node"] = json_numbert(std::to_string(p.condition));
    entry["output_node"] = json_numbert(std::to_string(p.output_node));
    entry["property_class"] = json_stringt(p.kind);
    props.push_back(std::move(entry));
  }
  result["properties"] = std::move(props);
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
  if(has_dynamic_allocations && budget != 0)
  {
    for(unsigned i = 0; i < budget; ++i)
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
    return b.uext(
      pointer_sort, index, pointer_bits - config.bv_encoding.object_bits);
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
