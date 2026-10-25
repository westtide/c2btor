// SPDX-License-Identifier: BSD-4-Clause
// SPDX-FileCopyrightText: 2026 C2BTOR contributors

#include "source_event_provenance.h"
#include <util/arith_tools.h>
#include <util/find_symbols.h>
#include <util/json_irep.h>
#include <util/namespace.h>
#include <util/simplify_expr.h>
#include <util/std_expr.h>
#include <util/std_types.h>
#include <util/symbol.h>
#include <langapi/language_util.h>
#include <optional>
#include <sstream>

namespace
{
json_numbert number(std::size_t n) { return json_numbert(std::to_string(n)); }
json_objectt location(const source_locationt &s)
{
  json_objectt v;
  v["file_name"] = json_stringt(id2string(s.get_file()));
  v["line"] = json_stringt(id2string(s.get_line()));
  v["column"] = json_stringt(id2string(s.get_column()));
  v["function"] = json_stringt(id2string(s.get_function()));
  return v;
}
auto signatures(const goto_programt &program)
{
  std::map<std::size_t, std::vector<std::string>> result;
  for(const auto &ins : program.instructions)
    for(const auto id : btor2_original_event_ids(ins.source_location()))
      result[id].push_back(btor2_event_signature(ins));
  return result;
}
bool source_nondet(const goto_programt::instructiont &ins, const namespacet &ns)
{
  const auto &source = ins.source_location();
  if(source.get_file().empty() || id2string(source.get_file()).front() == '<')
    return false;
  return btor2_source_nondet_call(ins, ns).has_value();
}

// Only the original, direct C designator is useful for disambiguating calls
// on one line. A rewritten *p may look like x after alias simplification.
std::optional<json_objectt> source_result_destination(
  const exprt &lhs, const namespacet &ns)
{
  const exprt *root = &lhs;
  std::vector<mp_integer> reversed_indices;
  while(root->id() == ID_index)
  {
    const auto &index = to_index_expr(*root);
    if(index.array().type().id() != ID_array)
      return {};
    const auto constant = numeric_cast<mp_integer>(simplify_expr(index.index(), ns));
    if(!constant)
      return {};
    reversed_indices.push_back(*constant);
    root = &index.array();
  }
  if(root->id() != ID_symbol)
    return {};
  const auto &id = to_symbol_expr(*root).get_identifier();
  const symbolt *symbol = nullptr;
  if(ns.lookup(id, symbol) || !symbol || symbol->is_auxiliary ||
     symbol->base_name.empty())
    return {};
  std::string canonical = id2string(symbol->base_name);
  json_arrayt indices;
  for(auto it = reversed_indices.rbegin(); it != reversed_indices.rend(); ++it)
  {
    const auto value = integer2string(*it);
    indices.push_back(json_stringt(value));
    canonical += "[" + value + "]";
  }
  json_objectt result;
  result["kind"] = json_stringt(indices.empty() ? "scalar-symbol" : "constant-array-element");
  result["symbol"] = json_stringt(id2string(id));
  result["source_name"] = json_stringt(id2string(symbol->base_name));
  result["constant_indices"] = std::move(indices);
  result["canonical"] = json_stringt(canonical);
  return result;
}
}
std::optional<btor2_nondet_callt> btor2_source_nondet_call(
  const goto_programt::instructiont &ins, const namespacet &ns)
{
  btor2_nondet_callt result;
  const exprt *nondet = nullptr;
  if(ins.is_assign())
  {
    result.lhs = &ins.assign_lhs();
    nondet = &ins.assign_rhs();
    while(nondet->id() == ID_typecast)
    {
      const auto &cast = to_typecast_expr(*nondet);
      if(cast.type() != cast.op().type() &&
         !(cast.type().id() == ID_c_bool && cast.op().type().id() == ID_bool))
      {
        result.value_preserving = false;
        result.unsupported_reason = "cast-wrapped nondet return is not identity or canonical bool-to-c_bool";
      }
      nondet = &cast.op();
    }
    if(nondet->id() != ID_side_effect || nondet->get(ID_statement) != ID_nondet)
      return {};
    result.function = id2string(nondet->get(ID_C_identifier));
  }
  else if(ins.is_function_call() && ins.call_function().id() == ID_symbol)
  {
    result.lhs = &ins.call_lhs();
    result.function = id2string(to_symbol_expr(ins.call_function()).get_identifier());
  }
  else
    return {};
  if(result.function.rfind("__VERIFIER_nondet_", 0) != 0)
    return {};
  const symbolt *function = nullptr;
  if(ns.lookup(irep_idt(result.function), function) || function == nullptr ||
     function->type.id() != ID_code)
  {
    result.value_preserving = false;
    result.unsupported_reason = "source nondet function return declaration unavailable";
    return result;
  }
  result.return_type = to_code_type(function->type).return_type();
  if(result.lhs->type() != result.return_type)
  {
    result.value_preserving = false;
    result.unsupported_reason = "observed event result type differs from declared source return type";
  }
  if(nondet != nullptr && nondet->type() != result.return_type &&
     !(nondet->type().id() == ID_bool && result.return_type.id() == ID_c_bool))
  {
    result.value_preserving = false;
    result.unsupported_reason = "internal nondet type differs from declared source return type";
  }
  return result;
}
std::set<std::size_t> btor2_original_event_ids(const source_locationt &s)
{
  std::set<std::size_t> result;
  std::istringstream stream(id2string(s.get("c2btor_original_event_ids")));
  std::string id;
  while(std::getline(stream, id, ',')) if(!id.empty()) result.insert(std::stoull(id));
  return result;
}
json_arrayt btor2_original_event_ids_json(const source_locationt &s)
{
  json_arrayt result;
  for(const auto id : btor2_original_event_ids(s)) result.push_back(number(id));
  return result;
}
std::optional<json_objectt> btor2_call_return_location(const source_locationt &s)
{
  if(s.get("c2btor_call_return_file").empty() ||
     s.get("c2btor_call_return_line").empty() ||
     s.get("c2btor_call_return_column").empty())
    return {};
  json_objectt result;
  result["format"] = json_stringt("c2btor-c-call-site-1");
  result["file_name"] = json_stringt(id2string(s.get("c2btor_call_return_file")));
  result["line"] = json_numbert(id2string(s.get("c2btor_call_return_line")));
  result["column"] = json_numbert(id2string(s.get("c2btor_call_return_column")));
  result["evidence"] = json_stringt(id2string(s.get("c2btor_call_return_evidence")));
  return result;
}
void btor2_add_call_return_metadata(json_objectt &record, const source_locationt &s)
{
  if(const auto call_site = btor2_call_return_location(s))
    record["call_return_location"] = *call_site;
  if(!s.get("c2btor_call_return_unavailable").empty())
    record["call_return_location_unavailable"] =
      json_stringt(id2string(s.get("c2btor_call_return_unavailable")));
}
void btor2_merge_event_origins(source_locationt &to, const source_locationt &from)
{
  auto ids = btor2_original_event_ids(to);
  const auto more = btor2_original_event_ids(from);
  ids.insert(more.begin(), more.end());
  std::string value;
  for(const auto id : ids) { if(!value.empty()) value += ','; value += std::to_string(id); }
  to.set("c2btor_original_event_ids", value);
}
std::string btor2_event_signature(const goto_programt::instructiont &ins)
{
  const json_irept ir(false);
  json_objectt value;
  value["kind"] = json_stringt(ins.to_string());
  value["code"] = ir.convert_from_irep(ins.code());
  if(ins.has_condition()) value["condition"] = ir.convert_from_irep(ins.condition());
  json_arrayt targets;
  for(const auto &target : ins.targets)
    targets.push_back(btor2_original_event_ids_json(target->source_location()));
  value["targets"] = std::move(targets);
  std::ostringstream text;
  value.output(text);
  return text.str();
}
void btor2_capture_source_events(
  goto_programt &program, const namespacet &ns,
  btor2_source_provenancet &p, const std::string &stage)
{
  if(p.enabled) return;
  p.enabled = true; p.stage = stage;
  std::map<const goto_programt::instructiont *, std::size_t> order;
  std::size_t id = 0;
  for(auto &ins : program.instructions)
  {
    order[&ins] = id;
    ins.source_location_nonconst().set("c2btor_original_event_ids", std::to_string(id++));
    if(source_nondet(ins, ns)) ins.source_location_nonconst().set("c2btor_witness_value_root", true);
  }
  // Source locations are recorded once per event. Keep structural typed IR
  // without repeating comments/source trees on every nested expression.
  const json_irept ir(false), full_types(true);
  find_symbols_sett symbols;
  for(auto it = program.instructions.begin(); it != program.instructions.end(); ++it)
  {
    const auto &ins = *it; const auto event_id = order.at(&ins);
    json_objectt e;
    e["original_event_id"] = number(event_id); e["original_order"] = number(event_id);
    e["goto_location"] = number(ins.location_number); e["kind"] = json_stringt(ins.to_string());
    e["source"] = location(ins.source_location()); e["code_ir"] = ir.convert_from_irep(ins.code());
    btor2_add_call_return_metadata(e, ins.source_location());
    find_symbols(ins.code(), symbols);
    if(ins.has_condition()) { e["condition_ir"] = ir.convert_from_irep(ins.condition()); find_symbols(ins.condition(), symbols); }
    std::ostringstream text; ins.output(text); e["instruction"] = json_stringt(text.str());
    json_arrayt successors;
    for(const auto next : program.get_successors(it))
      if(next != program.instructions.end()) successors.push_back(number(order.at(&*next)));
    e["successors"] = std::move(successors);
    e["witness_value_root"] = jsont::json_boolean(source_nondet(ins, ns));
    if(source_nondet(ins, ns))
    {
      const auto call = btor2_source_nondet_call(ins, ns).value();
      const auto &lhs = *call.lhs;
      e["nondet_function"] = json_stringt(call.function);
      e["result_type_ir"] = full_types.convert_from_irep(call.return_type);
      if(!call.value_preserving)
        e["nondet_return_unsupported"] = json_stringt(call.unsupported_reason);
      const symbolt *result_symbol = nullptr;
      const bool auxiliary_result = lhs.id() == ID_symbol &&
        !ns.lookup(to_symbol_expr(lhs).get_identifier(), result_symbol) &&
        result_symbol != nullptr && result_symbol->is_auxiliary;
      e["result_is_auxiliary"] = jsont::json_boolean(auxiliary_result);
      // Some frontend nondet calls directly assign the source variable. In
      // that case its own LHS is the destination: following x := nondet; y := x
      // would incorrectly label the first call as y.
      if(result_symbol != nullptr && !auxiliary_result)
      {
        if(auto destination = source_result_destination(lhs, ns))
        {
          (*destination)["producer_original_event_id"] = number(event_id);
          (*destination)["consumer_original_event_id"] = number(event_id);
          (*destination)["binding"] = json_stringt("direct-nondet-assignment");
          (*destination)["evidence"] = json_stringt("original GOTO snapshot: nondet directly assigns this source symbol; no successor or rewritten-LHS inference");
          e["result_destination_designator"] = *destination;
          p.original_result_destinations.emplace(event_id, std::move(*destination));
        }
      }
      const auto next = program.get_successors(it);
      if(auxiliary_result && next.size() == 1 &&
         next.front() != program.instructions.end())
      {
        const auto &consumer = *next.front();
        const auto &source = ins.source_location();
        const auto &consumer_source = consumer.source_location();
        if(consumer.is_assign() && consumer.assign_rhs() == lhs &&
           consumer_source.get_file() == source.get_file() &&
           consumer_source.get_line() == source.get_line() &&
           consumer_source.get_function() == source.get_function())
        {
          if(auto destination = source_result_destination(consumer.assign_lhs(), ns))
          {
            (*destination)["producer_original_event_id"] = number(event_id);
            (*destination)["consumer_original_event_id"] = number(order.at(&consumer));
            (*destination)["binding"] = json_stringt("auxiliary-result-consumer");
            (*destination)["evidence"] = json_stringt("original GOTO snapshot: unique immediate successor consumes exact auxiliary call-result temporary at same file/line/function; no rewritten-LHS inference");
            e["result_destination_designator"] = *destination;
            p.original_result_destinations.emplace(event_id, std::move(*destination));
          }
        }
      }
    }
    p.original_events.push_back(std::move(e));
    p.original_signatures[event_id] = btor2_event_signature(ins);
  }
  for(const auto &id : symbols)
  {
    const symbolt *symbol = nullptr;
    if(ns.lookup(id, symbol) || !symbol) continue;
    p.original_symbol_ids.insert(id);
    json_objectt e;
    e["symbol"] = json_stringt(id2string(id)); e["source_name"] = json_stringt(id2string(symbol->base_name));
    e["source"] = location(symbol->location); e["type_ir"] = full_types.convert_from_irep(symbol->type);
    e["type"] = json_stringt(from_type(ns, ID_main, symbol->type));
    e["static_lifetime"] = jsont::json_boolean(symbol->is_static_lifetime);
    e["auxiliary"] = jsont::json_boolean(symbol->is_auxiliary);
    p.original_symbols.push_back(std::move(e));
  }
  p.latest_signatures = signatures(program);
}
void btor2_record_source_transform(
  const goto_programt &program, btor2_source_provenancet &p, const std::string &pass)
{
  if(!p.enabled) return;
  const auto current = signatures(program);
  json_objectt record;
  record["pass"] = json_stringt(pass); record["retained_goto_instructions"] = number(program.instructions.size());
  json_arrayt removed, changed;
  for(const auto &[id, previous] : p.latest_signatures)
  {
    const auto now = current.find(id);
    if(now == current.end()) { removed.push_back(number(id)); p.removed_by[id] = pass; }
    else if(previous != now->second) changed.push_back(number(id));
  }
  record["removed_original_event_ids"] = std::move(removed);
  record["modified_or_aggregated_original_event_ids"] = std::move(changed);
  record["relation"] = json_stringt("observed GOTO transformation; not a one-to-one trace certificate");
  p.transformations.push_back(std::move(record)); p.latest_signatures = current;
}
