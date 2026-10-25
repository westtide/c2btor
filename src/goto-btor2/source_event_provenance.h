// SPDX-License-Identifier: BSD-4-Clause
// SPDX-FileCopyrightText: 2026 C2BTOR contributors

#ifndef CPROVER_GOTO_BTOR2_SOURCE_EVENT_PROVENANCE_H
#define CPROVER_GOTO_BTOR2_SOURCE_EVENT_PROVENANCE_H

#include <util/json.h>
#include <util/source_location.h>
#include <goto-programs/goto_program.h>
#include <map>
#include <optional>
#include <set>
#include <string>
#include <vector>
class namespacet;

struct btor2_nondet_callt
{
  std::string function;
  const exprt *lhs = nullptr;
  typet return_type;
  bool value_preserving = true;
  std::string unsupported_reason;
};
std::optional<btor2_nondet_callt> btor2_source_nondet_call(
  const goto_programt::instructiont &, const namespacet &);

// Origin IDs identify captured GOTO events, not runtime occurrences/BTOR nodes.
struct btor2_source_provenancet
{
  bool enabled = false;
  std::string stage;
  json_arrayt original_events, original_symbols, transformations;
  std::map<std::size_t, std::string> original_signatures, removed_by;
  // Certified before callback/alias simplification; never inferred from a
  // rewritten destination when the original designator was a pointer.
  std::map<std::size_t, json_objectt> original_result_destinations;
  std::set<irep_idt> original_symbol_ids;
  std::map<std::size_t, std::vector<std::string>> latest_signatures;
};
std::set<std::size_t> btor2_original_event_ids(const source_locationt &);
json_arrayt btor2_original_event_ids_json(const source_locationt &);
std::optional<json_objectt> btor2_call_return_location(const source_locationt &);
void btor2_add_call_return_metadata(json_objectt &, const source_locationt &);
void btor2_merge_event_origins(source_locationt &, const source_locationt &);
std::string btor2_event_signature(const goto_programt::instructiont &);
void btor2_capture_source_events(
  goto_programt &, const namespacet &, btor2_source_provenancet &, const std::string &stage);
void btor2_record_source_transform(
  const goto_programt &, btor2_source_provenancet &, const std::string &pass);
#endif
