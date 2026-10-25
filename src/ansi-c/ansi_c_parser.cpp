/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "ansi_c_parser.h"

#include "c_storage_spec.h"

#include <algorithm>
#include <fstream>
#include <optional>
#include <sstream>

namespace
{
// This restricted correspondence preserves every non-space byte and whether
// an internal whitespace boundary exists. It never joins/splits C tokens and
// never edits a string/character literal, escape or comment. Unlike stripping
// whitespace, it distinguishes e.g. "+ +" from "++" and "a b" from "ab".
std::optional<std::size_t> match_space_run_column(
  const std::string &source, const std::string &preprocessed,
  std::size_t pp_column)
{
  if(pp_column == 0 || pp_column > preprocessed.size() ||
     preprocessed[pp_column - 1] != ')')
    return {};
  auto source_index = source.find_first_not_of(" \t");
  auto pp_index = preprocessed.find_first_not_of(" \t");
  if(source_index == std::string::npos || pp_index == std::string::npos)
    return {};
  for(const auto &[text, begin] :
      {std::pair<const std::string &, std::size_t>{source, source_index},
       std::pair<const std::string &, std::size_t>{preprocessed, pp_index}})
  {
    if(text.find_first_of("\"'\\", begin) != std::string::npos ||
       text.find("/*", begin) != std::string::npos ||
       text.find("//", begin) != std::string::npos ||
       std::any_of(text.begin() + begin, text.end(), [](unsigned char c) {
         return c < 32 || c >= 128;
       }))
      return {};
  }
  std::optional<std::size_t> source_column;
  while(source_index < source.size() && pp_index < preprocessed.size())
  {
    if(source[source_index] == ' ' || preprocessed[pp_index] == ' ')
    {
      if(source[source_index] != ' ' || preprocessed[pp_index] != ' ')
        return {};
      while(source_index < source.size() && source[source_index] == ' ')
        ++source_index;
      while(pp_index < preprocessed.size() && preprocessed[pp_index] == ' ')
        ++pp_index;
      continue;
    }
    if(source[source_index] != preprocessed[pp_index])
      return {};
    if(pp_index + 1 == pp_column)
      source_column = source_index + 1;
    ++source_index;
    ++pp_index;
  }
  // Trailing spaces cannot introduce a token. All other remaining bytes must
  // match; a correct closing token alone does not certify the complete line.
  while(source_index < source.size() && source[source_index] == ' ')
    ++source_index;
  while(pp_index < preprocessed.size() && preprocessed[pp_index] == ' ')
    ++pp_index;
  return source_index == source.size() && pp_index == preprocessed.size()
           ? source_column : std::optional<std::size_t>{};
}
}

void ansi_c_parsert::capture_witness_tokens(const std::string &preprocessed)
{
  witness_tokens_enabled = true;
  witness_line = witness_token_line = 0;
  witness_column = witness_token_column = 1;
  witness_preprocessed_lines.clear();
  witness_source_lines.clear();
  std::istringstream input(preprocessed);
  std::string line;
  while(std::getline(input, line))
  {
    // YY_INPUT discards carriage returns. Only normal CRLF is supported for
    // source certification; an embedded CR in an original line fails equality.
    line.erase(std::remove(line.begin(), line.end(), '\r'), line.end());
    witness_preprocessed_lines.push_back(std::move(line));
  }
}

void ansi_c_parsert::witness_scan_token(const char *text, std::size_t length)
{
  if(!witness_tokens_enabled)
    return;
  witness_token_line = witness_line;
  witness_token_column = witness_column;
  for(std::size_t i = 0; i < length; ++i)
  {
    if(text[i] == '\n')
    {
      ++witness_line;
      witness_column = 1;
    }
    else
      ++witness_column;
  }
}

void ansi_c_parsert::witness_rewind_token(
  const char *text, std::size_t retained)
{
  if(!witness_tokens_enabled)
    return;
  witness_line = witness_token_line;
  witness_column = witness_token_column;
  // flex yyless returns the remaining characters to the scanner. Recount
  // only the retained prefix, including the INITIAL/STRING_LITERAL yyless(0).
  for(std::size_t i = 0; i < retained; ++i)
  {
    if(text[i] == '\n')
    {
      ++witness_line;
      witness_column = 1;
    }
    else
      ++witness_column;
  }
}

void ansi_c_parsert::witness_closing_token(exprt &token)
{
  if(!witness_tokens_enabled)
    return;
  auto &location = token.add_source_location();
  location.set("c2btor_pp_token_line", std::to_string(witness_token_line));
  location.set("c2btor_pp_token_column", std::to_string(witness_token_column));
}

void ansi_c_parsert::witness_call_return(
  exprt &function, exprt &call, const exprt &closing)
{
  if(!witness_tokens_enabled)
    return;
  const auto unavailable = [&](const std::string &reason) {
    for(auto *expr : {&function, &call})
    {
      auto &location = expr->add_source_location();
      location.remove("c2btor_call_return_file");
      location.remove("c2btor_call_return_line");
      location.remove("c2btor_call_return_column");
      location.remove("c2btor_call_return_evidence");
      location.set("c2btor_call_return_unavailable", reason);
    }
  };
  unavailable("missing-frontend-token-coordinate");
  const auto &end = closing.source_location();
  const auto &file = id2string(end.get_file());
  if(file.empty() || file.front() == '<' ||
     end.get("c2btor_pp_token_line").empty() ||
     end.get("c2btor_pp_token_column").empty() || end.get_line().empty())
    return;
  const auto physical_line = std::stoull(id2string(end.get("c2btor_pp_token_line")));
  auto column = std::stoull(id2string(end.get("c2btor_pp_token_column")));
  const auto source_line = std::stoull(id2string(end.get_line()));
  if(physical_line >= witness_preprocessed_lines.size() || source_line == 0)
  {
    unavailable("preprocessed-line-out-of-range");
    return;
  }
  auto cached = witness_source_lines.find(file);
  if(cached == witness_source_lines.end())
  {
    std::vector<std::string> lines;
    std::ifstream input(file);
    std::string line;
    while(std::getline(input, line))
    {
      if(!line.empty() && line.back() == '\r')
        line.pop_back();
      lines.push_back(std::move(line));
    }
    cached = witness_source_lines.emplace(file, std::move(lines)).first;
  }
  if(source_line > cached->second.size())
  {
    unavailable("original-source-line-unavailable");
    return;
  }
  const auto &source = cached->second[source_line - 1];
  const auto &preprocessed = witness_preprocessed_lines[physical_line];
  std::string evidence =
    "frontend closing-paren token; preprocessed line exactly matches original ASCII source";
  // Preprocessor token coordinates are not original C coordinates in general.
  // A different leading space/tab prefix is a provable coordinate translation
  // only when the complete remaining line is byte-identical. Internal whitespace,
  // comments, macros and all token changes still prevent certification.
  if(source != preprocessed)
  {
    auto source_prefix = source.find_first_not_of(" \t");
    auto pp_prefix = preprocessed.find_first_not_of(" \t");
    if(source_prefix == std::string::npos)
      source_prefix = source.size();
    if(pp_prefix == std::string::npos)
      pp_prefix = preprocessed.size();
    if(source.substr(source_prefix) == preprocessed.substr(pp_prefix) &&
       column > pp_prefix && column <= preprocessed.size())
    {
      column = source_prefix + (column - pp_prefix);
      evidence = "frontend closing-paren token; only leading horizontal whitespace differs from original ASCII source";
    }
    else if(const auto matched = match_space_run_column(source, preprocessed, column))
    {
      column = *matched;
      evidence = "frontend closing-paren token; ASCII space-run widths differ with identical bytes and preserved internal whitespace boundaries";
    }
    else
    {
      unavailable("preprocessed-line-differs-from-source");
      return;
    }
  }
  if(column == 0 || column > source.size() || source[column - 1] != ')')
  {
    unavailable("original-closing-token-mismatch");
    return;
  }
  if(std::any_of(source.begin(), source.end(), [](unsigned char c) { return c >= 128; }))
  {
    unavailable("non-ascii-source-line");
    return;
  }
  for(auto *expr : {&function, &call})
  {
    auto &location = expr->add_source_location();
    location.remove("c2btor_call_return_unavailable");
    location.set("c2btor_call_return_file", file);
    location.set("c2btor_call_return_line", std::to_string(source_line));
    location.set("c2btor_call_return_column", std::to_string(column));
    location.set("c2btor_call_return_evidence", evidence);
  }
}

ansi_c_id_classt ansi_c_parsert::lookup(
  const irep_idt &base_name,
  irep_idt &identifier, // output
  bool tag,
  bool label)
{
  // labels and tags have a separate name space
  const irep_idt scope_name=
    tag?"tag-"+id2string(base_name):
    label?"label-"+id2string(base_name):
    base_name;

  for(scopest::const_reverse_iterator it=scopes.rbegin();
      it!=scopes.rend();
      it++)
  {
    scopet::name_mapt::const_iterator n_it=
      it->name_map.find(scope_name);

    if(n_it!=it->name_map.end())
    {
      identifier=n_it->second.prefixed_name;
      return n_it->second.id_class;
    }
  }

  // Not found.
  // If it's a tag, we will add to current scope.
  if(tag)
  {
    ansi_c_identifiert &i=
      current_scope().name_map[scope_name];
    i.id_class=ansi_c_id_classt::ANSI_C_TAG;
    i.prefixed_name=current_scope().prefix+id2string(scope_name);
    i.base_name=base_name;
    identifier=i.prefixed_name;
    return ansi_c_id_classt::ANSI_C_TAG;
  }

  identifier=base_name;
  return ansi_c_id_classt::ANSI_C_UNKNOWN;
}

void ansi_c_parsert::add_tag_with_body(irept &tag)
{
  const std::string scope_name=
    "tag-"+tag.get_string(ID_C_base_name);

  irep_idt prefixed_name=current_scope().prefix+scope_name;

  if(prefixed_name!=tag.get(ID_identifier))
  {
    // re-defined in a deeper scope
    ansi_c_identifiert &identifier=
      current_scope().name_map[scope_name];
    identifier.id_class=ansi_c_id_classt::ANSI_C_TAG;
    identifier.prefixed_name=prefixed_name;
    tag.set(ID_identifier, prefixed_name);
  }
}

void ansi_c_parsert::add_declarator(
  exprt &declaration,
  irept &declarator)
{
  PRECONDITION(declarator.is_not_nil());
  ansi_c_declarationt &ansi_c_declaration=
    to_ansi_c_declaration(declaration);

  ansi_c_declaratort new_declarator;
  new_declarator.build(declarator);

  irep_idt base_name=new_declarator.get_base_name();

  bool is_member=ansi_c_declaration.get_is_member();
  bool is_parameter=ansi_c_declaration.get_is_parameter();

  if(is_member)
  {
    // we don't put them into a struct scope (unlike C++)
    new_declarator.set_name(base_name);
    ansi_c_declaration.declarators().push_back(new_declarator);
    return; // done
  }

  // global?
  if(current_scope().prefix.empty())
    ansi_c_declaration.set_is_global(true);

  // abstract?
  if(!base_name.empty())
  {
    c_storage_spect c_storage_spec(ansi_c_declaration.type());
    bool is_typedef=c_storage_spec.is_typedef;
    bool is_extern=c_storage_spec.is_extern;

    bool force_root_scope=false;

    // Functions always go into global scope, unless
    // declared as a parameter or are typedefs.
    if(new_declarator.type().id()==ID_code &&
       !is_parameter &&
       !is_typedef)
      force_root_scope=true;

    // variables marked as 'extern' always go into global scope
    if(is_extern)
      force_root_scope=true;

    ansi_c_id_classt id_class=is_typedef?
      ansi_c_id_classt::ANSI_C_TYPEDEF:
      ansi_c_id_classt::ANSI_C_SYMBOL;

    scopet &scope=
      force_root_scope?root_scope():current_scope();

    // set the final name
    irep_idt prefixed_name=force_root_scope?
             base_name:
             current_scope().prefix+id2string(base_name);
    new_declarator.set_name(prefixed_name);

    // add to scope
    ansi_c_identifiert &identifier=scope.name_map[base_name];
    identifier.id_class=id_class;
    identifier.prefixed_name=prefixed_name;

    if(force_root_scope)
      current_scope().name_map[base_name] = identifier;
  }

  ansi_c_declaration.declarators().push_back(new_declarator);
}

ansi_c_id_classt ansi_c_parsert::get_class(const typet &type)
{
  if(type.id()==ID_typedef)
    return ansi_c_id_classt::ANSI_C_TYPEDEF;
  else if(type.id()==ID_struct ||
          type.id()==ID_union ||
          type.id()==ID_c_enum)
    return ansi_c_id_classt::ANSI_C_TAG;
  else if(type.id()==ID_merged_type)
  {
    for(const typet &subtype : to_type_with_subtypes(type).subtypes())
    {
      if(get_class(subtype) == ansi_c_id_classt::ANSI_C_TYPEDEF)
        return ansi_c_id_classt::ANSI_C_TYPEDEF;
    }
  }
  else if(type.has_subtype())
    return get_class(to_type_with_subtype(type).subtype());

  return ansi_c_id_classt::ANSI_C_SYMBOL;
}

bool ansi_c_parsert::pragma_cprover_empty()
{
  return pragma_cprover_stack.empty();
}

void ansi_c_parsert::pragma_cprover_push()
{
  pragma_cprover_stack.emplace_back();
}

void ansi_c_parsert::pragma_cprover_pop()
{
  pragma_cprover_stack.pop_back();
}

void ansi_c_parsert::pragma_cprover_add_check(
  const irep_idt &name,
  bool enabled)
{
  if(pragma_cprover_stack.empty())
    pragma_cprover_push();

  pragma_cprover_stack.back()[name] = enabled;
}

bool ansi_c_parsert::pragma_cprover_clash(const irep_idt &name, bool enabled)
{
  auto top = pragma_cprover_stack.back();
  auto found = top.find(name);
  return found != top.end() && found->second != enabled;
}

void ansi_c_parsert::set_pragma_cprover()
{
  // handle enable/disable shadowing
  // by bottom-to-top flattening
  std::map<irep_idt, bool> flattened;

  for(const auto &pragma_set : pragma_cprover_stack)
    for(const auto &pragma : pragma_set)
      flattened[pragma.first] = pragma.second;

  _source_location.remove(ID_pragma);

  for(const auto &pragma : flattened)
  {
    std::string check_name = id2string(pragma.first);
    std::string full_name =
      (pragma.second ? "enable:" : "disable:") + check_name;
    _source_location.add_pragma(full_name);
  }
}
