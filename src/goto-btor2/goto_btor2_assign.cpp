#include <util/std_expr.h>

#include "goto_btor2_converter.h"

void goto_to_btor2_convertert::process_assign(
  unsigned loc,
  btor2_nid_t at_loc,
  const goto_programt::instructiont &instruction)
{
  const auto &lhs = instruction.assign_lhs();
  const auto &rhs = instruction.assign_rhs();
  // Dereference lowering can leave casts on the assignment target. Match
  // symex_assignt::assign_typecast: convert the value back to the underlying
  // lvalue type, rather than writing through the cast as a byte view.
  if(lhs.id() == ID_typecast)
  {
    auto assignment = instruction;
    assignment.assign_lhs_nonconst() = to_typecast_expr(lhs).op();
    assignment.assign_rhs_nonconst() = typecast_exprt::conditional_cast(
      rhs, assignment.assign_lhs().type());
    process_assign(loc, at_loc, assignment);
    return;
  }
  if(memory.assign(lhs, rhs))
  {
    add_pc_fallthrough(loc, at_loc);
    return;
  }
  if(lhs.id() != ID_symbol)
  {
    conversion_error("Unsupported assignment lvalue: " + lhs.id_string());
    return;
  }
  const auto id = to_symbol_expr(lhs).get_identifier();
  if(memory.logical_records.count(id))
  {
    for(const auto &field : to_struct_type(lhs.type()).components())
    {
      auto member_id = id2string(id) + "." + id2string(field.get_name());
      auto value = expr_converter.convert(
        member_exprt(rhs, field.get_name(), field.type()));
      if(!value)
        conversion_error("Cannot lower overflow pair");
      else
        state_updates[member_id].push_back({at_loc, value});
    }
    add_pc_fallthrough(loc, at_loc);
    return;
  }
  const auto it = variables.find(id);
  if(it == variables.end() || !it->second.state_nid)
  {
    conversion_error("Missing scalar state for " + id2string(id));
    return;
  }
  const auto value = expr_converter.convert(rhs);
  if(!value)
    conversion_error(
      "Failed to convert RHS expression at " + std::to_string(loc));
  else
    state_updates[id].push_back({at_loc, value});
  add_pc_fallthrough(loc, at_loc);
}
