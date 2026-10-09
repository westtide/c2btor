#include "lower_recursive_calls.h"

#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/find_symbols.h>
#include <util/fresh_symbol.h>
#include <util/replace_expr.h>
#include <util/simplify_expr.h>
#include <util/std_code.h>
#include <util/std_expr.h>

#include <goto-programs/goto_model.h>

#include <functional>
#include <map>
#include <set>
#include <vector>

namespace
{
using instructiont = goto_programt::instructiont;
using symbol_sett = find_symbols_sett;

bool addressed_local(const exprt &expr, const symbol_sett &locals)
{
  if(expr.id() == ID_address_of)
    for(const auto &id : find_symbol_identifiers(expr))
      if(locals.count(id))
        return true;
  for(const auto &op : expr.operands())
    if(addressed_local(op, locals))
      return true;
  return false;
}

// One self call, an acyclic body, and no saved automatic values other than
// reversible parameters. This is a loop transformation, not bounded inlining.
bool lower_linear(
  const irep_idt &id,
  goto_functionst::goto_functiont &function,
  symbol_tablet &symbols)
{
  auto &body = function.body;
  if(body.empty())
    return false;
  const namespacet ns(symbols);
  auto call = body.instructions.end();
  std::vector<goto_programt::targett> nodes;
  std::map<const instructiont *, std::size_t> indices;
  symbol_sett locals, parameters;
  for(const auto &p : function.parameter_identifiers)
  {
    const auto &type = symbols.lookup_ref(p).type;
    if(
      type.id() != ID_signedbv && type.id() != ID_unsignedbv &&
      type.id() != ID_pointer && type.id() != ID_bool && type.id() != ID_c_bool)
      return false;
    locals.insert(p);
    parameters.insert(p);
  }
  for(auto it = body.instructions.begin(); it != body.instructions.end(); ++it)
  {
    indices[&*it] = nodes.size();
    nodes.push_back(it);
    if(it->is_decl())
    {
      const auto &symbol = it->decl_symbol();
      const auto &type = symbol.type();
      if(
        type.id() != ID_signedbv && type.id() != ID_unsignedbv &&
        type.id() != ID_pointer && type.id() != ID_bool &&
        type.id() != ID_c_bool)
        return false;
      locals.insert(symbol.get_identifier());
    }
    if(
      it->is_function_call() && it->call_function().id() == ID_symbol &&
      to_symbol_expr(it->call_function()).get_identifier() == id)
    {
      if(call != body.instructions.end())
        return false;
      call = it;
    }
  }
  if(
    call == body.instructions.end() || call->call_lhs().id() != ID_symbol ||
    call->call_arguments().size() != function.parameter_identifiers.size())
    return false;
  const auto call_index = indices.at(&*call);
  const auto lhs = to_symbol_expr(call->call_lhs());
  if(parameters.count(lhs.get_identifier()))
    return false;
  const auto end = std::prev(body.instructions.end());
  if(!end->is_end_function())
    return false;

  const auto writes_parameter = [&](exprt lhs)
  {
    while(lhs.id() == ID_typecast)
      lhs = to_typecast_expr(lhs).op();
    return lhs.id() == ID_symbol &&
           parameters.count(to_symbol_expr(lhs).get_identifier());
  };

  // No addresses of automatic storage may escape a frame. All control-flow
  // edges must go forward, so each activation executes the self call at most
  // once, and the return continuation cannot enter it again.
  for(std::size_t i = 0; i < nodes.size(); ++i)
  {
    const auto &ins = *nodes[i];
    if(
      addressed_local(ins.code(), locals) ||
      (ins.has_condition() && addressed_local(ins.condition(), locals)))
      return false;
    if(ins.is_goto())
      for(const auto &target : ins.targets)
        if(indices.at(&*target) <= i)
          return false;
    if(ins.is_assign() && writes_parameter(ins.assign_lhs()))
      return false;
    if(ins.is_function_call() && writes_parameter(ins.call_lhs()))
      return false;
    if(!(ins.is_decl() || ins.is_dead() || ins.is_assign() || ins.is_goto() ||
         ins.is_assert() || ins.is_assume() || ins.is_skip() ||
         ins.is_location() || ins.is_function_call() ||
         ins.is_set_return_value() || ins.is_end_function()))
      return false;
  }

  // Standard backwards liveness on the acyclic CFG. Scalars that the caller
  // needs after the self call would require a stack and are not handled here.
  std::vector<symbol_sett> live(nodes.size());
  symbol_sett across;
  for(std::size_t r = nodes.size(); r-- > 0;)
  {
    const auto &ins = *nodes[r];
    auto &now = live[r];
    auto merge = [&](std::size_t n)
    { now.insert(live[n].begin(), live[n].end()); };
    if(
      !ins.is_end_function() && !(ins.is_goto() && ins.condition().is_true()) &&
      r + 1 < nodes.size())
      merge(r + 1);
    for(const auto &target : ins.targets)
      merge(indices.at(&*target));
    if(r == call_index)
      across = now;
    if(ins.is_decl())
      now.erase(ins.decl_symbol().get_identifier());
    else if(ins.is_dead())
      now.erase(ins.dead_symbol().get_identifier());
    else if(ins.is_assign())
    {
      if(ins.assign_lhs().id() == ID_symbol)
        now.erase(to_symbol_expr(ins.assign_lhs()).get_identifier());
      else
        find_symbols(ins.assign_lhs(), now);
      find_symbols(ins.assign_rhs(), now);
    }
    else if(ins.is_function_call())
    {
      if(ins.call_lhs().id() == ID_symbol)
        now.erase(to_symbol_expr(ins.call_lhs()).get_identifier());
      else
        find_symbols(ins.call_lhs(), now);
      for(const auto &arg : ins.call_arguments())
        find_symbols(arg, now);
    }
    else if(ins.is_set_return_value())
      find_symbols(ins.return_value(), now);
    if(ins.has_condition())
      find_symbols(ins.condition(), now);
  }
  across.erase(lhs.get_identifier());
  for(const auto &var : across)
    if(locals.count(var) && !parameters.count(var))
      return false;

  // Every argument must be its own parameter plus/minus a constant. Hence
  // updates commute, and their inverse restores the suspended caller exactly.
  std::vector<exprt> inverses;
  std::vector<symbol_exprt> params;
  std::optional<std::size_t> counter_parameter;
  for(std::size_t i = 0; i < function.parameter_identifiers.size(); ++i)
  {
    auto p =
      symbols.lookup_ref(function.parameter_identifiers[i]).symbol_expr();
    params.push_back(p);
    auto arg = simplify_expr(call->call_arguments()[i], ns);
    if(arg == p)
    {
      inverses.push_back(p);
      continue;
    }
    if(
      (arg.id() != ID_plus && arg.id() != ID_minus) ||
      arg.operands().size() != 2 || arg.operands()[0] != p)
      return false;
    const auto step = numeric_cast<mp_integer>(arg.operands()[1]);
    if(!step || arg.type() != p.type())
      return false;
    inverses.push_back(
      arg.id() == ID_plus ? exprt(minus_exprt(p, arg.operands()[1]))
                          : exprt(plus_exprt(p, arg.operands()[1])));
    if(p.type().id() == ID_signedbv || p.type().id() == ID_unsignedbv)
    {
      const auto modulus = mp_integer(1)
                           << to_bitvector_type(p.type()).get_width();
      if(*step == 1 || *step == -1 || *step == modulus - 1)
        counter_parameter = i;
    }
  }
  if(!counter_parameter)
    return false;
  const auto &counter = params[*counter_parameter];

  // Establish a finite descent bound without imposing one: a unit step visits
  // every W-bit parameter value within 2^W steps. Prefix branch decisions may
  // depend only on that parameter; at least one tested value must bypass the
  // self call. Thus at most 2^W-1 suspended frames exist and a W-bit depth is
  // exact, including modular arithmetic after a reported source overflow.
  for(std::size_t i = 0; i < call_index; ++i)
  {
    const auto &ins = *nodes[i];
    if(ins.is_function_call() || ins.is_assume())
      return false;
    if(
      ins.is_assign() &&
      (ins.assign_lhs().id() != ID_symbol ||
       !locals.count(to_symbol_expr(ins.assign_lhs()).get_identifier()) ||
       !simplify_expr(ins.assign_rhs(), ns).is_constant()))
      return false;
    if(ins.is_goto())
      for(const auto &var : find_symbol_identifiers(ins.condition()))
        if(var != counter.get_identifier())
          return false;
  }
  bool base_found = false;
  for(const int candidate : {0, 1, 2, -1})
  {
    std::size_t i = 0;
    while(i < call_index)
    {
      const auto &ins = *nodes[i];
      if(ins.is_goto())
      {
        auto cond = ins.condition();
        replace_expr(counter, from_integer(candidate, counter.type()), cond);
        cond = simplify_expr(cond, ns);
        if(!cond.is_true() && !cond.is_false())
          break;
        if(cond.is_true())
        {
          if(ins.targets.size() != 1)
            return false;
          i = indices.at(&*ins.targets.front());
          continue;
        }
      }
      ++i;
    }
    if(i > call_index)
      base_found = true;
    if(base_found)
      break;
  }
  if(!base_found)
    return false;

  const auto location = call->source_location();
  auto auxiliary = [&](const typet &type, const char *name)
  {
    return get_fresh_aux_symbol(
             type, id2string(id), name, location, ID_C, symbols)
      .symbol_expr();
  };
  const auto depth = auxiliary(
    unsignedbv_typet(to_bitvector_type(counter.type()).get_width()),
    "recursion_depth");
  const auto result = auxiliary(lhs.type(), "recursion_result");
  const auto entry = body.instructions.begin();
  const auto continuation = std::next(call);
  auto insert_prologue = [&](instructiont ins)
  { body.instructions.insert(entry, std::move(ins)); };
  insert_prologue(goto_programt::make_decl(depth, location));
  insert_prologue(goto_programt::make_decl(result, location));
  insert_prologue(
    goto_programt::make_assignment(
      depth, from_integer(0, depth.type()), location));
  for(auto &ins : body.instructions)
    if(ins.is_set_return_value())
      ins = goto_programt::make_assignment(
        result, ins.return_value(), ins.source_location());

  goto_programt descend;
  auto emit = [&](goto_programt &program, instructiont ins)
  {
    auto target = program.add_instruction();
    *target = std::move(ins);
    return target;
  };
  emit(
    descend,
    goto_programt::make_assignment(
      depth, plus_exprt(depth, from_integer(1, depth.type())), location));
  for(std::size_t i = 0; i < params.size(); ++i)
    emit(
      descend,
      goto_programt::make_assignment(
        params[i], call->call_arguments()[i], location));
  emit(descend, goto_programt::make_goto(entry, location));
  call->turn_into_skip();
  body.insert_before_swap(call, descend);

  end->turn_into_skip();
  const auto done = emit(
    body,
    goto_programt::make_goto(
      end, equal_exprt(depth, from_integer(0, depth.type())), location));
  emit(
    body,
    goto_programt::make_assignment(
      depth, minus_exprt(depth, from_integer(1, depth.type())), location));
  for(std::size_t i = 0; i < params.size(); ++i)
    emit(
      body, goto_programt::make_assignment(params[i], inverses[i], location));
  emit(body, goto_programt::make_assignment(lhs, result, location));
  emit(body, goto_programt::make_goto(continuation, location));
  const auto return_value =
    emit(body, goto_programt::make_set_return_value(result, location));
  done->targets = {return_value};
  emit(body, goto_programt::make_end_function(location));
  body.update();
  return true;
}
} // namespace

void lower_recursive_calls(goto_modelt &model)
{
  auto &functions = model.goto_functions.function_map;
  for(auto &entry : functions)
    lower_linear(entry.first, entry.second, model.symbol_table);

  // Preserve evidence of unresolved cycles before goto_inline can replace a
  // recursive call with SKIP. Mark the cyclic functions themselves: unreachable
  // recursive helpers must not prevent conversion of main. This also catches
  // mutual recursion, which a direct-self-call scan misses.
  std::map<irep_idt, std::set<irep_idt>> edges;
  for(const auto &entry : functions)
    for(const auto &ins : entry.second.body.instructions)
      if(ins.is_function_call() && ins.call_function().id() == ID_symbol)
        edges[entry.first].insert(
          to_symbol_expr(ins.call_function()).get_identifier());
  for(auto &entry : functions)
  {
    std::set<irep_idt> visited;
    std::function<bool(const irep_idt &)> reaches_self =
      [&](const irep_idt &node)
    {
      if(!visited.insert(node).second)
        return false;
      for(const auto &next : edges[node])
        if(next == entry.first || reaches_self(next))
          return true;
      return false;
    };
    if(!reaches_self(entry.first))
      continue;
    auto &body = entry.second.body;
    if(body.empty())
      continue;
    codet marker("c2btor_unlowered_recursion");
    marker.set("function", entry.first);
    body.instructions.insert(
      body.instructions.begin(),
      goto_programt::make_other(
        marker, body.instructions.front().source_location()));
  }
  model.goto_functions.update();
}
