// SPDX-License-Identifier: BSD-4-Clause
// SPDX-FileCopyrightText: 2026 C2BTOR contributors

#include "lower_float_operations.h"

#include <util/config.h>
#include <util/ieee_float.h>
#include <util/floatbv_expr.h>
#include <util/namespace.h>
#include <util/simplify_expr.h>
#include <util/std_expr.h>
#include <util/std_types.h>

#include <algorithm>

#include <goto-programs/adjust_float_expressions.h>
#include <goto-programs/goto_model.h>

void lower_float_operations(goto_modelt &model)
{
  // GotoIR floating operations already carry an explicit rounding mode,
  // whereas static initializers in the symbol table still contain ordinary
  // C casts and arithmetic. Normalize those too: a double-to-float cast
  // must round its numerical value, never truncate its representation bits.
  const namespacet ns(model.symbol_table);
  const auto initial_rounding_mode =
    ieee_floatt::rounding_mode_expr(config.ansi_c.rounding_mode);
  for(const auto &entry : model.symbol_table.symbols)
  {
    if(!entry.second.is_static_lifetime || entry.second.value.is_nil())
      continue;
    exprt value = entry.second.value;
    adjust_float_expressions(value, initial_rounding_mode);
    model.symbol_table.get_writeable(entry.first)->value =
      simplify_expr(std::move(value), ns);
  }
  for(auto &entry : model.goto_functions.function_map)
  {
    const auto name = id2string(entry.first);
    const bool square_root = name == "sqrt" || name == "sqrtf" ||
                             name == "sqrtl" || name == "__builtin_sqrt" ||
                             name == "__builtin_sqrtf" ||
                             name == "__builtin_sqrtl";
    const bool fused = name == "fma" || name == "fmaf" || name == "fmal" ||
                       name == "__builtin_fma" || name == "__builtin_fmaf" ||
                       name == "__builtin_fmal";
    const bool remainder =
      name == "remainder" || name == "remainderf" || name == "remainderl" ||
      name == "__builtin_remainder" || name == "__builtin_remainderf" ||
      name == "__builtin_remainderl";
    const bool fmod = name == "fmod" || name == "fmodf" || name == "fmodl" ||
                      name == "__builtin_fmod" || name == "__builtin_fmodf" ||
                      name == "__builtin_fmodl";
    if(!square_root && !fused && !remainder && !fmod)
      continue;
    auto &function = entry.second;
    if(function.body.instructions.empty())
      continue;
    const auto location = function.body.instructions.front().source_location();
    if(id2string(location.get_file()).find("<builtin-library-") != 0)
      continue;
    exprt operation(
      square_root ? "c2btor_sqrt"
      : fused     ? "c2btor_fma"
      : remainder ? "c2btor_remainder"
                  : "c2btor_fmod",
      to_code_type(model.symbol_table.lookup_ref(entry.first).type)
        .return_type());
    for(const auto &id : function.parameter_identifiers)
      operation.add_to_operands(
        model.symbol_table.lookup_ref(id).symbol_expr());
    if(square_root || fused)
      operation.add_to_operands(
        model.symbol_table.lookup_ref("__CPROVER_rounding_mode").symbol_expr());
    function.body.clear();
    function.body.add(
      goto_programt::make_set_return_value(operation, location));
    function.body.add(goto_programt::make_end_function(location));
  }
  // Compiler builtins need not have library bodies. Normalize their call
  // instructions directly; user-defined ordinary functions keep their bodies.
  for(auto &entry : model.goto_functions.function_map)
    for(auto &instruction : entry.second.body.instructions)
    {
      if(!instruction.is_function_call() ||
         instruction.call_function().id() != ID_symbol)
        continue;
      const auto id = to_symbol_expr(instruction.call_function()).get_identifier();
      auto name = id2string(id);
      if(name.rfind("__builtin_", 0) != 0)
        continue;
      const auto callee = model.goto_functions.function_map.find(id);
      if(callee != model.goto_functions.function_map.end() &&
         !callee->second.body.instructions.empty())
        continue;
      name.erase(0, 10);
      for(const std::string base : {"floor", "ceil", "trunc", "round", "rint",
                                    "nearbyint", "sqrt", "fma", "remainder",
                                    "fmod", "fabs"})
        if(name == base || name == base + "f" || name == base + "l")
        {
          name = base;
          break;
        }
      const auto &args = instruction.call_arguments();
      const auto type = to_code_type(instruction.call_function().type()).return_type();
      if(type.id() != ID_floatbv || args.empty())
        continue;
      const bool integral = name == "floor" || name == "ceil" || name == "trunc" ||
        name == "round" || name == "rint" || name == "nearbyint";
      const bool root = name == "sqrt", fused = name == "fma";
      const bool remainder = name == "remainder" || name == "fmod";
      const bool absolute = name == "fabs";
      const unsigned arity = fused ? 3 : remainder ? 2 : 1;
      if((!integral && !root && !fused && !remainder && !absolute) ||
         args.size() != arity ||
         std::any_of(args.begin(), args.end(), [&](const exprt &arg) {
           return arg.type() != type;
         }))
        continue;
      exprt mode = initial_rounding_mode;
      if(integral || root || fused)
      {
        const auto *symbol = model.symbol_table.lookup("__CPROVER_rounding_mode");
        if(symbol)
          mode = symbol->symbol_expr();
      }
      exprt operation;
      if(integral)
      {
        if(name == "floor") mode = ieee_floatt::rounding_mode_expr(ieee_floatt::ROUND_TO_MINUS_INF);
        if(name == "ceil") mode = ieee_floatt::rounding_mode_expr(ieee_floatt::ROUND_TO_PLUS_INF);
        if(name == "trunc") mode = ieee_floatt::rounding_mode_expr(ieee_floatt::ROUND_TO_ZERO);
        if(name == "round") mode = ieee_floatt::rounding_mode_expr(ieee_floatt::ROUND_TO_AWAY);
        operation = floatbv_round_to_integral_exprt(args[0], mode);
      }
      else if(absolute)
        operation = abs_exprt(args[0]);
      else
      {
        operation = exprt(root ? "c2btor_sqrt" : fused ? "c2btor_fma" :
                          name == "remainder" ? "c2btor_remainder" : "c2btor_fmod", type);
        operation.operands() = args;
        if(root || fused)
          operation.add_to_operands(mode);
      }
      auto replacement = instruction.call_lhs().is_nil()
        ? goto_programt::make_skip(instruction.source_location())
        : goto_programt::make_assignment(instruction.call_lhs(), operation,
                                        instruction.source_location());
      replacement.labels = instruction.labels;
      instruction = std::move(replacement);
    }
  model.goto_functions.update();
}
