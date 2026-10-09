#include "lower_float_operations.h"

#include <util/std_expr.h>
#include <util/std_types.h>

#include <goto-programs/goto_model.h>

void lower_float_operations(goto_modelt &model)
{
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
  model.goto_functions.update();
}
