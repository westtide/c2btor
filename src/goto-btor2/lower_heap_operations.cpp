#include "lower_heap_operations.h"
#include "lower_recursive_calls.h"

#include <util/std_code.h>
#include <util/std_expr.h>

#include <goto-programs/goto_model.h>

void lower_heap_operations(goto_modelt &model)
{
  lower_recursive_calls(model);
  for(const auto &name :
      {"__CPROVER_deallocate",
       "memcpy",
       "memmove",
       "__builtin___memcpy_chk",
       "__builtin___memmove_chk"})
  {
    auto it = model.goto_functions.function_map.find(name);
    if(
      it == model.goto_functions.function_map.end() ||
      it->second.body.instructions.empty())
      continue;
    auto &function = it->second;
    const auto location = function.body.instructions.front().source_location();
    // A user-defined function of the same name must retain its actual body.
    if(id2string(location.get_file()).find("<builtin-library-") != 0)
      continue;
    const bool release = std::string(name) == "__CPROVER_deallocate";
    const unsigned count = release ? 1 : 3;
    if(function.parameter_identifiers.size() < count)
      continue;
    codet event(release ? "c2btor_deallocate" : "c2btor_copy_check");
    for(unsigned i = 0; i < count; ++i)
      event.add_to_operands(
        model.symbol_table.lookup_ref(function.parameter_identifiers[i])
          .symbol_expr());
    if(!release)
      event.set(
        "allow_overlap",
        std::string(name).find("memmove") != std::string::npos);
    auto instruction = goto_programt::make_other(event, location);
    function.body.insert_before_swap(
      function.body.instructions.begin(), instruction);
  }
  model.goto_functions.update();
}
