/*******************************************************************\

Module: CBMC Command Line Option Processing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// CBMC Command Line Option Processing

#include "cbmc_parse_options.h"

#include <util/config.h>
#include <util/exit_codes.h>
#include <util/expr_util.h>
#include <util/find_symbols.h>
#include <util/pointer_expr.h>
#include <util/help_formatter.h>
#include <util/invariant.h>
#include <util/unicode.h>
#include <util/version.h>

#include <goto-programs/initialize_goto_model.h>
#include <goto-programs/goto_inline.h>
#include <goto-programs/loop_ids.h>
#include <goto-programs/process_goto_program.h>
#include <goto-programs/read_goto_binary.h>
#include <goto-programs/remove_skip.h>
#include <goto-programs/set_properties.h>
#include <goto-programs/show_goto_functions.h>
#include <goto-programs/show_properties.h>
#include <goto-programs/show_symbol_table.h>
#include <goto-programs/write_goto_binary.h>

#include <ansi-c/c_preprocess.h>
#include <ansi-c/cprover_library.h>
#include <ansi-c/gcc_version.h>
#include <ansi-c/goto-conversion/link_to_library.h>
#include <assembler/remove_asm.h>
#include <cpp/cprover_library.h>
#include <goto-checker/all_properties_verifier.h>
#include <goto-checker/all_properties_verifier_with_fault_localization.h>
#include <goto-checker/all_properties_verifier_with_trace_storage.h>
#include <goto-checker/bmc_util.h>
#include <goto-checker/cover_goals_verifier_with_trace_storage.h>
#include <goto-checker/multi_path_symex_checker.h>
#include <goto-checker/multi_path_symex_only_checker.h>
#include <goto-checker/properties.h>
#include <goto-checker/single_loop_incremental_symex_checker.h>
#include <goto-checker/single_path_symex_checker.h>
#include <goto-checker/single_path_symex_only_checker.h>
#include <goto-checker/stop_on_fail_verifier.h>
#include <goto-checker/stop_on_fail_verifier_with_fault_localization.h>
#include <goto-instrument/cover.h>
#include <goto-instrument/full_slicer.h>
#include <goto-instrument/nondet_static.h>
#include <goto-instrument/reachability_slicer.h>
#include <goto-symex/path_storage.h>
#include <langapi/language.h>
#include <langapi/mode.h>
#include <pointer-analysis/add_failed_symbols.h>

#include "c_test_input_generator.h"

#include <goto-btor2/goto_btor2.h>
#include <algorithm>
#include <limits>
#include <map>
#include <stdexcept>
#include <goto-btor2/simplify_callback_targets.h>
#include <goto-btor2/lower_array_operations.h>
#include <goto-btor2/lower_heap_operations.h>
#include <goto-btor2/lower_float_operations.h>
#include <xmllang/graphml.h>

#include <cstdlib> // exit()
#include <filesystem>
#include <fstream> // IWYU pragma: keep
#include <iostream>
#include <memory>
#include <set>
#include <system_error>
#include <vector>

namespace
{
// Preserve query identities through constant folding and later lowering. Only
// newly introduced assertions need an ID; removed queries reserve theirs too.
void label_btor2_properties(
  goto_modelt &model,
  const std::vector<source_locationt> &removed = {})
{
  std::set<irep_idt> used;
  for(const auto &source : removed)
    if(!source.get_property_id().empty())
      used.insert(source.get_property_id());
  for(const auto &function : model.goto_functions.function_map)
    for(const auto &instruction : function.second.body.instructions)
      if(instruction.is_assert() &&
         !instruction.source_location().get_property_id().empty())
        used.insert(instruction.source_location().get_property_id());

  std::map<std::string, std::size_t> counters;
  for(auto &function : model.goto_functions.function_map)
    for(auto &instruction : function.second.body.instructions)
    {
      if(!instruction.is_assert() ||
         !instruction.source_location().get_property_id().empty())
        continue;
      auto &source = instruction.source_location_nonconst();
      if(source.get_function().empty())
        source.set_function(function.first);
      std::string prefix = id2string(source.get_function());
      if(!source.get_property_class().empty())
      {
        if(!prefix.empty())
          prefix += ".";
        auto infix = id2string(source.get_property_class());
        std::replace(infix.begin(), infix.end(), ' ', '_');
        prefix += infix;
      }
      if(!prefix.empty())
        prefix += ".";
      irep_idt id;
      do
        id = prefix + std::to_string(++counters[prefix]);
      while(used.count(id));
      source.set_property_id(id);
      used.insert(id);
    }
}
}

cbmc_parse_optionst::cbmc_parse_optionst(int argc, const char **argv)
  : parse_options_baset(
      CBMC_OPTIONS,
      argc,
      argv,
      std::string("C2BTOR ") + C2BTOR_VERSION)
{
  json_interface(cmdline, ui_message_handler);
  xml_interface(cmdline, ui_message_handler);
}

::cbmc_parse_optionst::cbmc_parse_optionst(
  int argc,
  const char **argv,
  const std::string &extra_options)
  : parse_options_baset(
      CBMC_OPTIONS + extra_options,
      argc,
      argv,
      std::string("C2BTOR ") + C2BTOR_VERSION)
{
  json_interface(cmdline, ui_message_handler);
  xml_interface(cmdline, ui_message_handler);
}

void cbmc_parse_optionst::set_default_options(optionst &options)
{
  // Default true
  options.set_option("built-in-assertions", true);
  options.set_option("propagation", true);
  options.set_option("simple-slice", true);
  options.set_option("simplify", true);
  options.set_option("show-goto-symex-steps", false);
  options.set_option("show-points-to-sets", false);
  options.set_option("show-array-constraints", false);

  // Other default
  options.set_option("arrays-uf", "auto");
  options.set_option("depth", UINT32_MAX);
}

void cbmc_parse_optionst::set_default_analysis_flags(
  optionst &options,
  const bool enabled)
{
  // Checks enabled by default in v6.0+.
  options.set_option("bounds-check", enabled);
  options.set_option("pointer-check", enabled);
  options.set_option("pointer-primitive-check", enabled);
  options.set_option("div-by-zero-check", enabled);
  options.set_option("signed-overflow-check", enabled);
  options.set_option("undefined-shift-check", enabled);

  // Unwinding assertions required in certain cases for sound verification
  // results. See https://github.com/diffblue/cbmc/issues/6561 for elaboration.
  // As the unwinding-assertions is processed earlier, we set it only if it has
  // not been set yet.
  if(!options.is_set("unwinding-assertions"))
  {
    options.set_option("unwinding-assertions", enabled);
  }

  if(enabled)
  {
    config.ansi_c.malloc_may_fail = true;
    config.ansi_c.malloc_failure_mode =
      configt::ansi_ct::malloc_failure_modet::malloc_failure_mode_return_null;
  }
  else
  {
    config.ansi_c.malloc_may_fail = false;
    config.ansi_c.malloc_failure_mode =
      configt::ansi_ct::malloc_failure_modet::malloc_failure_mode_none;
  }
}

void cbmc_parse_optionst::get_command_line_options(optionst &options)
{
  // Enable flags that in combination provide analysis with no surprises
  // (expected checks and no unsoundness by missing checks).
  cbmc_parse_optionst::set_default_analysis_flags(
    options,
    !cmdline.isset("no-standard-checks") &&
      (!cmdline.isset("goto-btor2") || cmdline.isset("goto-btor2-checks")));

  if(cmdline.isset("goto-btor2"))
  {
    // Property instrumentation must not change allocation data semantics.
    // BTOR2 allocations never fail; there is no CLI override.
    config.ansi_c.malloc_may_fail = false;
    config.ansi_c.malloc_failure_mode =
      configt::ansi_ct::malloc_failure_modet::malloc_failure_mode_none;
  }

  if(config.set(cmdline))
  {
    usage_error();
    exit(CPROVER_EXIT_USAGE_ERROR);
  }

  cbmc_parse_optionst::set_default_options(options);
  parse_c_object_factory_options(cmdline, options);

  if(cmdline.isset("function"))
    options.set_option("function", cmdline.get_value("function"));

  if(cmdline.isset("cover") && cmdline.isset("unwinding-assertions"))
  {
    log.error()
      << "--cover and --unwinding-assertions must not be given together"
      << messaget::eom;
    exit(CPROVER_EXIT_USAGE_ERROR);
  }

  // We want to warn the user that if we are using standard checks (that enables
  // unwinding-assertions) and we did not disable them manually.
  if(
    cmdline.isset("cover") && !cmdline.isset("no-standard-checks") &&
    !cmdline.isset("no-unwinding-assertions"))
  {
    log.warning() << "--cover is incompatible with --unwinding-assertions, so "
                     "unwinding-assertions will be defaulted to false"
                  << messaget::eom;
  }

  // We want to set the unwinding-assertions option as early as we can,
  // otherwise we come across two issues: 1) there's no way to deactivate it
  // with `--no-unwinding-assertions`, as the `--no-xxx` flags are set by
  // `goto_check_c` which doesn't provide handling for the options, and 2) we
  // handle it only when we use `--no-standard-checks`, but if we do so, we have
  // already printed a couple times to the screen that `--unwinding-assertions`
  // must be passed because of some activation/sensitive further down below.
  if(cmdline.isset("unwinding-assertions"))
  {
    options.set_option("unwinding-assertions", true);
    options.set_option("paths-symex-explore-all", true);
  }
  else if(cmdline.isset("no-unwinding-assertions"))
  {
    options.set_option("unwinding-assertions", false);
    options.set_option("paths-symex-explore-all", false);
  }

  if(cmdline.isset("max-field-sensitivity-array-size"))
  {
    options.set_option(
      "max-field-sensitivity-array-size",
      cmdline.get_value("max-field-sensitivity-array-size"));
  }

  if(cmdline.isset("no-array-field-sensitivity"))
  {
    if(cmdline.isset("max-field-sensitivity-array-size"))
    {
      log.error()
        << "--no-array-field-sensitivity and --max-field-sensitivity-array-size"
        << " must not be given together" << messaget::eom;
      exit(CPROVER_EXIT_USAGE_ERROR);
    }
    options.set_option("no-array-field-sensitivity", true);
  }

  if(cmdline.isset("reachability-slice") &&
     cmdline.isset("reachability-slice-fb"))
  {
    log.error()
      << "--reachability-slice and --reachability-slice-fb must not be "
      << "given together" << messaget::eom;
    exit(CPROVER_EXIT_USAGE_ERROR);
  }

  if(cmdline.isset("full-slice"))
    options.set_option("full-slice", true);

  if(cmdline.isset("show-symex-strategies"))
  {
    log.status() << show_path_strategies() << messaget::eom;
    exit(CPROVER_EXIT_SUCCESS);
  }

  parse_path_strategy_options(cmdline, options, ui_message_handler);

  if(cmdline.isset("program-only"))
    options.set_option("program-only", true);

  if(cmdline.isset("show-byte-ops"))
    options.set_option("show-byte-ops", true);

  if(cmdline.isset("show-vcc"))
    options.set_option("show-vcc", true);

  if(cmdline.isset("cover"))
  {
    parse_cover_options(cmdline, options);
    // The default unwinding assertions option needs to be switched off when
    // performing coverage checks because we intend to solve for coverage rather
    // than assertions.
    options.set_option("unwinding-assertions", false);
  }

  if(cmdline.isset("mm"))
    options.set_option("mm", cmdline.get_value("mm"));

  if(cmdline.isset("symex-complexity-limit"))
  {
    options.set_option(
      "symex-complexity-limit", cmdline.get_value("symex-complexity-limit"));
    log.warning() << "**** WARNING: Complexity-limited analysis may yield "
                     "unsound verification results"
                  << messaget::eom;
  }

  if(cmdline.isset("symex-complexity-failed-child-loops-limit"))
  {
    options.set_option(
      "symex-complexity-failed-child-loops-limit",
      cmdline.get_value("symex-complexity-failed-child-loops-limit"));
    if(!cmdline.isset("symex-complexity-limit"))
    {
      log.warning() << "**** WARNING: Complexity-limited analysis may yield "
                       "unsound verification results"
                    << messaget::eom;
    }
  }

  if(cmdline.isset("property"))
    options.set_option("property", cmdline.get_values("property"));

  if(cmdline.isset("drop-unused-functions"))
    options.set_option("drop-unused-functions", true);

  if(cmdline.isset("string-abstraction"))
    options.set_option("string-abstraction", true);

  if(cmdline.isset("reachability-slice-fb"))
    options.set_option("reachability-slice-fb", true);

  if(cmdline.isset("reachability-slice"))
    options.set_option("reachability-slice", true);

  if(cmdline.isset("nondet-static"))
    options.set_option("nondet-static", true);

  if(cmdline.isset("inline"))
    options.set_option("inline", true);
  if(cmdline.isset("no-inline"))
    options.set_option("inline", false);

  if(cmdline.isset("no-simplify"))
    options.set_option("simplify", false);

  if(cmdline.isset("stop-on-fail") ||
     cmdline.isset("dimacs") ||
     cmdline.isset("outfile"))
    options.set_option("stop-on-fail", true);

  if(
    cmdline.isset("trace") || cmdline.isset("compact-trace") ||
    cmdline.isset("stack-trace") || cmdline.isset("stop-on-fail") ||
    (ui_message_handler.get_ui() != ui_message_handlert::uit::PLAIN &&
     !cmdline.isset("cover")))
  {
    options.set_option("trace", true);
  }

  if(cmdline.isset("export-symex-ready-goto"))
  {
    options.set_option(
      "export-symex-ready-goto", cmdline.get_value("export-symex-ready-goto"));
    if(options.get_option("export-symex-ready-goto").empty())
    {
      log.error()
        << "ERROR: Please provide a filename to write the goto-binary to."
        << messaget::eom;
      exit(CPROVER_EXIT_INTERNAL_ERROR);
    }
  }

  if(cmdline.isset("localize-faults"))
    options.set_option("localize-faults", true);

  if(cmdline.isset("unwind"))
  {
    options.set_option("unwind", cmdline.get_value("unwind"));
    if(
      !options.get_bool_option("unwinding-assertions") &&
      !cmdline.isset("unwinding-assertions"))
    {
      log.warning() << "**** WARNING: Use --unwinding-assertions to obtain "
                       "sound verification results"
                    << messaget::eom;
    }
  }

  if(cmdline.isset("depth"))
  {
    options.set_option("depth", cmdline.get_value("depth"));
    log.warning()
      << "**** WARNING: Depth-bounded analysis may yield unsound verification "
         "results"
      << messaget::eom;
  }

  if(cmdline.isset("slice-by-trace"))
  {
    log.error() << "--slice-by-trace has been removed" << messaget::eom;
    exit(CPROVER_EXIT_USAGE_ERROR);
  }

  if(cmdline.isset("unwindset"))
  {
    options.set_option(
      "unwindset", cmdline.get_comma_separated_values("unwindset"));
    if(
      !options.get_bool_option("unwinding-assertions") &&
      !cmdline.isset("unwinding-assertions"))
    {
      log.warning() << "**** WARNING: Use --unwinding-assertions to obtain "
                       "sound verification results"
                    << messaget::eom;
    }
  }

  // constant propagation
  if(cmdline.isset("no-propagation"))
    options.set_option("propagation", false);

  // transform self loops to assumptions
  options.set_option(
    "self-loops-to-assumptions",
    !cmdline.isset("no-self-loops-to-assumptions"));

  // all (other) checks supported by goto_check
  PARSE_OPTIONS_GOTO_CHECK(cmdline, options);

  if(cmdline.isset("partial-loops"))
  {
    options.set_option("partial-loops", true);
    log.warning()
      << "**** WARNING: --partial-loops may yield unsound verification results"
      << messaget::eom;
  }

  // remove unused equations
  if(cmdline.isset("slice-formula"))
    options.set_option("slice-formula", true);

  if(cmdline.isset("arrays-uf-always"))
    options.set_option("arrays-uf", "always");
  else if(cmdline.isset("arrays-uf-never"))
    options.set_option("arrays-uf", "never");

  if(cmdline.isset("show-array-constraints"))
    options.set_option("show-array-constraints", true);

  if(cmdline.isset("refine-strings"))
  {
    // The refined-string solver is a SAT (bit-vector refinement) procedure and
    // cannot run on an SMT2 back-end. The SMT2 back-end instead lowers string
    // operations to the SMT-LIB theory of strings directly. Reject the
    // contradictory combination rather than silently ignoring one of them.
    if(cmdline.isset("smt2") || cmdline.isset("incremental-smt2-solver"))
    {
      log.error() << "--refine-strings is not supported with an SMT2 back-end; "
                     "the SMT2 back-end handles strings via the SMT-LIB theory "
                     "of strings"
                  << messaget::eom;
      exit(CPROVER_EXIT_USAGE_ERROR);
    }

    options.set_option("refine-strings", true);
    options.set_option("string-printable", cmdline.isset("string-printable"));
  }

  options.set_option(
    "symex-cache-dereferences", cmdline.isset("symex-cache-dereferences"));

  if(cmdline.isset("incremental-loop"))
  {
    options.set_option(
      "incremental-loop", cmdline.get_value("incremental-loop"));
    options.set_option("refine", true);
    options.set_option("refine-arrays", true);

    if(cmdline.isset("unwind-min"))
      options.set_option("unwind-min", cmdline.get_value("unwind-min"));

    if(cmdline.isset("unwind-max"))
      options.set_option("unwind-max", cmdline.get_value("unwind-max"));

    if(cmdline.isset("ignore-properties-before-unwind-min"))
      options.set_option("ignore-properties-before-unwind-min", true);

    if(cmdline.isset("paths"))
    {
      log.error() << "--paths not supported with --incremental-loop"
                  << messaget::eom;
      exit(CPROVER_EXIT_USAGE_ERROR);
    }
  }

  if(cmdline.isset("graphml-witness"))
  {
    options.set_option("graphml-witness", cmdline.get_value("graphml-witness"));
    options.set_option("stop-on-fail", true);
    options.set_option("trace", true);
  }

  if(cmdline.isset("symex-coverage-report"))
  {
    options.set_option(
      "symex-coverage-report",
      cmdline.get_value("symex-coverage-report"));
    options.set_option("paths-symex-explore-all", true);
  }

  if(cmdline.isset("validate-ssa-equation"))
  {
    options.set_option("validate-ssa-equation", true);
  }

  if(cmdline.isset("validate-goto-model"))
  {
    options.set_option("validate-goto-model", true);
  }

  if(cmdline.isset("show-goto-symex-steps"))
    options.set_option("show-goto-symex-steps", true);

  if(cmdline.isset("show-points-to-sets"))
    options.set_option("show-points-to-sets", true);

  PARSE_OPTIONS_GOTO_TRACE(cmdline, options);

  // Options for process_goto_program
  options.set_option("rewrite-rw-ok", true);
  options.set_option("rewrite-union", true);
  options.set_option("goto-btor2", cmdline.isset("goto-btor2"));
  options.set_option("goto-btor2-checks", cmdline.isset("goto-btor2-checks"));
  options.set_option(
    "c2btor-witness-source-tokens",
    cmdline.isset("goto-btor2") && cmdline.isset("goto-btor2-map-out"));

  if(cmdline.isset("goto-btor2"))
  {
    if(!cmdline.isset("goto-btor2-checks"))
      options.set_option("built-in-assertions", false);
    options.set_option(
      "goto-btor2-slice-property",
      !cmdline.isset("goto-btor2-no-slice-property"));
  }

  if(cmdline.isset("smt1"))
  {
    log.error() << "--smt1 is no longer supported" << messaget::eom;
    exit(CPROVER_EXIT_USAGE_ERROR);
  }

  parse_solver_options(cmdline, options);
}

/// invoke main modules
int cbmc_parse_optionst::doit()
{
  if(cmdline.isset("version") || cmdline.isset('v'))
  {
    std::cout << C2BTOR_VERSION << '\n';
    return CPROVER_EXIT_SUCCESS;
  }

  if(cmdline.isset("goto-btor2"))
  {
    const char *const exclusive_options[][2] = {
      {"32", "64"},
      {"inline", "no-inline"},
      {"goto-btor2-lbe", "goto-btor2-no-lbe"},
      {"goto-btor2-scalar-blocks", "goto-btor2-no-scalar-blocks"},
      {"goto-btor2-slice-property", "goto-btor2-no-slice-property"},
      {"goto-btor2-merge-bads", "goto-btor2-no-merge-bads"},
      {"goto-btor2-optimize-state", "goto-btor2-no-optimize-state"}};
    for(const auto &pair : exclusive_options)
    {
      if(cmdline.isset(pair[0]) && cmdline.isset(pair[1]))
      {
        log.error() << "--" << pair[0] << " conflicts with --" << pair[1]
                    << messaget::eom;
        return CPROVER_EXIT_USAGE_ERROR;
      }
    }
    for(const char *option : {
          "array", "memory", "array-mixed-threshold-bits",
          "memory-object-max-bytes", "goto-btor2-out", "goto-btor2-map-out"})
    {
      const auto &values = cmdline.get_values(option);
      if(values.size() > 1 &&
         std::any_of(values.begin(), values.end(), [&](const std::string &value) {
           return value != values.front();
         }))
      {
        log.error() << "--" << option << " has conflicting repeated values"
                    << messaget::eom;
        return CPROVER_EXIT_USAGE_ERROR;
      }
    }
    // Validate aliases before opening either stream, which would truncate it.
    if(cmdline.isset("goto-btor2-out") && cmdline.isset("goto-btor2-map-out"))
    {
      std::error_code model_error, map_error, equivalent_error;
      const auto model_path = std::filesystem::weakly_canonical(
        cmdline.get_value("goto-btor2-out"), model_error);
      const auto map_path = std::filesystem::weakly_canonical(
        cmdline.get_value("goto-btor2-map-out"), map_error);
      if((!model_error && !map_error && model_path == map_path) ||
         std::filesystem::equivalent(model_path, map_path, equivalent_error))
      {
        log.error() << "BTOR2 model and source map need distinct paths"
                    << messaget::eom;
        return CPROVER_EXIT_USAGE_ERROR;
      }
    }
    if(cmdline.isset("property") || cmdline.isset("claim"))
    {
      log.error() << "--property/--claim are not supported with --goto-btor2; "
                     "all source ASSERTs are translated (optionally merge bads)"
                  << messaget::eom;
      return CPROVER_EXIT_USAGE_ERROR;
    }
    // These shared parser options belong to BMC, not transition-system
    // conversion. Reject them before preprocessing or opening output files.
    for(const char *option : {
          "unwind",
          "unwindset",
          "unwind-min",
          "unwind-max",
          "unwinding-assertions",
          "no-unwinding-assertions",
          "partial-loops",
          "incremental-loop",
          "ignore-properties-before-unwind-min"})
    {
      if(cmdline.isset(option))
      {
        log.error() << "--" << option
                    << " is a BMC option and is not supported with --goto-btor2; "
                       "BTOR2 represents loops using PC transitions"
                    << messaget::eom;
        return CPROVER_EXIT_USAGE_ERROR;
      }
    }
  }

  if(
    (cmdline.isset("goto-btor2-out") || cmdline.isset("goto-btor2-map-out") ||
     cmdline.isset("array") || cmdline.isset("array-mixed-threshold-bits") ||
     cmdline.isset("memory") || cmdline.isset("memory-object-max-bytes") ||
     cmdline.isset("goto-btor2-lbe") ||
     cmdline.isset("goto-btor2-no-lbe") ||
     cmdline.isset("goto-btor2-slice-property") ||
     cmdline.isset("goto-btor2-no-slice-property") ||
     cmdline.isset("goto-btor2-initialization") ||
     cmdline.isset("goto-btor2-scalar-slice") ||
     cmdline.isset("goto-btor2-optimize-state") ||
     cmdline.isset("goto-btor2-no-optimize-state") ||
     cmdline.isset("goto-btor2-logical-arrays") ||
     cmdline.isset("goto-btor2-scalar-blocks") ||
     cmdline.isset("goto-btor2-no-scalar-blocks") ||
     cmdline.isset("goto-btor2-array-blocks") ||
     cmdline.isset("goto-btor2-array-loop-summary") ||
     cmdline.isset("goto-btor2-scalar-loop-summary") ||
     cmdline.isset("goto-btor2-no-array-optimizations") ||
     cmdline.isset("goto-btor2-symbolic-heap") ||
     cmdline.isset("goto-btor2-symbolic-heap-arrays") ||
     cmdline.isset("goto-btor2-symbolic-heap-wide-offsets") ||
     cmdline.isset("goto-btor2-symbolic-heap-bv-array-fallback") ||
     cmdline.isset("goto-btor2-symbolic-heap-compact")) &&
    !cmdline.isset("goto-btor2"))
  {
    log.error()
      << "BTOR2 array/memory options require --goto-btor2"
      << messaget::eom;
    return CPROVER_EXIT_USAGE_ERROR;
  }
  array_encoding_optionst array_encoding;
  const auto memory_mode =
    cmdline.isset("memory") ? cmdline.get_value("memory") : "object";
  if(memory_mode != "object" && memory_mode != "global")
  {
    log.error() << "--memory requires object or global" << messaget::eom;
    return CPROVER_EXIT_USAGE_ERROR;
  }
  array_encoding.object_memory = memory_mode == "object";
  const auto array_mode =
    cmdline.isset("array") ? cmdline.get_value("array") : "bv";
  if(array_mode != "bv" && array_mode != "array" && array_mode != "mixed")
  {
    log.error() << "--array requires bv, array or mixed" << messaget::eom;
    return CPROVER_EXIT_USAGE_ERROR;
  }
  array_encoding.bitvectors = array_mode == "bv";
  array_encoding.mixed = array_mode == "mixed";

  // Native-Array storage is the user-visible request; the certified array
  // pipeline is part of that representation, not a separate tuning decision.
  // BV uses representation-independent state pruning, without native-Array
  // summaries or symbolic-heap storage transformations.
  const bool array_sort_defaults =
    (array_mode == "array" || array_mode == "mixed") &&
    !cmdline.isset("goto-btor2-no-array-optimizations");
  const bool lbe = !cmdline.isset("goto-btor2-no-lbe");
  const bool optimize_state =
    !cmdline.isset("goto-btor2-no-optimize-state") &&
    (cmdline.isset("goto-btor2-optimize-state") || array_sort_defaults ||
     array_encoding.bitvectors);
  const bool logical_arrays =
    cmdline.isset("goto-btor2-logical-arrays") || array_sort_defaults;
  const bool scalar_blocks =
    !cmdline.isset("goto-btor2-no-scalar-blocks") &&
    (lbe || cmdline.isset("goto-btor2-scalar-blocks"));
  const bool array_blocks =
    cmdline.isset("goto-btor2-array-blocks") ||
    (array_sort_defaults && logical_arrays && scalar_blocks);
  const bool array_loop_summary =
    cmdline.isset("goto-btor2-array-loop-summary") ||
    (array_sort_defaults && logical_arrays &&
     array_encoding.object_memory);
  const bool scalar_loop_summary =
    cmdline.isset("goto-btor2-scalar-loop-summary") ||
    array_sort_defaults;
  array_encoding.symbolic_heap =
    cmdline.isset("goto-btor2-symbolic-heap") ||
    (array_sort_defaults && array_encoding.object_memory);
  array_encoding.symbolic_heap_arrays =
    cmdline.isset("goto-btor2-symbolic-heap-arrays") ||
    (array_sort_defaults && array_encoding.symbolic_heap &&
     array_encoding.object_memory);
  array_encoding.symbolic_heap_wide_offsets =
    cmdline.isset("goto-btor2-symbolic-heap-wide-offsets") ||
    (array_sort_defaults && array_encoding.symbolic_heap_arrays);
  array_encoding.symbolic_heap_bv_array_fallback =
    cmdline.isset("goto-btor2-symbolic-heap-bv-array-fallback");
  array_encoding.symbolic_heap_compact =
    cmdline.isset("goto-btor2-symbolic-heap-compact") ||
    (array_sort_defaults && array_encoding.symbolic_heap_arrays);

  if(scalar_blocks && !lbe)
  {
    log.error() << "--goto-btor2-scalar-blocks requires LBE" << messaget::eom;
    return CPROVER_EXIT_USAGE_ERROR;
  }
  if(array_blocks && (!logical_arrays || !scalar_blocks))
  {
    log.error() << "--goto-btor2-array-blocks requires "
                   "--goto-btor2-logical-arrays and --goto-btor2-scalar-blocks"
                << messaget::eom;
    return CPROVER_EXIT_USAGE_ERROR;
  }
  if((array_encoding.symbolic_heap_wide_offsets ||
      array_encoding.symbolic_heap_bv_array_fallback ||
      array_encoding.symbolic_heap_compact) &&
     !array_encoding.symbolic_heap_arrays)
  {
    log.error() << "symbolic heap wide offsets and BV Array fallback require "
                   "--goto-btor2-symbolic-heap-arrays"
                << messaget::eom;
    return CPROVER_EXIT_USAGE_ERROR;
  }
  if(array_encoding.symbolic_heap_arrays &&
     (!array_encoding.symbolic_heap || !array_encoding.object_memory))
  {
    log.error() << "--goto-btor2-symbolic-heap-arrays requires "
                   "--goto-btor2-symbolic-heap and --memory object"
                << messaget::eom;
    return CPROVER_EXIT_USAGE_ERROR;
  }
  if(array_loop_summary &&
     (!logical_arrays || !array_encoding.object_memory ||
      array_encoding.bitvectors))
  {
    log.error() << "--goto-btor2-array-loop-summary requires "
                   "--goto-btor2-logical-arrays, --memory object and "
                   "--array array|mixed"
                << messaget::eom;
    return CPROVER_EXIT_USAGE_ERROR;
  }
  if(array_encoding.mixed && !array_encoding.object_memory)
  {
    log.error() << "--array mixed requires --memory object" << messaget::eom;
    return CPROVER_EXIT_USAGE_ERROR;
  }
  if(cmdline.isset("array-mixed-threshold-bits"))
  {
    const auto value = cmdline.get_value("array-mixed-threshold-bits");
    try
    {
      std::size_t end = 0;
      const auto parsed = std::stoull(value, &end);
      if(
        !array_encoding.mixed || value.empty() ||
        !std::all_of(value.begin(), value.end(), [](char digit) {
          return digit >= '0' && digit <= '9';
        }) ||
        end != value.size() || parsed == 0 ||
        parsed > std::numeric_limits<std::size_t>::max())
        throw std::invalid_argument("mixed array threshold");
      array_encoding.mixed_threshold_bits = static_cast<std::size_t>(parsed);
    }
    catch(const std::exception &)
    {
      log.error() << "--array-mixed-threshold-bits requires --array mixed and "
                     "a positive integer"
                  << messaget::eom;
      return CPROVER_EXIT_USAGE_ERROR;
    }
  }
  // Retain both historical spellings as validated no-op compatibility options.
  const auto initialization = cmdline.isset("goto-btor2-initialization")
                                ? cmdline.get_value("goto-btor2-initialization")
                                : "strict";
  if(initialization != "strict" && initialization != "nondet")
  {
    log.error() << "--goto-btor2-initialization requires strict or nondet"
                << messaget::eom;
    return CPROVER_EXIT_USAGE_ERROR;
  }
  const auto scalar_slice = cmdline.isset("goto-btor2-scalar-slice")
                              ? cmdline.get_value("goto-btor2-scalar-slice")
                              : "none";
  if(scalar_slice != "none" && scalar_slice != "dead" && scalar_slice != "liveness")
  {
    log.error() << "--goto-btor2-scalar-slice requires none, dead or liveness"
                << messaget::eom;
    return CPROVER_EXIT_USAGE_ERROR;
  }
  if(cmdline.isset("memory-object-max-bytes"))
  {
    const auto value = cmdline.get_value("memory-object-max-bytes");
    try
    {
      std::size_t end = 0;
      const auto parsed = std::stoull(value, &end);
      if(
        value.empty() || value[0] == '-' || end != value.size() || parsed == 0)
        throw std::invalid_argument("object capacity");
      array_encoding.max_object_bytes = static_cast<std::size_t>(parsed);
    }
    catch(const std::exception &)
    {
      log.error() << "--memory-object-max-bytes requires a positive integer"
                  << messaget::eom;
      return CPROVER_EXIT_USAGE_ERROR;
    }
  }

  //
  // command line options
  //

  optionst options;
  get_command_line_options(options);

  messaget::eval_verbosity(
    cmdline.get_value("verbosity"), messaget::M_STATUS, ui_message_handler);

  log.status() << "C2BTOR version " << C2BTOR_VERSION << " "
               << config.this_architecture() << " "
               << config.this_operating_system() << messaget::eom;
  log.status() << "Using CBMC's C parser and GOTO-IR, version "
               << CBMC_VERSION << messaget::eom;

  //
  // Unwinding of transition systems is done by hw-cbmc.
  //

  if(cmdline.isset("module") ||
     cmdline.isset("gen-interface"))
  {
    log.error() << "This version of CBMC has no support for "
                   " hardware modules. Please use hw-cbmc."
                << messaget::eom;
    return CPROVER_EXIT_USAGE_ERROR;
  }

  if(cmdline.isset("show-points-to-sets"))
  {
    if(!cmdline.isset("json-ui") || cmdline.isset("xml-ui"))
    {
      log.error() << "--show-points-to-sets supports only"
                     " json output. Use --json-ui."
                  << messaget::eom;
      return CPROVER_EXIT_USAGE_ERROR;
    }
  }

  if(cmdline.isset("show-array-constraints"))
  {
    if(!cmdline.isset("json-ui") || cmdline.isset("xml-ui"))
    {
      log.error() << "--show-array-constraints supports only"
                     " json output. Use --json-ui."
                  << messaget::eom;
      return CPROVER_EXIT_USAGE_ERROR;
    }
  }

  register_languages();

  // configure gcc, if required
  if(config.ansi_c.preprocessor == configt::ansi_ct::preprocessort::GCC)
  {
    gcc_versiont gcc_version;
    gcc_version.get("gcc");
    configure_gcc(gcc_version);
  }

  if(cmdline.isset("test-preprocessor"))
    return test_c_preprocessor(ui_message_handler)
             ? CPROVER_EXIT_PREPROCESSOR_TEST_FAILED
             : CPROVER_EXIT_SUCCESS;

  if(cmdline.isset("preprocess"))
  {
    preprocessing(options);
    return CPROVER_EXIT_SUCCESS;
  }

  if(cmdline.isset("show-parse-tree"))
  {
    if(
      cmdline.args.size() != 1 ||
      is_goto_binary(cmdline.args[0], ui_message_handler))
    {
      log.error() << "Please give exactly one source file" << messaget::eom;
      return CPROVER_EXIT_INCORRECT_TASK;
    }

    std::string filename=cmdline.args[0];

    std::ifstream infile(widen_if_needed(filename));

    if(!infile)
    {
      log.error() << "failed to open input file '" << filename << "'"
                  << messaget::eom;
      return CPROVER_EXIT_INCORRECT_TASK;
    }

    std::unique_ptr<languaget> language=
      get_language_from_filename(filename);

    if(language==nullptr)
    {
      log.error() << "failed to figure out type of file '" << filename << "'"
                  << messaget::eom;
      return CPROVER_EXIT_INCORRECT_TASK;
    }

    language->set_language_options(options, ui_message_handler);

    log.status() << "Parsing " << filename << messaget::eom;

    if(language->parse(infile, filename, ui_message_handler))
    {
      log.error() << "PARSING ERROR" << messaget::eom;
      return CPROVER_EXIT_INCORRECT_TASK;
    }

    language->show_parse(std::cout, ui_message_handler);
    return CPROVER_EXIT_SUCCESS;
  }

  int get_goto_program_ret =
    get_goto_program(goto_model, options, cmdline, ui_message_handler);

  if(get_goto_program_ret!=-1)
    return get_goto_program_ret;

  // Full goto-program to BTOR2 conversion
  if(cmdline.isset("goto-btor2"))
  {
    btor2_property_optionst properties;
    properties.merge = !cmdline.isset("goto-btor2-no-merge-bads");
    auto main = goto_model.goto_functions.function_map.find(ID_main);
    if(cmdline.isset("goto-btor2-map-out") &&
       main != goto_model.goto_functions.function_map.end())
      btor2_capture_source_events(
        main->second.body, namespacet(goto_model.symbol_table),
        properties.source_provenance,
        "post-frontend-lowering-and-inlining; before callback simplification, property slicing and converter optimization");
    if(
      main != goto_model.goto_functions.function_map.end() &&
      !cmdline.isset("nondet-static"))
      simplify_callback_targets(
        main->second.body, goto_model.symbol_table, log,
        &properties.unreachable_assertions);
    if(main != goto_model.goto_functions.function_map.end())
      btor2_record_source_transform(
        main->second.body, properties.source_provenance,
        "callback-target-and-constant-simplification");
    if(!cmdline.isset("goto-btor2-no-slice-property"))
    {
      // Keep the control-flow skeleton when slicing the inlined program.
      // Ordinary post-dominance does not preserve property reachability in
      // loops: dropping an exit guard while retaining its back edge can turn
      // a terminating loop into an unconditional self-loop. Anchoring every
      // GOTO and ASSUME also retains their transitive data dependencies.
      // Calls and OTHER instructions may affect heap state or termination;
      // preserve these effects even when the generic dependence analysis
      // does not model the converter-specific operations.
      class btor2_property_criteriont : public slicing_criteriont
      {
      public:
        explicit btor2_property_criteriont(const goto_functionst &functions)
        {
          const auto needs_complete_dependencies = [](const exprt &expr) {
            return expr.id() == ID_dereference ||
                   (expr.id() == ID_side_effect &&
                    expr.get(ID_statement) != ID_nondet) ||
                   (expr.id() == ID_index &&
                    to_index_expr(expr).array().type().id() == ID_pointer);
          };
          for(const auto &function : functions.function_map)
          {
            for(const auto &instruction : function.second.body.instructions)
            {
              const auto collect_addressed = [&](const exprt &expr) {
                if(expr.id() == ID_address_of)
                  find_symbols(to_address_of_expr(expr).object(), memory_lifetimes);
                return false;
              };
              has_subexpr(instruction.code(), collect_addressed);
              if(instruction.has_condition())
                has_subexpr(instruction.condition(), collect_addressed);
              // The generic read/write analysis may omit unresolved pointer
              // accesses and converter-specific heap events, including their
              // parameter dependencies. Keep the whole containing function
              // instead of treating an incomplete dependency set as empty.
              if(
                instruction.is_other() ||
                has_subexpr(instruction.code(), needs_complete_dependencies) ||
                (instruction.has_condition() &&
                 has_subexpr(
                   instruction.condition(), needs_complete_dependencies)))
              {
                preserve_functions.insert(function.first);
                break;
              }
            }
          }
        }
        bool operator()(
          const irep_idt &function,
          goto_programt::const_targett target) const override
        {
          const auto memory_lifetime = [&](const symbol_exprt &symbol) {
            const auto &type = symbol.type().id();
            return memory_lifetimes.count(symbol.get_identifier()) != 0 ||
              type == ID_array || type == ID_struct || type == ID_struct_tag ||
              type == ID_union || type == ID_union_tag;
          };
          return preserve_functions.count(function) != 0 ||
                 (target->is_decl() && memory_lifetime(target->decl_symbol())) ||
                 (target->is_dead() && memory_lifetime(target->dead_symbol())) ||
                 target->is_assert() || target->is_goto() || target->is_assume() ||
                 target->source_location().get_bool("c2btor_witness_value_root") ||
                 target->is_function_call() || target->is_other();
        }

      private:
        std::set<irep_idt> preserve_functions;
        find_symbols_sett memory_lifetimes;
      };
      const btor2_property_criteriont criterion(goto_model.goto_functions);
      log.status() << "Property-slicing GOTO program before BTOR2 conversion"
                   << messaget::eom;
      // Function-local simplification renumbers main from zero. The
      // interprocedural dependence analysis requires globally unique locations.
      goto_model.goto_functions.update();
      full_slicer(
        goto_model.goto_functions,
        namespacet(goto_model.symbol_table),
        criterion,
        log.get_message_handler());
      goto_model.goto_functions.update();
    }
    if(main != goto_model.goto_functions.function_map.end())
    {
      btor2_record_source_transform(
        main->second.body, properties.source_provenance, "property-slicing");
      if(properties.source_provenance.enabled)
      {
        auto record = properties.source_provenance.transformations.end();
        --record;
        to_json_object(*record)["enabled"] = jsont::json_boolean(
          !cmdline.isset("goto-btor2-no-slice-property"));
      }
    }
    if(main != goto_model.goto_functions.function_map.end())
      lower_array_operations(
        main->second.body, goto_model.symbol_table, log,
        array_encoding.object_memory && array_encoding.bitvectors &&
        !array_encoding.symbolic_heap_bv_array_fallback &&
        config.ansi_c.endianness == configt::ansi_ct::endiannesst::IS_LITTLE_ENDIAN);
    if(main != goto_model.goto_functions.function_map.end())
      btor2_record_source_transform(
        main->second.body, properties.source_provenance, "array-operation-lowering");
    if(
      main != goto_model.goto_functions.function_map.end() &&
      properties.unreachable_assertions.empty() &&
      std::none_of(
        main->second.body.instructions.begin(),
        main->second.body.instructions.end(),
        [](const goto_programt::instructiont &instruction)
        { return instruction.is_assert(); }))
    {
      log.error() << "No selected source property; no model emitted"
                  << messaget::eom;
      return CPROVER_EXIT_INCORRECT_TASK;
    }
    std::ofstream out_file;
    std::ostream *out = &std::cout;
    if(cmdline.isset("goto-btor2-out"))
    {
      out_file.open(cmdline.get_value("goto-btor2-out"));
      if(!out_file)
      {
        log.error() << "failed to open --goto-btor2-out file" << messaget::eom;
        return CPROVER_EXIT_INCORRECT_TASK;
      }
      out = &out_file;
    }

    // Generic checks were instrumented once in process_goto_program, only
    // when --goto-btor2-checks was requested. Preserve the IDs already assigned
    // there; any assertions introduced by later lowering get unused IDs.
    label_btor2_properties(goto_model, properties.unreachable_assertions);

    std::ofstream source_map;
    if(cmdline.isset("goto-btor2-map-out"))
    {
      source_map.open(cmdline.get_value("goto-btor2-map-out"));
      if(!source_map)
      {
        log.error() << "failed to open --goto-btor2-map-out file"
                    << messaget::eom;
        return CPROVER_EXIT_INCORRECT_TASK;
      }
    }
    unsigned heap_objects = 0;
    if(cmdline.isset("goto-btor2-heap-objects"))
    {
      const auto value = cmdline.get_value("goto-btor2-heap-objects");
      try
      {
        std::size_t end = 0;
        const auto parsed = std::stoul(value, &end);
        if(value.empty() || value[0] == '-' || end != value.size() ||
           parsed > std::numeric_limits<unsigned>::max())
          throw std::invalid_argument("allocation budget");
        heap_objects = static_cast<unsigned>(parsed);
      }
      catch(const std::exception &)
      {
        log.error() << "--goto-btor2-heap-objects requires a nonnegative integer"
                    << messaget::eom;
        return CPROVER_EXIT_USAGE_ERROR;
      }
    }
    log.status() << "Memory encoding: " << memory_mode << messaget::eom;
    if(array_encoding.mixed)
      log.status() << "Mixed array threshold: "
                   << array_encoding.mixed_threshold_bits << " bits"
                   << messaget::eom;
    if(array_encoding.bitvectors || array_encoding.object_memory)
    {
      if(array_encoding.max_object_bytes)
        log.status() << "Runtime-sized object capacity: "
                     << *array_encoding.max_object_bytes << " bytes per object"
                     << messaget::eom;
      else
        log.status() << "Runtime-sized object capacity: automatic (GotoIR bounds)"
                     << messaget::eom;
    }
    if(
      write_goto_btor2(
        goto_model,
        *out,
        log,
        cmdline.isset("goto-btor2-warn-comments"),
        source_map.is_open() ? &source_map : nullptr,
        heap_objects,
        array_encoding,
        properties,
        !cmdline.isset("goto-btor2-no-lbe"),
        scalar_slice == "liveness" ? scalar_projection_modet::LIVENESS
          : scalar_slice == "dead" ? scalar_projection_modet::DEAD
                                   : scalar_projection_modet::NONE,
        btor2_optimization_optionst{
          optimize_state,
          logical_arrays,
          scalar_blocks,
          array_blocks,
          array_loop_summary,
          scalar_loop_summary}))
    {
      // The output streams are opened before conversion; a rejected conversion
      // would leave empty model/map files whose existence could be mistaken
      // for success. The exit code stays the source of truth.
      out_file.close();
      source_map.close();
      for(const char *option :
          {"goto-btor2-out", "goto-btor2-map-out"})
      {
        if(!cmdline.isset(option))
          continue;
        const auto path = cmdline.get_value(option);
        std::error_code error;
        if(
          std::filesystem::exists(path, error) &&
          std::filesystem::file_size(path, error) == 0)
          std::filesystem::remove(path, error);
      }
      return CPROVER_EXIT_INTERNAL_ERROR;
    }
    return CPROVER_EXIT_SUCCESS;
  }

  if(cmdline.isset("show-claims") || // will go away
     cmdline.isset("show-properties")) // use this one
  {
    show_properties(goto_model, ui_message_handler);
    return CPROVER_EXIT_SUCCESS;
  }

  if(set_properties())
    return CPROVER_EXIT_SET_PROPERTIES_FAILED;

  // At this point, our goto-model should be in symex-ready-goto form (all of
  // the transformations have been run and the program is ready to be given
  // to the solver).
  if(options.is_set("export-symex-ready-goto"))
  {
    auto symex_ready_goto_filename =
      options.get_option("export-symex-ready-goto");

    bool success = !write_goto_binary(
      symex_ready_goto_filename, goto_model, ui_message_handler);

    if(!success)
    {
      log.error() << "ERROR: Unable to export goto-program in file "
                  << symex_ready_goto_filename << messaget::eom;
      return CPROVER_EXIT_INTERNAL_ERROR;
    }
    else
    {
      log.status() << "Exported goto-program in symex-ready-goto form at "
                   << symex_ready_goto_filename << messaget::eom;
      return CPROVER_EXIT_SUCCESS;
    }
  }

  if(
    options.get_bool_option("program-only") ||
    options.get_bool_option("show-vcc") ||
    options.get_bool_option("show-byte-ops"))
  {
    if(options.get_bool_option("paths"))
    {
      all_properties_verifiert<single_path_symex_only_checkert> verifier(
        options, ui_message_handler, goto_model);
      (void)verifier();
    }
    else
    {
      all_properties_verifiert<multi_path_symex_only_checkert> verifier(
        options, ui_message_handler, goto_model);
      (void)verifier();
    }

    return CPROVER_EXIT_SUCCESS;
  }

  if(
    options.get_bool_option("dimacs") || !options.get_option("outfile").empty())
  {
    if(options.get_bool_option("paths"))
    {
      stop_on_fail_verifiert<single_path_symex_checkert> verifier(
        options, ui_message_handler, goto_model);
      (void)verifier();
    }
    else
    {
      stop_on_fail_verifiert<multi_path_symex_checkert> verifier(
        options, ui_message_handler, goto_model);
      (void)verifier();
    }

    return CPROVER_EXIT_SUCCESS;
  }

  if(options.is_set("cover"))
  {
    cover_goals_verifier_with_trace_storaget<multi_path_symex_checkert>
      verifier(options, ui_message_handler, goto_model);
    (void)verifier();
    verifier.report();

    if(options.get_bool_option("show-test-suite"))
    {
      c_test_input_generatort test_generator(ui_message_handler, options);
      test_generator(verifier.get_traces());
    }

    return CPROVER_EXIT_SUCCESS;
  }

  std::unique_ptr<goto_verifiert> verifier = nullptr;

  if(options.is_set("incremental-loop"))
  {
    if(options.get_bool_option("stop-on-fail"))
    {
      verifier = std::make_unique<
        stop_on_fail_verifiert<single_loop_incremental_symex_checkert>>(
        options, ui_message_handler, goto_model);
    }
    else
    {
      verifier = std::make_unique<all_properties_verifier_with_trace_storaget<
        single_loop_incremental_symex_checkert>>(
        options, ui_message_handler, goto_model);
    }
  }
  else if(
    options.get_bool_option("stop-on-fail") && options.get_bool_option("paths"))
  {
    verifier =
      std::make_unique<stop_on_fail_verifiert<single_path_symex_checkert>>(
        options, ui_message_handler, goto_model);
  }
  else if(
    options.get_bool_option("stop-on-fail") &&
    !options.get_bool_option("paths"))
  {
    if(options.get_bool_option("localize-faults"))
    {
      verifier =
        std::make_unique<stop_on_fail_verifier_with_fault_localizationt<
          multi_path_symex_checkert>>(options, ui_message_handler, goto_model);
    }
    else
    {
      verifier =
        std::make_unique<stop_on_fail_verifiert<multi_path_symex_checkert>>(
          options, ui_message_handler, goto_model);
    }
  }
  else if(
    !options.get_bool_option("stop-on-fail") &&
    options.get_bool_option("paths"))
  {
    verifier = std::make_unique<
      all_properties_verifier_with_trace_storaget<single_path_symex_checkert>>(
      options, ui_message_handler, goto_model);
  }
  else if(
    !options.get_bool_option("stop-on-fail") &&
    !options.get_bool_option("paths"))
  {
    if(options.get_bool_option("localize-faults"))
    {
      verifier =
        std::make_unique<all_properties_verifier_with_fault_localizationt<
          multi_path_symex_checkert>>(options, ui_message_handler, goto_model);
    }
    else
    {
      verifier = std::make_unique<
        all_properties_verifier_with_trace_storaget<multi_path_symex_checkert>>(
        options, ui_message_handler, goto_model);
    }
  }
  else
  {
    UNREACHABLE;
  }

  const resultt result = (*verifier)();
  verifier->report();

  return result_to_exit_code(result);
}

bool cbmc_parse_optionst::set_properties()
{
  if(cmdline.isset("claim")) // will go away
    ::set_properties(goto_model, cmdline.get_values("claim"));

  if(cmdline.isset("property")) // use this one
    ::set_properties(goto_model, cmdline.get_values("property"));

  return false;
}

int cbmc_parse_optionst::get_goto_program(
  goto_modelt &goto_model,
  const optionst &options,
  const cmdlinet &cmdline,
  ui_message_handlert &ui_message_handler)
{
  messaget log{ui_message_handler};
  if(cmdline.args.empty())
  {
    log.error() << "Please provide a program to verify" << messaget::eom;
    return CPROVER_EXIT_INCORRECT_TASK;
  }

  goto_model = initialize_goto_model(cmdline.args, ui_message_handler, options);

  update_max_malloc_size(goto_model, ui_message_handler);

  if(cmdline.isset("show-symbol-table"))
  {
    show_symbol_table(goto_model, ui_message_handler);
    return CPROVER_EXIT_SUCCESS;
  }

  if(cbmc_parse_optionst::process_goto_program(goto_model, options, log))
    return CPROVER_EXIT_INTERNAL_ERROR;

  if(cmdline.isset("validate-goto-model"))
  {
    goto_model.validate();
  }

  // show it?
  if(cmdline.isset("show-loops"))
  {
    show_loop_ids(ui_message_handler.get_ui(), goto_model);
    return CPROVER_EXIT_SUCCESS;
  }

  log.statistics() << config.object_bits_info() << messaget::eom;

  return -1; // no error, continue
}

void cbmc_parse_optionst::preprocessing(const optionst &options)
{
  if(cmdline.args.size() != 1)
  {
    log.error() << "Please provide one program to preprocess" << messaget::eom;
    return;
  }

  std::string filename = cmdline.args[0];

  std::ifstream infile(filename);

  if(!infile)
  {
    log.error() << "failed to open input file" << messaget::eom;
    return;
  }

  std::unique_ptr<languaget> language = get_language_from_filename(filename);

  if(language == nullptr)
  {
    log.error() << "failed to figure out type of file" << messaget::eom;
    return;
  }

  language->set_language_options(options, ui_message_handler);

  if(language->preprocess(infile, filename, std::cout, ui_message_handler))
    log.error() << "PREPROCESSING ERROR" << messaget::eom;
}

bool cbmc_parse_optionst::process_goto_program(
  goto_modelt &goto_model,
  const optionst &options,
  messaget &log)
{
  // Remove inline assembler; this needs to happen before
  // adding the library.
  remove_asm(goto_model, log.get_message_handler());

  // add the library
  log.status() << "Adding CPROVER library (" << config.ansi_c.arch << ")"
               << messaget::eom;
  link_to_library(
    goto_model, log.get_message_handler(), cprover_cpp_library_factory);
  link_to_library(
    goto_model, log.get_message_handler(), cprover_c_library_factory);
  // library functions may introduce inline assembler
  while(has_asm(goto_model))
  {
    remove_asm(goto_model, log.get_message_handler());
    link_to_library(
      goto_model, log.get_message_handler(), cprover_cpp_library_factory);
    link_to_library(
      goto_model, log.get_message_handler(), cprover_c_library_factory);
  }

  // Common removal of types and complex constructs
  if(::process_goto_program(goto_model, options, log))
    return true;

  if(options.get_bool_option("goto-btor2"))
  {
    // Standard SV-COMP error events are assertions at their original call
    // sites. Ordinary assert/__CPROVER_assert are already GOTO ASSERTs.
    for(auto &function : goto_model.goto_functions.function_map)
      for(auto &instruction : function.second.body.instructions)
      {
        irep_idt target;
        if(instruction.is_assert())
          target = instruction.source_location().get("builtin_function");
        else if(instruction.is_function_call() &&
                instruction.call_function().id() == ID_symbol)
          target = to_symbol_expr(instruction.call_function()).get_identifier();
        if(target != "reach_error" && target != "__VERIFIER_error")
          continue;
        auto location = instruction.source_location();
        location.set_property_class("unreach-call");
        location.set("builtin_function", target);
        location.set("c2btor_error_function", target);
        location.set_comment("unreachable call to " + id2string(target));
        auto assertion = goto_programt::make_assertion(false_exprt(), location);
        assertion.labels = instruction.labels;
        instruction = std::move(assertion);
      }
    goto_model.goto_functions.update();
  }

  if(options.get_bool_option("goto-btor2"))
  {
    lower_float_operations(goto_model);
    lower_heap_operations(goto_model);
  }

  if(options.get_bool_option("inline"))
  {
    log.status() << "Performing function call inlining (from main)"
                 << messaget::eom;
    goto_function_inline(goto_model, ID_main, log.get_message_handler());
  }

  // ignore default/user-specified initialization
  // of variables with static lifetime
  if(options.get_bool_option("nondet-static"))
  {
    log.status() << "Adding nondeterministic initialization "
                    "of static/global variables"
                 << messaget::eom;
    nondet_static(goto_model);
  }

  // add failed symbols
  // needs to be done before pointer analysis
  add_failed_symbols(goto_model.symbol_table);

  // remove skips such that trivial GOTOs are deleted and not considered
  // for coverage annotation:
  remove_skip(goto_model);

  // instrument cover goals
  if(options.is_set("cover"))
  {
    const auto cover_config = get_cover_config(
      options, goto_model.symbol_table, log.get_message_handler());
    if(instrument_cover_goals(
         cover_config, goto_model, log.get_message_handler()))
      return true;
  }

  // label the assertions
  // This must be done after adding assertions and
  // before using the argument of the "property" option.
  // Do not re-label after using the property slicer because
  // this would cause the property identifiers to change.
  if(options.get_bool_option("goto-btor2"))
    label_btor2_properties(goto_model);
  else
    label_properties(goto_model);

  // reachability slice?
  if(options.get_bool_option("reachability-slice-fb"))
  {
    log.status() << "Performing a forwards-backwards reachability slice"
                 << messaget::eom;
    if(options.is_set("property"))
    {
      reachability_slicer(
        goto_model,
        options.get_list_option("property"),
        true,
        log.get_message_handler());
    }
    else
      reachability_slicer(goto_model, true, log.get_message_handler());
  }

  if(options.get_bool_option("reachability-slice"))
  {
    log.status() << "Performing a reachability slice" << messaget::eom;
    if(options.is_set("property"))
    {
      reachability_slicer(
        goto_model,
        options.get_list_option("property"),
        log.get_message_handler());
    }
    else
      reachability_slicer(goto_model, log.get_message_handler());
  }

  // full slice?
  if(options.get_bool_option("full-slice"))
  {
    log.warning() << "**** WARNING: Experimental option --full-slice, "
                  << "analysis results may be unsound. See "
                  << "https://github.com/diffblue/cbmc/issues/260"
                  << messaget::eom;
    log.status() << "Performing a full slice" << messaget::eom;
    if(options.is_set("property"))
      property_slicer(
        goto_model,
        options.get_list_option("property"),
        log.get_message_handler());
    else
      full_slicer(goto_model, log.get_message_handler());
  }

  // remove any skips introduced since coverage instrumentation
  remove_skip(goto_model);

  return false;
}

/// Display the C2BTOR workflow while retaining upstream parser compatibility.
void cbmc_parse_optionst::help()
{
  // clang-format off
  std::cout << '\n' << banner_string("C2BTOR", C2BTOR_VERSION) << '\n';
  std::cout << help_formatter(
    "\n"
    "Usage:\n"
    " {bc2btor} {y--help} \t show this help\n"
    " {bc2btor} {y--version} / {y-v} \t show C2BTOR product version\n"
    " {bc2btor} {ufile.c} {y--goto-btor2 --inline} [options] \t convert C to BTOR2\n"
    "\n"
    "Model output:\n"
    " {y--goto-btor2} \t enable C2BTOR conversion\n"
    " {y--goto-btor2-out} {ufile} \t write BTOR2 (default: stdout)\n"
    " {y--goto-btor2-map-out} {ufile} \t optional PC/GotoIR/source map (witness replay only; not written by default)\n"
    " {y--inline} \t inline ordinary function calls from main\n"
    " Loops are encoded by PC transitions; BMC unwinding options are not supported.\n"
    "\n"
    "Memory and encoding:\n"
    " {y--memory} {uobject|global} \t memory organization (default: object)\n"
    " {y--array} {ubv|array|mixed} \t storage representation (default: bv)\n"
    " Selecting array or mixed enables the certified array pipeline below; bv uses state pruning only.\n"
    " {y--goto-btor2-no-array-optimizations} \t keep array stages at their historical opt-in defaults (ablation)\n"
    " {y--array-mixed-threshold-bits} {uN} \t mixed object threshold in bits (default: 2048; requires object memory)\n"
    " {y--goto-btor2-initialization} {ustrict|nondet} \t compatibility option (no-op); stable arbitrary initial bytes\n"
    " {y--goto-btor2-scalar-slice} {unone|dead|liveness} \t project unobservable scalar values and initializations (default: none)\n"
    " {y--goto-btor2-optimize-state} \t optimize before capacity planning and prune unobservable model states (default: on)\n"
    " {y--goto-btor2-no-optimize-state} \t disable state pruning for comparison\n"
    " {y--goto-btor2-logical-arrays} \t separate certified element-only arrays from byte object memory (default: on for array|mixed)\n"
    " {y--goto-btor2-scalar-blocks} \t merge scalar loop bodies and assertion-ending blocks; omit block-local scalar states (default: on; disable with --goto-btor2-no-scalar-blocks)\n"
    " {y--goto-btor2-array-blocks} \t merge certified logical-array accesses using block-local storage versions (default: on for array|mixed; requires logical arrays and scalar blocks)\n"
    " {y--goto-btor2-array-loop-summary} \t summarize certified complete constant/nondet fills and same-index copies; propagate uniform values and array equality (default: on for array|mixed with object memory)\n"
    " {y--goto-btor2-scalar-loop-summary} \t summarize certified finite empty loops and integer constant reductions; preserve counter exits (default: on for array|mixed)\n"
    " {y--goto-btor2-symbolic-heap} \t record typed allocation byte expressions and allocation-time size snapshots (default: on for array|mixed with object memory)\n"
    " {y--goto-btor2-symbolic-heap-arrays} \t use fixed-domain object-local Arrays for symbolic allocation capacities (default: on for array|mixed with object memory)\n"
    " {y--goto-btor2-symbolic-heap-wide-offsets} \t retain full machine-width offsets with hidden object tags; reject unsupported pointer serialization (default: on for array|mixed with object memory)\n"
    " {y--goto-btor2-symbolic-heap-bv-array-fallback} \t explicitly allow native Arrays for dynamic objects unrepresentable in pure BV (default: off; requires symbolic heap Arrays)\n"
    " {y--goto-btor2-symbolic-heap-compact} \t remove duplicate symbolic heap seeds; certify aligned uniform 64-bit cells or retain bytes (default: on for array|mixed with object memory)\n"
    " {y--goto-btor2-lbe} \t merge acyclic scalar instructions and branches (default: on; disable with --goto-btor2-no-lbe)\n"
    " {y--goto-btor2-slice-property} \t property-slice GotoIR (default: on; disable with --goto-btor2-no-slice-property; SAFE transfers, SAT needs replay)\n"
    " {y--memory-object-max-bytes} {uN} \t explicit per-object byte limit (default: automatic; exceeding rejects)\n"
    " {y--goto-btor2-heap-objects} {uK} \t storage limit; reject insufficient slots (default/0: infer)\n"
    "\n"
    "Properties and checks:\n"
    " All GOTO assertions and standard SV-COMP error calls become properties.\n"
    " {y--goto-btor2-merge-bads} \t OR selected source bads into one (default: on)\n"
    " {y--goto-btor2-no-merge-bads} \t emit a separate bad for each selected source assertion\n"
    " {y--goto-btor2-checks} \t explicitly instrument CBMC checks as source properties (once)\n"
    " BTOR2 conversion instruments nothing by default; only source ASSERTs become bads.\n"
    " {y--no-standard-checks --no-pointer-check --no-bounds-check --no-built-in-assertions} \t compatibility no-ops for BTOR2\n"
    " {y--bounds-check --pointer-check --div-by-zero-check --signed-overflow-check} \t select checks with --goto-btor2-checks\n"
    "\n"
    "C frontend and target:\n"
    " {y-I} {upath} \t include directory\n"
    " {y-D} {umacro} \t preprocessor definition\n"
    " {y--32 --64} \t choose target data model (not host executable width)\n"
    " {y--arch} {uname} \t target architecture\n"
    " {y--os} {uname} \t target operating system\n"
    " {y--little-endian --big-endian} \t target byte order\n"
    " {y--round-to-nearest --round-to-plus-inf --round-to-minus-inf --round-to-zero} \t initial rounding mode\n"
    " {y--verbosity} {uN} \t diagnostic level (default: 6)\n"
    "\n"
    "Witness: c2btor-verify program.c --property unreach-call.prp --data-model ILP32.\n"
    "Use a hash-bound map and BtorSim replay before CPAchecker confirmation.\n"
    "Only selected source properties generate bads. Unsupported representations fail conversion.\n"
    "Bounded absence,\n"
    "TIMEOUT and UNKNOWN are not C SAFE results. See README.md.\n"
    "\n"
    "Uses CBMC's C parser and GOTO-IR: https://github.com/diffblue/cbmc\n"
    "Thanks to Daniel Kroening, Edmund Clarke and the CBMC contributors.\n"
    "This product includes software developed by Daniel Kroening, Edmund Clarke,\n"
    "Computer Science Department, University of Oxford,\n"
    "Computer Science Department, Carnegie Mellon University. See LICENSES/.\n"
    "\n");
  // clang-format on
}
