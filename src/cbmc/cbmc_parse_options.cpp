/*******************************************************************\

Module: CBMC Command Line Option Processing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// CBMC Command Line Option Processing

#include "cbmc_parse_options.h"

#include <util/config.h>
#include <util/exit_codes.h>
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
#include <goto-programs/remove_unused_functions.h>
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
#include <goto-instrument/unwind.h>
#include <goto-programs/unwindset.h>
#include <goto-symex/path_storage.h>
#include <langapi/language.h>
#include <langapi/mode.h>
#include <pointer-analysis/add_failed_symbols.h>

#include "c_test_input_generator.h"
#include "btor2_demo.h"

#include <goto-btor2/goto_btor2.h>
#include <limits>
#include <stdexcept>
#include <goto-btor2/simplify_callback_targets.h>
#include <goto-btor2/lower_array_operations.h>
#include <goto-btor2/lower_heap_operations.h>
#include <goto-btor2/lower_float_operations.h>
#include <goto-btor2/goto_btor2_unroll.h>
#include <xmllang/graphml.h>

#include <cstdlib> // exit()
#include <fstream> // IWYU pragma: keep
#include <iostream>
#include <memory>

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
    options, !cmdline.isset("no-standard-checks"));

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
  if(cmdline.isset("goto-btor2"))
    options.set_option(
      "goto-btor2-error-function",
      cmdline.get_value("goto-btor2-error-function"));

  if(cmdline.isset("goto-btor2"))
  {
    options.set_option(
      "goto-btor2-no-heap-guards", cmdline.isset("goto-btor2-no-heap-guards"));
    options.set_option(
      "goto-btor2-merge-properties",
      cmdline.isset("goto-btor2-merge-properties"));
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

  if(
    (cmdline.isset("array") || cmdline.isset("array-bv-max-object-bytes") ||
     cmdline.isset("memory") || cmdline.isset("memory-object-max-bytes")) &&
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
  if(array_mode != "bv" && array_mode != "array")
  {
    log.error() << "--array requires bv or array" << messaget::eom;
    return CPROVER_EXIT_USAGE_ERROR;
  }
  array_encoding.bitvectors = array_mode == "bv";
  if(cmdline.isset("array-bv-max-object-bytes"))
  {
    const auto value = cmdline.get_value("array-bv-max-object-bytes");
    try
    {
      std::size_t end = 0;
      const auto parsed = std::stoull(value, &end);
      if(
        !array_encoding.bitvectors || value.empty() || value[0] == '-' ||
        end != value.size() || parsed == 0 ||
        parsed > std::numeric_limits<std::size_t>::max())
        throw std::invalid_argument("BV object capacity");
      array_encoding.max_object_bytes = static_cast<std::size_t>(parsed);
    }
    catch(const std::exception &)
    {
      log.error() << "--array-bv-max-object-bytes requires --array bv and "
                     "a positive integer"
                  << messaget::eom;
      return CPROVER_EXIT_USAGE_ERROR;
    }
  }

  if(cmdline.isset("memory-object-max-bytes"))
  {
    const auto value = cmdline.get_value("memory-object-max-bytes");
    try
    {
      std::size_t end = 0;
      const auto parsed = std::stoull(value, &end);
      if(
        !array_encoding.object_memory || value.empty() || value[0] == '-' ||
        end != value.size() || parsed == 0 ||
        parsed > std::numeric_limits<std::size_t>::max() ||
        (cmdline.isset("array-bv-max-object-bytes") &&
         parsed != *array_encoding.max_object_bytes))
        throw std::invalid_argument("object capacity");
      array_encoding.max_object_bytes = static_cast<std::size_t>(parsed);
    }
    catch(const std::exception &)
    {
      log.error() << "--memory-object-max-bytes requires --memory object and "
                     "a positive integer; capacity options must agree"
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

  log.status() << "C2BTOR version " << C2BTOR_VERSION
               << " (CBMC frontend " << CBMC_VERSION << ") "
               << config.this_architecture() << " "
               << config.this_operating_system() << messaget::eom;

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

  if(cmdline.isset("btor2-demo"))
  {
    std::ofstream out_file;
    std::ostream *out = &std::cout;
    if(cmdline.isset("btor2-out"))
    {
      out_file.open(cmdline.get_value("btor2-out"));
      if(!out_file)
      {
        log.error() << "failed to open --btor2-out file" << messaget::eom;
        return CPROVER_EXIT_INCORRECT_TASK;
      }
      out = &out_file;
    }

    if(write_btor2_demo(goto_model, *out, log))
      return CPROVER_EXIT_INTERNAL_ERROR;
    return CPROVER_EXIT_SUCCESS;
  }

  // Full goto-program to BTOR2 conversion
  if(cmdline.isset("goto-btor2"))
  {
    btor2_property_optionst properties;
    properties.error_function = cmdline.get_value("goto-btor2-error-function");
    properties.reach_only = cmdline.isset("goto-btor2-reach-only");
    properties.merge = cmdline.isset("goto-btor2-merge-bads") ||
                       cmdline.isset("goto-btor2-merge-properties");
    properties.no_heap_guards = cmdline.isset("goto-btor2-no-heap-guards");
    if(properties.reach_only && properties.error_function.empty())
    {
      log.error() << "--goto-btor2-reach-only requires "
                    "--goto-btor2-error-function NAME" << messaget::eom;
      return CPROVER_EXIT_USAGE_ERROR;
    }
    auto main = goto_model.goto_functions.function_map.find(ID_main);
    if(
      main != goto_model.goto_functions.function_map.end() &&
      !cmdline.isset("nondet-static"))
      simplify_callback_targets(
        main->second.body, goto_model.symbol_table, log,
        &properties.unreachable_assertions);
    if(main != goto_model.goto_functions.function_map.end())
      lower_array_operations(
        main->second.body, goto_model.symbol_table, log,
        array_encoding.object_memory && array_encoding.bitvectors &&
        config.ansi_c.endianness == configt::ansi_ct::endiannesst::IS_LITTLE_ENDIAN);
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

    if(cmdline.isset("goto-btor2-checks"))
    {
      // Apply goto-check instrumentation (bounds-check, div-by-zero, etc.) before
      // converting to BTOR2 so that these checks become BTOR2 "bad" properties.
      //
      // Note: the BTOR2 converter does not support all C features (e.g. complex
      // pointer/heap modelling). Users should enable only checks they intend to
      // model in BTOR2.
      goto_check_c(options, goto_model, ui_message_handler);
    }

    // Give each assertion a stable property id before lowering it to a BTOR2
    // `bad` property. This keeps multiple bad states distinguishable even when
    // they originate from goto-check instrumentation.
    label_properties(goto_model);

    // When --unwind (or --unwindset) is given together with --goto-btor2,
    // apply goto-level loop unwinding BEFORE btor2 conversion. Each copied
    // allocation receives its own identity. Preserve unwinding assertions:
    // silently cutting a loop can produce both missing and spurious paths.
    // An unwind failure means the bound is insufficient, not a C violation.
    if(
      cmdline.isset("unwind") || cmdline.isset("unwindset") ||
      cmdline.isset("unwindset-file"))
    {
      unwindsett unwindset;
      if(cmdline.isset("unwind"))
        unwindset.parse_unwind(cmdline.get_value("unwind"));
      if(cmdline.isset("unwindset"))
        unwindset.parse_unwindset(
          cmdline.get_comma_separated_values("unwindset"),
          goto_model,
          ui_message_handler);
      if(cmdline.isset("unwindset-file"))
        unwindset.parse_unwindset_file(
          cmdline.get_value("unwindset-file"),
          goto_model,
          ui_message_handler);
      goto_unwindt goto_unwind;
      goto_unwind(
        goto_model,
        unwindset,
        goto_unwindt::unwind_strategyt::ASSERT_ASSUME);
      goto_model.goto_functions.update();
      log.status() << "Applied goto-level loop unwinding before BTOR2 conversion"
                   << messaget::eom;
    }

    if(cmdline.isset("goto-btor2-unroll"))
    {
      // Expand only counted allocation loops with a checked finite bound.
      // Remaining repeated allocation sites are rejected by the converter.
      unroll_malloc_counted_loops(goto_model, log);
    }

    label_properties(goto_model); // include newly introduced unwind properties

    std::ofstream source_map;
    if(cmdline.isset("goto-btor2-map-out"))
    {
      if(cmdline.get_value("goto-btor2-map-out") ==
         cmdline.get_value("goto-btor2-out"))
      {
        log.error() << "BTOR2 model and source map need distinct paths"
                    << messaget::eom;
        return CPROVER_EXIT_INCORRECT_TASK;
      }
      source_map.open(cmdline.get_value("goto-btor2-map-out"));
      if(!source_map)
      {
        log.error() << "failed to open --goto-btor2-map-out file"
                    << messaget::eom;
        return CPROVER_EXIT_INCORRECT_TASK;
      }
    }
    unsigned heap_objects = 32;
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
        properties))
      return CPROVER_EXIT_INTERNAL_ERROR;
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

  // show it?
  if(
    cmdline.isset("show-goto-functions") ||
    cmdline.isset("list-goto-functions"))
  {
    show_goto_functions(
      goto_model, ui_message_handler, cmdline.isset("list-goto-functions"));
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

  const auto &error_function =
    options.get_option("goto-btor2-error-function");
  if(!error_function.empty())
  {
    const auto *target = goto_model.symbol_table.lookup(error_function);
    if(target == nullptr || target->type.id() != ID_code)
    {
      log.error() << "Unknown --goto-btor2-error-function: " << error_function
                  << messaget::eom;
      return true;
    }
    // An unreach-call property is violated at the call site, not at an
    // assertion inside the callee. Preserve that location before inlining.
    for(auto &function : goto_model.goto_functions.function_map)
      for(auto &instruction : function.second.body.instructions)
        if(instruction.is_function_call() &&
           instruction.call_function().id() == ID_symbol &&
           to_symbol_expr(instruction.call_function()).get_identifier() ==
             error_function)
        {
          auto location = instruction.source_location();
          location.set_property_class("unreach-call");
          location.set_comment("unreachable call to " + error_function);
          auto assertion =
            goto_programt::make_assertion(false_exprt(), location);
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

  if(options.get_bool_option("drop-unused-functions"))
  {
    // Entry point will have been set before and function pointers removed
    log.status() << "Removing unused functions" << messaget::eom;
    remove_unused_functions(goto_model, log.get_message_handler());
  }

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
    " {y--goto-btor2-map-out} {ufile} \t write PC/GotoIR/source map and model metadata\n"
    " {y--inline} \t inline ordinary function calls from main\n"
    " {y--show-goto-functions} \t inspect the processed GotoIR\n"
    "\n"
    "Memory and encoding:\n"
    " {y--memory} {uobject|global} \t memory organization (default: object)\n"
    " {y--array} {ubv|array} \t storage representation (default: bv)\n"
    " {y--memory-object-max-bytes} {uN} \t explicit runtime capacity (default: automatic)\n"
    " {y--array-bv-max-object-bytes} {uN} \t same capacity limit for BV storage\n"
    " {y--goto-btor2-heap-objects} {uK} \t total successful allocations (default: 32)\n"
    " {y--malloc-may-fail --malloc-fail-null} \t enable NULL allocation failures\n"
    "\n"
    "Properties and checks:\n"
    " {y--goto-btor2-error-function} {uname} \t mark unreach-call before inlining\n"
    " {y--goto-btor2-reach-only} \t select that error function's source properties\n"
    " {y--goto-btor2-merge-bads} \t OR selected source bads (alias: --goto-btor2-merge-properties)\n"
    " {y--goto-btor2-no-heap-guards} \t hide auxiliary bads; preserve proof obligations and halting\n"
    " {y--goto-btor2-checks} \t instrument selected CBMC checks before conversion\n"
    " {y--no-standard-checks} \t disable default CBMC instrumentation\n"
    " {y--no-pointer-check --no-bounds-check --no-built-in-assertions} \t source-property workflow\n"
    " {y--bounds-check --pointer-check --div-by-zero-check --signed-overflow-check} \t select checks\n"
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
    "Witness: scripts/c2btor_witness.py export / translate / validate.\n"
    "Use a hash-bound map and BtorSim replay before CPAchecker confirmation.\n"
    "UNSAT requires all selected properties and model obligations; bounded absence,\n"
    "TIMEOUT and UNKNOWN are not C SAFE results. See README.md for witness commands.\n"
    "\n"
    "Based on CBMC: https://github.com/diffblue/cbmc\n"
    "CBMC documentation: https://diffblue.github.io/cbmc/\n"
    "Thanks to Daniel Kroening, Edmund Clarke and the CBMC contributors.\n"
    "This product includes software developed by Daniel Kroening, Edmund Clarke,\n"
    "Computer Science Department, University of Oxford,\n"
    "Computer Science Department, Carnegie Mellon University. See LICENSE.\n"
    "\n");
  // clang-format on
}
