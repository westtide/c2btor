# Library
file(GLOB_RECURSE sources "*.cpp" "*.h")
list(REMOVE_ITEM sources
    ${CMAKE_CURRENT_SOURCE_DIR}/cbmc_main.cpp
)
add_library(cbmc-lib ${sources})

generic_includes(cbmc-lib)

target_link_libraries(cbmc-lib
    analyses
    ansi-c
    assembler
    big-int
    cpp
    goto-btor2
    goto-checker
    goto-instrument-lib
    goto-programs
    goto-symex
    json
    json-symtab-language
    langapi
    linking
    pointer-analysis
    solvers
    statement-list
    util
    xml
)

add_if_library(cbmc-lib bv_refinement)

# Executable
add_executable(c2btor cbmc_main.cpp)
if(CMAKE_SYSTEM_NAME STREQUAL "Linux")
# There is a cyclic dependency between analyses and ansi-c, which the
# Makefile-based build system resolves by using --start-group, --end-group.
# CMake lacks direct support (cf.
# https://gitlab.kitware.com/cmake/cmake/-/issues/21511), so we ensure all
# object files from libanalyses.a remain present.
target_link_libraries(c2btor
  cbmc-lib
  -Wl,--whole-archive -Wl,${CMAKE_BINARY_DIR}/lib/libanalyses.a -Wl,--no-whole-archive
)
else()
target_link_libraries(c2btor cbmc-lib)
endif()
install(TARGETS c2btor DESTINATION ${CMAKE_INSTALL_BINDIR} COMPONENT c2btor)

# Product-specific shell completion.
if(NOT WIN32)
  find_program(BASH_PROGRAM bash REQUIRED)
  set(c2btor_completion "${CMAKE_CURRENT_BINARY_DIR}/c2btor.sh")
  add_custom_command(OUTPUT "${c2btor_completion}"
    COMMAND "${BASH_PROGRAM}" "${CBMC_ROOT_DIR}/scripts/bash-autocomplete/extract_switches.sh"
      "${CMAKE_CXX_COMPILER}" c2btor "${CMAKE_CURRENT_BINARY_DIR}"
    DEPENDS
      "${CMAKE_CURRENT_SOURCE_DIR}/cbmc_parse_options.h"
      "${CBMC_ROOT_DIR}/scripts/bash-autocomplete/extract_switches.sh"
      "${CBMC_ROOT_DIR}/scripts/bash-autocomplete/cbmc.sh.template"
    VERBATIM)
  add_custom_target(c2btor-completion ALL DEPENDS "${c2btor_completion}")
  add_dependencies(c2btor c2btor-completion)
  install(FILES "${c2btor_completion}"
    DESTINATION etc/bash_completion.d RENAME c2btor COMPONENT c2btor)
endif()

install(FILES ${CMAKE_SOURCE_DIR}/LICENSE ${CMAKE_SOURCE_DIR}/LICENSE.c2btor
  ${CMAKE_SOURCE_DIR}/README.md ${CMAKE_SOURCE_DIR}/README.zh-CN.md
  DESTINATION ${CMAKE_INSTALL_DATADIR}/doc/c2btor COMPONENT c2btor)

install(FILES
  ${CMAKE_SOURCE_DIR}/scripts/c2btor_witness.py
  ${CMAKE_SOURCE_DIR}/scripts/c2btor_solver.py
  ${CMAKE_SOURCE_DIR}/scripts/c2btor_model_contract.py
  ${CMAKE_SOURCE_DIR}/scripts/run_witness_svcomp.py
  DESTINATION ${CMAKE_INSTALL_DATADIR}/c2btor/scripts COMPONENT c2btor)
