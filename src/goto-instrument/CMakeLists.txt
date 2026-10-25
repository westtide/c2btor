# Library
file(GLOB_RECURSE sources "*.cpp" "*.h")
add_library(goto-instrument-lib ${sources})

generic_includes(goto-instrument-lib)

target_link_libraries(goto-instrument-lib
    ansi-c
    cpp
    linking
    big-int
    goto-programs
    goto-symex
    assembler
    pointer-analysis
    analyses
    langapi
    xml
    util
    json
    solvers
)

add_if_library(goto-instrument-lib glpk)
