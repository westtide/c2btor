if("${CMAKE_CXX_COMPILER_ID}" STREQUAL "MSVC")
  set(gcc_only -X gcc-only)
else()
  set(gcc_only "")
endif()

add_test_pl_tests(
    "$<TARGET_FILE:c2btor> --validate-goto-model --validate-ssa-equation" ${gcc_only}
)
