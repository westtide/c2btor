# SPDX-License-Identifier: BSD-4-Clause
file(GLOB_RECURSE sources CONFIGURE_DEPENDS
  "goto-btor2/*.cpp" "ansi-c/*.cpp" "goto-programs/*.cpp")
add_subdirectory(testing-utils)
add_executable(c2btor-unit unit_tests.cpp ${sources})
set_target_properties(c2btor-unit PROPERTIES
  RUNTIME_OUTPUT_DIRECTORY "${CMAKE_CURRENT_BINARY_DIR}")
target_include_directories(c2btor-unit PRIVATE
  ${CBMC_BINARY_DIR} ${CBMC_SOURCE_DIR}/src ${CMAKE_CURRENT_SOURCE_DIR})
target_link_libraries(c2btor-unit PRIVATE cbmc-lib testing-utils)
add_test(NAME c2btor-unit COMMAND c2btor-unit)
set_tests_properties(c2btor-unit PROPERTIES
  WORKING_DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}" LABELS "C2BTOR;CORE")

find_package(Python3 3.10 REQUIRED COMPONENTS Interpreter)
add_test(NAME c2btor-python COMMAND "${Python3_EXECUTABLE}"
  -m unittest discover -s scripts/tests -v)
add_test(NAME c2btor-witness COMMAND "${Python3_EXECUTABLE}"
  -m unittest discover -s test/c2btor_optimizations -p test_witness_v2.py -v)
set_tests_properties(c2btor-python c2btor-witness PROPERTIES
  WORKING_DIRECTORY "${CBMC_SOURCE_DIR}" LABELS "C2BTOR;CORE"
  ENVIRONMENT "C2BTOR_BINARY=$<TARGET_FILE:c2btor>" TIMEOUT 180)
