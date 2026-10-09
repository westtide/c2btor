# For goto-inspect, we are not building a library - only a binary.

file(GLOB_RECURSE sources "*.cpp" "*.h")

add_executable(goto-inspect ${sources})

generic_includes(goto-inspect)

target_link_libraries(goto-inspect
  util
  goto-programs
)

install(TARGETS goto-inspect DESTINATION ${CMAKE_INSTALL_BINDIR})
