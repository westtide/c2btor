if(NOT WIN32)
add_test_pl_tests(
    "$<TARGET_FILE:c2btor>"
)
else()
add_test_pl_profile(
    "cbmc-library"
    "$<TARGET_FILE:c2btor>"
    "-C;-X;unix;-X;gcc-only"
    "CORE"
)
endif()
