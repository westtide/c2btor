add_test_pl_tests(
    "perl ../timeout.pl 30 $<TARGET_FILE:c2btor> --incremental --magic-numbers"
)
