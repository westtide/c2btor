default: test

test:
	@../test.pl -e -p -c "../../../src/cbmc/c2btor" -X smt-backend

tests.log: ../test.pl test

clean:
	find . -name '*.out' -execdir $(RM) '{}' \;
	find . -name '*.smt2' -execdir $(RM) '{}' \;
	$(RM) tests.log
