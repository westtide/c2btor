default: tests.log

test:
	@../test.pl -e -p -c ../../../src/cbmc/c2btor

testfuture:
	@../test.pl -e -p -c ../../../src/cbmc/c2btor -CF

testall:
	@../test.pl -e -p -c ../../../src/cbmc/c2btor -CFTK

tests.log: ../test.pl
	@../test.pl -e -p -c ../../../src/cbmc/c2btor

clean:
	find . -name '*.out' -execdir $(RM) '{}' \;
	find . -name '*.gb' -execdir $(RM) '{}' \;
	$(RM) tests.log

