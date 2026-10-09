default: tests.log

test:
	@../test.pl -c "../../../src/cbmc/c2btor --incremental"

tests.log: ../test.pl
	@../test.pl -c "../../../src/cbmc/c2btor --incremental"

clean:
	@$(RM) *.log
	@for dir in *; do $(RM) $$dir/*.out; done;
