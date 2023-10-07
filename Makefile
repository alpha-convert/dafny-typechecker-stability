SOURCES := $(shell find . -name '*.dfy')

clean-test-results:
	rm -rf TestResults/*.csv TestResults/*.trx

restore-dafny:
	dotnet tool restore

NUM_ITERATIONS = 100

MEASURE_COMPLEXITY_ARGS = --iterations:$(NUM_ITERATIONS) --log-format csv 

$(SOURCES): restore-dafny clean-test-results
	-dotnet tool run dafny measure-complexity $(MEASURE_COMPLEXITY_ARGS) $@

stress : $(SOURCES)

clean:
	rm -rf build
	rm -rf TestResults/*


love:
	...

war:
	...