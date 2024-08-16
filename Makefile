# Set this to 'nil' or 't' to manage verbosity
ERT_QUIET := nil

# Set this to
# 'ert-run-tests-batch-and-exit' or
# 'ert-summarize-tests-batch-and-exit'
ERT_TEST_FORM := (ert-run-tests-batch-and-exit)

# All test suites are assumed to be follow 'foo-tests.el' pattern
test_suites := $(wildcard *-tests.el)

.PHONY: all tests clean

all: tests
clean: rm -rf logs

# All outputs from a test run are logged in a file such as
#   logs/2024-09-10__23-12-50.log
# the pattern is YYYY-MM-DD__HH-MM-SS.log
tests: $(test_suites) | logs
	@echo Test suites found: $(test_suites)
	@emacs \
	  --batch -Q \
	  -l ert \
	  $$(\
	  for test in $(test_suites); do \
	    echo -l $$test; \
	  done) \
	  --eval "(let ((ert-quiet $(ERT_QUIET))) \
	            $(ERT_TEST_FORM))" \
	|& tee logs/$$(date +%Y-%m-%d__%H-%M-%S.log)

logs:
	mkdir logs
