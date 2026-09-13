-include local.mk
GPRBUILD ?= gprbuild
GNATPROVE ?= gnatprove
GNATFORMAT ?= gnatformat
JOBS ?= 4
.PHONY: all test test-contracts flow prove format
all:
	$(GPRBUILD) -P tools.gpr -j$(JOBS)
test: all
	bin/test_regex
	python3 tests/test_cli.py
	python3 tests/test_rg.py
test-contracts:
	$(GPRBUILD) -P tools.gpr -XSPARK_RE_BUILD=checks -j$(JOBS)
	bin/checks/test_regex
	SPARK_GREP=bin/checks/spark-grep python3 tests/test_cli.py
	SPARK_RG=bin/checks/spark-rg python3 tests/test_rg.py
flow:
	$(GNATPROVE) -P spark_re.gpr --mode=flow -j$(JOBS)
prove:
	$(GNATPROVE) -P spark_re.gpr --level=2 --timeout=20 --prover=cvc5,z3 --counterexamples=off -j$(JOBS)
format:
	$(GNATFORMAT) -P tools.gpr -U --charset utf-8
