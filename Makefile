#  Optional, untracked, per-developer tool locations. The project states
#  which tools it needs and never where they live; a developer whose
#  environment offers several toolchains pins the choice here.
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
#  Assertions follow the build mode, so both the library and the vendored
#  CLI support crate must be switched over together.
CHECKS_VARS = -XSPARK_RE_BUILD=checks -XSPARK_CLI_BUILD=checks
test-contracts:
	$(GPRBUILD) -P tools.gpr $(CHECKS_VARS) -j$(JOBS)
	bin/checks/test_regex
	SPARK_GREP=bin/checks/spark-grep python3 tests/test_cli.py
	SPARK_RG=bin/checks/spark-rg python3 tests/test_rg.py
flow:
	$(GNATPROVE) -P spark_re.gpr --mode=flow -j$(JOBS)
prove:
	$(GNATPROVE) -P spark_re.gpr --level=4 --counterexamples=off -j$(JOBS)
#  Some sources hold UTF-8 literals, so the charset must be stated: the
#  formatter otherwise assumes iso-8859-1 and re-encodes them on every run.
format:
	$(GNATFORMAT) -P tools.gpr -U --charset utf-8
