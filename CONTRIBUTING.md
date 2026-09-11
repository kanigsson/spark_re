# Contributing

Keep the regex kernel in `src/` free of allocation, I/O, and global state.
Keep executable adapters and shared I/O outside the SPARK proof boundary.
Run `make test`, `make test-contracts`, `make flow`, and `make prove` with a
matching toolchain. Do not suppress unproved checks to obtain a passing run.

This project is Apache-2.0. Do not copy implementation code from GPL-only
projects such as gsh. Any downstream licensing assessment is separate from
this implementation. Keep library/API dependencies independent of the CLI.
