# Verification evidence

## Silver milestone — 2026-09-11

Commands `make test`, `make test-contracts`, `make flow`, and `make prove`
completed successfully. GNATprove reported **all 173 checks proved**, with
zero justified or unproved checks:

| Category | Checks |
| --- | ---: |
| Data dependencies | 6 |
| Initialization | 29 |
| Runtime checks | 105 |
| Assertions | 9 |
| Functional contracts (parser bounds) | 6 |
| Termination | 18 |

The default `Regex` instantiation covers every library subprogram. This
includes recursive compilation termination (decreasing syntax-node index),
parser progress, and bounded simulation loops. There are no `Assume` pragmas,
proof suppressions, or library bodies excluded from SPARK. The generic itself
is analyzed through the default instance; this evidence does not establish
proof for every possible instantiation or available stack space on every target.

Release and assertion-enabled runs both passed the Ada library cases and
**1,154 differential/CLI checks**, covering 279 patterns with Python `re` and
GNU `grep -aE` in locale C. Parser/compiler language equivalence and the
simulator's path semantics are not functional proof claims at this milestone.

Toolchain: GNAT/GPRbuild Pro 27.0w (20260909), GCC 15.3.1 (20260910),
GNATprove development build `0.0w`, Why3 1.8.2+git, cvc5 1.3.2 and Z3 4.15.4.
The project records no machine-specific tool paths. Proof uses `--level=2`,
`--timeout=20`, `--prover=cvc5,z3`, `--counterexamples=off`, four jobs, with
warnings and unproved checks treated as errors.

Run `python3 scripts/validate.py` to repeat the full sequence and save command
statuses, source hashes, elapsed times, and logs under ignored `validation/`.
Original Silver logs are retained locally in `validation/silver/`.
