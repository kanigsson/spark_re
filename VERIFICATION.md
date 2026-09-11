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

## Selected Gold properties — 2026-09-11

Silver was committed first as `5f3d361`. The subsequent functional-proof pass
reports **all 300 checks proved**, zero justified or unproved:

| Category | Checks |
| --- | ---: |
| Data dependencies | 8 |
| Initialization | 30 |
| Runtime checks | 151 |
| Assertions | 44 |
| Functional contracts | 40 |
| Termination | 27 |

The new properties are:

- `Compile` returns a valid program exactly when its status is `Success`.
  The program invariant bounds every emitted instruction target by `Count`
  and requires a successful program's entry point to be live. Recursive
  compilation preserves this invariant even on capacity failure.
- Default/invalid programs reject every input. `State_Count` stays within the
  configured capacity.
- `Advance` has an exact existential postcondition: a destination in the live
  prefix (or sentinel zero) is selected iff an active consuming instruction
  accepts the byte and points to that destination. This covers both directions
  of the one-byte transition relation.
- `Closure` preserves all input seeds in the live prefix and excludes sentinel
  zero. The proved `Certified` invariant and exit assertion construct ghost
  predecessor/depth arrays: each reached nonseed has a reached predecessor
  connected by a permitted epsilon edge, with strictly smaller natural depth.
  This is a finite path certificate back to a seed, including the truth of
  start/end anchor conditions. `Bounded_Depth` bounds these depths by the
  current closure iteration; worklist references remain reached/live.

At that milestone these were selected component-level Gold properties, not a
full-language correctness theorem. Pattern/compiler equivalence, closure
completeness, and end-to-end search correctness were still open. Termination
was proved; a formal machine-cost model was not. The simulator proof below
closes the closure and NFA simulation gaps. Array initialization costs depend
on configured capacity, even when fewer states are compiled.

The toolchain and proof settings are unchanged from Silver. Final validation
uses `python3 scripts/validate.py`: release and executable-contract tests,
flow analysis, then proof, with per-command logs/statuses and source hashes.
The Ada tests additionally exercise every one of the 256 byte values through
escaped classes, negated classes, and dot. The differential/CLI suite remains
1,154 checks over 279 fixed/generated patterns in both modes.

## NFA simulator correctness — 2026-09-11

The full regex proof attempt establishes **all 438 checks proved**, with zero
justified or unproved checks, using the same toolchain and proof options:

| Category | Checks |
| --- | ---: |
| Data dependencies | 9 |
| Initialization | 30 |
| Runtime checks | 215 |
| Assertions | 63 |
| Functional contracts | 74 |
| Termination | 47 |

`Search` and `Full_Match` now have proved public postconditions equating their
results to `NFA_Accepts`. This ghost model uses an independently defined
epsilon-path relation and a recurrence over text offsets; it does not call
the executable simulator. The closure result is proved both sound and complete
and is the least epsilon-closed superset of its seeds, respecting absolute
anchors. `Run` maintains equality with the model at every boundary, including
search restarts and early acceptance.

The executable worklist changed from a linked stack to an append-only queue.
Proved cardinality and inverse-index invariants ensure capacity and show that
every reached state is processed before closure returns. Additional compiler
contracts prove exact instruction emission and preservation of all existing
instructions during recursive compilation, including failure paths.

**This is not a full regex-language correctness proof.** No proved relation
yet connects pattern syntax to the parser's tree or that tree's language to
the compiled NFA. Those obligations are missing semantic specifications and
proofs, not checks suppressed from the reported total. [PROOF.md](PROOF.md)
states the proved model and the remaining full-language theorem.

The recursive model, induction lemmas, worklist certificates and compiler
snapshots use SPARK's `Static` ghost level. GNATprove proves their contracts
and termination, but they are erased in both build modes. Ordinary executable
contracts remain checked by `make test-contracts`. No assumptions, imported
proof axioms, proof suppressions or SPARK exclusions were added.

Validation uses `python3 scripts/validate.py`: release tests, executable-contract
tests, flow analysis and proof. Both test modes pass the Ada cases and **1,198
differential/CLI checks over 290 patterns**. New regressions cover anchored
nullable cycles and worklists filled exactly to capacity. The script retains
logs, command statuses, source hashes and timings under ignored `validation/`.
The proof still covers the default instance; custom capacities, stack space
and a formal machine-cost model remain outside this evidence.
