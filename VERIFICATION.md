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

## Tree semantics and compiler fragment boundaries — 2026-09-11

The full validation sequence passed, with **all 556 checks proved**, zero
justified checks, and zero unproved checks:

| Category | Checks |
| --- | ---: |
| Data dependencies | 9 |
| Initialization | 31 |
| Runtime checks | 250 |
| Assertions | 74 |
| Functional contracts | 118 |
| Termination | 74 |

Parsing and tree compilation now have separate proved contracts. The parser
returns a structurally valid tree with backward child references and valid
finite repetition bounds. Tree compilation accepts that contract and keeps
resource failures separate from syntax errors. Successful recursive builds
preserve the existing program, create no accepting or dead instructions, and
have no outgoing fragment edges except to their supplied continuation.

The independent `Matches` span model covers every tree constructor, including
absolute anchors and nullable repetition. Its mutually recursive definitions
have proved termination. `Lemma_Empty_Repetition` and `Lemma_Nullable` prove
exact empty-span characterizations. The model and lemmas use `Ghost => Static`
and do not execute in either build mode.

This is progress toward compiler refinement, not a proof of tree-to-NFA
language equivalence or parser language refinement. `PROOF.md` retains both
open obligations and identifies the needed fragment-path composition and
nullable-loop arguments.

Validation uses `python3 scripts/validate.py` with the same toolchain and proof
settings as the simulator milestone. The Ada regressions additionally cover
mandatory empty repetitions, finite nullable repetitions, and absolute anchors
inside mandatory copies. The differential/CLI suite remains 1,198 checks over
290 patterns in both build modes.

The local receipt is `validation/20260911T213545Z/summary.json`, with command
logs in the same directory. It records successful release tests, contract-mode
tests, flow analysis, and proof. Its hashes record the code at that milestone;
the evidence paragraph was added after validation.

## Fragment paths and NFA acceptance — 2026-09-12

The full validation sequence passed, with **all 883 checks proved**, zero
justified checks, and zero unproved checks:

| Category | Checks |
| --- | ---: |
| Data dependencies | 9 |
| Initialization | 41 |
| Runtime checks | 417 |
| Assertions | 88 |
| Functional contracts | 224 |
| Termination | 104 |

The new stopping-path model has proved budget monotonicity, preservation under
changes outside the fragment, and composition/decomposition at a fragment's
continuation. Successful leaf compilation now has a structural contract with
a proved equivalence to tree span matching for empty nodes, byte sets, and
both anchors.

The path model is connected to the NFA simulator in both directions:
`Lemma_Path_Accepts` proves that a valid accepting path implies the appropriate
`Search` or `Full_Match` result. `Lemma_Accepts_Path` reconstructs an accepting
path from NFA acceptance, including its span and a representable budget bounded
by `Last * (State_Count + 1) + State_Count`. The proofs preserve absolute
anchors, allow epsilon cycles, and handle search restarts. All new semantic
models and lemmas are `Ghost => Static`.

Compound compiler language refinement and parser grammar refinement remain
open in `PROOF.md`. The compiler reports seven unused static lemma procedures;
GNATprove checks their bodies and contracts. The compiler refinement still
needs to apply these theorems to compound construction.

`python3 scripts/validate.py` passed release tests, executable-contract tests,
flow analysis, and proof with the established toolchain/settings. Both test
modes passed the Ada cases and **1,198 differential/CLI checks over 290 patterns**.
The local receipt and logs are in `validation/20260912T030526Z/`; source and test
hashes identify that milestone. This verification section was added afterward.

## Compound construction certificates — 2026-09-12

The initial `make prove` run reported **1,356 of 1,358 checks proved**.
Two preservation invariants in `Lemma_Shape_Preserve` timed out, in the
concatenation and repetition cases. The code already contained compound
construction certificates beyond the objectives recorded in `PROOF.md`.

The witness-search invariants now retain the negated existential form of
their loop guards: every visited cut has no joining middle state. This is
logically equivalent to the previous universal negation. The mandatory-copy
search uses the same form. No contracts were weakened and no assumptions or
proof suppressions were introduced.

With the established proof settings, **all 1,358 checks are now proved**,
with zero justified or unproved checks:

| Category | Checks |
| --- | ---: |
| Data dependencies | 9 |
| Initialization | 41 |
| Runtime checks | 657 |
| Assertions | 131 |
| Functional contracts | 380 |
| Termination | 140 |

Successful `Build` establishes `Compiled_Shape` for every tree constructor,
including mandatory copies, bounded optional copies and patched unbounded
loops. Frame lemmas preserve these certificates across changes outside their
code intervals. Successful `Compile_Tree` establishes a root certificate
ending at accepting state 1. Compound language equivalence and parser grammar
refinement remain open; `PROOF.md` now states the completed structural step
and the remaining semantic obligations.

`python3 scripts/validate.py` passed release tests, executable-contract tests,
flow analysis and proof. Both test modes passed the Ada cases and **1,198
differential/CLI checks over 290 patterns**. The receipt and command logs are
in `validation/20260912T080650Z/`. Source and test hashes match this proof pass;
this verification section was added afterward. Compiler warnings remain for
unused ghost lemmas, an unused formal parameter, and intentionally swapped
code arrays in symmetric frame proofs; GNATprove reports no warnings.

## Tree compiler soundness and completeness — 2026-09-12

The committed baseline (`7f29364`) proved all 1,358 checks. The compiler
refinement now proves **all 2,149 checks**, with zero justified or unproved
checks, using the same GNAT Pro 27/GNATprove toolchain and proof settings:

| Category | Checks |
| --- | ---: |
| Data dependencies | 9 |
| Initialization | 84 |
| Runtime checks | 1,109 |
| Assertions | 173 |
| Functional contracts | 591 |
| Termination | 183 |

For every structurally valid tree whose compilation succeeds, the executable
whole-match result equals the independent tree-span interpretation over the
whole input, and search equals that interpretation over some input span.
`Lemma_Compiler_Correct` proves these equivalences from the compiler's
construction certificate. `Compile_Tree_For_Text` applies the theorem to an
actual compiler call and retains explicit resource-failure outcomes.

The proof covers every constructor. It extracts child boundaries, derives
closed code intervals, decomposes accepting paths into tree matches, and
constructs paths from tree matches. Mandatory empty copies retain their lower
bound and anchor conditions. Empty unbounded iterations can be omitted in the
soundness argument because the remaining path matches the same span; the path
budget decreases even when no byte is consumed. The constructive argument
uses only advancing extra unbounded copies, as specified by `Repeated_Matches`.

Path budgets now use mathematical nonnegative integers instead of machine
integers. Their addition cannot overflow when composing witnesses, and all
budgets remain finite. The path/simulator bridge and its reverse witness bound
were reproved with this representation. Additional check counts include the
big-integer validity and nonnegativity checks. This arithmetic occurs only in
static ghost code. Undefined-symbol inspection of both compiled `regex.o`
builds found no big-integer or allocation-routine references.

`python3 scripts/validate.py` passed release tests, executable-contract tests,
flow analysis and proof. Both test modes passed the Ada cases and **1,198
differential/CLI checks over 290 patterns**. The final receipt and logs are in
`validation/20260912T082933Z/`; code, tests and proof-objective hashes match this
pass. This evidence section was added afterward. GNATprove reports no warnings,
assumptions or proof suppressions; ordinary compiler warnings still identify
unused ghost helpers and the existing symmetric frame calls.

The proof covers the default `Regex` instantiation. It closes the tree-to-NFA
language gap, but parser refinement against an independent pattern grammar
remains open in `PROOF.md`. Stack capacity and a machine-cost model remain
outside this evidence.
