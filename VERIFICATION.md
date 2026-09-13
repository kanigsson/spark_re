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

## Lexical refinement and parser grammar soundness — 2026-09-12

The committed baseline (`6863971`) proved all 2,149 checks. This pass proves
**all 2,858 checks**, with zero justified or unproved checks, using the same
GNAT Pro 27/GNATprove toolchain and proof options:

| Category | Checks |
| --- | ---: |
| Data dependencies | 9 |
| Initialization | 104 |
| Runtime checks | 1,388 |
| Assertions | 233 |
| Functional contracts | 885 |
| Termination | 239 |

The lexical scanners prove acceptance, rejection, endpoints and exact token
contents against independent byte-span definitions. These cover decimal
bounds and overflow, ranges and class negation, escaped bytes, anchors, dot,
and every repetition form. The expression grammar separately specifies
precedence, empty terms/alternatives, grouping and quantifier attachment.
Successful `Parse` now proves that its root derives the complete pattern.
Frame and allocation-preservation lemmas connect the iterative parser to
that grammar without calling the parser from the model.

`Compile_With_Tree` is the executable parse/compile operation shared by public
`Compile` and the new `Compile_Pattern_For_Text` proof. For an arbitrary text
and whole/search mode, the latter proves that successful compilation returns
a grammar-derived tree whose span semantics agree with both NFA acceptance
and executable matching. This remains a theorem with an explicit derived-tree
witness: parser completeness, structural syntax rejection, and a pattern-only
denotation independent of the chosen derivation remain open in `PROOF.md`.

`python3 scripts/validate.py` passed release tests, executable-contract tests,
flow analysis and proof. Both test modes passed the expanded Ada cases and
**1,198 differential/CLI checks over 290 patterns**. New Ada cases exercise
leading zeros and oversized bounds, overlapping/negated ranges, all byte
values in a range, malformed escapes/classes/bounds, high string indices,
empty alternatives and nested groups, and parser frame/node limits.

The receipt and command logs are in `validation/20260912T223952Z/`. All recorded
file hashes matched after validation; only this evidence section was added
afterward. GNATprove analyzed all 154 subprograms/packages in the default
`Regex` instance, with no warnings, assumptions or proof suppressions.
Inspection of release and checks `regex.o` files found no new lexical/grammar
model symbols or big-integer/allocation-routine references. Static ghost spans,
models, snapshots and lemmas do not execute in either build mode.

The evidence covers the default instantiation. Custom capacities need their
own proof run; available stack space and exact resource sufficiency remain
outside this theorem.

## Layer separation — 2026-09-13

The committed baseline (`f3fb4cf`) proved all 2,858 checks from a single
6,584-line package body. That body is now split into four units — a dependency-
free `Spark_Re_Common`, the generic `Spark_Re_Trees`, and its generic children
`Spark_Re_Trees.Parsing` and `Spark_Re_Trees.Matching` — with `Spark_Re`
reduced to a 124-line facade. The full validation sequence passed, with **all
2,879 checks proved**, zero justified and zero unproved:

| Category | Checks |
| --- | ---: |
| Data dependencies | 17 |
| Initialization | 104 |
| Runtime checks | 1,387 |
| Assertions | 233 |
| Functional contracts | 890 |
| Termination | 248 |

The parser and the matcher now share only the syntax tree and neither withs
the other, so each layer's obligations are discharged on its own. The split is
transcription only: diffing the new bodies against the baseline's line ranges
shows the parser text identical and the compiler/simulator text identical apart
from two blank lines. No proof body, loop invariant or assertion was edited;
the only relocations are contracts that were in-body pragmas and are now unit
interfaces. The added
checks come from contracts that were previously in-body pragmas and are now
unit interfaces, from the `Program` wrapper in the facade, and from the two
new opaque certificates `Grammar` and `Tree_Compiled`.

Two interface changes accompany the split. `Compile_Status` and `Byte_Set` now
live in `Spark_Re_Common`; `Spark_Re` re-exports the status type as a subtype
with renamed literals, so client code is unaffected. `Program` inside
`Spark_Re_Trees.Matching` carries a `Default_Initial_Condition`, which is what
lets the facade return a rejecting program on a compile failure without seeing
the instruction representation.

**Proof settings changed.** The prover list is now `cvc5,z3,altergo`; level,
timeout and job count are unchanged. Five quantified goals — four witness
searches in the compiler frame and parts lemmas, one decimal-bound
precondition in the scanner — reach the 20-second limit for cvc5 and Z3 once
those lemmas are analyzed as their own unit, and did not recover at
`--timeout=120` or `--level=3`. Alt-Ergo discharges them at the standard
settings; it carries 1% of assertions and under 1% of functional contracts,
and nothing else. Alt-Ergo ships with SPARK and adds no axioms. Reformulating
the four witness searches around named cut predicates was tried first and
relocated the difficulty rather than removing it, so the proof text was left
identical to the baseline instead.

`python3 scripts/validate.py` passed release tests, executable-contract tests,
flow analysis and proof. Both test modes passed the Ada cases and **1,198
differential/CLI checks over 290 patterns**. The receipt and command logs are
in `validation/20260913T015050Z/`; proof took 80 seconds. Source hashes there
record the code at that pass; the two documentation sections were written
afterward. Flow analysis reports
206 checks across 6 units. Compiler warnings remain for unused ghost lemmas, an
unused formal parameter, and the intentionally swapped code arrays in symmetric
frame proofs; GNATprove reports no warnings, assumptions or proof suppressions.

Parser completeness, structural syntax rejection and a pattern-only denotation
remain open, and now live entirely inside `Spark_Re_Trees.Parsing`.

## Proof-context pruning — 2026-09-13

This pass supersedes the prover-list change recorded above. The five marginal
goals are now closed by pruning proof context instead, so **the prover list
returns to `cvc5,z3`**; level, timeout and job count are unchanged throughout.
A cleaned, forced run (`gnatprove --clean`, then `-f`) proves **all 2,913
checks**, with zero justified and zero unproved:

| Category | Checks |
| --- | ---: |
| Data dependencies | 17 |
| Initialization | 104 |
| Runtime checks | 1,400 |
| Assertions | 234 |
| Functional contracts | 907 |
| Termination | 251 |

Alt-Ergo appears nowhere in the prover breakdown.

The witness searches over compiled code intervals carry the shape certificates
without ever inspecting them; only their quantifier structure matters, and the
witnesses come from `Reveal_Shape`'s postcondition and the frame and join
lemmas' contracts. Hiding the recursive `Compiled_Shape`, `Copies_Shape`,
`Optional_Shape` and `Tail_Shape` bodies in those entities keeps the nested
existentials from being re-instantiated under each enclosing universal
invariant. Because hiding is decided per verified entity, `Lemma_Shape_Preserve`
was split into `Lemma_Concat_Preserve`, `Lemma_Alt_Preserve` and
`Lemma_Repeat_Preserve` over a dispatch: the two searches prune, while the leaf
and alternation cases still unfold their certificates. The mutual-recursion
variants were renumbered to give the three case lemmas a slot below the preserve
family, which in turn moved below the frame family; no variant component changed
meaning. `Lemma_Repeat_Join` prunes the child certificates and names the outer
cut witness explicitly. `Bounds_Valid` hides `Decimal_Digits`, whose digit spans
`Numeral_End`'s postcondition already certifies. `Numeral_End` was already
hidden by default before this pass.

No contract was weakened and nothing was assumed: these annotations remove
definitions from the proof context, they do not add facts to it. The reported
total rises from 2,879 to 2,913 because the three case lemmas carry their own
contracts.

Proof is also substantially faster. On a warm cache `make prove` takes 48
seconds, against 80 seconds for the split with Alt-Ergo and 99 seconds for the
single-unit baseline. A fully cold, cleaned, forced run takes 3 minutes 10.

An earlier warm run of this configuration appeared to prove everything while
two checks in fact depended on cached Alt-Ergo results; the figures above come
from a cleaned forced run, which is how this configuration should be checked.

`python3 scripts/validate.py` passed release tests, executable-contract tests,
flow analysis and proof. Both test modes passed the Ada cases and **1,198
differential/CLI checks over 290 patterns**. The receipt and command logs are in
`validation/20260913T024145Z/`; source hashes there record the code at that
pass, and this section was written afterward.

## Parser completeness and structural syntax rejection — 2026-09-13

From baseline `7dc6ca7` (2,913 checks), this pass proves **all 3,076 checks**,
with zero justified and zero unproved checks. It uses the same GNAT Pro 27
compiler, local GNATprove, and `--level=2 --timeout=20 --prover=cvc5,z3
--counterexamples=off -j4` settings.

| Category | Checks |
| --- | ---: |
| Data dependencies | 17 |
| Initialization | 107 |
| Runtime checks | 1,460 |
| Assertions | 252 |
| Functional contracts | 970 |
| Termination | 270 |

`Lemma_Grammar_Continuation` proves that the independent expression grammar
implies byte-only syntax validity. The parser loop preserves that validity
through every token and structural transition. `Parse_Complete` applies the
result to an actual parse of any supplied complete grammar derivation:
`Syntax_Error` is impossible; `Success`, `Node_Limit`, and `Pattern_Too_Long`
remain possible. The successful result still derives the complete pattern.
Thus syntax rejection excludes every complete derivation in the modeled tree
type. No resource-sufficiency or derivation-independent matching theorem is
claimed; the latter remains open in `PROOF.md`.

All new semantic functions, lemmas, contracts, and loop certificates are static
ghost code. Executable parsing is unchanged. No assumptions, proof suppressions,
or weakened contracts were introduced. Inspection of release and checks
`regex.o` files found no new continuation-model/theorem symbols or references
to allocation or big-integer routines.

`python3 scripts/validate.py` passed release tests, executable-contract tests,
flow analysis (214 checks), and proof. Both test modes passed the Ada cases and
**1,198 differential/CLI checks over 290 patterns**. GNATprove reports no
warnings; the existing ordinary compiler warnings remain in the matching
layer and facade.

The receipt and command logs are in `validation/20260913T032302Z/`; proof took
62.748 seconds. All recorded source hashes matched after validation. Only this
evidence section was added afterward. The proof covers the default `Regex`
instantiation; custom capacities require their own proof run.

## Derivation-independent matching — 2026-09-13

From baseline `0c29779` (3,076 checks), **all 3,664 checks are proved**, with
zero justified and zero unproved checks. The GNAT Pro 27 compiler, local
GNATprove, and `--level=2 --timeout=20 --prover=cvc5,z3 --counterexamples=off
-j4` settings are unchanged. A forced `-f` run also passed all 3,664 checks.

| Category | Checks |
| --- | ---: |
| Data dependencies | 18 |
| Initialization | 113 |
| Runtime checks | 1,666 |
| Assertions | 301 |
| Functional contracts | 1,242 |
| Termination | 324 |

`Lemma_Grammar_Matches` proves that every complete grammar derivation agrees
with the byte-only `Pattern_Matches` denotation on every supplied text span.
`Lemma_Derivation_Independent` equates any two such derivations. The proof
covers different node allocations and tree shapes, including an extra empty
left term, grouping, classes, escapes, absolute anchors, and nullable bounded
or unbounded repetition. The model neither constructs trees nor calls the
parser, compiler, or executable scanners.

The public `Compile_For_Text` theorem composes this result with the compiler
proof: on success, NFA acceptance and executable whole/search matching equal
`Pattern_Accepts`. Its contract has no tree witness. This closes the remaining
matching-language gap. Resource sufficiency and stack capacity remain outside
the theorem; custom instantiations require their own proof run.

All additions are static ghost models, lemmas, and contracts. Executable
parsing, compilation, and matching are unchanged. There are no assumptions,
proof suppressions, or weakened contracts. `Lemma_Grammar_Accepts` hides the
two span predicates' bodies and uses their proved equality to lift the result
to existential search acceptance. Both predicates remain independently proved.

`python3 scripts/validate.py` passed release tests, executable-contract tests,
flow analysis (234 checks), and proof. Both test modes passed the Ada cases and
**1,198 differential/CLI checks over 290 patterns**. Flow and proof reported no
warnings; the existing ordinary compiler warnings remain in the matching unit.
Inspection of release and checks `regex.o` files found no new model/theorem
symbols or allocation/big-integer references.

The final receipt, command logs, proof summary, and object-symbol check are in
`validation/20260913T041756Z/`; proof took 60.456 seconds. All recorded source
hashes matched after validation. Only this evidence section was added afterward.
