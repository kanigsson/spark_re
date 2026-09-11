# Correctness proof and remaining obligations

This attempt proves correctness of the NFA simulator. It does **not** yet
prove that a pattern compiles to an NFA accepting exactly the pattern's
language. `NFA_Accepts` describes the supplied program's instructions; it does
not interpret pattern syntax.

## Proved simulator specification

`Search (P, T) = NFA_Accepts (P, T, False)` and
`Full_Match (P, T) = NFA_Accepts (P, T, True)` are public ghost postconditions.
Invalid programs reject input in both the implementation and the model.

The model in `src/spark_re.adb` uses these definitions:

- `Epsilon_Edge` permits split edges and anchors whose condition holds at the
  current text boundary. Sentinel zero is never an epsilon destination.
- `Epsilon_Reach (..., Target, Steps)` means that a live target is a seed or
  has an epsilon predecessor reachable with one fewer step. Thus it describes
  paths of at most `Steps` edges, including zero-edge seed paths.
- `Model_Closure` selects exactly the states with such paths bounded by the
  compiled state count. `Lemma_Closed_Reach` proves that every closed superset
  of the seeds contains these states. The implementation proves that its
  result is closed and agrees with `Model_Closure`, establishing the least
  closed superset, including for cyclic and nullable NFAs.
- `Model_Step` selects a destination iff some active consuming instruction
  accepts the current byte and points there. Search also seeds the entry
  state at each new boundary.
- `Model_States` defines the active set recursively by text offset: initial
  closure, then a byte step and another closure. Start/end anchors use the
  absolute input boundaries. `NFA_Accepts` tests acceptance at the final
  boundary for whole matching, or at any boundary for search.

These definitions do not call `Advance`, `Closure`, or `Run`.

## Why the worklist is complete

The executable closure uses an append-only queue. `Tail` counts discovered
states and `Done` counts processed entries. A ghost inverse `Rank` connects
reached states to their queue slots. `Queue_Valid` proves both directions of
that correspondence and equates `Tail` with the cardinality of the reached
set. A missing live state therefore implies room to append it.

`Processed_Closed` says every permitted edge from a processed state reaches
an already discovered state. Each iteration processes the next queue entry.
The state-count iteration budget suffices: either the queue empties early,
or `Done` reaches the state count while `Tail` cannot exceed it. In both cases
`Done = Tail`, so every discovered state has been processed and the final set
is epsilon-closed.

For soundness, each newly discovered state receives a ghost path depth and
satisfies `Epsilon_Reach` at that depth. Depth is bounded by the iteration
number. `Lemma_Reach_Monotone` raises this bound to the state count at exit.
Completeness follows from `Lemma_Closed_Reach`. Array extensionality is proved
separately so equal state sets can be substituted in the recursive model.

`Run` maintains equality between its current state set and `Model_States` at
the current offset. For search it also records that no earlier boundary was
accepting. These invariants cover early success and exhaustion of the input.

## Compiler facts established

`Compile` retains its validity/status and well-formedness guarantees.
`Emit` additionally proves that a nonzero result names a fresh instruction,
that successful emission stores exactly the requested opcode, byte set and
successors, and that all previous instructions are unchanged. `Build` proves
that it preserves every instruction present on entry, including on failure.
In particular, patching an unbounded repetition's split cannot modify a
previously compiled continuation.

These are preservation facts, not compiler language equivalence.

## Full regex theorem still open

A full theorem needs an independent grammar and a span interpretation
`Matches (Tree, Text, First, Last)`, with anchors evaluated against the whole
text. For successful compilation of a pattern to `P`, the intended result is:

- whole matching iff the parsed tree matches span `0 .. Text'Length`;
- search iff the parsed tree matches some span with
  `0 <= First <= Last <= Text'Length`.

Two semantic layers remain unproved and are not asserted as assumptions:

1. **Parser refinement.** Relate consumed pattern bytes, active frames and
   allocated nodes to the grammar. This must cover precedence, empty
   alternatives, grouping, byte classes and escapes, repetition bounds, and
   errors. Existing parser contracts prove bounds/progress, not this relation.
2. **Compiler refinement.** Relate `Build (Node, Next, Entry)` to the tree's
   span interpretation, stopping fragment paths at `Next`. The argument must
   compose concatenation and alternation, account for optional and mandatory
   copies, and handle the patched back edge of unbounded repetitions. Empty
   matches and anchored nullable cycles require an explicit argument, not an
   assumption that every repetition consumes a byte. Resource failures must
   remain separate from successful language equivalence.

The current monolithic compiler keeps its tree and construction information
local. A next proof pass should give parsing and tree compilation separate
contracts, with a structural fragment relation and preservation lemmas, then
connect that relation to NFA paths. Merely defining pattern semantics by calling
`Compile` would make the missing compiler claim circular.

## Proof and execution boundary

The recursive semantic model, its lemmas, queue certificates, and compiler
preservation snapshots use `Ghost => Static` or `Static` assertions. GNATprove
checks them, including termination; neither release nor assertion-enabled
binaries execute them. Ordinary executable contracts remain enabled in the
checks build. There are no assumptions, imported proof axioms, proof
suppressions, or library bodies excluded from SPARK.

The evidence covers the default `Regex` instantiation. Other capacities need
their own GNATprove run. Stack capacity and a formal machine-cost model are
outside the proof. Each closure processes at most the compiled state count;
clearing the fixed-size arrays also costs time proportional to state capacity.
See `VERIFICATION.md` for validation evidence.
