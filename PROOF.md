# Correctness proof and remaining obligations

The tree compiler and NFA simulator are proved sound and complete against
independent tree-span and instruction-path models. The remaining semantic gap
is parsing: there is no proved relation between pattern bytes and an independent
pattern grammar. `NFA_Accepts` describes instructions, and `Matches` interprets
tree nodes; neither interprets pattern syntax.

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

Successful `Build` also establishes `Fragment_Closed`: every newly emitted
instruction is consuming, splitting, or an anchor; each of its active edges
stays in the newly allocated interval or points to `Next`. Its entry is either
`Next` or a newly allocated state. This includes the patched split of an
unbounded repetition.

For leaves, successful `Build` establishes `Leaf_Compiled`, describing the
empty continuation or the exact byte/anchor instruction it emitted.
`Lemma_Leaf_Path` proves that this contract makes `Matches` equivalent to
`Fragment_Path` for every span and every positive path budget.

Successful `Build` also establishes `Compiled_Shape` for every constructor.
This independent structural relation inspects the allocated code interval:

- Concatenation has a boundary and middle state joining the right child,
  compiled first, to the left child.
- Alternation has two child intervals and a final split to their entries.
- `Copies_Shape` describes the mandatory copies; `Optional_Shape` describes
  each bounded optional copy and its bypass split.
- `Tail_Shape` describes either the bounded optional suffix or an unbounded
  split whose body returns to that split and whose other edge exits to `Next`.

The shape frame lemmas prove that changing instructions outside the allocated
interval preserves these certificates, including when patching the unbounded
split. The join lemmas assemble child certificates. `Compile_Tree` proves
that successful compilation has an accepting instruction at state 1 and a
root certificate with state 1 as its continuation. The compiler theorem below
uses these certificates to establish `Matches`/`Fragment_Path` correspondence
for every constructor.

## Tree contracts and span semantics

`Parse` and `Compile_Tree` now have separate contracts. `Parse` proves
`Tree_Valid`: child references point backward, concatenation and alternation
have two nonzero children, repetition has a nonzero child, and finite bounds
satisfy `Low <= High`. Successful parsing returns a nonzero root. Parser frame
invariants bound every reference by the allocated prefix. `Add` proves fresh
allocation, exact node storage, and preservation of all earlier nodes.

`Compile_Tree` consumes this structural contract. Recursive `Build` calls
prove that their node arguments are live and decrease, without runtime checks
for malformed trees. Tree compilation can return only success, state-capacity
failure, or expansion-limit failure; syntax errors belong to parsing.

The independent ghost function `Matches (Nodes, Id, Text, First, Last)` now
interprets tree spans. It handles empty nodes, byte sets, absolute anchors,
concatenation by a split point, alternation, and repetition. It calls neither
parser, compiler, nor simulator. Offsets are relative to the whole input,
including when the Ada string has a nonstandard lower bound.

`Repeated_Matches` permits empty mandatory copies and decrements their lower
bound. Bounded optional copies decrement the upper bound. Once the lower
bound of an unbounded repetition is satisfied, additional copies advance the
text position; empty copies are omitted. Lexicographic variants prove
termination even for nullable repeated subtrees.

`Lemma_Empty_Repetition` proves that a repetition accepts an empty span exactly
when its lower bound is zero or its child accepts that empty span.
`Lemma_Nullable` lifts this to every tree constructor: empty-span `Matches`
is equivalent to the structural `Nullable` predicate with the appropriate
absolute-anchor flags. The compiler theorem also covers these empty spans,
relating them to compiled epsilon paths.

## Fragment paths and simulator equivalence

`Fragment_Path (Code, Entry, Stop, Text, First, Last, Fuel)` describes a path
of at most `Fuel` instruction edges consuming exactly the span `First .. Last`.
It stops immediately at `Stop`, accepting there only when the entire span has
been consumed. It never reads or executes that continuation instruction.
Consuming edges advance one byte; split and permitted anchor edges preserve
the offset. Anchors use absolute input boundaries. Sentinel zero, dead
instructions, and accepting instructions cannot be traversed. The ghost
`Path_Steps` counter is a mathematical nonnegative integer (`Big_Natural`);
termination decreases this counter and never assumes that an edge consumes a
byte. Its uses are static ghost code, erased in both executable build modes.

The following lemmas are proved:

- `Lemma_Path_Monotone`: increasing the budget preserves a path.
- `Lemma_Path_Frame`: changing code outside a closed fragment preserves its
  paths. In particular, the continuation instruction may change, which is
  needed when patching an unbounded repetition's split.
- `Lemma_Path_Compose`: a path through a closed fragment to its continuation
  composes with a path from that continuation, with the sum of the budgets.
  Mathematical budgets avoid an artificial machine-integer ceiling when
  composing witnesses. `Closed_Interval` describes internal code intervals,
  so the lemma also applies to child fragments inside a larger program.
- `Lemma_Path_Decompose`: a path through the same boundary yields a span split
  and two path budgets that partition the original budget. This establishes
  the reverse direction of composition, including empty spans and cycles.
- `Lemma_Path_States`: a path from a state active at `First` leaves its endpoint
  active at `Last` in `Model_States`.
- `Lemma_Path_Accepts`: a path from a valid program's entry to a live accepting
  state implies `NFA_Accepts` and the corresponding `Search` or `Full_Match`
  result. Whole matching requires span `0 .. Text'Length`; search permits any
  span within the input.
- `Lemma_Accepts_Path`: conversely, NFA acceptance constructs an accepting
  state, span, and path witness. Its budget is at most
  `Last * (State_Count + 1) + State_Count`.

The reverse construction (`Lemma_Reach_Prepend`) follows epsilon predecessors
back to a boundary seed, then consuming predecessors back to the previous text
boundary. It carries a valid suffix to an accepting state. That accepting
state has no outgoing edges, so it cannot be traversed earlier in the prefix.
Search may stop reconstruction at an entry-state restart; whole matching must
reach the initial boundary. Its lexicographic variant decreases the text
offset or the remaining epsilon steps.

Thus the path relation and the simulator model agree on acceptance for valid
programs. `Fragment_Path` is independent of the simulator. The bridge proof
reuses the already proved `Closure` contract to establish that `Model_Closure`
is closed and contains its seeds; this does not change either semantic model's
definition.

## Tree compiler correctness

For every `Tree_Valid` tree, root and input text, successful `Compile_Tree`
establishes:

- `Full_Match (P, Text) = Matches (Nodes, Root, Text, 0, Text'Length)`;
- `Search (P, Text)` iff some span `First .. Last` matches the root, with
  `0 <= First <= Last <= Text'Length`.

`Tree_Accepts` states these two interpretations. `Lemma_Compiler_Correct`
proves equivalence to `NFA_Accepts` and the executable matching functions from
the compiler's structural guarantees. `Compile_Tree_For_Text` applies that
theorem to an actual `Compile_Tree` call for an arbitrary supplied text. Its
contract keeps state-capacity and expansion failures separate from success.

`Shape_Parts`, `Copies_Parts` and `Optional_Parts` extract construction
witnesses. The four `Lemma_*_Closed` procedures prove that every fragment's
edges stay inside its interval or reach its continuation, and that its entry
is internal or the continuation. These are derived from the structural
certificates, including certificates for subintervals of the final code.

`Lemma_Shape_Sound` extracts a tree match from a stopping path. Concatenation
decomposes at the child boundary; alternation follows the selected split.
Repetition uses separate lemmas for mandatory copies and the optional or
unbounded suffix. Mandatory empty copies remain mandatory. On an unbounded
loop, a nonempty body provides the advancing span witness required by
`Repeated_Matches`; an empty body is discarded because the recursively proved
suffix already matches the same span. Induction decreases the path budget even
when the text offset does not advance. Anchors retain their absolute offsets.

`Lemma_Shape_Complete` constructs a finite stopping-path witness from a tree
match. It composes child paths and includes the required split edges. Mandatory
copies decrease their count, bounded optional copies decrease their upper
bound, and extra unbounded copies decrease the remaining text span. Thus empty
mandatory copies and nullable unbounded bodies both terminate without assuming
that every copy consumes a byte. Mathematical budgets can always be added;
the executable compiler and simulator retain their original bounded storage.

The final acceptance argument uses the fact that the root fragment has no
accepting instruction: state 1 is the only live accepting state. The existing
path/simulator bridge then supplies both directions of the theorem.

## Parser grammar refinement still open

The next semantic obligation is an independent pattern grammar and a proof
that `Parse` implements it. Relate consumed pattern bytes, active frames and
allocated nodes to that grammar, covering precedence, empty alternatives,
grouping, byte classes and escapes, repetition bounds, and syntax errors.
Resource failures must remain distinct from syntax rejection. Existing parser
contracts prove bounds, progress and tree structure, which suffice to apply
the compiler theorem, but do not establish this pattern-language relation.

A full pattern theorem must connect that independent byte interpretation to
`Matches`, then use the proved compiler/simulator equivalence. Defining pattern
semantics by calling `Parse` or `Compile` would not close this gap.

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
