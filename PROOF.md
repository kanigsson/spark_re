# Correctness proof

The tree compiler and NFA simulator are proved sound and complete against
independent tree-span and instruction-path models. Lexical scanning is proved
against independent byte-span definitions, and successful parsing constructs
a derivation in an independent expression grammar. Parser completeness proves
that a pattern with any such derivation cannot produce `Syntax_Error`;
resource failures remain explicit. Every grammar derivation has the same span
semantics as the byte-only `Pattern_Matches` denotation. The public
`Compile_For_Text` theorem connects successful compilation to `Pattern_Accepts`
for both whole matching and search, independently of the chosen derivation.

## Unit structure

The proof is split across units so that each layer's obligations can be
discharged, and re-discharged, on its own:

| Unit | Contents | Proves |
| --- | --- | --- |
| `Spark_Re_Common` | limits, `Compile_Status`, `Byte_Set` | nothing; no body |
| `Spark_Re_Trees` | tree types, `Tree_Valid`, `Matches`, `Nullable` | span semantics and its empty-span lemmas |
| `Spark_Re_Trees.Parsing` | scanners, lexical models, `Grammar`, `Pattern_Valid`, `Pattern_Matches`, `Parse` | lexical refinement, parser soundness and completeness, derivation-independent matching |
| `Spark_Re_Trees.Matching` | instructions, `Compile_Tree`, simulator, path model | tree-to-NFA equivalence and the simulator model |
| `Spark_Re` | facade | composition only |

The two large layers share only the tree. `Spark_Re_Trees.Parsing` never names
a program, an instruction or an NFA state; `Spark_Re_Trees.Matching` never names a
pattern span, a scanner or a grammar level. Neither withs the other. The
parser-completeness proof lives entirely inside the parsing unit and uses no
compiler or simulator theorem.

The following predicates are declared in a spec and defined in its body,
so that a client carries them without being able to unfold them:

- `Grammar` is the parser's derivation relation. `Parse` produces it and the
  facade passes it on; only the parser body sees what it means.
- `Pattern_Valid` is byte-only syntax acceptance. Grammar derivations imply
  it, and `Parse` cannot report a syntax error when it holds.
- `Pattern_Matches` gives byte-only span semantics; clients use the grammar
  refinement lemmas without unfolding its lexical walk.
- `Tree_Compiled` is the matcher's construction certificate, packaging the
  accepting state and root `Compiled_Shape` that `Compile_Tree` establishes and
  `Lemma_Compiler_Correct` consumes. The facade joins a parse result to a
  compile result without seeing the instruction layout.

`Compile_Pattern_For_Text` composes the parser and compiler certificates with
the grammar-to-pattern matching theorem. The public `Compile_For_Text` wrapper
hides the intermediate tree entirely.

## Proved simulator specification

`Search (P, T) = NFA_Accepts (P, T, False)` and
`Full_Match (P, T) = NFA_Accepts (P, T, True)` are public ghost postconditions.
Invalid programs reject input in both the implementation and the model.

The model in `src/spark_re_trees-matching.adb` uses these definitions:

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

These definitions do not call `Advance`, `Closure`, `Sparse_Closure`, or `Run`.

## Why the worklist is complete

The executable `Sparse_Closure` uses the reached set's dense list as an
append-only queue. `Length` counts discovered states and `Done` counts processed
entries. `Sparse_Valid` connects each live current-generation stamp to its dense
slot through an inverse index, proves the reverse correspondence, and equates
`Length` with the cardinality of the ghost Boolean `View`. A missing live state
therefore implies room to append it. `Include` preserves this correspondence
and the existing dense prefix; duplicate insertion leaves the set unchanged.
The zero sentinel may be stamped by a byte transition but has no dense slot;
closure discards it, as in the original Boolean model.

`Clear` increments the generation and resets only the length. All stamps are
at most the previous generation, so the new view is empty even though dense
entries and indices remain in storage. `Run` bounds both sets' generations by
the text offset; skipped bytes do not advance them. An increment occurs only
before the final boundary, proving
absence of overflow even for the maximum String length. The two local sets
are constrained by the compiled state count, so initialization and workspace
cost O(compiled states); no per-position array clearing remains.

The original Boolean `Closure` is now a static ghost procedure used to prove
model properties. It is absent from executable builds. The sparse closure
proves the same reachability and closed-set postconditions against `View`.

`Processed_Closed` says every permitted edge from a processed state reaches
an already discovered state. Each iteration processes the next queue entry.
The state-count iteration budget suffices: either the queue empties early,
or `Done` reaches the state count while `Length` cannot exceed it. In both cases
`Done = Length`, so every discovered state has been processed and the final set
is epsilon-closed.

For soundness, each newly discovered state receives a ghost path depth and
satisfies `Epsilon_Reach` at that depth. Depth is bounded by the iteration
number. `Lemma_Reach_Monotone` raises this bound to the state count at exit.
Completeness follows from `Lemma_Closed_Reach`. Array extensionality is proved
separately so equal state sets can be substituted in the recursive model.

`Run` maintains equality between its current state set and `Model_States` at
the current offset. For search it also records that no earlier boundary was
accepting. These invariants cover early success and exhaustion of the input.

## Start-byte filtering and skipped positions

`Build_Start_Info` runs the proved sparse closure on the entry state with both
anchor flags false. It stores the reached-state mask and computes the union of
its consuming instructions' byte sets, plus whether it contains an accept state.
The loop invariants specify the exact union and accept-state test. This analysis
runs only after successful compilation. It receives a read-only program and
returns a separate `Start_Info` record, preserving the instructions, entry,
state count and validity flag.

The private `Program` invariant includes `Restart_Info_Valid`: the cached mask
contains the entry state, is closed under interior epsilon edges, and its byte
and nullable summaries cover every consuming and accepting state in the mask.
This local certificate is sufficient for filter safety even without assuming a
canonical cache. `Lemma_Closed_Reach` connects it to the independent path model;
no cache contents are trusted. The original NFA and pattern denotations are
unchanged.

`Run` tests for an empty continuation set after the byte transition and before
injecting the next search start. Testing the full restarted active set would
miss this opportunity because it already contains the entry state. When no
continuation survives and the interior closure is not nullable, it skips bytes
outside `Restart.Bytes`. `Lemma_Skip_One` proves that the current interior restart
cannot accept or consume that byte, and the next model state is another restart
closure. `Lemma_Reach_Live_Equal` accounts for the discarded zero sentinel.
The loop carries model equality and rejection of all earlier positions, and
records that the offset only increases.

The first boundary is evaluated before skipping. The skip loop stops at the
final boundary, where the normal closure enables end anchors; `$`, `^$`, nullable
cycles and alternatives therefore retain their absolute-boundary semantics.
Interior start-anchored branches contribute no candidate bytes. Whole matching
keeps the normal simulator path.

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

`Parse` and `Compile_Tree` have separate contracts. `Parse` proves
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

## Lexical grammar refinement

The executable parser uses separately contracted scanners. Their static
models read pattern bytes directly and call neither the scanners nor `Parse`:

- `Decimal_Digits`, `Decimal_Value` and `Numeral_End` define a maximal decimal
  numeral. The value recurrence saturates at 256; `Lemma_Decimal_Saturated`
  proves that further digits cannot turn overflow into an accepted bound.
  `Scan_Number` succeeds exactly when the numeral is nonempty and at most 255,
  and returns its exact value and endpoint. Failure has either a missing-digit
  or an overflowing-prefix witness. Leading zeros remain valid.
- `Class_Unit_Valid`, `Class_Unit_End` and `Class_Unit_Byte` specify literal and
  escaped class bytes, excluding recognizable POSIX class/collation syntax.
  `Class_Piece_Valid` adds optional ordered inclusive ranges. The corresponding
  scanners succeed exactly when these predicates hold and return exact bytes
  and endpoints.
- `Class_Tail_Valid`, `Class_Tail_End` and `Class_Tail_Has` give a recursive
  class grammar and its byte membership. A first `]` belongs to the first
  piece; a subsequent unescaped `]` closes the class. `Range_Follows` states
  when a hyphen introduces a range. `Class_Syntax` adds the opening bracket,
  optional negation, closing endpoint, and membership for all 256 bytes.
  `Scan_Class` proves both acceptance and rejection, as well as exact set
  construction. Its iterative union invariant relates the accumulated set
  and remaining class suffix to the complete class; negation complements it.
- `Bounds_Valid`, `Quantifier_Valid` and `Quantifier_Model` specify `*`, `+`,
  `?`, `{n}`, `{n,m}` and `{n,}`. `Scan_Quantifier` succeeds exactly for these
  forms, with exact bounds, unboundedness and endpoint. Missing delimiters,
  missing/oversized numerals and descending bounds reject.
- `Leaf_Valid` and `Leaf_Syntax` cover literal bytes, dot, absolute anchors,
  classes, and the restricted set of outside-class escapes. `Scan_Leaf`
  proves exact node kind/byte set and endpoint, and rejects exactly the invalid
  leaf starts within its caller precondition.

All spans are offsets, including for strings ending at `Integer'Last`. The
scanners produce only `Success` or `Syntax_Error`; node/state/expansion limits
belong to their callers. The parser retains its existing error propagation
when an allocation failure precedes a malformed leaf. These contracts describe
one token from a supplied boundary, not acceptance of the entire pattern.

## Successful parser grammar refinement

`Grammar (Pattern, Nodes, Id, First, Last, Level)` relates pattern spans to
syntax trees using four precedence levels:

```text
expression ::= term | expression "|" term
term       ::= empty | factor | term factor
factor     ::= atom | atom quantifier
atom       ::= leaf | "(" expression ")"
```

Leaves and quantifiers use the independently specified lexical relations.
The empty term requires an empty node. Concatenation, alternation and
repetition require the corresponding node kind and child derivations;
grouping wraps an expression without allocating a node. A repeated factor's
child must derive an atom, so another postfix quantifier requires grouping.
The grammar calls neither `Parse` nor any executable scanner. Its recursive
variant decreases the node identifier, pattern-span length, or precedence
level; grouping decreases the span even when it retains the node identifier.

`Lemma_Grammar_Frame` and `Lemma_Frame_Syntax_Frame` prove that preserving a
tree's allocated prefix preserves its existing grammar derivations. `Add`
applies these lemmas to the active frames when it allocates a fresh node.

Each active parser frame has static ghost pattern offsets for its start,
current term start, and flushed-term endpoint. `Frame_Syntax` relates its
expression, term and pending atom to those spans. An expression prefix ends
at an actual alternation separator. Suspended frames end at the following
frame's opening parenthesis and have no pending atom. The ghost cursor marks
the boundary whose frame derivation is established while a scanner advances
the executable cursor over the next token.

`Flush_Atom` proves concatenation of the term and pending atom. `Flush_Term`
proves the empty term or joins the completed term to the expression prefix.
The main loop proves opening/closing groups, alternation, leaf attachment,
and attachment of a single quantifier. The successful `Parse` postcondition
establishes `Grammar` for the root over the complete pattern, in addition
to `Tree_Valid` and a nonzero root.

`Compile_With_Tree` is the shared executable parse/compile operation used by
public `Compile`. It retains the successful grammar derivation and compiled
root certificate. For any supplied text and whole/search mode,
`Compile_Pattern_For_Text` calls that same operation and applies the compiler
theorem. On success, both `NFA_Accepts` and the executable matching result equal
`Tree_Accepts` for the returned grammar-derived tree. Failure leaves an invalid
program and makes no matching-language claim.

## Parser completeness and structural syntax rejection

`Pattern_Valid` is an independent byte-only syntax predicate. Its recursive
`Syntax_Continuation` model consumes maximal lexical tokens, tracks the number
of unmatched opening parentheses, and distinguishes no pending atom, a plain
atom, and an already quantified atom. End of pattern requires zero unmatched
parentheses. Closing groups and alternation accept empty contents; a postfix
quantifier requires a plain atom. Classes and escapes consume their lexical
spans, so punctuation inside them has no structural effect. The model calls
neither `Parse` nor its scanners and contains no allocation or capacity state.
Its termination variant is the remaining pattern length.

`Lemma_Grammar_Continuation` proves by induction on the existing `Grammar`
relation that a derived span can precede any compatible valid continuation.
Atoms leave a plain atom; factors may leave a quantified one; terms and
expressions may also be empty. These continuation hypotheses compose across
concatenation and alternation and discharge grouping and quantifier attachment.
The induction follows the grammar's node/span/precedence variant, including
empty left terms and groups that allocate no node. `Lemma_Grammar_Valid`
specializes it to a complete expression followed by the end of the pattern.
Thus byte-only validity is justified from the independent grammar, rather
than defined as the parser's success result.

The executable parser loop maintains that an initially valid pattern has a
valid continuation at its current cursor, group depth, and pending-atom state.
Each structural and lexical error branch contradicts that invariant. The
allocation and flushing helpers prove that they introduce only `Node_Limit`,
not syntax errors. Their existing error propagation remains unchanged,
including a malformed leaf overriding an earlier allocation failure.

`Parse_Complete` takes an arbitrary valid tree deriving the complete pattern,
proves `Pattern_Valid`, and calls the actual `Parse`. Its postcondition permits
only `Success`, `Node_Limit`, or `Pattern_Too_Long`; success retains the existing
grammar derivation for the returned tree. Consequently `Syntax_Error` excludes
any complete derivation in the modeled tree type. This closes parser
completeness and structural syntax rejection, with explicit resource failures.
An invalid pattern may still hit a resource limit before its error is reached;
no exact resource-sufficiency claim is made.

All added definitions, lemmas and loop certificates are static ghost code.

## Derivation-independent pattern matching

`Pattern_Matches (Pattern, Text, First, Last)` requires byte-only syntax
validity and interprets the pattern directly. It calls neither `Grammar`,
`Parse`, `Compile`, nor any executable scanner, and constructs no tree.
`Pattern_Accepts` applies it to the whole text or existentially to any span.

The independent `Walk` model consumes maximal lexical tokens while tracking
group depth and the last top-level alternative, atom, and quantifier positions.
Classes and escapes consume their complete token, so embedded punctuation
cannot become a structural separator. Nested groups preserve the outer
positions. `Lemma_Walk_Join` proves composition at a reached token boundary;
`Lemma_Grammar_Walk` proves that every grammar span reaches its endpoint with
balanced depth and the appropriate outer boundaries.

`Denotes` uses those deterministic positions to interpret precedence. It splits
expressions at their last top-level bar and terms at their last factor, applies
the lexical quantifier bounds to atoms, and interprets group contents
recursively. Leaves read the independently modeled byte sets and absolute
anchors. `Repeat_Denotes` permits empty mandatory and finite optional copies;
extra unbounded copies advance the text position. Its decreasing pattern span,
precedence, repetition bounds, and text span establish termination without a
fuel cutoff or an assumption that repeated atoms consume bytes.

`Lemma_Denotation` proves equality to `Matches` for every grammar level and
pattern/text span. The grammar induction fixes the denotation's split positions;
`Lemma_Repeat_Denotation` supplies repetition congruence, including nullable
atoms. An empty left term is eliminated using the empty-span identity. This
case matters: the grammar can derive `a` with a leaf or with a concatenation of
an empty node and that leaf. The theorem proves semantic equality without
requiring identical tree shapes, node identifiers, or unused nodes.

The public parser lemmas expose the result without unfolding the grammar:

- `Lemma_Grammar_Matches`: every complete derivation agrees with
  `Pattern_Matches` on any supplied text span.
- `Lemma_Derivation_Independent`: any two complete derivations of the same
  pattern agree on that span.
- `Lemma_Grammar_Accepts`: the tree's whole/search interpretation equals
  `Pattern_Accepts`.

The facade's public `Compile_For_Text` invokes the same `Compile_With_Tree`
operation as executable `Compile`, then composes grammar refinement with the
compiler theorem. On success, both NFA acceptance and the selected executable
`Full_Match` or `Search` equal `Pattern_Accepts (Pattern, Text, Whole)`. Its
contract contains no tree witness. Compilation failures retain their explicit
statuses; no resource-sufficiency theorem is claimed.

This closes the remaining matching-language obligation. The denotation follows
the project's byte grammar and Boolean span semantics; it does not specify
captures, match-selection priority, or a different regex dialect.

## Proof and execution boundary

The recursive semantic model, its lemmas, queue certificates, and compiler
preservation snapshots use `Ghost => Static` or `Static` assertions. GNATprove
checks them, including termination; neither release nor assertion-enabled
binaries execute them. Ordinary executable contracts remain enabled in the
checks build. There are no assumptions, imported proof axioms, proof
suppressions, or library bodies excluded from SPARK.

Proof runs at `--level=4`, which uses cvc5, Z3 and Alt-Ergo.

Several entities prune their own proof context with `Hide_Info` on expression
function bodies. `Numeral_End` is hidden by default and disclosed only by its
step lemma. In addition, the witness searches over compiled code intervals
carry the shape certificates without inspecting them: `Lemma_Concat_Preserve`,
`Lemma_Repeat_Preserve`, `Shape_Parts`, `Copies_Parts` and `Lemma_Repeat_Join`
hide the recursive `Compiled_Shape`, `Copies_Shape`, `Optional_Shape` and
`Tail_Shape` definitions, and `Bounds_Valid` hides `Decimal_Digits`, whose
digit spans are already certified by `Numeral_End`'s postcondition. Hiding is
decided per verified entity, so `Lemma_Shape_Preserve` is a dispatch over three
case lemmas plus the leaf case, which is the one place that still unfolds a
certificate. `Lemma_Grammar_Accepts` hides `Matches` and `Pattern_Matches`: its span
quantification needs only their proved equality, not either recursive
definition. These annotations prune context; they assert nothing.

The evidence covers the default `Regex` instantiation. Other capacities need
their own GNATprove run. Stack capacity and a formal machine-cost model are
outside the proof. Each closure processes at most the compiled state count.
The sparse set refinement removes per-position clearing and scans of inactive states;
initialization costs time proportional to the compiled state count once per call.
The machine-cost bound is an implementation argument, not a proved theorem.
