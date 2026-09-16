# Roadmap

Ordered by payoff over effort. The ordering principle is that changes which leave the
public specification (`Search = NFA_Accepts`, `Full_Match = NFA_Accepts`) untouched are
cheap, because they are refinements under existing theorems; changes which replace the
specification are projects, because they re-open the composition from parser to matcher.

Unchecked items are proposals; none is required for the library to be correct
as it stands.

## Tier 1 — specification-preserving, cheap

- [x] **Generation-stamped sparse set in the simulator.** Active sets use a dense
  list, inverse index and generation stamps. Resetting a set changes only its generation
  and length; transitions, closure and acceptance visit dense entries. Local workspaces
  are sized to the compiled state count, with `O(states)` initialization and storage
  and `O((n+1) * states)` worst-case work.
  The representation proof preserves the existing NFA and language theorems.
  Saturation is handled by the workspace reuse refinement below. See `PROOF.md`.
- [x] **Start-byte set and an empty-active-set skip loop.** Compilation caches
  the entry closure for interior positions, its accepted byte set and nullability.
  After a byte transition leaves no live continuation, search scans excluded bytes
  without NFA transitions or closures. A local cache certificate and the model's
  skip-step lemma preserve exact acceptance. The first and final boundaries keep
  their normal closure checks, including nullable patterns and absolute anchors.
  Start-anchored branches have no interior candidates. See `PROOF.md` and
  `BENCHMARKS.md`.

- [x] **Reuse the match workspace across records.** A compiled-state-sized
  `Matcher` retains both sparse sets; initialization is paid once per workspace.
  Both CLIs reuse it across records and files. Generation changes empty the sets
  in O(1), with an O(states) stamp reset at 32-bit saturation and a proved
  overflow guard. Reusable entry points preserve validity and equal the existing
  one-shot functions, leaving the NFA and composition theorems unchanged.
  Initial closure still visits active states; a wide nullable prefix retains
  that per-record cost. See `PROOF.md` and `BENCHMARKS.md`.

These refinements remove capacity-sized per-position and per-record clearing
and replace state-set updates with byte comparisons where no match can start. Their measured
benefits and costs are recorded in `BENCHMARKS.md`.

## Tier 2 — specification-preserving, but a project

- **Multi-byte required-literal prefilter.** Higher payoff than the start-byte set on
  realistic patterns, but extraction needs a theorem of the form "every accepted span
  contains this literal", which is an analysis over the compiled program rather than a
  one-step reachability fact. Worth doing only after Tier 1, and only if measurement
  justifies it.
- **Lazy DFA.** One table lookup per byte, and invisible in the specification: a cached
  transition is a memoised composition of the closure and step models. It fits this design
  badly, and is the third performance step rather than the first:
  - A DFA state is a subset of the state space, so with the default budget the cache key
    is 512 bytes. Hashing and comparing keys of that size on every miss, in a fixed table
    with no heap, can plausibly cost more than it saves. A smaller instantiation, or a
    bounded sparse representation of the subset, is a precondition.
  - Cache exhaustion needs an eviction path, and correctness must then hold across
    invalidation. The performance argument also becomes data-dependent in a way the proof
    cannot express.
  - It interacts with per-position start injection, and anchors make the transition
    function boundary-sensitive.

## Tier 3 — changes the specification

- **Capture groups**, as PikeVM registers. The most valuable feature addition, and the one
  with a published verification precedent: the Linden development mechanises a PikeVM with
  captures in Rocq. It requires replacing language acceptance with a leftmost-first
  semantics over backtracking trees, which re-opens the parser-to-matcher composition
  rather than extending it. Plan it as a second version of the specification, not as an
  increment.
- **Lookaround.** No verified precedent exists; the published linear-time algorithms are
  not proved. This would be a research contribution rather than an engineering task.

## Explicitly not planned

- Backreferences. They take matching outside the regular languages and make the problem
  NP-hard, which forfeits the worst-case bound the engine exists to provide.
- Unicode. It moves the alphabet from bytes to code points, and turns the per-instruction
  byte set into a data structure with its own correctness argument, backed by large
  generated tables that would have to be trusted or proved.
- Becoming a drop-in grep or ripgrep. The CLI is a named subset by intent.

## Background

`~/aireports/2026-09-14-spark-re-vs-other-regex-engines.md` compares this engine with
RegElk/Linden, the three GNAT pattern packages and other Ada engines, and records the
reasoning behind the ordering above.
