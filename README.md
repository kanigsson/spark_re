# Spark RE

An allocation-free, byte-oriented Thompson NFA regex library in Ada/SPARK,
with ordinary Ada `spark-grep` and `spark-rg` CLIs. The library has no I/O or
dependencies.

## Build and use

Use a matching Ada 2022 GNAT/GPRbuild and GNATprove installation.

```sh
make test                 # library tests, Python re and grep -E oracles
make test-contracts       # same tests with executable library contracts
make flow                 # initialization and dependency analysis
make prove                # safety, termination, NFA simulator correctness
make format
printf '%s\n' src/foo.adb src/bar.ads | bin/spark-grep '\.adb$'
bin/spark-grep -n 'procedure|function' src/*.ad?
bin/spark-rg 'procedure|function'
```

`spark_re.gpr` builds the static library alone; `tools.gpr` builds the CLI
and tests. `alire.toml` publishes the library alone.
Release builds retain runtime checks; `-XSPARK_RE_BUILD=checks` also executes
assertions and uses separate object/library/executable directories. Tool paths
belong in optional, ignored `local.mk`; `GPRBUILD`, `GNATPROVE`, `GNATFORMAT`,
and `JOBS` can also be overridden on the make command line. Nothing is installed
or added to PATH by the build.

```ada
with Regex;
--  In a client procedure:
P : Regex.Program;
Status : Regex.Compile_Status;
--  In its body:
Regex.Compile ("^(src|tests)/.*[.]ad[bs]$", P, Status);
if Status = Regex.Success and then Regex.Search (P, "src/example.adb") then
   null; -- matched
end if;
```

`Regex` is the default instance of generic `Spark_Re`. Clients can instantiate
`Spark_Re (Max_Nodes => ..., Max_States => ...)` to choose other storage budgets.
`Program` owns the fixed instruction array; compilation uses bounded local
syntax-tree/frame arrays and recursion decreasing in syntax-node index.
Matching uses two local sparse sets sized to the compiled state count, each
with stamp, dense and index arrays.
No heap allocation occurs in the library. Account for this automatic storage on small-stack targets.
Patterns and text may have arbitrary String lower bounds, including a final
index equal to `Integer'Last`. Search accepts any substring, including an empty
one; `Full_Match` requires the whole string. Anchors always refer to the whole
input. An invalid/default-initialized program never matches.

## Pattern language

Supported syntax:

| Syntax | Meaning |
| --- | --- |
| `abc`, `a\+b` | literal bytes (escape punctuation to make it literal) |
| `.`, `[abc]`, `[a-z]`, `[^a-z]` | any byte; sets, inclusive byte ranges, negation |
| `(ab)`, `a\|b` | grouping, alternation |
| `a*`, `a+`, `a?` | zero or more, one or more, optional |
| `a{n}`, `a{n,m}`, `a{n,}` | exact, bounded, unbounded repetition |
| `^`, `$` | start and end of the entire input |

Concatenation binds more tightly than alternation; postfix repetition binds
most tightly. Empty patterns, groups, and alternatives accept the empty string.
Repeated postfix quantifiers are errors. `]` is literal when first in a class;
`-` is literal first or last, and a range separator otherwise. Backslash escapes
the next byte inside a class; outside classes only regex punctuation and `-`
may be escaped. Ranges use Character byte order. Dot includes NUL and newline.

No backreferences, lookaround, capture extraction, lazy quantifiers, Unicode
normalization, locale folding, POSIX named classes, collating elements, or
escape shorthands such as `\d` are part of this language. These constructs are
rejected when syntactically recognizable. Use actual bytes for newline/tab.

Limits are explicit: 65,535 pattern bytes, 512 syntax nodes and 4,096 NFA states
in the default instance, repetition bounds 0..255, and 65,536 compiler node
expansions. `Compile_Status` distinguishes syntax, pattern, node, state, and
expansion errors. Failure leaves an invalid program; its partial instructions
cannot be used for matching. Repetition is expanded during compilation, so
state use depends on expanded pattern size. Nested empty repetitions are also
bounded by the separate compiler work budget.

The simulator performs at most one visit per state in each epsilon closure,
using generation-stamped sparse sets whose dense lists also serve as worklists.
Sets are initialized once per match; advancing their generation empties them
without clearing arrays. Byte transitions and acceptance checks visit only the
active dense prefix. Matching uses O(compiled states) workspace and
O((text length + 1) * compiled states) worst-case time.
Each closure processes at most the compiled state count. Generations follow
text offsets and cannot wrap within a call. Search injects the start state at
each position, with no backtracking. [Measurements](BENCHMARKS.md) cover
sparse searches, wide active sets, and short records, including their tradeoffs.

## CLI

`bin/spark-grep [OPTIONS] PATTERN [FILE ...]` reads stdin when files are omitted;
`-` names stdin. Supported flags can be combined:

- `-E` extended regex (default), `-F` literal text, `-e PATTERN` (one pattern).
- `-n` record numbers, `-v` invert, `-x` whole-record matching.
- `-c` selected-record counts, `-l` matching filenames, `-q` quiet/early exit.
- `-h` suppress filename prefixes, `-H` force them, `-z` NUL-delimited records.
- `--`, `--help`, `--version`.

Unknown flags fail with status 2 and an error naming the option. Exit status
is 0 for selected records, 1 for none, 2 for errors encountered. Quiet takes
precedence over listing, which takes precedence over counting. Files after a
quiet match are not opened. Multiple files otherwise continue after read/open
errors. Missing final record delimiters are accepted; selected records are
printed with a delimiter. Empty input has no records. Counts and filename lists
end in newline even with `-z`. NUL/CR bytes are preserved; there is no binary-file
heuristic. Literal mode escapes a single pattern and uses the same budgets.

### Recursive search

`bin/spark-rg [OPTIONS] PATTERN [PATH ...]` searches directories itself instead
of being handed a file list, in the manner of ripgrep. `PATH` defaults to the
current directory; a `PATH` naming a file is searched directly, and `-` is
stdin. Directory entries are visited in sorted order, so output is reproducible.

By default it honours every `.gitignore` file it passes, skips `.git`, skips
names beginning with a dot, skips files with a NUL byte near the start, and does
not descend through symbolic links. Filenames and record numbers are shown, as a
recursive search reports matches from many files.

- All of `spark-grep`'s flags, plus `-N` to drop record numbers, which are on
  by default here.
- `-g GLOB` restricts paths, repeatable; a leading `!` excludes. Globs are
  matched against the path as it is reported.
- `--no-ignore`, `--hidden`, `-L`/`--follow`, `--binary` each turn off one of
  the defaults above; `--max-depth N` bounds traversal as ripgrep counts it,
  with zero visiting nothing.

Ignore handling covers nested `.gitignore` files, `!` negation, last-rule-wins
ordering, anchoring by an interior separator, directory-only `/` rules, `**`
segments, character classes and escaped blanks. Ignore globs are translated into
this library's own pattern language and matched by the proved engine, so no
second matching implementation exists to disagree with the first; only the
translation has to be trusted. Untranslatable or oversized rules are reported on
stderr and skipped, costing precision rather than the traversal. Global excludes,
`core.excludesFile` and `.git/info/exclude` are not consulted; like ripgrep,
neither is the index, so a tracked file matching an ignore rule is still
skipped. Because a compiled program is dominated by a per-instruction byte set, glob
rules use a much smaller storage budget than the default instance; that
instantiation, like all CLI code, is outside the proof run.

The unproved `common/spark_cli` library provides streaming byte-record framing
with early stop and dynamically growing record storage. It is separately
consumable; the regex kernel does not depend on it. The CLI is deliberately a
named subset, not a drop-in GNU grep or ripgrep replacement.

## Verification

Proof covers absence of runtime errors, initialization, global
dependencies, and termination for the complete default `Regex` instance.
The functional proof establishes exact byte transitions, epsilon-closure
soundness and completeness, and equivalence of `Search` and `Full_Match` to
the declarative `NFA_Accepts` model. Compile status agrees with validity;
instruction targets stay inside the compiled prefix; recursive compilation
preserves existing instructions; invalid programs reject input.

The tree compiler is also proved sound and complete: successful compilation
preserves the independent tree-span semantics for every constructor, including
nullable repetition and absolute anchors. Lexical scanners prove acceptance,
rejection and exact token contents. Successful parsing now proves a derivation
in an independent expression grammar, and the composed theorem connects that
derived tree to executable matching. Parser completeness also proves that a
pattern with a grammar derivation cannot produce a syntax error, with resource
failures allowed separately. Every derivation has the same span semantics as
the byte-only `Pattern_Matches` denotation. The public `Compile_For_Text`
theorem connects successful compilation to `Pattern_Accepts` for whole matching
and search. [PROOF.md](PROOF.md) states the theorems and proof boundary.

Recursive semantic models and proof certificates use SPARK's `Static` ghost
level. They are proved but never executed, including in contract-enabled
builds; ordinary executable contracts remain enabled there. The generic body
is checked through the default instance: custom instantiations need their own
GNATprove run. CLI code, shared I/O and the recursive walker are outside SPARK.

`tests/test_regex.adb` exercises default invalid programs, arbitrary/high string
bounds, empty/nullable cycles, all 256 bytes through escaped/negated classes and
dot, anchored nullable cycles, repetitions, and worklist/capacity limits.
`tests/test_cli.py` deterministically compares 290 fixed/generated patterns in
both search and whole-record modes against Python `re` and GNU `grep -aE` in
locale C, and checks CLI output, statuses, framing and malformed inputs. It
also exercises adversarial nonmatching input. Tests require Python 3 and GNU
grep. Differential tests establish agreement on that corpus, not complete
POSIX compatibility or a proof of parsing/compilation semantics.
