# Spark RE

An allocation-free, byte-oriented Thompson NFA regex library in Ada/SPARK,
with an ordinary Ada `spark-grep` CLI. The library has no I/O or dependencies.

## Build and use

Use a matching Ada 2022 GNAT/GPRbuild and GNATprove installation.

```sh
make test                 # library tests, Python re and grep -E oracles
make test-contracts       # same tests with executable library contracts
make flow                 # initialization and dependency analysis
make prove                # runtime safety and termination
make format
printf '%s\n' src/foo.adb src/bar.ads | bin/spark-grep '\.adb$'
bin/spark-grep -n 'procedure|function' src/*.ad?
```

As in `fuzzy_matcher`, `spark_re.gpr` builds the static library alone;
`tools.gpr` builds the CLI and tests. `alire.toml` publishes the library alone.
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
Matching uses bounded local state arrays. No heap allocation occurs in the
library. Account for this automatic storage on small-stack targets.
Patterns and text may have arbitrary String lower bounds, including a final
index equal to `Integer'Last`. Search accepts any substring, including an empty
one; `Full_Match` requires the whole string. Anchors always refer to the whole
input. An invalid/default-initialized program never matches.

## Pattern language

Supported syntax:

| Syntax | Meaning |
| --- | --- |
| `abc`, `a\|b` | literal bytes (escape punctuation to make it literal) |
| `.`, `[abc]`, `[a-z]`, `[^a-z]` | any byte; sets, inclusive byte ranges, negation |
| `(ab)`, `a|b` | grouping, alternation |
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
using a visited set and linked worklist. It uses O(state capacity) workspace
and O((text length + 1) * compiled state count) time, with no backtracking.
Search injects the start state at each position in the same simulation.

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

The unproved `common/spark_cli` library provides streaming byte-record framing
with early stop and dynamically growing record storage. It is separately
consumable; the regex kernel does not depend on it. Existing fuzzy matcher
sources and their build remain untouched. The CLI is deliberately a named
subset, not a drop-in GNU grep or ripgrep replacement.

## Verification

The initial Silver milestone proves absence of runtime errors, initialization,
global dependencies, and termination for the complete default `Regex` instance.
The generic body is checked through that instance: custom instantiations need
their own GNATprove run. CLI and shared I/O code are outside SPARK.

`tests/test_regex.adb` exercises default invalid programs, arbitrary/high string
bounds, empty/nullable cycles, classes, anchors, repetitions and capacity limits.
`tests/test_cli.py` deterministically compares 279 fixed/generated patterns in
both search and whole-record modes against Python `re` and GNU `grep -aE` in
locale C, and checks CLI output, statuses, framing and malformed inputs. It
also exercises adversarial nonmatching input. Tests require Python 3 and GNU
grep. Differential tests establish agreement on that corpus, not complete
POSIX compatibility or a proof of parsing/compilation semantics.

See `VERIFICATION.md` for milestone evidence and the precise proof scope.
