"""Differential tests for the recursive walker: ripgrep and git are oracles."""
import os
from pathlib import Path
import random
import shutil
import subprocess
import tempfile

BIN = os.path.abspath(os.environ.get('SPARK_RG', 'bin/spark-rg'))
ENV = dict(os.environ, LC_ALL='C')
RG = shutil.which('rg')
GIT = shutil.which('git')
checks = 0

NEEDLE = 'needle\n'

def run(args, cwd, data=b'', binary=BIN):
    return subprocess.run([binary, *args], input=data, capture_output=True,
                          env=ENV, cwd=cwd, timeout=30)

def lines(out):
    return sorted(x for x in out.decode().split('\n') if x)

def make_tree(root, files, ignores):
    for name in files:
        path = Path(root) / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(NEEDLE)
    for where, text in ignores.items():
        path = Path(root) / where / '.gitignore'
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)

def compare(files, ignores, flags=(), label=''):
    """spark-rg must select exactly the files ripgrep selects."""
    global checks
    with tempfile.TemporaryDirectory() as root:
        make_tree(root, files, ignores)
        subprocess.run([GIT, 'init', '-q', '.'], cwd=root, check=True)
        mine = run(['-l', *flags, 'needle', '.'], root)
        theirs = subprocess.run([RG, '-l', *flags, 'needle', '.'],
                                capture_output=True, env=ENV, cwd=root,
                                timeout=30)
        got = lines(mine.stdout)
        want = [x[2:] if x.startswith('./') else x for x in lines(theirs.stdout)]
        assert got == sorted(want), (label, flags, got, sorted(want), ignores)
        assert mine.returncode == (0 if got else 1), (label, mine)
        checks += 1

def check(args, files, ignores, expected, status, data=b''):
    global checks
    with tempfile.TemporaryDirectory() as root:
        make_tree(root, files, ignores)
        p = run(args, root, data)
        assert (p.returncode, lines(p.stdout)) == (status, sorted(expected)), \
            (args, p, expected, status)
        checks += 1

TREE = ['src/a.adb', 'src/deep/b.ads', 'build/gen.adb', 'vendor/skip.txt',
        'vendor/keep/important.txt', 'node_modules/x.js', 'top.o', 'keep.md',
        'a/b/c/f.txt', 'a/b/f.log', 'doc/readme.md', 'doc/img/p.png',
        'x/y/z.tmp', 'sp ace/s.txt', 'A1/q.c', 'deep/1/2/3/deep.txt',
        'root.log', 'a.o', 'ab.o', 'abc.o', '.dotfile', '.dotdir/inner.txt']

IGNORE_CASES = [
    '',
    '*.o\n',
    '# comment\n\n*.o\nbuild/\nnode_modules\nvendor/*\n!vendor/keep/\n',
    '*.log\n!root.log\n',
    'doc/**/*.png\n',
    'a/**/c/\n',
    '**/deep.txt\n',
    '/keep.md\n',
    '/keep.md\n!/keep.md\n',
    'sp\\ ace/\n',
    '[ab].o\n',
    '?bc.o\n',
    '[!a]bc.o\n',
    'src\n',
    'src/\n',
    '/src/deep\n',
    '*\n!*.adb\n',
    '**\n',
    'doc/**\n',
    'a/**/f.txt\n',
    '*.o   \n',
    'x/y/\n',
    '.dotfile\n',
]

if not (RG and GIT):
    raise SystemExit('test_rg.py needs ripgrep and git as oracles')

for text in IGNORE_CASES:
    for flags in [(), ('--hidden',), ('--no-ignore',), ('--hidden', '--no-ignore')]:
        compare(TREE, {'': text}, flags, label=repr(text))

# Nested ignore files: the nearer file overrides the more distant one.
for outer, inner in [('*.txt\n', '!f.txt\n'), ('*\n', '!*.log\n'),
                     ('a/b/c/\n', '!c/\n'), ('', '*.txt\n')]:
    compare(TREE, {'': outer, 'a/b': inner}, label=f'{outer!r}/{inner!r}')

for depth in range(5):
    compare(TREE, {'': '*.o\n'}, ('--max-depth', str(depth)))

rng = random.Random(20260914)
ALPHABET = ['*.o', '*.log', 'src', 'src/', '/src', 'doc/**', '**/deep.txt',
            'a/**/c', '!*.adb', '!root.log', '[ab].o', '?bc.o', 'x/y/*.tmp',
            '*', '!*.md', 'vendor/*', '!vendor/keep/', '**/b.ads', 'A?/']
for _ in range(60):
    text = '\n'.join(rng.sample(ALPHABET, rng.randint(1, 5))) + '\n'
    compare(TREE, {'': text}, label=repr(text))

# Output shapes, exit statuses and flag interactions.
SMALL = {'': '*.o\n'}
check(['-l', 'needle', '.'], ['f.txt', 'd/g.txt', 'skip.o'], SMALL,
      ['d/g.txt', 'f.txt'], 0)
check(['needle', '.'], ['f.txt'], SMALL, ['f.txt:1:needle'], 0)
check(['-N', 'needle', '.'], ['f.txt'], SMALL, ['f.txt:needle'], 0)
check(['-h', 'needle', '.'], ['f.txt'], SMALL, ['1:needle'], 0)
check(['-hN', 'needle', '.'], ['f.txt'], SMALL, ['needle'], 0)
check(['-c', 'needle', '.'], ['f.txt'], SMALL, ['f.txt:1'], 0)
check(['-q', 'needle', '.'], ['f.txt'], SMALL, [], 0)
check(['-q', 'missing', '.'], ['f.txt'], SMALL, [], 1)
check(['-l', 'missing', '.'], ['f.txt'], SMALL, [], 1)
check(['-vN', 'needle', '.'], ['f.txt'], SMALL, [], 1)
check(['-x', 'needle', '.'], ['f.txt'], SMALL, ['f.txt:1:needle'], 0)
check(['-xN', 'need', '.'], ['f.txt'], SMALL, [], 1)
check(['-F', 'needle', '.'], ['f.txt'], SMALL, ['f.txt:1:needle'], 0)
check(['-e', 'needle', '.'], ['f.txt'], SMALL, ['f.txt:1:needle'], 0)
check(['-l', '-g', '*.txt', 'needle', '.'], ['f.txt', 'g.md'], {}, ['f.txt'], 0)
check(['-l', '-g', '!*.txt', 'needle', '.'], ['f.txt', 'g.md'], {}, ['g.md'], 0)
check(['-l', '-g', 'd/**', 'needle', '.'], ['f.txt', 'd/g.md'], {}, ['d/g.md'], 0)
check(['-l', 'needle', 'src'], ['src/f.txt', 'g.txt'], {}, ['src/f.txt'], 0)
check(['-n', 'needle', 'src/f.txt'], ['src/f.txt'], {}, ['src/f.txt:1:needle'], 0)
check(['-n', 'needle', '-'], [], {}, ['(standard input):1:needle'], 0,
      data=b'needle\n')
check(['-l', '--hidden', 'needle', '.'], ['.x/f.txt'], {}, ['.x/f.txt'], 0)
check(['-l', 'needle', '.'], ['.x/f.txt'], {}, [], 1)

# Binary files are skipped unless asked for, as in ripgrep.
with tempfile.TemporaryDirectory() as root:
    (Path(root) / 'b.bin').write_bytes(b'needle\n\x00more\n')
    (Path(root) / 't.txt').write_text(NEEDLE)
    assert lines(run(['-l', 'needle', '.'], root).stdout) == ['t.txt']
    assert lines(run(['-l', '--binary', 'needle', '.'], root).stdout) == \
        ['b.bin', 't.txt']
    checks += 2

# Symbolic links are not followed without --follow, so cycles terminate.
with tempfile.TemporaryDirectory() as root:
    (Path(root) / 'd').mkdir()
    (Path(root) / 'd' / 'f.txt').write_text(NEEDLE)
    os.symlink(root, Path(root) / 'd' / 'loop')
    assert lines(run(['-l', 'needle', '.'], root).stdout) == ['d/f.txt']
    p = run(['-l', '--follow', '--max-depth', '4', 'needle', '.'], root)
    assert p.returncode == 0 and 'd/f.txt' in lines(p.stdout)
    checks += 2

# Unknown options and missing patterns are errors, as in spark-grep.
for args in [['-Z', 'a', '.'], [], ['-e'], ['--max-depth'], ['--max-depth', 'x', 'a', '.']]:
    with tempfile.TemporaryDirectory() as root:
        p = run(args, root)
        assert p.returncode == 2 and p.stderr, (args, p)
        checks += 1

# Unreadable directories are reported but do not end the search.
with tempfile.TemporaryDirectory() as root:
    (Path(root) / 'ok.txt').write_text(NEEDLE)
    closed = Path(root) / 'closed'
    closed.mkdir()
    (closed / 'hidden.txt').write_text(NEEDLE)
    closed.chmod(0o000)
    try:
        p = run(['-l', 'needle', '.'], root)
        assert lines(p.stdout) == ['ok.txt'] and p.stderr, p
        checks += 1
    finally:
        closed.chmod(0o755)

print(f'PASS: {checks} walker checks against ripgrep and git')
