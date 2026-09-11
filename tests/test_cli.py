"""Deterministic differential tests: independent Python re and GNU grep -E."""
import itertools
import os
from pathlib import Path
import random
import re
import subprocess
import tempfile

BIN = os.environ.get('SPARK_GREP', 'bin/spark-grep')
ENV = dict(os.environ, LC_ALL='C')
checks = 0

def run(args, data=b'', binary=BIN):
    return subprocess.run([binary, *args], input=data, capture_output=True,
                          env=ENV, timeout=15)

def check(args, data, output, status):
    global checks
    p = run(args, data)
    assert (p.returncode, p.stdout) == (status, output), (args, p, output, status)
    checks += 1

texts = [''.join(x) for n in range(6) for x in itertools.product('ab', repeat=n)]
texts += ['c', 'abc', 'xyz', '123', ']-', 'a.b', 'A', '\r']
data = ('\n'.join(texts) + '\n').encode()
patterns = ['', 'a', '.', '^$', '^a', 'a$', 'a|b', '(ab|a)*b', '(a*)*',
            '(a?)*', '((a|)*)*b', '()', '|', 'a|', '|a', 'a||b',
            '[a-b]+', '[^a-b]*', '[]-]+', '[-ab]', '[a-]', '\\.',
            'a{0}', 'a{2}', 'a{0,3}', 'a{2,}', '(ab|a){1,3}', 'a^', '$a',
            '(^|a)*b$', '(^$)*', '(a|$)*', 'a($|b)*', '($a|^b)*',
            '($a|^b)+', '(a?|b?)*c', '((^|$)|())*a', '(|a)',
            '((a?|^)|($|b?))*', '((a?|^)|($|b?))*a$']
rng = random.Random(20260911)
def expression(depth):
    if depth == 0:
        return rng.choice(['a', 'b', '.', '[ab]', '[^a]', '()'])
    x = expression(depth - 1)
    return rng.choice([f'({x})*', f'({x})+', f'({x})?', f'({x}){{0,2}}',
                       f'({x}|{expression(depth - 1)})', x + expression(depth - 1)])
patterns += [expression(3) for _ in range(250)]
for pattern in patterns:
    for whole in [False, True]:
        flags = ['-x'] if whole else []
        predicate = re.compile(pattern).fullmatch if whole else re.compile(pattern).search
        expected = ''.join(t + '\n' for t in texts if predicate(t) is not None).encode()
        check([*flags, '-e', pattern], data, expected, 0 if expected else 1)
        reference = run(['-aE', *flags, '-e', pattern], data, 'grep')
        assert (reference.returncode, reference.stdout) == (0 if expected else 1, expected), pattern
        checks += 1

for pattern in ['(', ')', '[', '[z-a]', 'a{', 'a{256}', 'a{2,1}', '*',
                'a**', 'a+?', '\\1', '(?=a)', '[[:alpha:]]', '\\d', '\\', 'a}']:
    p = run(['-e', pattern], data)
    assert p.returncode == 2 and p.stderr and not p.stdout, (pattern, p)
    checks += 1
for args in [['-P', 'a'], ['--unknown', 'a'], ['-i', 'a'], [], ['-e'], ['-e', 'a', '-e', 'b']]:
    p = run(args)
    assert p.returncode == 2 and p.stderr, (args, p)
    checks += 1
check(['-nv', 'a'], b'a\nb\n\nlast', b'2:b\n3:\n', 0)
check(['-c', 'a'], b'a\nb\na', b'2\n', 0)
check(['-q', 'a'], b'a\nb', b'', 0)
check(['-q', 'x'], b'a\nb', b'', 1)
check(['-F', 'a.b'], b'axb\na.b', b'a.b\n', 0)
check(['--', '-a'], b'-a\nb\n', b'-a\n', 0)
check(['-z', '^a.*b$'], b'a\nb\0abc\0', b'a\nb\0', 0)
check(['.', '-'], b'\0\r\n', b'\0\r\n', 0)
check([''], b'', b'', 1)
check([''], b'\n', b'\n', 0)
check(['a'], b'a' * 150000, b'a' * 150000 + b'\n', 0)
check(['(a|aa)*b'], b'a' * 10000 + b'\n', b'', 1)
with tempfile.TemporaryDirectory() as directory:
    a, b = (Path(directory) / x for x in ['a', 'b'])
    a.write_bytes(b'aa\nbb')
    b.write_bytes(b'ab\n')
    check(['-n', 'a', str(a), str(b)], b'', f'{a}:1:aa\n{b}:1:ab\n'.encode(), 0)
    check(['-hc', 'a', str(a), str(b)], b'', b'1\n1\n', 0)
    check(['-l', 'a', str(a), str(b)], b'', f'{a}\n{b}\n'.encode(), 0)
    p = run(['a', str(a) + '.missing', str(b)])
    assert p.returncode == 2 and p.stderr and p.stdout == f'{b}:ab\n'.encode()
    checks += 1
print(f'PASS: {checks} differential and CLI checks ({len(patterns)} patterns)')
