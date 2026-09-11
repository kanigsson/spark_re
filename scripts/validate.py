#!/usr/bin/env python3
"""Run the complete validation sequence serially and retain attributable logs."""
import hashlib
import json
from pathlib import Path
import re
import subprocess
import time

root = Path(__file__).resolve().parents[1]
out = root / 'validation' / time.strftime('%Y%m%dT%H%M%SZ', time.gmtime())
out.mkdir(parents=True)
files = sorted(p for d in ['src', 'cli', 'common', 'tests']
               for p in (root / d).rglob('*') if p.is_file() and '__pycache__' not in str(p))
receipt = {'source_sha256': {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest()
                             for p in files}, 'commands': []}
for target in ['test', 'test-contracts', 'flow', 'prove']:
    start = time.monotonic()
    result = subprocess.run(['make', target], cwd=root, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, text=True)
    (out / f'{target}.log').write_text(result.stdout)
    receipt['commands'].append({'command': ['make', target], 'exit_status': result.returncode,
                                 'seconds': round(time.monotonic() - start, 3)})
    print(f'make {target}: exit {result.returncode}', flush=True)
    if target == 'prove':
        match = re.search(r'Success: all checks proved \((\d+) checks\)', result.stdout)
        receipt['proved_checks'] = int(match[1]) if match else None
    (out / 'summary.json').write_text(json.dumps(receipt, indent=2) + '\n')
    if result.returncode:
        raise SystemExit(f'Validation failed; see {out}')
if receipt.get('proved_checks') is None:
    raise SystemExit(f'Missing proof success summary; inspect {out}')
print(out)
