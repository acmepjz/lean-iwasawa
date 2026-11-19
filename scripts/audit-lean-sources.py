#!/usr/bin/env python3
"""Audit repository Lean sources and Solution's transitive source imports."""
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parent.parent

def strip_comments(text):
    out = []
    i = depth = 0
    while i < len(text):
        if text.startswith('/-', i):
            depth += 1
            out.append(' ')
            i += 2
        elif depth and text.startswith('-/', i):
            depth -= 1
            i += 2
        elif not depth and text.startswith('--', i):
            end = text.find('\n', i)
            i = len(text) if end < 0 else end
        else:
            if not depth or text[i] == '\n':
                out.append(text[i])
            i += 1
    return ''.join(out)

def audit(path):
    source = path.read_text()
    code = strip_comments(source)
    return {'path': str(path.relative_to(ROOT)), 'lines': len(source.splitlines()),
            'module': bool(re.match(r'\s*module\b', code)), 'symlink': path.is_symlink()}

files = subprocess.check_output(['git', 'ls-files', '--cached', '--others', '--exclude-standard',
                                 '*.lean'], cwd=ROOT, text=True).splitlines()
rows = [audit(ROOT / name) for name in sorted(set(files))]
bad = [r for r in rows if r['symlink'] or r['lines'] > 10000 or
       (not r['module'] and Path(r['path']).name != 'lakefile.lean')]
search = [ROOT / 'IwasawalibCFT', ROOT]
search += sorted((ROOT / '.lake/packages').iterdir())
seen, unresolved, todo = {}, [], ['Solution']
while todo:
    name = todo.pop()
    if name in seen:
        continue
    suffix = Path(*name.split('.')).with_suffix('.lean')
    path = next((base / suffix for base in search if (base / suffix).is_file()), None)
    if path is None:
        if not name.startswith(('Init', 'Lean', 'Std', 'Lake')):
            unresolved.append(name)
        continue
    row = audit(path)
    seen[name] = row
    code = strip_comments(path.read_text())
    todo.extend(re.findall(r'^\s*(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?([\w.]+)', code, re.M))
closure_bad = [r for r in seen.values() if not r['module'] or r['lines'] > 10000 or r['symlink']]
result = {'repository_files': len(rows), 'largest_repository_file': max(rows, key=lambda r:r['lines']),
          'repository_violations': bad, 'solution_import_files': len(seen),
          'solution_import_violations': closure_bad, 'unresolved_noncore_imports': unresolved}
print(json.dumps(result, indent=2))
raise SystemExit(bool(bad or closure_bad or unresolved))
