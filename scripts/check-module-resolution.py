#!/usr/bin/env python3
"""Reject comparator module collisions in Lake's ordered source search path.

Palomar resolves source files before compilation. In particular, an imported
dependency may provide its own generic Challenge/Solution modules. This check
requires the configured modules to resolve uniquely to this project's files.
"""
import json
import os
from pathlib import Path
import re
import subprocess

root = Path(__file__).resolve().parents[1]
config = json.loads((root / 'comparator.json').read_text())
result = subprocess.run(
    ['lake', 'env', 'printenv', 'LEAN_SRC_PATH'], cwd=root,
    capture_output=True, text=True, check=True,
)
lines = [line.strip() for line in result.stdout.splitlines() if line.strip()]
if not lines:
    raise SystemExit('Lake did not report LEAN_SRC_PATH')
roots = [(root / item).resolve() for item in lines[-1].split(os.pathsep) if item]
for key in ['challenge_module', 'solution_module']:
    module = config[key]
    if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*", module):
        raise SystemExit(f'Invalid module name: {module!r}')
    suffix = Path(*module.split('.')).with_suffix('.lean')
    expected = (root / suffix).resolve()
    found = list(dict.fromkeys(
        (directory / suffix).resolve() for directory in roots
        if (directory / suffix).is_file()
    ))
    if found != [expected]:
        raise SystemExit(f'{module}: expected only {expected}, found {found}')
    print(f'{module}: uniquely resolves to {expected.relative_to(root)}')
