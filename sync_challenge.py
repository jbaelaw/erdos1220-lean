#!/usr/bin/env python3
"""Generate (or --check) Erdos1220Challenge.lean from the library's statement definitions.

Part A of the Challenge must consist of declarations *identical* to the ones the Solution's
library defines (the comparator checks every constant occurring in the target statements), so it
is copied verbatim from:
  * Erdos1220.lean               -- IsOmegaInaccessible, PairArrow, Hypotheses, Problem1220
  * Erdos1220Full/Statement1220.lean -- leqF … Erdos1220 (the first-order sentence)
  * erdos501's Erdos501/FOL/Statement.lean (pinned dependency) -- the language L, the formula
    combinators, ZFC and zfsetStructure, restricted to the declarations used by #1220
    (the Erdos501 sentence and its helpers are omitted), so that the Challenge imports Mathlib only.
"""
import os
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent
HERE = Path(__file__).resolve().parent


def block(path, start_marker, end_marker):
    lines = (ROOT / path).read_text().splitlines()
    s = next(i for i, l in enumerate(lines) if l.startswith(start_marker))
    e = next(i for i, l in enumerate(lines) if i > s and l.startswith(end_marker))
    while lines[e - 1].strip() == '':
        e -= 1
    return '\n'.join(lines[s:e])


def erdos501_statement():
    cands = [os.environ.get('ERDOS501_STATEMENT', ''),
             str(ROOT / '.lake/packages/erdos501/Erdos501/FOL/Statement.lean')]
    for c in cands:
        if c and Path(c).exists():
            return Path(c).read_text().splitlines()
    raise SystemExit('erdos501 Statement.lean not found (set ERDOS501_STATEMENT)')


def cut(lines, start, end):
    s = next(i for i, l in enumerate(lines) if l.startswith(start))
    e = next(i for i, l in enumerate(lines) if i > s and l.startswith(end))
    while lines[e - 1].strip() == '':
        e -= 1
    return '\n'.join(lines[s:e])


def erdos501_parta():
    L = erdos501_statement()
    part1 = cut(L, '/-! ### The language `L`', '/-! ### The sentence `Erdos501`')
    appf = cut(L, '/-- `f(x) = y`, for a function', '/-- `op(x, y) = z`')
    isfun = cut(L, '/-- `f` is a (total, single-valued) function', '/-- `op` is a binary operation')
    zfset = cut(L, '/-! ### The standard interpretation', 'end Erdos501.FOL')
    return '\n\n'.join([part1, appf, isfun, zfset])


def render():
    problem = block('Erdos1220.lean', '/-- Closure below', '/-- The cardinal `ℵ_(𝔠⁺)`')
    sentence = block('Erdos1220Full/Statement1220.lean', '/-- `|A| ≤ |B|`',
                     '/-- **Target (headline)**')
    tmpl = (HERE / 'Erdos1220Challenge.template').read_text()
    return (tmpl.replace('@@PROBLEM1220@@', problem).replace('@@SENTENCE1220@@', sentence)
            .replace('@@ERDOS501_PARTA@@', erdos501_parta()))


if __name__ == '__main__':
    out = HERE / 'Erdos1220Challenge.lean'
    text = render()
    if '--check' in sys.argv:
        ok = out.exists() and out.read_text() == text
        print('Erdos1220Challenge.lean in sync' if ok else 'Erdos1220Challenge.lean OUT OF SYNC')
        sys.exit(0 if ok else 1)
    out.write_text(text)
    print('wrote', out)
