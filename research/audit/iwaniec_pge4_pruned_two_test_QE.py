#!/usr/bin/env python3
"""Generate only the three possible support-failure cases under verified RC.

Reads the original exact generator and drops the two impossible disjuncts
using the structural theorem in the companion note. This is not a
standalone PC oracle: first verify F>=0 and globally RC.
"""
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parent))
from iwaniec_pge4_two_test_QE import gen
from fractions import Fraction as Q
import json

def pruned(p,h):
    full=gen(p,h)
    lines=full.splitlines()
    start=lines.index('(assert (or')
    end=lines.index('))',start)
    clauses=lines[start+1:end]
    assert len(clauses)==5,clauses
    # Original cases: K=0, lower>U, upper<L, pair conflict, empty interval.
    kept=clauses[1:4]
    return '\n'.join(lines[:start+1]+kept+lines[end:])+'\n'

def check():
    for p,h in [(Q(4),(Q(1),)),(Q(9,2),(Q(2),Q(0),Q(2),Q(0),Q(1)))]:
        f=pruned(p,h)
        assert f.count('(')==f.count(')')
        assert '(assert (or' in f
        assert '(and (= ' not in f
        assert f.count('\n  (and ') == 3
    print('PASS: three exact obstruction branches for integer and rational p')

if __name__=='__main__':
    if len(sys.argv)==1:check()
    elif len(sys.argv)==3:
        obj=json.loads(Path(sys.argv[1]).read_text())
        p=Q(str(obj['p']));h=tuple(Q(str(z)) for z in obj['h'])
        if p<4 or not h:raise ValueError('rational p>=4, polynomial h required')
        Path(sys.argv[2]).write_text(pruned(p,h))
        print('Wrote pruned formula; REQUIRES independently verified RC and F>=0')
    else:raise SystemExit('usage: script [input.json output.smt2]')
