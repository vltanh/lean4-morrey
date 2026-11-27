#!/usr/bin/env python3
"""Exact 5/7-variable QF_NRA support-infeasibility query for rational p>=4.

Assume F(A)=||A||op^p h(det A/||A||op^2) is nonnegative and
globally rank-one convex. SAT means F is NOT globally polyconvex;
UNSAT from a sound complete exact QE/CAD solver means globally PC.
The mathematical support/Helly reduction is documented separately.
This tool only GENERATES the query. No solver is bundled.
"""
from fractions import Fraction as Q
from pathlib import Path
import json,sys

def lit(q):
    q=Q(q); n=str(abs(q.numerator))
    if q.denominator!=1:n='(/ '+n+' '+str(q.denominator)+')'
    return '(- '+n+')' if q<0 else n
def add(*x):return '(+ '+' '.join(x)+')'
def mul(*x):return '(* '+' '.join(x)+')'
def sub(x,y):return '(- '+x+' '+y+')'
def powi(x,n):return mul(*([x]*n)) if n>0 else '1'
def horner(a,x):
    z=lit(a[-1])
    for c in a[-2::-1]:z=add(lit(c),mul(x,z))
    return z

def gen(p,h):
    m,n=p.numerator,p.denominator
    h1=tuple(Q(i)*h[i] for i in range(1,len(h))) or (Q(0),)
    H='(h t)';M='(dh t)';P=lit(p)
    Lnum=sub(mul(add('1','t'),M),mul(P,H))
    Unum=add(mul(P,H),mul(sub('1','t'),M))
    support=[];lookup={}
    for j in ('1','2'):
        a,s,v='a'+j,'s'+j,'v'+j
        power=powi(a,m) if n==1 else v
        support += [f'(declare-const {x} Real)' for x in ((a,s) if n==1 else (a,s,v))]
        K=mul(sub(a,'1'),sub('t',mul(a,s)))
        A=add(mul(power,f'(h {s})'),mul(sub(P,'1'),H),
              mul('(- 1)',a,add(mul(P,H),mul(M,sub(s,'t')))))
        support += [f'(assert (>= {a} 0))',
                    f'(assert (<= (- 1) {s}))',f'(assert (<= {s} 1))']
        if n!=1:
            support += [f'(assert (>= {v} 0))',
                        f'(assert (= {powi(v,n)} {powi(a,m)}))']
        lookup['K'+j]=K;lookup['A'+j]=A
    k1,k2=lookup['K1'],lookup['K2']
    a1,a2=lookup['A1'],lookup['A2']
    fails=[
        f'(and (= {k1} 0) (< {a1} 0))',
        f"(and (> {k1} 0) (> {mul('(- 1)',a1,add('1','t'))} {mul(k1,Unum)}))",
        f"(and (< {k1} 0) (> {mul('(- 1)',a1,sub('1','t'))} {mul(k1,Lnum)}))",
        f'(and (> {k1} 0) (< {k2} 0) (> {mul(a1,k2)} {mul(a2,k1)}))',
        f'(< {sub(mul(P,H),mul("2","t",M))} 0)'
    ]
    lines=['(set-logic QF_NRA)',
           '(define-fun h ((r Real)) Real '+horner(h,'r')+')',
           '(define-fun dh ((r Real)) Real '+horner(h1,'r')+')',
           '(declare-const t Real)',
           '(assert (< (- 1) t))','(assert (< t 1))']
    lines+=support
    lines+=['(assert (or']+['  '+z for z in fails]+['))','(check-sat)']
    return '\n'.join(lines)+'\n'

if __name__=='__main__':
    if len(sys.argv)!=3:raise SystemExit(__doc__)
    obj=json.loads(Path(sys.argv[1]).read_text())
    p=Q(str(obj['p']));h=tuple(Q(str(x)) for x in obj['h'])
    if p<4 or not h:raise ValueError('p>=4 and polynomial h required')
    text=gen(p,h)
    assert text.count('(')==text.count(')')
    Path(sys.argv[2]).write_text(text)
    print('Generated',len(text),'bytes; 5 reals for integer p, 7 otherwise')
    print('SAT refutes PC; UNSAT proves PC only after independent nonnegative/RC checks.')
