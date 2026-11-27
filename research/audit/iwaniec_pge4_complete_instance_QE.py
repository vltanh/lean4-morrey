#!/usr/bin/env python3
"""Exact QF_NRA decision queries for one rational p>=4 / polynomial isotropic F.

F(0)=0; F(A)=||A||op**p * h(det(A)/||A||op**2) for A!=0.
Run: python iwaniec_pge4_complete_instance_QE.py input.json output-dir
Produces three SMT-LIB2 existential queries. SAT/UNSAT are DECISIVE ONLY if
certified by a complete real-algebraic QE/CAD implementation; NO solver bundled.
A SAT polyconvexity witness is NOT a quasiconvexity counterexample.
"""
from fractions import Fraction as Q
from pathlib import Path
import json, sys

def qlit(x):
    x=Q(x); a=str(abs(x.numerator))
    if x.denominator>1:a=f'(/ {a} {x.denominator})'
    return f'(- {a})' if x<0 else a

def add(*xs):
    xs=[x for x in xs if x!='0']
    return '0' if not xs else xs[0] if len(xs)==1 else '(+ '+' '.join(xs)+')'

def prod(*xs):
    xs=[x for x in xs if x!='1']
    return '1' if not xs else xs[0] if len(xs)==1 else '(* '+' '.join(xs)+')'

def diff(x,y): return f'(- {x} {y})'
def pw(x,k): return prod(*([x]*k)) if k else '1'
def horner(coeffs,x):
    out=qlit(coeffs[-1])
    for c in reversed(coeffs[:-1]):out=add(prod(out,x),qlit(c))
    return out
def eq(x,y): return f'(= {x} {y})'
def ge(x,y): return f'(>= {x} {y})'
def le(x,y): return f'(<= {x} {y})'

def query(defs,varblocks,requirements):
    lines=['(set-logic QF_NRA)','(set-option :produce-models true)',defs]
    lines += varblocks
    lines += ['(assert (and']+['  '+a for a in requirements]+['))','(check-sat)']
    return '\n'.join(lines)+'\n'

class Model:
    def __init__(self,p,h):
        self.m,self.n=p.numerator,p.denominator
        self.defs=f'(define-fun h ((r Real)) Real {horner(h,"r")})'
    def var(self,x):return f'(declare-const {x} Real)'
    def scalar(self,key):
        s,r,v=[f'{z}{key}' for z in ('s','r','v')]
        con=[ge(s,'0'),ge(v,'0'),ge(r,'(- 1)'),le(r,'1'),
             eq(pw(v,2*self.n),pw(s,self.m))]
        return (s,r,v),con
    def diag(self,key):
        x,y=f'x{key}',f'y{key}'
        (s,r,v),con=self.scalar(key)
        x2,y2=pw(x,2),pw(y,2)
        con += [ge(s,x2),ge(s,y2),f'(or {eq(s,x2)} {eq(s,y2)})',
                eq(prod(s,r),prod(x,y))]
        return [self.var(z) for z in [x,y,s,r,v]],con,prod(v,f'(h {r})')
    def matrix(self,key):
        aa=[f'{z}{key}' for z in ('a','b','c','d')]
        (s,r,v),con=self.scalar(key)
        tr=add(*[pw(z,2) for z in aa])
        det=diff(prod(aa[0],aa[3]),prod(aa[1],aa[2]))
        con += [eq(add(pw(s,2),prod(qlit(-1),tr,s),pw(det,2)),'0'),
                ge(prod('2',s),tr),eq(prod(s,r),det)]
        return [self.var(z) for z in aa+[s,r,v]],con,prod(v,f'(h {r})'),det

def make_queries(p,h):
    model=Model(p,h)
    negative=query(model.defs,[model.var('r')],
                   [ge('r','(- 1)'),le('r','1'),'( < (h r) 0 )'])
    va,ca,ea,_=model.matrix('A'); vb,cb,eb,_=model.matrix('B')
    vc,cc,ec,_=model.matrix('C')
    t='tau';decl=va+vb+vc+[model.var(t)]
    cond=ca+cb+cc+[ge(t,'0'),le(t,'1')]
    for z in ('a','b','c','d'):
        cond.append(eq(f'{z}C',add(prod(diff('1',t),f'{z}A'),prod(t,f'{z}B'))))
    dx=[diff(f'{z}B',f'{z}A') for z in ('a','b','c','d')]
    cond.append(eq(diff(prod(dx[0],dx[3]),prod(dx[1],dx[2])),'0'))
    cond.append(f'(> {ec} {add(prod(diff("1",t),ea),prod(t,eb))})')
    non_rc=query(model.defs,decl,cond)
    atoms=[model.diag(i) for i in range(5)]
    variables=sum((e[0] for e in atoms),[])+[model.var(f'w{i}') for i in range(1,5)]
    req=sum((e[1] for e in atoms),[])+[ge(f'w{i}','0') for i in range(1,5)]
    req.append(eq(add(*[f'w{i}' for i in range(1,5)]),'1'))
    for name in ('x','y'):
        req.append(eq(add(*[prod(f'w{i}',f'{name}{i}') for i in range(1,5)]),f'{name}0'))
    req.append(eq(add(*[prod(f'w{i}',f'x{i}',f'y{i}') for i in range(1,5)]),prod('x0','y0')))
    req.append(f'(< {add(*[prod(f"w{i}",atoms[i][2]) for i in range(1,5)])} {atoms[0][2]})')
    non_pc=query(model.defs,variables,req)
    return {'negative.smt2':negative,
            'not_rank_one_convex.smt2':non_rc,
            'not_polyconvex.smt2':non_pc}

def main():
    if len(sys.argv)!=3:raise SystemExit(__doc__)
    obj=json.loads(Path(sys.argv[1]).read_text())
    p=Q(str(obj['p']));h=[Q(str(z)) for z in obj['h']]
    if p<4 or not h:raise ValueError('require rational p>=4 and nonempty h')
    out=Path(sys.argv[2]);out.mkdir(parents=True,exist_ok=True)
    for name,contents in make_queries(p,h).items():
        (out/name).write_text(contents)
        assert contents.count('(')==contents.count(')'),name
        print(name,len(contents),'bytes, balanced parentheses')
    print('SAT: exact algebraic failure witness; UNSAT: globally true for this input')
    print('A complete, sound QE/CAD solver is required; none is bundled.')

if __name__=='__main__':main()
