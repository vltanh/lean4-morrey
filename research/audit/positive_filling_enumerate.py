#!/usr/bin/env python3
"""Exact finite positive filling enumeration and optional laminate certificates.

Boundary expansion is exhaustive on the given rational vertex set. A failed
binary merge is not a counterexample to lamination or Morrey.
"""
import argparse,json,time
from collections import defaultdict
from fractions import Fraction as Q
from functools import lru_cache
from pathlib import Path
from joint_positive_filling import triangles,make_input,check_boundary,rat,det


def edge_terms(t):
    a,b,c=t
    return tuple(((i,j),s) if i<j else ((j,i),-s) for i,j,s in ((b,c,1),(a,c,-1),(a,b,1)))


def overlap(T,U):
    # Separating-axis theorem for full-dimensional triangles, exact rational.
    for P in (T,U):
        for a,b in zip(P,P[1:]+P[:1]):
            n=(b[1]-a[1],a[0]-b[0])
            p=[sum(x*y for x,y in zip(n,v)) for v in T]
            q=[sum(x*y for x,y in zip(n,v)) for v in U]
            if max(p)<=min(q) or max(q)<=min(p):return False
    return True


def enumerate_fillings(data):
    V,_,bd,ts=triangles(data);P=len({v[:2] for v in V});n=len(ts)
    projs=[tuple(V[i][:2] for i in t) for t,_,_ in ts]
    # Cache geometric conflict for repeated projected triangle directions.
    @lru_cache(None)
    def ov(T,U):return overlap(T,U)
    blocked=[1<<i for i in range(n)]
    for i in range(n):
        t=ts[i][0];h={V[j][:2]:j for j in t}
        for j in range(i):
            u=ts[j][0]
            if any(V[k][:2] in h and h[V[k][:2]]!=k for k in u) or ov(projs[i],projs[j]):
                blocked[i]|=1<<j;blocked[j]|=1<<i
    incidence=[edge_terms(t) for t,_,_ in ts]
    by_edge=defaultdict(int)
    for i,e in enumerate(incidence):
        for edge,s in e:by_edge[edge,s]|=1<<i
    full=(1<<n)-1;seen=set();outputs=[]
    def visit(mask,banned,residual,area,depth):
        if mask in seen:return
        seen.add(mask)
        if not residual:
            if area!=1:raise AssertionError('boundary area identity failed')
            outputs.append(mask);return
        if depth>=2*P-6 or area>=1:return
        available=full&~banned
        choices=None
        for e,v in residual.items():
            if abs(v)>1:return  # positive nonoverlapping triangles cannot repair a doubled directed edge
            can=available&by_edge[e,1 if v>0 else -1]
            if not can:return
            if choices is None or can.bit_count()<choices.bit_count():choices=can
        while choices:
            bit=choices&-choices;choices^=bit;i=bit.bit_length()-1
            _,ar,_=ts[i]
            if area+ar>1:continue
            r=residual.copy()
            for e,s in incidence[i]:
                r[e]=r.get(e,0)-s
                if not r[e]:del r[e]
            visit(mask|bit,banned|blocked[i],r,area+ar,depth+1)
    visit(0,0,{k:v for k,v in bd.items() if v},Q(0),0)
    return ts,outputs,len(seen)


def canonical(law):
    weights=defaultdict(Q)
    for w,X in law:weights[tuple(X)]+=w
    return tuple(sorted((X,w) for X,w in weights.items() if w))


def laminate_tree(law,max_states=20000):
    """Return a bottom-up merge sequence, or None. Sound, not complete for laminates."""
    start=canonical(law);seen=set()
    def visit(state):
        if len(state)==1:return []
        if state in seen or len(seen)>=max_states:return None
        seen.add(state)
        for i,(X,w) in enumerate(state):
            for j in range(i):
                Y,v=state[j]
                if det(tuple(x-y for x,y in zip(X,Y))):continue
                p=w+v;Z=tuple((w*x+v*y)/p for x,y in zip(X,Y))
                new=canonical([(u,T) for k,(T,u) in enumerate(state) if k!=i and k!=j]+[(p,Z)])
                trail=visit(new)
                if trail is not None:return [(X,Y,w,v)]+trail
        return None
    return visit(start)


def check_tree(law,steps):
    state=defaultdict(Q)
    for w,X in law:state[tuple(X)]+=w
    for X,Y,w,v in steps:
        X,Y=tuple(map(Q,X)),tuple(map(Q,Y));w,v=Q(w),Q(v)
        if X==Y or state[X]!=w or state[Y]!=v or w<=0 or v<=0 or det(tuple(x-y for x,y in zip(X,Y))):raise ValueError('invalid merge')
        del state[X];del state[Y];p=w+v
        Z=tuple((w*x+v*y)/p for x,y in zip(X,Y));state[Z]+=p
    if dict(state)!={(Q(0),)*4:Q(1)}:raise ValueError('merge did not finish at base')


def campaign(data,max_states=20000):
    t=time.monotonic();ts,outputs,states=enumerate_fillings(data);enum_time=time.monotonic()-t
    yes=0;bad=[];unique=set();trees={}
    for mask in outputs:
        I=[i for i in range(len(ts)) if mask>>i&1]
        law=[(ts[i][1],ts[i][2]) for i in I]
        # Each output is checked independently, with exact boundary incidence.
        faces=[list(ts[i][0]) for i in I]
        check_boundary(data,faces)
        key=canonical(law)
        if key in trees:tree=trees[key]
        else:tree=laminate_tree(law,max_states);trees[key]=tree
        if tree is not None:
            check_tree(law,tree);yes+=1
        else:
            bad.append({'faces':faces,'law':[[str(w),list(map(str,X))] for X,w in key]})
    report={'vertices':len(data['vertices']),'projected_vertices':len({tuple(v[:2]) for v in data['vertices']}),'candidate_triangles':len(ts),'partial_states':states,'fillings':len(outputs),'distinct_laws':len(trees),'exact_merge_certified_fillings':yes,'unclosed_fillings':len(bad),'unclosed_distinct_laws':sum(v is None for v in trees.values()),'enumeration_seconds':enum_time,'total_seconds':time.monotonic()-t,'scope':'Exact finite enumeration; successful merges certify all rank-one convex integrands, failures do not imply a violation.'}
    return report,bad

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--case',choices=['small','four']);p.add_argument('--input',type=Path);p.add_argument('--max-states',type=int,default=20000);p.add_argument('--report',type=Path);p.add_argument('--unclosed',type=Path);a=p.parse_args()
    data=json.loads(a.input.read_text()) if a.input else make_input(a.case or 'small')
    r,u=campaign(data,a.max_states);print(json.dumps(r,indent=2))
    if a.report:a.report.write_text(json.dumps(r,indent=2)+'\n')
    if a.unclosed:a.unclosed.write_text(json.dumps(u,indent=2)+'\n')
