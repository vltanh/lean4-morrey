#!/usr/bin/env python3
"""Exact rational lower-bound certificates for a finite joint-filling model.

Floating HiGHS duals suggest certificates. Replay checks every arithmetic
bound and disjunction with fractions; it never calls a numerical solver.
"""
import argparse, json, time
from fractions import Fraction as Q
from pathlib import Path
from collections import defaultdict
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix, hstack, csc_matrix
from joint_positive_filling import model,make_input,rat


def standard_rows(m):
    rows=[];rhs=[]
    for a,l,u in m['rows'].exact:
        if u is not None:rows.append(a);rhs.append(u)
        if l is not None:rows.append({j:-v for j,v in a.items()});rhs.append(-l)
    return rows,rhs


def lagrangian(rows,rhs,obj,lo,hi,multipliers,phase=False):
    """Exact lower bound from arbitrary nonpositive inequality multipliers."""
    r=list(obj);constant=Q(0);sum_y=Q(0);seen=set()
    for i,y in multipliers:
        if type(i)!=int or i in seen or not 0<=i<len(rows):raise ValueError('invalid dual row index')
        seen.add(i);y=rat(y)
        if y>0:raise ValueError('dual multiplier must be nonpositive')
        constant+=y*rhs[i];sum_y+=y
        for j,a in rows[i].items():r[j]-=y*a
    bound=constant+sum(min(x*l,x*u) for x,l,u in zip(r,lo,hi))
    if phase:
        # All original rows are relaxed by the same t>=0. The phase-I
        # objective is t. Choose a guaranteed feasible finite upper bound.
        T=max([Q(1)]+[sum(max(a*lo[j],a*hi[j]) for j,a in row.items())-h for row,h in zip(rows,rhs)])
        bound+=min(Q(0),(1+sum_y)*T)
    return bound


def replay(proof):
    m=model(proof['input']);rows,rhs=standard_rows(m);tol=rat(proof['tolerance'])
    if tol<0:raise ValueError('negative tolerance')
    lo=list(m['lo_exact']);hi=list(m['hi_exact']);obj=[Q(int(x)) for x in m['objective']]
    count=defaultdict(int);worst=None
    def visit(node):
        nonlocal worst
        kind=node['kind'];count[kind]+=1
        if kind=='branch':
            j=node['variable']
            if type(j)!=int or not 0<=j<m['n'] or not m['integrality'][j] or lo[j]!=0 or hi[j]!=1:raise ValueError('invalid binary disjunction')
            hi[j]=Q(0);visit(node['zero']);hi[j]=Q(1)
            lo[j]=Q(1);visit(node['one']);lo[j]=Q(0)
        elif kind in ('lower','infeasible'):
            phase=kind=='infeasible'
            bound=lagrangian(rows,rhs,[Q(0)]*m['n'] if phase else obj,lo,hi,node['dual'],phase)
            if bound!=rat(node['bound']):raise ValueError('incorrect saved rational bound')
            if phase:
                if bound<=0:raise ValueError('phase-I bound is not strictly positive')
            else:
                if bound < -tol:raise ValueError('insufficient lower bound')
                worst=bound if worst is None else min(worst,bound)
        else:raise ValueError('unknown proof node')
    visit(proof['tree'])
    return {'verified':True,'lower_bound':str(-tol),'weakest_leaf_bound':None if worst is None else str(worst),'nodes':dict(count),
            'scope':'all positive fillings in this fixed rational vertex set and all polynomials in the finite square-factor cone with the two stated normalizations; not unrestricted Morrey'}


def certify(data,tol=Q(1,10**7),seconds=30,max_nodes=3000):
    m=model(data);rows,rhs=standard_rows(m);n=m['n'];obj=[Q(int(x)) for x in m['objective']]
    lo=list(m['lo_exact']);hi=list(m['hi_exact'])
    ii=[];jj=[];vv=[]
    for i,row in enumerate(rows):
        for j,v in row.items():ii.append(i);jj.append(j);vv.append(float(v))
    G=coo_matrix((vv,(ii,jj)),shape=(len(rows),n)).tocsc();h=np.array(list(map(float,rhs)))
    Gphase=hstack([G,csc_matrix(-np.ones((len(rows),1)))],format='csc')
    t0=time.monotonic();count=0;stop_reason=None
    def exact_dual(res,phase=False):
        # Use two rational reconstructions and retain whichever exact bound is better.
        ys=res.ineqlin.marginals
        candidates=[]
        for mode in [0,1]:
            dy=[]
            for i,v in enumerate(ys):
                if not np.isfinite(v) or v>=0:continue
                q=Q(float(v)).limit_denominator(10**7) if mode==0 else Q(round(float(v)*10**10),10**10)
                if q<0:dy.append([i,str(q)])
            val=lagrangian(rows,rhs,[Q(0)]*n if phase else obj,lo,hi,dy,phase)
            candidates.append((val,dy))
        return max(candidates,key=lambda t:t[0])
    def visit():
        nonlocal count,stop_reason
        if count>=max_nodes or time.monotonic()-t0>seconds:
            stop_reason='budget exhausted';return None
        count+=1
        bounds=list(zip(map(float,lo),map(float,hi)))
        lp=linprog(np.array(list(map(float,obj))),A_ub=G,b_ub=h,bounds=bounds,method='highs')
        if lp.status==2:
            T=max([Q(1)]+[sum(max(a*lo[j],a*hi[j]) for j,a in row.items())-b for row,b in zip(rows,rhs)])
            p=linprog(np.r_[np.zeros(n),1.],A_ub=Gphase,b_ub=h,bounds=bounds+[(0,float(T))],method='highs')
            if p.status==0:
                v,d=exact_dual(p,True)
                if v>0:return {'kind':'infeasible','bound':str(v),'dual':d}
            # A floating infeasibility result is never accepted without proof.
            x=None
        elif lp.status==0:
            v,d=exact_dual(lp)
            if v>=-tol:return {'kind':'lower','bound':str(v),'dual':d}
            x=lp.x
        else:x=None
        free=[j for j in range(m['ft'],m['ct']) if lo[j]==0 and hi[j]==1]
        if not free:
            stop_reason='unclosed fixed-binary leaf';return None
        if x is not None:
            # Prioritize fractional face/height variables, favor height choice
            # in ties since it eliminates whole collections of faces.
            j=max(free,key=lambda j:(min(x[j],1-x[j]),j>=m['ht']))
        else:j=free[-1]
        hi[j]=Q(0);a=visit();hi[j]=Q(1)
        if a is None:return None
        lo[j]=Q(1);b=visit();lo[j]=Q(0)
        if b is None:return None
        return {'kind':'branch','variable':j,'zero':a,'one':b}
    tree=visit()
    report={'visited':count,'seconds':time.monotonic()-t0,'complete':tree is not None,'stop_reason':stop_reason}
    if tree is None:return report,None
    proof={'input':data,'tolerance':str(tol),'tree':tree}
    report['replay']=replay(proof)
    return report,proof


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--case',choices=['small','four']);p.add_argument('--input',type=Path);p.add_argument('--verify',type=Path);p.add_argument('--tolerance',default='1/10000000');p.add_argument('--seconds',type=float,default=30);p.add_argument('--max-nodes',type=int,default=3000);p.add_argument('--proof',type=Path);p.add_argument('--report',type=Path);a=p.parse_args()
    if a.verify:print(json.dumps(replay(json.loads(a.verify.read_text())),indent=2));raise SystemExit
    data=json.loads(a.input.read_text()) if a.input else make_input(a.case or 'small')
    r,c=certify(data,rat(a.tolerance),a.seconds,a.max_nodes);print(json.dumps(r,indent=2))
    if a.proof and c:a.proof.write_text(json.dumps(c,separators=(',',':'))+'\n')
    if a.report:a.report.write_text(json.dumps(r,indent=2)+'\n')
