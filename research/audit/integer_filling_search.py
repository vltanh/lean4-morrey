#!/usr/bin/env python3
"""Finite candidate discovery, never a proof of positivity. Exact-check candidates."""
from itertools import combinations
from fractions import Fraction as Q
from collections import defaultdict
import argparse
import json
from pathlib import Path
import numpy as np
from scipy.optimize import milp, Bounds, LinearConstraint
from scipy.sparse import csc_matrix
from integer_filling_exact import (rat, graph, wedge_half, sqnorm, make_energy,
                                   sqrt_bounds, edge_add, verify_filling, plus, shift, scale)


def search(data, seconds=30):
    A=tuple(map(rat,data['base']))
    V=[tuple(map(rat,p)) for p in data['vertices']]
    if len(A)!=4 or any(len(p)!=4 for p in V) or len(set(V))!=len(V):
        raise ValueError('invalid base or vertex set')
    ids=[V.index(graph(A,y)) for y in ((Q(0),Q(0)),(Q(1),Q(0)),(Q(1),Q(1)),(Q(0),Q(1)))]
    bd=defaultdict(int)
    for i,j in zip(ids,ids[1:]+ids[:1]): edge_add(bd,i,j,1)
    E=list(combinations(range(len(V)),2)); row={e:i for i,e in enumerate(E)}
    b=np.array([bd[e] for e in E],dtype=float)
    Phi,M=make_energy(data['energy'],80)
    eta=rat(data.get('area_penalty','1/100'))
    if eta<=0: raise ValueError('positive area penalty required for the finite search')
    q=1
    from math import lcm
    for p in V:
        for x in p: q=lcm(q,x.denominator)
    ref=(Q(1),A[1],A[3],-A[0],-A[2],A[0]*A[3]-A[1]*A[2])
    baseline=plus(shift(Phi(ref),M),scale(eta,sqrt_bounds(sqnorm(ref))))
    # Exact finite bound for all candidates no worse than the flat square.
    cap=int(2*q*q*baseline[1]/eta)
    cols=[];cost=[];ii=[];jj=[];vv=[]
    for i,j,k in combinations(range(len(V)),3):
        xi=wedge_half(V[i],V[j],V[k])
        if not any(xi): continue
        for s in (1,-1):
            z=tuple(s*x for x in xi)
            I=plus(shift(Phi(z),M*z[0]),scale(eta,sqrt_bounds(sqnorm(z))))
            col=len(cols);cols.append(((i,j,k),s));cost.append(float((I[0]+I[1])/2))
            for e,t in (((j,k),1),((i,k),-1),((i,j),1)):
                ii.append(row[e]);jj.append(col);vv.append(s*t)
    B=csc_matrix((vv,(ii,jj)),shape=(len(E),len(cols)),dtype=float)
    res=milp(c=np.array(cost),integrality=np.ones(len(cols)),bounds=Bounds(0,cap),
             constraints=LinearConstraint(B,b,b),options={'time_limit':seconds})
    report={'vertices':len(V),'oriented_faces':len(cols),'multiplicity_cap':cap,
            'solver_status':int(res.status),'solver_message':res.message,
            'solver_objective':None if res.fun is None else float(res.fun),
            'scope':'floating search only; no positive lower-bound certificate'}
    if res.x is not None:
        out=dict(data);out['area_penalty']=str(eta)
        out['faces']=[{'vertices':list(t),'multiplicity':s*int(round(x))}
                      for (t,s),x in zip(cols,res.x) if int(round(x))]
        try: report['exact_candidate']=verify_filling(out)
        except (ValueError,AssertionError) as exc: report['exact_rejection']=str(exc)
        return report,out
    return report,None


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('input',type=Path);p.add_argument('--seconds',type=float,default=30)
    p.add_argument('--candidate',type=Path)
    args=p.parse_args();report,candidate=search(json.loads(args.input.read_text()),args.seconds)
    if args.candidate and candidate is not None:
        args.candidate.write_text(json.dumps(candidate,indent=2)+'\n')
    print(json.dumps(report,indent=2))
