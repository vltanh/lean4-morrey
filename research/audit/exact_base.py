#!/usr/bin/env python3
"""Exact rational minimization of c+2h.F+F^T K F for PSD K.

Avoids silently discarding null or tiny-eigenvalue directions. This is a
quadratic-objective diagnostic, not a Morrey counterexample construction.
"""
from fractions import Fraction as F
from itertools import combinations
from pathlib import Path
import json


def determinant(A):
    A=[row[:] for row in A]; n=len(A); value=F(1)
    for j in range(n):
        piv=next((i for i in range(j,n) if A[i][j]),None)
        if piv is None:return F(0)
        if piv!=j:A[j],A[piv]=A[piv],A[j];value=-value
        x=A[j][j];value*=x
        for i in range(j+1,n):
            t=A[i][j]/x
            for k in range(j+1,n):A[i][k]-=t*A[j][k]
    return value


def rref(A):
    A=[row[:] for row in A]; pivots=[]; r=0
    for j in range(len(A[0])):
        p=next((i for i in range(r,len(A)) if A[i][j]),None)
        if p is None:continue
        A[r],A[p]=A[p],A[r]; q=A[r][j];A[r]=[x/q for x in A[r]]
        for i in range(len(A)):
            if i!=r:
                q=A[i][j];A[i]=[x-q*y for x,y in zip(A[i],A[r])]
        pivots.append(j);r+=1
        if r==len(A):break
    return A,pivots


def value(K,h,c,x):
    return c+2*sum(a*b for a,b in zip(h,x))+sum(x[i]*K[i][j]*x[j] for i in range(len(x)) for j in range(len(x)))


def minimize_psd(K,h,c):
    K=[[F(x) for x in row] for row in K];h=[F(x) for x in h];c=F(c);n=len(h)
    if len(K)!=n or any(len(row)!=n for row in K) or any(K[i][j]!=K[j][i] for i in range(n) for j in range(n)):
        raise ValueError('Expected a symmetric square K matching h')
    for k in range(1,n+1):
        for I in combinations(range(n),k):
            if determinant([[K[i][j] for j in I] for i in I])<0:
                raise ValueError('K is not positive semidefinite (negative exact principal minor)')
    R,pivots=rref(K)
    kernel=[]
    for j in range(n):
        if j in pivots:continue
        z=[F(0)]*n;z[j]=1
        for row,p in enumerate(pivots):z[p]=-R[row][j]
        kernel.append(z)
    for z in kernel:
        hz=sum(a*b for a,b in zip(h,z))
        if hz:
            t=(abs(c)+1)/(2*abs(hz));sign=1 if hz>0 else -1
            x=[-sign*t*a for a in z];gap=value(K,h,c,x)
            assert gap<0
            return {'status':'unbounded_below','kernel_direction':[str(a) for a in z],
                    'linear_kernel_pairing':str(hz),'negative_base':[str(a) for a in x],
                    'negative_value':str(gap)}
    aug,piv=rref([row+[-h[i]] for i,row in enumerate(K)])
    if n in piv:raise AssertionError('Range/kernel criterion inconsistency')
    x=[F(0)]*n
    for row,p in enumerate(piv):x[p]=aug[row][-1]
    assert all(sum(K[i][j]*x[j] for j in range(n))==-h[i] for i in range(n))
    gap=value(K,h,c,x)
    return {'status':'finite_minimum','base':[str(a) for a in x],'minimum':str(gap),
            'rank':len(pivots),'nullity':n-len(pivots)}


def main():
    records={
        'null_linear_direction':minimize_psd([[1,0],[0,0]],[0,1],1),
        'tiny_positive_curvature':minimize_psd([[1,0],[0,F(1,10**14)]],[0,F(1,10**6)],1),
        'safe_singular_minimum':minimize_psd([[1,0],[0,0]],[1,0],2),
    }
    assert records['null_linear_direction']['negative_value']=='-1'
    assert records['tiny_positive_curvature']['minimum']=='-99'
    assert records['safe_singular_minimum']['minimum']=='1'
    try:minimize_psd([[0,1],[1,0]],[0,0],0)
    except ValueError:records['indefinite_control']='rejected by exact principal minor'
    else:raise AssertionError('Indefinite K was accepted')
    records['scope']='Quadratic regression controls only; no claim these cases arise from a valid planar Morrey candidate.'
    Path(__file__).with_name('exact_base_controls.json').write_text(json.dumps(records,indent=2)+'\n')
    print(json.dumps(records,indent=2))


if __name__=='__main__':main()
