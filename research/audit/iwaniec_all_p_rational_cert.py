#!/usr/bin/env python3
"""Exact sufficient global rank-one-convexity certificate, rational p>=4.

JSON: {"p":"9/2", "h":["2","0","2","0","1"],
       "atoms":[["1","1","0"]] }.
h coefficients are in increasing monomial degree. Optional atoms
are (weight,x,y) signed-diagonal matrices. Only a STRICT negative
minor-Jensen upper bound is accepted. This is NOT a Morrey witness.
Requires Python standard library; no floating point.
"""
import json,sys
from fractions import Fraction as Q
from math import comb

def trim(a):
    a=list(a)
    while len(a)>1 and not a[-1]:a.pop()
    return tuple(a)
def add(a,b):
    return trim([(a[i] if i<len(a) else Q(0))+
                 (b[i] if i<len(b) else Q(0))
                 for i in range(max(len(a),len(b)))])
def scale(a,c):return trim([c*x for x in a])
def sub(a,b):return add(a,scale(b,-1))
def mul(a,b):
    z=[Q(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):z[i+j]+=x*y
    return trim(z)
def deriv(a):return trim([Q(i)*a[i] for i in range(1,len(a))] or [Q(0)])
def ev(a,x):
    v=Q(0)
    for c in reversed(a):v=v*x+c
    return v
def bern(a,lo,hi):
    n=len(a)-1
    q=[sum(a[i]*comb(i,j)*lo**(i-j)*(hi-lo)**j
           for i in range(j,len(a))) for j in range(n+1)]
    return tuple(sum((q[j]*Q(comb(k,j),comb(n,j))
                      for j in range(k+1)),Q(0)) for k in range(n+1))
def half(a):
    v=list(a);left=[v[0]];right=[v[-1]]
    for _ in range(len(a)-1):
        v=[(v[i]+v[i+1])/2 for i in range(len(v)-1)]
        left.append(v[0]);right.append(v[-1])
    return tuple(left),tuple(reversed(right))

def certify(p,h,limit=24):
    assert p>=4 and len(h)>2
    r=(Q(0),Q(1));one=(Q(1),)
    dh=deriv(h);V=deriv(dh)
    C=sub(scale(h,p),scale(mul(r,dh),2))
    U=add(scale(C,p-1),mul(mul(r,r),V))
    E=sub(scale(dh,p-2),mul(r,V))
    Pp=add(C,mul(sub(one,r),E))
    Pm=sub(C,mul(add(one,r),E))
    Qp=sub(mul(mul(sub(one,r),sub(one,r)),mul(U,V)),mul(Pp,Pp))
    Qm=sub(mul(mul(add(one,r),add(one,r)),mul(U,V)),mul(Pm,Pm))
    polys=(h,C,V,Pp,Pm,Qp,Qm)
    stats={'leaves':0,'depth':0}
    def rec(v,d):
        good=[min(x)>0 for x in v]
        if all(good[i] for i in (0,1,2)) and (good[3] or good[5]) and (good[4] or good[6]):
            stats['leaves']+=1;stats['depth']=max(d,stats['depth']);return
        if d>=limit:
            raise ValueError("No strict certificate at this depth (NOT evidence of non-RC)")
        pairs=[half(x) for x in v]
        rec(tuple(x[0] for x in pairs),d+1)
        rec(tuple(x[1] for x in pairs),d+1)
    rec(tuple(bern(q,Q(-1),Q(1)) for q in polys),0)
    return stats

def power_interval(a,p,bits=96):
    assert a>=0 and p>=0
    if a==0:return Q(0),Q(0)
    m,n=p.numerator,p.denominator
    target=a**m
    if n==1:return target,target
    hi=Q(1)
    while hi**n<target:hi*=2
    lo=Q(0)
    for _ in range(bits+hi.numerator.bit_length()):
        mid=(lo+hi)/2
        if mid**n<target:lo=mid
        else:hi=mid
    return lo,hi

def witness(p,h,atoms):
    assert 1<=len(atoms)<=4
    w=[Q(str(row[0])) for row in atoms]
    x=[Q(str(row[1])) for row in atoms]
    y=[Q(str(row[2])) for row in atoms]
    assert all(z>=0 for z in w) and sum(w)==1
    x0=sum(z*u for z,u in zip(w,x))
    t=sum(z*u for z,u in zip(w,y))
    assert x0==1 and -1<t<1
    assert sum(z*u*v for z,u,v in zip(w,x,y))==t
    upper=Q(0)
    for z,u,v in zip(w,x,y):
        a=max(abs(u),abs(v))
        if not a:continue
        r=u*v/(a*a)
        assert -1<=r<=1
        value=ev(h,r)
        assert value>0
        upper+=z*power_interval(a,p)[1]*value
    gap=upper-ev(h,t)
    return {'upper_gap':str(gap),
            'certificate':('STRICT_NEGATIVE_DIAGONAL_MINORS_JENSEN'
                            if gap<0 else 'NO_NEGATIVE_WITNESS_CERTIFIED')}

def main():
    obj=json.load(open(sys.argv[1])) if len(sys.argv)>1 else {
      'p':'4','h':['2','0','2','0','1']}
    p=Q(str(obj['p']));h=trim([Q(str(z)) for z in obj['h']])
    result=certify(p,h)
    print('PASS: globally nonnegative, strictly rank-one convex',result)
    if 'atoms' in obj:
        outcome=witness(p,h,obj['atoms'])
        print(outcome)
        if outcome['certificate']!='STRICT_NEGATIVE_DIAGONAL_MINORS_JENSEN':
            raise SystemExit(2)
if __name__=='__main__':main()
