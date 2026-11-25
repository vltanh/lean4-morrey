#!/usr/bin/env python3
"""Exact global poly-affine support of the p=4 hybrid separator at rank-one E.

Proves F(A)>= -3h(0)+4h(0)A11+(h'(0)-7)A22+7det A
for all A, via exact rational Bernstein covering of a>=0, -1<=r<=1.
Requires only Python stdlib; does not depend on Iwaniec or Lean.
"""
from fractions import Fraction as Q
from math import comb
D=1<<24
A=[37676885,55559819,22507846,3634764,1122809,
   1068027,57237,275379,623336,96945,-261804,-126467,-6991]
def add(a,b):
    return [(a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0)
            for i in range(max(len(a),len(b)))]
def scale(a,c):return [c*v for v in a]
def mul(a,b):
    out=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):out[i+j]+=x*y
    return out
def diff(a):return [i*a[i] for i in range(1,len(a))]
T=[[1],[0,1]]
for _ in range(2,len(A)):
    T.append(add(scale(mul([0,1],T[-1]),2),scale(T[-2],-1)))
H=[0]
for c,t in zip(A,T):H=add(H,scale(t,c))
h0,h1=H[0],H[1]
c=7
assert 4*h0>abs(h1-c*D)
# P*D as polynomial in a, coefficients themselves polynomials in r
P=[[3*h0],[-4*h0,c*D-h1],[0,-c*D],[0],H]

def bern1(poly,a,b):
    n=len(poly)-1
    q=[sum(Q(poly[i])*comb(i,j)*Q(a)**(i-j)*Q(b-a)**j
           for i in range(j,n+1)) for j in range(n+1)]
    return tuple(sum(q[j]*Q(comb(k,j),comb(n,j))
                     for j in range(k+1)) for k in range(n+1))
def bern2(poly,ar,rr):
    n=len(poly)-1
    nr=max(len(v) for v in poly)-1
    rb=[bern1(list(v)+[0]*(nr+1-len(v)),*rr) for v in poly]
    a,b=map(Q,ar)
    return tuple(tuple(sum(Q(comb(k,m),comb(n,m))*(b-a)**m*
        sum(rb[i][j]*comb(i,m)*a**(i-m) for i in range(m,n+1))
        for m in range(k+1)) for j in range(nr+1))
        for k in range(n+1))
def halve(v):
    v=list(v);left=[v[0]];right=[v[-1]]
    for _ in range(len(v)-1):
        v=[(v[i]+v[i+1])/2 for i in range(len(v)-1)]
        left.append(v[0]);right.append(v[-1])
    return tuple(left),tuple(reversed(right))
def half2(B,axis):
    if axis==0:
        z=[halve([B[i][j] for i in range(len(B))])
           for j in range(len(B[0]))]
        return (tuple(tuple(z[j][0][i] for j in range(len(z)))
                      for i in range(len(B))),
                tuple(tuple(z[j][1][i] for j in range(len(z)))
                      for i in range(len(B))))
    z=[halve(v) for v in B]
    return (tuple(t[0] for t in z),tuple(t[1] for t in z))

# The corner check detects swapped axes in bivariate conversion.
root=bern2(P,(0,16),(-1,1))
assert root[0][0]==3*h0
assert root[-1][-1]==sum(16**i*sum(v) for i,v in enumerate(P))

# Local strict Hessian in S; P(1,0)=0, dP(1,0)=0.
S=((Q(1)-Q(1,128),Q(1)+Q(1,128)),(-Q(1,128),Q(1,128)))
Paa=[[0,-2*c*D],[0],scale(H,12),[0]]
Prr=[[0],[0],[0],[0],diff(diff(H))]
Par=[[c*D-h1],[-2*c*D],[0],scale(diff(H),4)]
lo_aa=min(map(min,bern2(Paa,*S)))/D
lo_rr=min(map(min,bern2(Prr,*S)))/D
max_ar=max(abs(v) for row in bern2(Par,*S) for v in row)/D
assert lo_aa>0 and lo_rr>0 and lo_aa*lo_rr>max_ar**2
assert Q(h0,D)>0
assert 4*Q(h0,D)+abs(Q(h1,D)-c)<16

# h > 1/32 globally by exact one-dimensional Bernstein subdivision.
h_leaves=0
def certify_h(v,depth=0):
    global h_leaves
    if min(v)>Q(D,32):h_leaves+=1;return
    if depth>=20:raise AssertionError('h positivity')
    left,right=halve(v)
    certify_h(left,depth+1);certify_h(right,depth+1)
certify_h(bern1(H,-1,1))
assert h_leaves==3
# For a>=16: a^4h>=a^4/32>=8a^2; estimate the remaining
# negative terms by -7a^2-(4h0+|h1-7|)a.

count={'positive':0,'local':0,'nodes':0,'depth':0}
def prove(B,ab,rb,depth=0):
    count['nodes']+=1
    if all(v>0 for row in B for v in row):
        count['positive']+=1;count['depth']=max(depth,count['depth']);return
    if (ab[0]>=S[0][0] and ab[1]<=S[0][1] and
        rb[0]>=S[1][0] and rb[1]<=S[1][1]):
        count['local']+=1;count['depth']=max(depth,count['depth']);return
    if depth>=35:raise AssertionError(('unproved box',ab,rb))
    axis=0 if ab[1]-ab[0]>2*(rb[1]-rb[0]) else 1
    left,right=half2(B,axis)
    if axis==0:
        m=(ab[0]+ab[1])/2
        prove(left,(ab[0],m),rb,depth+1)
        prove(right,(m,ab[1]),rb,depth+1)
    else:
        m=(rb[0]+rb[1])/2
        prove(left,ab,(rb[0],m),depth+1)
        prove(right,ab,(m,rb[1]),depth+1)
prove(root,(Q(0),Q(16)),(Q(-1),Q(1)))
assert count=={'positive':178,'local':6,'nodes':367,'depth':21},count
print('PASS: global p4 rank-one poly-affine support, exact',count)
print('Local Hess bounds:',lo_aa,lo_rr,max_ar)
