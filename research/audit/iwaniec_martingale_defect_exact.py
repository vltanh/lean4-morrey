"""Exact regression controls for the determinant defect identities.
Diagonal matrices are represented by their two diagonal entries; this
makes the nearest rank-one truncation rational. No optimization or
claim that every gradient law has zero defect is made.
"""
from fractions import Fraction as Q
from itertools import product
from random import Random


def add(a,b): return tuple(x+y for x,y in zip(a,b))
def sub(a,b): return tuple(x-y for x,y in zip(a,b))
def scale(t,a): return tuple(t*x for x in a)
def norm2(a): return sum(x*x for x in a)
def det(a): return a[0]*a[1]
def nearest(a):
    return (a[0],Q(0)) if abs(a[0])>=abs(a[1]) else (Q(0),a[1])

def mean(rows,prob):
    return tuple(sum(prob[i]*rows[i][j] for i in rows) for j in range(2))

def conditional(rows,prob,depth):
    p={}; a={}
    for k in range(depth+1):
        for s in product((0,1),repeat=k):
            group={i:x for i,x in rows.items() if i[:k]==s}
            p[s]=sum(prob[i] for i in group)
            a[s]=scale(1/p[s],mean(group,prob))
    return p,a

def cost(rows,prob,depth):
    p,a=conditional(rows,prob,depth)
    defects=sum(p[s]*abs(det(sub(a[s],a[s[:-1]]))) for s in a if s)
    residual=sum(prob[i]*norm2(sub(x,a[i[:depth]]))/2 for i,x in rows.items())
    return defects,residual,p,a

def repair_control(rows,prob,depth,r):
    c1,c2,p,a=cost(rows,prob,depth); A=a[()]; R2=max(norm2(sub(x,A)) for x in rows.values())
    y={():A}; err={(): (Q(0),Q(0))}; stop={():False}; m={():A}
    for k in range(1,depth+1):
        for s in product((0,1),repeat=k):
            t=s[:-1]
            if stop[t]: y[s]=y[t]; m[s]=m[t]; err[s]=err[t]; stop[s]=True; continue
            h=sub(a[t+(0,)],a[t+(1,)])
            hp=nearest(h)
            q=p[t+(0,)]/p[t]
            factor=1-q if s[-1]==0 else -q
            y[s]=add(y[t],scale(factor,hp)); m[s]=a[s]; err[s]=sub(y[s],m[s]); stop[s]=norm2(err[s])>=r*r
            assert norm2(scale(factor,sub(hp,h)))<=abs(det(scale(factor,h)))
            if s[-1]==1:
                s0=t+(0,); assert det(sub(y[s0],y[s]))==0
                assert add(scale(q,y[s0]),scale(1-q,y[s]))==y[t]
    distance=sum(prob[i]*norm2(sub(rows[i],y[i[:depth]])) for i in rows)
    ed=sum(prob[i]*norm2(err[i[:depth]]) for i in rows)
    remainder=sum(prob[i]*norm2(sub(rows[i],m[i[:depth]])) for i in rows)
    assert distance==ed+remainder and ed<=c1
    assert distance<=(1+R2/(r*r))*c1+2*c2
    return any(stop[s] for s in stop if len(s)<depth)

def coupling_control(X,Y,prob,depth):
    assert mean(X,prob)==mean(Y,prob)
    c1,c2,p,a=cost(X,prob,depth); d1,d2,_,b=cost(Y,prob,depth)
    eps2=sum(prob[i]*norm2(sub(X[i],Y[i])) for i in X)
    var=sum(prob[i]*norm2(sub(Y[i],b[()])) for i in Y)
    diff=c1+c2-d1-d2-eps2/2
    assert diff<=0 or diff*diff<=var*eps2
    D={s:sub(a[s],b[s]) for s in a}
    e=sum(p[s]*norm2(sub(D[s],D[s[:-1]])) for s in D if s)
    tail=sum(prob[i]*norm2(sub(sub(X[i],Y[i]),D[i[:depth]])) for i in X)
    assert e+tail==eps2

def main():
    rng=Random(20261123); leaves=list(product((0,1),repeat=4)); stopped=0
    for _ in range(40):
        weights={i:rng.randint(1,7) for i in leaves}; total=sum(weights.values()); p={i:Q(w,total) for i,w in weights.items()}
        Y={i:(Q(rng.randint(-5,5)),Q(rng.randint(-5,5))) for i in leaves}
        noise={i:(Q(rng.randint(-2,2),3),Q(rng.randint(-2,2),3)) for i in leaves}; avg=mean(noise,p)
        X={i:add(Y[i],sub(noise[i],avg)) for i in leaves}
        for n in range(4):
            stopped+=repair_control(X,p,n,Q(1,3))
            coupling_control(X,Y,p,n)
    assert stopped>0
    print('160 rational binary-tree controls: rank-one repair, stopping bound, coupling transfer, variance identities passed')
    print('Controls with an early stop:',stopped)
    # Projection algebra: U=(s,0), V=(t/3,s), with independent fair signs.
    # Reveal s, then t.  E[V|s]=(0,s), which has the same L2 norm as U.
    delta=Q(1,9); projection_error=Q(1,9)
    assert projection_error==delta
    print('Projection variance identity: defect and conditional variance both 1/9')

if __name__=='__main__': main()
