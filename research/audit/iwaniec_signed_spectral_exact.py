"""Exact regression of the signed spectral-support algebra, not a Morrey proof."""
from fractions import Fraction as Q
from itertools import product


def sub_jet(p,t,H,m):
    C=p*H-2*t*m
    a=(2-p)/p
    assert 1<p<2 and -1<t<0 and H<0 and m>0 and C>=0 and H-m*(t+a)<=0
    c=((1+t)*m-p*H)/(1-t)
    beta=2*C/(1-t)
    alpha=c*t-(p-1)*H
    mu=(p-1)*beta/((2-p)*c)
    x0=(1+t)/2
    assert c>0 and beta>=0 and alpha<0 and 0<=mu<=2
    assert alpha+beta*x0+c*t==H
    assert p*alpha+(p-1)*beta*x0+(p-2)*c*t==0
    assert beta/2+c==m
    k=mu*x0-t
    assert k>=mu/2
    return k,mu


def super_jet(p,t,H,m):
    C=p*H-2*t*m
    a=(p-2)/p
    assert p>2 and -a<t<1 and H>0 and m>0 and C>=0 and H-m*(t+a)<0
    c=(p*H+(1-t)*m)/(1+t)
    gamma=2*C/(1+t)
    alpha=c*t-(p-1)*H
    b=(p-1)*gamma/(2*(p-2)*c)
    y0=(1-t)/2
    assert c>0 and gamma>=0 and alpha<0 and 0<=b<1 and b>=-t
    assert alpha+gamma*y0+c*t==H
    assert p*alpha+(p-1)*gamma*y0+(p-2)*c*t==0
    assert c-gamma/2==m
    k=b*(1-t)+t
    assert k>0 and k-b*b==(1-b)*(b+t)>=0
    assert -2*k+b*(1-t)<=0
    return k,b


def main():
    sub=[(Q(3,2),Q(-3,4),Q(-1,4),Q(1,3)),
         (Q(3,2),Q(-3,4),Q(-1,4),Q(1,4)),
         (Q(3,2),Q(-3,4),Q(-1,4),Q(3,5)),
         (Q(5,4),Q(-4,5),Q(-1,5),Q(1,5)),
         (Q(7,4),Q(-3,5),Q(-1,5),Q(2,5))]
    sup=[(Q(4),Q(-1,4),Q(1,4),Q(2)),
         (Q(4),Q(1,2),Q(1,4),Q(1)),
         (Q(3),Q(1,2),Q(1,6),Q(1,2)),
         (Q(5),Q(-1,2),Q(1,10),Q(2)),
         (Q(6),Q(1,2),Q(1,6),Q(1))]
    count=0
    for p,t,H,m in sub:
        k,mu=sub_jet(p,t,H,m)
        for s,u in product((Q(0),Q(1,5),Q(1,2),Q(1)),(Q(1),Q(3,2),Q(3),Q(10))):
            f=-k*u*u+mu*(1+s)*u/2-s
            assert f<=0,(p,t,s,u,f)
            count+=1
        # Pure Burkholder with same negative base has explicit jet.
        k0,mu0=sub_jet(p,t,(2-p)/p+t,Q(1))
        assert k0==1 and mu0==2
    for p,t,H,m in sup:
        k,b=super_jet(p,t,H,m)
        for v,u in product((Q(0),Q(1,4),Q(1,2),Q(1)),(Q(1),Q(3,2),Q(3),Q(10))):
            s=-1+v*(t+1)
            f=-k*u*u+b*(1-s)*u+s
            assert f<=0,(p,t,s,u,f)
            count+=1
    # Exact rank-one-line interval feasibility for normalized safe matrices.
    interval_count=0
    for t,sigma,delta in product((Q(-4,5),Q(-1,4),Q(1,2)),(Q(1),Q(2),Q(5)),(Q(-1),Q(-1,2),Q(1,2),Q(1))):
        x,y=(sigma+delta)/2,(sigma-delta)/2; d=sigma*delta
        if t<0 and delta>0:
            tau=x-(1+t)/2
            assert tau>=0 and t+2*t*tau<=d<=t+2*tau
            interval_count+=1
        if delta<=t and delta<0:
            tau=y-(1-t)/2
            assert tau>=0 and t-2*tau<=d<=t+2*t*tau
            interval_count+=1
    print(f'{count} exact scaling-polynomial controls; {interval_count} exact rank-one interval controls passed')
    print('Both subquadratic boundary cases mu=0,2, and superquadratic negative/positive base ratios checked.')

if __name__=='__main__': main()
