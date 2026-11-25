"""Exact negative rank-one curvature witnesses for two LP candidates.
Python standard library only. Binary float coefficients are interpreted
as exact rational numbers, not intervals or approximate signs.
"""
from fractions import Fraction as Q
from itertools import product
from math import prod
E=[e for e in product(range(5),repeat=4) if sum(e)<=4 and e[3]<=1]
data=[
(2, '371000/569313 16000/569313 -3000/63257 430687/569313',
 '-26093/50000 16409/125000 -81771/100000 51423/250000',
 '''0x1.0000000000000p+0 0x1.d817e0129b8cep-2 -0x1.88600c611ff80p-2 0x1.d8e4aedf86950p-2 0x1.5e349f71a3223p-3 -0x1.0000000000000p+0 -0x1.6588c013aab9bp-2 0x1.b879cfaf2050dp-4 0x1.410a39f913abbp-1 0x1.0000000000000p+0 0x1.0000000000000p+0 -0x1.0000000000000p+0 -0x1.d8f970c4cbba3p-3 0x1.2a0a5a7c5ae1dp-6 -0x1.633490dffb5a5p-1 0x1.b85411249d832p-3 0x1.0000000000000p+0 -0x1.597b56166ac50p-2 -0x1.0000000000000p+0 -0x1.bd9016b651e1dp-1 0x1.0000000000000p+0 0x1.06cc64fbfb4bep-1 -0x1.ef4938c5d0352p-2 -0x1.60a99cc5dfc3fp-3 0x1.5508133cca7f9p-1 0x1.0000000000000p+0 -0x1.374f5bad22800p-2 -0x1.72936b1887051p-2 -0x1.0000000000000p+0 -0x1.3e53c5e89eddap-2 -0x1.0000000000000p+0 -0x1.d24beb15ff7ebp-1 0x1.bfc70983c6d02p-2 0x1.a15fd1518fc57p-1 0x1.1c640f217e56cp-1 0x1.4a3562e3bfeb2p-4 -0x1.0000000000000p+0 -0x1.0000000000000p+0 -0x1.0000000000000p+0 -0x1.f665f4d5aa5c0p-3 -0x1.ef33ba52ed2dep-1 0x1.0000000000000p+0 0x1.9e700deb35271p-1 -0x1.190f4eac221a8p-1 -0x1.0000000000000p+0 -0x1.2c05387b10f3dp-5 -0x1.06004870f751cp-2 0x1.9f436f5ac3adfp-1 0x1.b839160f42879p-4 -0x1.f7cfcf4ffd8a0p-2 -0x1.15a42108150d0p-3 0x1.0201f9cfe11b0p-6 -0x1.6b9192513dddfp-1 -0x1.aa37b27a36059p-2 -0x1.4a97628cf2374p-1'''),
(8, '193000/224003 1000/2016027 -122000/2016027 -1016027/2016027',
 '-1089/12500 -198/15625 -24651/25000 -2241/15625',
 '''0x1.0000000000000p+0 -0x1.cec843e167047p-2 0x1.eaa333267b831p-3 0x1.469d7d51c592dp-2 0x1.e33b1a0bdc489p-2 0x1.2e821fa516bddp-1 -0x1.fe5b587e00eb0p-8 -0x1.350fd212fa47dp-3 -0x1.115a26ec7132cp-1 -0x1.44ea36ea790d0p-2 0x1.ef5d8a4ef2adcp-1 0x1.d39b4b1ad6e0ap-1 -0x1.6dedbc0a4ad76p-1 -0x1.5b98a7ff1ef52p-3 -0x1.8327baf9da487p-2 -0x1.0000000000000p+0 0x1.0000000000000p+0 0x1.6c6b065ad4232p-1 0x1.7a6e30dd29f7ep-2 0x1.d7f5ad42803b5p-7 0x1.0000000000000p+0 -0x1.9a3db59efc7bdp-6 -0x1.79d646743c850p-1 -0x1.f589982cde2a4p-1 -0x1.3d013b4003130p-3 0x1.0000000000000p+0 0x1.0000000000000p+0 0x1.25253ac1d5000p-1 -0x1.4d1a6abeaaa89p-4 -0x1.c73dacc4d4042p-1 0x1.0000000000000p+0 -0x1.83ee132a753e8p-1 0x1.1abd67ee0701bp-1 -0x1.3be42a6486879p-3 0x1.0000000000000p+0 0x1.c71e8c07b829dp-2 0x1.76b0e611776e6p-1 -0x1.925a66859b5efp-1 0x1.0000000000000p+0 -0x1.1e527ae490599p-2 -0x1.5dd51ce2faad6p-4 0x1.0000000000000p+0 -0x1.d5934d49d65c0p-8 -0x1.8b85c38e9e693p-2 -0x1.48972ada4bafap-6 -0x1.5d12b0c2d324fp-1 0x1.b4554d790f75dp-3 -0x1.cd98494bac2d1p-2 -0x1.4eb2ab6e2de85p-1 -0x1.0000000000000p+0 0x1.716d89c7f95ffp-2 -0x1.131cfb433d1adp-1 -0x1.0000000000000p+0 0x1.ad2208bc05041p-2 0x1.296086e4310b8p-2''')]
for i,x0,h0,c0 in data:
    x=list(map(Q,x0.split()));h=list(map(Q,h0.split()))
    c=[Q(float.fromhex(z)) for z in c0.split()]
    assert len(c)==len(E)==55
    assert sum(z*z for z in x)==1 and h[0]*h[3]==h[1]*h[2] and any(h)
    alpha=sum(z*w for z,w in zip(x,h));norm2=sum(z*z for z in h)
    def mon(e): return prod(z**k for z,k in zip(x,e))
    val=Q(0)
    for coef,ex in zip(c,E):
        e=list(ex); q=2-sum(e)
        df=Q(0);ddf=Q(0)
        for j in range(4):
            if not e[j]:continue
            ee=e.copy();ee[j]-=1
            df+=h[j]*e[j]*mon(ee)
            for k in range(4):
                if not ee[k]:continue
                eee=ee.copy();eee[k]-=1
                ddf+=h[j]*h[k]*e[j]*ee[k]*mon(eee)
        val+=coef*(ddf+2*q*alpha*df+(q*norm2+q*(q-2)*alpha**2)*mon(e))
    assert val < -1
    print(i,'negative exact curvature',float(val))
