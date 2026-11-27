from fractions import Fraction as Q
import sympy as S

s,d,r,U,Up,V,Vp,m,H0,t=S.symbols('s d r U Up V Vp m H0 t')
D=s*d
P=U+H0-m*t+Up*(s-r)+(V+m-r*Vp)*d+Vp*D
assert S.expand(P.subs({s:r,d:t})-U-V*t-H0)==0
assert S.expand(P-(U+H0-m*t+Up*(s-r)+(V+m+Vp*(s-r))*d))==0
M,N,R=S.symbols('M N R', nonnegative=True)
C=M*R*s*s/2+N*s**4/24
assert S.expand(S.diff(C,s,2)-(M*R+N*s*s/2))==0
assert S.expand(S.diff(C,s)-(M*R*s+N*s**3/6))==0
print('Symbolic starter contact and radial repair identities passed')

# f=K_1^+ + H(delta), with arbitrary convex angular residual.
def pos(a):return max(Q(0),a)
def U0(s):return pos(s-1)
def V0(s):return pos(s-1)
def H(d):
    if d<=1:return Q(0)
    if d<=2:return (d-1)**2
    return 1+2*(d-2)
def Hp(d):return min(Q(2),2*pos(d-1))
def f(s,d):return U0(s)+V0(s)*d+H(d)
def K(s,d):return pos(s-1)*(1+d)
# U''=delta_1, V''=delta_1, so U''=s|V''| exactly.
for r in [Q(i,8) for i in range(1,41) if i!=8]:
    up=vp=Q(r>1)
    assert up+r*vp >= V0(r)+Hp(r)
    assert up-r*vp >= -V0(r)-Hp(-r)
    for t in [r*Q(i,8) for i in range(-7,8)]:
        m=Hp(t)
        assert up>=abs(V0(r)+m-r*vp)
        def minor(s,d):
            p=U0(r)+H(t)-m*t+up*(s-r)+(V0(r)+m-r*vp)*d+vp*s*d
            return p+(K(s,d) if r<1 else 0)
        assert minor(r,t)==f(r,t)
        for s in [Q(i,8) for i in range(41)]:
            for d in [s*Q(j,4) for j in range(-4,5)]:
                assert minor(s,d)<=f(s,d),(r,t,s,d)
print('39-radius nonsmooth example: boundary budgets, touching, and rational minorant controls passed')

# Check compact-sector repair for the signed RC Dacorogna-Marcellini quartic.
s,d=S.symbols("s d",real=True)
F=(s*s+d*d)**2-Q(9,4)*(s*s+d*d)*s*d
U=F.subs(d,0); V=S.diff(F,d).subs(d,0)
R=Q(2); M=Q(43); N=Q(8)
H=F.subs(s,R)-F.subs({s:R,d:0})-S.diff(F,d).subs({s:R,d:0})*d
C=M*(R*s*s/2-s**3/6)+N*s**4/24
assert S.expand(S.diff(C,s,2)-(M*(R-s)+N*s*s/2))==0
assert S.expand(S.diff(C,s)-(M*(R*s-s*s/2)+N*s**3/6))==0
for a in [Q(i,8) for i in range(1,17)]:
    u2=S.diff(U+C,s,2).subs(s,a); v2=S.diff(V,s,2).subs(s,a)
    assert u2>=a*abs(v2)
    u1=S.diff(U+C,s).subs(s,a); v1=S.diff(V,s).subs(s,a); v=V.subs(s,a)
    assert u1>=v-a*v1+S.diff(H,d).subs(d,a)
    assert u1>=-v+a*v1-S.diff(H,d).subs(d,-a)
    for b in [a*Q(i,8) for i in range(-8,9)]:
        err=(U+V*d+H-F).subs({s:a,d:b})
        assert abs(err)<=M*(R-a)*b*b/2
        assert abs(S.diff(F,s,1,d,2).subs({s:a,d:b}))<=M
        assert abs(S.diff(F,s,2,d,2).subs({s:a,d:b}))<=N
print('Signed quartic: compact-sector curvature repair and error bounds passed')
