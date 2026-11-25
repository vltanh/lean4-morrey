#!/usr/bin/env python3
"""Exact high-resonance all-wave Jensen control for strict rank-one ellipticity.

The arbitrary-N theorem in the research note is analytic, not proved by this
regression. F(X)=||X||_F²+5det(X)+X11 is signed, anisotropic,
nonhomogeneous and nonconvex, but uniformly strict rank-one convex.
"""
from fractions import Fraction as Q

# Full Hessian of F: Frobenius 2I plus 5 times determinant's Hessian;
# eigenvalues 2+5=7 and 2-5=-3. For rank-one H, det(H)=0.
mu=Q(2)
M=Q(7)
R=Q(3)
n=169
# H1=e1⊗(1,0), H2=e2⊗(0,1), H3=(e1/1024)⊗(1024,1)
S=Q(3)+Q(1,1024**2)
margin=mu*S/4
error=4*M*R*R/n
k1=(1,0);k2=(0,1);k3=(1024,1)
# Any relation is n1=-1024*n3 and n2=-n3.
shortest=sum(map(abs,(-1024,-1,1)))
assert shortest==1026
assert all((a*k1[0]+b*k2[0]+c*k3[0],
            a*k1[1]+b*k2[1]+c*k3[1])!=(0,0)
           for a,b,c in ((0,0,1),(-1,-1,1),(1024,1,1)))
assert 4*n<shortest
assert error==Q(252,169)
assert margin==Q(3145729,2097152)
assert error<margin
print("PASS: exact high-resonance all-wave Jensen control")
print("rank-one margin =",margin,"Bernstein correlation error =",error)
