"""Turn a floating-point candidate from exchange optimization into an exact
countercertificate against global rank-one convexity.
No assumption that the candidate is a QC counterexample.
"""
import sympy as sp, numpy as np
R=np.load('/mnt/data/morrey_four_wave_exchange_last.npz');E=R['exps'];c=R['coef']
x=sp.symbols('a b c d');
P=sum(sp.Rational(int(round(float(z)*10**8)),10**8)*sp.prod(x[i]**int(ei) for i,ei in enumerate(e)) for e,z in zip(E,c))
H=sp.Matrix([-1,-2,3,6]);A=sp.Matrix([sp.Rational(3,5),0,0,sp.Rational(4,5)])
D2=(H.T*sp.hessian(P,x)*H)[0]
print('candidate J using floating c:',R['J'],'sampled worst hessian:',R['worst_hessian']);print('exact rational rank-one H:',H,'det(H):',H[0]*H[3]-H[1]*H[2]);print('exact rational matrix A:',A)
print('D²P(A)[H,H] exact:',D2.subs(dict(zip(x,A))));print('negative?',D2.subs(dict(zip(x,A)))<0)
