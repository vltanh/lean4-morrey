"""Check whether arbitrary 2x2 pullbacks of the 2x6 quaternionic energy are polyconvex via PSD minor Gram forms."""
import numpy as np
from scipy.optimize import minimize_scalar
rng=np.random.default_rng(182)
M=np.zeros((2,6));M[0,0]=-2;M[1,3]=-2
idx=[(i,j) for i in range(6) for j in range(i,6)]
def GG(X):
 u,v,s,t=X[0,:3],X[0,3:],X[1,:3],X[1,3:]
 return np.dot(u,u)*np.dot(t,t)+np.dot(s,s)*np.dot(v,v)-2*np.dot(u,s)*np.dot(v,t)-2*np.dot(u,v)*np.dot(s,t)+2*np.dot(u,t)*np.dot(s,v)
def feat(A):
 a,b,c,d=A.flat; z=np.array([1,a,b,c,d,a*d-b*c]); return z, np.array([z[i]*z[j]*(1 if i==j else 2) for i,j in idx])
As=rng.uniform(-2,2,size=(150,2,2));fs=np.stack([feat(A)[1] for A in As]); U,sv,Vt=np.linalg.svd(fs,full_matrices=False)
print('Design singular values tail:',sv[-4:])
J=np.zeros((6,6));J[0,5]=J[5,0]=1/2;J[1,4]=J[4,1]=-1/2;J[2,3]=J[3,2]=1/2
for it in range(15):
 B=rng.normal(size=(2,6))*rng.uniform(.2,3)
 vals=np.array([GG(M+A@B) for A in As])
 vals2=np.linalg.lstsq(fs,vals,rcond=None)[0]
 QQ=np.zeros((6,6));
 for (i,j),val in zip(idx,vals2): QQ[i,j]=QQ[j,i]=val
 def mineig(t):return np.linalg.eigvalsh(QQ+t*J)[0]
 rr=minimize_scalar(lambda t:-mineig(t),bounds=(-500,500),method='bounded',options={'xatol':1e-11})
 print('test',it,'best min eig',round(mineig(rr.x),8),'λ',round(rr.x,6),'res',np.max(abs(fs@vals2-vals)))
