"""Exact rational versions of the constructions of model.py (gradients, the linear system of T(t))."""
import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fractions import Fraction as Fr
import itertools, sympy as sp
from model import tri_index, interfaces, tree_nodes

def grads(n, w):
    G = [None]*(2*n*n)
    for a in range(n):
        for b in range(n):
            w00=w[a%n][b%n]; w10=w[(a+1)%n][b%n]; w01=w[a%n][(b+1)%n]; w11=w[(a+1)%n][(b+1)%n]
            G[tri_index(n,0,a,b)] = (n*(w10-w00), n*(w01-w00))
            G[tri_index(n,1,a,b)] = (n*(w11-w01), n*(w11-w10))
    return G

def system(n, mold, Gu, Gv, t):
    NL=4*n*n; NI=2*n*n; tot=3*NL; c=Fr(1,3*NI)
    rows=[]; rhs=[]; names=[]
    for j in (1,2,3):
        for i in range(NI):
            r=[Fr(0)]*tot; r[(j-1)*NL+2*i]=1; r[(j-1)*NL+2*i+1]=1; rows.append(r); rhs.append(c); names.append(f"pair j{j} i{i}")
    for s in range(2*n*n):
        r=[Fr(0)]*tot
        for j in (1,2,3):
            for k in range(NL):
                if mold[j][k]==s: r[(j-1)*NL+k]=1
        rows.append(r); rhs.append(Fr(1,2*n*n)); names.append(f"tri {s}")
    # linear maps r -> direction, as list of (coef vector for x, coef vector for y)
    def dirs(G):
        out=[]; roots={}
        for j in (1,2,3):
            X=[]
            for i in range(NI):
                mx=[Fr(0)]*tot; my=[Fr(0)]*tot
                for k in (2*i,2*i+1):
                    g=(j-1)*NL+k; gx,gy=G[mold[j][k]]
                    mx[g]=Fr(gx)/c; my[g]=Fr(gy)/c
                X.append((mx,my))
            def avg(S):
                return ([sum(X[i][0][g] for i in S)/len(S) for g in range(tot)],
                        [sum(X[i][1][g] for i in S)/len(S) for g in range(tot)])
            for (L,R) in tree_nodes(NI):
                aL=avg(L); aR=avg(R)
                out.append(([aL[0][g]-aR[0][g] for g in range(tot)],[aL[1][g]-aR[1][g] for g in range(tot)], f"node j{j} {L}|{R}"))
            roots[j]=avg(list(range(NI)))
        r1,r2,r3=roots[1],roots[2],roots[3]
        out.append(([r1[0][g]-r2[0][g] for g in range(tot)],[r1[1][g]-r2[1][g] for g in range(tot)],"final W1-W2"))
        out.append(([(r1[0][g]+r2[0][g])/2-r3[0][g] for g in range(tot)],[(r1[1][g]+r2[1][g])/2-r3[1][g] for g in range(tot)],"final (W1+W2)/2-W3"))
        return out
    Du=dirs(Gu); Dv=dirs(Gv)
    for (ux,uy,nm),(vx,vy,_) in zip(Du,Dv):
        Ux=sum(a*b for a,b in zip(ux,t)); Uy=sum(a*b for a,b in zip(uy,t))
        rows.append([Ux*vy[g]-Uy*vx[g] for g in range(tot)]); rhs.append(Fr(0)); names.append("par "+nm)
    return rows,rhs,names
