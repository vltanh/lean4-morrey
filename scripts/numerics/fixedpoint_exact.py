import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from exact import *
from fractions import Fraction as Fr
n=2; ifs=interfaces(n); mold={j:[x for pq in ifs[j] for x in pq] for j in (1,2,3)}
lam=[1,0,0,1,0,1,1,0, 1,0,0,1,Fr(1,2),Fr(1,2),Fr(1,2),Fr(1,2), 0,1,1,0,Fr(1,2),Fr(1,2),Fr(1,2),Fr(1,2)]
c=Fr(1,24); t=[]
for j in range(3):
    for i in range(8):
        t+= [c*(1-lam[8*j+i]), c*lam[8*j+i]]
u=[[0,-1],[0,0]]; v=[[0,0],[-1,0]]
Gu,Gv=grads(n,u),grads(n,v)
rows,rhs,names=system(n,mold,Gu,Gu,t)   # Theta rows are the first 32
ok_theta=all(sum(a*b for a,b in zip(rows[i],t))==rhs[i] for i in range(32)) and min(t)>=0
rowsT,rhsT,namesT=system(n,mold,Gu,Gv,t)
par=[sum(a*b for a,b in zip(rowsT[i],t)) for i in range(32,len(rowsT))]
print("t in Theta:",ok_theta,"  all parallelism conditions at t vanish:",all(p==0 for p in par))
