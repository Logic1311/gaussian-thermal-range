from fractions import Fraction as F
import sys, hashlib
from pathlib import Path
count=0
def check(x,label):
    global count
    assert x,label
    count+=1
def inverse(A):
    n=len(A)
    B=[list(row)+[F(i==j) for j in range(n)] for i,row in enumerate(A)]
    for i in range(n):
        k=next(k for k in range(i,n) if B[k][i])
        B[i],B[k]=B[k],B[i]
        d=B[i][i]; B[i]=[x/d for x in B[i]]
        for k in range(n):
            if k!=i:
                d=B[k][i]
                B[k]=[x-d*y for x,y in zip(B[k],B[i])]
    return [row[n:] for row in B]
def matrix(n,c,rho,cycle=False):
    return [[c if i==j else -1/rho if abs(i-j)==1 or (cycle and abs(i-j)==n-1) else F(0) for j in range(n)] for i in range(n)]
def laurent(A,u,S):
    n=len(u)
    return {d:sum((u[i]*u[j]*A[i][j]/S for i in range(n) for j in range(n) if j-i==d),F(0)) for d in range(1-n,n)}
def evaluate(a,x):
    n=max(abs(d) for d in a)
    C=[F(1),x]
    for j in range(2,n+1): C.append(2*x*C[-1]-C[-2])
    return sum(v*C[abs(d)] for d,v in a.items())
def positive_path(n,c,rho):
    a,b=F(1),c
    if b<=0:return False
    for k in range(2,n+1):
        a,b=b,c*b-a/rho**2
        if b<=0:return False
    return True
print(sys.version,flush=True)
for n in range(2,13):
    u=[F((j+1)*(n-j)) for j in range(n)]
    S=sum(x*x for x in u); rho=sum(u[j]*u[j+1] for j in range(n-1))/S
    L=(n+1)**2+1
    for m in [F(1,10000),F(1,100),F(1),F(10),F(10,L-5)]:
        c=m+2; M=matrix(n,c,rho)
        I=[[F(i==j) for j in range(n)] for i in range(n)]
        a=laurent(I,u,S); b=laurent(M,u,S)
        check(all(v==F(d==0) for d,v in a.items()),('normal',n,m))
        check(all(v==(c if d==0 else -1 if abs(d)==1 else 0) for d,v in b.items()),('weighted',n,m))
        second=sum(u[i]**2*sum(v*v for v in M[i])/S for i in range(n))
        residual=second-c*c-2
        check(residual==(2-(u[0]**2+u[-1]**2)/S)/rho**2-2,('residual',n,m))
        check(residual>=0,('nonnegative',n,m))
        pos=positive_path(n,c,rho); cyclic=c>2/rho
        check(not cyclic or pos,('positive compression',n,m))
        if not pos:
            print('path excluded exact Sylvester',n,m,flush=True)
            continue
        P=laurent(inverse(M),u,S); C=None
        if cyclic:
            N=2*n+3
            Q=inverse(matrix(N,c,rho,True))
            C=laurent([row[:n] for row in Q[:n]],u,S)
        for t in [F(-3),F(-1),F(-1,3),F(0),F(1,3),F(1),F(3)]:
            x=(1-t*t)/(1+t*t); D=c-2*x
            sig=D*evaluate(P,x)-1
            check(sig>=0,('path entropy',n,m,t))
            if C is not None:
                check(sig<=D*evaluate(C,x)-1,('compression',n,m,t))
        if m==F(10,L-5):
            check(c==2/rho and pos,('cyclic critical path positive',n,m))
print('PASS exact independent path checks:',count)
print('SHA256',hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
