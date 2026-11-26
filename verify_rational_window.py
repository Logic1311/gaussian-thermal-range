from fractions import Fraction as F
import hashlib, sys
from pathlib import Path
count=0
for n in range(2,1001):
    u=[(j+1)*(n-j) for j in range(n)]
    A=sum(x*x for x in u)
    B=sum(x*y for x,y in zip(u,u[1:]))
    assert 30*A==n*(n+1)*(n+2)*(n*n+2*n+2)
    assert F(B,A)==1-F(5,n*n+2*n+2)
    count+=2
    rho=F(B,A)
    for m in [F(1,1000),F(1,10),F(1),F(10),F(100)]:
        c=m+2
        if c<=2/rho: continue
        var=2*(1/rho**2-1)
        upper=var/(m*(c-2/rho))
        assert var>=0 and upper>=0
        if 10*(m+4)<=m*(n*n+2*n+2):
            assert c-2/rho>=m/2
            assert upper<=F(80,1)/(m*m*(n*n+2*n+2))
        count+=2
print('Exact rational checks:',count)
print('Python:',sys.version)
print('SHA256:',hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
