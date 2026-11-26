from fractions import Fraction as F
from collections import defaultdict
from pathlib import Path
import sys, hashlib
# Independent route: cyclic adjacency matrix, not sampled trigonometric weights.
def mul(a,b):
    c=defaultdict(F)
    for i,x in a.items():
        for j,y in b.items(): c[i+j]+=x*y
    return {i:x for i,x in c.items() if x}
checks=0
for n in range(2,41):
    N=2*n+3
    u=[(j+1)*(n-j) for j in range(n)]
    S=sum(x*x for x in u)
    rho=F(sum(u[j]*u[j+1] for j in range(n-1)),S)
    # A is the cyclic adjacency; entries of A^2 count two-step walks.
    def A(i,j): return int((i-j)%N in (1,N-1))
    def A2(i,j): return sum(A(i,k)*A(k,j) for k in range(N))
    masses=[F(1,100),F(1),F(10),10/(F(n*n+2*n+2)-5)]
    for m in masses:
        c=m+2
        tmin=c-2/rho
        assert (tmin>0)==(m>10/(F(n*n+2*n+2)-5))
        checks+=1
        p=[defaultdict(F) for _ in range(3)]
        for i in range(n):
            for j in range(n):
                q=F(u[i]*u[j],S)
                p[0][j-i]+=q*int(i==j)
                p[1][j-i]+=q*(c*int(i==j)-A(i,j)/rho)
                p[2][j-i]+=q*(c*c*int(i==j)-2*c*A(i,j)/rho+A2(i,j)/rho**2)
        D={0:c,1:F(-1),-1:F(-1)}
        for d in range(-n,n+1):
            assert p[0][d]==int(d==0)
            assert p[1][d]==D.get(d,0)
            checks+=2
        residual=p[2][0]-mul(D,D)[0]
        assert residual==2*(rho**-2-1)
        checks+=1
        if tmin>0:
            upper=residual/(m*tmin)
            L=F(n*n+2*n+2)
            assert upper==10*(2*L-5)/(m*(L-5)*(m*(L-5)-10))
            assert upper>=1/(c*(c+2)*(n-1)**2)
            checks+=2
            if L>=10+20/m:
                assert upper<=80/(m*m*L)
                checks+=1
        print(f'n={n} N={N} m={m} rho={rho} Tmin={tmin} residual={residual}')
print('PASS',checks,'exact checks')
print(sys.version)
print('SHA256',hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
