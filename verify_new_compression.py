import sympy as s
import sys
from itertools import product
checks=0
def check(v):
    global checks
    assert v
    checks+=1
print(sys.version, 'sympy', s.__version__)
# Embed a two-temperature nearest-neighbor realization into arbitrary larger support.
# Split each physical row across a rational unit vector, including a zero channel.
for n,m,(a,b) in product(range(3,9),[s.Rational(1,10000),s.Rational(1,3),s.Integer(2)],[(s.Rational(3,5),s.Rational(4,5)),(s.Rational(5,13),s.Rational(12,13))]):
    R=s.zeros(2,n); R[0,0]=R[0,1]=s.Rational(1,2); R[1,0]=s.Rational(1,2); R[1,1]=-s.Rational(1,2)
    B=s.Matrix([[a,0],[b,0],[0,a],[0,b],[0,0]])
    T=s.diag(m,m,m+4,m+4,7); A=B*R
    H=B.T*B; K=B.T*T*B
    check(A.rank()==2 and A.shape==(5,n)); check(A[4,:]==s.zeros(1,n))
    check(A.T*A==R.T*R); check(A.T*T*A==R.T*K*R)
    check(A.T*T.inv()*A==R.T*K.inv()*R)
    for d in range(n):
        check(sum((A.T*A)[i,i+d] for i in range(n-d))==(1 if d==0 else 0))
        check(sum((A.T*T*A)[i,i+d] for i in range(n-d))==(m+2 if d==0 else -1 if d==1 else 0))
    # Nontrivial strict compression: mix unequal temperatures in each split.
    T=s.diag(m/2,(m-a*a*m/2)/(b*b),(m+4)/2,(m+4-a*a*(m+4)/2)/(b*b),7)
    K=B.T*T*B; check(K==s.diag(m,m+4))
    # Exact weighted square certificate, valid for every complex frequency.
    X=B-T*B*K.inv(); Delta=A.T*T.inv()*A-R.T*K.inv()*R
    check(Delta==R.T*X.T*T.inv()*X*R)
    check(all(t>0 for t in T.diagonal())); check(Delta[:2,:2].det()>0)
    print('PASS rank-deficient strict/equality',n,m,a,b)
print('PASS independent exact certificates:',checks)