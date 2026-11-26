"""Independent exact checks of the critical construction via Chebyshev polynomials.
No numerical sampling or test count from the previous package is reused.
"""
import sympy as s
from fractions import Fraction
x=s.symbols('x')
checks=0

def eq(a,b):
    global checks
    assert s.expand(a-b)==0, (a,b)
    checks+=1

def ck(p):
    global checks
    assert p
    checks+=1

def nonnegative_on_interval(p):
    # Exact Bernstein basis on [-1,1] can be inconclusive. Here use exact
    # real-root multiplicities and rational sign samples between roots.
    p=s.Poly(p,x,domain=s.QQ)
    if p.is_zero:return True
    if p.eval(-1)<0 or p.eval(1)<0:return False
    intervals=p.intervals(eps=s.Rational(1,10**12),inf=-1,sup=1)
    for (a,b),mult in intervals:
        if a==b and a in (-1,1):continue
        if mult%2: return False
    for k in range(2, p.degree()+5):
        v=p.eval(s.Rational(1,k))
        if v!=0:return v>0
    raise AssertionError('No rational non-root probe')

# Exact arcsine moment on x=cos k.
def mean(p):
    p=s.Poly(p,x)
    return sum(co*s.binomial(j[0],j[0]//2)/2**j[0] for j,co in p.terms() if j[0]%2==0)

for r in range(1,11):
    n=r+1; S=s.Rational(n*(n+1)*(n+2),6); C=2/S
    a=[s.Rational((j+1)*(n-j),1)/S for j in range(n)]
    eq(sum(a),1); ck(all(v>0 for v in a))
    # independent recurrence in x rather than Laurent coefficients
    w0=s.expand(sum(a[i]*a[j]*s.chebyshevt(abs(i-j),x) for i in range(n) for j in range(n)))
    D0=2-2*x; R=1-w0; A=s.Rational(1,n*n); B=A+1+2/(a[0]*a[1]);
    eq(mean(D0*w0),C); eq(w0.subs(x,1),1)
    w1=s.expand((B*R-D0)/(B-A)); w2=s.expand((D0-A*R)/(B-A))
    for w in (w0,w1,w2):
        ck(s.Poly(w,x).degree()<=r or w==0)
        ck(nonnegative_on_interval(w))
    eq(w0+w1+w2,1); eq(A*w1+B*w2,D0)
    # Independent Dirichlet solution via exact linear system.
    K=s.diag(*([2]*n));
    for i in range(n-1):K[i,i+1]=K[i+1,i]=-1
    u=K.inv()*s.ones(n,1); eq((s.ones(1,n)*u)[0],1/C)
    eq((s.Matrix(a).T*K*s.Matrix(a))[0],C)
    for m in (s.Rational(1,100000),s.Rational(1,100),s.Rational(1,3),s.Rational(1),s.Rational(10)):
        D=m+D0
        eq(m*w0+(m+A)*w1+(m+B)*w2,D)
        sigma=s.expand(D*(w0/m+w1/(m+A)+w2/(m+B))-1)
        cost=mean(sigma)
        ck(nonnegative_on_interval(sigma))
        ck(C/m-1<=cost<=C/m+4/A)
        ck(C-m<=m*cost<=C+4*m/A)
    print('PASS range',r,'C_r',C,'hot increments',A,B,flush=True)
print('PASS exact critical-extension assertions:',checks,flush=True)
