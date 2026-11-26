"""Independent real spectral-factor, odd-rate and relaxation separation certificates.
All arithmetic is rational or exact SymPy algebra. No sampled frequency checks.
"""
import sys
import sympy as S
from itertools import product

x,z=S.symbols('x z', real=True)
Q=S.Rational
count=0
def check(v,label,detail=None):
    global count
    if not v:
        raise AssertionError((label,detail))
    count+=1
def equal(a,b,label):
    check(S.cancel(S.expand(a-b))==0,label,(a,b))
def lift(p):
    return S.expand(p.subs(x,(z+1/z)/2))
def norm(p):
    return S.expand(p*p.subs(z,1/z))
def linear(a,b):
    assert a>=abs(b)
    u=(S.sqrt(a+b)+S.sqrt(a-b))/2
    v=(S.sqrt(a+b)-S.sqrt(a-b))/2
    return S.expand(u+v*z)
def quad(a,b2):
    assert b2>=0
    A=S.sqrt((a+1)**2+b2)
    B=S.sqrt((a-1)**2+b2)
    u=(A+B)/2; v=(A-B)/2
    d=S.sqrt(S.simplify(u*u-1))
    return S.expand((u-d)/2-v*z+(u+d)*z*z/2)

print(sys.version, 'SymPy',S.__version__)
# Factor by real roots: endpoints, strictly outside, and repeated interior.
# Each nonnegative factor is checked on the whole unit circle via Laurent identity.
for a in [-3,-1,Q(-2,3),0,Q(4,5),1,4]:
    if -1<a<1:
        h=(x-a)**2
        P=quad(Q(a),Q(0))
        degree=2
    elif a<=-1:
        h=x-a
        P=linear(Q(-a),Q(1))
        degree=1
    else:
        h=a-x
        P=linear(Q(a),Q(-1))
        degree=1
    equal(norm(P),lift(h),'real-root factor')
    check(S.Poly(P,z).degree()<=degree,'real-root degree',a)
    check(all(c.is_real for c in S.Poly(P,z).all_coeffs()),'real coefficients',a)
    print('PASS real-root',a,degree)

# Non-real conjugate roots parameterized to give exact rational radicals.
# Combine with endpoint and interior factors; includes zeros on the circle.
for t,v in product([Q(2),Q(3),Q(5,3),Q(7,4)], [Q(0),Q(3,5),Q(-5,13),Q(4,5)]):
    u=(t+1/t)/2; d=(t-1/t)/2
    a=u*v; b2=d*d*(1-v*v)
    h=x*x-2*a*x+a*a+b2
    P=quad(a,b2)
    check(b2>0,'nonreal roots')
    equal(P,(u-d)/2-v*z+(u+d)*z*z/2,'explicit factor')
    equal(norm(P),lift(h),'quadratic identity')
    mixed=h*(1-x)*(1+x)*(x-Q(1,3))**2
    F=P*linear(Q(1),Q(-1))*linear(Q(1),Q(1))*quad(Q(1,3),Q(0))
    equal(norm(F),lift(mixed),'multiplicative certificate')
    check(S.Poly(F,z).degree()<=6,'degree budget')
    check(all(c.is_Rational for c in S.Poly(F,z).all_coeffs()),'rational factor')
    print('PASS mixed',t,v,a,b2)

# Original odd polynomial rates: three distinct positive temperatures.
# The odd perturbation is in the joint kernel of the two physical constraints,
# but changes the inverse-temperature weight before symmetrization.
for m,s in product([Q(1,10000),Q(1,100),Q(1,3),Q(2),Q(10)],range(1,9)):
    c=m+2; b=1/(c-m/2); a=(b+Q(1,2))/2
    eps=min(a-b,(1-2*a)/2)/2
    T=[m/2,c,2*c-m/2]
    check(eps>0 and all(t>0 for t in T),'positive margins')
    odd=(z**s-z**(-s))/(2*S.I)
    w=[a+b*(z+1/z)/2+eps*odd,1-2*a-2*eps*odd,a-b*(z+1/z)/2+eps*odd]
    # uniform proof using |cos|, |sin|<=1
    check(a-b-eps>0 and 1-2*a-2*eps>0,'uniform positivity')
    equal(sum(w),1,'normalization')
    D=c-z-1/z
    equal(sum(t*y for t,y in zip(T,w)),D,'temperature normalization')
    we=[S.expand((y+y.subs(z,1/z))/2) for y in w]
    P=[linear(a,b),S.sqrt(1-2*a),linear(a,-b)]
    for w0,p0 in zip(we,P):
        equal(norm(p0),w0,'real FIR of symmetrized rate')
    sig=S.expand(D*sum(y/t for t,y in zip(T,w))-1)
    sige=S.expand(D*sum(y/t for t,y in zip(T,we))-1)
    equal((sig+sig.subs(z,1/z))/2,sige,'symmetrized entropy pointwise')
    equal(sig.coeff(z,0),sige.coeff(z,0),'exact average')
    check(S.expand(sig-sige)!=0,'nontrivial odd contribution')
    print('PASS odd-rate physical',m,s,eps)

# Exact finite-size exponential comparison, independent of rank-two solver.
# A finite geometric sum supplies bounds on the known relaxed value.
for t,p in product([Q(101,100),Q(5,4),Q(3,2),Q(2),Q(5)],range(2,41)):
    q=sum(t**(2*j) for j in range(p+1))-(p+1)*t**p
    closed=(t**(2*(p+1))-1)/(t*t-1)-(p+1)*t**p
    equal(q,closed,'geometric form')
    check(q>0,'strict denominator')
    L=2*t**p/q
    check(L>=2*(1-t**-2)*t**-p,'exponential lower')
    # Sufficient condition for the eventual upper bound, not a threshold claim.
    if t**p>=2*(p+1):
        check(L<=4*t**-p,'exponential upper')
    if p in [2,20,40]:
        print('PASS gap',t,p,'upper-domain',t**p>=2*(p+1))
print('PASS independent spectral/symmetry/gap assertions:',count)