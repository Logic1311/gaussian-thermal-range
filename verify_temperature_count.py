"""Exact independent checks of temperature-level limitation and root-sign stress tests.
No numerical tolerance. Counts exclude the repeated critical construction tests.
"""
import sympy as S
from pathlib import Path
from hashlib import sha256
x=S.Symbol('x')
count=0

def ck(p, label):
    global count
    if not p: raise AssertionError(label)
    count+=1

def eq(a,b,label): ck(S.cancel(a-b)==0,label)

def nonnegative_on_interval(p):
    # Exact certificate: no odd-multiplicity root in the open interval;
    # remove endpoint roots before the Sturm count. A rational interior
    # root is NOT exempt from the odd-multiplicity test.
    p=S.Poly(p,x,domain=S.QQ)
    if p.is_zero:return True
    if p.eval(-1)<0 or p.eval(1)<0:return False
    for f,mult in p.sqf_list()[1]:
        if mult%2==0:continue
        for endpoint in (-1,1):
            if f.eval(endpoint)==0:
                f=f.exquo(S.Poly(x-endpoint,x,domain=S.QQ))
        if f.degree()>0 and f.count_roots(-1,1):return False
    for k in range(2,p.degree()+5):
        v=p.eval(S.Rational(1,k))
        if v!=0:return bool(v>0)
    raise AssertionError('No rational non-root probe')

f=nonnegative_on_interval
# Explicit negative wells between rational roots and endpoint zeros.
R=S.Rational
cases=[(0,True),(1,True),(-1,False),((x+R(7,10))*(x+R(2,5)),False),
       ((x-R(4,5))*(x-R(9,10)),False),((x-R(1,3))**2,True),
       (1-x,True),(1+x,True),(1-x*x,True),((1-x*x)*(x+R(3,5))**2,True),
       (x*x-R(1,2),False),((x*x-R(1,2))**2,True),
       ((1-x)*(1+x)**3,True),(x*(x-R(1,2))*(1-x*x),False),
       ((1-x*x)*(x+R(1,7))*(x+R(2,7)),False)]
for p,want in cases: ck(f(p)==want,('Sturm regression',p,want))
print('PASS exact root-sign regressions:',len(cases),flush=True)
regression_count=count
count=0

# Symbolic independent derivation using affine interpolation; q denotes cold weight.
a,h,d,q,m=S.symbols('a h d q m', positive=True)
qsol=S.solve(q*a+(1-q)*h-d,q)[0]
expr=S.factor((d*(q/a+(1-q)/h)-1).subs(q,qsol))
eq(expr,(d-a)*(h-d)/(a*h),'two-temperature factorization')
eq(expr,(d/a-1)*(1-d/h),'two-temperature monotone factors')
# Fourier arcsine mean from moments x=cos k.
def mean(p):
    return S.factor(sum(c*S.binomial(j[0],j[0]//2)/2**j[0]
                        for j,c in S.Poly(S.expand(p),x).terms() if j[0]%2==0))
D=m+2-2*x
nearest=(D-m)*(m+4-D)/(m*(m+4))
eq(mean(nearest),2/(m*(m+4)),'nearest exact mean')
s=(1-x)/2
W=[(1-s)**2,2*s*(1-s),s**2];T=[m,m+2,m+4]
eq(sum(W),1,'three-rate sum')
eq(sum(t*w for t,w in zip(T,W)),D,'three-rate weighted sum')
for w in W: ck(f(S.expand(w)),'three-rate nonnegativity')
sigma=S.factor(D*sum(w/t for t,w in zip(T,W))-1)
eq(mean(sigma),1/(m*(m+4)),'three-rate half cost')
eq(S.factor(nearest-sigma),2*D*(1-x*x)/(m*(m+2)*(m+4)),'pointwise improvement identity')
# Independently verify full all-interval comparisons and constrained minimum
# on finite rational parameters with arbitrary exterior endpoints.
for M in [R(1,10000),R(1,100),R(1,3),R(1),R(5),R(100)]:
    d0=M+2-2*x; near=nearest.subs(m,M)
    for A in [M/10,M/2,M]:
        for H in [M+4,M+5,2*(M+4),100*(M+4)]:
            u=(H-d0)/(H-A); v=(d0-A)/(H-A)
            ck(f(u),'cold rate nonnegative');ck(f(v),'hot rate nonnegative')
            eq(u+v,1,'two-rate sum');eq(A*u+H*v,d0,'two-rate weighted sum')
            sig=d0*(u/A+v/H)-1
            ck(f(S.expand(sig-near)),'pointwise nearest dominance')
            ck(mean(sig)>=2/(M*(M+4)),'mean two-level optimum')
    sig3=sigma.subs(m,M)
    ck(f(S.expand(near-sig3)),'three-level strict mean gain with pointwise dominance')
    eq(mean(sig3),1/(M*(M+4)),'three-level exact cost')
# Small-m threshold for the critical three-level family; independent scalar checks.
for r in range(2,41):
    C=R(12,(r+1)*(r+2)*(r+3)); M=R(1,40*(r+1)**2)
    ck(C<=R(1,5),'critical coefficient below 1/2')
    ck(C+4*M*(r+1)**2<=R(3,10),'scaled upper at threshold')
    ck(R(3,10)<2/(M+4),'strict two-level exclusion at threshold')
print('PASS independent exact scientific temperature-count assertions:',count,flush=True)
print('Separate software-regression assertions:',regression_count,flush=True)
print('PYTHON_SOURCE_SHA256',sha256(Path(__file__).read_bytes()).hexdigest(),flush=True)
