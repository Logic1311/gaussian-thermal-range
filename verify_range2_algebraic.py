#!/usr/bin/env python3
"""Exact cross-check for the range-two algebraic optimum, independent of Lean.
Only symbolic polynomial identities, rational root isolation, interval arithmetic,
and principal-minor certificates are used. Finite cases are not a general proof.
The three prior SDP certificates are replayed separately and are not new cases.
"""
import json
from pathlib import Path
from itertools import combinations
import sympy as s
from sympy import Rational as R, Matrix, eye, zeros, diag, trace
P=Path(__file__).resolve().parent
c,e,a,m=s.symbols('c e a m', real=True)
q=c-2*e; D=e*q-R(1,2); B=4*c*c*e-c+8*e
N=32*c**3*e**4+(128-64*c**4)*e**3+(16*c**5+20*c**3-40*c)*e**2-8*c**4*e+c**3+2*c
astar=2*e*(2*c*e+1)/B
H=Matrix([[e,-R(1,2),0],[-R(1,2),q,-R(1,2)],[0,-R(1,2),e]])
Q=Matrix([[c,-1,0],[-1,c,-1],[0,-1,c]])
G=diag(astar,1-2*astar,astar)
# Independent derivation: invert H symbolically, do not use the Lean K formula.
K=(H.inv()*G).applyfunc(s.factor); J=G*K
U=(K*Q+Q*K.T).applyfunc(s.factor); V=(K*Q*K.T).applyfunc(s.factor)
f=2*e*(4*c**3*e-8*c**2*e**2-c**2-2)/((2*c*e-4*e**2-1)*B)

def eq(x,y):
    if isinstance(x,Matrix):
        assert x.shape==y.shape
        for d in x-y: assert s.cancel(d)==0,d
    else: assert s.cancel(x-y)==0,(x,y)

def lags(A): return tuple(sum(A[i,i+k] for i in range(A.rows-k)) for k in range(A.rows))
def toe(A): return Matrix(A.rows,A.cols,lambda i,j:A[0,abs(i-j)])
def pd(A): return A==A.T and all(A[:i,:i].det()>0 for i in range(1,A.rows+1))
def psd(A):
    assert A==A.T
    return all(A.extract(I,I).det()>=0 for k in range(1,A.rows+1) for I in combinations(range(A.rows),k))

# Symbolic identities (report groups separately; not the finite case counter).
F=trace(Q*diag(a,1-2*a,a)*H.inv()*diag(a,1-2*a,a))
eq(F,c*a*a/e+(c*q*a*a+c*e*(1-2*a)**2-2*a*(1-2*a))/D)
eq(s.diff(F,a).subs(a,astar),0)
eq(s.diff(F,a,2),B/(e*D))
eq(trace(Q*J),f)
eq(s.diff(f,e),-2*N/((2*c*e-4*e**2-1)**2*B**2))
eq(U,toe(U))
eq(V-toe(V),diag(0,-N/(2*D*B)**2,0))
w=2*c*e+1;u=w*(4*D+1);v=B-4*e*w;x=2*e*w;y=2*e*v
eq(K,Matrix([[u,v,w],[x,y,x],[w,v,u]])/(2*D*B))
eq(N.subs({e:(m+2)/4,c:m+2}),m**7/8+7*m**6/4+39*m**5/4+55*m**4/2+81*m**3/2+27*m**2+4*m)
eq(N.subs({e:(3*(m+2)-2)/8,c:m+2}),-m*(63*m**6+618*m**5+2380*m**4+4552*m**3+4368*m**2+2144*m+768)/128)
eq(trace(U*G)-trace(V*H),trace(Q*J))
eq(B-2*(2*e*(2*c*e+1)),4*c*D+c+4*e)
print('SYMBOLIC_IDENTITY_GROUPS 12 PASS')

class I:
    def __init__(self,l,u=None): self.l=R(l); self.u=R(l if u is None else u); assert self.l<=self.u
    def __add__(self,o):
        o=iv(o); return I(self.l+o.l,self.u+o.u)
    __radd__=__add__
    def __neg__(self): return I(-self.u,-self.l)
    def __sub__(self,o): return self+-iv(o)
    def __rsub__(self,o): return iv(o)+-self
    def __mul__(self,o):
        o=iv(o); L=[self.l*o.l,self.l*o.u,self.u*o.l,self.u*o.u]; return I(min(L),max(L))
    __rmul__=__mul__
    def __truediv__(self,o):
        o=iv(o); assert not o.l<=0<=o.u; return self*I(1/o.u,1/o.l)
    def __rtruediv__(self,o): return iv(o)/self
    def __pow__(self,n):
        assert n>=0; out=I(1)
        for _ in range(n):out=out*self
        return out
    def out(self,places=18):
        n=10**places
        lo=int(s.floor(self.l*n)); hi=int(s.ceiling(self.u*n))
        def d(k):return ('-' if k<0 else '')+str(abs(k)//n)+'.'+str(abs(k)%n).zfill(places)
        return [d(lo),d(hi)]

def iv(o): return o if isinstance(o,I) else I(o)
def interval_f(C,E):
    DD=E*(C-2*E)-R(1,2); BB=4*C*C*E-C+8*E
    # Stable objective from positive definite inverse, independent of f formula.
    AA=2*E*(2*C*E+1)/BB; BB0=1-2*AA
    return C*AA**2/E+(C*(C-2*E)*AA**2+C*E*BB0**2-2*AA*BB0)/DD-1

previous=json.loads((P/'previous_range2_certificates.json').read_text())
prev_by_mass={R(d['m']):d for d in previous}
rows=[]
for M in map(R,['1/10000','1/1000','1/100','1/10','1/3','1/2','1','2','3','10','100','1000']):
    C=M+2; lo=C/4; hi=(3*C-2)/8
    p=s.Poly(N.subs(c,C),e)
    assert p.eval(lo)>0 and p.eval(hi)<0
    assert p.count_roots(lo,hi)==1  # independent exact Sturm isolation
    # Exact bisection is sufficient now; no numeric polynomial root finder.
    for _ in range(180):
        t=(lo+hi)/2; z=p.eval(t)
        if z==0: lo=hi=t; break
        if z>0: lo=t
        else: hi=t
    E=I(lo,hi); cost=interval_f(C,E)
    assert cost.l>0 and cost.u<1/(M*(M+4))
    assert cost.u-cost.l<R(1,10**35)
    Dint=E*(C-2*E)-R(1,2); Bint=4*C*C*E-C+8*E
    Aint=2*E*(2*C*E+1)/Bint
    assert E.l>R(1,2) and (C-2*E).l>1 and Dint.l>0 and Aint.l>0 and (1-2*Aint).l>0
    if M in prev_by_mass:
        prior=prev_by_mass[M]
        assert R(prior['lower_rational'])<=cost.l<=cost.u<=R(prior['upper_rational'])
    row={'m':str(M),'e_interval_rational':[str(lo),str(hi)],'cost_interval_rational':[str(cost.l),str(cost.u)],'e_outward_18':E.out(),'cost_outward_18':cost.out(),'sturm_root_count':1,'previous_interval_contains_new':M in prev_by_mass}
    rows.append(row)
    print('RANGE2',str(M),'e',E.out(),'cost',cost.out())

# Independently replay the earlier three rational SDP primal-dual certificates.
# Use all principal minors (not the earlier Schur elimination checker).
for prior in previous:
    M=R(prior['m']); C=M+2; E=R(prior['e']); A=R(prior['a']);
    sub={c:C,e:E}; g=G.subs(sub);h=H.subs(sub);j=J.subs(sub);qq=Q.subs(sub)
    eq(g,diag(A,1-2*A,A)); assert pd(g) and pd(h) and pd(qq)
    assert lags(g)==(1,0,0) and lags(h)==(C,-1,0)
    primal=h.row_join(g).col_join(g.row_join(j)); assert psd(primal)
    # Previous certificate construction, using a separate explicit lag projector.
    def project(M):return Matrix(3,3,lambda i,j:sum(M[k,k+abs(i-j)] for k in range(3-abs(i-j)))/(3-abs(i-j)))
    C0=-h.inv()*g*qq; S=(C0+C0.T)/2; cross=C0-S+project(S)
    W=cross*qq.inv()*cross.T; VP=project(W); error=VP-W
    delta=max(sum(abs(error[i,j]) for j in range(3)) for i in range(3))+R(1,10**12)
    VP+=delta*eye(3); Z=VP.row_join(cross).col_join(cross.T.row_join(qq))
    assert psd(Z); assert -(cross+cross.T)==toe(-(cross+cross.T)); assert VP==toe(VP)
    lower=trace(-(cross+cross.T)*g)-trace(VP*h)-1; upper=trace(qq*j)-1
    assert lower==R(prior['lower_rational']) and upper==R(prior['upper_rational'])
    assert upper-lower==trace(Z*primal)>=0
print('HISTORICAL_RANGE2_CERTIFICATES_REPLAYED 3 PASS (NOT NEW CASES)')
print('NEW_EXACT_STRUCTURED_CASES',len(rows))
(P/'range2_algebraic_intervals.json').write_text(json.dumps(rows,indent=2)+'\n')
