#!/usr/bin/env python3
"""Independent exact checks for the finite-range entropy barrier.

All entries and polynomial coefficients are rational. Sturm root counts of odd
square-free factors certify the sign on the entire closed interval [-1,1].
There is no floating-point tolerance or frequency sampling in these checks.
"""
from itertools import product
from pathlib import Path
import hashlib
import sys
import sympy as s

x=s.Symbol('x'); Q=s.Rational
count=0

def check(ok,label,context):
    global count
    if not ok:
        print('FAIL',label,context,flush=True)
        raise AssertionError((label,context))
    count+=1

def eq(a,b,label,context):
    check(s.expand(a-b)==0,label,(context,s.expand(a-b)))

def poly(q): return s.Poly(q,x,domain=s.QQ)

def avg(q):
    # Integral moments of cos(k): E[cos(k)^(2j)]=binom(2j,j)/4^j.
    return sum(a*s.binomial(k,k//2)/2**k for (k,),a in poly(q).terms() if k%2==0)

def nonnegative(q):
    p=poly(q)
    if p.is_zero: return True,('zero',)
    if p.eval(-1)<0 or p.eval(1)<0:
        return False,('negative endpoint',p.eval(-1),p.eval(1))
    # Odd-multiplicity interior roots force sign changes. Even factors cannot.
    roots=[]
    for f,k in p.sqf_list()[1]:
        for a in (-1,1):
            if f.eval(a)==0: f=f.exquo(poly(x-a))
        if f.degree()>0 and k%2:
            c=f.count_roots(-1,1)
            roots.append((str(f.as_expr()),k,int(c)))
            if c: return False,('odd interior root',roots[-1])
    # No odd interior roots. Evaluate at a guaranteed non-root rational point.
    for d in range(1,p.degree()+3):
        v=Q(1,d+1)
        h=p.eval(v)
        if h: return bool(h>0),('no odd interior roots',roots,'sign',str(v),str(h))
    raise AssertionError('Nonzero polynomial has too many roots')

def certify(q,label,context):
    ok,cert=nonnegative(q)
    check(ok,label,(context,cert))

def gram_poly(B):
    n=B.rows
    return s.expand(sum(B[i,j]*s.chebyshevt(abs(i-j),x) for i in range(n) for j in range(n)))

def tangent_poly(B):
    # Im[(zP'(z))conj(P(z))]/sin(k) in the real Gram representation.
    n=B.rows
    return s.expand(sum(i*B[i,j]*(1 if i>j else -1)*s.chebyshevu(abs(i-j)-1,x)
                        for i in range(n) for j in range(n) if i!=j))

def relaxed(t,r):
    p=r+1
    return 2*t**p/(sum(t**(2*j) for j in range(p+1))-(p+1)*t**p)

def constants(t,r):
    c=t+1/t
    S=sum(j*j for j in range(r+1))
    h=c*c/4-1
    delta=1/(c*(c+2)*S)
    L=relaxed(t,r)
    return c,S,h,delta,L,1-delta*h,L+delta*(Q(1,2)-h*L)

def test_gram(B,C,H,t,tag):
    n=B.rows;r=n-1
    c,S,h,delta,L,K,lower=constants(t,r)
    D=c-2*x
    ctx=(tag,r,str(t),B.rank())
    eq(gram_poly(B),1,'full normalization',ctx)
    eq(gram_poly(C),D,'full temperature normalization',ctx)
    eq(s.trace(C),c,'weighted Parseval',ctx)
    eq(tangent_poly(B),0,'unweighted Euler angular identity',ctx)
    eq(tangent_poly(C),-1,'weighted Euler angular identity',ctx)
    J=gram_poly(s.diag(*range(n))*C*s.diag(*range(n)))
    certify(c*S-J,'uniform derivative-energy bound',ctx)
    g=gram_poly(H);sig=s.expand(D*g-1)
    res=gram_poly(C)-2*D*gram_poly(B)+D**2*g
    eq(res,D*sig,'weighted residual identity',ctx)
    certify(c*S*D*sig-(1-x*x),'strong pointwise barrier',ctx)
    rem=s.expand(sig-delta*(1-x*x))
    certify(rem,'constant pointwise barrier',ctx)
    eq(rem.subs(x,c/2),-K,'root constraint after subtracting barrier',ctx)
    check(K>0,'positive root normalization',ctx)
    q=s.expand(rem/K)
    quo,rest=s.div(poly(q+1),poly(D))
    check(rest.is_zero and quo.degree()<=r,'reverse polynomial realization in majorant',ctx)
    certify(q,'normalized residual nonnegative',ctx)
    eq(avg(rem),avg(sig)-delta/2,'exact averaged barrier',ctx)
    check(avg(sig)>=lower,'strengthened finite-r physical lower bound',ctx)
    print('PASS physical certificate',ctx,'cost',avg(sig),'bound',lower,flush=True)

def rational_unit(k):
    # rational points on the positive part of the sphere, k>=2
    if k==1:return [Q(1)]
    u=[Q(j+1,10*k*k) for j in range(k-1)]
    q=sum(a*a for a in u)
    return [(1-q)/(1+q)]+[2*a/(1+q) for a in u]

def translated_family(r,t,split,rank):
    # Several shifted nearest-neighbor implementations; each pair may be split
    # into unequal-temperature baths via exact rational amplitudes.  An explicit
    # zero-amplitude bath is included. Truncation of shifts gives rank deficiency.
    m=t+1/t-2;n=r+1
    g=rational_unit(rank-1); rows=[]; temps=[]
    for j,a in enumerate(g):
        for sign,T in [(1,m),(-1,m+4)]:
            row=[Q(0)]*n;row[j]=a/2;row[j+1]=sign*a/2
            if split:
                eps=T/3
                for b,T2 in [(Q(3,5),T-eps),(Q(4,5),T+Q(9,16)*eps)]:
                    rows.append([b*v for v in row]);temps.append(T2)
            else: rows.append(row);temps.append(T)
    rows.append([Q(0)]*n);temps.append(m+1)
    A=s.Matrix(rows);T=s.diag(*temps)
    assert all(a>0 for a in temps)
    assert A.rank()==rank
    return A.T*A,A.T*T*A,A.T*T.inv()*A

def path_family(r,t):
    n=r+1;c=t+1/t
    g=rational_unit(n);rho=sum(g[j]*g[j+1] for j in range(n-1))
    J=s.zeros(n)
    for j in range(n-1):J[j,j+1]=J[j+1,j]=1
    M=c*s.eye(n)-J/rho; G=s.diag(*g)
    if any(M[:k,:k].det()<=0 for k in range(1,n+1)): return None
    return G*G,G*M*G,G*M.inv()*G

print(sys.version,'SymPy',s.__version__,'source_sha256',hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),flush=True)
# Exact relaxed minima: use a rank-two outer-product polynomial and independently
# verify the averaged barrier forces strict infeasibility for every tested r>=2.
for t,r in product([Q(101,100),Q(5,4),Q(3,2),Q(2),Q(4)],range(1,11)):
    c,S,h,delta,L,K,lower=constants(t,r);p=r+1;ctx=(str(t),r)
    check(L>0 and 0<K<1,'relaxed and normalized positivity',ctx)
    eq(delta*h,(c-2)/(4*c*S),'exact barrier normalization',ctx)
    u=s.Matrix([t**j-t**(p-j) for j in range(p+1)])
    qq=(u.T*u)[0]
    B=(4*t**p/qq**2)*u*u.T
    qopt=gram_poly(B)
    eq(qopt.subs(x,c/2),-1,'relaxed minimizer root',ctx)
    eq(avg(qopt),L,'relaxed minimizer mean',ctx)
    certify(qopt,'relaxed minimizer nonnegative',ctx)
    if r==1:
        eq(L,1/(2*h),'nearest-neighbor exact equality',ctx)
        eq(lower,L,'zero finite-gap improvement at r=1',ctx)
    else:
        check(lower>L,'strict finite-gap constant',ctx)
        ok,cert=nonnegative(qopt-delta*(1-x*x))
        check(not ok,'relaxed minimizer violates physical barrier', (ctx,cert))
        print('PASS nonrealizable relaxed minimizer',ctx,cert,flush=True)
# Physical checks at ranks 2 through r+1 and variable positive bath temperatures.
for t,r in product([Q(101,100),Q(3,2),Q(4)],range(1,7)):
    for rank in sorted({2,r+1}):
        for split in (False,True):
            test_gram(*translated_family(r,t,split,rank),t,('translated',split))
    G=path_family(r,t)
    if G is not None: test_gram(*G,t,'rational-window path')
    else: print('EXCLUDED non-SPD rational-window path',r,t,flush=True)
print('PASS independent finite-gap assertions:',count,flush=True)
