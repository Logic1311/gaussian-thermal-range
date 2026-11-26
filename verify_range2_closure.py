#!/usr/bin/env python3
"""Independent all-parameter rational Bernstein sign certificates.
This checker tests universal symbolic sign certificates, not sampled mass values.
It does not import Lean code or use a numerical root finder.
Count groups separately from the legacy finite science-case total.
"""
from math import comb
import sympy as S
import json
from pathlib import Path
m,t=S.symbols("m t")
c=m+2
e=c/4+m*t/8
q=c-2*e
D=e*q-S.Rational(1,2)
B=4*c*c*e-c+8*e
N=32*c**3*e**4+(128-64*c**4)*e**3+(16*c**5+20*c**3-40*c)*e**2-8*c**4*e+c**3+2*c

def bernstein(expr, degree):
    p=S.Poly(S.expand(expr),t)
    assert p.degree()<=degree
    b=[S.expand(sum(p.nth(k)*S.Rational(comb(i,k),comb(degree,k))
                    for k in range(i+1))) for i in range(degree+1)]
    rebuilt=sum(b[i]*comb(degree,i)*t**i*(1-t)**(degree-i) for i in range(degree+1))
    assert S.expand(rebuilt-expr)==0
    return b

def positive_coefficients(p):
    v=S.Poly(p,m)
    assert not v.is_zero and all(k>=0 for k in v.all_coeffs())
    assert any(k>0 for k in v.all_coeffs())
    # m>0 makes every monomial with positive coefficient strictly positive.

checks=[
    ("negative_derivative", -S.diff(128*N,t),3),
    ("left_endpoint",128*N.subs(t,0),0),
    ("negative_right_endpoint",-128*N.subs(t,1),0),
    ("outer_diagonal_margin",e-S.Rational(1,2),1),
    ("inner_diagonal_margin",q-1,1),
    ("determinant_factor",D,2),
    ("rational_denominator_B",B,1),
    ("cold_gram_numerator",2*e*(2*c*e+1),2),
    ("middle_gram_numerator",B-4*e*(2*c*e+1),2),
]
data={}
for label,p,n in checks:
    b=bernstein(p,n)
    for v in b: positive_coefficients(v)
    data[label]=[str(v) for v in b]
    print(label,"PASS; Bernstein degree",n,"positive polynomials",len(b))

# Since the Bernstein basis is nonnegative and sums to one on [0,1],
# these exact identities certify strict derivative, endpoint signs and SPD
# margins for every positive real mass. The rational objective denominator
# (2ce-4e^2-1)*B=2*D*B is strictly positive.
assert S.expand((2*c*e-4*e**2-1)*B-2*D*B)==0
print("objective_denominator_identity PASS")
print("UNIVERSAL_SYMBOLIC_CERTIFICATE_GROUPS 10 PASS")
print("NEW_FINITE_SCIENTIFIC_CASES 0; prior case count unchanged")
Path(__file__).with_name("range2_closure_bernstein.json").write_text(json.dumps(data,indent=2)+"\n")
