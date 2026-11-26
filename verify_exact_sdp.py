"""Independent exact certificates for the closed moment SDP.
No floating-point optimization is run here. Frozen rational trial parameters
for range 2 were found by a numerical search; all subsequent tests are exact.
Finite cases do not replace the general proof or its Lean counterpart.
"""
from sympy import Matrix, eye, zeros, diag, Rational as R, simplify, trace, N
from itertools import combinations
import json
from pathlib import Path

counts = {"reference": 0, "singular_boundary_mixing": 0, "range1_dual": 0,
          "range2_primal_dual": 0, "exact_generalized_eigen_recovery": 0}

def mat_eq(A,B):
    assert A.shape == B.shape
    assert all(simplify(x-y)==0 for x,y in zip(A,B))

def is_pd(A):
    assert A==A.T
    return all(A[:k,:k].det()>0 for k in range(1,A.rows+1))

def is_psd_small(A):
    assert A==A.T
    return all(A.extract(I,I).det()>=0 for k in range(1,A.rows+1)
               for I in combinations(range(A.rows),k))

def is_psd(A):
    # Exact Schur-pivot elimination, valid for singular PSD matrices too.
    assert A==A.T
    if A.rows==0:return True
    if any(A[i,i]<0 for i in range(A.rows)):return False
    candidates=[i for i in range(A.rows) if A[i,i]>0]
    if not candidates:return A==zeros(A.rows)
    i=candidates[0];I=[j for j in range(A.rows) if j!=i]
    b=A.extract(I,[i]);C=A.extract(I,I)
    return is_psd(C-b*b.T/A[i,i])

def lags(A):
    return tuple(sum(A[i,i+k] for i in range(A.rows-k)) for k in range(A.rows))

def Qmat(n,m):
    return Matrix(n,n,lambda i,j:m+2 if i==j else (-1 if abs(i-j)==1 else 0))

def block(H,G,J):
    return H.row_join(G).col_join(G.row_join(J))

def schur_certificate(H,G,J):
    assert is_pd(H)
    W=G*H.inv()*G
    D=J-W
    # Check block quadratic-form factorization by exact congruence.
    n=H.rows
    L=eye(n).row_join(zeros(n)).col_join((G*H.inv()).row_join(eye(n)))
    mat_eq(block(H,G,J),L*diag(H,D)*L.T)
    return W,D

def reference(r,m):
    n=r+1
    G,H,J=zeros(n),zeros(n),zeros(n)
    for i in range(r):
        for sign,T in [(1,m),(-1,m+4)]:
            a=zeros(n,1); a[i]=R(1,2); a[i+1]=R(sign,2)
            A=a*a.T/r
            G+=A; H+=T*A; J+=A/T
    assert lags(G)==(1,)+(0,)*r
    assert lags(H)==(m+2,-1)+(0,)*(r-1)
    assert is_pd(G) and is_pd(H)
    W,D=schur_certificate(H,G,J)
    # Independent exact Gram (the original positive-temperature witness).
    assert is_psd(D)
    assert trace(Qmat(n,m)*J)-1==2/(m*(m+4))
    return G,H,J

def toeplitz_project(A):
    n=A.rows
    v=[sum(A[i,i+k] for i in range(n-k))/(n-k) for k in range(n)]
    return Matrix(n,n,lambda i,j:v[abs(i-j)])

def is_toeplitz_sym(A):
    return A==A.T and A==toeplitz_project(A)

def dual_check(G,H,J,Q,C,Vpos):
    # C: top-right dual block. U=-(C+C^T), V=-Vpos.
    # The constraints make U,V Toeplitz, hence dual values depend on lags only.
    U=-(C+C.T); V=-Vpos
    assert is_toeplitz_sym(U) and is_toeplitz_sym(V)
    D=Vpos-C*Q.inv()*C.T
    assert is_psd_small(D)
    n=G.rows
    L=eye(n).row_join(C*Q.inv()).col_join(zeros(n).row_join(eye(n)))
    Z=Vpos.row_join(C).col_join(C.T.row_join(Q))
    mat_eq(Z,L*diag(D,Q)*L.T)
    lo=trace(U*G)+trace(V*H)-1
    hi=trace(Q*J)-1
    assert hi-lo==trace(Z*block(H,G,J))>=0
    return lo,hi

for r in range(1,9):
    for m in [R(1,100),R(1,3),R(1),R(10)]:
        G0,H0,J0=reference(r,m);counts['reference']+=1
        n=r+1;Q=Qmat(n,m)
        # Rank-one G is constant on the circle; H0 is SPD and has the correct
        # weighted spectrum. Such a triple cannot be an exact physical Gram:
        # diagonal G[1,1]=0 would force H[1,1]=0, but H0[1,1]>0.
        G=zeros(n);G[0,0]=1;H=H0;J=G*H.inv()*G
        assert G[1,1]==0 and H[1,1]>0
        assert lags(G)==(1,)+(0,)*r
        W,D=schur_certificate(H,G,J);assert D==zeros(n)
        for t in [R(1,2),R(1,100),R(1,10**5)]:
            g=(1-t)*G+t*G0;h=(1-t)*H+t*H0;j=(1-t)*J+t*J0
            assert is_pd(g) and is_pd(h)
            assert lags(g)==lags(G0) and lags(h)==lags(H0)
            w,d=schur_certificate(h,g,j)
            # In this test H is fixed, and the Schur residual is an exact sum
            # of two manifestly PSD terms, including convexity variance.
            mat_eq(d,t*(J0-G0*H.inv()*G0)+t*(1-t)*(G-G0)*H.inv()*(G-G0))
            assert is_psd(d)
            assert trace(Q*w)-1<=trace(Q*j)-1
            assert trace(Q*j)-1==(1-t)*(trace(Q*J)-1)+t*(trace(Q*J0)-1)
            counts['singular_boundary_mixing']+=1

# Exact r=1 dual equality for all tested rational masses.
for m in [R(1,1000),R(1,100),R(1,2),R(1),R(2),R(10),R(100)]:
    c=m+2;G=eye(2)/2;H=Matrix([[c/2,-1],[-1,c/2]]);Q=Qmat(2,m)
    J=G*H.inv()*G;K=H.inv()*G;C=-K*Q;Vpos=K*Q*K.T
    lo,hi=dual_check(G,H,J,Q,C,Vpos)
    assert lo==hi==2/(m*(m+4))
    counts['range1_dual']+=1

# Nontrivial rational dual certificates: these prove rigorous finite-range
# intervals, irrespective of whether the trial parameters are optimal.
results=[]
for m,e in [(R(1,100),R(1982689,3941624)),(R(1),R(2450873,2986436)),(R(10),R(28710037,8200090))]:
    c=m+2;a=2*e*(2*c*e+1)/(4*c*c*e-c+8*e)
    G=diag(a,1-2*a,a)
    H=Matrix([[e,-R(1,2),0],[-R(1,2),c-2*e,-R(1,2)],[0,-R(1,2),e]])
    Q=Qmat(3,m);assert is_pd(G) and is_pd(H) and is_pd(Q)
    assert lags(G)==(1,0,0) and lags(H)==(c,-1,0)
    J=G*H.inv()*G;_,d=schur_certificate(H,G,J);assert d==zeros(3)
    # Take a rational Toeplitz projection of the approximate stationarity
    # matrix, then add an exact diagonal-dominance margin to the dual block.
    C0=-H.inv()*G*Q;S=(C0+C0.T)/2;C=C0-S+toeplitz_project(S)
    W=C*Q.inv()*C.T;P=toeplitz_project(W);E=P-W
    eps=max(sum(abs(E[i,j]) for j in range(3)) for i in range(3))+R(1,10**12)
    Vpos=P+eps*eye(3)
    lo,hi=dual_check(G,H,J,Q,C,Vpos)
    assert 0<lo<=hi
    assert hi-lo<R(1,10**6)
    if m==1: assert hi-lo<R(3,10**10)
    counts['range2_primal_dual']+=1
    # All decimal strings below are outward rounded using exact integer arithmetic.
    scale=10**12
    ln=int((lo*scale).floor());un=int((hi*scale).ceiling())
    def dec(k): return f'{k//scale}.{k%scale:012d}'
    results.append({'m':str(m),'e':str(e),'a':str(a),'lower_rational':str(lo),
                    'upper_rational':str(hi),'width_rational':str(hi-lo),
                    'lower_decimal_outward':dec(ln),'upper_decimal_outward':dec(un)})
    print('RANGE2_CERTIFICATE m=',m,'interval=[',dec(ln),',',dec(un),']')

# Independent generalized-eigenvector reconstruction on rational moment pairs.
# Work in the H metric, not the square-root basis used in the Lean proof.
for m in [R(1,2),R(1),R(4)]:
    for r in (1,2):
        G,H,J=reference(r,m);n=r+1
        E=H.inv()*G
        Arows=[];temps=[]
        for lam,mult,vecs in E.eigenvects():
            assert lam.is_positive
            assert len(vecs)==mult
            # Distinct eigenvalues are H-orthogonal; Gram-Schmidt within a
            # repeated eigenvalue is also exact.
            basis=[]
            for v in vecs:
                u=v
                for w in basis:
                    u=u-w*(w.T*H*u)[0]
                from sympy import sqrt
                u=u/sqrt(simplify((u.T*H*u)[0]));basis.append(u)
                Arows.append(sqrt(lam)*u.T*H);temps.append(1/lam)
        A=Matrix.vstack(*Arows);T=diag(*temps)
        assert A.rows==n
        mat_eq(A.T*A,G);mat_eq(A.T*T*A,H);mat_eq(A.T*T.inv()*A,G*H.inv()*G)
        counts['exact_generalized_eigen_recovery']+=1

print('EXACT_CASE_COUNTS',json.dumps(counts,sort_keys=True))
print('EXACT_STRUCTURED_SCIENTIFIC_UNITS',sum(counts.values()))
print('No previous scientific checks counted again. No floating tolerance.')
Path(__file__).with_name('range2_exact_certificates.json').write_text(json.dumps(results,indent=2)+'\n')
