"""Exact nonorthogonal Schur-complement certificates, not frequency sampling."""
import sympy as s
from itertools import product
import sys
print(sys.version, 'SymPy', s.__version__)
checks=0
def ck(v):
    global checks
    assert v
    checks+=1

def ldl_positive(M):
    L,D=M.LDLdecomposition(hermitian=False)
    return L*D*L.T==M and all(x>0 for x in D.diagonal())

def laurent(M):
    n=M.rows
    return [sum(M[j,j+k] for j in range(n-k)) for k in range(n)]

# Independent nonorthogonal decomposition of rank-d physical matrices.
for d,m,offset in product(range(3,7), [s.Rational(1,10000),s.Rational(2,3)], [0,2]):
    n=d+offset; v=[s.Rational(j,10*d) for j in range(1,d-1)]
    h=sum(x*x for x in v); w=[2*x/(1+h) for x in v]+[(1-h)/(1+h)]
    ck(sum(x*x for x in w)==1); rows=[]; temps=[]
    for j in range(d-1):
        for sign,temp in [(1,m),(-1,m+4)]:
            row=s.zeros(1,n); row[j]=w[j]/2; row[j+1]=sign*w[j]/2
            # Split the rate into unequal-temperature channels with unchanged mean.
            rows.extend([s.Rational(3,5)*row,s.Rational(4,5)*row]); temps.extend([temp/2,41*temp/32])
    rows.append(s.zeros(1,n)); temps.append(s.Integer(7))
    A=s.Matrix.vstack(*rows); T=s.diag(*temps); B=A[:,:d]
    R=s.eye(d).row_join(s.zeros(d,offset)); ck(A==B*R); ck(A.rank()==d)
    H=B.T*B; K=B.T*T*B; ck(ldl_positive(H)); ck(ldl_positive(K))
    ck(laurent(A.T*A)==[1]+[0]*(n-1)); ck(laurent(A.T*T*A)==[m+2,-1]+[0]*(n-2))
    Q=s.Matrix.hstack(*B.T.nullspace()); ck(B.T*Q==s.zeros(d,Q.cols)); ck(ldl_positive(Q.T*Q))
    E=Q.T*T*Q; F=B.T*T*Q; Ki=K.inv(); S=E-F.T*Ki*F
    ck(ldl_positive(S)); W=H*Ki*F
    diff=A.T*T.inv()*A-R.T*H*Ki*H*R
    ck(diff==R.T*W*S.inv()*W.T*R)
    # Strict improvement on the entire column space, including complex x.
    ck(ldl_positive(diff[:d,:d])); ck(all(t>0 for t in temps)); ck(A[-1,:]==s.zeros(1,n))
    print('PASS physical Schur',d,n,A.rows,m)

# Path-cycle comparison via a block Schur complement, with exact LDL certificate.
for n,m in product(range(2,9),[s.Rational(1,10000),s.Rational(1,100),s.Integer(1),s.Integer(10)]):
    N=2*n+3; L=n*n+2*n+2; rho=1-s.Rational(5,L); c=m+2
    C=s.eye(N)*c
    for j in range(N): C[j,(j+1)%N]=C[(j+1)%N,j]=-1/rho
    M=C[:n,:n]; char=M.charpoly().as_poly()
    # Sturm counts roots on the strictly negative half-line. SPD iff no nonpositive root.
    neg=char.count_roots(-s.oo,0); path_spd=(neg==0 and M.det()!=0)
    ck(path_spd==(all(x>0 for x in M.LDLdecomposition(hermitian=False)[1].diagonal())))
    if c<=2/rho:
        print('EXCLUDED cyclic',n,m,'path_spd',path_spd); continue
    ck(path_spd); F=C[:n,n:]; E=C[n:,n:]; Mi=M.inv(); S=E-F.T*Mi*F; ck(ldl_positive(S))
    Z=Mi*F; diff=C.inv()[:n,:n]-Mi
    ck(diff==Z*S.inv()*Z.T)
    # With real g, the weighted Laurent polynomial is a sum of exact rational squares
    # in real and imaginary Fourier coordinates. Certificate holds for all |z|=1.
    u=s.Matrix([(j+1)*(n-j) for j in range(n)]); G=s.diag(*u); norm=(u.T*u)[0]
    H=G*diff*G/norm; Ls,Ds=S.inv().LDLdecomposition(hermitian=False); W=G*Z*Ls
    ck(H==W*Ds*W.T/norm); ck(all(x>0 for x in Ds.diagonal()))
    print('PASS all-frequency path certificate',n,m)
# Critical cases without floating point; rational LDL (n=40 uses tridiagonal M).
for n,m,expected in [(2,s.Rational(1,10000),True),(3,s.Rational(1,10000),False),(3,s.Rational(1,100),True),(40,s.Rational(10,1677),True)]:
    rho=1-s.Rational(5,n*n+2*n+2); c=m+2; M=s.eye(n)*c
    for j in range(n-1): M[j,j+1]=M[j+1,j]=-1/rho
    ld=M.LDLdecomposition(hermitian=False)[1]; ck(all(x>0 for x in ld.diagonal())==expected)
    if n==40: ck(c==2/rho)
    print('PASS boundary',n,m,expected,'cyclic floor',c-2/rho)
print('PASS independent exact Schur certificates:',checks)