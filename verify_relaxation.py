import sympy as s
import sys
print(sys.version, s.__version__)
checks=0
def ck(x):
    global checks
    assert x
    checks+=1
z=s.Symbol('z')
for r in range(1,13):
    for t in map(s.Rational,['101/100','5/4','2','5']):
        N=r+1; m=t+1/t-2
        u=s.Matrix([t**j for j in range(N+1)]); v=s.Matrix([t**(-j) for j in range(N+1)])
        H=(u*v.T+v*u.T)/2
        # v has norm t^-N times norm u, so the negative eigenvector is rational.
        a=u-t**N*v
        lam=(N+1-sum(t**(2*j-N) for j in range(N+1)))/2
        ck(H*a==lam*a); ck(lam<0)
        scale=-1/(a.T*H*a)[0]
        p=sum(a[j]*z**j for j in range(N+1))
        q=s.expand(scale*p*p.subs(z,1/z))
        ck(q.subs(z,t)==-1); ck(q.subs(z,1/t)==-1)
        D=t+1/t-z-1/z
        g=s.cancel((q+1)/D)
        ck(s.Poly(s.cancel(z**r*g),z).degree()<=2*r)
        ck(s.expand(D*g-q-1).simplify()==0)
        ck(q.coeff(z,0)==-1/lam)
        # Exact PSD lower-bound certificate H-lambda I via rank-two eigenbasis.
        b=u+t**N*v
        ck((a.T*b)[0]==0)
        ck(H*b==((N+1)-lam)*b)
        if r==1: ck(-1/lam==2/(m*(m+4)))
        print('PASS',r,t,m)
print('PASS exact relaxation certificates:',checks)