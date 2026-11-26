from fractions import Fraction
import numpy as np
# Rigorous sufficient positivity certificate using pi < 22/7 and cos x >= 1-x^2/2.
def certified(r,m):
    x2=Fraction(22,7)**2/(r+2)**2
    return 1-x2/2 > Fraction(2,1)/(2+m)
def strong(r,m):
    return Fraction((r+2)**2)*m >= Fraction(22,7)**2*(m+4)
count=0; skipped=0
for r in [1,2,3,4,8,16,32,64,128]:
    n=r+1; j=np.arange(n)
    g=np.sin(np.pi*(j+1)/(n+1)); g/=np.linalg.norm(g)
    rho=g[:-1]@g[1:]
    for N in [2*r+5,2*r+7]:
        theta=2*np.pi*np.arange(N)/N
        a=np.concatenate([g*np.cos(theta[:,None]*j)/np.sqrt(N),g*np.sin(theta[:,None]*j)/np.sqrt(N)])
        for m0 in ['0.01','0.1','0.5','1','2','10','100']:
            mf=Fraction(m0); m=float(mf); c=m+2
            if not certified(r,mf):
                skipped+=1; continue
            T=np.tile(c-2*np.cos(theta)/rho,2)
            assert min(T)>0
            for d in range(n):
                b=np.sum(a[:,:n-d]*a[:,d:],axis=1)
                assert abs(b.sum()-(d==0))<1e-10
                assert abs(T@b-({0:c,1:-1}.get(d,0)))<1e-9
                count+=2
            k=np.linspace(-np.pi,np.pi,2048,endpoint=False)+.00013
            D=c-2*np.cos(k); w=abs(a@np.exp(1j*j[:,None]*k))**2
            sig=D*(1/T@w)-1
            h=np.zeros((len(T),n+2))
            h[:,1:-1]=(T[:,None]-c)*a
            h[:,:n]+=a; h[:,2:]+=a
            H=np.sum(np.sum(h*h,axis=1)/T)
            var=2/rho**2-2
            assert np.max(abs(w.sum(axis=0)-1))<1e-10
            assert np.max(abs(T@w-D))<1e-9
            assert np.max(abs(sig-np.sum(w*(T[:,None]-D)**2/(T[:,None]*D),axis=0)))<1e-9
            assert abs(np.mean(D*sig)-H)<1e-9
            assert abs(np.mean(T**2@w-D**2)-var)<1e-9
            assert sig.mean()>=1/(c*(c+2)*r*r)-1e-10
            assert H>=1/(c*r*r)-1e-10
            assert sig.mean()<=var/(m*min(T))+1e-10
            count+=9
            if strong(r,mf):
                assert min(T)>=m/2-1e-12
                assert sig.mean()<=np.pi**2*(m+4)**2/(4*m*m*(r+2)**2)+1e-10
                count+=2
            print(r,N,m0,sig.mean(),H)
assert not certified(1,Fraction(2))
print('PASS',count,'SKIPPED WITHOUT POSITIVITY CERTIFICATE',skipped)
