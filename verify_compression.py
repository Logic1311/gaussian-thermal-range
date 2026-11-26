from fractions import Fraction as F
from itertools import combinations
import random, sys, hashlib
def tr(A): return list(map(list,zip(*A)))
def mm(A,B): return [[sum(x*y for x,y in zip(a,b)) for b in tr(B)] for a in A]
def sub(A,B): return [[x-y for x,y in zip(a,b)] for a,b in zip(A,B)]
def diag(t): return [[x if i==j else F(0) for j in range(len(t))] for i,x in enumerate(t)]
def inv(A):
 n=len(A); B=[list(map(F,row))+[F(i==j) for j in range(n)] for i,row in enumerate(A)]
 for i in range(n):
  k=next(k for k in range(i,n) if B[k][i]); B[i],B[k]=B[k],B[i]
  x=B[i][i]; B[i]=[v/x for v in B[i]]
  for j in range(n):
   if j!=i:
    x=B[j][i]; B[j]=[a-x*b for a,b in zip(B[j],B[i])]
 return [a[n:] for a in B]
def det(A):
 A=[list(map(F,a)) for a in A]; d=F(1)
 for i in range(len(A)):
  k=next((k for k in range(i,len(A)) if A[k][i]),None)
  if k is None:return F(0)
  if k!=i:A[k],A[i]=A[i],A[k];d=-d
  x=A[i][i];d*=x
  for j in range(i+1,len(A)):
   y=A[j][i]/x
   A[j]=[a-y*b for a,b in zip(A[j],A[i])]
 return d
rng=random.Random(20261126); checks=0
# Arbitrary nonorthogonal full column rank bases: B=U S.
# Compression inverse Gram is H K^-1 H where H=B^t B,K=B^t T B.
for d in range(1,6):
 for extra in range(0,4):
  q=d+extra
  for trial in range(10):
   B=[[F(i==j) for j in range(d)] if i<d else [F(rng.randint(-5,5),rng.randint(1,5)) for j in range(d)] for i in range(q)]
   t=[F(rng.randint(1,20),rng.randint(1,10)) for i in range(q)]
   H=mm(tr(B),B); K=mm(mm(tr(B),diag(t)),B)
   C=mm(mm(tr(B),diag([1/x for x in t])),B)
   D=sub(C,mm(mm(H,inv(K)),H))
   assert D==tr(D)
   for k in range(1,d+1):
    for inds in combinations(range(d),k):
     assert det([[D[i][j] for j in inds] for i in inds])>=0,(d,q,trial,inds,D)
     checks+=1
   if extra==0: assert all(x==0 for a in D for x in a)
print('exact compression PSD principal minors:',checks)
print('Python',sys.version)
print('SHA256',hashlib.sha256(open(__file__,'rb').read()).hexdigest())
