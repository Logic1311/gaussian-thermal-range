"""Exact independent finite-case checks of the palette law; not a proof of universality."""
from fractions import Fraction as F
from math import comb
from itertools import pairwise

count = 0
palette_cases = 0
family_cases = 0

def check(p):
    global count
    assert p
    count += 1


def tent(x,t,e):
    return max(F(0), 2-abs(x-t)/e)


def integral_tent(a,b,t,e):
    pts = sorted({a,b,*(x for x in (t-2*e,t,t+2*e) if a<x<b)})
    return sum((v-u)*(tent(u,t,e)+tent(v,t,e))/2 for u,v in pairwise(pts))


def bracket(grid,d):
    for a,h in pairwise(grid):
        if a<=d<=h:
            return a,h
    raise AssertionError('unbracketed value')


def moment(n,j):
    # <s^j (1-s)^(n-j)> for s=(1-cos k)/2. Beta(1/2,1/2).
    p,q=j,n-j
    return F(comb(2*p,p)*comb(2*q,q),4**n*comb(n,p))


def exact_cost(m,weights,grid,n):
    # weights[l][j] are Bernstein coefficients. Compute mean D*g - 1 directly.
    return sum(w*comb(n,j)/t*(m*moment(n,j)+4*moment(n+1,j+1))
               for t,row in zip(grid,weights) for j,w in enumerate(row))-1

for m in map(F,['1/1000','1/5','1','7','100']):
    M=m+4
    for K in range(2,13):
        for variant in range(3):
            # Actual grid, with arbitrarily exterior levels in two variants.
            if variant==0:
                grid=[m+F(4*j,K-1) for j in range(K)]
            elif variant==1:
                grid=[m/1000]+[m+F(4*j,K-1) for j in range(1,K-1)]+[1000*M]
            else:
                grid=[m/2]+[m+4*F(j,K-1)**2 for j in range(1,K-1)]+[M+1]
            # Include repeated palette slots and unused negative slots in alternate cases.
            palette=grid if variant==0 else grid+[grid[0],-F(1)]
            k=len(palette); e=F(1,4*k)
            check(all(t>0 for t in grid) and grid[0]<=m and grid[-1]>=M)
            tins=[integral_tent(m,M,t,e) for t in palette]
            check(all(0<=v<=8*e for v in tins))
            check(4-sum(tins)>=2)
            clipped=sorted({m,M,*(t for t in grid if m<t<M)})
            gaps=[h-a for a,h in pairwise(clipped)]
            check(len(gaps)<=k-1 and sum(gaps)==4)
            # Exact integration of the adjacent-level secant entropy lower.
            integ=sum((h-a)**3/(6*M*M) for a,h in pairwise(clipped))
            check(integ>=F(64,6)/(M*M*(k-1)**2))
            for a,h in pairwise(grid):
                for t in grid:
                    check(1/t-(a+h-t)/(a*h)==(t-a)*(t-h)/(a*h*t)>=0)
            palette_cases += 1
            # Feasible polynomials with a split into two same-T channels per level.
            for n in (1,2,3,5,9):
                w=[[F(0) for _ in range(n+1)] for _ in grid]
                for j in range(n+1):
                    d=m+F(4*j,n); a,h=bracket(grid,d)
                    w[grid.index(a)][j]=(h-d)/(h-a)
                    w[grid.index(h)][j]=(d-a)/(h-a)
                check(all(v>=0 for row in w for v in row))
                check(all(sum(row[j] for row in w)==1 for j in range(n+1)))
                check(all(sum(t*row[j] for t,row in zip(grid,w))==m+F(4*j,n) for j in range(n+1)))
                cost=exact_cost(m,w,grid,n)
                split_grid=[t for t in grid for _ in (0,1)]
                split_w=[[F(q,3)*v for v in row] for row in w for q in (1,2)]
                check(exact_cost(m,split_w,split_grid,n)==cost)
                # The verified analytic secant bound is stronger than this rational
                # comparison; pi>3 means this also exceeds the Lean bound.
                check(cost>=F(1,192)/(M*M*k*k))
                check(cost>=1/((m+2)*M*n*n))
                if K==2 and variant==0:
                    check(cost==2/(m*M))
                if K==3 and variant==0 and n==2:
                    check(cost==1/(m*M))
                family_cases += 1

print(f'PALETTE_CASES={palette_cases}; FAMILY_CASES={family_cases}')
print(f'EXACT_SCIENTIFIC_UNITS={palette_cases+family_cases}')
print(f'INTERNAL_ASSERTIONS={count} (including regression assertions; not added to scientific counter)')
print('METHOD=Fraction; exact tent integration, adjacent-grid secants, Bernstein-coefficient certificates and beta moments')
print('NO_FLOAT_TOLERANCE; repeated Windows execution is not an added count')
