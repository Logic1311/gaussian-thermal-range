# Temperature-level obstruction and three-level witnesses (working, 2026-11-26)

This extension is in the same normalized, degree-bounded FIR physical class, with strictly positive temperatures and all-frequency equalities. A level means a **distinct scalar temperature**, not the number of amplitudes at that level. In particular, arbitrarily many independent channels at either of two temperatures cannot evade the theorem.

## Exact two-temperature minimum

Let the two possible temperatures be a,h, with 0<a<=h. At every frequency the normalized nonnegative weights have temperature mean D=m+2-2 cos k. At k=0 and k=pi this gives a<=m and h>=m+4; hence a<h (one level is impossible). This reasoning permits a,h to depend on m and r, and permits a<m or h>m+4. No prior assumption that temperatures lie in [m,m+4] is made.

For every channel, T is either a or h, so ah/T=a+h-T. Multiply by the weight and sum, obtaining ah g=a+h-D for g=sum w/T. Thus

    sigma = (D/a-1)(1-D/h).

Both factors are nonnegative on the dispersion band. The first is nonincreasing in a and the second nondecreasing in h. Since a<=m, h>=m+4, every such family is pointwise dominated (in the cost-minimization sense) by the nearest-neighbor family at m,m+4. Its amplitudes (1+z)/2 and (1-z)/2 are available for every degree budget r>=1. Its mean cost is exactly 2/[m(m+4)]. Therefore the restricted minimum (not just an infimum) over all finite families with at most two temperature values is

    E_{r,<=2 temperatures}(m) = 2/[m(m+4)]    (r>=1, m>0).

The proof of the lower bound does not use polynomial support; the witness does. This is a direct model-specific consequence of elementary two-point interpolation and the known nearest-neighbor realization; it is not a new Jensen inequality or an independent high-impact claim. It even holds for nonpolynomial rates in the same two-normalization model, but the rest of the paper does not extend to arbitrary microscopic rates.

## Three distinct levels at any positive mass

Write s=(1-cos k)/2, so D=m+4s. Use temperatures (m,m+2,m+4) and rates ((1-s)^2, 2s(1-s), s^2). They are nonnegative, even, of degree <=2, sum to one, and reproduce D exactly. Each has a single real FIR factor; explicit factors are (1+z)^2/4, (1-z^2)/(2 sqrt 2), (1-z)^2/4. The middle amplitude is normalized because |1-z^2|^2/8 = (1-cos^2 k)/2. All three channels are nonzero. This is the degree-two classical Bernstein operator applied to f(T)=1/T on [m,m+4], not an original basis.

For the nearest two-level family the inverse-temperature mixture is g2=(1-s)/m+s/(m+4). For the three-level family g3=(1-s)^2/m+2s(1-s)/(m+2)+s^2/(m+4). Subtraction gives

    g2-g3 = 8s(1-s)/[m(m+2)(m+4)].

Hence the mean improvement is D-weighted: <D s(1-s)>=(m+2)/8, because <sin^2 k>=1/2 and <cos k sin^2 k>=0. The cost of the witness is exactly 1/[m(m+4)]. For all r>=2,m>0,

    E_r(m) <= 1/[m(m+4)] = (1/2) E_{r,<=2 temperatures}(m).

It is an attained cost of a specific family, NOT a claim that the unrestricted or three-level infimum equals that value. The pointwise difference vanishes at k=0,pi, and is positive elsewhere. The physical advantage of a third temperature level is strict at every positive mass. The classical Bernstein monotonicity already implies that the chosen degree-two interpolation improves degree-one interpolation for convex reciprocal temperature; our exact half-cost is an elementary Fourier-weighted specialization.

## Minimum number of temperature levels for sharp critical coefficient

By the established critical squeeze C_r/m-1<=E_r(m)<=C_r/m+4(r+1)^2 with C_r=12/[(r+1)(r+2)(r+3)], a three-channel family reaches the sharp leading coefficient at fixed r. Its actual positive temperature levels m,m+A,m+B are distinct by 0<A<B. A two-level family, even with arbitrary multiplicities and m-dependent choices of a,h, satisfies m cost>=2/(m+4), whose limit is 1/2. For r>=2, C_r<=1/5<1/2. Therefore at least three distinct temperature levels are necessary and three suffice for asymptotically attaining the sharp critical coefficient. At r=1 two levels suffice (and one is infeasible). This result also identifies the exact leading cost over the at-most-three-channel class by squeezing between the all-family lower and the explicit three-channel upper, without assuming an attained optimum.

A quantitative separation for the critical construction itself: if r>=2 and 0<m<=1/[40(r+1)^2], then its scaled cost is <=C_r+4m(r+1)^2<=3/10, while every two-level family's scaled cost is >=2/(m+4)>3/10, since the threshold implies m<=1. This avoids all interchange of the mass limit and the infimum. For all larger m the separate degree-two witness above gives strict advantage, but that is not the critical-optimal construction.

## Formal scope and prior-art posture

The formalization uses `BathFamily.twoTemperature` with two arbitrary ordered positive values (possibly equal), actual `BathFamily.admissible`, `BathFamily.cost`, and `IsLeast (twoTemperatureCosts r m)`. The three-channel witness uses the already kernel-verified real spectral factor theorem, not arbitrary nonpolynomial rates. The sharp critical limit remains an analytic corollary of its verified inequalities. See TemperatureCount.lean and ThreeTemperature.lean with their actual success/failed logs; use only successful versions in the active build. No human specialist review, priority certification, or publication permission is implied.
