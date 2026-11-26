# Joint range–temperature resource law — 26 November 2026

Status: internal working research, not an originality certification or authorization to release.

## Class and theorem
Let m>0, integer r>=1, K>=2, D(k)=m+2-2 cos k. Retain all original admissibility conditions: finite arbitrary channel type, strictly positive actual T, real FIR amplitudes of degree <=r, sum w=1 and sum T w=D on the whole circle. The palette predicate is that there exists a map tau:Fin K -> R covering every actual channel temperature. Repetitions and unused slots are permitted; positivity is imposed on actual channels, not on unused entries. This represents at most K distinct temperatures and places no limit on same-temperature multiplicities. Define E_{r,K}(m) as the infimum of the corresponding physical costs. The two-temperature nearest-neighbor family makes this set nonempty for every r>=1,K>=2.

For fixed m there exist A(m),B(m)>0, independent of r,K, such that

    A(m)/min(r,K)^2 <= E_{r,K}(m) <= B(m)/min(r,K-1)^2.

In particular E_{r,K}(m)=Theta_m(min(r,K)^(-2))=Theta_m(r^(-2)+K^(-2)), uniformly in r>=1,K>=2 at fixed m. No simultaneous mass-uniform claim, finite-(r,K) exact optimum, or attainment of the unrestricted optimum is implied. One explicit temperature-only bound is

    cost >= 1/[64*pi*(m+4)^2*K^2].

## Direct lower bound without a temperature-range restriction
Put M=m+4, delta=1/(4K), C=delta^2/(2M^2). For t,d>0,d<=M and |t-d|>=delta, (t-d)^2/(td)>=C. If t<=2M, this follows from td<=2M^2. Otherwise t>=2d, and 2(t-d)^2-td=(t-2d)(2t-d)>=0, so the ratio is at least 1/2>=C. The argument explicitly covers arbitrarily small and arbitrarily large positive actual temperatures.

For each palette slot set H_i(x)=max(0,2-|x-tau_i|/delta), G(x)=1-sum H_i(x). If some |d-tau_i|<=delta then H_i(d)>=1, so G(d)<=0. Otherwise all actual temperatures have |T-d|>=delta. Using sigma=sum w(T-D)^2/(TD)>=0 and sum w=1 gives sigma>=C in this latter case. In either case sigma(k)>=C G(D(k)). Each tent is bounded by twice the indicator of an interval of length 4 delta. Hence integral_m^{m+4} H_i<=8 delta, and integral_m^{m+4} G>=4-8K delta=2. On [0,pi] use 0<=sin k<=1 and sigma>=0 to deduce sigma>=C G(D) sin k even if G(D)<0. Since D'=2sin k, integration gives integral_0^pi sigma >= (C/2) integral_m^{m+4} G>=C. The other half of the full circle contributes nonnegative cost. Divide by 2pi to get the stated coefficient.

## Physical upper bound; no hidden rate relaxation
Set n=min(r,K-1)>=1. For every feasible degree-n family, the established finite-family compression produces a degree-n family of at most n+1 channels, with no larger cost. The actual temperature list therefore contains at most n+1<=K values. Zero-padding each real FIR coefficient list to degree budget r preserves its polynomial, all-frequency equalities, positivity of T and its cost. Infimizing this map of families gives E_{r,K}<=E_n, without needing an attained infimum. The already proved fixed-m E_n=Theta(n^-2) supplies a constant B(m) for all sufficiently large n; enlarging it using the nearest-neighbor cost covers the finite number of smaller n. For the lower bound combine the established support cost >=1/[(m+2)(m+4)r^2] with the temperature-only lower above, taking A=min(1/[(m+2)(m+4)],1/[64*pi*(m+4)^2]). Since min(r,K-1)>=min(r,K)/2, the stated joint-order equivalence follows.

## Independent secant and scalar-quantization derivation
This alternate analytic argument provides a stronger constant, not the constant claimed by the new Lean theorem. Sort distinct actual temperature values; the normalization at the two band endpoints gives min T<=m, max T>=m+4. For consecutive values a<=d<=h, all actual temperatures t obey (t-a)(t-h)>=0, even exterior ones. The identity

    1/t - (a+h-t)/(a*h) = (t-a)(t-h)/(a*h*t)

and the two constraints yield sigma>= (d/a-1)(1-d/h). The reciprocal secant is exact for adjacent two-level mixing with arbitrary weights; no FIR feasibility is asserted for this piecewise rule. Clip the enclosing ordered grid to the dispersion band [m,M], retaining endpoints and its strictly interior actual values. Clipping raises a and lowers h in each relevant gap, which can only lower the two nonnegative factors. For clipped adjacent endpoints a',h' the lower is >=(d-a')(h'-d)/M^2. There are J<=K-1 positive gaps of lengths ell_j with sum 4. Integration over d yields sum ell_j^3/(6M^2)>=64/[6 M^2(K-1)^2]. The normalized full-circle dispersion density is 1/[pi sqrt((d-m)(M-d))]>=1/(2pi) almost everywhere on the band. Consequently the analytic lower is 16/[3*pi*M^2*(K-1)^2]. This is a useful independent check and quantization interpretation, not an optimized or separately Lean-verified coefficient. Classical dual quantization with conditional mean preservation already has this squared-error order; the contribution here is the physical joint range/palette restriction and attainable comparison using the actual FIR compression.

## Consequences and boundaries
At fixed positive mass, a fixed finite palette cannot produce vanishing dissipation by increasing r. To maintain order O(r^-2) as r grows, K must grow at least linearly in r (and linear growth suffices for that order). These are analytic corollaries of the joint bounds. They do not contradict the fixed-r critical theorem: its three-channel construction attains the leading coefficient as m decreases to zero, not an r-uniform mass-independent prefactor. No joint m,r,K limit is exchanged. The lower argument is independent of degree and applies to the same two normalizations with nonpolynomial rates, but the upper argument and the full joint theorem are for the precise normalized FIR class (or the already proved equivalent individual degree-bounded nonnegative trigonometric rate class). No identification of general momentum-dependent microscopic DOS with this class is asserted.
