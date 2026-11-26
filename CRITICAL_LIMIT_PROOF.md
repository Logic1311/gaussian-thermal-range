# Critical-mass extension (working, 2026-11-26)

This is an additional research derivation. The quantitative two-sided bound, three-channel realization and squeeze are now kernel-verified by CriticalEnergy, CriticalRealization and CriticalScaling. The displayed limits are analytic consequences, not separately formalized limit statements. This is not a public release. The verified 488-file predecessor is unchanged. Here r >= 1 is fixed, n = r+1, m>0, D0(k)=2-2 cos k, and D=m+D0. Let C_r=12/[(r+1)(r+2)(r+3)]. We prove the following analytic candidate:

    C_r/m - 1 <= E_r(m) <= C_r/m + 4(r+1)^2.

In particular lim_{m downarrow 0} m E_r(m)=C_r. Since the scalar majorant in Gopalakrishnan (2026), Eq. (15), has the same leading coefficient, E_r/L_r -> 1 for fixed r. This is consistent with strict E_r>L_r at every positive m for r>=2. The fixed-m, large-r exponential separation is a different limit. The construction uses at most three actual strictly positive-temperature real FIR channels; no extra support or temperature constraint is assumed. Neither finite-m equality nor physical attainment of the optimum is asserted.

## Universal lower bound
For real P(z)=sum_{j=0}^r a_j z^j, put F(z)=(1-z)P(z)=sum_{j=0}^{r+1} f_j z^j. F(1)=0 and F'(1)=-P(1). Hence sum f_j=0 and sum (j-(r+1)/2) f_j=-P(1). Finite Cauchy-Schwarz and Parseval give

    |P(1)|^2 <= [sum_{j=0}^{r+1}(j-(r+1)/2)^2] < D0 |P|^2 >
               = (1/C_r) < D0 |P|^2 >.

For every physical family the exact constraints at k=0 imply sum w_v(0)=1, sum T_v w_v(0)=m. Weighted Cauchy-Schwarz, equivalently nonnegative entropy at k=0, gives sum w_v(0)/T_v >= 1/m. Then

    1+<sigma> = sum_v <(m+D0) |P_v|^2>/T_v
              >= C_r sum_v w_v(0)/T_v >= C_r/m.

The bound passes to the infimum. The finite-dimensional extremal calculation is a classical Dirichlet energy / reproducing-kernel calculation, not claimed as an original inequality.

## Three-channel upper construction
Let S=n(n+1)(n+2)/6 and a_j=(j+1)(n-j)/S, j=0,...,r. These are strictly positive and sum to 1. Let P0(z)=sum a_j z^j, w0=|P0|^2, R=1-w0. On the circle,

    R = sum_{i,j} a_i a_j (1-Re(z^i conj(z^j)))
      = (1/2) sum_{i,j} a_i a_j |z^i-z^j|^2.

All terms are nonnegative. The single ordered pair (0,1) proves R >= (a0*a1/2) D0. The identity |1-z^d| <= d |1-z| for d>=0 follows from the finite geometric sum or induction; |i-j|<=r gives R <= (r+1)^2 D0. Both inequalities hold at z=1 as well (R=D0=0); no division by a vanishing frequency factor occurs. Set A=1/(r+1)^2 and B=A+1+2/(a0*a1), so 0<A<B and A R<=D0<=B R.

    w1=(B R-D0)/(B-A),   w2=(D0-A R)/(B-A).

These are even real nonnegative trigonometric polynomials of degree <=r, satisfy w1+w2=R and A w1+B w2=D0. The previously verified real Fejer-Riesz theorem gives real degree<=r FIR amplitudes for both. The temperatures m, m+A, m+B are strictly positive, and both original all-frequency normalizations hold exactly. The degree restriction is on actual rates; no arbitrary microscopic density-of-states equivalence is asserted.

For this cold polynomial the coefficients of (1-z)P0 are f_j=(n-2j)/S for j=0,...,n, including both boundary coefficients. Direct sums give <D0 w0>=sum f_j^2=2/S=C_r. The cold mean weight is <=1; w1,w2 sum to R<=1. For all frequencies the hot inverse temperature contribution is bounded above by 1/(m+A), since both hot temperatures >=m+A. Thus

    1+<sigma> <= C_r/m + <w0> + (m+4)/(m+A)
              <= C_r/m + 1 + 4/A

using A<=4. The stated upper bound follows. Taking infima and multiplying by m gives the explicit squeeze C_r-m <= m E_r <= C_r+4m(r+1)^2. This is not a claim of a joint uniform limit in m,r: the error depends on r.

## Scientific positioning
The known scalar coefficient and nearest-neighbor realization are not new (primary v1, Eq. (15)-(18), Fig. 2). The new candidate is constructive leading-order *physical* saturation for every fixed degree, in the same unrestricted finite-family optimization where exact finite-m saturation has been excluded at r>=2. This clarifies the order of limits and the physical meaning of the original critical-cost coefficient. Classical positive polynomial approximation and the endpoint Christoffel inequality provide related methods, not priority evidence. Human independent specialist review and all publication permissions remain pending.
