# Exact range-two physical minimum: analytic extension

**WORKING / UNPUBLISHED — 2026-11-26.** This is an AI-developed mathematical result within the existing normalized FIR bath model. It is not a human originality assessment or a claim of microscopic realizability for arbitrary bath density of states. Its Lean status is recorded separately in the acceptance record. The previous accepted baseline is immutable.

## 1. Main theorem and scope

Let `m>0`, `c=m+2`, and consider all finite families of real degree-at-most-two FIR amplitudes with strictly positive temperatures. The two normalizations and objective are exactly those of the accepted paper. Let

```
N_c(e) = 32 c^3 e^4 + (128-64 c^4)e^3
         + (16 c^5+20 c^3-40 c)e^2 - 8 c^4 e + c^3 + 2 c.
```

There is exactly one root `e_*` in `(c/4,(3c-2)/8)`. The physical infimum is an attained minimum and is

```
E_2(m) = 2 e_* (4 c^3 e_* - 8 c^2 e_*^2 - c^2 - 2)
         / ((2 c e_* - 4 e_*^2 - 1)(4 c^2 e_* - c + 8 e_*)) - 1.
```

It can be realized using exactly three channels, at three distinct, strictly positive temperatures. No optimal realization can have fewer than three distinct temperatures or three channels. This is stronger than the earlier range-two bound and approximate primal/dual certificates. It establishes actual physical attainment for range two, **not** for arbitrary range. Uniqueness here concerns the specified scalar parameter/root, not all optimal physical bath decompositions or the unconstrained SDP triple.

## 2. Independent audit of the general SDP and its boundary

Write `G=A^T A`, `H=A^T T A`, `J=A^T T^{-1} A`. The block in the accepted SDP is PSD because it is the Gram matrix of `[T^{1/2}A, T^{-1/2}A]`. Real amplitudes give cosine lag sums, hence the affine constraints on G and H hold exactly; the Fourier average is `tr(QJ)-1`, `Q=cI-Adj(P_{r+1})`. These facts do not presume a temperature bound, nonzero individual amplitudes, or a fixed number of channels.

For every feasible triple, block positivity gives `H,J >= 0`. Positivity plus a zero quadratic form implies membership in the kernel (e.g. test on `x+t y`). Thus `ker H` and `ker J` are contained in `ker G`. Physical triples additionally have `ker H=ker G=ker J=ker A`: positivity and finiteness of all temperatures ensure the same zero sets of the three weighted sums of squares. The reverse containment is not a consequence of the closed SDP conditions. For `r=m=1`, `G=diag(1,0)`, `H=[[3/2,-1],[-1,3/2]]`, `J=G H^{-1}G` satisfy the exact lag and block conditions, but `ker G` is nontrivial while H is positive definite. No finite positive-temperature physical family has this triple. Zero-temperature or infinite-temperature atoms may not be silently added to the admissible family.

When G,H are both positive definite, let `S=H^{1/2}`, `M=S^{-1}G S^{-1}`, and write `M=V diag(lambda_i) V^T`, with orthogonal V and all `lambda_i>0`. Set `A=diag(sqrt(lambda_i)) V^T S`, `T=diag(1/lambda_i)`. These real matrices realize G,H and `J_rec=G H^{-1}G`. The Schur complement gives `J_rec <= J`, so the cost does not increase. The original normalizations hold at every frequency, not only a grid. No nonphysical J is needed in this recovery.

At arbitrary range r, a strictly positive G,H reference is obtained by averaging all r shifted nearest-neighbor realizations; their amplitudes are `z^j(1+z)/(2 sqrt(r))` and `z^j(1-z)/(2 sqrt(r))`, `0<=j<r`, with temperatures m and m+4, respectively. The rows span the coefficient space. The two normalizations hold by summing pairs and the total cost is the nearest-neighbor cost. Mix a closed-cone feasible triple with this reference using a positive weight t. G,H become positive definite, affine conditions persist, and the objective tends to the original value as `t -> 0+`. Recover the mixed triple with at most r+1 channels. This proves equality of physical infimum and SDP infimum without claiming that a singular SDP optimizer is realizable.

For the SDP minimum, `Q>=mI` follows from the path-edge square decomposition with nonnegative endpoint contributions. Feasible G and H have fixed traces 1 and c, so their PSD cones intersect bounded trace sections. For a fixed objective sublevel `tr(QJ)-1<=C`, PSD J has `tr J<=(C+1)/m`. This sublevel is bounded, closed, and nonempty for a sufficiently large C; continuity of the linear objective yields attainment. This establishes the distinction between SDP attainment and physical attainment. Strict feasibility for the block is obtained by adding a positive scalar multiple of I to the reference J, so ordinary finite-dimensional Slater theory applies, although the direct certificate below does not need dual attainment theorems.

## 3. Candidate construction

Define

```
q=c-2e, D=e*q-1/2, B=4*c^2*e-c+8*e,
a=2*e*(2*c*e+1)/B, b=1-2*a,
G=diag(a,b,a),
H=[[e,-1/2,0],[-1/2,q,-1/2],[0,-1/2,e]],
Q=[[c,-1,0],[-1,c,-1],[0,-1,c]],
K=H^{-1}G, J=GK=K^T H K.
```

The bracket `c/4<=e<=(3c-2)/8` has positive length `(c-2)/8`. Throughout it `e>=c/4>1/2` and `q>1`. Hence H is positive definite: its form is

```
(e-1/2)(x0^2+x2^2)+(q-1)x1^2
  +(1/2)[(x0-x1)^2+(x1-x2)^2].
```

Also D>0, B>=c^3+c>0, a>0, and `B-4e(2ce+1)=4cD+c+4e>0`, so b>0. Both lag conditions hold identically. The primal block equals `[I;K^T] H [I,K]` and is PSD. Therefore this candidate is feasible and physically recoverable without an approximation limit. The construction imposes symmetry only on the *candidate*, not on the competing set.

Root existence follows from continuity and explicit endpoint values with `m=c-2`:

```
N_c(c/4) = m^7/8 + 7m^6/4 + 39m^5/4 + 55m^4/2 + 81m^3/2 + 27m^2 + 4m > 0,
N_c((3c-2)/8) = -m(63m^6+618m^5+2380m^4+4552m^3+4368m^2+2144m+768)/128 < 0.
```

The inequalities are strict for every m>0; no limit at m=0 is included.

## 4. Universal primal/dual equality (no symmetry assumption on competitors)

Set

```
L=2DB, w=2ce+1, u=w(4D+1), v=B-4ew, x=2ew, y=2ev,
K=[[u,v,w],[x,y,x],[w,v,u]]/L,
U=KQ+QK^T, V=KQK^T.
```

The identity `HK=G` follows by multiplication. U is symmetric Toeplitz for all parameters in the bracket. V is symmetric and reflection-invariant, so only its diagonal entries can violate the Toeplitz condition; direct expansion gives `V00-V11=N_c(e)/L^2`. Therefore V is Toeplitz at every bracket root.

For any other feasible G',H',J', test the block quadratic form on `(-K z,z)` for arbitrary real z. The residual

```
W=J'-K^T G'-G'K+K^T H'K
```

is PSD. Since Q is positive definite, `tr(QW)>=0`, and cyclicity gives

```
tr(QJ') >= tr(U G') - tr(V H').
```

For a symmetric Toeplitz X with first row `(u0,u1,u2)`, `tr(XG')=u0` and `tr(XH')=c*u0-2*u1`, because the exact affine lag constraints are the same for every feasible triple. The right side is consequently independent of the competitor. At the candidate, `G=HK`, `J=GK=K^T H K`, so W=0 and equality holds. This is a global certificate even for singular competing triples. Equivalently the dual block `[V,-KQ;-QK^T,Q]` is PSD since it equals `[K;-I] Q [K^T,-I]`. Both arguments give the same bound.

Evaluating `tr(QJ)` produces the displayed rational expression plus 1. A separate scalar check starts from the restricted symmetric objective

```
F(a,e)=c*a^2/e+(c*q*a^2+c*e*(1-2a)^2-2a*(1-2a))/D.
```

Its second derivative in a equals `B/(eD)>0`. Stationarity gives the stated a. Substitution gives f(e), and

```
f'(e)=-2N_c(e)/[(2ce-4e^2-1)^2 B^2].
```

This scalar calculation alone would not justify global optimality; the universal certificate above does.

## 5. Uniqueness of the bracket root

Suppose e1 and e2 are bracket roots. Each corresponding triple is optimal by the universal certificate. Apply the certificate K1 to the second triple. Optimality gives `tr(QW)=0`. But `W=(K2-K1)^T H2 (K2-K1)`; positive definiteness of both Q and H2 forces K2=K1. Invertibility follows from H_i,G_i>0. Consequently `K1^{-1}=K2^{-1}`, i.e. `G1^{-1} H1=G2^{-1}H2`. Its (0,1) and (1,0) entries are `-1/(2 a_i)` and `-1/(2 b_i)` respectively, so a1=a2 and b1=b2. Its (0,0) entry gives e1/a1=e2/a2. Thus e1=e2. This proves uniqueness on the entire bracket for all positive real m, independently of numerical root isolation.

## 6. Physical attainment and minimum temperature count

The positive definite recovery in section 2, applied to the candidate, realizes its exact J with three rows and temperatures `1/lambda_i`. Hence the physical minimum is attained. The existing two-temperature theorem gives the lower bound `2/[m(m+4)]` for every admissible family with at most two distinct temperatures, regardless of channel count. The accepted explicit degree-two three-temperature witness gives `E_2(m)<=1/[m(m+4)]`, which is strictly smaller. This rules out every two-temperature optimum and forces three distinct temperatures in the constructed three-channel optimum. For comparison the two-temperature bound can also be derived pointwise: if temperatures t<=m and u>=m+4, then `sigma=(D(k)/t-1)(1-D(k)/u)`, minimized at t=m and u=m+4; its average is `2/[m(m+4)]`. No bound on the number of unused zero-amplitude channels is assumed.

The earlier finite-range strict scalar gap, critical coefficient, and fixed-mass joint resource bounds are consistent with this result. It does not resolve physical attainment for all r, establish arbitrary microscopic bath realizability, or convert asymptotic scalings into finite-parameter equalities.

## 7. Independent verification and known limits

`verify_range2_algebraic.py` computes H inverse independently of the K formula, checks 12 groups of exact symbolic identities, isolates the bracket root at 12 rational masses using exact Sturm counts and bisection, and encloses the cost using rational interval arithmetic in the unreduced objective formula. It checks the three historical rational intervals using an independent all-principal-minors PSD test. Their replay is not counted as new scientific cases. See the actual exit code, log and JSON fractions. The first draft of the symbolic verifier had a factor of two error in its *test* for the second derivative in a; the failure is preserved. The verified derivative is B/(eD); neither the stationary a, quartic, cost nor certificate changed. No finite sample substitutes for the all-mass proof.

## 8. Direct all-mass root closure (current revision)

Set e=c/4+mt/8, c=m+2, 0<=t<=1. For P(t)=128 N_c(e), exact expansion gives

```
P(t)=P(0)-A*t-B2*t^2-C3*t^3+D4*t^4
A=32*m*(m+2)^2*(m^2+4*m+2)*(m^2+4*m+5)
B2=8*m^2*(m+2)*(5*m^4+40*m^3+115*m^2+140*m+46)
C3=8*m^3*(m^2+4*m+2)*(m^2+4*m+6)
D4=m^4*(m+2)^3
A-4*D4=4*m*(m+2)^2*(7*m^4+62*m^3+184*m^2+224*m+80)>0.
```

For 0<=s<t<=1, factor t^4-s^4 to bound it by 4(t-s). The other powers are monotone. Thus P(t)-P(s)<=-(A-4D4)(t-s)<0 for every positive real m. The endpoint identities in section 3 imply existence, uniqueness, and strict interiority. This proof is independent of the older optimal-matrix uniqueness proof in section 5 (retained as an alternative). On the entire bracket e>1/2, q>1, D=e*q-1/2>0, B>0, a,b>0; elimination is used only after checking HK=G, exact lags and the two Toeplitz multipliers. The universal PSD residual proves the bound for every competitor, not only reflected candidates. Every bracket root has exact physical cost. No claim is made about roots outside the bracket or uniqueness of all optimal decompositions.

`RangeTwoClosure.lean` verifies the rescaling, strict antitonicity, unique strict root, arbitrary-root exact physical optimum, and `range2_every_optimum_resources` (at least three channels and not a palette of size two for *every* optimum). `range2_complete` combines these with an attaining family of exactly three channels and three distinct positive temperatures. Its `palette_two_is_twoTemperature` proof handles repeated, unused and nonpositive unused palette entries without weakening positivity of actual channel temperatures. The physical model is unchanged. Raw development and staged clean compile logs: `evidence/range2_closure/windows_evidence/`. Six new representative audits list only propext, Classical.choice, Quot.sound. General higher-range physical attainment and general coordinate-SDP minimum are still distinct from this theorem.

The new independent Bernstein checker converts the derivative and positivity polynomials on the rescaled interval to Bernstein coefficients. All coefficient polynomials have nonnegative rational coefficients and at least one positive term. At m>0 each is strictly positive; the basis is nonnegative and sums to one. Ten symbolic certificate groups pass in Windows and Linux, with matching JSON values. They are not new finite science cases. Source SHA-256 `9ed484f2d6fcf14d942cabc419efa45f131ddccca6afb160129efa3152af43bb`.
