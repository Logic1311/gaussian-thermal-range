# Bath compression theorem (physical compression kernel-verified)

Let A be the real q by n coefficient matrix of any admissible finite bath family, T a positive diagonal q by q matrix, and x(z)=(1,z,...,z^(n-1))^t. Let U be a real q by d orthonormal basis matrix for range(A), where d=rank(A)<=n. Write A=UR, and M=U^t T U. M is positive definite. Diagonalize M=V diag(t) V^t by a real orthogonal V. Define A'=V^t R with d rows and positive temperatures t.

Then A'^t A'=A^t A and A'^t diag(t) A'=A^t T A, so both all-frequency physical constraints are unchanged. The new inverse-temperature Gram matrix is R^t M^(-1) R. The old one is R^t U^t T^(-1) U R.

For any real y, put v=M^(-1)y and q=T^(-1/2)Uy-T^(1/2)Uv. Then ||q||^2=y^t U^t T^(-1) U y-y^t M^(-1)y >=0, using U^t U=I. Thus the inverse-temperature Gram difference is positive semidefinite. This extends to complex x by writing real and imaginary parts. Since D(z)>0, the new entropy is pointwise no larger than the old one. All coefficients are real and support length is unchanged. Hence the infimum over arbitrarily many finite baths equals that over at most n=r+1 baths. No claim of attainment follows.

In particular the explicit cyclic construction may be compressed to n baths without worsening its entropy upper bound. This gives a separate structural theorem beyond the r^-2 order. The underlying compression inequality is classical operator convexity of inversion; novelty of this application is not established.

A direct alternative uses the path adjacency J on n vertices, G=diag(g), M=cI-J/rho, A'=V^t G. Its two Gram matrices are G^2 and G M G, so the two physical constraints follow exactly. Since ||J||<=2, M is positive definite when c>2/rho. The mean unweighted residual equals trace(G M^2 G)-c^2-2 = (2-g_0^2-g_(n-1)^2)/rho^2-2, at most the cyclic residual 2/rho^2-2. This uses fewer baths and gives a slightly better upper bound, but does not replace the requested cyclic construction in the main formalization.

Status: analytical derivation with physical compression now kernel-verified; not peer reviewed, not a novelty certification.
## Full-frequency comparison and exact positivity
Let n=r+1, N=2n+3, and C=cI-J_cycle/rho on R^N. The real cosine/sine Fourier frame used in the cyclic realization resolves C (each frequency pair shares its eigenvalue). Its coefficient Gram is obtained by restricting to the first n coordinates and multiplying by G on both sides. With E the coordinate inclusion, E^T C E=M=cI-J_path/rho. If C is SPD, M is SPD. The exact identity

E^T C^{-1} E-M^{-1}=(E-C E M^{-1})^T C^{-1}(E-C E M^{-1})

follows by expanding, using E^T E=I and E^T C E=M. Thus G times this difference times G is PSD. Apply separately to real and imaginary parts of x=(1,z,...,z^{n-1}) and multiply by D>0 to prove pointwise sigma_path<=sigma_cyclic, not merely a residual comparison.

The vectors sin((j+1)k*pi/(n+1)), j=0,...,n-1, satisfy the path adjacency eigen-equation by the sine addition identity and the two vanishing boundary values. For k=1,...,n they are nonzero and have distinct eigenvalues 2 cos(k*pi/(n+1)), hence form an orthogonal basis. For rho>0 the exact positivity threshold is c>2 cos(pi/(n+1))/rho. The trace of G M^2 G is c^2+(2-g_0^2-g_{n-1}^2)/rho^2, since each endpoint has degree one and all internal vertices degree two. Subtract c^2+2 for the averaged variance. Division by m times the smallest eigenvalue bounds entropy. At the cyclic zero-temperature threshold the path is strictly positive; n=2 has rho=1/2 and minimum temperature m. For n=3 rho=12/17, so positivity requires m>17 sqrt(2)/12-2; m=1/100 is admissible, m=1/10000 is not. The n=40 cyclic boundary m=10/1677 is exact. No uniform claim as m tends to zero.

## Exact Gram certificate for general compression
For U^T U=I, M=U^T T U, X=U-T U M^{-1}, expansion gives U^T T^{-1} U-M^{-1}=X^T T^{-1} X. This does not require matrix square roots. Multiplication by R and evaluation on real and imaginary parts of x preserves nonnegativity. Rank zero contradicts normalization. Choose an orthonormal basis of the actual column space, not the entire bath space. Diagonalize M, whose strict positivity follows from injectivity of U and T>0. A'=V^T R preserves both Gram constraints exactly. Costs decrease by integration. Inclusion of restricted costs gives one infimum inequality; the pointwise construction supplies a restricted cost no larger than every original cost, giving the other. No attainment or minimality is asserted.

Verification: verify_new_compression.py, 36 rank-deficient physical configurations, 720 assertions, exit 0, Python 3.11.9 / SymPy 1.13.1. These are finite exact certificates, not a substitute for the general theorem. Physical compression existence and the path adjacency spectrum are now verified; exact temperature-spectrum linkage and path residual are separate extension tasks.
## Verified path spectral completion (2026-11-26)
PathSpectralLink.lean verifies the exact set of actual bath temperatures, and pathBath_admissible_iff is the exact necessary-and-sufficient strict-positivity condition. PathResidual.lean verifies path_avg_residual and path_entropy_upper_exact, giving the endpoint-corrected mean residual and bound with the actual minimum path temperature. Both have successful compilation and standard-axiom audits. PathConstruction.lean proves pointwise and mean entropy dominance over the cyclic construction on the cyclic admissibility domain. The earlier pending-status lines above are historical and superseded.
# Final integration note (26 November 2026)
All physical compression, restricted-infimum, boundary, path spectrum/residual, and pointwise dominance declarations remain unchanged and passed the clean replay. RateEquivalence now proves exact equality of physical mean-cost sets for all degree-bounded nonnegative real trigonometric individual rates and real FIR. Thus the at-most-r+1 channel reduction also suffices for the rate-class mean-cost infimum; no claim of pointwise dominance of an unsymmetrized original odd rate is needed. MajorantExact proves the separate relaxed optimization problem and the exponential relative gap.

## 2026-11-26 finite-range extension
The earlier original-model, compression, and window results remain unchanged. FINITE_GAP_PROOF.md proves a new pointwise physical barrier and strict scalar-relaxation gap at every r>=2, not merely an asymptotic gap. The new proof uses the same physical constraints and the exact prior relaxed minimum. See FiniteGapStrict.lean; no extra temperature or channel-count assumption.
