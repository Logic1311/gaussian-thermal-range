# Exact finite-dimensional physical optimization — theorem 13

WORKING / UNPUBLISHED. 26 November 2026. AI-derived proof; not an independent human originality assessment.

The full analytic proof, notation, singular counterexample, and rational primal/dual certificate argument are in section 12 of `manuscript.tex` (also `sdp_section.tex` in the evidence folder). The model is precisely the previous normalized real FIR implementation class. All statements concern arbitrary finite positive-temperature families, all continuous unit-circle frequencies, and the normalized circular mean. No arbitrary microscopic DOS equivalence, palette constraint or physical optimum attainment is claimed.

## Key argument and formal coverage

For n=r+1 and c=m+2 let G,H,J be symmetric n-by-n matrices, with G positive semidefinite and [H G; G J] positive semidefinite. The two affine lag conditions fix tr G=1, all positive-lag G sums zero, tr H=c, lag-one H sum -1, all higher H sums zero. With Q=cI-Adj(P_n) the objective is tr(QJ)-1. The equality of this SDP minimum and E_r(m) for r>=1,m>0 follows from the following chain.

1. Physical inclusion: G=A^t A, H=A^t T A, J=A^t T^{-1} A; the block is a Gram matrix and the constraints and objective follow by exact Fourier expansion.
2. Positive definite recovery: put S=H^(1/2), R=S^(-1); diagonalize RGR with real orthonormal e_i and positive eigenvalues lambda_i. Rows sqrt(lambda_i)e_i^t S, temperatures 1/lambda_i, have moments G,H,GH^(-1)G. Testing the block on (-H^(-1)Gy,y) proves GH^(-1)G <= J. Pointwise entropy does not increase. The number of rows is n.
3. Full-rank admissible reference: average the r shifted nearest-neighbor pairs z^i(1+z)/(2sqrt(r)), z^i(1-z)/(2sqrt(r)) at temperatures m,m+4, respectively. Their rows span every coordinate; both G0,H0 are positive definite and both lag constraints hold exactly.
4. Mix any closed-cone feasible triple with this reference by weight t>0. The mixed G,H are positive definite, the affine conditions remain exact, and the cost tends to the original objective as t tends to zero. This establishes arbitrary-tolerance recovery with at most n channels and both inequalities between infima.
5. Analytic finite-coordinate/minimum argument: the Fourier formula gives the stated lag and trace conditions; Q>=mI. The trace bounds on G,H and the objective sublevel bound on tr J make a nonempty closed sublevel compact. Adding a positive scalar identity to reference J makes the block strictly positive, hence Slater applies. Physical attainment is left open.

The new Lean theorem `GaussianRange.exact_sdp_infimum` proves `sInf (sdpCosts r m) = optimalEntropy r m` with all assumptions r>0,m>0 in the equivalent real-operator formulation; `sdp_recover_approx` proves the arbitrary-positive-epsilon existence statement with cardinality <=r+1, original admissibility and cost inequality. `sdpRealization` handles SPD G,H directly; `reference_sdp` constructs the admissible reference; `physical_subset_sdp` handles the unrestricted original family class. `SDPFeasible` contains symmetry, G quadratic-form nonnegativity, the full two-vector block quadratic condition and exact unit-circle normalizations. Explicit finite diagonal sums and trace calculation, compactness/Slater, classical moment comparison and concrete rational matrix certificates are analytic / separately exact-checked, not asserted as separate Lean theorems. See final source and clean replay logs for actual signatures. All nine new representative axiom checks list only propext, Classical.choice, Quot.sound.

## Why closed-cone feasibility is not physical feasibility

At r=m=1 choose G=diag(1,0), H=[[3/2,-1],[-1,3/2]], J=GH^(-1)G. Both Fourier constraints and block PSD hold. But a zero second diagonal G entry forces the corresponding column of every physical A to vanish, inconsistent with H[1,1]>0 (zero-based). The approximation in step 4 is essential. This also refutes an indiscriminate use of a singular inverse in the physical reconstruction.

## Exact dual certificates and verification

Take real C, symmetric V_plus with Z=[V_plus C; C^t Q] PSD. If U=-(C+C^t) and V=-V_plus are symmetric Toeplitz, tr(UG)+tr(VH)-1 is constant on the primal affine constraints and is a lower bound by tr(Z [H G;G J])>=0. The verifier constructs rational certificates with G,H positive definite and J=GH^(-1)G, producing upper bounds attained by the recovered families. See the exact fractions in range2_exact_certificates.json; the outward rounded intervals are printed in the manuscript. The frozen trial parameters were selected numerically, but no float tolerance enters certificate validation. The 144 new structured cases additionally verify the shifted reference, singular nonphysical triples, convex mixing, exact r=1 primal/dual equality, and generalized eigenvector recovery in the H metric (rather than Lean's square-root basis). No repeat case is counted twice. The independently coded verifier is not an independent human review.
