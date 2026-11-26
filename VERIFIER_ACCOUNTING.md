# Verifier accounting correction and replay audit

The historical figure 41,243 is the sum of reported check counters excluding the historically separately counted 436 relaxation checks. It is not a count of exclusively exact checks or of distinct theorems. The first verifier uses NumPy sine/cosine, complex exponentials, 2048-point frequency sampling and numerical tolerances after exact rational sufficient-positive-temperature screening. The other active verifiers use exact rational or symbolic calculations; their source was checked for numeric literals, operations and imports. The Linux replay returned the following counters, unchanged from the historic convention.

| Script | Reported count | Method |
|---|---:|---|
| verify_window_v2 | 8,200 | numerical tolerance (exact rational sufficient positivity screening) |
| verify_rational_window | 11,774 | exact rational |
| verify_cyclic_coefficients | 13,976 | exact rational |
| verify_compression | 2,280 | exact rational |
| verify_path_exact | 748 | exact rational |
| verify_new_compression | 720 | exact symbolic/rational |
| verify_relaxation | 436 | exact symbolic; historically excluded from total |
| verify_schur_physical | 322 | exact symbolic/rational |
| verify_real_factorization | 1,238 | exact symbolic/rational |
| verify_finite_gap | 1,340 | exact rational and symbolic/Sturm |
| verify_finite_gap_path | 645 | exact rational and symbolic/Sturm |

- Historic total: 41,243 = 33,043 exact counted checks + 8,200 numerical counted checks.
- Additional previously excluded exact relaxation counter: 436.
- Full active-script replay total: 41,679 = 33,479 exact + 8,200 numerical counted checks.
- No new checks added to the historical total by this replay. A check counter can represent a conjunction of assertions or a test case, and is not always one source-code assert.
- Lean verification and all 42 representative axiom declarations are separate from finite tests.
- Raw cross-platform replay evidence: https://drive.google.com/file/d/1s0kK2W_NZog_OVWMMvkfCIwZoAVOIZtZ/view .

## New work (2026-11-26)

`verify_critical_limit.py`: 340 new exact rational/symbolic checks across r=1..10 and five positive rational masses per range. Independent Chebyshev polynomial recurrence, exact arcsine moments, rational real-root interval/multiplicity tests, and direct discrete Dirichlet inverse. The test construction checks nonnegative degree-bounded rates, not sampled-only positivity. Real FIR factor existence is provided by the Lean factorization theorem. Exit 0 on Linux Python 3.13.5 / SymPy 1.14.0. The failed r=1..18 attempt timed out after printing r=15 and is preserved, not counted. The 340 are counted units, not distinct general theorems. No new Windows Python execution of this new verifier is claimed. Prior 11/11 Windows and Linux results remain valid for their byte-identical sources. Updated historic-convention total 41,583 = 33,383 exact + 8,200 numerical-tolerance. Including 436 separately counted historical exact checks: 42,019 = 33,819 exact + 8,200 numerical.


## Temperature-resource extension and adversarial audit

`verify_temperature_count.py` (canonical SHA-256 b218d3b9fb641bf217778b71b73bd07ceb1a5920bbaf02cc2bbdea108092c8ef) adds 571 exact scientific test units (symbolic two-point mixture identities; exact all-interval rate positivity; exact Fourier weighted half-cost; rational exterior-node cases; critical thresholds for r=2..40) and 15 separately reported software root-sign regressions. Linux Python 3.13.5/SymPy 1.14.0 and Windows Python 3.11.9/SymPy 1.13.1 both exit 0. The prewording and first-pass variants are evidence, not separate active verifiers. A suspected original verifier bug was refuted: `a in (-1,1)` is literal tuple membership. The original byte-exact critical script remains active. Alternate square-free/Sturm 340 checks repeat old cases; 17 classifier comparisons and 15 new software regressions are not scientific counter additions. Windows cross-platform replay is also not counted twice.

Current convention: 42,154 = 33,954 exact + 8,200 numerical tolerance. Including additional 436 historic exact units: 42,590 = 34,390 exact + 8,200 numerical tolerance. Count 58 representative axiom declarations separately. No assertion-count convention implies 42,154 different theorems. Finite tests only support the analytic/kernel proofs.

## Joint-resource extension
New `verify_temperature_resource.py` uses only standard-library Fraction exact arithmetic: 165 palette cases (including duplicate/unused slots and exterior actual temperatures) and 825 structured feasible polynomial-rate family cases at five degrees, checked via adjacent secants, exact tent integrals, Bernstein coefficient certificates and beta/arcsine moments. Same-T channel splitting preserves cost. 14,385 internal assertion evaluations include old-identity regressions and are NOT added as the scientific count. The first accounting variant (raw assertion counter) is archived and superseded by the conservative 990 structured-unit convention. Both Linux Python 3.13.5 and Windows (version log in raw evidence) exit zero and use identical verifier bytes SHA-256 b1f42aeb3f2112a1c64be6142fcb17c2cdccdc27a9cd6ffd3ae18aa1c3c32e5f. Cross-platform repeats are not counted. New total 43,144 = 34,944 exact + 8,200 numerical-tolerance; historical extra 436 exact remains separate, as do 15 software regressions. 64 representative axiom audits are separate. Finite tests do not establish universality.


## Exact SDP extension (current)
New verify_exact_sdp.py: Linux Python 3.13.5/SymPy 1.14.0, exit 0. 32 reference, 96 singular-boundary mixtures, 7 range-one dual, 3 range-two primal/dual, 6 generalized eigenvector recovery =144 exact structured cases. The first and improved PSD check versions cover the same cases and are counted once. No floating tolerances in certificate validation. Historic total 43,288=35,088 exact+8,200 tolerance; additional 436 historic exact and earlier 15 software regressions separately retained. No prior tests rerun for credit. 73 representative axiom audits separate from science counts.

## Range-two algebraic extension
12 new structured rational cases (all-mass theorem supported by independent proof; these are finite checks). 12 symbolic identity groups separately, not added. Three predecessor rational primal/dual certificates checked again by all principal minors; zero new credit. Linux exit 0; failed preliminary symbolic second-derivative expectation preserved (factor-of-two expectation, not theorem failure). Current historical convention 43,300 = 35,100 exact + 8,200 tolerance; another 436 historical exact units reported separately (43,736 including them). No repeat count and no new Windows Python execution.

## Current range-two closure and cross-platform evidence

Windows replay of the already counted `verify_exact_sdp.py` (144 cases) and `verify_range2_algebraic.py` (12 cases, 12 symbolic groups, three historical certificates) succeeded; input bytes match the earlier accepted sources and both output JSON values match the earlier Linux outputs. No new science count. `verify_range2_closure.py` independently converts universal positivity identities to Bernstein form. Windows Python 3.11.9 / SymPy 1.13.1 and Linux Python 3.13.5 / SymPy 1.14.0 each exit zero. Ten universal symbolic certificate groups, separate; JSON values match across platforms. Active scripts 17, active Lean modules 45, 87 representative axiom audits. Historic convention unchanged: 43,300 = 35,100 exact + 8,200 tolerance; separate 436 earlier exact and 15 software regressions remain separate. No duplicate counts.
