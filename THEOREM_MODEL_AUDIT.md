# Theorem/model audit — 26 November 2026

Scope: the original definitional review is retained, followed by the critical and temperature-resource extensions. Actual replay scopes and exit codes are in ENGINEERING_ACCEPTANCE.json. This document does not replace a referee or a kernel proof.

## Definitional correspondence and non-vacuity

| Manuscript concept | Source definition / exact domain |
| --- | --- |
| Degree-r, real FIR coefficients | Integrated.lean: amp, finite sum j in range(r+1), real a(j) cast into complex. Values beyond r irrelevant. |
| Frequency | all complex z with norm 1, no discrete test grid. |
| D, w, sigma | Integrated.lean: dispersion c z = c-2 Re z; weight = squared norm of amp evaluation; sigma = D * sum(w/T) - 1. |
| Average | Integrated.lean: avg = Real.circleAverage f 0 1. |
| Arbitrary finite baths | BathFamily contains finite index type, Fintype witness, real coefficients and real temperatures. No fixed bath count; even zero-amplitude channels allowed. |
| Admissibility | positive temperature for every index, both normalization constraints for all unit-circle z. |
| Physical infimum | admissibleCosts contains every admissible family's mean cost; optimalEntropy = sInf of that set. Boundary proves nonemptiness for m>0,r>=1 and no admissible family at r=0. |
| Restricted infimum | restricted_inf_eq: m>0,r>0, sInf restrictedCosts = optimalEntropy; compression is unconditional on full rank of original matrix. |
| Rates | RateFamily: all real cosine and sine coefficients truncated at r; rates nonnegative on entire circle, same positivity and normalization. rateCosts_eq proves equality of cost sets, not pointwise equivalence for odd rates. |
| Majorant | trigMajorant = all unit z, 1 <= D*trigRate; arbitrary cosine and sine coefficients. Since m>0, equivalent to g>=1/D. relaxedEntropy = sInf majorantCosts. majorant_exact_minimum gives IsLeast, including attainment of relaxed cost only. |
| Exact value | algebraicRelaxedValue(r+1,t), t>1, m+2=t+t^-1. Hyperbolic form by analytic geometric sum. |
| Pointwise lower bound | physical_pointwise_barrier: for all m>0,r>0, admissible b and unit z, z.im^2 / ((m+2)*momentBudget(r)*D(z)) <= sigma; momentBudget = sum j^2. |
| Strict finite gap | strict_finite_range_gap(r:Nat)(2<=r)(m:Real)(0<m): relaxedEntropy r m < optimalEntropy r m. No optimizer attainment assumption. finite_range_gap_bound gives quantitative correction. nearest_gap_zero proves exact r=1 equality. |

The 42 representative declarations are explicit `#check` and `#print axioms` outputs in the three audit logs. Their whitelist was checked; the other project modules are compiled as dependencies and many contain additional axiom prints. A text scan is not a substitute for a Lean kernel check. No explicit sorry/admit/sorryAx/axiom/unsafe was found in executable project-source text by this supplementary scan; no import cycle in the 29 listed local modules. The imports of Mathlib rely on the recorded exact Mathlib commit and prebuilt dependency cache. This is not a from-scratch build of all Mathlib.

## Statement coverage and boundaries

- Theorem 1: physical_entropy_lower/admissible_lower; correct positive mass/range and all-frequency constraints. Theorem 2 and Corollary 3: rational physical realization, explicit bound and optimalEntropy_theta; asymptotic constants fixed per m, not a uniform m->0 result. 
- Theorem 4: compress_admissible, restricted_inf_eq; positivity and pointwise monotonicity preserved; rank bound, not claimed minimal channel count.
- Section 5: pathBath_admissible_iff, pathBath_sigma_le_cyclic, path_avg_residual, path_entropy_upper_exact; formal path uses rational window. The comparison sine-window formula in the prose is an analytic comparison, not separately asserted as a machine theorem.
- Proposition 5 / Corollary 6: realFactor_interval, trigRate_sym_factor, rateFIR_realization, rateCosts_eq; allows nonnegative factors with roots and odd rates via evenization.
- Section 7: majorant_exact_minimum, physical_cost_subset_majorant, actual_gap_theta. The scalar optimum is classical prior result; physical gap follows from the two feasible sets and lower/upper physical order. The exact hyperbolic leading coefficient is the manuscript's analytic reformulation, not separately proved as a hyperbolic limit in Lean.
- Theorems 7--8: physical_pointwise_barrier, finite_range_gap_bound, strict_finite_range_gap, nearest_gap_zero. Distinguish r^-3 correction at fixed m from the stronger large-r order r^-2. This proves strict separation of infima, including sequences, not merely nonattainment of one candidate.

## Representative kernel axiom evidence (staged logs)

- FinalAudit: `GaussianRange.optimalEntropy_theta` — `propext, Classical.choice, Quot.sound`
- FinalAudit: `GaussianRange.BathFamily.sigma_identity` — `propext, Classical.choice, Quot.sound`
- FinalAudit: `GaussianRange.compress_admissible` — `propext, Classical.choice, Quot.sound`
- FinalAudit: `GaussianRange.restricted_inf_eq` — `propext, Classical.choice, Quot.sound`
- FinalAudit: `GaussianRange.compressed_rank_pos` — `propext, Classical.choice, Quot.sound`
- FinalAudit: `GaussianRange.pathBath_count` — `propext, Classical.choice, Quot.sound`
- FinalAudit: `GaussianRange.pathBath_admissible_iff` — `propext, Classical.choice, Quot.sound`
- FinalAudit: `GaussianRange.pathBath_sigma_le_cyclic` — `propext, Classical.choice, Quot.sound`
- FinalAudit: `GaussianRange.pathBath_cost_le_cyclic` — `propext, Classical.choice, Quot.sound`
- FinalAudit: `GaussianRange.path_avg_residual` — `propext, Classical.choice, Quot.sound`
- FinalAudit: `GaussianRange.path_entropy_upper_exact` — `propext, Classical.choice, Quot.sound`
- FinalAudit: `GaussianRange.rankTwo_exact_minimum` — `propext, Classical.choice, Quot.sound`
- FinalAudit: `GaussianRange.power_relaxation_minimum` — `propext, Classical.choice, Quot.sound`
- FinalAudit: `GaussianRange.factor_relaxation_minimum` — `propext, Classical.choice, Quot.sound`
- FullAudit: `GaussianRange.realFactor_interval` — `propext, Classical.choice, Quot.sound`
- FullAudit: `GaussianRange.real_factor_weight` — `propext, Classical.choice, Quot.sound`
- FullAudit: `GaussianRange.trigRate_sym_factor` — `propext, Classical.choice, Quot.sound`
- FullAudit: `GaussianRange.rateFIR_realization` — `propext, Classical.choice, Quot.sound`
- FullAudit: `GaussianRange.rateCosts_eq` — `propext, Classical.choice, Quot.sound`
- FullAudit: `GaussianRange.rate_infimum_eq` — `propext, Classical.choice, Quot.sound`
- FullAudit: `GaussianRange.poly_cos_repr` — `propext, Classical.choice, Quot.sound`
- FullAudit: `GaussianRange.factor_root_iff` — `propext, Classical.choice, Quot.sound`
- FullAudit: `GaussianRange.majorant_exact_minimum` — `propext, Classical.choice, Quot.sound`
- FullAudit: `GaussianRange.relaxedEntropy_eq` — `propext, Classical.choice, Quot.sound`
- FullAudit: `GaussianRange.physical_cost_subset_majorant` — `propext, Classical.choice, Quot.sound`
- FullAudit: `GaussianRange.actual_gap_theta` — `propext, Classical.choice, Quot.sound`
- FullAudit: `GaussianRange.factor_gap_theta` — `propext, Classical.choice, Quot.sound`
- FullAudit: `GaussianRange.relaxed_scaled_bounds` — `propext, Classical.choice, Quot.sound`
- FiniteGapAudit: `GaussianRange.angular_normalizations` — `propext, Classical.choice, Quot.sound`
- FiniteGapAudit: `GaussianRange.moment_energy_bound` — `propext, Classical.choice, Quot.sound`
- FiniteGapAudit: `GaussianRange.bath_moment_energy_bound` — `propext, Classical.choice, Quot.sound`
- FiniteGapAudit: `GaussianRange.bath_angular_variational` — `propext, Classical.choice, Quot.sound`
- FiniteGapAudit: `GaussianRange.physical_pointwise_barrier` — `propext, Classical.choice, Quot.sound`
- FiniteGapAudit: `GaussianRange.physical_constant_barrier` — `propext, Classical.choice, Quot.sound`
- FiniteGapAudit: `GaussianRange.avg_im_square` — `propext, Classical.choice, Quot.sound`
- FiniteGapAudit: `GaussianRange.barrier_majorant_lower` — `propext, Classical.choice, Quot.sound`
- FiniteGapAudit: `GaussianRange.finite_range_gap_bound` — `propext, Classical.choice, Quot.sound`
- FiniteGapAudit: `GaussianRange.strict_relaxed_height` — `propext, Classical.choice, Quot.sound`
- FiniteGapAudit: `GaussianRange.strict_finite_range_gap` — `propext, Classical.choice, Quot.sound`
- FiniteGapAudit: `GaussianRange.nearest_sigma_exact` — `propext, Classical.choice, Quot.sound`
- FiniteGapAudit: `GaussianRange.nearest_cost_exact` — `propext, Classical.choice, Quot.sound`
- FiniteGapAudit: `GaussianRange.nearest_gap_zero` — `propext, Classical.choice, Quot.sound`

## Local import order

Core -> Entropy -> FourierBridge -> Integrated -> Compression -> Boundary -> CompressionExistence -> PhysicalCompression -> PhysicalInfimum -> PathConstruction -> PathSpectrumCore -> PathSpectralLink -> PathResidual -> RelaxationAlgebra -> RelaxationPower -> FinalAudit -> RealFactorBase -> RealFactorization -> TrigSymmetry -> RateEquivalence -> RelaxationGap -> MajorantBridge -> MajorantExact -> FullAudit -> PointwiseBarrier -> PointwiseBound -> FiniteGapBound -> FiniteGapStrict -> FiniteGapAudit

Local dependency edges (importer : import):
- Compression: Integrated
- Boundary: Integrated
- CompressionExistence: Integrated
- PhysicalCompression: CompressionExistence
- PhysicalInfimum: PhysicalCompression
- PhysicalInfimum: Compression
- PhysicalInfimum: Boundary
- PathConstruction: PhysicalInfimum
- PathSpectrumCore: Integrated
- PathSpectralLink: PathConstruction
- PathSpectralLink: PathSpectrumCore
- PathResidual: PathSpectralLink
- RelaxationPower: Integrated
- RelaxationPower: RelaxationAlgebra
- FinalAudit: PathResidual
- FinalAudit: RelaxationPower
- RealFactorBase: Integrated
- RealFactorization: RealFactorBase
- TrigSymmetry: RealFactorBase
- RateEquivalence: RealFactorization
- RateEquivalence: TrigSymmetry
- RateEquivalence: Compression
- RelaxationGap: RelaxationPower
- MajorantBridge: TrigSymmetry
- MajorantBridge: RealFactorization
- MajorantBridge: RelaxationPower
- MajorantExact: MajorantBridge
- MajorantExact: RateEquivalence
- MajorantExact: RelaxationGap
- FullAudit: FinalAudit
- FullAudit: MajorantExact
- PointwiseBarrier: MajorantExact
- PointwiseBarrier: PhysicalInfimum
- PointwiseBound: PointwiseBarrier
- FiniteGapBound: PointwiseBound
- FiniteGapStrict: FiniteGapBound
- FiniteGapAudit: FullAudit
- FiniteGapAudit: FiniteGapStrict


## Final accounting correction (supersedes earlier wording)
See VERIFIER_ACCOUNTING.md: 41,243 historical counted checks comprise 33,043 exact rational/symbolic and 8,200 numerical-tolerance checks. The 436 extra exact relaxation checks remain outside the historical counter convention. Linux replay 11/11 successful, 41,679 reported units including the 436. No new mathematical claims or counted tests. The revised manuscript makes this distinction explicit.


## Full sequential replay acceptance (supersedes earlier pending status)

The Windows fresh project rebuild, CoS session 71743, returned exit 0 after all 29 Lean modules and 11 scientific verifier scripts. The cloud-read fresh replay evidence supplies 41 SHA-256 input hashes (including reproduce.ps1), all byte-exact against the current sources. The three audit logs each report 14 declarations (42 distinct representative declarations in total); all axiom dependencies are subsets of the standard three. The strict statement is `relaxedEntropy r m < optimalEntropy r m` for `2 ≤ r`, `0 < m`; it asserts no physical optimizer. A lexical review of active Lean modules found no sorry/admit/unsafe or added axiom declaration; the only word `admit` occurs as English in a RateEquivalence doc comment. Local project imports follow the recorded dependency order. The shared precompiled Mathlib dependency cache was used, not rebuilt. The actual proof statements and full logs, rather than these summaries, are the authoritative evidence.

## New critical-mass theorem (superseding earlier open fixed-r coefficient)

Theorem 9: for r>=1, m>0, define C_r=12/((r+1)(r+2)(r+3)). The new bound C_r/m-1 <= optimalEntropy r m <= C_r/m+4(r+1)^2 is in the SAME physical model, not the scalar relaxation. CriticalEnergy proves the exact finite-support evaluation-energy inequality and its cold-window equality; CriticalRealization builds 3 actual real FIR channels via the established factor theorem, with strict positive temperatures and both all-frequency constraints; CriticalScaling establishes the family lower bound, physical construction cost upper, both infimum inequalities and quantitative squeeze. The ratio limit and hyperbolic Taylor expansion are analytic consequences, not separate formal limit theorems. The upper bound is not an attainment statement. The original finite-m strict gap and fixed-positive-m large-r order remain unchanged. Fixed-r is essential; the explicit error is not uniform in r. No assumption that arbitrary DOS factors preserve individual rate degree, no temperature cap, no sampling-only constraint, no new nonstandard axiom.

New representative axiom audit (all [propext, Classical.choice, Quot.sound], actual clean replay): firstDiff_amp, critical_energy_lower, critical_cold_energy, criticalCoeff_sum, critical_mix_bounds, critical_realization, critical_family_lower, critical_realization_upper, critical_infimum_bounds, critical_infimum_squeeze. New module dependency order: CriticalEnergy -> CriticalRealization -> CriticalScaling, with CriticalEnergy importing FiniteGapStrict. See evidence/critical_extension_lean/clean_replay/. Clean extension replay CoS 86953 exit 0, 3/3 module exits 0, 32/32 actual base/extension input source SHA-256 match. Existing 29-module full fresh replay remains intact and was used as the dependency basis; no new one-command all-32-module execution is claimed. The original 42 audit entries remain byte-identical in their preserved evidence.


## Temperature count extension: actual kernel statements and scope

`TemperatureCount.lean` preserves the exact unit-circle admissibility and introduces `BathFamily.twoTemperature` (exists ordered a,h with 0<a, each temperature equals a or h). It imposes no bound on number of amplitude channels, no endpoint-node assumption, and allows equal candidates (ruled out by the two normalization identities). Actual successful v2 development output:

```lean
GaussianRange.two_temperature_minimum (r : ℕ) (hr : 0 < r) (m : ℝ) (hm : 0 < m) :
  IsLeast (GaussianRange.twoTemperatureCosts r m) (2 / (m * (m + 4)))
GaussianRange.critical_three_temperature_advantage (r : ℕ) (hr : 2 ≤ r) (m : ℝ) (hm : 0 < m)
  (hsmall : m ≤ 1 / (40 * (↑r + 1) ^ 2)) :
  ∃ b, b.admissible r m ∧ Fintype.card b.ι = 3 ∧ ¬b.twoTemperature ∧
    ∀ a, a.admissible r m → a.twoTemperature → b.cost r m < a.cost r m
```

`ThreeTemperature.lean` actual successful v2 development output:

```lean
GaussianRange.three_temperature_half_cost (r : ℕ) (hr : 2 ≤ r) (m : ℝ) (hm : 0 < m) :
  ∃ b, b.admissible r m ∧ Fintype.card b.ι = 3 ∧ ¬b.twoTemperature ∧ b.cost r m = 1 / (m * (m + 4))
```

The six representative audited theorems (`two_temperature_minimum`, `two_temperature_pointwise`, `critical_three_temperature_advantage`, `three_temperature_realization`, `three_temperature_half_cost`, `unrestricted_strict_two_temperature_gap`) list only propext, Classical.choice and Quot.sound. Failed v1 development versions retained but not active; kernel acceptance is exit 0, not log absence of errors alone. The critical minimum-level limit follows from the quantified scaled inequality and earlier critical squeeze; no formal filter-limit statement is claimed. Analytic independent square completion, strict nonzero rates, explicit FIR factors and generator heat derivation are in CRITICAL_ADVERSARIAL_REVIEW.md; do not claim Lean proved stochastic calculus or a microscopic equivalence. The root 32 prior module sources remain byte identical. The new resource theorem does not weaken assumptions of any old result and its exact attained minimum is only the two-temperature restricted one.


## Joint range and palette extension
The new `temperaturePalette` predicate covers actual channel temperatures with `Fin K` values; unused slots may be arbitrary and repeated, while every actual bath remains strictly positive. No bound on the number of channels per temperature. `paletteCosts` retains `b.admissible r m`, its full circle conditions and `b.cost r m`, and `optimalPaletteEntropy` uses sInf. `palette_nearest_mem` and `palette_bddBelow` establish the actual nonempty bounded-below set. `paddedBath` truncates coefficients at the smaller degree n, preserves their amplitudes at degree budget r>=n, and preserves admissibility, cost and the palette. `palette_inf_le_range` compresses arbitrary feasible degree-n families using the existing physical theorem; no attainment is required.

Actual successful clean replay statements:
```lean
GaussianRange.palette_cost_lower (b : GaussianRange.BathFamily) (r K : ℕ) (hK : 0 < K) (m : ℝ) (hm : 0 < m)
  (hb : b.admissible r m) (hpal : b.temperaturePalette K) :
  1 / (64 * Real.pi * (m + 4) ^ 2 * ↑K ^ 2) ≤ b.cost r m
GaussianRange.palette_joint_resource_scaling (m : ℝ) (hm : 0 < m) :
  ∃ A B, 0 < A ∧ 0 < B ∧ ∀ (r K : ℕ), 0 < r → 2 ≤ K →
  A / ↑(min r K) ^ 2 ≤ GaussianRange.optimalPaletteEntropy r K m ∧
  GaussianRange.optimalPaletteEntropy r K m ≤ B / ↑(min r (K - 1)) ^ 2
```
Six new representative audits: temperature_far_penalty, temperature_avoidance_pointwise, palette_cost_lower, palette_inf_lower, palette_inf_le_range, palette_joint_resource_scaling; all list propext, Classical.choice, Quot.sound, no sorryAx. Full final statements and initial failures are in the raw Windows evidence. The analytic joint-order and sharper secant bound are derived in RESOURCE_TRADEOFF_PROOF.md; they are not separate formal limit/quantization theorems. All 34 predecessor source bytes match the staged input manifest; both new development and clean replay sources also match. The base 32 modules had a full clean run; two temperature modules and two resource modules were subsequently built cleanly in separate stages against those verified dependencies. No all-36 one-command execution claimed. The new dependencies are existing cached Mathlib integral/measure modules. No shared toolchain modification.

## CURRENT external-review revision audit
See JOINT_RESOURCE_ADVERSARIAL_REVIEW.md sections 1--6 for explicit boundary cases and proof checks, and LITERATURE_RECHECK_2026-11-26.md for the classical derivation. The quantified palette inequalities hold with constants depending only on fixed m, not r or K; at K>=r+1 compression implies equality to the unrestricted infimum by cost comparison and set inclusion, not optimizer attainment. Empty feasible cases are not physical zero cost. Temperature count is not channel count. The separate centered Fourier proof and DOS scope illustration are analytic comparisons only. No new formal statement is asserted. All 36 Lean sources, 14 scientific verifiers, reproducer and existing process evidence are unchanged byte-for-byte. All theorem/proof environments in the manuscript are unchanged. No blanket claim of an independent reproof of every theorem or full microscopic sufficiency is made.


## Current new theorem 13
See EXACT_SDP_PROOF.md and SDPSpectral.lean, SDPMoments.lean, SDPReference.lean, SDPRealization.lean, SDPExact.lean. The kernel-checked result is exact equality of the physical and closed-operator SDP infima and existence of original admissible families (cardinality <=r+1) within arbitrary positive epsilon of each feasible SDP objective. No physical attainment assumed. SPD recovery is pointwise. Coordinate lag/trace translation, attained matrix minimum, Slater and prior-art moment mapping are analytic; rational intervals separately exact-checked. Singular example prohibits a stronger feasible-triple equality claim. Nine new audited declarations, all standard axioms. Earlier 23 theorem/proof environments unchanged.

## Range-two follow-up (26 November 2026)
The original model remains arbitrary finite nonempty positive-temperature real FIR families, not a symmetric ansatz. The exact value and attainment theorem is `GaussianRange.range2_exact_attained`; `GaussianRange.range2_sdp_global` provides universal comparison, including singular/non-reflection-symmetric triples. Supporting modules are RangeTwoCoordinates (Fourier coordinate/average), RangeTwoAlgebra (quartic root existence, algebraic dual identities), RangeTwoExact (candidate feasibility, global optimum and physical recovery). The clean kernel audits of these modules list only standard axioms. Root uniqueness, strictness of bracket endpoints, and minimality of exactly three distinct temperatures/channels follow analytically; general physical attainment for r>=3 is unproved. The range-two derivation uses the original normalized cost, not scalar majorant minimization. General SDP coordinate/compactness arguments remain analytic. See RANGE2_EXACT_PROOF.md, original logs and new acceptance record.

## Current closure audit: all-mass range two

The preceding scope qualification about root uniqueness and cardinality is superseded by the accepted `RangeTwoClosure.lean`. The complete statement and resource lower bound are shown below. The operator definitions remain those of the original `BathFamily` and `optimalEntropy`. For every positive real m, the strict bracket has exactly one root; the theorem links any such root to the exact physical optimum and an attained bath. It does not replace the physical quantifiers by a fixed number of channels or a finite frequency grid. `range2_every_optimum_resources` applies to arbitrary admissible finite families, including equal temperatures and zero rows. The general SDP coordinate representation and compactness argument remain analytic, and higher-range physical attainment is not established.

```lean
theorem range2_complete (m : ℝ) (hm : 0<m) :
    ∃! e : ℝ, (m+2)/4<e ∧ e<(3*(m+2)-2)/8 ∧ range2N (m+2) e=0 ∧
      optimalEntropy 2 m=range2Value (m+2) e ∧
      (∃ b : BathFamily, Fintype.card b.ι=3 ∧ b.admissible 2 m ∧
        b.cost 2 m=optimalEntropy 2 m ∧ b.temperaturePalette 3 ∧ ¬b.temperaturePalette 2)

theorem range2_every_optimum_resources (m : ℝ) (hm : 0<m) (b : BathFamily)
    (hb : b.admissible 2 m) (hc : b.cost 2 m=optimalEntropy 2 m) :
    3≤Fintype.card b.ι ∧ ¬b.temperaturePalette 2
```

The new module was compiled in development and in an empty extension directory against previously rebuilt dependencies. The 45 staged source hashes match the active source bytes. Six new axiom audits, 87 in total; all six are `[propext, Classical.choice, Quot.sound]`. The 10 Bernstein groups are an independent symbolic sign check, not an independent human review. No finite-case count was increased. Source and log evidence, failed initial transfer, and Windows/Linux JSON comparisons are preserved.
