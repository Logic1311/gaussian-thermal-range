import SDPRealization
import SDPReference

namespace GaussianRange
open Finset
open scoped RealInnerProductSpace
noncomputable section

def mixSDP {r : ℕ} (p q : SDPMoments r) (t : ℝ) : SDPMoments r :=
  ⟨(1-t) • p.G+t • q.G,(1-t) • p.H+t • q.H,(1-t) • p.J+t • q.J⟩

theorem sdpInner_mix {n : ℕ} (A B : SDPOp n) (t : ℝ) (x y : SDPSpace n) :
    ⟪x,((1-t) • A+t • B) y⟫=(1-t)*⟪x,A y⟫+t*⟪x,B y⟫ := by
  simp only [LinearMap.add_apply,LinearMap.smul_apply,inner_add_right,real_inner_smul_right]

theorem sdpSpectrum_mix (r : ℕ) (A B : SDPOp (r+1)) (t : ℝ) (z : ℂ) :
    sdpSpectrum r ((1-t) • A+t • B) z =
      (1-t)*sdpSpectrum r A z+t*sdpSpectrum r B z := by
  unfold sdpSpectrum
  rw [sdpInner_mix,sdpInner_mix]
  ring

theorem sdpH_nonneg {r : ℕ} {p : SDPMoments r} {m : ℝ} (hp : SDPFeasible p m)
    (x : SDPSpace (r+1)) : 0≤⟪x,p.H x⟫ := by
  simpa using hp.block x 0

theorem mixSDP_feasible {r : ℕ} {p q : SDPMoments r} {m : ℝ}
    (hp : SDPFeasible p m) (hq : SDPFeasible q m) (t : ℝ) (ht : 0≤t) (ht1 : t≤1) :
    SDPFeasible (mixSDP p q t) m := by
  have h1 : 0≤1-t := by linarith
  refine ⟨(hp.gs.smul (by simp)).add (hq.gs.smul (by simp)),
    (hp.hs.smul (by simp)).add (hq.hs.smul (by simp)),
    (hp.js.smul (by simp)).add (hq.js.smul (by simp)),?_,?_,?_,?_⟩
  · intro x
    change 0≤⟪x,((1-t) • p.G+t • q.G) x⟫
    rw [sdpInner_mix]
    exact add_nonneg (mul_nonneg h1 (hp.gn x)) (mul_nonneg ht (hq.gn x))
  · intro x y
    change 0≤⟪x,((1-t) • p.H+t • q.H) x⟫+
      2*⟪x,((1-t) • p.G+t • q.G) y⟫+
      ⟪y,((1-t) • p.J+t • q.J) y⟫
    rw [sdpInner_mix,sdpInner_mix,sdpInner_mix]
    have h := add_nonneg (mul_nonneg h1 (hp.block x y)) (mul_nonneg ht (hq.block x y))
    linarith only [h]
  · intro z hz
    change sdpSpectrum r ((1-t) • p.G+t • q.G) z=1
    rw [sdpSpectrum_mix,hp.normalization z hz,hq.normalization z hz]
    ring
  · intro z hz
    change sdpSpectrum r ((1-t) • p.H+t • q.H) z=_
    rw [sdpSpectrum_mix,hp.weighted z hz,hq.weighted z hz]
    ring

theorem mixSDP_positive {n : ℕ} (A B : SDPOp n) (hA : ∀ x,0≤⟪x,A x⟫)
    (hB : sdpPositive B) (t : ℝ) (ht : 0<t) (ht1 : t≤1) :
    sdpPositive ((1-t) • A+t • B) := by
  intro x hx
  rw [sdpInner_mix]
  have h1 : 0≤(1-t)*⟪x,A x⟫ := mul_nonneg (by linarith) (hA x)
  have h2 : 0<t*⟪x,B x⟫ := mul_pos ht (hB x hx)
  linarith

theorem sdpSigma_mix {r : ℕ} (p q : SDPMoments r) (m t : ℝ) (z : ℂ) :
    sdpSigma (mixSDP p q t) m z=(1-t)*sdpSigma p m z+t*sdpSigma q m z := by
  unfold sdpSigma mixSDP
  rw [sdpSpectrum_mix]
  ring

theorem sdpCost_mix {r : ℕ} (p q : SDPMoments r) (m t : ℝ) :
    sdpCost (mixSDP p q t) m=(1-t)*sdpCost p m+t*sdpCost q m := by
  unfold sdpCost
  have he : sdpSigma (mixSDP p q t) m =
      fun z => (1-t)*sdpSigma p m z+t*sdpSigma q m z := funext (sdpSigma_mix p q m t)
  rw [he]
  unfold avg
  have hp : Continuous (fun z : ℂ => (1-t)*sdpSigma p m z) :=
    continuous_const.mul (sdpSigma_cont p m)
  have hq : Continuous (fun z : ℂ => t*sdpSigma q m z) :=
    continuous_const.mul (sdpSigma_cont q m)
  rw [Real.circleAverage_fun_add (hp.continuousOn.circleIntegrable (by norm_num))
    (hq.continuousOn.circleIntegrable (by norm_num))]
  have h₁ : Real.circleAverage (fun z => (1-t)*sdpSigma p m z) 0 1 =
      (1-t)*Real.circleAverage (sdpSigma p m) 0 1 :=
    Real.circleAverage_fun_smul (a:=1-t)
  have h₂ : Real.circleAverage (fun z => t*sdpSigma q m z) 0 1 =
      t*Real.circleAverage (sdpSigma q m) 0 1 :=
    Real.circleAverage_fun_smul (a:=t)
  rw [h₁,h₂]

/-- Recovery for every closed-cone feasible point: arbitrary positive tolerance,
with at most r+1 genuine positive-temperature real FIR channels. -/
theorem sdp_recover_approx (r : ℕ) (hr : 0<r) (m : ℝ) (hm : 0<m)
    (p : SDPMoments r) (hp : SDPFeasible p m) (ε : ℝ) (hε : 0<ε) :
    ∃ b : BathFamily, Fintype.card b.ι≤r+1 ∧ b.admissible r m ∧
      b.cost r m≤sdpCost p m+ε := by
  obtain ⟨q,hq,hqG,hqH⟩ := reference_sdp r hr m hm
  let d := sdpCost q m-sdpCost p m
  let t := ε/(ε+|d|+1)
  have hden : 0<ε+|d|+1 := by linarith [abs_nonneg d]
  have ht : 0<t := div_pos hε hden
  have ht1 : t≤1 := by
    dsimp [t]
    apply (div_le_iff₀ hden).2
    linarith [abs_nonneg d]
  have htd : t*|d|≤ε := by
    dsimp [t]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hden).2
    nlinarith [sq_nonneg ε]
  let a := mixSDP p q t
  have ha : SDPFeasible a m := mixSDP_feasible hp hq t ht.le ht1
  have haG : sdpPositive a.G := mixSDP_positive p.G q.G hp.gn hqG t ht ht1
  have haH : sdpPositive a.H := mixSDP_positive p.H q.H (sdpH_nonneg hp) hqH t ht ht1
  obtain ⟨b,hcard,hb,hσ⟩ := sdpRealization a m hm ha haG haH
  have hcost : b.cost r m≤sdpCost a m := by
    rw [← bathMoments_cost]
    apply sdpCost_mono
    intro z hz
    rw [bathMoments_sigma]
    exact hσ z hz
  refine ⟨b,hcard,hb,hcost.trans ?_⟩
  change sdpCost (mixSDP p q t) m≤sdpCost p m+ε
  rw [sdpCost_mix]
  have hle : t*d≤t*|d| := mul_le_mul_of_nonneg_left (le_abs_self d) ht.le
  dsimp [d] at hle
  linarith only [hle.trans htd]

/-- Equality of the original physical infimum and the closed block-PSD
moment problem; no attainment of the physical infimum is assumed. -/
theorem exact_sdp_infimum (r : ℕ) (hr : 0<r) (m : ℝ) (hm : 0<m) :
    sInf (sdpCosts r m)=optimalEntropy r m := by
  have hn := admissibleCosts_nonempty_all r hr m hm
  have hbd : BddBelow (admissibleCosts r m) :=
    ⟨_,fun x hx => admissible_lower r hr m hm x hx⟩
  apply le_antisymm
  · unfold optimalEntropy
    apply le_csInf hn
    intro x hx
    exact csInf_le (sdpCosts_bddBelow r m hm) (physical_subset_sdp r m hx)
  · apply le_csInf (sdpCosts_nonempty r hr m hm)
    rintro x ⟨p,hp,rfl⟩
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨b,hcard,hb,hcost⟩ := sdp_recover_approx r hr m hm p hp ε hε
    exact (csInf_le hbd ⟨b,hb,rfl⟩).trans hcost

end
end GaussianRange
#check GaussianRange.sdp_recover_approx
#check GaussianRange.exact_sdp_infimum
#print axioms GaussianRange.sdp_recover_approx
#print axioms GaussianRange.exact_sdp_infimum
