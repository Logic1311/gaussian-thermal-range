import CriticalRealization

namespace GaussianRange
open Finset Polynomial
noncomputable section

theorem critical_avg_div (f : ℂ → ℝ) (t : ℝ) :
    avg (fun z => f z/t)=avg f/t := by
  unfold avg
  simp_rw [div_eq_mul_inv,mul_comm _ t⁻¹]
  exact Real.circleAverage_fun_smul (a := t⁻¹)

theorem critical_avg_add_const (f : ℂ → ℝ) (hf : Continuous f) (c : ℝ) :
    avg (fun z => f z+c)=avg f+c := by
  unfold avg
  rw [Real.circleAverage_fun_add (hf.continuousOn.circleIntegrable (by norm_num))
    (continuous_const.continuousOn.circleIntegrable (by norm_num))]
  rw [Real.circleAverage_const]

theorem critical_family_lower (b : BathFamily) (r : ℕ) (m : ℝ) (hm : 0<m)
    (hb : b.admissible r m) : criticalConst r/m-1≤b.cost r m := by
  let f (v : b.ι) (z : ℂ) := dispersion 2 z*weight r (b.coeff v) z/b.temp v
  have hf (v : b.ι) : Continuous (f v) := by
    exact ((cont_dispersion 2).mul (cont_weight r (b.coeff v))).div_const _
  have hfs : Continuous (fun z : ℂ => ∑ v, f v z) :=
    continuous_finset_sum _ (fun v _ => hf v)
  have hsum : avg (fun z => ∑ v, f v z)=
      ∑ v, avg (fun z => dispersion 2 z*weight r (b.coeff v) z)/b.temp v := by
    unfold avg
    rw [Real.circleAverage_fun_sum (fun v _ => (hf v).continuousOn.circleIntegrable (by norm_num))]
    apply sum_congr rfl
    intro v hv
    exact critical_avg_div (fun z => dispersion 2 z*weight r (b.coeff v) z) (b.temp v)
  have hmean : avg (fun z => ∑ v, f v z)≤b.cost r m+1 := by
    calc
      _ ≤ avg (fun z => sigma r b.coeff b.temp (m+2) z+1) := by
        unfold avg
        apply Real.circleAverage_mono (hfs.continuousOn.circleIntegrable (by norm_num))
          (((cont_sigma r b.coeff b.temp (m+2)).add continuous_const).continuousOn.circleIntegrable (by norm_num))
        intro z hz
        have hD : dispersion 2 z≤dispersion (m+2) z := by unfold dispersion; linarith
        have hnon : 0≤∑ v, weight r (b.coeff v) z/b.temp v :=
          sum_nonneg (fun v _ => div_nonneg (sq_nonneg _) (hb.1 v).le)
        have he : (∑ v, f v z)=dispersion 2 z*(∑ v, weight r (b.coeff v) z/b.temp v) := by
          simp only [f,mul_div_assoc,← mul_sum]
        rw [he]
        change dispersion 2 z*(∑ v, weight r (b.coeff v) z/b.temp v) ≤
          dispersion (m+2) z*(∑ v, weight r (b.coeff v) z/b.temp v)-1+1
        linarith [mul_le_mul_of_nonneg_right hD hnon]
      _ = _ := critical_avg_add_const _ (cont_sigma r b.coeff b.temp (m+2)) 1
  have hE : criticalConst r*(∑ v, weight r (b.coeff v) 1/b.temp v)≤avg (fun z => ∑ v, f v z) := by
    rw [hsum,mul_sum]
    apply sum_le_sum
    intro v hv
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (critical_energy_lower r (b.coeff v)) (hb.1 v).le
  have hd : dispersion (m+2) (1:ℂ)=m := by simp [dispersion]
  have hσ : 0≤sigma r b.coeff b.temp (m+2) (1:ℂ) := by
    rw [BathFamily.sigma_identity b r m hm hb 1 (by norm_num),hd]
    exact sum_nonneg (fun v _ => div_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (mul_pos (hb.1 v) hm).le)
  unfold sigma at hσ
  rw [hd] at hσ
  have hinv : 1/m≤∑ v, weight r (b.coeff v) 1/b.temp v :=
    (div_le_iff₀ hm).2 (by linarith)
  have hmul := mul_le_mul_of_nonneg_left hinv (criticalConst_pos r).le
  rw [show criticalConst r*(1/m)=criticalConst r/m by ring] at hmul
  linarith [hmul.trans (hE.trans hmean)]

theorem critical_realization_upper (r : ℕ) (hr : 0<r) (m : ℝ) (hm : 0<m) :
    ∃ b : BathFamily, b.admissible r m ∧ Fintype.card b.ι=3 ∧
      b.cost r m≤criticalConst r/m+4/criticalA r := by
  obtain ⟨b,hb,hcard,he⟩ := critical_realization r hr m hm
  have hA := criticalA_pos r
  have hAB := criticalA_lt_B r hr
  have hma : 0<m+criticalA r := by linarith
  have hmb : 0<m+criticalB r := by linarith
  have ha4 : criticalA r≤4 := by
    unfold criticalA
    apply (div_le_iff₀ (by positivity : 0<((r:ℝ)+1)^2)).2
    have hn : 0≤(r:ℝ) := by positivity
    nlinarith [sq_nonneg (r:ℝ)]
  let f : ℂ → ℝ := fun z => dispersion 2 z*weight r (criticalCoeff r) z/m
  have hf : Continuous f := ((cont_dispersion 2).mul (cont_weight r _)).div_const _
  have hp (z : ℂ) (hz : ‖z‖=1) : sigma r b.coeff b.temp (m+2) z≤f z+4/criticalA r := by
    have hR := criticalResidual_nonneg r z hz
    have hw : 0≤weight r (criticalCoeff r) z := sq_nonneg _
    have hw1 : weight r (criticalCoeff r) z≤1 := by unfold criticalResidual at hR; linarith
    have hr1 : criticalResidual r z≤1 := by unfold criticalResidual; linarith
    have hhot : criticalHotRate r false z/(m+criticalA r)+criticalHotRate r true z/(m+criticalB r)≤1/(m+criticalA r) := by
      calc
        _ ≤ criticalHotRate r false z/(m+criticalA r)+criticalHotRate r true z/(m+criticalA r) := by
          apply add_le_add le_rfl
          exact div_le_div_of_nonneg_left (criticalHotRate_nonneg r hr true z hz) hma (by linarith)
        _ = criticalResidual r z/(m+criticalA r) := by rw [← add_div,criticalHotRate_sum r hr z]
        _ ≤ _ := div_le_div_of_nonneg_right hr1 hma.le
    obtain ⟨hlo,hhi⟩ := unit_re_mem z hz
    have hD : 0≤dispersion (m+2) z := by unfold dispersion; linarith
    have hDmax : dispersion (m+2) z≤m+4 := by unfold dispersion; linarith
    have hcap : dispersion (m+2) z/(m+criticalA r)≤4/criticalA r := by
      apply (div_le_div_iff₀ hma hA).2
      have hh := mul_le_mul_of_nonneg_right hDmax hA.le
      nlinarith [mul_nonneg hm.le (sub_nonneg.mpr ha4)]
    rw [he z hz]
    have hh := mul_le_mul_of_nonneg_left (add_le_add (le_refl (weight r (criticalCoeff r) z/m)) hhot) hD
    have hsum : dispersion (m+2) z*(weight r (criticalCoeff r) z/m+1/(m+criticalA r))-1 =
        f z+weight r (criticalCoeff r) z+dispersion (m+2) z/(m+criticalA r)-1 := by
      dsimp [f,dispersion]
      field_simp [hm.ne',hma.ne']
      <;> ring
    have hle : dispersion (m+2) z*(weight r (criticalCoeff r) z/m+
        criticalHotRate r false z/(m+criticalA r)+criticalHotRate r true z/(m+criticalB r))-1 ≤
        dispersion (m+2) z*(weight r (criticalCoeff r) z/m+1/(m+criticalA r))-1 := by
      convert sub_le_sub_right hh 1 using 1 <;> ring
    rw [hsum] at hle
    linarith
  refine ⟨b,hb,hcard,?_⟩
  have hmean : b.cost r m≤avg (fun z => f z+4/criticalA r) := by
    unfold BathFamily.cost avg
    apply Real.circleAverage_mono ((cont_sigma r b.coeff b.temp (m+2)).continuousOn.circleIntegrable (by norm_num))
      ((hf.add continuous_const).continuousOn.circleIntegrable (by norm_num))
    intro z hz
    exact hp z (norm_unit_of_mem z hz)
  rw [critical_avg_add_const f hf,show avg f=criticalConst r/m by
    dsimp [f]; rw [critical_avg_div,critical_cold_energy]] at hmean
  exact hmean

theorem critical_infimum_bounds (r : ℕ) (hr : 0<r) (m : ℝ) (hm : 0<m) :
    criticalConst r/m-1≤optimalEntropy r m ∧
      optimalEntropy r m≤criticalConst r/m+4*((r:ℝ)+1)^2 := by
  have hn := admissibleCosts_nonempty_all r hr m hm
  have hl : ∀ x ∈ admissibleCosts r m, criticalConst r/m-1≤x := by
    rintro x ⟨b,hb,rfl⟩
    exact critical_family_lower b r m hm hb
  have hbd : BddBelow (admissibleCosts r m) := ⟨_,hl⟩
  constructor
  · exact le_csInf hn hl
  · obtain ⟨b,hb,hcard,hbnd⟩ := critical_realization_upper r hr m hm
    have hu := (csInf_le hbd (show b.cost r m∈admissibleCosts r m from ⟨b,hb,rfl⟩)).trans hbnd
    have he : 4/criticalA r=4*((r:ℝ)+1)^2 := by unfold criticalA; rw [div_div_eq_mul_div]; norm_num
    rw [he] at hu
    exact hu

theorem critical_infimum_squeeze (r : ℕ) (hr : 0<r) (m : ℝ) (hm : 0<m) :
    criticalConst r-m≤m*optimalEntropy r m ∧
      m*optimalEntropy r m≤criticalConst r+4*m*((r:ℝ)+1)^2 := by
  obtain ⟨hl,hu⟩ := critical_infimum_bounds r hr m hm
  constructor
  · have h := mul_le_mul_of_nonneg_left hl hm.le
    convert h using 1
    field_simp [hm.ne'] <;> ring
  · have h := mul_le_mul_of_nonneg_left hu hm.le
    convert h using 1
    field_simp [hm.ne'] <;> ring

end
end GaussianRange
#print axioms GaussianRange.critical_family_lower
#print axioms GaussianRange.critical_realization_upper
#print axioms GaussianRange.critical_infimum_bounds
#print axioms GaussianRange.critical_infimum_squeeze
