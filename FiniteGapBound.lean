import PointwiseBound

namespace GaussianRange
open Finset Polynomial
noncomputable section

def barrierDelta (r : ℕ) (m : ℝ) : ℝ :=
  1/((m+2)*(m+4)*momentBudget r)

def gapHeight (m : ℝ) : ℝ := m*(m+4)/4

theorem barrierDelta_pos (r : ℕ) (hr : 0<r) (m : ℝ) (hm : 0<m) :
    0<barrierDelta r m := by
  unfold barrierDelta
  have hs : 0<momentBudget r := lt_of_lt_of_le zero_lt_one (momentBudget_ge_one r hr)
  positivity

theorem barrierNormalizer_pos (r : ℕ) (hr : 0<r) (m : ℝ) (hm : 0<m) :
    0<1-barrierDelta r m*gapHeight m := by
  have hs := momentBudget_ge_one r hr
  have hs0 : 0<momentBudget r := by linarith
  have hc : 0<(m+2)*(m+4)*momentBudget r := by positivity
  unfold barrierDelta gapHeight
  apply sub_pos.mpr
  rw [one_div_mul_eq_div]
  apply (div_lt_one hc).2
  nlinarith [mul_nonneg (show 0≤(m+2)*(m+4) by positivity) (show 0≤momentBudget r-1 by linarith)]

theorem physical_constant_barrier (b : BathFamily) (r : ℕ) (hr : 0<r) (m : ℝ) (hm : 0<m)
    (hb : b.admissible r m) (z : ℂ) (hz : ‖z‖=1) :
    barrierDelta r m*z.im^2 ≤ sigma r b.coeff b.temp (m+2) z := by
  have h := physical_pointwise_barrier b r hr m hm hb z hz
  obtain ⟨hzl,hzu⟩ := unit_re_mem z hz
  have hs : 0<momentBudget r := lt_of_lt_of_le zero_lt_one (momentBudget_ge_one r hr)
  have hd : 0<dispersion (m+2) z := by unfold dispersion; linarith
  have hd' : dispersion (m+2) z≤m+4 := by unfold dispersion; linarith
  have hk : 0<(m+2)*momentBudget r := by positivity
  have hden : (m+2)*momentBudget r*dispersion (m+2) z≤(m+2)*momentBudget r*(m+4) :=
    mul_le_mul_of_nonneg_left hd' hk.le
  apply le_trans _ h
  have he : barrierDelta r m*z.im^2=z.im^2/((m+2)*momentBudget r*(m+4)) := by
    unfold barrierDelta
    rw [one_div_mul_eq_div]
    congr 1
    ring
  rw [he]
  exact div_le_div_of_nonneg_left (sq_nonneg _) (mul_pos hk hd) hden

theorem avg_im_square : avg (fun z : ℂ => z.im^2)=1/2 := by
  let a : ℕ → ℝ := fun j => if j=0 then 1/2 else if j=2 then -1/2 else 0
  have he (z : ℂ) (hz : ‖z‖=1) : weight 2 a z=z.im^2 := by
    have ha : (amp 2 a).eval z=(1-z^2)/2 := by
      rw [amp_eval]
      norm_num [a,Finset.sum_range_succ]
      ring
    have hb : (1-z^2)/2 = z*(-Complex.I)*(z.im:ℂ) := by
      have hstar : z*star z=1 := unit_mul_star z hz
      have him : star z-z= -2*Complex.I*(z.im:ℂ) := by
        apply Complex.ext <;> simp [Complex.sub_re,Complex.sub_im,Complex.mul_re,Complex.mul_im] <;> ring
      calc
        _ = z*(star z-z)/2 := by rw [mul_sub,hstar]; ring
        _ = _ := by rw [him]; ring
    unfold weight
    rw [ha,hb,norm_mul,norm_mul,norm_neg,Complex.norm_I,hz,one_mul,one_mul,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  have h := avg_congr_unit (fun z : ℂ => z.im^2) (weight 2 a)
    (Complex.continuous_im.pow 2) (cont_weight 2 a) (fun z hz => (he z hz).symm)
  rw [h,avg_weight_parseval]
  norm_num [Finset.sum_range_succ,a]

def inverseWeightPoly (b : BathFamily) (r : ℕ) : ℝ[X] :=
  evenRatePoly r (fun j => ∑ v, lagCoeff r (b.coeff v) j/b.temp v)

theorem inverseWeightPoly_degree (b : BathFamily) (r : ℕ) :
    (inverseWeightPoly b r).natDegree≤r := evenRatePoly_degree _ _

theorem inverseWeightPoly_eval (b : BathFamily) (r : ℕ) (z : ℂ) (hz : ‖z‖=1) :
    (inverseWeightPoly b r).eval z.re=∑ v, weight r (b.coeff v) z/b.temp v := by
  simp_rw [physical_weight_trig r _ z hz]
  unfold inverseWeightPoly
  rw [evenRatePoly_eval r _ z hz]
  unfold trigRate
  simp only [zero_mul,add_zero]
  simp_rw [Finset.sum_div,Finset.sum_mul,div_mul_eq_mul_div]
  exact Finset.sum_comm

/-- A pointwise barrier can be subtracted while keeping a normalized feasible
scalar majorant, with no enlargement of the polynomial degree. -/
theorem barrier_majorant_lower (b : BathFamily) (r : ℕ) (hr : 0<r) (m : ℝ) (hm : 0<m)
    (hb : b.admissible r m) :
    relaxedEntropy r m+barrierDelta r m*(1/2-gapHeight m*relaxedEntropy r m) ≤ b.cost r m := by
  let c := m+2
  let δ := barrierDelta r m
  let K := 1-δ*gapHeight m
  have hK : 0<K := barrierNormalizer_pos r hr m hm
  let g := C K⁻¹*(inverseWeightPoly b r-C (δ*c/4)-C (δ/2)*X)
  have hgdeg : g.natDegree≤r := by
    unfold g
    apply (natDegree_C_mul_le _ _).trans
    apply (natDegree_sub_le _ _).trans
    apply max_le
    · exact (natDegree_sub_le _ _).trans (max_le (inverseWeightPoly_degree b r) (by simp))
    · exact natDegree_mul_le.trans (by simp; omega)
  have hge (z : ℂ) (hz : ‖z‖=1) :
      dispersion c z*g.eval z.re-1=(sigma r b.coeff b.temp c z-δ*z.im^2)/K := by
    have h := unit_re_sq_im_sq z hz
    unfold g sigma
    simp only [eval_mul,eval_sub,eval_C,eval_X,inverseWeightPoly_eval b r z hz]
    have he : dispersion c z*(c/4+z.re/2)=gapHeight m+z.im^2 := by
      dsimp [c,dispersion,gapHeight]
      nlinarith
    field_simp [hK.ne']
    dsimp [K]
    have he' := congrArg (fun x : ℝ => δ*x) he
    dsimp [c] at he' ⊢
    nlinarith only [he']
  have hg : evenMajorant r c g := by
    refine ⟨hgdeg,?_⟩
    intro z hz
    have he := hge z hz
    have hp := physical_constant_barrier b r hr m hm hb z hz
    change δ*z.im^2≤sigma r b.coeff b.temp c z at hp
    have hnon : 0≤(sigma r b.coeff b.temp c z-δ*z.im^2)/K :=
      div_nonneg (sub_nonneg.mpr hp) hK.le
    linarith
  obtain ⟨t,ht,hct⟩ := dispersion_root_exists m hm
  have hc : c=t+t⁻¹ := hct
  have hgb : evenMajorant r (t+t⁻¹) g := hc ▸ hg
  have hrel := even_majorant_bound r t ht g hgb
  rw [← hc,← relaxedEntropy_eq r m t ht hct] at hrel
  have havg : majorantCost c g=(b.cost r m-δ/2)/K := by
    have hsig := cont_sigma r b.coeff b.temp c
    have him : Continuous (fun z : ℂ => z.im^2) := Complex.continuous_im.pow 2
    have himd : Continuous (fun z : ℂ => δ*z.im^2) := continuous_const.mul him
    unfold majorantCost
    have hcont : Continuous (fun z : ℂ => dispersion c z*g.eval z.re-1) :=
      ((cont_dispersion c).mul (g.continuous.comp Complex.continuous_re)).sub continuous_const
    rw [avg_congr_unit (fun z : ℂ => dispersion c z*g.eval z.re-1)
      (fun z : ℂ => (sigma r b.coeff b.temp c z-δ*z.im^2)/K) hcont
      ((hsig.sub himd).div_const K) hge]
    unfold BathFamily.cost avg
    have he : Real.circleAverage (fun z => (sigma r b.coeff b.temp c z-δ*z.im^2)/K) 0 1 =
        K⁻¹*Real.circleAverage (fun z => sigma r b.coeff b.temp c z-δ*z.im^2) 0 1 := by
      simp_rw [div_eq_mul_inv,mul_comm _ K⁻¹]
      exact Real.circleAverage_fun_smul (a := K⁻¹)
    rw [he,Real.circleAverage_fun_sub (hsig.continuousOn.circleIntegrable (by norm_num))
      (himd.continuousOn.circleIntegrable (by norm_num))]
    have he' : Real.circleAverage (fun z : ℂ => δ*z.im^2) 0 1=δ*avg (fun z : ℂ => z.im^2) :=
      Real.circleAverage_fun_smul (a := δ)
    rw [he',avg_im_square]
    change _=(avg (sigma r b.coeff b.temp c)-δ/2)/K
    unfold avg
    ring
  rw [havg] at hrel
  have he := (le_div_iff₀ hK).1 hrel
  change relaxedEntropy r m+δ*(1/2-gapHeight m*relaxedEntropy r m)≤b.cost r m
  dsimp [K] at he
  nlinarith

theorem finite_range_gap_bound (r : ℕ) (hr : 0<r) (m : ℝ) (hm : 0<m) :
    relaxedEntropy r m+barrierDelta r m*(1/2-gapHeight m*relaxedEntropy r m) ≤ optimalEntropy r m := by
  unfold optimalEntropy
  apply le_csInf (admissibleCosts_nonempty_all r hr m hm)
  rintro x ⟨b,hb,rfl⟩
  exact barrier_majorant_lower b r hr m hm hb

end
end GaussianRange
#print axioms GaussianRange.avg_im_square
#print axioms GaussianRange.barrier_majorant_lower
#print axioms GaussianRange.finite_range_gap_bound