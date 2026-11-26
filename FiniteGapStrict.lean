import FiniteGapBound

namespace GaussianRange
open Finset Polynomial
noncomputable section

theorem denominator_endpoint_lower (p : ℕ) (hp : 0<p) (t : ℝ) :
    (t^p-1)^2≤realSq (forwardPower p t)-((p:ℝ)+1)*t^p := by
  let f : Fin (p+1) → ℝ := fun i => (forwardPower p t i-reversePower p t i)^2
  have hne : (0:Fin (p+1))≠Fin.last p := by
    intro h
    have e := congrArg Fin.val h
    simp at e
    omega
  have h₀ : f 0=(1-t^p)^2 := by simp [f,forwardPower,reversePower]
  have h₁ : f (Fin.last p)=(t^p-1)^2 := by simp [f,forwardPower,reversePower]
  have hsum : f 0+f (Fin.last p) ≤ ∑ i,f i := by
    have h : (∑ i ∈ ({0,Fin.last p}:Finset (Fin (p+1))), f i) ≤ ∑ i,f i :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _=>sq_nonneg _)
    simpa [Finset.sum_insert,hne] using h
  have he : (∑ i,f i)=2*(realSq (forwardPower p t)-((p:ℝ)+1)*t^p) := by
    change realSq (fun i=>forwardPower p t i-reversePower p t i)=_
    rw [realSq_diff,← power_norm_eq p t,power_dot]
    ring
  rw [h₀,h₁,he] at hsum
  nlinarith

theorem strict_relaxed_height (r : ℕ) (hr : 2≤r) (m : ℝ) (hm : 0<m) :
    gapHeight m*relaxedEntropy r m<1/2 := by
  obtain ⟨t,ht,hc⟩ := dispersion_root_exists m hm
  rw [relaxedEntropy_eq r m t ht hc]
  let p := r+1
  let den := realSq (forwardPower p t)-((p:ℝ)+1)*t^p
  have ht0 : 0<t := by linarith
  have ht2 : 1<t^2 := one_lt_pow₀ ht (by norm_num)
  have hp : 2<p := by dsimp [p]; omega
  have hpt : t^2<t^p := pow_lt_pow_right₀ ht hp
  have htp : 0<t^p := pow_pos ht0 _
  have hxy : 0<(t^p-t^2)*(t^p*t^2-1) := by
    apply mul_pos (sub_pos.mpr hpt)
    nlinarith [mul_pos (sub_pos.mpr ht2) (sub_pos.mpr (ht2.trans hpt))]
  have hcompare : (t^2-1)^2*t^p<(t^p-1)^2*t^2 := by nlinarith only [hxy]
  have hmul : (m+2)*t=t^2+1 := by rw [hc]; field_simp <;> ring
  have hsq := congrArg (fun x : ℝ=>x^2) hmul
  have hheight : (t^2-1)^2=4*gapHeight m*t^2 := by
    unfold gapHeight
    nlinarith only [hsq]
  rw [hheight] at hcompare
  have hcomparison : 4*gapHeight m*t^p<(t^p-1)^2 := by
    have h := (mul_lt_mul_iff_left₀ (sq_pos_of_pos ht0)).mp
      (show (4*gapHeight m*t^p)*t^2<(t^p-1)^2*t^2 by nlinarith only [hcompare])
    exact h
  have hden : 0<den := relaxed_denominator_pos p (by omega) t ht
  have hlow : (t^p-1)^2≤den := denominator_endpoint_lower p (by omega) t
  change gapHeight m*(2*t^p/den)<1/2
  rw [← mul_div_assoc]
  exact (div_lt_iff₀ hden).2 (by linarith)

theorem strict_finite_range_gap (r : ℕ) (hr : 2≤r) (m : ℝ) (hm : 0<m) :
    relaxedEntropy r m<optimalEntropy r m := by
  have h := finite_range_gap_bound r (by omega) m hm
  have hd := barrierDelta_pos r (by omega) m hm
  have hg := strict_relaxed_height r hr m hm
  have hp := mul_pos hd (sub_pos.mpr hg)
  linarith

theorem relaxed_nearest_exact (m : ℝ) (hm : 0<m) :
    relaxedEntropy 1 m=2/(m*(m+4)) := by
  obtain ⟨t,ht,hc⟩ := dispersion_root_exists m hm
  rw [relaxedEntropy_eq 1 m t ht hc]
  have ht0 : 0<t := by linarith
  have hmul : (m+2)*t=t^2+1 := by rw [hc]; field_simp <;> ring
  have hsq := congrArg (fun x : ℝ=>x^2) hmul
  have he : (t^2-1)^2=m*(m+4)*t^2 := by nlinarith only [hsq]
  unfold algebraicRelaxedValue realSq forwardPower
  norm_num [Fin.sum_univ_succ]
  have hden : t^4+t^2+1-3*t^2=(t^2-1)^2 := by ring
  have hm0 : m*(m+4)≠0 := by positivity
  have ht2 : t^2≠0 := by positivity
  have h : 1+(t^2+(t^2)^2)-3*t^2=m*(m+4)*t^2 := by nlinarith only [he]
  rw [h]
  field_simp
  <;> ring

theorem nearest_sigma_exact (r : ℕ) (hr : 0<r) (m : ℝ) (hm : 0<m)
    (z : ℂ) (hz : ‖z‖=1) :
    sigma r (nearestBath m).coeff (nearestBath m).temp (m+2) z =
      4*z.im^2/(m*(m+4)) := by
  unfold sigma
  change dispersion (m+2) z*(∑ v : Bool,weight r (nearestCoeff v) z/(if v then m else m+4))-1=_
  rw [Fintype.sum_bool,nearest_weight r hr false z hz,nearest_weight r hr true z hz]
  simp only [Bool.false_eq_true,if_false,if_true]
  unfold dispersion
  have h := unit_re_sq_im_sq z hz
  have hm4 : m+4≠0 := by positivity
  field_simp [hm.ne',hm4]
  nlinarith only [h]

theorem nearest_cost_exact (r : ℕ) (hr : 0<r) (m : ℝ) (hm : 0<m) :
    (nearestBath m).cost r m=2/(m*(m+4)) := by
  unfold BathFamily.cost
  have hcont : Continuous (fun z : ℂ=>4*z.im^2/(m*(m+4))) := by fun_prop
  rw [avg_congr_unit _ (fun z : ℂ=>4*z.im^2/(m*(m+4))) (cont_sigma r _ _ _) hcont
    (nearest_sigma_exact r hr m hm)]
  unfold avg
  have he : (fun z : ℂ=>4*z.im^2/(m*(m+4)))=(fun z : ℂ=>(4/(m*(m+4)))*z.im^2) := by
    funext z; ring
  rw [he,show Real.circleAverage (fun z : ℂ=>(4/(m*(m+4)))*z.im^2) 0 1=
    (4/(m*(m+4)))*avg (fun z : ℂ=>z.im^2) from Real.circleAverage_fun_smul (a:=4/(m*(m+4)))]
  rw [avg_im_square]
  ring

theorem nearest_gap_zero (m : ℝ) (hm : 0<m) :
    optimalEntropy 1 m=relaxedEntropy 1 m := by
  have hlo : relaxedEntropy 1 m≤optimalEntropy 1 m := by
    have h := finite_range_gap_bound 1 (by omega) m hm
    rw [relaxed_nearest_exact m hm] at h ⊢
    have he : gapHeight m*(2/(m*(m+4)))=1/2 := by unfold gapHeight; field_simp; ring
    rw [he,sub_self,mul_zero,add_zero] at h
    exact h
  have hhi : optimalEntropy 1 m≤(nearestBath m).cost 1 m := by
    unfold optimalEntropy
    apply csInf_le
    · exact ⟨_,fun x hx=>admissible_lower 1 (by omega) m hm x hx⟩
    · exact ⟨nearestBath m,nearest_admissible 1 (by omega) m hm,rfl⟩
  rw [nearest_cost_exact 1 (by omega) m hm,← relaxed_nearest_exact m hm] at hhi
  exact le_antisymm hhi hlo

end
end GaussianRange
#print axioms GaussianRange.strict_relaxed_height
#print axioms GaussianRange.strict_finite_range_gap
#print axioms GaussianRange.nearest_cost_exact
#print axioms GaussianRange.nearest_gap_zero