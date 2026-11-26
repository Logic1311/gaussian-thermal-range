import RealFactorBase

namespace GaussianRange
open Finset Polynomial
noncomputable section

def cosPoly : ℕ → ℝ[X]
  | 0 => 1
  | 1 => X
  | n+2 => C 2*X*cosPoly (n+1)-cosPoly n

theorem cosPoly_degree (j : ℕ) : (cosPoly j).natDegree≤j := by
  induction j using Nat.twoStepInduction with
  | zero => simp [cosPoly]
  | one => simp [cosPoly]
  | more n hn hm =>
    rw [cosPoly]
    apply (natDegree_sub_le _ _).trans
    apply max_le
    · apply natDegree_mul_le.trans
      have h : (C (2:ℝ)*X).natDegree≤1 := by
        exact natDegree_mul_le.trans (by simp)
      omega
    · omega

theorem unit_mul_star (z : ℂ) (hz : ‖z‖=1) : z*star z=1 := by
  change z*(starRingEnd ℂ) z=1
  rw [Complex.mul_conj,Complex.normSq_eq_norm_sq,hz]
  norm_num

theorem unit_star_inv (z : ℂ) (hz : ‖z‖=1) : star z=z⁻¹ := by
  have h := unit_mul_star z hz
  have h0 : z≠0 := by intro e; rw [e,norm_zero] at hz; norm_num at hz
  calc
    star z = z⁻¹*(z*star z) := by rw [← mul_assoc,inv_mul_cancel₀ h0,one_mul]
    _ = z⁻¹ := by rw [h,mul_one]

theorem unit_quadratic_eq (z : ℂ) (hz : ‖z‖=1) : z^2-2*(z.re:ℂ)*z+1=0 := by
  have h := unit_mul_star z hz
  have e : z+star z=2*(z.re:ℂ) := by
    apply Complex.ext <;> simp [Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im] <;> ring
  linear_combination z*e-h

theorem cosPoly_eval_unit (j : ℕ) (z : ℂ) (hz : ‖z‖=1) :
    (cosPoly j).eval z.re=(z^j).re := by
  induction j using Nat.twoStepInduction with
  | zero => simp [cosPoly]
  | one => simp [cosPoly]
  | more n hn hm =>
    have h : z^(n+2)=2*(z.re:ℂ)*z^(n+1)-z^n := by
      rw [pow_add z n 2,pow_add z n 1,pow_one]
      linear_combination z^n*(unit_quadratic_eq z hz)
    have he := congrArg Complex.re h
    rw [show (2:ℂ)*(z.re:ℂ)=((2*z.re:ℝ):ℂ) by push_cast; ring] at he
    simp only [Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      zero_mul,sub_zero] at he
    rw [cosPoly,eval_sub,eval_mul,eval_mul,eval_C,eval_X,hm,hn]
    exact he.symm

def trigRate (r : ℕ) (a b : ℕ → ℝ) (z : ℂ) : ℝ :=
  ∑ j ∈ range (r+1), (a j*(z^j).re+b j*(z^j).im)

def evenRatePoly (r : ℕ) (a : ℕ → ℝ) : ℝ[X] :=
  ∑ j ∈ range (r+1), C (a j)*cosPoly j

theorem evenRatePoly_degree (r : ℕ) (a : ℕ → ℝ) : (evenRatePoly r a).natDegree≤r := by
  unfold evenRatePoly
  apply natDegree_sum_le_of_forall_le
  intro j hj
  have hj' := Finset.mem_range.mp hj
  exact (natDegree_mul_le.trans (by rw [natDegree_C,zero_add]; have := cosPoly_degree j; omega))

theorem evenRatePoly_eval (r : ℕ) (a : ℕ → ℝ) (z : ℂ) (hz : ‖z‖=1) :
    (evenRatePoly r a).eval z.re=∑ j ∈ range (r+1),a j*(z^j).re := by
  simp [evenRatePoly,eval_finset_sum,cosPoly_eval_unit _ z hz]

theorem trigRate_cont (r : ℕ) (a b : ℕ → ℝ) : Continuous (trigRate r a b) := by
  unfold trigRate
  apply continuous_finset_sum
  intro j hj
  fun_prop

theorem trigRate_sym (r : ℕ) (a b : ℕ → ℝ) (z : ℂ) (hz : ‖z‖=1) :
    (trigRate r a b z+trigRate r a b (star z))/2=(evenRatePoly r a).eval z.re := by
  rw [evenRatePoly_eval r a z hz]
  unfold trigRate
  rw [← Finset.sum_add_distrib,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← star_pow]
  change (a j*(z^j).re+b j*(z^j).im+(a j*((starRingEnd ℂ) (z^j)).re+b j*((starRingEnd ℂ) (z^j)).im))/2=a j*(z^j).re
  rw [Complex.conj_re,Complex.conj_im]
  ring

theorem unit_re_mem (z : ℂ) (hz : ‖z‖=1) : -1≤z.re ∧ z.re≤1 := by
  have h := Complex.abs_re_le_norm z
  rw [hz] at h
  exact abs_le.mp h

theorem interval_point_unit (x : ℝ) (h₁ : -1≤x) (h₂ : x≤1) :
    ∃ z : ℂ, ‖z‖=1 ∧ z.re=x := by
  let z : ℂ := ⟨x,Real.sqrt (1-x^2)⟩
  have h : 0≤1-x^2 := by nlinarith [mul_nonneg (by linarith : 0≤1-x) (by linarith : 0≤1+x)]
  have he : ‖z‖^2=1 := by
    rw [← Complex.normSq_eq_norm_sq,Complex.normSq_apply]
    change x*x+Real.sqrt (1-x^2)*Real.sqrt (1-x^2)=1
    nlinarith [Real.sq_sqrt h]
  exact ⟨z,by nlinarith [norm_nonneg z],rfl⟩

theorem avg_star (f : ℂ → ℝ) : avg (fun z => f (star z))=avg f := by
  unfold avg
  rw [← Real.circleAverage_zero_one_congr_inv (f := f)]
  apply Real.circleAverage_congr_sphere
  intro z hz
  change f (star z)=f z⁻¹
  rw [unit_star_inv z (norm_unit_of_mem z hz)]

theorem avg_sym (f : ℂ → ℝ) (hf : Continuous f) :
    avg (fun z => (f z+f (star z))/2)=avg f := by
  have hstar : Continuous (fun z : ℂ => f (star z)) := hf.comp continuous_star
  unfold avg
  simp_rw [div_eq_mul_inv,mul_comm _ (2:ℝ)⁻¹]
  rw [show Real.circleAverage (fun z : ℂ => (2:ℝ)⁻¹*(f z+f (star z))) 0 1 =
      (2:ℝ)⁻¹*Real.circleAverage (fun z => f z+f (star z)) 0 1 from Real.circleAverage_fun_smul (a := (2:ℝ)⁻¹),
    Real.circleAverage_fun_add (hf.continuousOn.circleIntegrable (by norm_num))
      (hstar.continuousOn.circleIntegrable (by norm_num))]
  rw [show Real.circleAverage (fun z : ℂ => f (star z)) 0 1=Real.circleAverage f 0 1 from avg_star f]
  ring

theorem unit_pair_re (z : ℂ) (hz : ‖z‖=1) (i j : ℕ) :
    (z^i*star (z^j)).re=(z^(if i≤j then j-i else i-j)).re := by
  have h := unit_mul_star z hz
  have hpow (n : ℕ) : z^n*star (z^n)=1 := by
    rw [star_pow,← mul_pow,h,one_pow]
  by_cases he : i≤j
  · have hp : j-i+i=j := by omega
    rw [if_pos he]
    have hh : z^i*star (z^j)=star (z^(j-i)) := by
      calc
        _ = z^i*star (z^(j-i+i)) := by rw [hp]
        _ = _ := by rw [pow_add,star_mul,← mul_assoc,hpow,one_mul]
    rw [hh]
    exact Complex.conj_re _
  · have hp : i-j+j=i := by omega
    rw [if_neg he]
    have hh : z^i*star (z^j)=z^(i-j) := by
      calc
        _ = z^(i-j+j)*star (z^j) := by rw [hp]
        _ = _ := by rw [pow_add,mul_assoc,hpow,mul_one]
    rw [hh]

def lagCoeff (r : ℕ) (a : ℕ → ℝ) (d : ℕ) : ℝ :=
  ∑ i ∈ range (r+1),∑ j ∈ range (r+1),
    if (if i≤j then j-i else i-j)=d then a i*a j else 0

theorem weight_pair_sum (r : ℕ) (a : ℕ → ℝ) (z : ℂ) :
    weight r a z=∑ i ∈ range (r+1),∑ j ∈ range (r+1),a i*a j*(z^i*star (z^j)).re := by
  have he : weight r a z=(((amp r a).eval z)*(starRingEnd ℂ) ((amp r a).eval z)).re := by
    unfold weight
    change ‖(amp r a).eval z‖^2=(((amp r a).eval z)*(starRingEnd ℂ) ((amp r a).eval z)).re
    rw [Complex.mul_conj,Complex.ofReal_re,Complex.normSq_eq_norm_sq]
  rw [he,amp_eval]
  change ((∑ j ∈ range (r+1),(a j:ℂ)*z^j)*(starRingEnd ℂ) (∑ j ∈ range (r+1),(a j:ℂ)*z^j)).re=_
  simp only [map_sum,map_mul,Complex.conj_ofReal,mul_sum,sum_mul]
  change Complex.reAddGroupHom (∑ j ∈ range (r+1), ∑ i ∈ range (r+1), (a i:ℂ)*z^i*((a j:ℂ)*(starRingEnd ℂ) (z^j))) = _
  simp only [map_sum,Complex.coe_reAddGroupHom]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  simp [Complex.mul_re,Complex.mul_im,Complex.star_def,Complex.conj_re,Complex.conj_im]
  ring

theorem physical_weight_trig (r : ℕ) (a : ℕ → ℝ) (z : ℂ) (hz : ‖z‖=1) :
    weight r a z=trigRate r (lagCoeff r a) (fun _ => 0) z := by
  rw [weight_pair_sum]
  simp_rw [unit_pair_re z hz]
  unfold trigRate lagCoeff
  simp only [zero_mul,add_zero]
  calc
    _ = ∑ i ∈ range (r+1),∑ j ∈ range (r+1),∑ d ∈ range (r+1),
        if (if i≤j then j-i else i-j)=d then a i*a j*(z^d).re else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      have h : (if i≤j then j-i else i-j) ∈ range (r+1) := by
        simp only [mem_range] at *
        split_ifs <;> omega
      rw [Finset.sum_ite_eq,if_pos h]
    _ = ∑ i ∈ range (r+1),∑ d ∈ range (r+1),∑ j ∈ range (r+1),
        if (if i≤j then j-i else i-j)=d then a i*a j*(z^d).re else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_comm
    _ = ∑ d ∈ range (r+1),∑ i ∈ range (r+1),∑ j ∈ range (r+1),
        if (if i≤j then j-i else i-j)=d then a i*a j*(z^d).re else 0 := Finset.sum_comm
    _ = _ := by
      simp_rw [Finset.sum_mul,ite_mul,zero_mul]

end
end GaussianRange
#print axioms GaussianRange.cosPoly_eval_unit
#print axioms GaussianRange.trigRate_sym
#print axioms GaussianRange.avg_sym
#print axioms GaussianRange.physical_weight_trig