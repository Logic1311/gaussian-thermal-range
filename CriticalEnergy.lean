import FiniteGapStrict

namespace GaussianRange
open Finset Polynomial
noncomputable section

def cutCoeff (r : ℕ) (a : ℕ → ℝ) (j : ℕ) : ℝ :=
  if j ≤ r then a j else 0

def firstDiff (r : ℕ) (a : ℕ → ℝ) (j : ℕ) : ℝ :=
  cutCoeff r a j - (if 1 ≤ j then cutCoeff r a (j-1) else 0)

theorem firstDiff_amp (r : ℕ) (a : ℕ → ℝ) :
    amp (r+1) (firstDiff r a) = (1-X)*amp r a := by
  ext j
  rw [sub_mul,one_mul,coeff_sub,amp_coeff,mul_comm X (amp r a)]
  have hx : (amp r a * X).coeff j = if 1 ≤ j then (amp r a).coeff (j-1) else 0 := by
    simpa only [pow_one] using coeff_mul_X_pow' (amp r a) 1 j
  rw [hx,amp_coeff,amp_coeff]
  unfold firstDiff cutCoeff
  by_cases hj : j≤r+1
  · rw [if_pos hj]
    split_ifs <;> push_cast <;> simp <;> try omega
  · have h₁ : ¬ j≤r := by omega
    have h₂ : ¬ j-1≤r := by omega
    simp [hj,h₁,h₂]

theorem firstDiff_sum (r : ℕ) (a : ℕ → ℝ) :
    (∑ j ∈ range (r+2), firstDiff r a j)=0 := by
  have h : (amp (r+1) (firstDiff r a)).eval 1=0 := by rw [firstDiff_amp]; simp
  simp only [amp_eval,one_pow,mul_one] at h
  exact_mod_cast h

theorem firstDiff_moment (r : ℕ) (a : ℕ → ℝ) :
    (∑ j ∈ range (r+2), (j:ℝ)*firstDiff r a j)= -(∑ j ∈ range (r+1), a j) := by
  have hd : (derivative (amp (r+1) (firstDiff r a))).eval 1= -(amp r a).eval 1 := by
    rw [firstDiff_amp,derivative_mul]
    simp
  have he : (momentAmp (r+1) (firstDiff r a)).eval 1= -(amp r a).eval 1 := by
    rw [← euler_amp_eval,one_mul,hd]
  unfold momentAmp at he
  simp only [amp_eval,one_pow,mul_one] at he
  exact_mod_cast he

theorem weight_at_one (r : ℕ) (a : ℕ → ℝ) :
    weight r a 1 = (∑ j ∈ range (r+1), a j)^2 := by
  unfold weight
  rw [amp_eval]
  simp only [one_pow,mul_one]
  rw [← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem norm_one_sub_sq (z : ℂ) (hz : ‖z‖=1) :
    ‖1-z‖^2=dispersion 2 z := by
  have h : z.re*z.re+z.im*z.im=1 := by
    rw [← Complex.normSq_apply,Complex.normSq_eq_norm_sq,hz]
    norm_num
  rw [← Complex.normSq_eq_norm_sq,Complex.normSq_apply]
  simp [Complex.sub_re,Complex.sub_im,dispersion]
  nlinarith

theorem firstDiff_weight (r : ℕ) (a : ℕ → ℝ) (z : ℂ) (hz : ‖z‖=1) :
    weight (r+1) (firstDiff r a) z=dispersion 2 z*weight r a z := by
  unfold weight
  rw [firstDiff_amp,eval_mul,eval_sub,eval_one,eval_X,norm_mul,mul_pow,norm_one_sub_sq z hz]

theorem critical_energy_sum (r : ℕ) (a : ℕ → ℝ) :
    avg (fun z => dispersion 2 z*weight r a z) =
      ∑ j ∈ range (r+2), (firstDiff r a j)^2 := by
  rw [avg_congr_unit (fun z : ℂ => dispersion 2 z*weight r a z) (weight (r+1) (firstDiff r a))
    (show Continuous (fun z : ℂ => dispersion 2 z*weight r a z) from
      (cont_dispersion 2).mul (cont_weight r a)) (cont_weight _ _)
    (fun z hz => (firstDiff_weight r a z hz).symm),avg_weight_parseval]

def criticalBudget (r : ℕ) : ℝ := ((r:ℝ)+1)*(r+2)*(r+3)/12

def criticalConst (r : ℕ) : ℝ := 1/criticalBudget r

theorem criticalBudget_pos (r : ℕ) : 0<criticalBudget r := by
  unfold criticalBudget
  positivity

theorem criticalConst_pos (r : ℕ) : 0<criticalConst r :=
  one_div_pos.mpr (criticalBudget_pos r)

theorem criticalConst_formula (r : ℕ) :
    criticalConst r = 12/(((r:ℝ)+1)*(r+2)*(r+3)) := by
  unfold criticalConst criticalBudget
  field_simp
  <;> ring

theorem critical_sum_nat (n : ℕ) :
    (∑ j ∈ range n, (j:ℝ)) = (n:ℝ)*(n-1)/2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ,ih]; push_cast; ring

theorem critical_sum_nat_sq (n : ℕ) :
    (∑ j ∈ range n, (j:ℝ)^2) = (n:ℝ)*(n-1)*(2*n-1)/6 := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ,ih]; push_cast; ring

theorem critical_budget_sum (r : ℕ) :
    (∑ j ∈ range (r+2), ((j:ℝ)-((r:ℝ)+1)/2)^2)=criticalBudget r := by
  calc
    _ = ∑ j ∈ range (r+2), ((j:ℝ)^2-((r:ℝ)+1)*j+(((r:ℝ)+1)/2)^2) := by
      apply sum_congr rfl
      intro j hj
      ring
    _ = _ := by
      rw [sum_add_distrib,sum_sub_distrib,← mul_sum,critical_sum_nat_sq,critical_sum_nat]
      simp [criticalBudget]
      ring

theorem critical_energy_lower (r : ℕ) (a : ℕ → ℝ) :
    criticalConst r * weight r a 1 ≤ avg (fun z => dispersion 2 z*weight r a z) := by
  rw [weight_at_one,critical_energy_sum]
  have h := Finset.sum_mul_sq_le_sq_mul_sq (range (r+2))
    (fun j => (j:ℝ)-((r:ℝ)+1)/2) (firstDiff r a)
  have hm : (∑ j ∈ range (r+2), ((j:ℝ)-((r:ℝ)+1)/2)*firstDiff r a j)
      = -(∑ j ∈ range (r+1), a j) := by
    simp only [sub_mul,sum_sub_distrib,← mul_sum,firstDiff_sum,mul_zero,sub_zero,firstDiff_moment]
  rw [hm,neg_sq,critical_budget_sum] at h
  unfold criticalConst
  rw [one_div,mul_comm,← div_eq_mul_inv]
  exact (div_le_iff₀ (criticalBudget_pos r)).2 (by simpa [mul_comm] using h)

def criticalCoeff (r j : ℕ) : ℝ :=
  rawWindow (r+1) j/(2*criticalBudget r)

theorem criticalCoeff_pos (r j : ℕ) (hj : j≤r) : 0<criticalCoeff r j := by
  unfold criticalCoeff rawWindow
  apply div_pos
  · apply mul_pos (by positivity)
    have h : (j:ℝ)≤r := by exact_mod_cast hj
    push_cast
    linarith
  · exact mul_pos (by norm_num) (criticalBudget_pos r)

theorem criticalCoeff_sum (r : ℕ) :
    (∑ j ∈ range (r+1), criticalCoeff r j)=1 := by
  unfold criticalCoeff
  rw [← sum_div]
  have hs : (∑ j ∈ range (r+1), rawWindow (r+1) j)=2*criticalBudget r := by
    calc
      _ = ∑ j ∈ range (r+1), (-(j:ℝ)^2+(r:ℝ)*j+(r:ℝ)+1) := by
        apply sum_congr rfl
        intro j hj
        unfold rawWindow
        push_cast
        ring
      _ = _ := by
        simp only [sum_add_distrib,sum_neg_distrib,← mul_sum,sum_const,card_range,nsmul_eq_mul]
        rw [critical_sum_nat_sq,critical_sum_nat]
        push_cast
        unfold criticalBudget
        ring
  rw [hs,div_self (ne_of_gt (mul_pos (by norm_num) (criticalBudget_pos r)))]

theorem criticalCoeff_diff (r j : ℕ) (hj : j≤r+1) :
    firstDiff r (criticalCoeff r) j= -((j:ℝ)-((r:ℝ)+1)/2)/criticalBudget r := by
  unfold firstDiff cutCoeff
  by_cases h0 : j=0
  · subst j
    simp [criticalCoeff,rawWindow]
    push_cast
    field_simp [(criticalBudget_pos r).ne']
    <;> ring
  · have hp : 1≤j := by omega
    have hq : j-1≤r := by omega
    rw [if_pos hp,if_pos hq]
    by_cases h : j≤r
    · rw [if_pos h]
      unfold criticalCoeff rawWindow
      push_cast [Nat.cast_sub hp]
      field_simp [(criticalBudget_pos r).ne']
      <;> ring
    · have he : j=r+1 := by omega
      rw [if_neg h,he,show r+1-1=r by omega]
      unfold criticalCoeff rawWindow
      push_cast
      field_simp [(criticalBudget_pos r).ne']
      <;> ring

theorem critical_cold_energy (r : ℕ) :
    avg (fun z => dispersion 2 z*weight r (criticalCoeff r) z)=criticalConst r := by
  rw [critical_energy_sum]
  calc
    _ = ∑ j ∈ range (r+2), ((j:ℝ)-((r:ℝ)+1)/2)^2/(criticalBudget r)^2 := by
      apply sum_congr rfl
      intro j hj
      rw [criticalCoeff_diff r j (by simpa using Nat.le_of_lt_succ (mem_range.mp hj)),div_pow,neg_sq]
    _ = _ := by
      rw [← sum_div,critical_budget_sum]
      unfold criticalConst
      field_simp [(criticalBudget_pos r).ne']

end
end GaussianRange
#print axioms GaussianRange.firstDiff_amp
#print axioms GaussianRange.critical_energy_lower
#print axioms GaussianRange.critical_cold_energy
#print axioms GaussianRange.criticalCoeff_sum
