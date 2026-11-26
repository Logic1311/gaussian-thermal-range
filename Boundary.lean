import Integrated

namespace GaussianRange
open Finset Polynomial
noncomputable section

theorem zero_range_not_admissible (b : BathFamily) (m : ℝ) : ¬ b.admissible 0 m := by
  intro hb
  have h₁ := hb.2.2 (1 : ℂ) (by norm_num)
  have h₂ := hb.2.2 (-1 : ℂ) (by norm_num)
  simp [weight, amp, dispersion] at h₁ h₂
  linarith

def nearestCoeff (v : Bool) (j : ℕ) : ℝ :=
  if j = 0 then 1/2 else if j = 1 then (if v then 1/2 else -1/2) else 0

def nearestBath (m : ℝ) : BathFamily where
  ι := Bool
  finite := inferInstance
  coeff := nearestCoeff
  temp := fun v => if v then m else m+4

theorem nearest_amp_eval (r : ℕ) (hr : 0 < r) (v : Bool) (z : ℂ) :
    (amp r (nearestCoeff v)).eval z = 1/2 + (if v then 1/2 else -1/2)*z := by
  have e : amp r (nearestCoeff v) = amp 1 (nearestCoeff v) := by
    unfold amp
    symm
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro j hj hj2
    have h : 2 ≤ j := by simpa [Finset.mem_range, not_lt] using hj2
    simp [nearestCoeff, show j ≠ 0 by omega, show j ≠ 1 by omega]
  rw [e]
  cases v <;> simp [amp, Finset.sum_range_succ, nearestCoeff, eval_monomial] <;> ring

theorem nearest_weight (r : ℕ) (hr : 0 < r) (v : Bool) (z : ℂ) (hz : ‖z‖ = 1) :
    weight r (nearestCoeff v) z = (1+(if v then z.re else -z.re))/2 := by
  unfold weight
  rw [nearest_amp_eval r hr, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  have h : z.re*z.re+z.im*z.im = 1 := by
    rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq, hz]
    norm_num
  cases v <;> norm_num [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.div_re, Complex.div_im, Complex.normSq_apply] <;> nlinarith

theorem nearest_admissible (r : ℕ) (hr : 0 < r) (m : ℝ) (hm : 0 < m) :
    (nearestBath m).admissible r m := by
  refine ⟨?_, ?_, ?_⟩
  · intro v
    cases v <;> simp [nearestBath] <;> linarith
  · intro z hz
    change (∑ v : Bool, weight r (nearestCoeff v) z) = 1
    rw [Fintype.sum_bool, nearest_weight r hr false z hz, nearest_weight r hr true z hz]
    simp <;> ring
  · intro z hz
    change (∑ v : Bool, (if v then m else m+4)*weight r (nearestCoeff v) z) = dispersion (m+2) z
    rw [Fintype.sum_bool, nearest_weight r hr false z hz, nearest_weight r hr true z hz]
    simp [dispersion] <;> ring

theorem admissibleCosts_nonempty_all (r : ℕ) (hr : 0 < r) (m : ℝ) (hm : 0 < m) :
    (admissibleCosts r m).Nonempty :=
  ⟨(nearestBath m).cost r m, nearestBath m, nearest_admissible r hr m hm, rfl⟩

end
end GaussianRange
#print axioms GaussianRange.zero_range_not_admissible
#print axioms GaussianRange.nearest_weight
#print axioms GaussianRange.nearest_admissible
#print axioms GaussianRange.admissibleCosts_nonempty_all