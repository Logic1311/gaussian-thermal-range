import Mathlib.Tactic
open Finset
namespace GaussianRange
variable {β : Type*} [Fintype β]

theorem entropy_identity (w T : β → ℝ) (d : ℝ)
    (hd : 0 < d) (ht : ∀ v, 0 < T v)
    (hw : ∑ v, w v = 1) (hm : ∑ v, T v * w v = d) :
    (∑ v, w v * (T v-d)^2 / (T v*d)) =
      d * (∑ v, w v / T v) - 1 := by
  calc
    _ = ∑ v, (T v*w v/d - 2*w v + d*(w v/T v)) := by
      apply sum_congr rfl
      intro v _
      field_simp [(ht v).ne', hd.ne']
      <;> ring
    _ = _ := by
      rw [sum_add_distrib, sum_sub_distrib, ← sum_div, ← mul_sum, ← mul_sum, hw, hm, div_self hd.ne']
      ring

theorem variance_identity (w T : β → ℝ) (d : ℝ)
    (hw : ∑ v, w v = 1) (hm : ∑ v, T v*w v=d) :
    (∑ v, w v*(T v-d)^2) = (∑ v, w v*T v^2)-d^2 := by
  calc
    _ = ∑ v, (w v*T v^2 - (2*d)*(T v*w v) + d^2*w v) := by
      apply sum_congr rfl
      intro v _
      ring
    _ = _ := by
      rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum, hw, hm]
      ring

theorem entropy_upper (w T : β → ℝ) (d m t : ℝ)
    (hm : 0 < m) (ht : 0 < t) (hd : m ≤ d)
    (hT : ∀ v, t ≤ T v) (hw : ∀ v, 0 ≤ w v) :
    (∑ v, w v*(T v-d)^2/(T v*d)) ≤
      (∑ v, w v*(T v-d)^2)/(t*m) := by
  rw [sum_div]
  apply sum_le_sum
  intro v _
  apply div_le_div_of_nonneg_left (mul_nonneg (hw v) (sq_nonneg _)) (mul_pos ht hm)
  exact mul_le_mul (hT v) hd hm.le (ht.le.trans (hT v))

#print axioms entropy_identity
#print axioms variance_identity
#print axioms entropy_upper
end GaussianRange
