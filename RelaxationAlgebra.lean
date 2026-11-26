import Mathlib.Tactic

namespace GaussianRange
open Finset
noncomputable section
variable {ι : Type*} [Fintype ι]

def realDot (a b : ι → ℝ) : ℝ := ∑ i, a i * b i

def realSq (a : ι → ℝ) : ℝ := ∑ i, (a i)^2

theorem realDot_sub (a u v : ι → ℝ) :
    realDot a (fun i => u i-v i) = realDot a u-realDot a v := by
  simp [realDot,mul_sub,Finset.sum_sub_distrib]

theorem realSq_diff (u v : ι → ℝ) :
    realSq (fun i => u i-v i)=realSq u+realSq v-2*realDot u v := by
  unfold realSq realDot
  have h (i : ι) : (u i-v i)^2 = u i^2+v i^2-2*(u i*v i) := by ring
  simp_rw [h,Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum]

theorem realDot_diff_left_u (u v : ι → ℝ) :
    realDot (fun i => u i-v i) u=realSq u-realDot u v := by
  unfold realDot realSq
  simp_rw [sub_mul,Finset.sum_sub_distrib,pow_two,mul_comm (v _) (u _)]

theorem realDot_diff_left_v (u v : ι → ℝ) :
    realDot (fun i => u i-v i) v=realDot u v-realSq v := by
  unfold realDot realSq
  simp_rw [sub_mul,Finset.sum_sub_distrib,pow_two]

theorem realDot_scale (a b : ι → ℝ) (c : ℝ) :
    realDot (fun i => c*a i) b=c*realDot a b := by
  simp [realDot,mul_assoc,Finset.mul_sum]

theorem realSq_scale (a : ι → ℝ) (c : ℝ) :
    realSq (fun i => c*a i)=c^2*realSq a := by
  simp [realSq,mul_pow,Finset.mul_sum]

-- Exact rank-two constrained minimum; the target is a negative product.
-- This is the algebraic part of the majorant proof, not Fejer-Riesz itself.
theorem rankTwo_exact_minimum (u v : ι → ℝ) (h : ℝ) (hh : 0<h)
    (he : realSq u=realSq v) (hq : 0<realSq (fun i => u i-v i)) :
    ∃ a : ι → ℝ, realDot a u*realDot a v = -h ∧
      realSq a=4*h/realSq (fun i => u i-v i) ∧
      ∀ b : ι → ℝ, realDot b u*realDot b v = -h →
        4*h/realSq (fun i => u i-v i) ≤ realSq b := by
  let q := realSq (fun i => u i-v i)
  have hq' : 0<q := hq
  have hqu : realDot (fun i => u i-v i) u=q/2 := by
    rw [realDot_diff_left_u]
    dsimp [q]
    rw [realSq_diff,← he]
    ring
  have hqv : realDot (fun i => u i-v i) v=-(q/2) := by
    rw [realDot_diff_left_v]
    dsimp [q]
    rw [realSq_diff,← he]
    ring
  let c := 2*Real.sqrt h/q
  let a := fun i => c*(u i-v i)
  have hu : realDot a u=Real.sqrt h := by
    dsimp [a]
    rw [realDot_scale,hqu]
    dsimp [c]
    field_simp [hq'.ne']
  have hv : realDot a v= -Real.sqrt h := by
    dsimp [a]
    rw [realDot_scale,hqv]
    dsimp [c]
    field_simp [hq'.ne']
  refine ⟨a,?_,?_,?_⟩
  · rw [hu,hv, mul_neg,← pow_two,Real.sq_sqrt hh.le]
  · change realSq a=4*h/q
    dsimp [a]
    rw [realSq_scale]
    change c^2*q=4*h/q
    dsimp [c]
    rw [div_pow,mul_pow,Real.sq_sqrt hh.le]
    field_simp [hq'.ne']
    <;> ring
  · intro b hb
    change 4*h/q≤realSq b
    apply (div_le_iff₀ hq').2
    have hc : (realDot b (fun i => u i-v i))^2 ≤ realSq b*q :=
      Finset.sum_mul_sq_le_sq_mul_sq Finset.univ b (fun i => u i-v i)
    rw [realDot_sub] at hc
    nlinarith [sq_nonneg (realDot b u+realDot b v)]

end
end GaussianRange
#print axioms GaussianRange.rankTwo_exact_minimum