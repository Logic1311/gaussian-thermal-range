import Mathlib.Tactic

open scoped BigOperators
open Finset

namespace GaussianRange

noncomputable section

def q (a : ℕ → ℝ) (k : ℝ) (j : ℕ) : ℝ := (j - k) * a j
def h (a : ℕ → ℝ) (d : ℝ) (j : ℕ) : ℝ :=
  d * a j + a (j - 1) + a (j + 1)
def B (n : ℕ) (a : ℕ → ℝ) : ℝ := ∑ j ∈ range n, a j * a (j+1)
def D (n : ℕ) (a : ℕ → ℝ) : ℝ := ∑ j ∈ range n, a j * a (j+2)
def K (n : ℕ) (a : ℕ → ℝ) (k d : ℝ) : ℝ :=
  ∑ j ∈ range n, (q a k j * h a d (j+1) - q a k (j+1) * h a d j)

theorem telescoping (f : ℕ → ℝ) (n : ℕ) :
    (∑ j ∈ range n, (f j - f (j+1))) = f 0 - f n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    ring

theorem shift_two (a : ℕ → ℝ) (k : ℝ) (n : ℕ)
    (h0 : a 0 = 0) (hn : a (n+1) = 0) :
    (∑ j ∈ range n, q a k (j+1) * a (j-1)) =
      ∑ j ∈ range n, q a k (j+2) * a j := by
  cases n with
  | zero => simp
  | succ n =>
    rw [sum_range_succ', sum_range_succ]
    simp only [Nat.zero_add, Nat.zero_sub, h0, mul_zero, add_zero]
    have hz : q a k (n+2) = 0 := by unfold q; rw [show n+2 = n+1+1 by omega, hn, mul_zero]
    rw [hz, zero_mul, add_zero]
    apply sum_congr rfl
    intro j _
    simp only [Nat.add_sub_cancel]


theorem commutator (a : ℕ → ℝ) (k d : ℝ) (n : ℕ)
    (h0 : a 0 = 0) (hn : a n = 0) (hn1 : a (n+1) = 0) :
    K n a k d = -d * B n a - 2 * D n a := by
  have e0 : q a k 0 * a 0 = 0 := by simp [q,h0]
  have en : q a k n * a n = 0 := by simp [q,hn]
  have ht := telescoping (fun j => q a k j * a j) n
  rw [e0, en, sub_zero] at ht
  have hs := shift_two a k n h0 hn1
  unfold K B D
  calc
    _ = ∑ j ∈ range n,
      (-(d * (a j * a (j+1))) +
        (q a k j * a j - q a k (j+1) * a (j+1)) +
        (q a k j * a (j+2) - q a k (j+1) * a (j-1))) := by
          apply sum_congr rfl
          intro j _
          unfold h q
          push_cast
          ring
    _ = -d * (∑ j ∈ range n, a j * a (j+1)) -
      2 * (∑ j ∈ range n, a j * a (j+2)) := by
        rw [sum_add_distrib, sum_add_distrib, ht, add_zero, sum_sub_distrib, hs]
        rw [← sum_sub_distrib]; simp only [← neg_mul, ← mul_sum]
        have eq : (∑ j ∈ range n, (q a k j * a (j+2) - q a k (j+2) * a j)) =
          -2 * (∑ j ∈ range n, a j * a (j+2)) := by
            rw [mul_sum]
            apply sum_congr rfl
            intro j _
            unfold q
            push_cast
            ring
        rw [eq]
        ring

theorem young (x y t : ℝ) (ht : 0 < t) :
    2*x*y ≤ t*x^2 + y^2/t := by
  apply le_of_sub_nonneg
  have h' : 0 ≤ (t*x-y)^2/t := div_nonneg (sq_nonneg _) ht.le
  convert h' using 1
  field_simp
  ring

theorem sum_shift_le (f : ℕ → ℝ) (n : ℕ) (hf : ∀ j, 0 ≤ f j) :
    (∑ j ∈ range n, f (j+1)) ≤ ∑ j ∈ range (n+1), f j := by
  rw [sum_range_succ']
  linarith [hf 0]

theorem sum_plain_le (f : ℕ → ℝ) (n : ℕ) (hf : ∀ j, 0 ≤ f j) :
    (∑ j ∈ range n, f j) ≤ ∑ j ∈ range (n+1), f j := by
  rw [sum_range_succ]
  linarith [hf n]

theorem K_bound (a : ℕ → ℝ) (k d t : ℝ) (n : ℕ) (ht : 0 < t) :
    K n a k d ≤ t * (∑ j ∈ range (n+1), (q a k j)^2) +
       (∑ j ∈ range (n+1), (h a d j)^2)/t := by
  have e : K n a k d ≤
      (∑ j ∈ range n, (t*(q a k j)^2 + (h a d (j+1))^2/t +
                         t*(q a k (j+1))^2 + (h a d j)^2/t)/2) := by
    unfold K
    apply sum_le_sum
    intro j _
    have h1 := young (q a k j) (h a d (j+1)) t ht
    have h2 := young (-q a k (j+1)) (h a d j) t ht
    rw [neg_sq] at h2
    linarith
  rw [← sum_div] at e
  simp only [sum_add_distrib, ← mul_sum, ← sum_div] at e
  have e1 := sum_plain_le (fun j => (q a k j)^2) n (fun _ => sq_nonneg _)
  have e2 := sum_shift_le (fun j => (q a k j)^2) n (fun _ => sq_nonneg _)
  have e3 := sum_plain_le (fun j => (h a d j)^2) n (fun _ => sq_nonneg _)
  have e4 := sum_shift_le (fun j => (h a d j)^2) n (fun _ => sq_nonneg _)
  have e5 := mul_le_mul_of_nonneg_left e1 ht.le
  have e6 := mul_le_mul_of_nonneg_left e2 ht.le
  have e7 := div_le_div_of_nonneg_right e3 ht.le
  have e8 := div_le_div_of_nonneg_right e4 ht.le
  linarith

end
end GaussianRange

namespace GaussianRange
open Finset
noncomputable section
variable {β : Type*} [Fintype β]

def A (n : ℕ) (a : ℕ → ℝ) := ∑ j ∈ range (n+1), (a j)^2

def Q (r : ℕ) (a : ℕ → ℝ) := ∑ j ∈ range (r+3), (q a ((r:ℝ)/2+1) j)^2

def H (r : ℕ) (a : β → ℕ → ℝ) (T : β → ℝ) (c : ℝ) :=
  ∑ v, (∑ j ∈ range (r+3), (h (a v) (T v-c) j)^2) / T v

theorem Q_bound (r : ℕ) (a : ℕ → ℝ) (h0 : a 0 = 0) (hn : a (r+2)=0) :
    Q r a ≤ (r:ℝ)^2/4 * A (r+2) a := by
  unfold Q A
  rw [mul_sum]
  apply sum_le_sum
  intro j hj
  have hj' : j < r+3 := mem_range.mp hj
  by_cases e0 : j=0
  · subst j
    simp [q,h0]
  by_cases en : j=r+2
  · subst j
    simp [q,hn]
  have jl : (1:ℝ) ≤ j := by exact_mod_cast (show 1≤j by omega)
  have ju : (j:ℝ) ≤ (r:ℝ)+1 := by exact_mod_cast (show j≤r+1 by omega)
  have rr : 0 ≤ (r:ℝ) := by positivity
  have bound : ((j:ℝ)-((r:ℝ)/2+1))^2 ≤ (r:ℝ)^2/4 := by
    nlinarith [mul_nonneg (show 0 ≤ (j:ℝ)-1 by linarith)
      (show 0 ≤ (r:ℝ)+1-j by linarith)]
  unfold q
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_right bound (sq_nonneg _)

theorem residual_nonnegative (r : ℕ) (a : β → ℕ → ℝ) (T : β → ℝ)
    (c : ℝ) (ht : ∀ v, 0 < T v) : 0 ≤ H r a T c := by
  unfold H
  exact sum_nonneg fun v _ => div_nonneg (sum_nonneg fun j _ => sq_nonneg _) (ht v).le

/-- Exact finite coefficient inequality for range r real bath amplitudes, padded on
    both ends. All hypotheses are Fourier coefficient identities of the two
    normalization equations; no optimized entropy bound is assumed. -/
theorem residual_lower (r : ℕ) (hr : 0 < r) (a : β → ℕ → ℝ)
    (T : β → ℝ) (c : ℝ) (hc : 0<c) (ht : ∀ v, 0<T v)
    (pad0 : ∀ v, a v 0=0) (pad1 : ∀ v, a v (r+2)=0)
    (pad2 : ∀ v, a v (r+3)=0)
    (mass : ∑ v, T v * A (r+2) (a v) = c)
    (b0 : ∑ v, B (r+2) (a v)=0)
    (b1 : ∑ v, T v * B (r+2) (a v) = -1)
    (d0 : ∑ v, D (r+2) (a v)=0) :
    1 ≤ (r:ℝ)^2*c*H r a T c := by
  let t : ℝ := 2 / ((r:ℝ)^2*c)
  have rr : 0 < (r:ℝ) := by exact_mod_cast hr
  have rc : 0 < (r:ℝ)^2*c := by positivity
  have hp : 0 < t := by dsimp [t]; positivity
  have ksum : ∑ v, K (r+2) (a v) ((r:ℝ)/2+1) (T v-c) = 1 := by
    simp_rw [commutator _ _ _ _ (pad0 _) (pad1 _) (pad2 _)]
    simp only [neg_sub, sub_mul, sum_sub_distrib, ← mul_sum]
    rw [b0,b1,d0]
    ring
  have qsum : ∑ v, T v * Q r (a v) ≤ (r:ℝ)^2/4*c := by
    calc
      _ ≤ ∑ v, ((r:ℝ)^2/4)*(T v * A (r+2) (a v)) := by
        apply sum_le_sum
        intro v _
        have hq := mul_le_mul_of_nonneg_left (Q_bound r (a v) (pad0 v) (pad1 v)) (ht v).le
        convert hq using 1 <;> ring
      _ = _ := by rw [← mul_sum, mass]
  have kk : ∑ v, K (r+2) (a v) ((r:ℝ)/2+1) (T v-c) ≤
      t*(∑ v,T v*Q r (a v)) + H r a T c / t := by
    unfold H
    rw [mul_sum, sum_div, ← sum_add_distrib]
    apply sum_le_sum
    intro v _
    have e := K_bound (a v) ((r:ℝ)/2+1) (T v-c) (t*T v) (r+2)
      (mul_pos hp (ht v))
    unfold Q
    convert e using 1 <;> simp only [div_div] <;> ring
  rw [ksum] at kk
  have e := mul_le_mul_of_nonneg_left qsum hp.le
  have e' : 1 ≤ t*((r:ℝ)^2/4*c) + H r a T c/t := by linarith
  have ht1 : t*((r:ℝ)^2/4*c) = 1/2 := by dsimp [t]; field_simp; ring
  rw [ht1] at e'
  have e2 : (1/2:ℝ) ≤ H r a T c/t := by linarith
  have e3 := (le_div_iff₀ hp).mp e2
  have e4 := mul_le_mul_of_nonneg_right e3 rc.le
  have ht2 : (1/2:ℝ)*t*((r:ℝ)^2*c) = 1 := by dsimp [t]; field_simp
  rw [ht2] at e4
  convert e4 using 1 <;> ring

end
end GaussianRange
