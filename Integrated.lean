import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.Polynomial.Fourier
import Mathlib.Tactic
open Finset Polynomial
namespace GaussianRange
noncomputable section
variable {β : Type*} [Fintype β]

/-- Reversal using a fixed padding degree, expressed as a finite polynomial. -/
def amp (r : ℕ) (a : ℕ → ℝ) : ℂ[X] :=
  ∑ j ∈ range (r+1), monomial j (a j : ℂ)
def rev (r : ℕ) (a : ℕ → ℝ) : ℂ[X] :=
  ∑ j ∈ range (r+1), monomial (r-j) (a j : ℂ)

theorem amp_eval (r : ℕ) (a : ℕ → ℝ) (z : ℂ) :
    (amp r a).eval z = ∑ j ∈ range (r+1), (a j : ℂ)*z^j := by
  simp [amp, eval_finset_sum, eval_monomial]

theorem rev_eval (r : ℕ) (a : ℕ → ℝ) (z : ℂ) :
    (rev r a).eval z = ∑ j ∈ range (r+1), (a j : ℂ)*z^(r-j) := by
  simp [rev, eval_finset_sum, eval_monomial]

theorem rev_unit (r : ℕ) (a : ℕ → ℝ) (z : ℂ) (hz : ‖z‖ = 1) :
    (rev r a).eval z = z^r * star ((amp r a).eval z) := by
  have hzz : z * star z = 1 := by
    change z * (starRingEnd ℂ) z = 1
    rw [Complex.mul_conj]
    simp [Complex.normSq_eq_norm_sq, hz]
  rw [rev_eval, amp_eval, star_sum, mul_sum]
  apply sum_congr rfl
  intro j hj
  have hj' : j ≤ r := Nat.lt_succ_iff.mp (mem_range.mp hj)
  rw [star_mul, star_pow]
  have hpow : z^j * (star z)^j = 1 := by rw [← mul_pow,hzz,one_pow]
  calc
    _ = (a j : ℂ) * (z^(r-j) * (z^j * (star z)^j)) := by rw [hpow,mul_one]
    _ = z^r * star ((a j : ℂ)) * (star z)^j := by
      rw [Complex.star_def, Complex.conj_ofReal, ← mul_assoc (z^(r-j)), ← pow_add, Nat.sub_add_cancel hj']
      ring
    _ = _ := by ring

end
end GaussianRange

namespace GaussianRange
open Finset Polynomial
noncomputable section
variable {β : Type*} [Fintype β]

theorem spectral_eval (r : ℕ) (a : ℕ → ℝ) (z : ℂ) (hz : ‖z‖ = 1) :
    (amp r a * rev r a).eval z = z^r * ((‖(amp r a).eval z‖^2 : ℝ) : ℂ) := by
  rw [eval_mul, rev_unit r a z hz]
  rw [← mul_assoc, mul_comm ((amp r a).eval z) (z^r), mul_assoc]
  congr 1
  change (amp r a).eval z * (starRingEnd ℂ) ((amp r a).eval z) = _
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem spectral_sum_eval (r : ℕ) (a : β → ℕ → ℝ) (T : β → ℝ)
    (z : ℂ) (hz : ‖z‖ = 1) :
    (∑ v, C (T v : ℂ) * (amp r (a v) * rev r (a v))).eval z =
      z^r * ((∑ v, T v * ‖(amp r (a v)).eval z‖^2 : ℝ) : ℂ) := by
  simp only [eval_finset_sum, eval_mul, eval_C, spectral_eval _ _ _ hz]
  push_cast
  rw [mul_sum]
  apply sum_congr rfl
  intro v _
  ring

#print axioms rev_unit
#print axioms spectral_eval
#print axioms spectral_sum_eval
end
end GaussianRange

namespace GaussianRange
open Finset Polynomial
noncomputable section
variable {β : Type*} [Fintype β]

/-- A purely algebraic unit-circle parametrization. -/
def cayley (t : ℝ) : ℂ := ((t : ℂ) + Complex.I) / ((t : ℂ) - Complex.I)

theorem cayley_den (t : ℝ) : (t : ℂ) - Complex.I ≠ 0 := by
  intro h
  have e := congrArg Complex.im h
  simp at e

theorem cayley_unit (t : ℝ) : ‖cayley t‖ = 1 := by
  unfold cayley
  rw [norm_div]
  have hn : ‖(t : ℂ) - Complex.I‖ ≠ 0 := norm_ne_zero_iff.mpr (cayley_den t)
  apply (div_eq_one_iff_eq hn).mpr
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  simp [Complex.normSq_apply]
  <;> ring

theorem cayley_injective : Function.Injective cayley := by
  intro s t h
  unfold cayley at h
  have e := (div_eq_div_iff (cayley_den s) (cayley_den t)).mp h
  have ei := congrArg Complex.im e
  simp [Complex.mul_im] at ei
  linarith

theorem poly_unit_unique (p q : ℂ[X])
    (h : ∀ z : ℂ, ‖z‖ = 1 → p.eval z = q.eval z) : p = q := by
  apply Polynomial.eq_of_infinite_eval_eq
  have hi : Set.Infinite (Set.range cayley) := Set.infinite_range_of_injective cayley_injective
  apply hi.mono
  rintro z ⟨t,rfl⟩
  exact h _ (cayley_unit t)

def spectrum (r : ℕ) (a : β → ℕ → ℝ) (T : β → ℝ) : ℂ[X] :=
  ∑ v, C (T v : ℂ) * (amp r (a v) * rev r (a v))

theorem normalization_poly (r : ℕ) (a : β → ℕ → ℝ)
    (h : ∀ z : ℂ, ‖z‖ = 1 → ∑ v, ‖(amp r (a v)).eval z‖^2 = 1) :
    spectrum r a (fun _ => 1) = X^r := by
  apply poly_unit_unique
  intro z hz
  unfold spectrum
  rw [spectral_sum_eval _ _ _ _ hz]
  simp only [one_mul] 
  rw [h z hz]
  simp

theorem weighted_normalization_poly (r : ℕ) (hr : 0 < r)
    (a : β → ℕ → ℝ) (T : β → ℝ) (c : ℝ)
    (h : ∀ z : ℂ, ‖z‖ = 1 →
      ∑ v, T v * ‖(amp r (a v)).eval z‖^2 = c - 2*z.re) :
    spectrum r a T = C (c : ℂ)*X^r - X^(r+1) - X^(r-1) := by
  apply poly_unit_unique
  intro z hz
  unfold spectrum
  rw [spectral_sum_eval _ _ _ _ hz, h z hz]
  simp only [eval_sub, eval_mul, eval_C, eval_pow, eval_X]
  have hzz : z * star z = 1 := by
    change z * (starRingEnd ℂ) z = 1
    rw [Complex.mul_conj]
    simp [Complex.normSq_eq_norm_sq,hz]
  have hre : (2 * (z.re : ℂ)) = z + star z := by
    apply Complex.ext <;> simp [Complex.add_re, Complex.add_im] <;> ring
  have hs : z^r * star z = z^(r-1) := by
    have e : r = (r-1)+1 := by omega
    calc
      _ = z^((r-1)+1)*star z := by rw [← e]
      _ = _ := by rw [pow_succ, mul_assoc,hzz,mul_one]
  push_cast
  rw [hre, mul_sub, mul_add, ← pow_succ, hs]
  ring

#print axioms poly_unit_unique
#print axioms normalization_poly
#print axioms weighted_normalization_poly
end
end GaussianRange

namespace GaussianRange
open Finset Polynomial
noncomputable section
variable {β : Type*} [Fintype β]

/-- The full spectrum as a double sum of monomials, with no sampling. -/
theorem spectral_expand (r : ℕ) (a : ℕ → ℝ) :
    amp r a * rev r a =
      ∑ i ∈ range (r+1), ∑ j ∈ range (r+1),
        monomial (i+(r-j)) ((a i : ℂ)*(a j : ℂ)) := by
  unfold amp rev
  rw [sum_mul]
  apply sum_congr rfl
  intro i _
  rw [mul_sum]
  apply sum_congr rfl
  intro j _
  rw [monomial_mul_monomial]

theorem spectral_coeff (r k : ℕ) (a : ℕ → ℝ) :
    (amp r a * rev r a).coeff k =
      ∑ i ∈ range (r+1), ∑ j ∈ range (r+1),
        if i+(r-j)=k then (a i : ℂ)*(a j : ℂ) else 0 := by
  rw [spectral_expand]
  simp only [finset_sum_coeff, coeff_monomial]

theorem spectral_lag (r d : ℕ) (a : ℕ → ℝ) :
    (amp r a * rev r a).coeff (r+d) =
      ∑ j ∈ range (r+1), if j+d≤r then (a (j+d) : ℂ)*(a j : ℂ) else 0 := by
  rw [spectral_coeff, sum_comm]
  apply sum_congr rfl
  intro j hj
  have hjr : j ≤ r := Nat.lt_succ_iff.mp (mem_range.mp hj)
  have hiff (i : ℕ) : i+(r-j)=r+d ↔ i=j+d := by omega
  simp_rw [hiff]
  rw [sum_ite_eq']
  simp [Nat.lt_succ_iff]

theorem spectrum_lag (r d : ℕ) (a : β → ℕ → ℝ) (T : β → ℝ) :
    (spectrum r a T).coeff (r+d) =
      ∑ v, (T v : ℂ) * (∑ j ∈ range (r+1),
        if j+d≤r then (a v (j+d) : ℂ)*(a v j : ℂ) else 0) := by
  simp only [spectrum, finset_sum_coeff, coeff_C_mul, spectral_lag]

#print axioms spectral_lag
#print axioms spectrum_lag
end
end GaussianRange

namespace GaussianRange
open Finset Polynomial
noncomputable section
variable {β : Type*} [Fintype β]

def lag (r d : ℕ) (a : ℕ → ℝ) : ℝ :=
  ∑ j ∈ range (r+1), if j+d≤r then a (j+d)*a j else 0

theorem spectrum_lag_real (r d : ℕ) (a : β → ℕ → ℝ) (T : β → ℝ) :
    ((spectrum r a T).coeff (r+d)).re = ∑ v, T v * lag r d (a v) := by
  rw [spectrum_lag]
  unfold lag
  have e : (∑ v, (T v : ℂ) * (∑ j ∈ range (r+1),
        if j+d≤r then (a v (j+d) : ℂ)*(a v j : ℂ) else 0)) =
      ((∑ v, T v * (∑ j ∈ range (r+1),
        if j+d≤r then a v (j+d)*a v j else 0) : ℝ) : ℂ) := by
    push_cast
    apply sum_congr rfl
    intro v _
    congr 1
    apply sum_congr rfl
    intro j _
    split_ifs <;> simp
  rw [e, Complex.ofReal_re]

theorem physical_lags (r : ℕ) (hr : 0 < r)
    (a : β → ℕ → ℝ) (T : β → ℝ) (c : ℝ)
    (h0 : ∀ z : ℂ, ‖z‖ = 1 → ∑ v, ‖(amp r (a v)).eval z‖^2 = 1)
    (h1 : ∀ z : ℂ, ‖z‖ = 1 →
      ∑ v, T v * ‖(amp r (a v)).eval z‖^2 = c - 2*z.re) :
    (∑ v, T v * lag r 0 (a v)) = c ∧
    (∑ v, lag r 1 (a v)) = 0 ∧
    (∑ v, T v * lag r 1 (a v)) = -1 ∧
    (∑ v, lag r 2 (a v)) = 0 := by
  have e0 := normalization_poly r a h0
  have e1 := weighted_normalization_poly r hr a T c h1
  have hne : r-1 ≠ r := by omega
  have hne1 : r-1 ≠ r+1 := by omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← spectrum_lag_real, e1]
    simp [coeff_sub, coeff_C_mul, coeff_X_pow, hne, Ne.symm hne]
  · have e := spectrum_lag_real r 1 a (fun _ => 1)
    rw [e0] at e
    simpa [coeff_X_pow] using e.symm
  · rw [← spectrum_lag_real, e1]
    simp [coeff_sub, coeff_C_mul, coeff_X_pow, hne1, Ne.symm hne1]
  · have e := spectrum_lag_real r 2 a (fun _ => 1)
    rw [e0] at e
    simpa [coeff_X_pow] using e.symm

#print axioms physical_lags
end
end GaussianRange

namespace GaussianRange
open Finset Polynomial
noncomputable section
variable {β : Type*} [Fintype β]

/-- Padding used by the original finite-coefficient lower bound. -/
def padded (r : ℕ) (a : ℕ → ℝ) (j : ℕ) : ℝ :=
  if 1 ≤ j ∧ j ≤ r+1 then a (j-1) else 0

theorem padded_zero (r : ℕ) (a : ℕ → ℝ) : padded r a 0 = 0 := by simp [padded]

theorem padded_end (r : ℕ) (a : ℕ → ℝ) : padded r a (r+2) = 0 := by
  simp [padded]

theorem padded_end2 (r : ℕ) (a : ℕ → ℝ) : padded r a (r+3) = 0 := by
  simp [padded]

theorem padded_lag_term (r d j : ℕ) (a : ℕ → ℝ) (hj : j ≤ r) :
    padded r a (j+1) * padded r a (j+1+d) =
      if j+d≤r then a (j+d)*a j else 0 := by
  have hfirst : 1 ≤ j+1 ∧ j+1≤r+1 := by omega
  unfold padded
  rw [if_pos hfirst]
  by_cases hd : j+d≤r
  · rw [if_pos (show 1≤j+1+d ∧ j+1+d≤r+1 by omega), if_pos hd]
    have e : j+1+d-1=j+d := by omega
    rw [e, Nat.add_sub_cancel]
    ring
  · rw [if_neg (show ¬(1≤j+1+d ∧ j+1+d≤r+1) by omega), if_neg hd, mul_zero]

theorem padded_lag (r d : ℕ) (a : ℕ → ℝ) :
    (∑ j ∈ range (r+2), padded r a j * padded r a (j+d)) = lag r d a := by
  rw [sum_range_succ']
  simp only [Nat.zero_add, padded_zero, zero_mul, add_zero]
  unfold lag
  apply sum_congr rfl
  intro j hj
  exact padded_lag_term r d j a (Nat.lt_succ_iff.mp (mem_range.mp hj))

end
end GaussianRange


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


namespace GaussianRange
open Finset
noncomputable section
variable {β : Type*} [Fintype β]

theorem padded_A (r : ℕ) (a : ℕ → ℝ) :
    A (r+2) (padded r a) = lag r 0 a := by
  unfold A
  rw [sum_range_succ]
  rw [padded_end, zero_pow (by decide : (2:ℕ) ≠ 0), add_zero]
  simpa [pow_two] using padded_lag r 0 a

theorem physical_residual_lower (r : ℕ) (hr : 0 < r)
    (a : β → ℕ → ℝ) (T : β → ℝ) (c : ℝ)
    (hc : 0 < c) (ht : ∀ v, 0 < T v)
    (h0 : ∀ z : ℂ, ‖z‖ = 1 → ∑ v, ‖(amp r (a v)).eval z‖^2 = 1)
    (h1 : ∀ z : ℂ, ‖z‖ = 1 →
      ∑ v, T v * ‖(amp r (a v)).eval z‖^2 = c - 2*z.re) :
    1 ≤ (r:ℝ)^2*c*H r (fun v => padded r (a v)) T c := by
  obtain ⟨e0,e1,e2,e3⟩ := physical_lags r hr a T c h0 h1
  apply residual_lower r hr _ T c hc ht
    (fun v => padded_zero r (a v))
    (fun v => padded_end r (a v))
    (fun v => padded_end2 r (a v))
  · simpa only [padded_A] using e0
  · simpa only [B, padded_lag] using e1
  · simpa only [B, padded_lag] using e2
  · simpa only [D, padded_lag] using e3

#print axioms physical_residual_lower
end
end GaussianRange

namespace GaussianRange
open Finset Polynomial
noncomputable section
variable {β : Type*} [Fintype β]

def dispersion (c : ℝ) (z : ℂ) : ℝ := c-2*z.re

def weight (r : ℕ) (a : ℕ → ℝ) (z : ℂ) : ℝ :=
  ‖(amp r a).eval z‖^2

def sigma (r : ℕ) (a : β → ℕ → ℝ) (T : β → ℝ) (c : ℝ) (z : ℂ) : ℝ :=
  dispersion c z * (∑ v, weight r (a v) z / T v) - 1

def resPoly (r : ℕ) (a : ℕ → ℝ) (d : ℝ) : ℂ[X] :=
  (C (d : ℂ)*X + X^2 + 1)*amp r a

theorem resPoly_unit (r : ℕ) (a : ℕ → ℝ) (T c : ℝ) (z : ℂ) (hz : ‖z‖ = 1) :
    (resPoly r a (T-c)).eval z =
      z * ((T-dispersion c z : ℝ) : ℂ) * (amp r a).eval z := by
  have hzz : z * star z = 1 := by
    change z * (starRingEnd ℂ) z = 1
    rw [Complex.mul_conj]
    simp [Complex.normSq_eq_norm_sq,hz]
  have hre : (2 * (z.re : ℂ)) = z + star z := by
    apply Complex.ext <;> simp [Complex.add_re, Complex.add_im] <;> ring
  unfold resPoly dispersion
  simp only [eval_mul, eval_add, eval_C, eval_X, eval_pow, eval_one]
  push_cast
  rw [hre]
  have e : z^2 + 1 = z*(z+star z) := by rw [mul_add,hzz,pow_two]
  rw [add_assoc, e]
  ring

theorem resPoly_norm (r : ℕ) (a : ℕ → ℝ) (T c : ℝ) (z : ℂ) (hz : ‖z‖ = 1) :
    ‖(resPoly r a (T-c)).eval z‖^2 =
      (T-dispersion c z)^2 * weight r a z := by
  rw [resPoly_unit r a T c z hz]
  simp only [norm_mul, hz, one_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs, weight]

theorem sigma_weighted_residual (r : ℕ) (a : β → ℕ → ℝ) (T : β → ℝ)
    (c : ℝ) (z : ℂ) (hz : ‖z‖ = 1)
    (hc : 2 < c) (ht : ∀ v, 0<T v)
    (h0 : ∑ v, weight r (a v) z = 1)
    (h1 : ∑ v, T v * weight r (a v) z = dispersion c z) :
    (∑ v, ‖(resPoly r (a v) (T v-c)).eval z‖^2 / T v) =
      dispersion c z * sigma r a T c z := by
  have hzre := Complex.abs_re_le_norm z
  rw [hz] at hzre
  have hd : 0 < dispersion c z := by
    unfold dispersion
    linarith [le_abs_self z.re]
  have e := entropy_identity (fun v => weight r (a v) z) T (dispersion c z) hd ht h0 h1
  unfold sigma
  rw [← e]
  rw [mul_sum]
  apply sum_congr rfl
  intro v _
  rw [resPoly_norm r (a v) (T v) c z hz]
  field_simp [(ht v).ne',hd.ne']

#print axioms resPoly_norm
#print axioms sigma_weighted_residual
end
end GaussianRange

namespace GaussianRange
open Finset Polynomial
noncomputable section

theorem amp_coeff (r j : ℕ) (a : ℕ → ℝ) :
    (amp r a).coeff j = if j≤r then (a j : ℂ) else 0 := by
  unfold amp
  simp only [finset_sum_coeff, coeff_monomial]
  rw [sum_ite_eq']
  simp

theorem amp_coeff_pad (r j : ℕ) (a : ℕ → ℝ) :
    (amp r a).coeff j = (padded r a (j+1) : ℂ) := by
  rw [amp_coeff]
  simp [padded]
  split_ifs <;> simp

theorem resPoly_coeff (r j : ℕ) (a : ℕ → ℝ) (d : ℝ) :
    (resPoly r a d).coeff j = (h (padded r a) d j : ℂ) := by
  unfold resPoly h
  rw [add_mul, add_mul, one_mul]
  simp only [coeff_add, mul_assoc, coeff_C_mul]
  rw [mul_comm X (amp r a), mul_comm (X^2) (amp r a)]
  rw [coeff_mul_X_pow']
  have hx : (amp r a * X).coeff j = if 1 ≤ j then (amp r a).coeff (j-1) else 0 := by simpa only [pow_one] using coeff_mul_X_pow' (amp r a) 1 j
  rw [hx]
  simp only [pow_one, amp_coeff_pad]
  push_cast
  cases j with
  | zero => simp [padded]
  | succ j =>
    cases j with
    | zero => simp [padded]
    | succ j =>
      have e1 : 1 ≤ j+1+1 := by omega
      have e2 : 2 ≤ j+1+1 := by omega
      rw [if_pos e1, if_pos e2]
      simp only [Nat.add_sub_cancel]
      have e3 : j+1+1-2+1 = j+1 := by omega
      rw [e3]

#print axioms resPoly_coeff
end
end GaussianRange

namespace GaussianRange
open Finset Polynomial
noncomputable section
variable {β : Type*} [Fintype β]

theorem residual_parseval_le (r : ℕ) (a : ℕ → ℝ) (d : ℝ) :
    (∑ j ∈ range (r+3), (h (padded r a) d j)^2) ≤
      Real.circleAverage (fun z => ‖(resPoly r a d).eval z‖^2) 0 1 := by
  rw [← Polynomial.sum_sq_norm_coeff_eq_circleAverage]
  have e : (∑ j ∈ range (r+3), (h (padded r a) d j)^2) =
      ∑ j ∈ range (r+3), ‖(resPoly r a d).coeff j‖^2 := by
    apply sum_congr rfl
    intro j _
    rw [resPoly_coeff, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [e]
  have hs : (∑ j ∈ range (r+3), ‖(resPoly r a d).coeff j‖^2) =
      ∑ j ∈ (range (r+3)).filter (fun j => j ∈ (resPoly r a d).support),
        ‖(resPoly r a d).coeff j‖^2 := by
    rw [sum_filter]
    apply sum_congr rfl
    intro j _
    split_ifs with hj
    · rfl
    · have hz : (resPoly r a d).coeff j = 0 := by simpa [Polynomial.mem_support_iff] using hj
      simp [hz]
  rw [hs]
  exact sum_le_sum_of_subset_of_nonneg (fun j hj => (mem_filter.mp hj).2)
    (fun j _ _ => sq_nonneg _)

#print axioms residual_parseval_le
end
end GaussianRange

namespace GaussianRange
open Finset Polynomial
open scoped BigOperators
noncomputable section
variable {β : Type*} [Fintype β]

def avg (f : ℂ → ℝ) : ℝ := Real.circleAverage f 0 1

theorem cont_weight (r : ℕ) (a : ℕ → ℝ) : Continuous (weight r a) := by
  unfold weight
  fun_prop

theorem cont_sigma (r : ℕ) (a : β → ℕ → ℝ) (T : β → ℝ) (c : ℝ) :
    Continuous (sigma r a T c) := by
  unfold sigma dispersion
  have hw (v : β) : Continuous (fun z => weight r (a v) z / T v) :=
    (cont_weight r (a v)).div_const _
  have hs : Continuous (fun z => ∑ v, weight r (a v) z / T v) :=
    continuous_finset_sum _ (fun v _ => hw v)
  fun_prop

theorem cont_residual (r : ℕ) (a : ℕ → ℝ) (d T : ℝ) :
    Continuous (fun z => ‖(resPoly r a d).eval z‖^2 / T) := by
  fun_prop

theorem norm_unit_of_mem (z : ℂ) (hz : z ∈ Metric.sphere (0:ℂ) |(1:ℝ)|) :
    ‖z‖ = 1 := by
  simpa [Metric.mem_sphere, dist_zero_right] using hz

theorem physical_entropy_lower (r : ℕ) (hr : 0 < r)
    (a : β → ℕ → ℝ) (T : β → ℝ) (c : ℝ) (hc : 2 < c)
    (ht : ∀ v, 0 < T v)
    (h0 : ∀ z : ℂ, ‖z‖ = 1 → ∑ v, weight r (a v) z = 1)
    (h1 : ∀ z : ℂ, ‖z‖ = 1 → ∑ v, T v * weight r (a v) z = dispersion c z) :
    1 ≤ (r:ℝ)^2*c*(c+2)*avg (sigma r a T c) := by
  have hlow := physical_residual_lower r hr a T c (by linarith) ht h0 h1
  let f := fun (v : β) (z : ℂ) => ‖(resPoly r (a v) (T v-c)).eval z‖^2 / T v
  have hA : H r (fun v => padded r (a v)) T c ≤ avg (fun z => ∑ v, f v z) := by
    unfold avg H
    rw [Real.circleAverage_fun_sum (fun v _ => (cont_residual r (a v) (T v-c) (T v)).continuousOn.circleIntegrable (by norm_num))]
    apply sum_le_sum
    intro v _
    have hp := div_le_div_of_nonneg_right (residual_parseval_le r (a v) (T v-c)) (ht v).le
    change _ ≤ Real.circleAverage (fun z => ‖(resPoly r (a v) (T v-c)).eval z‖^2 / T v) 0 1
    have he : Real.circleAverage (fun z => ‖(resPoly r (a v) (T v-c)).eval z‖^2 / T v) 0 1 =
        Real.circleAverage (fun z => ‖(resPoly r (a v) (T v-c)).eval z‖^2) 0 1 / T v := by
      simp_rw [div_eq_mul_inv, mul_comm _ (T v)⁻¹]
      exact Real.circleAverage_fun_smul (a := (T v)⁻¹)
    rw [he]
    exact hp
  have hB : avg (fun z => ∑ v, f v z) ≤ (c+2)*avg (sigma r a T c) := by
    unfold avg
    rw [← smul_eq_mul, ← Real.circleAverage_fun_smul]
    apply Real.circleAverage_mono
    · exact (continuous_finset_sum _ (fun v _ => cont_residual r (a v) (T v-c) (T v))).continuousOn.circleIntegrable (by norm_num)
    · exact ((cont_sigma r a T c).const_smul (c+2)).continuousOn.circleIntegrable (by norm_num)
    intro z hz
    have hzu := norm_unit_of_mem z hz
    have e := sigma_weighted_residual r a T c z hzu hc ht (h0 z hzu) (h1 z hzu)
    change (∑ v, ‖(resPoly r (a v) (T v-c)).eval z‖^2 / T v) ≤ (c+2)*sigma r a T c z
    rw [e]
    have hre := Complex.abs_re_le_norm z
    rw [hzu] at hre
    have hd : 0 < dispersion c z := by unfold dispersion; linarith [le_abs_self z.re]
    have hdup : dispersion c z ≤ c+2 := by unfold dispersion; linarith [neg_abs_le z.re]
    have hn : 0 ≤ dispersion c z * sigma r a T c z := by
      rw [← e]
      exact sum_nonneg (fun v _ => div_nonneg (sq_nonneg _) (ht v).le)
    have hsig : 0 ≤ sigma r a T c z := nonneg_of_mul_nonneg_right hn hd
    exact mul_le_mul_of_nonneg_right hdup hsig
  have hpos : 0 ≤ (r:ℝ)^2*c := by positivity
  have hC := mul_le_mul_of_nonneg_left (hA.trans hB) hpos
  calc
    1 ≤ (r:ℝ)^2*c*H r (fun v => padded r (a v)) T c := hlow
    _ ≤ (r:ℝ)^2*c*((c+2)*avg (sigma r a T c)) := hC
    _ = _ := by ring

#print axioms physical_entropy_lower
end
end GaussianRange

namespace GaussianRange
open Finset
noncomputable section

/-- A rational polynomial window, avoiding trigonometric normalization in
    the rate estimate. The spectral construction can use any real window. -/
def tentParabola (n j : ℕ) : ℝ :=
  if j < n then ((j:ℝ)+1)*((n:ℝ)-j) else 0

theorem tentParabola_nonneg (n j : ℕ) : 0 ≤ tentParabola n j := by
  unfold tentParabola
  split_ifs with hj
  · apply mul_nonneg (by positivity)
    exact sub_nonneg.mpr (by exact_mod_cast hj.le)
  · rfl

theorem window_energy_identity (n : ℕ) (g : ℕ → ℝ)
    (h0 : g 0 = 0) (hn : g (n+1) = 0) :
    (∑ j ∈ range (n+1), (g (j+1)-g j)^2) =
      2*(∑ j ∈ range (n+1), (g j)^2) -
      2*(∑ j ∈ range (n+1), g j*g (j+1)) := by
  have hs : (∑ j ∈ range (n+1), (g (j+1))^2) =
      ∑ j ∈ range (n+1), (g j)^2 := by
    have e : (∑ j ∈ range (n+2), (g j)^2) =
        (g 0)^2 + ∑ j ∈ range (n+1), (g (j+1))^2 := by rw [sum_range_succ']; ring
    rw [sum_range_succ, hn, h0] at e
    simpa using e.symm
  calc
    _ = ∑ j ∈ range (n+1), ((g (j+1))^2+(g j)^2-2*(g j*g (j+1))) := by
      apply sum_congr rfl
      intro j _
      ring
    _ = _ := by rw [sum_sub_distrib,sum_add_distrib,← mul_sum,hs]; ring

#print axioms window_energy_identity
end
end GaussianRange

namespace GaussianRange
open Finset
noncomputable section

theorem parabola_square_sum (n : ℕ) :
    (∑ j ∈ range n, (((j:ℝ)+1)*((n:ℝ)-j))^2) =
       (n:ℝ)*(n+1)*(n+2)*((n:ℝ)^2+2*n+2)/30 := by
  have h1 : (∑ j ∈ range n, (j:ℝ)) = (n:ℝ)*(n-1)/2 := by
    try clear h3
    try clear h2
    try clear h1
    induction n with
    | zero => simp
    | succ n ih =>
      rw [sum_range_succ, ih]
      push_cast
      ring
  have h2 : (∑ j ∈ range n, (j:ℝ)^2) = (n:ℝ)*(n-1)*(2*n-1)/6 := by
    try clear h3
    try clear h2
    try clear h1
    induction n with
    | zero => simp
    | succ n ih =>
      rw [sum_range_succ, ih]
      push_cast
      ring
  have h3 : (∑ j ∈ range n, (j:ℝ)^3) = (n:ℝ)^2*(n-1)^2/4 := by
    try clear h3
    try clear h2
    try clear h1
    induction n with
    | zero => simp
    | succ n ih =>
      rw [sum_range_succ, ih]
      push_cast
      ring
  have h4 : (∑ j ∈ range n, (j:ℝ)^4) =
      (n:ℝ)*(n-1)*(2*n-1)*(3*(n:ℝ)^2-3*n-1)/30 := by
    try clear h3
    try clear h2
    try clear h1
    induction n with
    | zero => simp
    | succ n ih =>
      rw [sum_range_succ, ih]
      push_cast
      ring
  calc
    _ = ∑ j ∈ range n, ((j:ℝ)^4 + (2-2*(n:ℝ))*(j:ℝ)^3 +
         ((n:ℝ)^2-4*n+1)*(j:ℝ)^2 + (2*(n:ℝ)^2-2*n)*(j:ℝ) + (n:ℝ)^2) := by
      apply sum_congr rfl
      intro j _
      ring
    _ = _ := by
      simp only [sum_add_distrib, ← mul_sum, sum_const, card_range, nsmul_eq_mul]
      rw [h1,h2,h3,h4]
      ring

theorem rational_window_upper_constant (m L : ℝ) (hm : 0<m)
    (hL : 10+20/m ≤ L) :
    10*(2*L-5)/(m*(L-5)*(m*(L-5)-10)) ≤ 80/(m^2*L) := by
  have hh : 20 ≤ m*(L-10) := by
    have e := (div_le_iff₀ hm).mp (show 20/m ≤ L-10 by linarith)
    linarith
  have hLp : 0<L := by linarith [show 0<20/m by positivity]
  have ha : L/2 ≤ L-5 := by linarith [show 0<20/m by positivity]
  have hb : m*L/2 ≤ m*(L-5)-10 := by nlinarith
  have hp : 0<m*(L-5)*(m*(L-5)-10) := mul_pos (mul_pos hm (by linarith)) (lt_of_lt_of_le (by positivity : 0 < m*L/2) hb)
  have hq : 0<m^2*L := by positivity
  apply (div_le_div_iff₀ hp hq).2
  have hmul := mul_le_mul ha hb (by positivity : 0≤m*L/2) (by linarith : 0≤L-5)
  have hmul2 := mul_le_mul_of_nonneg_left hmul (show 0≤80*m by positivity)
  have hh3 := mul_nonneg (show 0 ≤ 50*m^2*L by positivity) (show 0 ≤ (1:ℝ) by norm_num)
  nlinarith

#print axioms parabola_square_sum
#print axioms rational_window_upper_constant
end
end GaussianRange

namespace GaussianRange
open Finset
noncomputable section

theorem parabola_adjacent_sum (n : ℕ) :
    (∑ j ∈ range n, (((j:ℝ)+1)*((n:ℝ)-j))*(((j:ℝ)+2)*((n:ℝ)-j-1))) =
       (n:ℝ)*(n+1)*(n+2)*((n:ℝ)^2+2*n-3)/30 := by
  have h1 : ∀ k : ℕ, (∑ j ∈ range k, (j:ℝ)) = (k:ℝ)*(k-1)/2 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [sum_range_succ, ih]; push_cast; ring
  have h2 : ∀ k : ℕ, (∑ j ∈ range k, (j:ℝ)^2) = (k:ℝ)*(k-1)*(2*k-1)/6 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [sum_range_succ, ih]; push_cast; ring
  have h3 : ∀ k : ℕ, (∑ j ∈ range k, (j:ℝ)^3) = (k:ℝ)^2*(k-1)^2/4 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [sum_range_succ, ih]; push_cast; ring
  have h4 : ∀ k : ℕ, (∑ j ∈ range k, (j:ℝ)^4) =
      (k:ℝ)*(k-1)*(2*k-1)*(3*(k:ℝ)^2-3*k-1)/30 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [sum_range_succ, ih]; push_cast; ring
  calc
    _ = ∑ j ∈ range n, ((j:ℝ)^4 + (4-2*(n:ℝ))*(j:ℝ)^3 +
         ((n:ℝ)^2-7*n+5)*(j:ℝ)^2 + (3*(n:ℝ)^2-7*n+2)*(j:ℝ) +
         (2*(n:ℝ)^2-2*n)) := by
      apply sum_congr rfl
      intro j _
      ring
    _ = _ := by
      simp only [sum_add_distrib, ← mul_sum, sum_const, card_range, nsmul_eq_mul]
      rw [h1,h2,h3,h4]
      ring

def rationalRho (n : ℕ) : ℝ := 1-5/((n:ℝ)^2+2*n+2)

theorem rationalRho_pos (n : ℕ) (hn : 2 ≤ n) : 0 < rationalRho n := by
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hL : 5 < (n:ℝ)^2+2*n+2 := by nlinarith
  unfold rationalRho
  apply sub_pos.mpr
  apply (div_lt_iff₀ (by linarith : 0 < (n:ℝ)^2+2*n+2)).2
  linarith

theorem rational_temperature_floor (m L : ℝ) (hm : 0<m)
    (hL : 5+20/m ≤ L) :
    m/2 ≤ m-10/(L-5) := by
  have hp : 0<L-5 := by linarith [show 0<20/m by positivity]
  have h := (div_le_iff₀ hm).mp (show 20/m ≤ L-5 by linarith)
  have h' : 10/(L-5) ≤ m/2 := (div_le_iff₀ hp).2 (by nlinarith)
  linarith

#print axioms parabola_adjacent_sum
#print axioms rationalRho_pos
#print axioms rational_temperature_floor
end
end GaussianRange

namespace GaussianRange
open Finset Polynomial AddChar
noncomputable section

theorem cyclic_char_sum (N : ℕ) [NeZero N] (t : ZMod N) :
    (∑ i : ZMod N, ZMod.stdAddChar (t*i)) = if t = 0 then (N:ℂ) else 0 := by
  split_ifs with h
  · simp only [h, zero_mul, map_zero_eq_one, sum_const, card_univ, ZMod.card,
      nsmul_eq_mul, mul_one]
  · exact sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar N h)

def cyclicRe (N : ℕ) [NeZero N] (l j : ZMod N) : ℝ :=
  (ZMod.stdAddChar (j*l)).re

def cyclicIm (N : ℕ) [NeZero N] (l j : ZMod N) : ℝ :=
  (ZMod.stdAddChar (j*l)).im

theorem cyclicRe_sum (N : ℕ) [NeZero N] (t : ZMod N) :
    (∑ l : ZMod N, cyclicRe N l t) = if t = 0 then (N:ℝ) else 0 := by
  unfold cyclicRe
  have h := congrArg Complex.re (cyclic_char_sum N t)
  rw [Complex.re_sum] at h
  split_ifs at h ⊢ <;> simpa using h

theorem rational_window_ratio (n : ℕ) (hn : 2 ≤ n) :
    (∑ j ∈ range n, (((j:ℝ)+1)*((n:ℝ)-j))*(((j:ℝ)+2)*((n:ℝ)-j-1))) /
      (∑ j ∈ range n, (((j:ℝ)+1)*((n:ℝ)-j))^2) = rationalRho n := by
  rw [parabola_adjacent_sum,parabola_square_sum]
  unfold rationalRho
  have h : (0:ℝ) < n := by exact_mod_cast (show 0<n by omega)
  have h1 : (0:ℝ) < (n:ℝ)+1 := by positivity
  have h2 : (0:ℝ) < (n:ℝ)+2 := by positivity
  have h3 : (0:ℝ) < (n:ℝ)^2+2*n+2 := by positivity
  field_simp
  <;> ring

#print axioms cyclic_char_sum
#print axioms cyclicRe_sum
#print axioms rational_window_ratio
end
end GaussianRange

namespace GaussianRange
open Finset Polynomial AddChar
noncomputable section

def realChannel (N : ℕ) [NeZero N] (g : ℕ → ℝ)
    (v : ZMod N × Bool) (j : ℕ) : ℝ :=
  g j * (if v.2 then cyclicRe N v.1 (j : ZMod N)
         else cyclicIm N v.1 (j : ZMod N)) / Real.sqrt N

def channelTemp (N : ℕ) [NeZero N] (c rho : ℝ) (v : ZMod N × Bool) : ℝ :=
  c - 2 * cyclicRe N v.1 1 / rho

theorem char_unit_norm (N : ℕ) [NeZero N] (j : ZMod N) :
    ‖ZMod.stdAddChar j‖ = 1 := by
  rw [ZMod.stdAddChar_apply]
  exact Circle.norm_coe (ZMod.toCircle j)

theorem cyclicRe_le_one (N : ℕ) [NeZero N] (l j : ZMod N) :
    cyclicRe N l j ≤ 1 := by
  unfold cyclicRe
  calc
    _ ≤ |(ZMod.stdAddChar (j*l)).re| := le_abs_self _
    _ ≤ ‖ZMod.stdAddChar (j*l)‖ := Complex.abs_re_le_norm _
    _ = 1 := char_unit_norm N _

theorem channelTemp_lower (N : ℕ) [NeZero N] (c rho : ℝ) (hrho : 0<rho)
    (v : ZMod N × Bool) : c-2/rho ≤ channelTemp N c rho v := by
  unfold channelTemp
  have h := cyclicRe_le_one N v.1 1
  have h' : 2*cyclicRe N v.1 1/rho ≤ 2/rho :=
    div_le_div_of_nonneg_right (by linarith) hrho.le
  linarith

theorem channelTemp_zero (N : ℕ) [NeZero N] (c rho : ℝ) :
    channelTemp N c rho (0,true) = c-2/rho := by
  simp [channelTemp,cyclicRe,map_zero_eq_one]

theorem channelTemp_pos_iff (N : ℕ) [NeZero N] (c rho : ℝ) (hrho : 0<rho) :
    (∀ v : ZMod N × Bool, 0<channelTemp N c rho v) ↔ 2/rho<c := by
  constructor
  · intro h
    have e := h (0,true)
    rw [channelTemp_zero] at e
    linarith
  · intro h v
    exact lt_of_lt_of_le (by linarith : 0<c-2/rho) (channelTemp_lower N c rho hrho v)

theorem char_conj_neg (N : ℕ) [NeZero N] (t : ZMod N) :
    star (ZMod.stdAddChar t) = ZMod.stdAddChar (-t) := by
  have h : ZMod.stdAddChar t * ZMod.stdAddChar (-t) = 1 := by
    rw [← map_add_eq_mul, add_neg_cancel, map_zero_eq_one]
  have h' : ZMod.stdAddChar t * star (ZMod.stdAddChar t) = 1 := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, char_unit_norm]
    norm_num
  exact mul_left_cancel₀ (norm_ne_zero_iff.mp (by rw [char_unit_norm]; norm_num)) (h'.trans h.symm)

theorem cyclic_pair (N : ℕ) [NeZero N] (l i j : ZMod N) :
    cyclicRe N l i * cyclicRe N l j + cyclicIm N l i * cyclicIm N l j =
      cyclicRe N l (i-j) := by
  unfold cyclicRe cyclicIm
  have e : ZMod.stdAddChar ((i-j)*l) =
      ZMod.stdAddChar (i*l) * star (ZMod.stdAddChar (j*l)) := by
    rw [char_conj_neg, ← map_add_eq_mul]
    congr 1
    ring
  rw [e,Complex.mul_re,Complex.star_def,Complex.conj_re,Complex.conj_im]
  ring

theorem cyclicRe_product (N : ℕ) [NeZero N] (l i j : ZMod N) :
    2*cyclicRe N l i*cyclicRe N l j =
      cyclicRe N l (i+j)+cyclicRe N l (i-j) := by
  have e := cyclic_pair N l i j
  unfold cyclicRe cyclicIm at *
  rw [add_mul,map_add_eq_mul,Complex.mul_re]
  linarith

#print axioms channelTemp_pos_iff
#print axioms cyclic_pair
#print axioms cyclicRe_product
end
end GaussianRange

namespace GaussianRange
open Finset Polynomial AddChar
noncomputable section

theorem channel_pair_sum (N : ℕ) [NeZero N] (g : ℕ → ℝ)
    (l : ZMod N) (i j : ℕ) :
    (∑ b : Bool, realChannel N g (l,b) i * realChannel N g (l,b) j) =
      g i*g j*cyclicRe N l ((i:ZMod N)-(j:ZMod N))/N := by
  have hN : 0 < (N:ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne N))
  have hs := Real.sq_sqrt hN.le
  have hp := cyclic_pair N l (i:ZMod N) (j:ZMod N)
  simp [realChannel, Fintype.sum_bool]
  calc
    _ = g i*g j*(cyclicRe N l (i:ZMod N)*cyclicRe N l (j:ZMod N) +
       cyclicIm N l (i:ZMod N)*cyclicIm N l (j:ZMod N))/(Real.sqrt N)^2 := by ring
    _ = _ := by rw [hp,hs]

theorem channel_gram (N : ℕ) [NeZero N] (g : ℕ → ℝ) (i j : ℕ) :
    (∑ v : ZMod N × Bool, realChannel N g v i * realChannel N g v j) =
       if (i:ZMod N) = (j:ZMod N) then g i*g j else 0 := by
  rw [Fintype.sum_prod_type]
  simp_rw [channel_pair_sum]
  simp_rw [div_eq_mul_inv]
  rw [← sum_mul,← mul_sum,cyclicRe_sum]
  have hN : (N:ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne N)
  by_cases h : (i:ZMod N) = (j:ZMod N)
  · simp [h,hN]
  · simp [sub_ne_zero.mpr h,h]

theorem channel_weighted_gram (N : ℕ) [NeZero N] (g : ℕ → ℝ)
    (c rho : ℝ) (i j : ℕ) :
    (∑ v : ZMod N × Bool, channelTemp N c rho v *
      (realChannel N g v i * realChannel N g v j)) =
      c*(if (i:ZMod N)=(j:ZMod N) then g i*g j else 0) -
      (g i*g j/rho)*
      ((if (i:ZMod N)-(j:ZMod N)+1=0 then 1 else 0) +
       (if (i:ZMod N)-(j:ZMod N)-1=0 then 1 else 0)) := by
  rw [Fintype.sum_prod_type]
  have hN : (N:ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne N)
  simp only [channelTemp,Prod.fst, ← mul_sum, channel_pair_sum]
  calc
    _ = ∑ l : ZMod N,
       (c*(g i*g j*cyclicRe N l ((i:ZMod N)-(j:ZMod N))/N) -
        (g i*g j/(rho*N))*(cyclicRe N l (((i:ZMod N)-(j:ZMod N))+1)+
         cyclicRe N l (((i:ZMod N)-(j:ZMod N))-1))) := by
      apply sum_congr rfl
      intro l _
      rw [← cyclicRe_product]
      ring
    _ = _ := by
      simp only [sum_sub_distrib,sum_add_distrib,div_eq_mul_inv,← sum_mul,← mul_sum,cyclicRe_sum]
      split_ifs <;> simp_all [sub_eq_zero] <;> field_simp <;> ring

#print axioms channel_pair_sum
#print axioms channel_gram
#print axioms channel_weighted_gram
end
end GaussianRange

namespace GaussianRange
open Finset Polynomial
noncomputable section
variable {β : Type*} [Fintype β]

theorem weighted_spectral_expand (r : ℕ) (a : β → ℕ → ℝ)
    (T : β → ℝ) (z : ℂ) :
    (∑ v, (T v : ℂ)*((amp r (a v)).eval z)*((rev r (a v)).eval z)) =
      ∑ i ∈ range (r+1), ∑ j ∈ range (r+1),
        ((∑ v, T v * (a v i * a v j) : ℝ):ℂ) * (z^j*z^(r-i)) := by
  simp only [amp_eval,rev_eval,mul_sum,sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  push_cast
  rw [sum_mul]
  apply sum_congr rfl
  intro v _
  ring

theorem no_alias_eq (r i j : ℕ) (hi : i≤r) (hj : j≤r) :
    ((i:ZMod (2*r+5)) = (j:ZMod (2*r+5))) ↔ i=j := by
  constructor
  · intro h
    have e := congrArg ZMod.val h
    rw [ZMod.val_natCast,ZMod.val_natCast,Nat.mod_eq_of_lt (by omega : i<2*r+5),
      Nat.mod_eq_of_lt (by omega : j<2*r+5)] at e
    exact e
  · rintro rfl
    rfl

theorem physical_channel_normalization (r : ℕ) (g : ℕ → ℝ)
    (hg : ∑ j ∈ range (r+1), (g j)^2 = 1)
    (z : ℂ) (hz : ‖z‖=1) :
    (∑ v : ZMod (2*r+5) × Bool, weight r (realChannel (2*r+5) g v) z) = 1 := by
  let a := realChannel (2*r+5) g
  have e := weighted_spectral_expand r a (fun _ => 1) z
  simp only [Complex.ofReal_one,one_mul] at e
  dsimp [a] at e
  simp_rw [channel_gram] at e
  have rhs : (∑ i ∈ range (r+1), ∑ j ∈ range (r+1),
       ((if (i:ZMod (2*r+5))=(j:ZMod (2*r+5)) then g i*g j else 0 : ℝ):ℂ) *
       (z^j*z^(r-i))) = z^r := by
    calc
      _ = ∑ i ∈ range (r+1), ((g i)^2 : ℝ) * (z^r) := by
        apply sum_congr rfl
        intro i hi
        have hi' : i≤r := by simpa using mem_range.mp hi
        have hh : ∀ j ∈ range (r+1), (((if (i:ZMod (2*r+5))=(j:ZMod (2*r+5)) then g i*g j else 0 : ℝ):ℂ) *
          (z^j*z^(r-i))) = if i=j then ((g i)^2 : ℝ) * z^r else 0 := by
          intro j hj
          have hj' : j≤r := by simpa using mem_range.mp hj
          simp only [no_alias_eq r i j hi' hj']
          split_ifs with he
          · subst j
            rw [← pow_add, Nat.add_sub_of_le hi']
            push_cast
            ring
          · simp
        rw [sum_congr rfl hh,sum_ite_eq,if_pos hi]
      _ = _ := by rw [← sum_mul,← Complex.ofReal_sum,hg]; simp
  rw [rhs] at e
  have hspec (v : ZMod (2*r+5) × Bool) :
      (amp r (a v)).eval z * (rev r (a v)).eval z = z^r*(weight r (a v) z : ℂ) := by
    rw [← eval_mul,spectral_eval r (a v) z hz]
    rfl
  dsimp [a] at hspec
  simp_rw [hspec] at e
  rw [← mul_sum,← Complex.ofReal_sum] at e
  have hzn : z^r ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mp (by rw [hz]; norm_num))
  have he := mul_left_cancel₀ hzn (e.trans (mul_one _).symm)
  exact_mod_cast he

#print axioms weighted_spectral_expand
#print axioms no_alias_eq
#print axioms physical_channel_normalization
end
end GaussianRange

namespace GaussianRange
open Finset Polynomial
noncomputable section

theorem no_alias_succ (r i j : ℕ) (hi : i≤r) (hj : j≤r) :
    ((i:ZMod (2*r+5))-(j:ZMod (2*r+5))+1=0) ↔ i+1=j := by
  have e : ((i:ZMod (2*r+5))-(j:ZMod (2*r+5))+1=0) ↔
      ((i+1:ℕ):ZMod (2*r+5))=(j:ZMod (2*r+5)) := by
    push_cast
    constructor <;> intro h <;> linear_combination h
  rw [e]
  constructor
  · intro h
    have h' := congrArg ZMod.val h
    rw [ZMod.val_natCast,ZMod.val_natCast,Nat.mod_eq_of_lt (by omega : i+1<2*r+5),
      Nat.mod_eq_of_lt (by omega : j<2*r+5)] at h'
    exact h'
  · intro h
    rw [h]

theorem no_alias_pred (r i j : ℕ) (hi : i≤r) (hj : j≤r) :
    ((i:ZMod (2*r+5))-(j:ZMod (2*r+5))-1=0) ↔ j+1=i := by
  have h := no_alias_succ r j i hj hi
  rw [← h]
  constructor <;> intro e <;> linear_combination -e

theorem adjacent_spectrum_forward (r : ℕ) (g : ℕ → ℝ) (z : ℂ) :
    (∑ i ∈ range (r+1), ∑ j ∈ range (r+1),
      (if i+1=j then ((g i*g j:ℝ):ℂ)*(z^j*z^(r-i)) else 0)) =
      ((∑ i ∈ range r,g i*g (i+1):ℝ):ℂ)*z^(r+1) := by
  rw [sum_range_succ]
  have he : (∑ j ∈ range (r+1), if r+1=j then
      ((g r*g j:ℝ):ℂ)*(z^j*z^(r-r)) else 0) = 0 := by
    apply sum_eq_zero
    intro j hj
    rw [if_neg (by have := mem_range.mp hj; omega)]
  rw [he,add_zero]
  calc
    _ = ∑ i ∈ range r, ((g i*g (i+1):ℝ):ℂ)*z^(r+1) := by
      apply sum_congr rfl
      intro i hi
      rw [sum_ite_eq,if_pos (by have := mem_range.mp hi; exact mem_range.mpr (by omega))]
      rw [← pow_add]
      congr 2
      have := mem_range.mp hi
      omega
    _ = _ := by rw [← sum_mul,Complex.ofReal_sum]

theorem adjacent_spectrum_backward (r : ℕ) (g : ℕ → ℝ) (z : ℂ) :
    (∑ i ∈ range (r+1), ∑ j ∈ range (r+1),
      (if j+1=i then ((g i*g j:ℝ):ℂ)*(z^j*z^(r-i)) else 0)) =
      ((∑ i ∈ range r,g i*g (i+1):ℝ):ℂ)*z^(r-1) := by
  rw [sum_comm,sum_range_succ]
  have he : (∑ i ∈ range (r+1), if r+1=i then
      ((g i*g r:ℝ):ℂ)*(z^r*z^(r-i)) else 0) = 0 := by
    apply sum_eq_zero
    intro i hi
    rw [if_neg (by have := mem_range.mp hi; omega)]
  rw [he,add_zero]
  calc
    _ = ∑ j ∈ range r, ((g j*g (j+1):ℝ):ℂ)*z^(r-1) := by
      apply sum_congr rfl
      intro j hj
      rw [sum_ite_eq,if_pos (by have := mem_range.mp hj; exact mem_range.mpr (by omega))]
      rw [← pow_add]
      have e : j+(r-(j+1))=r-1 := by have := mem_range.mp hj; omega
      rw [e]
      push_cast
      ring
    _ = _ := by rw [← sum_mul,Complex.ofReal_sum]

#print axioms no_alias_succ
#print axioms no_alias_pred
#print axioms adjacent_spectrum_forward
#print axioms adjacent_spectrum_backward
end
end GaussianRange

namespace GaussianRange
open Finset Polynomial
noncomputable section

theorem channel_weighted_spectral (r : ℕ) (g : ℕ → ℝ) (c rho : ℝ)
    (hρ : rho ≠ 0)
    (hg : ∑ j ∈ range (r+1), (g j)^2 = 1)
    (hb : ∑ j ∈ range r, g j*g (j+1) = rho)
    (z : ℂ) :
    (∑ v : ZMod (2*r+5) × Bool,
      (channelTemp (2*r+5) c rho v : ℂ) *
      ((amp r (realChannel (2*r+5) g v)).eval z) *
      ((rev r (realChannel (2*r+5) g v)).eval z)) =
        (c:ℂ)*z^r-z^(r+1)-z^(r-1) := by
  rw [weighted_spectral_expand]
  simp_rw [channel_weighted_gram]
  have hsplit : ∀ i ∈ range (r+1), ∀ j ∈ range (r+1),
      ((c*(if (i:ZMod (2*r+5))=(j:ZMod (2*r+5)) then g i*g j else 0) -
      (g i*g j/rho)*
      ((if (i:ZMod (2*r+5))-(j:ZMod (2*r+5))+1=0 then 1 else 0) +
       (if (i:ZMod (2*r+5))-(j:ZMod (2*r+5))-1=0 then 1 else 0)) : ℝ)) = 
      c*(if i=j then g i*g j else 0) -
      (if i+1=j then g i*g j else 0)/rho -
      (if j+1=i then g i*g j else 0)/rho := by
    intro i hi j hj
    have hi' : i≤r := by have := mem_range.mp hi; omega
    have hj' : j≤r := by have := mem_range.mp hj; omega
    simp only [no_alias_eq r i j hi' hj',no_alias_succ r i j hi' hj',
      no_alias_pred r i j hi' hj']
    split_ifs <;> ring
  have e : (∑ i ∈ range (r+1), ∑ j ∈ range (r+1),
      ((if i=j then g i*g j else 0 : ℝ):ℂ)*(z^j*z^(r-i))) = z^r := by
    calc
      _ = ∑ i ∈ range (r+1), ((g i)^2:ℝ)*z^r := by
        apply sum_congr rfl
        intro i hi
        have h : ∀ j ∈ range (r+1),
          ((if i=j then g i*g j else 0 : ℝ):ℂ)*(z^j*z^(r-i)) =
            if i=j then ((g i)^2:ℝ)*z^r else 0 := by
          intro j _
          split_ifs with he
          · subst j
            rw [← pow_add, Nat.add_sub_of_le (by have := mem_range.mp hi; omega)]
            push_cast
            ring
          · simp
        rw [sum_congr rfl h,sum_ite_eq,if_pos hi]
      _ = _ := by rw [← sum_mul,← Complex.ofReal_sum,hg]; simp
  have f := adjacent_spectrum_forward r g z
  have b := adjacent_spectrum_backward r g z

  calc
    _ = ∑ i ∈ range (r+1), ∑ j ∈ range (r+1),
      ((c:ℂ)*((if i=j then g i*g j else 0 : ℝ):ℂ)*(z^j*z^(r-i)) -
      ((if i+1=j then ((g i*g j:ℝ):ℂ)*(z^j*z^(r-i)) else 0))/(rho:ℂ) -
      ((if j+1=i then ((g i*g j:ℝ):ℂ)*(z^j*z^(r-i)) else 0))/(rho:ℂ)) := by
        apply sum_congr rfl
        intro i hi
        apply sum_congr rfl
        intro j hj
        rw [hsplit i hi j hj]
        push_cast
        split_ifs <;> push_cast <;> ring
    _ = _ := by
      simp only [sum_sub_distrib, mul_assoc (c:ℂ),← mul_sum,← sum_div]
      rw [e,adjacent_spectrum_forward,adjacent_spectrum_backward,hb]
      have h : (rho:ℂ) ≠ 0 := by exact_mod_cast hρ
      field_simp
      <;> ring

theorem physical_channel_weighted_normalization (r : ℕ) (hr : 0<r)
    (g : ℕ → ℝ) (c rho : ℝ) (hρ : rho ≠ 0)
    (hg : ∑ j ∈ range (r+1), (g j)^2 = 1)
    (hb : ∑ j ∈ range r, g j*g (j+1) = rho)
    (z : ℂ) (hz : ‖z‖=1) :
    (∑ v : ZMod (2*r+5) × Bool,
      channelTemp (2*r+5) c rho v * weight r (realChannel (2*r+5) g v) z) =
        dispersion c z := by
  have e := channel_weighted_spectral r g c rho hρ hg hb z
  have hspec (v : ZMod (2*r+5) × Bool) :
      (amp r (realChannel (2*r+5) g v)).eval z *
      (rev r (realChannel (2*r+5) g v)).eval z =
      z^r*(weight r (realChannel (2*r+5) g v) z : ℂ) := by
    rw [← eval_mul,spectral_eval _ _ _ hz]
    rfl
  simp_rw [mul_assoc,hspec,← mul_assoc, mul_comm (channelTemp (2*r+5) c rho _ : ℂ) (z^r),mul_assoc] at e
  rw [← mul_sum] at e
  have hzz : z * star z = 1 := by
    rw [Complex.star_def,Complex.mul_conj,Complex.normSq_eq_norm_sq,hz]
    norm_num
  have hzback : z^(r-1) = z^r*star z := by
    calc
      _ = z^(r-1)*1 := by ring
      _ = z^(r-1)*(z*star z) := by rw [hzz]
      _ = _ := by rw [← mul_assoc,← pow_succ,Nat.sub_add_cancel (by omega : 1≤r)]
  rw [pow_succ,hzback] at e
  have he : z^r*((∑ v : ZMod (2*r+5) × Bool,
      channelTemp (2*r+5) c rho v * weight r (realChannel (2*r+5) g v) z : ℝ):ℂ)
       = z^r*((dispersion c z:ℝ):ℂ) := by
    push_cast
    rw [e]
    unfold dispersion
    have hreal : z+star z = ((2*z.re:ℝ):ℂ) := by
      apply Complex.ext <;> simp [Complex.star_def] <;> ring
    push_cast
    calc
      _ = z^r*((c:ℂ)-(z+star z)) := by ring
      _ = _ := by rw [hreal]; push_cast; ring
  have hzn : z^r ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mp (by rw [hz]; norm_num))
  exact_mod_cast (mul_left_cancel₀ hzn he)

#print axioms channel_weighted_spectral
#print axioms physical_channel_weighted_normalization
end
end GaussianRange

namespace GaussianRange
open Finset Polynomial
noncomputable section

def rawWindow (n j : ℕ) : ℝ := ((j:ℝ)+1)*((n:ℝ)-j)
def windowNorm (n : ℕ) : ℝ := ∑ j ∈ range n, (rawWindow n j)^2
def rationalWindow (n j : ℕ) : ℝ := rawWindow n j / Real.sqrt (windowNorm n)
def windowL (n : ℕ) : ℝ := (n:ℝ)^2+2*n+2

theorem windowNorm_pos (n : ℕ) (hn : 2≤n) : 0 < windowNorm n := by
  unfold windowNorm rawWindow
  rw [parabola_square_sum]
  have h : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  positivity

theorem rationalWindow_norm (n : ℕ) (hn : 2≤n) :
    ∑ j ∈ range n, (rationalWindow n j)^2 = 1 := by
  simp only [rationalWindow, div_pow, Real.sq_sqrt (windowNorm_pos n hn).le]
  rw [← sum_div]
  change windowNorm n / windowNorm n = 1
  exact div_self (windowNorm_pos n hn).ne'

theorem rationalWindow_correlation (r : ℕ) (hr : 0<r) :
    ∑ j ∈ range r, rationalWindow (r+1) j * rationalWindow (r+1) (j+1) =
      rationalRho (r+1) := by
  have hn : 2≤r+1 := by omega
  have hp := windowNorm_pos (r+1) hn
  have hmul (j : ℕ) :
    rationalWindow (r+1) j * rationalWindow (r+1) (j+1) =
    (rawWindow (r+1) j * rawWindow (r+1) (j+1))/windowNorm (r+1) := by
      unfold rationalWindow
      rw [div_mul_div_comm, ← pow_two, Real.sq_sqrt hp.le]
  simp_rw [hmul]
  rw [← sum_div]
  have hlast : rawWindow (r+1) (r+1) = 0 := by simp [rawWindow]
  have he : (∑ j ∈ range (r+1), rawWindow (r+1) j * rawWindow (r+1) (j+1)) =
      ∑ j ∈ range r, rawWindow (r+1) j * rawWindow (r+1) (j+1) := by
    rw [sum_range_succ, hlast]
    simp
  rw [← he]
  have hnum : (∑ j ∈ range (r+1), rawWindow (r+1) j * rawWindow (r+1) (j+1)) =
      ∑ j ∈ range (r+1), (((j:ℝ)+1)*(((r+1:ℕ):ℝ)-j))*(((j:ℝ)+2)*(((r+1:ℕ):ℝ)-j-1)) := by
    apply sum_congr rfl
    intro j _
    unfold rawWindow
    push_cast
    ring
  rw [hnum]
  exact rational_window_ratio (r+1) hn
theorem rationalTemp_min_formula (r : ℕ) (hr : 0<r) (m : ℝ) :
    m+2-2/rationalRho (r+1) = m-10/(windowL (r+1)-5) := by
  have hn : (2:ℝ)≤(r+1:ℕ) := by exact_mod_cast (show 2≤r+1 by omega)
  have hp : 0<windowL (r+1)-5 := by unfold windowL; nlinarith
  have hq : 0<windowL (r+1) := by linarith
  change m+2-2/(1-5/windowL (r+1)) = _
  field_simp
  <;> ring

theorem rationalTemp_pos_iff (r : ℕ) (hr : 0<r) (m : ℝ) (hm : 0<m) :
    (∀ v : ZMod (2*r+5) × Bool,
      0<channelTemp (2*r+5) (m+2) (rationalRho (r+1)) v) ↔
      5+10/m < windowL (r+1) := by
  have hn : 2≤r+1 := by omega
  have hρ := rationalRho_pos (r+1) hn
  rw [channelTemp_pos_iff _ _ _ hρ]
  have hf := rationalTemp_min_formula r hr m
  have hnr : (2:ℝ)≤(r+1:ℕ) := by exact_mod_cast hn
  have hp : 0<windowL (r+1)-5 := by unfold windowL; nlinarith
  constructor
  · intro h
    have hh : 10/(windowL (r+1)-5)<m := by linarith
    have hh' := (div_lt_iff₀ hp).mp hh
    have hh'' := (div_lt_iff₀ hm).mpr (show 10<(windowL (r+1)-5)*m by linarith)
    linarith
  · intro h
    have hh := (div_lt_iff₀ hm).mp (show 10/m<windowL (r+1)-5 by linarith)
    have hh' := (div_lt_iff₀ hp).mpr (show 10<m*(windowL (r+1)-5) by linarith)
    linarith

theorem rational_physical_realization (r : ℕ) (hr : 0<r) (m : ℝ) (hm : 0<m)
    (hL : 5+10/m < windowL (r+1)) :
    (∀ v : ZMod (2*r+5) × Bool,
      0<channelTemp (2*r+5) (m+2) (rationalRho (r+1)) v) ∧
    (∀ z : ℂ, ‖z‖=1 →
      (∑ v : ZMod (2*r+5) × Bool, weight r (realChannel (2*r+5) (rationalWindow (r+1)) v) z)=1) ∧
    (∀ z : ℂ, ‖z‖=1 →
      (∑ v : ZMod (2*r+5) × Bool,
        channelTemp (2*r+5) (m+2) (rationalRho (r+1)) v *
        weight r (realChannel (2*r+5) (rationalWindow (r+1)) v) z)=dispersion (m+2) z) := by
  have hn : 2≤r+1 := by omega
  have hg := rationalWindow_norm (r+1) hn
  have hb := rationalWindow_correlation r hr
  exact ⟨(rationalTemp_pos_iff r hr m hm).2 hL,
    physical_channel_normalization r _ hg,
    physical_channel_weighted_normalization r hr _ _ _ (rationalRho_pos _ hn).ne' hg hb⟩

#print axioms rationalWindow_norm
#print axioms rationalWindow_correlation
#print axioms rationalTemp_min_formula
#print axioms rationalTemp_pos_iff
#print axioms rational_physical_realization
end
end GaussianRange

namespace GaussianRange
open Finset Polynomial
noncomputable section

theorem avg_weight_parseval (r : ℕ) (a : ℕ → ℝ) :
    avg (weight r a) = ∑ j ∈ range (r+1), (a j)^2 := by
  unfold avg weight
  rw [← Polynomial.sum_sq_norm_coeff_eq_circleAverage]
  have hs : (amp r a).support ⊆ range (r+1) := by
    intro j hj
    have hn : (amp r a).coeff j ≠ 0 := Polynomial.mem_support_iff.mp hj
    by_contra h
    have h' : ¬j≤r := by simpa using h
    rw [amp_coeff, if_neg h'] at hn
    exact hn rfl
  calc
    _ = ∑ j ∈ range (r+1), ‖(amp r a).coeff j‖^2 := by
      apply sum_subset hs
      intro j _ hj
      have h : (amp r a).coeff j = 0 := by simpa [Polynomial.mem_support_iff] using hj
      simp [h]
    _ = _ := by
      apply sum_congr rfl
      intro j hj
      have h : j≤r := by have := mem_range.mp hj; omega
      rw [amp_coeff,if_pos h,Complex.norm_real,Real.norm_eq_abs,sq_abs]

theorem rational_channel_count (r : ℕ) :
    Fintype.card (ZMod (2*r+5) × Bool) = 4*r+10 := by
  simp
  omega

theorem rational_channel_floor (r : ℕ) (hr : 0<r) (m : ℝ) (hm : 0<m)
    (hL : 5+20/m ≤ windowL (r+1)) (v : ZMod (2*r+5) × Bool) :
    m/2 ≤ channelTemp (2*r+5) (m+2) (rationalRho (r+1)) v := by
  have hp := rationalRho_pos (r+1) (by omega)
  have h := channelTemp_lower (2*r+5) (m+2) (rationalRho (r+1)) hp v
  rw [rationalTemp_min_formula r hr m] at h
  exact (rational_temperature_floor m (windowL (r+1)) hm hL).trans h

#print axioms avg_weight_parseval
#print axioms rational_channel_count
#print axioms rational_channel_floor
end
end GaussianRange

namespace GaussianRange
open Finset Polynomial
noncomputable section

theorem paired_average_weight (r : ℕ) (g : ℕ → ℝ)
    (hg : ∑ j ∈ range (r+1), (g j)^2 = 1)
    (l : ZMod (2*r+5)) :
    (∑ b : Bool, avg (weight r (realChannel (2*r+5) g (l,b)))) =
      1/(2*r+5:ℝ) := by
  simp_rw [avg_weight_parseval, pow_two]
  rw [sum_comm]
  simp_rw [channel_pair_sum, sub_self, cyclicRe]
  simp only [zero_mul]
  have hz : (ZMod.stdAddChar (0 : ZMod (2*r+5))).re = 1 := by simpa [cyclicRe] using (show cyclicRe (2*r+5) 0 0 = 1 by simp [cyclicRe])
  simp only [hz,mul_one]
  rw [← sum_div]
  have he : (∑ j ∈ range (r+1), g j*g j) = 1 := by simpa only [pow_two] using hg
  rw [he]
  push_cast
  ring

theorem cyclic_temperature_second_moment (r : ℕ) (c rho : ℝ) :
    (∑ l : ZMod (2*r+5), (channelTemp (2*r+5) c rho (l,true))^2) /
      (2*r+5:ℝ) = c^2+2/rho^2 := by
  have h1 : (1:ZMod (2*r+5)) ≠ 0 := by
    intro h
    have he := congrArg (fun x : ZMod (2*r+5) => x.val) h
    change ((1:ℕ):ZMod (2*r+5)).val = (0:ZMod (2*r+5)).val at he
    rw [ZMod.val_natCast,ZMod.val_zero,Nat.mod_eq_of_lt (by omega)] at he
    omega
  have h2 : (2:ZMod (2*r+5)) ≠ 0 := by
    intro h
    have he := congrArg ZMod.val h
    change ((2:ℕ):ZMod (2*r+5)).val = _ at he
    rw [ZMod.val_natCast,ZMod.val_zero,Nat.mod_eq_of_lt (by omega)] at he
    omega
  have hc1 : (∑ l : ZMod (2*r+5), cyclicRe (2*r+5) l 1) = 0 := by
    rw [cyclicRe_sum,if_neg h1]
  have hc2 : (∑ l : ZMod (2*r+5), cyclicRe (2*r+5) l 2) = 0 := by
    rw [cyclicRe_sum,if_neg h2]
  have hsq (l : ZMod (2*r+5)) :
    2*(cyclicRe (2*r+5) l 1)^2 = cyclicRe (2*r+5) l 2+1 := by
    have h := cyclicRe_product (2*r+5) l 1 1
    rw [sub_self] at h
    have hz : cyclicRe (2*r+5) l 0 = 1 := by simp [cyclicRe]
    rw [hz] at h
    rw [pow_two]
    convert h using 1 <;> ring
  have he (l : ZMod (2*r+5)) :
      (channelTemp (2*r+5) c rho (l,true))^2 =
      c^2-4*c/rho*cyclicRe (2*r+5) l 1+
        (2/rho^2)*(cyclicRe (2*r+5) l 2+1) := by
    unfold channelTemp
    have h := hsq l
    rw [← h]
    ring
  simp_rw [he]
  simp only [sum_add_distrib,sum_sub_distrib,← mul_sum,hc1,hc2,mul_zero,sub_zero,
    sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  push_cast
  have hp : (2*r+5:ℝ) ≠ 0 := by positivity
  field_simp
  <;> ring

#print axioms paired_average_weight
#print axioms cyclic_temperature_second_moment
end
end GaussianRange

namespace GaussianRange
open Finset Polynomial
noncomputable section

def dispersionCoeffs (c : ℝ) (j : ℕ) : ℝ :=
  if j=1 then c else -1

theorem dispersion_weight (c : ℝ) (z : ℂ) (hz : ‖z‖=1) :
    weight 2 (dispersionCoeffs c) z = (dispersion c z)^2 := by
  have he : (amp 2 (dispersionCoeffs c)).eval z = z*(dispersion c z:ℂ) := by
    have hzz : z * star z = 1 := by
      change z * (starRingEnd ℂ) z = 1
      rw [Complex.mul_conj]
      simp [Complex.normSq_eq_norm_sq,hz]
    have hre : (2*(z.re:ℂ)) = z+star z := by
      apply Complex.ext <;> simp [Complex.add_re,Complex.add_im] <;> ring
    unfold amp dispersionCoeffs dispersion
    simp [Finset.sum_range_succ, eval_monomial]
    push_cast
    rw [hre]
    linear_combination hzz
  unfold weight
  rw [he,norm_mul,hz,one_mul,Complex.norm_real,Real.norm_eq_abs,sq_abs]

theorem avg_dispersion_square (c : ℝ) :
    avg (fun z => (dispersion c z)^2) = c^2+2 := by
  have he : avg (fun z => (dispersion c z)^2) = avg (weight 2 (dispersionCoeffs c)) := by
    unfold avg
    apply le_antisymm
    · apply Real.circleAverage_mono
      · exact (show Continuous (fun z : ℂ => (dispersion c z)^2) by unfold dispersion; fun_prop).continuousOn.circleIntegrable (by norm_num)
      · exact (cont_weight 2 (dispersionCoeffs c)).continuousOn.circleIntegrable (by norm_num)
      intro z hz
      exact (dispersion_weight c z (norm_unit_of_mem z hz)).symm.le
    · apply Real.circleAverage_mono
      · exact (cont_weight 2 (dispersionCoeffs c)).continuousOn.circleIntegrable (by norm_num)
      · exact (show Continuous (fun z : ℂ => (dispersion c z)^2) by unfold dispersion; fun_prop).continuousOn.circleIntegrable (by norm_num)
      intro z hz
      exact (dispersion_weight c z (norm_unit_of_mem z hz)).le
  rw [he,avg_weight_parseval]
  simp [Finset.sum_range_succ,dispersionCoeffs]
  ring

theorem avg_channel_temperature_square (r : ℕ) (g : ℕ → ℝ) (c rho : ℝ)
    (hg : ∑ j ∈ range (r+1), (g j)^2=1) :
    avg (fun z => ∑ v : ZMod (2*r+5) × Bool,
        weight r (realChannel (2*r+5) g v) z * (channelTemp (2*r+5) c rho v)^2) =
      c^2+2/rho^2 := by
  unfold avg
  rw [Real.circleAverage_fun_sum (fun v _ =>
    (show Continuous (fun z : ℂ => weight r (realChannel (2*r+5) g v) z * (channelTemp (2*r+5) c rho v)^2) from (cont_weight r _).mul continuous_const).continuousOn.circleIntegrable (by norm_num))]
  have he (v : ZMod (2*r+5) × Bool) :
      Real.circleAverage (fun z => weight r (realChannel (2*r+5) g v) z *
        (channelTemp (2*r+5) c rho v)^2) 0 1 =
      (channelTemp (2*r+5) c rho v)^2 * avg (weight r (realChannel (2*r+5) g v)) := by
    simp_rw [mul_comm (weight r (realChannel (2*r+5) g v) _)]
    exact Real.circleAverage_fun_smul (a := (channelTemp (2*r+5) c rho v)^2)
  simp_rw [he]
  rw [Fintype.sum_prod_type]
  have hsum (l : ZMod (2*r+5)) :
      (∑ b : Bool, (channelTemp (2*r+5) c rho (l,b))^2 *
        avg (weight r (realChannel (2*r+5) g (l,b)))) =
        (channelTemp (2*r+5) c rho (l,true))^2 / (2*r+5:ℝ) := by
    change (∑ b : Bool, (channelTemp (2*r+5) c rho (l,true))^2 *
        avg (weight r (realChannel (2*r+5) g (l,b)))) = _
    rw [← mul_sum,paired_average_weight r g hg l]
    ring
  simp_rw [hsum]
  rw [← sum_div,cyclic_temperature_second_moment]

#print axioms dispersion_weight
#print axioms avg_dispersion_square
#print axioms avg_channel_temperature_square
end
end GaussianRange

namespace GaussianRange
open Finset Polynomial
noncomputable section

variable {β : Type} [Fintype β]

theorem avg_congr_unit (f g : ℂ → ℝ) (hf : Continuous f) (hg : Continuous g)
    (he : ∀ z : ℂ, ‖z‖ = 1 → f z = g z) : avg f = avg g := by
  unfold avg
  apply le_antisymm
  · apply Real.circleAverage_mono (hf.continuousOn.circleIntegrable (by norm_num))
      (hg.continuousOn.circleIntegrable (by norm_num))
    intro z hz
    exact (he z (norm_unit_of_mem z hz)).le
  · apply Real.circleAverage_mono (hg.continuousOn.circleIntegrable (by norm_num))
      (hf.continuousOn.circleIntegrable (by norm_num))
    intro z hz
    exact (he z (norm_unit_of_mem z hz)).symm.le

def varianceFun (r : ℕ) (a : β → ℕ → ℝ) (T : β → ℝ) (c : ℝ) (z : ℂ) : ℝ :=
  ∑ v, weight r (a v) z * (T v-dispersion c z)^2

theorem cont_dispersion (c : ℝ) : Continuous (dispersion c) := by
  unfold dispersion
  fun_prop

theorem cont_varianceFun (r : ℕ) (a : β → ℕ → ℝ) (T : β → ℝ) (c : ℝ) :
    Continuous (varianceFun r a T c) := by
  unfold varianceFun
  apply continuous_finset_sum
  intro v _
  exact (cont_weight r (a v)).mul ((continuous_const.sub (cont_dispersion c)).pow 2)

theorem avg_variance_identity (r : ℕ) (a : β → ℕ → ℝ) (T : β → ℝ) (c : ℝ)
    (h0 : ∀ z : ℂ, ‖z‖=1 → ∑ v, weight r (a v) z = 1)
    (h1 : ∀ z : ℂ, ‖z‖=1 → ∑ v, T v * weight r (a v) z = dispersion c z) :
    avg (varianceFun r a T c) =
      avg (fun z => ∑ v, weight r (a v) z * (T v)^2) - (c^2+2) := by
  have hc : Continuous (fun z => ∑ v, weight r (a v) z * (T v)^2) :=
    continuous_finset_sum _ (fun v _ => (cont_weight r (a v)).mul continuous_const)
  have hd : Continuous (fun z => (dispersion c z)^2) := (cont_dispersion c).pow 2
  calc
    _ = avg (fun z => (∑ v, weight r (a v) z * (T v)^2) - (dispersion c z)^2) := by
      apply avg_congr_unit _ _ (cont_varianceFun r a T c) (hc.sub hd)
      intro z hz
      exact variance_identity (fun v => weight r (a v) z) T (dispersion c z) (h0 z hz) (h1 z hz)
    _ = _ := by
      unfold avg
      rw [Real.circleAverage_fun_sub (hc.continuousOn.circleIntegrable (by norm_num))
        (hd.continuousOn.circleIntegrable (by norm_num))]
      change _ - avg (fun z => (dispersion c z)^2) = _
      rw [avg_dispersion_square]

theorem channel_avg_variance (r : ℕ) (hr : 0<r) (g : ℕ → ℝ) (c rho : ℝ)
    (hρ : rho ≠ 0)
    (hg : ∑ j ∈ range (r+1), (g j)^2=1)
    (hb : ∑ j ∈ range r, g j*g (j+1)=rho) :
    avg (varianceFun r (realChannel (2*r+5) g) (channelTemp (2*r+5) c rho) c) =
      2*(1/rho^2-1) := by
  rw [avg_variance_identity _ _ _ _ (physical_channel_normalization r g hg)
    (physical_channel_weighted_normalization r hr g c rho hρ hg hb)]
  rw [avg_channel_temperature_square r g c rho hg]
  ring

theorem physical_avg_entropy_upper (r : ℕ) (a : β → ℕ → ℝ) (T : β → ℝ)
    (m t : ℝ) (hm : 0<m) (ht : 0<t) (hT : ∀ v, t ≤ T v)
    (h0 : ∀ z : ℂ, ‖z‖=1 → ∑ v, weight r (a v) z=1)
    (h1 : ∀ z : ℂ, ‖z‖=1 → ∑ v, T v*weight r (a v) z=dispersion (m+2) z) :
    avg (sigma r a T (m+2)) ≤ avg (varianceFun r a T (m+2))/(t*m) := by
  have hpos : ∀ v, 0<T v := fun v => ht.trans_le (hT v)
  have hcont := cont_varianceFun r a T (m+2)
  have hc : Continuous (fun z => varianceFun r a T (m+2) z / (t*m)) :=
    hcont.div_const _
  have hscale : avg (fun z => varianceFun r a T (m+2) z / (t*m)) =
      avg (varianceFun r a T (m+2))/(t*m) := by
    unfold avg
    simp_rw [div_eq_mul_inv, mul_comm _ (t*m)⁻¹]
    exact Real.circleAverage_fun_smul (a := (t*m)⁻¹)
  rw [← hscale]
  unfold avg
  apply Real.circleAverage_mono ((cont_sigma r a T (m+2)).continuousOn.circleIntegrable (by norm_num))
    (hc.continuousOn.circleIntegrable (by norm_num))
  intro z hz
  have hzu := norm_unit_of_mem z hz
  have hre := Complex.abs_re_le_norm z
  rw [hzu] at hre
  have hd : m ≤ dispersion (m+2) z := by unfold dispersion; linarith [le_abs_self z.re]
  have e := entropy_identity (fun v => weight r (a v) z) T (dispersion (m+2) z)
    (hm.trans_le hd) hpos (h0 z hzu) (h1 z hzu)
  unfold sigma varianceFun
  rw [← e]
  exact entropy_upper (fun v => weight r (a v) z) T (dispersion (m+2) z) m t hm ht hd hT
    (fun v => sq_nonneg _)

#print axioms avg_variance_identity
#print axioms channel_avg_variance
#print axioms physical_avg_entropy_upper
end
end GaussianRange

namespace GaussianRange
open Finset Polynomial
noncomputable section

def rationalSigma (r : ℕ) (m : ℝ) : ℝ :=
  avg (sigma r (realChannel (2*r+5) (rationalWindow (r+1)))
    (channelTemp (2*r+5) (m+2) (rationalRho (r+1))) (m+2))

theorem rational_sigma_explicit (r : ℕ) (hr : 0<r) (m : ℝ) (hm : 0<m)
    (hL : 5+10/m < windowL (r+1)) :
    rationalSigma r m ≤
      10*(2*windowL (r+1)-5)/
        (m*(windowL (r+1)-5)*(m*(windowL (r+1)-5)-10)) := by
  let L := windowL (r+1)
  let ρ := rationalRho (r+1)
  have hρ : 0<ρ := rationalRho_pos (r+1) (by omega)
  have h5 : 0<L-5 := by
    dsimp [L] at *
    have hp : 0<10/m := by positivity
    linarith
  have h10 : 0<m*(L-5)-10 := by
    have h : 10/m < L-5 := by dsimp [L]; linarith
    have e := (div_lt_iff₀ hm).mp h
    nlinarith
  have ht : 0<m-10/(L-5) := by
    apply sub_pos.mpr
    apply (div_lt_iff₀ h5).mpr
    linarith
  obtain ⟨hpos,h0,h1⟩ := rational_physical_realization r hr m hm hL
  have hT (v : ZMod (2*r+5) × Bool) :
      m-10/(L-5) ≤ channelTemp (2*r+5) (m+2) ρ v := by
    rw [← rationalTemp_min_formula r hr m]
    exact channelTemp_lower _ _ _ hρ v
  have hup := physical_avg_entropy_upper r
    (realChannel (2*r+5) (rationalWindow (r+1)))
    (channelTemp (2*r+5) (m+2) ρ) m (m-10/(L-5)) hm ht hT h0 h1
  have hv := channel_avg_variance r hr (rationalWindow (r+1)) (m+2) ρ
    hρ.ne' (rationalWindow_norm (r+1) (by omega)) (rationalWindow_correlation r hr)
  rw [hv] at hup
  have hratio : ρ = (L-5)/L := by
    dsimp [ρ,L,rationalRho,windowL]
    field_simp
    <;> ring
  have hLpos : 0<L := by linarith
  have he : 2*(1/ρ^2-1)/((m-10/(L-5))*m) =
      10*(2*L-5)/(m*(L-5)*(m*(L-5)-10)) := by
    rw [hratio]
    field_simp
    <;> ring
  unfold rationalSigma
  exact hup.trans_eq he

theorem rational_sigma_upper (r : ℕ) (hr : 0<r) (m : ℝ) (hm : 0<m)
    (hL : 10+20/m ≤ windowL (r+1)) :
    rationalSigma r m ≤ 80/(m^2*windowL (r+1)) := by
  have h : 5+10/m < windowL (r+1) := by
    have hp : 0<10/m := by positivity
    have he : 20/m = 2*(10/m) := by ring
    linarith
  exact (rational_sigma_explicit r hr m hm h).trans
    (rational_window_upper_constant m (windowL (r+1)) hm hL)

structure BathFamily where
  ι : Type
  finite : Fintype ι
  coeff : ι → ℕ → ℝ
  temp : ι → ℝ

attribute [instance] BathFamily.finite

def BathFamily.admissible (b : BathFamily) (r : ℕ) (m : ℝ) : Prop :=
  (∀ v, 0<b.temp v) ∧
  (∀ z : ℂ, ‖z‖=1 → ∑ v, weight r (b.coeff v) z=1) ∧
  (∀ z : ℂ, ‖z‖=1 → ∑ v, b.temp v*weight r (b.coeff v) z=dispersion (m+2) z)

def BathFamily.cost (b : BathFamily) (r : ℕ) (m : ℝ) : ℝ :=
  avg (sigma r b.coeff b.temp (m+2))

def admissibleCosts (r : ℕ) (m : ℝ) : Set ℝ :=
  {x | ∃ b : BathFamily, b.admissible r m ∧ b.cost r m=x}

def optimalEntropy (r : ℕ) (m : ℝ) : ℝ := sInf (admissibleCosts r m)

def rationalBath (r : ℕ) (m : ℝ) : BathFamily where
  ι := ZMod (2*r+5) × Bool
  finite := inferInstance
  coeff := realChannel (2*r+5) (rationalWindow (r+1))
  temp := channelTemp (2*r+5) (m+2) (rationalRho (r+1))

theorem admissible_lower (r : ℕ) (hr : 0<r) (m : ℝ) (hm : 0<m)
    (x : ℝ) (hx : x ∈ admissibleCosts r m) :
    1/((m+2)*(m+4)*(r:ℝ)^2) ≤ x := by
  obtain ⟨b,⟨ht,h0,h1⟩,rfl⟩ := hx
  have h := physical_entropy_lower r hr b.coeff b.temp (m+2) (by linarith) ht h0 h1
  have hp : 0<(m+2)*(m+4)*(r:ℝ)^2 := by positivity
  apply (div_le_iff₀ hp).mpr
  unfold BathFamily.cost
  convert h using 1 <;> ring

theorem optimalEntropy_bounds (r : ℕ) (hr : 0<r) (m : ℝ) (hm : 0<m)
    (hL : 10+20/m ≤ windowL (r+1)) :
    (admissibleCosts r m).Nonempty ∧
    1/((m+2)*(m+4)*(r:ℝ)^2) ≤ optimalEntropy r m ∧
    optimalEntropy r m ≤ 80/(m^2*windowL (r+1)) := by
  have h : 5+10/m < windowL (r+1) := by
    have hp : 0<10/m := by positivity
    have he : 20/m = 2*(10/m) := by ring
    linarith
  have hb : (rationalBath r m).admissible r m :=
    rational_physical_realization r hr m hm h
  have hx : rationalSigma r m ∈ admissibleCosts r m :=
    ⟨rationalBath r m,hb,rfl⟩
  have hn : (admissibleCosts r m).Nonempty := ⟨_,hx⟩
  have hl : ∀ x ∈ admissibleCosts r m, 1/((m+2)*(m+4)*(r:ℝ)^2) ≤ x :=
    admissible_lower r hr m hm
  have hbd : BddBelow (admissibleCosts r m) := ⟨_,hl⟩
  exact ⟨hn,le_csInf hn hl,(csInf_le hbd hx).trans (rational_sigma_upper r hr m hm hL)⟩

#print axioms rational_sigma_explicit
#print axioms rational_sigma_upper
#print axioms admissible_lower
#print axioms optimalEntropy_bounds
end
end GaussianRange

namespace GaussianRange
open Finset Polynomial
noncomputable section

theorem optimalEntropy_theta (m : ℝ) (hm : 0<m) :
    ∃ C₁ C₂ : ℝ, 0<C₁ ∧ 0<C₂ ∧ ∃ R : ℕ, 0<R ∧
      ∀ r : ℕ, R≤r → (admissibleCosts r m).Nonempty ∧
        C₁/(r:ℝ)^2 ≤ optimalEntropy r m ∧
        optimalEntropy r m ≤ C₂/(r:ℝ)^2 := by
  obtain ⟨R,hR⟩ := exists_nat_gt (10+20/m)
  have hp : 0<20/m := by positivity
  have hRpos : 0<R := by
    by_contra hn
    have he : R=0 := by omega
    rw [he] at hR
    norm_num at hR
    linarith
  refine ⟨1/((m+2)*(m+4)),80/m^2,by positivity,by positivity,R,hRpos,?_⟩
  intro r hr
  have hrpos : 0<r := by omega
  have hrc : (R:ℝ) ≤ r := by exact_mod_cast hr
  have hL : 10+20/m ≤ windowL (r+1) := by
    unfold windowL
    push_cast
    nlinarith [sq_nonneg (r:ℝ), show 0≤(r:ℝ) by positivity]
  obtain ⟨hn,hl,hu⟩ := optimalEntropy_bounds r hrpos m hm hL
  refine ⟨hn,?_,?_⟩
  · simpa only [div_div] using hl
  · apply hu.trans
    have hsq : (r:ℝ)^2 ≤ windowL (r+1) := by
      unfold windowL
      push_cast
      nlinarith [show 0≤(r:ℝ) by positivity]
    have hden : m^2*(r:ℝ)^2 ≤ m^2*windowL (r+1) :=
      mul_le_mul_of_nonneg_left hsq (sq_nonneg m)
    have ht : 0<m^2*(r:ℝ)^2 := by positivity
    have hh := div_le_div_of_nonneg_left (show 0≤(80:ℝ) by norm_num) ht hden
    convert hh using 1 <;> ring

#print axioms optimalEntropy_theta
end
end GaussianRange
