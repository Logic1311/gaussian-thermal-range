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
