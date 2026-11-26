import MajorantExact
import PhysicalInfimum

namespace GaussianRange
open Finset Polynomial
noncomputable section
variable {β : Type} [Fintype β]

/-- Euler multiplication preserves the FIR degree and weights coefficient j by j. -/
def momentAmp (r : ℕ) (a : ℕ → ℝ) : ℂ[X] :=
  amp r (fun j => (j:ℝ)*a j)

def momentRev (r : ℕ) (a : ℕ → ℝ) : ℂ[X] :=
  rev r (fun j => (j:ℝ)*a j)

theorem euler_monomial_eval (j : ℕ) (a z : ℂ) :
    z*(derivative (monomial j a)).eval z = (j:ℂ)*(monomial j a).eval z := by
  rw [derivative_monomial,eval_monomial,eval_monomial]
  cases j with
  | zero => simp
  | succ j => simp only [Nat.add_sub_cancel,Nat.cast_succ]; rw [pow_succ]; ring

theorem euler_amp_eval (r : ℕ) (a : ℕ → ℝ) (z : ℂ) :
    z*(derivative (amp r a)).eval z = (momentAmp r a).eval z := by
  unfold momentAmp
  rw [amp_eval]
  unfold amp
  rw [derivative_sum,eval_finset_sum,mul_sum]
  apply sum_congr rfl
  intro j hj
  rw [euler_monomial_eval]
  simp only [eval_monomial]
  push_cast
  ring

theorem euler_rev_eval (r : ℕ) (a : ℕ → ℝ) (z : ℂ) :
    z*(derivative (rev r a)).eval z = (r:ℂ)*(rev r a).eval z-(momentRev r a).eval z := by
  unfold momentRev rev
  rw [derivative_sum,eval_finset_sum,mul_sum,eval_finset_sum,eval_finset_sum,mul_sum,← sum_sub_distrib]
  apply sum_congr rfl
  intro j hj
  have hj' : j≤r := by have := mem_range.mp hj; omega
  rw [euler_monomial_eval]
  simp only [eval_monomial]
  push_cast [Nat.cast_sub hj']
  ring

def angularDot (r : ℕ) (a : ℕ → ℝ) (z : ℂ) : ℝ :=
  (((momentAmp r a).eval z)*star ((amp r a).eval z)).im

theorem angularDot_formula (r : ℕ) (a : ℕ → ℝ) (z : ℂ) :
    angularDot r a z=((momentAmp r a).eval z).im*((amp r a).eval z).re-
      ((momentAmp r a).eval z).re*((amp r a).eval z).im := by
  unfold angularDot
  change (((momentAmp r a).eval z)*(starRingEnd ℂ) ((amp r a).eval z)).im=_
  simp [Complex.mul_im,Complex.conj_re,Complex.conj_im]
  ring

theorem euler_spectrum_eval (r : ℕ) (a : β → ℕ → ℝ) (T : β → ℝ) (z : ℂ) (hz : ‖z‖=1) :
    z*(derivative (spectrum r a T)).eval z-(r:ℂ)*(spectrum r a T).eval z =
      z^r * ((2:ℂ)*Complex.I*(∑ v, T v*angularDot r (a v) z : ℝ)) := by
  unfold spectrum
  rw [derivative_sum,eval_finset_sum,eval_finset_sum,mul_sum,mul_sum,← sum_sub_distrib]
  push_cast
  rw [show (2:ℂ)*Complex.I*(∑ v, (T v:ℂ)*(angularDot r (a v) z:ℂ))=
      ∑ v, (2:ℂ)*Complex.I*((T v:ℂ)*(angularDot r (a v) z:ℂ)) by rw [mul_sum],mul_sum]
  apply sum_congr rfl
  intro v hv
  rw [derivative_C_mul,derivative_mul,eval_mul,eval_C,eval_add,eval_mul,eval_mul,eval_mul,eval_C,eval_mul]
  have he := euler_amp_eval r (a v) z
  have hr := euler_rev_eval r (a v) z
  have hrev := rev_unit r (a v) z hz
  have hmrev : (momentRev r (a v)).eval z=z^r*star ((momentAmp r (a v)).eval z) := rev_unit r _ z hz
  have hdot : (momentAmp r (a v)).eval z*star ((amp r (a v)).eval z)-
      (amp r (a v)).eval z*star ((momentAmp r (a v)).eval z)=
      (2:ℂ)*Complex.I*(angularDot r (a v) z:ℂ) := by
    unfold angularDot
    apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im,Complex.sub_re,Complex.sub_im] <;> ring
  calc
    _ = (T v:ℂ)*((z*(derivative (amp r (a v))).eval z)*(rev r (a v)).eval z+
          (amp r (a v)).eval z*(z*(derivative (rev r (a v))).eval z)-
          (r:ℂ)*((amp r (a v)).eval z*(rev r (a v)).eval z)) := by ring
    _ = z^r*((T v:ℂ)*((momentAmp r (a v)).eval z*star ((amp r (a v)).eval z)-
          (amp r (a v)).eval z*star ((momentAmp r (a v)).eval z))) := by rw [he,hr,hrev,hmrev]; ring
    _ = _ := by rw [hdot]; ring

theorem euler_X_pow_eval (k : ℕ) (z : ℂ) :
    z*(derivative (X^k : ℂ[X])).eval z=(k:ℂ)*z^k := by
  have h : (monomial k (1:ℂ))=X^k := by rw [← C_mul_X_pow_eq_monomial,C_1,one_mul]
  simpa [h,eval_pow] using (euler_monomial_eval k 1 z)

theorem angular_normalizations (b : BathFamily) (r : ℕ) (hr : 0<r) (m : ℝ)
    (hb : b.admissible r m) (z : ℂ) (hz : ‖z‖=1) :
    (∑ v, angularDot r (b.coeff v) z)=0 ∧
    (∑ v, b.temp v*angularDot r (b.coeff v) z)=-z.im := by
  have hz0 : z≠0 := by intro h; rw [h,norm_zero] at hz; norm_num at hz
  have hzpow : z^r≠0 := pow_ne_zero _ hz0
  have h0 := euler_spectrum_eval r b.coeff (fun _=>1) z hz
  have h1 := euler_spectrum_eval r b.coeff b.temp z hz
  have hN := normalization_poly r b.coeff hb.2.1
  have hT := weighted_normalization_poly r hr b.coeff b.temp (m+2) hb.2.2
  rw [hN, euler_X_pow_eval,eval_pow,eval_X,sub_self] at h0
  have h0' : (2:ℂ)*Complex.I*((∑ v, angularDot r (b.coeff v) z : ℝ):ℂ)=0 := by
    simp only [one_mul] at h0
    exact (mul_eq_zero.mp h0.symm).resolve_left hzpow
  have h0i := congrArg Complex.im h0'
  simp [Complex.mul_im,Complex.mul_re] at h0i
  constructor
  · linarith
  · rw [hT,derivative_sub,derivative_sub,derivative_C_mul,eval_sub,eval_sub,eval_mul,eval_C,
      eval_sub,eval_sub,eval_mul,eval_C,eval_pow,eval_pow,eval_pow,eval_X] at h1
    have e₀ := euler_X_pow_eval r z
    have e₁ := euler_X_pow_eval (r+1) z
    have e₂ := euler_X_pow_eval (r-1) z
    have hc : (r-1:ℕ)=(r-1) := rfl
    have hcast : ((r-1:ℕ):ℂ)=(r:ℂ)-1 := by push_cast [Nat.cast_sub (show 1≤r by omega)]; ring
    rw [hcast] at e₂
    have hsum : z*( (↑(m+2):ℂ)*(derivative (X^r : ℂ[X])).eval z -
        (derivative (X^(r+1) : ℂ[X])).eval z - (derivative (X^(r-1) : ℂ[X])).eval z) =
        (↑(m+2):ℂ)*((r:ℂ)*z^r)-((r+1:ℕ):ℂ)*z^(r+1)-((r:ℂ)-1)*z^(r-1) := by
      linear_combination (↑(m+2):ℂ)*e₀-e₁-e₂
    have hpow : z^(r-1)=z^r*star z := by
      have he : r=(r-1)+1 := by omega
      conv_rhs => rw [he,pow_succ,mul_assoc,unit_mul_star z hz,mul_one]
    have hleft : z^r*(star z-z)=z^r*((2:ℂ)*Complex.I*(∑ v,b.temp v*angularDot r (b.coeff v) z:ℝ)) := by
      rw [← h1, hsum, hpow, pow_succ]
      push_cast
      ring
    have hcancel := mul_left_cancel₀ hzpow hleft
    have hi := congrArg Complex.im hcancel
    simp [Complex.sub_im,Complex.mul_re,Complex.mul_im] at hi
    linarith

end
end GaussianRange
#print axioms GaussianRange.angular_normalizations