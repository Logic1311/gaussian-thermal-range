import Integrated
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Polynomial

namespace GaussianRange
open Polynomial
open scoped BigOperators
noncomputable section

/-- A real FIR spectral factor, with degree budget explicitly controlled. -/
def RealFactor (p : ℝ[X]) (d : ℕ) : Prop :=
  ∃ q : ℝ[X], q.natDegree ≤ d ∧
    ∀ z : ℂ, ‖z‖ = 1 → p.eval z.re = ‖(q.map (algebraMap ℝ ℂ)).eval z‖^2

theorem realFactor_mono {p : ℝ[X]} {d e : ℕ} (h : RealFactor p d) (hde : d ≤ e) :
    RealFactor p e := by
  obtain ⟨q,hq,he⟩ := h
  exact ⟨q,hq.trans hde,he⟩

theorem realFactor_const (a : ℝ) (ha : 0 ≤ a) : RealFactor (C a) 0 := by
  refine ⟨C (Real.sqrt a), by simp, ?_⟩
  intro z hz
  simp [Real.sq_sqrt ha, abs_of_nonneg (Real.sqrt_nonneg a)]

theorem realFactor_mul {p q : ℝ[X]} {d e : ℕ} (hp : RealFactor p d) (hq : RealFactor q e) :
    RealFactor (p*q) (d+e) := by
  obtain ⟨a,ha,he⟩ := hp
  obtain ⟨b,hb,hf⟩ := hq
  refine ⟨a*b, (natDegree_mul_le.trans (Nat.add_le_add ha hb)), ?_⟩
  intro z hz
  rw [eval_mul,Polynomial.map_mul,eval_mul,norm_mul,mul_pow,he z hz,hf z hz]

theorem unit_re_sq_im_sq (z : ℂ) (hz : ‖z‖=1) : z.re^2+z.im^2=1 := by
  have h : Complex.normSq z=1 := by rw [Complex.normSq_eq_norm_sq,hz]; norm_num
  rw [Complex.normSq_apply] at h
  nlinarith

theorem realFactor_linear (a b : ℝ) (h₁ : 0 ≤ a+b) (h₂ : 0 ≤ a-b) :
    RealFactor (C b*X+C a) 1 := by
  let u := (Real.sqrt (a+b)+Real.sqrt (a-b))/2
  let v := (Real.sqrt (a+b)-Real.sqrt (a-b))/2
  have hsum : u^2+v^2=a := by
    dsimp [u,v]
    nlinarith [Real.sq_sqrt h₁, Real.sq_sqrt h₂]
  have hprod : 2*u*v=b := by
    dsimp [u,v]
    nlinarith [Real.sq_sqrt h₁, Real.sq_sqrt h₂]
  refine ⟨C v*X+C u,natDegree_linear_le,?_⟩
  intro z hz
  simp only [eval_add,eval_mul,eval_C,eval_X,Polynomial.map_add,Polynomial.map_mul,Polynomial.map_C,Polynomial.map_X]
  change b*z.re+a = ‖(v:ℂ)*z+(u:ℂ)‖^2
  rw [← Complex.normSq_eq_norm_sq,Complex.normSq_apply]
  simp only [Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,mul_zero,sub_zero,zero_add,add_zero]
  change b*z.re+a = (v*z.re+u)*(v*z.re+u)+(v*z.im)*(v*z.im)
  have h := unit_re_sq_im_sq z hz
  calc
    _ = (u^2+v^2)+2*u*v*z.re := by rw [hsum,hprod]; ring
    _ = _ := by linear_combination -v^2*h

/-- The norm of a real quadratic amplitude, evaluated on the unit circle. -/
theorem realQuadratic_norm (a b c : ℝ) (z : ℂ) (hz : ‖z‖=1) :
    ‖(a:ℂ)+(b:ℂ)*z+(c:ℂ)*z^2‖^2 =
      (a+c)^2*z.re^2+2*(a+c)*b*z.re+b^2+(c-a)^2*z.im^2 := by
  have he : z*star z = 1 := by
    change z*(starRingEnd ℂ) z=1
    rw [Complex.mul_conj,Complex.normSq_eq_norm_sq,hz]
    norm_num
  have hs : ‖star z‖=1 := by simpa using hz
  have hm : ((a:ℂ)+(b:ℂ)*z+(c:ℂ)*z^2)*star z = (a:ℂ)*star z+(b:ℂ)+(c:ℂ)*z := by
    linear_combination ((b:ℂ)+(c:ℂ)*z)*he
  calc
    _ = ‖((a:ℂ)+(b:ℂ)*z+(c:ℂ)*z^2)*star z‖^2 := by rw [norm_mul,hs,mul_one]
    _ = _ := by
      rw [hm,← Complex.normSq_eq_norm_sq,Complex.normSq_apply]
      simp [Complex.star_def,Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im]
      ring

/-- Every conjugate-root quadratic has a real factor of length three. -/
theorem realFactor_quadratic (a b : ℝ) :
    RealFactor (X^2-C (2*a)*X+C (a^2+b^2)) 2 := by
  let A := Real.sqrt ((a+1)^2+b^2)
  let B := Real.sqrt ((a-1)^2+b^2)
  let u := (A+B)/2
  let v := (A-B)/2
  have hA : A^2=(a+1)^2+b^2 := Real.sq_sqrt (by positivity)
  have hB : B^2=(a-1)^2+b^2 := Real.sq_sqrt (by positivity)
  have hAn : 0≤A := Real.sqrt_nonneg _
  have hBn : 0≤B := Real.sqrt_nonneg _
  have hAl : a+1≤A := by nlinarith [sq_nonneg b]
  have hBl : 1-a≤B := by nlinarith [sq_nonneg b]
  have hu : 1≤u := by dsimp [u]; linarith
  have huv : u*v=a := by dsimp [u,v]; nlinarith
  have hsum : u^2+v^2=a^2+b^2+1 := by dsimp [u,v]; nlinarith
  let d := Real.sqrt (u^2-1)
  have hd : d^2=u^2-1 := Real.sq_sqrt (by nlinarith)
  let x := (u-d)/2
  let y := (u+d)/2
  have hx : x+y=u := by dsimp [x,y]; ring
  have hy : y-x=d := by dsimp [x,y]; ring
  refine ⟨C y*X^2+C (-v)*X+C x,natDegree_quadratic_le,?_⟩
  intro z hz
  simp only [eval_add,eval_sub,eval_mul,eval_pow,eval_C,eval_X,Polynomial.map_add,Polynomial.map_mul,Polynomial.map_C,Polynomial.map_X,Polynomial.map_pow]
  have he : (algebraMap ℝ ℂ y)*z^2+algebraMap ℝ ℂ (-v)*z+algebraMap ℝ ℂ x =
      (x:ℂ)+(-v:ℝ)*z+(y:ℂ)*z^2 := by simp; ring
  rw [he,realQuadratic_norm x (-v) y z hz,hx,hy,hd]
  have h := unit_re_sq_im_sq z hz
  calc
    _ = z.re^2 - 2*a*z.re + (a^2+b^2) := by ring
    _ = _ := by
      linear_combination (1-u^2)*h + 2*z.re*huv - hsum

end
end GaussianRange
#print axioms GaussianRange.realFactor_linear
#print axioms GaussianRange.realFactor_quadratic