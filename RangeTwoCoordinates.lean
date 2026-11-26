import SDPExact

namespace GaussianRange
open Finset
open scoped RealInnerProductSpace Matrix
noncomputable section

abbrev R2Mat := Matrix (Fin 3) (Fin 3) ℝ
def r2op (M : R2Mat) : SDPOp 3 := Matrix.toEuclideanLin M

theorem r2op_apply (M : R2Mat) (x : SDPSpace 3) (i : Fin 3) :
    (r2op M x) i = ∑ j,M i j*x j := rfl

theorem r2op_inner (M : R2Mat) (x y : SDPSpace 3) :
    ⟪x,r2op M y⟫=∑ i, x i*(∑ j,M i j*y j) := by
  rw [PiLp.inner_apply]
  apply sum_congr rfl
  intro i hi
  change (r2op M y) i*star (x i)=_
  rw [r2op_apply]
  simp [mul_comm]

theorem r2op_mul (M N : R2Mat) (x : SDPSpace 3) :
    r2op (M*N) x=r2op M (r2op N x) := by
  change WithLp.toLp 2 ((M*N)*ᵥ x.ofLp)=WithLp.toLp 2 (M*ᵥ (N*ᵥ x.ofLp))
  rw [Matrix.mulVec_mulVec]

theorem r2op_transpose (M : R2Mat) (x y : SDPSpace 3) :
    ⟪r2op M x,y⟫=⟪x,r2op Mᵀ y⟫ := by
  rw [real_inner_comm y (r2op M x),r2op_inner,r2op_inner]
  simp only [Fin.sum_univ_three,Matrix.transpose_apply]
  ring

theorem r2op_symm (M : R2Mat) (hM : Mᵀ=M) : (r2op M).IsSymmetric := by
  intro x y
  rw [r2op_transpose,hM]

def r2trace0 (M : R2Mat) : ℝ := M 0 0+M 1 1+M 2 2
def r2trace1 (M : R2Mat) : ℝ := M 0 1+M 1 0+M 1 2+M 2 1
def r2trace2 (M : R2Mat) : ℝ := M 0 2+M 2 0

theorem r2_spectrum (M : R2Mat) (z : ℂ) (hz : ‖z‖=1) :
    sdpSpectrum 2 (r2op M) z =
      r2trace0 M+r2trace1 M*z.re+r2trace2 M*(2*z.re^2-1) := by
  have hunit := unit_re_sq_im_sq z hz
  have he : sdpSpectrum 2 (r2op M) z =
      ∑ i : Fin 3,∑ j : Fin 3,M i j *
        ((z^(i:ℕ)).re*(z^(j:ℕ)).re+(z^(i:ℕ)).im*(z^(j:ℕ)).im) := by
    unfold sdpSpectrum
    rw [r2op_inner,r2op_inner]
    simp only [sdpRe,sdpIm,WithLp.ofLp_toLp]
    simp only [Fin.sum_univ_three]
    ring
  rw [he]
  have hp (i j : Fin 3) :
      (z^(i:ℕ)).re*(z^(j:ℕ)).re+(z^(i:ℕ)).im*(z^(j:ℕ)).im =
        (z^(if (i:ℕ)≤(j:ℕ) then (j:ℕ)-(i:ℕ) else (i:ℕ)-(j:ℕ))).re := by
    rw [← unit_pair_re z hz]
    simp [Complex.mul_re,Complex.star_def,Complex.conj_re,Complex.conj_im,← map_pow]
  simp_rw [hp]
  norm_num [Fin.sum_univ_three,Fin.val_natCast,r2trace0,r2trace1,r2trace2,pow_two,Complex.mul_re] <;>
    simp (disch := decide) [show (1:ℕ)≤2 by decide,show ¬(2:ℕ)≤1 by decide,show (2:ℕ)≠0 by decide, Complex.mul_re] <;>
    linear_combination -(M 0 2+M 2 0)*hunit

theorem r2_lag_from_spectrum (M : R2Mat) (d a : ℝ)
    (h : ∀ z : ℂ, ‖z‖=1 → sdpSpectrum 2 (r2op M) z=d+a*z.re) :
    r2trace0 M=d ∧ r2trace1 M=a ∧ r2trace2 M=0 := by
  have hp := h 1 (by norm_num)
  have hn := h (-1) (by norm_num)
  have hi := h Complex.I (by norm_num)
  rw [r2_spectrum M 1 (by norm_num)] at hp
  rw [r2_spectrum M (-1) (by norm_num)] at hn
  rw [r2_spectrum M Complex.I (by norm_num)] at hi
  norm_num at hp hn hi
  exact ⟨by linarith,by linarith,by linarith⟩

theorem r2_avg_add (f g : ℂ → ℝ) (hf : Continuous f) (hg : Continuous g) :
    avg (fun z => f z+g z)=avg f+avg g := by
  unfold avg
  exact Real.circleAverage_fun_add (hf.continuousOn.circleIntegrable (by norm_num))
    (hg.continuousOn.circleIntegrable (by norm_num))

theorem r2_avg_smul (a : ℝ) (f : ℂ → ℝ) :
    avg (fun z => a*f z)=a*avg f :=
  Real.circleAverage_fun_smul (a:=a)

theorem r2_avg_odd (f : ℂ → ℝ) (hf : ∀ z, f (-z)= -f z) : avg f=0 := by
  have he : avg (fun z => f (-z))=avg f := by
    unfold avg
    rw [← Real.circleAverage_neg_radius (f:=f) (c:=(0:ℂ)) (R:=(1:ℝ))]
    unfold Real.circleAverage
    congr 1
    apply intervalIntegral.integral_congr
    intro θ hθ
    congr 1
    simp [circleMap]
  have hneg : (fun z => f (-z))=(fun z => (-1:ℝ)*f z) := by
    funext z
    rw [hf]
    ring
  rw [hneg,r2_avg_smul] at he
  linarith

theorem r2_avg_re : avg (fun z : ℂ => z.re)=0 :=
  r2_avg_odd _ (by intro z; simp)
theorem r2_avg_re_cube : avg (fun z : ℂ => z.re^3)=0 :=
  r2_avg_odd _ (by intro z; simp [Complex.neg_re]; ring)
theorem r2_avg_re_sq : avg (fun z : ℂ => z.re^2)=1/2 := by
  have he := avg_congr_unit (fun z : ℂ => z.re^2) (fun z => 1-z.im^2)
    (Complex.continuous_re.pow 2) (continuous_const.sub (Complex.continuous_im.pow 2))
    (fun z hz => by nlinarith [unit_re_sq_im_sq z hz])
  have hc : avg (fun _ : ℂ => (1:ℝ))=1 := Real.circleAverage_const 1 0 1
  have hn : avg (fun z : ℂ => -(z.im^2))= -(1/2) := by
    have h := r2_avg_smul (-1) (fun z : ℂ => z.im^2)
    rw [avg_im_square] at h
    simpa using h
  rw [he,show (fun z : ℂ => 1-z.im^2)=(fun z => 1+ -(z.im^2)) by funext z; ring,
    r2_avg_add _ _ continuous_const ((Complex.continuous_im.pow 2).neg),hc,hn]
  ring

theorem r2_avg_poly (a b d e : ℝ) :
    avg (fun z : ℂ => a+b*z.re+d*z.re^2+e*z.re^3)=a+d/2 := by
  have hc : avg (fun _ : ℂ => a)=a := Real.circleAverage_const a 0 1
  have hb : Continuous (fun z : ℂ => b*z.re) := continuous_const.mul Complex.continuous_re
  have hd : Continuous (fun z : ℂ => d*z.re^2) := continuous_const.mul (Complex.continuous_re.pow 2)
  have he : Continuous (fun z : ℂ => e*z.re^3) := continuous_const.mul (Complex.continuous_re.pow 3)
  rw [r2_avg_add (fun z : ℂ => a+b*z.re+d*z.re^2) (fun z => e*z.re^3)
    (by fun_prop) he,
    r2_avg_add (fun z : ℂ => a+b*z.re) (fun z => d*z.re^2) (by fun_prop) hd,
    r2_avg_add (fun _ : ℂ => a) (fun z => b*z.re) continuous_const hb,
    r2_avg_smul b (fun z => z.re),r2_avg_smul d (fun z => z.re^2),
    r2_avg_smul e (fun z => z.re^3),hc,r2_avg_re,r2_avg_re_sq,r2_avg_re_cube]
  ring

theorem r2_avg_spectrum (M : R2Mat) (c : ℝ) :
    avg (fun z => dispersion c z*sdpSpectrum 2 (r2op M) z-1)=
      c*r2trace0 M-r2trace1 M-1 := by
  let a := r2trace0 M
  let b := r2trace1 M
  let d := r2trace2 M
  let f : ℂ → ℝ := fun z => (c*(a-d)-1)+(c*b-2*(a-d))*z.re+
      (2*c*d-2*b)*z.re^2+(-4*d)*z.re^3
  have hf : Continuous f := by dsimp [f]; fun_prop
  have h := avg_congr_unit
    (fun z => dispersion c z*sdpSpectrum 2 (r2op M) z-1) f
    (((cont_dispersion c).mul (sdpSpectrum_cont 2 _)).sub continuous_const) hf
    (fun z hz => by
      change dispersion c z*sdpSpectrum 2 (r2op M) z-1=f z
      rw [r2_spectrum M z hz]; dsimp [f,a,b,d,dispersion]; ring)
  rw [h]
  dsimp [f]
  rw [r2_avg_poly]
  dsimp [a,b,d]
  ring

theorem r2_op_surj (A : SDPOp 3) : ∃ M : R2Mat, r2op M=A :=
  ⟨Matrix.toEuclideanLin.symm A,Matrix.toEuclideanLin.apply_symm_apply A⟩

end
end GaussianRange
#print axioms GaussianRange.r2_spectrum
#print axioms GaussianRange.r2_avg_spectrum
