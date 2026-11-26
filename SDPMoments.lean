import SDPSpectral

namespace GaussianRange
open Finset Polynomial
open scoped RealInnerProductSpace
noncomputable section

def rankOneSDP {n : ℕ} (u : SDPSpace n) : SDPOp n :=
  (innerSL ℝ u).toLinearMap.smulRight u

theorem rankOne_inner {n : ℕ} (u x y : SDPSpace n) :
    ⟪x,rankOneSDP u y⟫=⟪u,x⟫*⟪u,y⟫ := by
  unfold rankOneSDP
  change ⟪x,⟪u,y⟫ • u⟫=_
  rw [real_inner_smul_right,real_inner_comm x u]
  ring

def sdpRow (b : BathFamily) (r : ℕ) (v : b.ι) : SDPSpace (r+1) :=
  WithLp.toLp 2 (fun j => b.coeff v j)

def gramOp (b : BathFamily) (r : ℕ) (t : b.ι → ℝ) : SDPOp (r+1) :=
  ∑ v, t v • rankOneSDP (sdpRow b r v)

theorem gramOp_inner (b : BathFamily) (r : ℕ) (t : b.ι → ℝ)
    (x y : SDPSpace (r+1)) :
    ⟪x,gramOp b r t y⟫=∑ v,t v*⟪sdpRow b r v,x⟫*⟪sdpRow b r v,y⟫ := by
  unfold gramOp
  rw [LinearMap.sum_apply,inner_sum]
  apply sum_congr rfl
  intro v hv
  rw [LinearMap.smul_apply,real_inner_smul_right,rankOne_inner]
  ring

theorem gramOp_symm (b : BathFamily) (r : ℕ) (t : b.ι → ℝ) :
    (gramOp b r t).IsSymmetric := by
  intro x y
  rw [real_inner_comm y (gramOp b r t x),gramOp_inner,gramOp_inner]
  apply sum_congr rfl
  intro v hv
  ring

theorem row_inner (b : BathFamily) (r : ℕ) (v : b.ι) (x : SDPSpace (r+1)) :
    ⟪sdpRow b r v,x⟫=∑ j : Fin (r+1),b.coeff v j*x j := by
  change (∑ j : Fin (r+1),x j*star (b.coeff v j))=_
  simp [mul_comm]

def sdpRe (r : ℕ) (z : ℂ) : SDPSpace (r+1) :=
  WithLp.toLp 2 (fun j => (z^(j:ℕ)).re)

def sdpIm (r : ℕ) (z : ℂ) : SDPSpace (r+1) :=
  WithLp.toLp 2 (fun j => (z^(j:ℕ)).im)

def sdpSpectrum (r : ℕ) (A : SDPOp (r+1)) (z : ℂ) : ℝ :=
  ⟪sdpRe r z,A (sdpRe r z)⟫+⟪sdpIm r z,A (sdpIm r z)⟫

theorem gramOp_spectrum (b : BathFamily) (r : ℕ) (t : b.ι → ℝ) (z : ℂ) :
    sdpSpectrum r (gramOp b r t) z=∑ v,t v*weight r (b.coeff v) z := by
  unfold sdpSpectrum
  rw [gramOp_inner,gramOp_inner,← sum_add_distrib]
  apply sum_congr rfl
  intro v hv
  rw [weight_fin,row_inner,row_inner]
  change t v*(∑ j : Fin (r+1), b.coeff v j*(z^(j:ℕ)).re)*
      (∑ j : Fin (r+1), b.coeff v j*(z^(j:ℕ)).re) +
    t v*(∑ j : Fin (r+1), b.coeff v j*(z^(j:ℕ)).im)*
      (∑ j : Fin (r+1), b.coeff v j*(z^(j:ℕ)).im) = _
  ring

theorem sdpRe_cont (r : ℕ) : Continuous (sdpRe r) := by
  unfold sdpRe
  apply (PiLp.continuous_toLp 2 (fun _ : Fin (r+1) => ℝ)).comp
  exact continuous_pi (fun j => Complex.continuous_re.comp (continuous_id.pow (j:ℕ)))

theorem sdpIm_cont (r : ℕ) : Continuous (sdpIm r) := by
  unfold sdpIm
  apply (PiLp.continuous_toLp 2 (fun _ : Fin (r+1) => ℝ)).comp
  exact continuous_pi (fun j => Complex.continuous_im.comp (continuous_id.pow (j:ℕ)))

theorem sdpSpectrum_cont (r : ℕ) (A : SDPOp (r+1)) :
    Continuous (sdpSpectrum r A) := by
  unfold sdpSpectrum
  exact ((sdpRe_cont r).inner (A.continuous_of_finiteDimensional.comp (sdpRe_cont r))).add
    ((sdpIm_cont r).inner (A.continuous_of_finiteDimensional.comp (sdpIm_cont r)))

structure SDPMoments (r : ℕ) where
  G : SDPOp (r+1)
  H : SDPOp (r+1)
  J : SDPOp (r+1)

structure SDPFeasible {r : ℕ} (p : SDPMoments r) (m : ℝ) : Prop where
  gs : p.G.IsSymmetric
  hs : p.H.IsSymmetric
  js : p.J.IsSymmetric
  gn : ∀ x, 0≤⟪x,p.G x⟫
  block : ∀ x y, 0≤⟪x,p.H x⟫+2*⟪x,p.G y⟫+⟪y,p.J y⟫
  normalization : ∀ z : ℂ, ‖z‖=1 → sdpSpectrum r p.G z=1
  weighted : ∀ z : ℂ, ‖z‖=1 → sdpSpectrum r p.H z=dispersion (m+2) z

def sdpSigma {r : ℕ} (p : SDPMoments r) (m : ℝ) (z : ℂ) : ℝ :=
  dispersion (m+2) z*sdpSpectrum r p.J z-1

def sdpCost {r : ℕ} (p : SDPMoments r) (m : ℝ) : ℝ := avg (sdpSigma p m)

def bathMoments (b : BathFamily) (r : ℕ) : SDPMoments r :=
  ⟨gramOp b r (fun _ => 1),gramOp b r b.temp,gramOp b r (fun v => (b.temp v)⁻¹)⟩

theorem bathMoments_feasible (b : BathFamily) (r : ℕ) (m : ℝ)
    (hb : b.admissible r m) : SDPFeasible (bathMoments b r) m := by
  refine ⟨gramOp_symm _ _ _,gramOp_symm _ _ _,gramOp_symm _ _ _,?_,?_,?_,?_⟩
  · intro x
    change 0≤⟪x,gramOp b r (fun _ => 1) x⟫
    rw [gramOp_inner]
    exact sum_nonneg (fun v _ => by simpa [pow_two] using sq_nonneg ⟪sdpRow b r v,x⟫)
  · intro x y
    change 0≤⟪x,gramOp b r b.temp x⟫+2*⟪x,gramOp b r (fun _ => 1) y⟫+
      ⟪y,gramOp b r (fun v => (b.temp v)⁻¹) y⟫
    rw [gramOp_inner,gramOp_inner,gramOp_inner,mul_sum,← sum_add_distrib,← sum_add_distrib]
    apply sum_nonneg
    intro v hv
    have ht := hb.1 v
    have he : b.temp v*⟪sdpRow b r v,x⟫*⟪sdpRow b r v,x⟫+
        2*(1*⟪sdpRow b r v,x⟫*⟪sdpRow b r v,y⟫)+
        (b.temp v)⁻¹*⟪sdpRow b r v,y⟫*⟪sdpRow b r v,y⟫ =
        (b.temp v*⟪sdpRow b r v,x⟫+⟪sdpRow b r v,y⟫)^2/b.temp v := by
      field_simp [ht.ne']
      <;> ring
    rw [he]
    positivity
  · intro z hz
    change sdpSpectrum r (gramOp b r (fun _ => 1)) z=1
    simpa [gramOp_spectrum] using hb.2.1 z hz
  · intro z hz
    change sdpSpectrum r (gramOp b r b.temp) z=_
    rw [gramOp_spectrum]
    exact hb.2.2 z hz

theorem bathMoments_sigma (b : BathFamily) (r : ℕ) (m : ℝ) (z : ℂ) :
    sdpSigma (bathMoments b r) m z=sigma r b.coeff b.temp (m+2) z := by
  unfold sdpSigma sigma bathMoments
  rw [gramOp_spectrum]
  simp only [div_eq_mul_inv,mul_comm]

theorem bathMoments_cost (b : BathFamily) (r : ℕ) (m : ℝ) :
    sdpCost (bathMoments b r) m=b.cost r m := by
  unfold sdpCost BathFamily.cost
  exact congrArg avg (funext (bathMoments_sigma b r m))

theorem sdpSigma_cont {r : ℕ} (p : SDPMoments r) (m : ℝ) :
    Continuous (sdpSigma p m) :=
  ((cont_dispersion _).mul (sdpSpectrum_cont _ _)).sub continuous_const

theorem sdpCost_mono {r : ℕ} (p q : SDPMoments r) (m : ℝ)
    (hle : ∀ z : ℂ, ‖z‖=1 → sdpSigma p m z≤sdpSigma q m z) :
    sdpCost p m≤sdpCost q m := by
  unfold sdpCost avg
  apply Real.circleAverage_mono ((sdpSigma_cont p m).continuousOn.circleIntegrable (by norm_num))
    ((sdpSigma_cont q m).continuousOn.circleIntegrable (by norm_num))
  intro z hz
  exact hle z (norm_unit_of_mem z hz)

theorem sdpSigma_nonneg {r : ℕ} (p : SDPMoments r) (m : ℝ) (hm : 0<m)
    (hp : SDPFeasible p m) (z : ℂ) (hz : ‖z‖=1) : 0≤sdpSigma p m z := by
  let d := dispersion (m+2) z
  obtain ⟨hlo,hhi⟩ := unit_re_mem z hz
  have hd : 0<d := by dsimp [d,dispersion]; linarith
  have hb (y : SDPSpace (r+1)) :
      0≤(d⁻¹)^2*⟪y,p.H y⟫-2*d⁻¹*⟪y,p.G y⟫+⟪y,p.J y⟫ := by
    have h := hp.block ((-d⁻¹) • y) y
    rw [map_smul,real_inner_smul_left,real_inner_smul_right,real_inner_smul_left] at h
    nlinarith only [h]
  have hs := add_nonneg (hb (sdpRe r z)) (hb (sdpIm r z))
  have hE : 0≤(d⁻¹)^2*sdpSpectrum r p.H z-2*d⁻¹*sdpSpectrum r p.G z+sdpSpectrum r p.J z := by
    unfold sdpSpectrum
    linarith only [hs]
  rw [hp.weighted z hz,hp.normalization z hz] at hE
  change 0≤(d⁻¹)^2*d-2*d⁻¹*1+sdpSpectrum r p.J z at hE
  have he : (d⁻¹)^2*d-2*d⁻¹*1= -d⁻¹ := by
    field_simp [hd.ne']
    <;> ring
  rw [he] at hE
  have hmul := mul_nonneg hd.le hE
  change 0≤d*sdpSpectrum r p.J z-1
  rw [mul_add,show d*(-d⁻¹)= -1 by field_simp [hd.ne']] at hmul
  linarith

def sdpCosts (r : ℕ) (m : ℝ) : Set ℝ :=
  {x | ∃ p : SDPMoments r, SDPFeasible p m ∧ sdpCost p m=x}

theorem physical_subset_sdp (r : ℕ) (m : ℝ) : admissibleCosts r m⊆sdpCosts r m := by
  rintro x ⟨b,hb,rfl⟩
  exact ⟨bathMoments b r,bathMoments_feasible b r m hb,bathMoments_cost b r m⟩

theorem sdpCosts_nonempty (r : ℕ) (hr : 0<r) (m : ℝ) (hm : 0<m) :
    (sdpCosts r m).Nonempty := by
  obtain ⟨x,hx⟩ := admissibleCosts_nonempty_all r hr m hm
  exact ⟨x,physical_subset_sdp r m hx⟩

theorem sdpCosts_bddBelow (r : ℕ) (m : ℝ) (hm : 0<m) : BddBelow (sdpCosts r m) := by
  refine ⟨0,?_⟩
  rintro x ⟨p,hp,rfl⟩
  unfold sdpCost avg
  have he : Real.circleAverage (fun _ : ℂ => (0:ℝ)) 0 1=0 :=
    Real.circleAverage_const 0 0 1
  rw [← he]
  apply Real.circleAverage_mono (continuous_const.continuousOn.circleIntegrable (by norm_num))
    ((sdpSigma_cont p m).continuousOn.circleIntegrable (by norm_num))
  intro z hz
  exact sdpSigma_nonneg p m hm hp z (norm_unit_of_mem z hz)

end
end GaussianRange
#print axioms GaussianRange.bathMoments_feasible
#print axioms GaussianRange.physical_subset_sdp
#print axioms GaussianRange.sdpCosts_bddBelow
