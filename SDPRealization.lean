import SDPMoments

namespace GaussianRange
open Finset
open scoped RealInnerProductSpace
noncomputable section

def sdpStd (n : ℕ) (j : Fin n) : SDPSpace n :=
  EuclideanSpace.basisFun (Fin n) ℝ j

theorem sdpStd_expand {n : ℕ} (x : SDPSpace n) :
    (∑ j,x j • sdpStd n j)=x := by
  ext i
  simp [sdpStd,EuclideanSpace.basisFun_apply,Pi.single_apply,eq_comm]

theorem sdp_parseval {n : ℕ} {ι : Type} [Fintype ι]
    (B : OrthonormalBasis ι ℝ (SDPSpace n)) (x : SDPSpace n) :
    (∑ i,⟪B i,x⟫^2)=⟪x,x⟫ := by
  rw [← B.sum_inner_mul_inner x x]
  apply sum_congr rfl
  intro i hi
  rw [real_inner_comm x (B i)]
  ring

theorem sdpRealization {r : ℕ} (p : SDPMoments r) (m : ℝ) (hm : 0<m)
    (hp : SDPFeasible p m) (hG : sdpPositive p.G) (hH : sdpPositive p.H) :
    ∃ b : BathFamily, Fintype.card b.ι≤r+1 ∧ b.admissible r m ∧
      (∀ z : ℂ, ‖z‖=1 → sigma r b.coeff b.temp (m+2) z≤sdpSigma p m z) := by
  obtain ⟨S,R,hSs,hRs,hSS,hSR,hRS⟩ := sdp_square_root_pair p.H hp.hs hH
  let M : SDPOp (r+1) := R.comp (p.G.comp R)
  have hMs : M.IsSymmetric := by
    intro x y
    change ⟪R (p.G (R x)),y⟫=⟪x,R (p.G (R y))⟫
    rw [hRs,hp.gs,← hRs]
  have hMp : sdpPositive M := by
    intro x hx
    change 0<⟪x,R (p.G (R x))⟫
    rw [← hRs]
    apply hG
    intro he
    exact hx (by rw [← hSR x,he,map_zero])
  let B := hMs.eigenvectorBasis rfl
  let lam := hMs.eigenvalues rfl
  have hlam (i) : 0<lam i := sdp_eigen_pos M hMs hMp i
  let b : BathFamily := {
    ι := Fin (Module.finrank ℝ (SDPSpace (r+1)))
    finite := inferInstance
    coeff := fun v j => if hj : j<r+1 then Real.sqrt (lam v)*⟪B v,S (sdpStd (r+1) ⟨j,hj⟩)⟫ else 0
    temp := fun v => (lam v)⁻¹ }
  have ht (v : b.ι) : 0<b.temp v := inv_pos.mpr (hlam v)
  have hcoeff (v : b.ι) (j : Fin (r+1)) :
      b.coeff v j=Real.sqrt (lam v)*⟪B v,S (sdpStd (r+1) j)⟫ := by
    simp [b,j.isLt]
  have hrow (v : b.ι) (x : SDPSpace (r+1)) :
      ⟪sdpRow b r v,x⟫=Real.sqrt (lam v)*⟪B v,S x⟫ := by
    rw [row_inner]
    conv_rhs => rw [← sdpStd_expand x,map_sum,inner_sum,mul_sum]
    apply sum_congr rfl
    intro j hj
    rw [hcoeff,map_smul,real_inner_smul_right]
    ring
  have hqG (x : SDPSpace (r+1)) :
      ⟪x,(bathMoments b r).G x⟫=⟪x,p.G x⟫ := by
    change ⟪x,gramOp b r (fun _ => 1) x⟫=_
    rw [gramOp_inner]
    simp_rw [hrow]
    calc
      _ = ∑ v,lam v*⟪B v,S x⟫*⟪B v,S x⟫ := by
        apply sum_congr rfl
        intro v hv
        calc
          _ = (Real.sqrt (lam v))^2*⟪B v,S x⟫*⟪B v,S x⟫ := by ring
          _ = _ := by rw [Real.sq_sqrt (hlam v).le]
      _ = ⟪S x,M (S x)⟫ := by rw [← basisDiag_inner,symm_eigen_diag]
      _ = _ := by
        change ⟪S x,R (p.G (R (S x)))⟫=_
        rw [← hRs,hRS]
  have hqH (x : SDPSpace (r+1)) :
      ⟪x,(bathMoments b r).H x⟫=⟪x,p.H x⟫ := by
    change ⟪x,gramOp b r b.temp x⟫=_
    rw [gramOp_inner]
    simp_rw [hrow]
    calc
      _ = ∑ v,⟪B v,S x⟫^2 := by
        apply sum_congr rfl
        intro v hv
        change (lam v)⁻¹*(Real.sqrt (lam v)*⟪B v,S x⟫)*
          (Real.sqrt (lam v)*⟪B v,S x⟫)=_
        have h := Real.sq_sqrt (hlam v).le
        field_simp [(hlam v).ne']
        nlinarith only [h]
      _ = ⟪S x,S x⟫ := sdp_parseval B (S x)
      _ = _ := by rw [hSs,hSS]
  have hqJ (x : SDPSpace (r+1)) :
      ⟪x,(bathMoments b r).J x⟫≤⟪x,p.J x⟫ := by
    change ⟪x,gramOp b r (fun v => (b.temp v)⁻¹) x⟫≤_
    rw [gramOp_inner]
    simp_rw [hrow]
    have he (v : b.ι) : ⟪B v,M (S x)⟫=lam v*⟪B v,S x⟫ := by
      rw [← hMs,hMs.apply_eigenvectorBasis rfl,real_inner_smul_left]
      rfl
    have hEq : (∑ v,(b.temp v)⁻¹*(Real.sqrt (lam v)*⟪B v,S x⟫)*
          (Real.sqrt (lam v)*⟪B v,S x⟫))=⟪R (p.G x),R (p.G x)⟫ := by
      calc
        _ = ∑ v,⟪B v,M (S x)⟫^2 := by
          apply sum_congr rfl
          intro v hv
          rw [he]
          change ((lam v)⁻¹)⁻¹*(Real.sqrt (lam v)*⟪B v,S x⟫)*
            (Real.sqrt (lam v)*⟪B v,S x⟫)=_
          rw [inv_inv]
          calc
            _ = lam v*(Real.sqrt (lam v))^2*⟪B v,S x⟫^2 := by ring
            _ = _ := by rw [Real.sq_sqrt (hlam v).le]; ring
        _ = ⟪M (S x),M (S x)⟫ := sdp_parseval B _
        _ = _ := by
          change ⟪R (p.G (R (S x))),R (p.G (R (S x)))⟫=_
          rw [hRS]
    rw [hEq]
    let y := R (p.G x)
    have hblock := hp.block (-(R y)) x
    have hHy : p.H (R y)=S y := by rw [← hSS,hSR]
    rw [map_neg,hHy,inner_neg_left,inner_neg_right,neg_neg,inner_neg_left] at hblock
    have hA : ⟪R y,S y⟫=⟪y,y⟫ := by rw [hRs,hSR]
    have hB : ⟪R y,p.G x⟫=⟪y,y⟫ := hRs y (p.G x)
    rw [hA,hB] at hblock
    change ⟪y,y⟫≤_
    linarith
  have hGs (z : ℂ) : sdpSpectrum r (bathMoments b r).G z=sdpSpectrum r p.G z := by
    unfold sdpSpectrum
    rw [hqG,hqG]
  have hHs (z : ℂ) : sdpSpectrum r (bathMoments b r).H z=sdpSpectrum r p.H z := by
    unfold sdpSpectrum
    rw [hqH,hqH]
  have hJs (z : ℂ) : sdpSpectrum r (bathMoments b r).J z≤sdpSpectrum r p.J z := by
    unfold sdpSpectrum
    exact add_le_add (hqJ _) (hqJ _)
  have hb : b.admissible r m := by
    refine ⟨ht,?_,?_⟩
    · intro z hz
      have h := (hGs z).trans (hp.normalization z hz)
      change sdpSpectrum r (gramOp b r (fun _ => 1)) z=1 at h
      simpa [gramOp_spectrum] using h
    · intro z hz
      have h := (hHs z).trans (hp.weighted z hz)
      change sdpSpectrum r (gramOp b r b.temp) z=_ at h
      rw [gramOp_spectrum] at h
      exact h
  refine ⟨b,?_,hb,?_⟩
  · change Fintype.card (Fin (Module.finrank ℝ (SDPSpace (r+1))))≤r+1
    simp [SDPSpace,BathSpace,finrank_euclideanSpace]
  · intro z hz
    rw [← bathMoments_sigma b r m z]
    unfold sdpSigma
    obtain ⟨hlo,hhi⟩ := unit_re_mem z hz
    have hd : 0≤dispersion (m+2) z := by unfold dispersion; linarith
    exact sub_le_sub_right (mul_le_mul_of_nonneg_left (hJs z) hd) 1

end
end GaussianRange
#print axioms GaussianRange.sdpRealization
