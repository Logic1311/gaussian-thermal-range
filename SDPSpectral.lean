import TemperatureResource

namespace GaussianRange
open Finset
open scoped RealInnerProductSpace
noncomputable section

abbrev SDPSpace (n : ℕ) := BathSpace (Fin n)
abbrev SDPOp (n : ℕ) := SDPSpace n →ₗ[ℝ] SDPSpace n

def sdpPositive {n : ℕ} (A : SDPOp n) : Prop :=
  ∀ x, x ≠ 0 → 0 < ⟪x,A x⟫

def basisDiag {ι E : Type} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (B : OrthonormalBasis ι ℝ E) (t : ι → ℝ) : E →ₗ[ℝ] E :=
  B.repr.symm.toLinearEquiv.toLinearMap.comp
    ((temperatureOperator t).comp B.repr.toLinearEquiv.toLinearMap)

theorem basisDiag_repr {ι E : Type} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (B : OrthonormalBasis ι ℝ E) (t : ι → ℝ) (x : E) :
    B.repr (basisDiag B t x) = temperatureOperator t (B.repr x) := by
  simp [basisDiag]

theorem basisDiag_inner {ι E : Type} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (B : OrthonormalBasis ι ℝ E) (t : ι → ℝ) (x y : E) :
    ⟪x,basisDiag B t y⟫ = ∑ i, t i * ⟪B i,x⟫ * ⟪B i,y⟫ := by
  rw [← B.repr.inner_map_map, basisDiag_repr, temperature_inner]
  simp only [← OrthonormalBasis.repr_apply_apply]

theorem basisDiag_symmetric {ι E : Type} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (B : OrthonormalBasis ι ℝ E) (t : ι → ℝ) : (basisDiag B t).IsSymmetric := by
  intro x y
  rw [real_inner_comm y (basisDiag B t x),basisDiag_inner,basisDiag_inner]
  apply sum_congr rfl
  intro i hi
  ring

theorem basisDiag_comp {ι E : Type} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (B : OrthonormalBasis ι ℝ E) (a b : ι → ℝ) (x : E) :
    basisDiag B a (basisDiag B b x) = basisDiag B (fun i => a i*b i) x := by
  apply B.repr.injective
  rw [basisDiag_repr,basisDiag_repr,basisDiag_repr]
  ext i
  change a i*(b i*(B.repr x) i)=(a i*b i)*(B.repr x) i
  ring

theorem basisDiag_one {ι E : Type} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (B : OrthonormalBasis ι ℝ E) (x : E) :
    basisDiag B (fun _ => 1) x=x := by
  apply B.repr.injective
  rw [basisDiag_repr]
  ext i
  change 1*(B.repr x) i=(B.repr x) i
  ring

theorem symm_eigen_diag {n : ℕ} (M : SDPOp n) (hM : M.IsSymmetric) (x : SDPSpace n) :
    basisDiag (hM.eigenvectorBasis rfl) (hM.eigenvalues rfl) x=M x := by
  let B := hM.eigenvectorBasis rfl
  apply B.repr.injective
  change B.repr (basisDiag B (hM.eigenvalues rfl) x)=B.repr (M x)
  rw [basisDiag_repr]
  ext i
  change (hM.eigenvalues rfl i)*(B.repr x) i=(B.repr (M x)) i
  exact (hM.eigenvectorBasis_apply_self_apply rfl x i).symm

theorem sdp_eigen_pos {n : ℕ} (M : SDPOp n) (hM : M.IsSymmetric) (hp : sdpPositive M)
    (i : Fin (Module.finrank ℝ (SDPSpace n))) : 0 < hM.eigenvalues rfl i := by
  let e := hM.eigenvectorBasis rfl i
  have hn : ‖e‖=1 := (hM.eigenvectorBasis rfl).orthonormal.1 i
  have hne : e≠0 := by intro he; rw [he,norm_zero] at hn; norm_num at hn
  have h := hp e hne
  change 0 < ⟪e,M e⟫ at h
  rw [show M e=hM.eigenvalues rfl i • e from hM.apply_eigenvectorBasis rfl i,
      real_inner_smul_right,real_inner_self_eq_norm_sq,hn] at h
  simpa using h

theorem sdp_square_root_pair {n : ℕ} (M : SDPOp n) (hM : M.IsSymmetric) (hp : sdpPositive M) :
    ∃ S R : SDPOp n, S.IsSymmetric ∧ R.IsSymmetric ∧
      (∀ x,S (S x)=M x) ∧ (∀ x,S (R x)=x) ∧ (∀ x,R (S x)=x) := by
  let B := hM.eigenvectorBasis rfl
  let a := fun i => Real.sqrt (hM.eigenvalues rfl i)
  let b := fun i => (a i)⁻¹
  have ha (i) : 0<a i := Real.sqrt_pos.2 (sdp_eigen_pos M hM hp i)
  have hsq : (fun i => a i*a i)=hM.eigenvalues rfl := by
    funext i
    exact (pow_two (a i)).symm.trans (Real.sq_sqrt (sdp_eigen_pos M hM hp i).le)
  have hab : (fun i => a i*b i)=fun _ => 1 := by
    funext i
    exact mul_inv_cancel₀ (ha i).ne'
  have hba : (fun i => b i*a i)=fun _ => 1 := by
    funext i
    exact inv_mul_cancel₀ (ha i).ne'
  refine ⟨basisDiag B a,basisDiag B b,basisDiag_symmetric _ _,basisDiag_symmetric _ _,?_,?_,?_⟩
  · intro x
    rw [basisDiag_comp,hsq]
    exact symm_eigen_diag M hM x
  · intro x
    rw [basisDiag_comp,hab,basisDiag_one]
  · intro x
    rw [basisDiag_comp,hba,basisDiag_one]

end
end GaussianRange
#print axioms GaussianRange.sdp_square_root_pair
