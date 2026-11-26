import PathConstruction
import PathSpectrumCore

namespace GaussianRange
open Finset
open scoped RealInnerProductSpace
noncomputable section

def pathUnit (r : ℕ) (m : ℝ) (i : Fin (r+1)) : bathSpan (rationalBath r m) r :=
  (rationalWindow (r+1) i)⁻¹ • bathColumnIn (rationalBath r m) r i

theorem pathUnit_orthonormal (r : ℕ) (hr : 0 < r) (m : ℝ) :
    Orthonormal ℝ (pathUnit r m) := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [pathUnit, pathUnit, real_inner_smul_left, real_inner_smul_right]
  change (rationalWindow (r+1) i)⁻¹ * ((rationalWindow (r+1) j)⁻¹ *
    ⟪bathColumn (rationalBath r m) r i, bathColumn (rationalBath r m) r j⟫) = _
  rw [rational_column_inner]
  by_cases h : i=j
  · subst j
    simp
    field_simp [ne_of_gt (rationalWindow_pos_fin r hr i)]
  · simp [h]

def pathUnitBasis (r : ℕ) (hr : 0 < r) (m : ℝ) :
    OrthonormalBasis (Fin (r+1)) ℝ (bathSpan (rationalBath r m) r) := by
  let b := basisOfLinearIndependentOfCardEqFinrank (pathUnit_orthonormal r hr m).linearIndependent
    (by simp [bathSpan, finrank_span_eq_card (rational_column_independent r hr m)])
  exact b.toOrthonormalBasis (by simpa [b] using pathUnit_orthonormal r hr m)

theorem pathUnitBasis_apply (r : ℕ) (hr : 0 < r) (m : ℝ) (i : Fin (r+1)) :
    pathUnitBasis r hr m i = pathUnit r m i := by
  unfold pathUnitBasis
  simp

theorem pathUnit_entry (r : ℕ) (hr : 0 < r) (m : ℝ) (i j : Fin (r+1)) :
    ⟪pathUnit r m i, compressedOperator (rationalBath r m).temp (bathSpan (rationalBath r m) r) (pathUnit r m j)⟫ =
      pathTemperatureMatrix r m i j := by
  have h := pathBath_weighted_gram r m i j
  unfold pathBath at h
  simp_rw [← mul_assoc] at h
  rw [compressed_weighted_gram_coeff] at h
  rw [pathUnit, pathUnit, map_smul, real_inner_smul_left, real_inner_smul_right, compressed_inner]
  change (rationalWindow (r+1) i)⁻¹ * ((rationalWindow (r+1) j)⁻¹ *
    (∑ v, (rationalBath r m).temp v * (rationalBath r m).coeff v i * (rationalBath r m).coeff v j)) = _
  rw [h]
  field_simp [ne_of_gt (rationalWindow_pos_fin r hr i),ne_of_gt (rationalWindow_pos_fin r hr j)]

def pathLambda (r : ℕ) (m : ℝ) (k : Fin (r+1)) : ℝ :=
  m+2-2*Real.cos (pathAngle r k)/rationalRho (r+1)

theorem pathMatrix_sine (r : ℕ) (m : ℝ) (k i : Fin (r+1)) :
    (∑ j : Fin (r+1), pathTemperatureMatrix r m i j * pathSine r k j) = pathLambda r m k * pathSine r k i := by
  unfold pathTemperatureMatrix pathLambda
  simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have h : (∑ j : Fin (r+1), pathAdj r i j / rationalRho (r+1) * pathSine r k j) =
      (∑ j : Fin (r+1), pathAdjacency r i j * pathSine r k j)/rationalRho (r+1) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [pathAdj,pathAdjacency]
    ring
  rw [h,pathSine_eigen]
  simp
  ring

def pathPhysicalSine (r : ℕ) (hr : 0 < r) (m : ℝ) (k : Fin (r+1)) : bathSpan (rationalBath r m) r :=
  (pathUnitBasis r hr m).repr.symm (pathSineVector r k)

theorem pathPhysicalSine_ne_zero (r : ℕ) (hr : 0 < r) (m : ℝ) (k : Fin (r+1)) :
    pathPhysicalSine r hr m k ≠ 0 := by
  intro h
  apply pathSineVector_ne_zero r k
  have he := congrArg (pathUnitBasis r hr m).repr h
  simpa [pathPhysicalSine] using he

theorem pathPhysicalSine_eigen (r : ℕ) (hr : 0 < r) (m : ℝ) (k : Fin (r+1)) :
    compressedOperator (rationalBath r m).temp (bathSpan (rationalBath r m) r) (pathPhysicalSine r hr m k) =
      pathLambda r m k • pathPhysicalSine r hr m k := by
  let B := pathUnitBasis r hr m
  apply B.repr.injective
  ext i
  change B.repr (compressedOperator (rationalBath r m).temp (bathSpan (rationalBath r m) r) (B.repr.symm (pathSineVector r k))) i =
    B.repr (pathLambda r m k • B.repr.symm (pathSineVector r k)) i
  rw [map_smul, LinearIsometryEquiv.apply_symm_apply]
  rw [B.repr_apply_apply, ← B.sum_repr_symm]
  rw [map_sum, inner_sum]
  simp_rw [map_smul, real_inner_smul_right]
  have h (j : Fin (r+1)) : ⟪B i, compressedOperator (rationalBath r m).temp (bathSpan (rationalBath r m) r) (B j)⟫ = pathTemperatureMatrix r m i j := by
    simp only [B,pathUnitBasis_apply]
    exact pathUnit_entry r hr m i j
  simp_rw [h]
  change (∑ j : Fin (r+1), pathSine r k j * pathTemperatureMatrix r m i j) = pathLambda r m k * pathSine r k i
  simp_rw [mul_comm (pathSine r k _)]
  exact pathMatrix_sine r m k i

theorem pathLambda_injective (r : ℕ) (hr : 0 < r) (m : ℝ) : Function.Injective (pathLambda r m) := by
  intro i j h
  by_contra hn
  apply pathCos_ne r i j hn
  unfold pathLambda at h
  have hp := ne_of_gt (rationalRho_pos (r+1) (by omega))
  have he : 2*Real.cos (pathAngle r i)/rationalRho (r+1) = 2*Real.cos (pathAngle r j)/rationalRho (r+1) := by linarith
  field_simp [hp] at he
  linarith

theorem pathTemps_range_eq (r : ℕ) (hr : 0 < r) (m : ℝ) :
    Set.range (pathBath r m).temp = Set.range (pathLambda r m) := by
  have h (k : Fin (r+1)) : ∃ j : (pathBath r m).ι, (pathBath r m).temp j = pathLambda r m k := by
    have he : Module.End.HasEigenvalue (compressedOperator (rationalBath r m).temp (bathSpan (rationalBath r m) r)) (pathLambda r m k) :=
      Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.mpr (pathPhysicalSine_eigen r hr m k), pathPhysicalSine_ne_zero r hr m k⟩
    exact (compressed_symmetric (rationalBath r m).temp (bathSpan (rationalBath r m) r)).exists_eigenvalues_eq rfl he
  choose f hf using h
  have hinj : Function.Injective f := by
    intro i j he
    apply pathLambda_injective r hr m
    rw [← hf i, ← hf j,he]
  have hsurj : Function.Surjective f := ((Fintype.bijective_iff_injective_and_card f).2 ⟨hinj, by rw [Fintype.card_fin,pathBath_count r hr m]⟩).2
  ext x
  constructor
  · rintro ⟨j,rfl⟩
    obtain ⟨k,rfl⟩ := hsurj j
    exact ⟨k,(hf k).symm⟩
  · rintro ⟨k,rfl⟩
    exact ⟨f k,hf k⟩

theorem pathLambda_min (r : ℕ) (hr : 0 < r) (m : ℝ) (k : Fin (r+1)) :
    pathLambda r m 0 ≤ pathLambda r m k := by
  have ha : pathAngle r 0 ≤ pathAngle r k := by
    unfold pathAngle
    simp only [Fin.val_zero, Nat.cast_zero, zero_add, one_mul]
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith [Real.pi_pos, Nat.cast_nonneg (α := ℝ) k.val]
  have hc := Real.strictAntiOn_cos.antitoneOn ⟨(pathAngle_bounds r 0).1.le,(pathAngle_bounds r 0).2.le⟩
    ⟨(pathAngle_bounds r k).1.le,(pathAngle_bounds r k).2.le⟩ ha
  unfold pathLambda
  apply sub_le_sub_left
  exact div_le_div_of_nonneg_right (by linarith) (rationalRho_pos (r+1) (by omega)).le

theorem pathBath_temp_pos_iff (r : ℕ) (hr : 0 < r) (m : ℝ) :
    (∀ j, 0 < (pathBath r m).temp j) ↔ 0 < pathLambda r m 0 := by
  have he := pathTemps_range_eq r hr m
  constructor
  · intro h
    have hm : pathLambda r m 0 ∈ Set.range (pathBath r m).temp := by rw [he]; exact ⟨0,rfl⟩
    obtain ⟨j,hj⟩ := hm
    rw [← hj]
    exact h j
  · intro h j
    have hm : (pathBath r m).temp j ∈ Set.range (pathLambda r m) := by rw [← he]; exact ⟨j,rfl⟩
    obtain ⟨k,hk⟩ := hm
    rw [← hk]
    exact lt_of_lt_of_le h (pathLambda_min r hr m k)

theorem pathBath_admissible_iff (r : ℕ) (hr : 0 < r) (m : ℝ) :
    (pathBath r m).admissible r m ↔ m+2 > 2*Real.cos (Real.pi/((r:ℝ)+2))/rationalRho (r+1) := by
  constructor
  · intro h
    have hp := (pathBath_temp_pos_iff r hr m).mp h.1
    simpa [pathLambda,pathAngle,sub_pos] using hp
  · intro h
    have hp : 0 < pathLambda r m 0 := by simpa [pathLambda,pathAngle,sub_pos] using h
    exact ⟨(pathBath_temp_pos_iff r hr m).mpr hp, pathBath_normalization r hr m, pathBath_weighted_normalization r hr m⟩

end
end GaussianRange
#print axioms GaussianRange.pathTemps_range_eq
#print axioms GaussianRange.pathBath_admissible_iff
