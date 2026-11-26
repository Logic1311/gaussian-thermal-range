import Integrated
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

namespace GaussianRange
open Finset
open scoped RealInnerProductSpace
noncomputable section
variable {ι : Type} [Fintype ι]

abbrev BathSpace (ι : Type) := EuclideanSpace ℝ ι

def temperatureOperator (T : ι → ℝ) : BathSpace ι →ₗ[ℝ] BathSpace ι where
  toFun x := WithLp.toLp 2 (fun i => T i * x i)
  map_add' x y := by
    ext i
    simp [mul_add]
  map_smul' a x := by
    ext i
    simp [mul_left_comm]

theorem temperature_inner (T : ι → ℝ) (x y : BathSpace ι) :
    ⟪x, temperatureOperator T y⟫ = ∑ i, T i * x i * y i := by
  change (∑ i, (T i * y i) * star (x i)) = _
  apply Finset.sum_congr rfl
  intro i hi
  simp
  ring

def compressedOperator (T : ι → ℝ) (K : Submodule ℝ (BathSpace ι)) : K →ₗ[ℝ] K :=
  K.orthogonalProjection.toLinearMap.comp ((temperatureOperator T).comp K.subtype)

theorem compressed_inner (T : ι → ℝ) (K : Submodule ℝ (BathSpace ι)) (x y : K) :
    ⟪x, compressedOperator T K y⟫ = ∑ i, T i * (x.val i) * (y.val i) := by
  change ⟪x, K.orthogonalProjection (temperatureOperator T y.val)⟫ = _
  rw [Submodule.inner_orthogonalProjection_eq_of_mem_left, temperature_inner]

theorem compressed_symmetric (T : ι → ℝ) (K : Submodule ℝ (BathSpace ι)) :
    (compressedOperator T K).IsSymmetric := by
  intro x y
  rw [real_inner_comm y (compressedOperator T K x), compressed_inner, compressed_inner]
  apply Finset.sum_congr rfl
  intro i hi
  ring

def compressedBasis (T : ι → ℝ) (K : Submodule ℝ (BathSpace ι)) :
    OrthonormalBasis (Fin (Module.finrank ℝ K)) ℝ K :=
  (compressed_symmetric T K).eigenvectorBasis rfl

def compressedTemp (T : ι → ℝ) (K : Submodule ℝ (BathSpace ι)) :
    Fin (Module.finrank ℝ K) → ℝ :=
  (compressed_symmetric T K).eigenvalues rfl

theorem compressed_eigen (T : ι → ℝ) (K : Submodule ℝ (BathSpace ι)) (j : Fin (Module.finrank ℝ K)) :
    compressedOperator T K (compressedBasis T K j) = compressedTemp T K j • compressedBasis T K j :=
  (compressed_symmetric T K).apply_eigenvectorBasis rfl j

theorem compressedTemp_pos (T : ι → ℝ) (K : Submodule ℝ (BathSpace ι))
    (ht : ∀ i, 0 < T i) (j : Fin (Module.finrank ℝ K)) : 0 < compressedTemp T K j := by
  let e := compressedBasis T K j
  have hn : ‖e‖ = 1 := (compressedBasis T K).orthonormal.1 j
  have hq : ⟪e, compressedOperator T K e⟫ = compressedTemp T K j := by
    rw [show compressedOperator T K e = compressedTemp T K j • e from compressed_eigen T K j,
      real_inner_smul_right, real_inner_self_eq_norm_sq, hn]
    ring
  rw [← hq, compressed_inner]
  have he : ∃ i : ι, e.val i ≠ 0 := by
    by_contra! h
    have hv : e.val = 0 := by ext i; simpa using h i
    have hz : e = 0 := Subtype.ext hv
    rw [hz, norm_zero] at hn
    norm_num at hn
  obtain ⟨i, hi⟩ := he
  apply Finset.sum_pos' (fun k _ => by nlinarith [mul_nonneg (ht k).le (sq_nonneg (e.val k))])
  exact ⟨i, mem_univ _, by nlinarith [mul_pos (ht i) (sq_pos_of_ne_zero hi)]⟩

theorem compressed_parseval (T : ι → ℝ) (K : Submodule ℝ (BathSpace ι)) (x : K) :
    (∑ j, ⟪compressedBasis T K j, x⟫^2) = ∑ i, (x.val i)^2 := by
  calc
    (∑ j, ⟪compressedBasis T K j, x⟫^2) =
        ∑ j, ⟪x, compressedBasis T K j⟫ * ⟪compressedBasis T K j, x⟫ := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [real_inner_comm (compressedBasis T K j) x]
      ring
    _ = ⟪x, x⟫ := (compressedBasis T K).sum_inner_mul_inner x x
    _ = ∑ i, (x.val i)^2 := by
      change (∑ i, x.val i * star (x.val i)) = _
      simp [pow_two]

theorem compressed_weighted (T : ι → ℝ) (K : Submodule ℝ (BathSpace ι)) (x : K) :
    (∑ j, compressedTemp T K j * ⟪compressedBasis T K j, x⟫^2) = ∑ i, T i * (x.val i)^2 := by
  have h := (compressedBasis T K).sum_inner_mul_inner x (compressedOperator T K x)
  simp_rw [← (compressed_symmetric T K) (compressedBasis T K _) x, compressed_eigen, real_inner_smul_left] at h
  rw [compressed_inner] at h
  convert h using 1
  · apply Finset.sum_congr rfl
    intro j hj
    rw [real_inner_comm x]
    ring
  · apply Finset.sum_congr rfl
    intro i hi
    ring


theorem compressed_inverse (T : ι → ℝ) (K : Submodule ℝ (BathSpace ι))
    (ht : ∀ i, 0 < T i) (x : K) :
    (∑ j, ⟪compressedBasis T K j, x⟫^2 / compressedTemp T K j) ≤ ∑ i, (x.val i)^2 / T i := by
  let y : K := ∑ j, (⟪compressedBasis T K j, x⟫ / compressedTemp T K j) • compressedBasis T K j
  have hy : compressedOperator T K y = x := by
    dsimp only [y]
    rw [map_sum]
    simp_rw [map_smul, compressed_eigen, smul_smul]
    calc
      _ = ∑ j, ⟪compressedBasis T K j, x⟫ • compressedBasis T K j := by
        apply Finset.sum_congr rfl
        intro j hj
        congr 1
        exact div_mul_cancel₀ _ (ne_of_gt (compressedTemp_pos T K ht j))
      _ = x := (compressedBasis T K).sum_repr' x
  have hxy : ⟪x, y⟫ = ∑ j, ⟪compressedBasis T K j, x⟫^2 / compressedTemp T K j := by
    dsimp only [y]
    rw [inner_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [real_inner_smul_right, real_inner_comm (compressedBasis T K j) x]
    ring
  have hxy' : ⟪x, y⟫ = ∑ i, x.val i * y.val i := by
    change (∑ i, y.val i * star (x.val i)) = _
    simp [mul_comm]
  have hyy : (∑ i, T i * (y.val i)^2) = ⟪x, y⟫ := by
    have h := compressed_inner T K y y
    rw [hy, real_inner_comm x y] at h
    rw [h]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hle : (∑ i, (2*x.val i*y.val i - T i*(y.val i)^2)) ≤ ∑ i, (x.val i)^2/T i := by
    apply Finset.sum_le_sum
    intro i hi
    apply (le_div_iff₀ (ht i)).2
    nlinarith [sq_nonneg (x.val i - T i*y.val i)]
  have he : (∑ i, (2*x.val i*y.val i - T i*(y.val i)^2)) = ⟪x,y⟫ := by
    rw [Finset.sum_sub_distrib]
    simp only [mul_assoc, ← Finset.mul_sum]
    rw [← hxy', hyy]
    ring
  rwa [he, hxy] at hle

-- Bilinear identities explicitly preserve the two Gram matrices.
theorem compressed_gram (T : ι → ℝ) (K : Submodule ℝ (BathSpace ι)) (x y : K) :
    (∑ j, ⟪compressedBasis T K j, x⟫ * ⟪compressedBasis T K j, y⟫) = ∑ i, x.val i * y.val i := by
  calc
    _ = ⟪x,y⟫ := by
      rw [← (compressedBasis T K).sum_inner_mul_inner x y]
      apply Finset.sum_congr rfl
      intro j hj
      rw [real_inner_comm (compressedBasis T K j) x]
    _ = _ := by
      change (∑ i, y.val i * star (x.val i)) = _
      simp [mul_comm]

theorem compressed_weighted_gram (T : ι → ℝ) (K : Submodule ℝ (BathSpace ι)) (x y : K) :
    (∑ j, compressedTemp T K j * ⟪compressedBasis T K j, x⟫ * ⟪compressedBasis T K j, y⟫) =
      ∑ i, T i * x.val i * y.val i := by
  have h := (compressedBasis T K).sum_inner_mul_inner x (compressedOperator T K y)
  simp_rw [← (compressed_symmetric T K) (compressedBasis T K _) y, compressed_eigen, real_inner_smul_left] at h
  rw [compressed_inner] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [real_inner_comm (compressedBasis T K j) x]
  ring
end
end GaussianRange
#print axioms GaussianRange.compressedTemp_pos
#print axioms GaussianRange.compressed_parseval
#print axioms GaussianRange.compressed_weighted
#print axioms GaussianRange.compressed_inverse
#print axioms GaussianRange.compressed_gram
#print axioms GaussianRange.compressed_weighted_gram
