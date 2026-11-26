import Integrated
import Mathlib.Analysis.Matrix.Spectrum

namespace GaussianRange
open Finset
open scoped RealInnerProductSpace
noncomputable section

def pathAdjacency (r : ℕ) : Matrix (Fin (r+1)) (Fin (r+1)) ℝ :=
  fun i j => if (i:ℕ)+1=j.val ∨ j.val+1=i.val then 1 else 0

theorem pathAdjacency_hermitian (r : ℕ) : (pathAdjacency r).IsHermitian := by
  ext i j
  simp [Matrix.IsHermitian, pathAdjacency, Matrix.conjTranspose_apply, or_comm]

theorem pathAdjacency_sum (r : ℕ) (i : Fin (r+1)) (f : ℕ → ℝ) :
    (∑ j : Fin (r+1), pathAdjacency r i j * f j) =
      (if i.val=0 then 0 else f (i.val-1)) + (if i.val+1<r+1 then f (i.val+1) else 0) := by
  have h (j : Fin (r+1)) : pathAdjacency r i j * f j =
      (if j.val+1=i.val then f j else 0)+(if i.val+1=j.val then f j else 0) := by
    unfold pathAdjacency
    by_cases h₁ : j.val+1=i.val <;> by_cases h₂ : i.val+1=j.val
    · omega
    · simp [h₁,h₂]
    · simp [h₁,h₂]
    · simp [h₁,h₂]
  simp_rw [h, Finset.sum_add_distrib]
  congr 1
  · by_cases hi : i.val=0
    · have hn (j : Fin (r+1)) : ¬ j.val+1=i.val := by omega
      simp [hi,hn]
    · let l : Fin (r+1) := ⟨i.val-1, by omega⟩
      have he (j : Fin (r+1)) : (j.val+1=i.val) ↔ j=l := by
        constructor
        · intro hj; apply Fin.ext; dsimp [l]; omega
        · intro hj; subst j; dsimp [l]; omega
      simp [he,hi,l]
  · by_cases hi : i.val+1<r+1
    · let j₀ : Fin (r+1) := ⟨i.val+1,hi⟩
      have he (j : Fin (r+1)) : (i.val+1=j.val) ↔ j=j₀ := by
        constructor
        · intro hj; apply Fin.ext; dsimp [j₀]; omega
        · intro hj; subst j; rfl
      simp [he,hi,j₀]
    · have hn (j : Fin (r+1)) : ¬ i.val+1=j.val := by omega
      simp [hi,hn]

def pathAngle (r : ℕ) (k : Fin (r+1)) : ℝ := ((k.val:ℝ)+1)*Real.pi/((r:ℝ)+2)

def pathSine (r : ℕ) (k : Fin (r+1)) (j : ℕ) : ℝ := Real.sin (((j:ℝ)+1)*pathAngle r k)

theorem pathAngle_bounds (r : ℕ) (k : Fin (r+1)) : 0 < pathAngle r k ∧ pathAngle r k < Real.pi := by
  unfold pathAngle
  constructor
  · positivity
  · apply (div_lt_iff₀ (by positivity)).2
    have hk : (k.val:ℝ)+1 < (r:ℝ)+2 := by exact_mod_cast (show k.val+1<r+2 by omega)
    nlinarith [mul_lt_mul_of_pos_right hk Real.pi_pos]

theorem pathSine_eigen (r : ℕ) (k i : Fin (r+1)) :
    (∑ j : Fin (r+1), pathAdjacency r i j * pathSine r k j) =
      2*Real.cos (pathAngle r k)*pathSine r k i := by
  rw [pathAdjacency_sum]
  have hl : (if i.val=0 then 0 else pathSine r k (i.val-1)) = Real.sin ((i.val:ℝ)*pathAngle r k) := by
    split_ifs with hi
    · simp [hi]
    · unfold pathSine
      congr 1
      rw [Nat.cast_sub (show 1 ≤ i.val by omega)]
      push_cast
      ring
  have hr : (if i.val+1<r+1 then pathSine r k (i.val+1) else 0) =
      Real.sin (((i.val:ℝ)+2)*pathAngle r k) := by
    split_ifs with hi
    · unfold pathSine
      congr 1
      push_cast
      ring
    · have he : i.val=r := by omega
      rw [he]
      have h : ((r:ℝ)+2)*pathAngle r k = ((k.val+1:ℕ):ℝ)*Real.pi := by
        unfold pathAngle
        push_cast
        field_simp
      rw [h, Real.sin_nat_mul_pi]
  rw [hl,hr]
  unfold pathSine
  rw [show (i.val:ℝ)*pathAngle r k = ((i.val:ℝ)+1)*pathAngle r k-pathAngle r k by ring,
    show ((i.val:ℝ)+2)*pathAngle r k = ((i.val:ℝ)+1)*pathAngle r k+pathAngle r k by ring,
    Real.sin_sub,Real.sin_add]
  ring

def pathSineVector (r : ℕ) (k : Fin (r+1)) : EuclideanSpace ℝ (Fin (r+1)) :=
  WithLp.toLp 2 (fun i => pathSine r k i)

def pathAdjOp (r : ℕ) : EuclideanSpace ℝ (Fin (r+1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (r+1)) :=
  Matrix.toEuclideanLin (pathAdjacency r)

theorem pathAdjOp_symmetric (r : ℕ) : (pathAdjOp r).IsSymmetric :=
  Matrix.isHermitian_iff_isSymmetric.1 (pathAdjacency_hermitian r)

theorem pathSineVector_eigen (r : ℕ) (k : Fin (r+1)) :
    pathAdjOp r (pathSineVector r k) = (2*Real.cos (pathAngle r k)) • pathSineVector r k := by
  ext i
  exact pathSine_eigen r k i

theorem pathSineVector_ne_zero (r : ℕ) (k : Fin (r+1)) : pathSineVector r k ≠ 0 := by
  intro h
  have e := congrArg (fun v : EuclideanSpace ℝ (Fin (r+1)) => v (0 : Fin (r+1))) h
  have hp := Real.sin_pos_of_pos_of_lt_pi (pathAngle_bounds r k).1 (pathAngle_bounds r k).2
  simp [pathSineVector,pathSine] at e
  linarith

theorem pathCos_ne (r : ℕ) (i j : Fin (r+1)) (hij : i≠j) :
    Real.cos (pathAngle r i) ≠ Real.cos (pathAngle r j) := by
  intro he
  have ha : pathAngle r i=pathAngle r j := Real.strictAntiOn_cos.injOn
    ⟨(pathAngle_bounds r i).1.le,(pathAngle_bounds r i).2.le⟩
    ⟨(pathAngle_bounds r j).1.le,(pathAngle_bounds r j).2.le⟩ he
  unfold pathAngle at ha
  have hd : (r:ℝ)+2 ≠ 0 := by positivity
  have hp : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  apply hij
  apply Fin.ext
  have hh : (i.val:ℝ)+1=(j.val:ℝ)+1 := by
    apply mul_right_cancel₀ hp
    exact (div_left_inj' hd).mp ha
  exact_mod_cast (show (i.val:ℝ)=(j.val:ℝ) by linarith)

theorem pathSine_orthogonal (r : ℕ) (i j : Fin (r+1)) (hij : i≠j) :
    ⟪pathSineVector r i,pathSineVector r j⟫=0 := by
  have he := pathAdjOp_symmetric r (pathSineVector r i) (pathSineVector r j)
  rw [pathSineVector_eigen, pathSineVector_eigen, real_inner_smul_left, real_inner_smul_right] at he
  have hn := pathCos_ne r i j hij
  by_contra h
  apply hn
  apply mul_right_cancel₀ h
  nlinarith

theorem pathSine_independent (r : ℕ) : LinearIndependent ℝ (pathSineVector r) :=
  linearIndependent_of_ne_zero_of_inner_eq_zero (pathSineVector_ne_zero r) (pathSine_orthogonal r)

theorem pathSine_span (r : ℕ) : Submodule.span ℝ (Set.range (pathSineVector r))=⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  rw [finrank_span_eq_card (pathSine_independent r), finrank_euclideanSpace]

end
end GaussianRange
#print axioms GaussianRange.pathSine_eigen
#print axioms GaussianRange.pathSine_independent
#print axioms GaussianRange.pathSine_span