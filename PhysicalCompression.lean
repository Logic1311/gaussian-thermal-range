import CompressionExistence

namespace GaussianRange
open Finset Polynomial
open scoped RealInnerProductSpace
noncomputable section

def bathColumn (b : BathFamily) (r : ℕ) (j : Fin (r+1)) : BathSpace b.ι :=
  WithLp.toLp 2 (fun i => b.coeff i j)

def bathSpan (b : BathFamily) (r : ℕ) : Submodule ℝ (BathSpace b.ι) :=
  Submodule.span ℝ (Set.range (bathColumn b r))

def bathColumnIn (b : BathFamily) (r : ℕ) (j : Fin (r+1)) : bathSpan b r :=
  ⟨bathColumn b r j, Submodule.subset_span ⟨j,rfl⟩⟩

def bathEval (b : BathFamily) (r : ℕ) (f : Fin (r+1) → ℝ) : bathSpan b r :=
  ∑ j, f j • bathColumnIn b r j

theorem bathEval_apply (b : BathFamily) (r : ℕ) (f : Fin (r+1) → ℝ) (i : b.ι) :
    (bathEval b r f).val i = ∑ j : Fin (r+1), b.coeff i j * f j := by
  simp [bathEval, bathColumnIn, bathColumn, mul_comm]

def compressedBath (b : BathFamily) (r : ℕ) : BathFamily where
  ι := Fin (Module.finrank ℝ (bathSpan b r))
  finite := inferInstance
  coeff := fun v j => if h : j < r+1 then ⟪compressedBasis b.temp (bathSpan b r) v, bathColumnIn b r ⟨j,h⟩⟫ else 0
  temp := compressedTemp b.temp (bathSpan b r)

theorem compressedBath_count (b : BathFamily) (r : ℕ) :
    Fintype.card (compressedBath b r).ι ≤ r+1 := by
  change Fintype.card (Fin (Module.finrank ℝ (bathSpan b r))) ≤ r+1
  simpa [bathSpan, Set.finrank] using (finrank_range_le_card (R := ℝ) (bathColumn b r))

theorem compressedCoeff_fin (b : BathFamily) (r : ℕ) (v : (compressedBath b r).ι) (j : Fin (r+1)) :
    (compressedBath b r).coeff v j = ⟪compressedBasis b.temp (bathSpan b r) v, bathColumnIn b r j⟫ := by
  simp [compressedBath, j.isLt]

theorem compressed_eval (b : BathFamily) (r : ℕ) (v : (compressedBath b r).ι) (f : Fin (r+1) → ℝ) :
    (∑ j : Fin (r+1), (compressedBath b r).coeff v j * f j) = ⟪compressedBasis b.temp (bathSpan b r) v, bathEval b r f⟫ := by
  rw [bathEval, inner_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [real_inner_smul_right, compressedCoeff_fin]
  ring

theorem weight_fin (r : ℕ) (a : ℕ → ℝ) (z : ℂ) :
    weight r a z = (∑ j : Fin (r+1), a j * (z^(j:ℕ)).re)^2 +
      (∑ j : Fin (r+1), a j * (z^(j:ℕ)).im)^2 := by
  unfold weight
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  have he : (amp r a).eval z = ∑ j : Fin (r+1), (a j : ℂ)*z^(j:ℕ) := by
    rw [amp_eval]
    exact (Fin.sum_univ_eq_sum_range (fun j : ℕ => (a j : ℂ)*z^j) (r+1)).symm
  rw [he]
  simp [Complex.mul_re, Complex.mul_im, pow_two]

theorem compressed_gram_coeff (b : BathFamily) (r : ℕ) (i j : Fin (r+1)) :
    (∑ v, (compressedBath b r).coeff v i * (compressedBath b r).coeff v j) = ∑ v, b.coeff v i * b.coeff v j := by
  simp_rw [compressedCoeff_fin]
  exact compressed_gram b.temp (bathSpan b r) (bathColumnIn b r i) (bathColumnIn b r j)

theorem compressed_weighted_gram_coeff (b : BathFamily) (r : ℕ) (i j : Fin (r+1)) :
    (∑ v, (compressedBath b r).temp v * (compressedBath b r).coeff v i * (compressedBath b r).coeff v j) =
      ∑ v, b.temp v * b.coeff v i * b.coeff v j := by
  simp_rw [compressedCoeff_fin]
  exact compressed_weighted_gram b.temp (bathSpan b r) (bathColumnIn b r i) (bathColumnIn b r j)

theorem compressed_weight_sum (b : BathFamily) (r : ℕ) (z : ℂ) :
    (∑ v, weight r ((compressedBath b r).coeff v) z) = ∑ v, weight r (b.coeff v) z := by
  have hx := compressed_parseval b.temp (bathSpan b r) (bathEval b r (fun j => (z^(j:ℕ)).re))
  have hy := compressed_parseval b.temp (bathSpan b r) (bathEval b r (fun j => (z^(j:ℕ)).im))
  simp_rw [← compressed_eval, bathEval_apply] at hx hy
  simp_rw [weight_fin, Finset.sum_add_distrib]
  exact congrArg₂ (· + ·) hx hy

theorem compressed_temp_weight_sum (b : BathFamily) (r : ℕ) (z : ℂ) :
    (∑ v, (compressedBath b r).temp v * weight r ((compressedBath b r).coeff v) z) =
      ∑ v, b.temp v * weight r (b.coeff v) z := by
  have hx := compressed_weighted b.temp (bathSpan b r) (bathEval b r (fun j => (z^(j:ℕ)).re))
  have hy := compressed_weighted b.temp (bathSpan b r) (bathEval b r (fun j => (z^(j:ℕ)).im))
  simp_rw [← compressed_eval, bathEval_apply] at hx hy
  simp_rw [weight_fin, mul_add, Finset.sum_add_distrib]
  exact congrArg₂ (· + ·) hx hy

theorem compressed_inverse_weight_sum (b : BathFamily) (r : ℕ) (ht : ∀ v, 0 < b.temp v) (z : ℂ) :
    (∑ v, weight r ((compressedBath b r).coeff v) z / (compressedBath b r).temp v) ≤
      ∑ v, weight r (b.coeff v) z / b.temp v := by
  have hx := compressed_inverse b.temp (bathSpan b r) ht (bathEval b r (fun j => (z^(j:ℕ)).re))
  have hy := compressed_inverse b.temp (bathSpan b r) ht (bathEval b r (fun j => (z^(j:ℕ)).im))
  simp_rw [← compressed_eval, bathEval_apply] at hx hy
  simp_rw [weight_fin, add_div, Finset.sum_add_distrib]
  exact add_le_add hx hy

theorem compressed_admissible (b : BathFamily) (r : ℕ) (m : ℝ) (hb : b.admissible r m) :
    (compressedBath b r).admissible r m := by
  refine ⟨fun v => compressedTemp_pos b.temp (bathSpan b r) hb.1 v, ?_, ?_⟩
  · intro z hz
    rw [compressed_weight_sum]
    exact hb.2.1 z hz
  · intro z hz
    rw [compressed_temp_weight_sum]
    exact hb.2.2 z hz

theorem compressed_sigma_le (b : BathFamily) (r : ℕ) (m : ℝ) (hm : 0 < m)
    (ht : ∀ v, 0 < b.temp v) (z : ℂ) (hz : ‖z‖ = 1) :
    sigma r (compressedBath b r).coeff (compressedBath b r).temp (m+2) z ≤ sigma r b.coeff b.temp (m+2) z := by
  have hre := Complex.abs_re_le_norm z
  rw [hz] at hre
  have hd : 0 ≤ dispersion (m+2) z := by unfold dispersion; linarith [le_abs_self z.re]
  unfold sigma
  exact sub_le_sub_right (mul_le_mul_of_nonneg_left (compressed_inverse_weight_sum b r ht z) hd) 1

theorem compress_admissible (b : BathFamily) (r : ℕ) (m : ℝ) (hm : 0 < m) (hb : b.admissible r m) :
    ∃ b' : BathFamily, Fintype.card b'.ι ≤ r+1 ∧ b'.admissible r m ∧
      (∀ z : ℂ, ‖z‖ = 1 → sigma r b'.coeff b'.temp (m+2) z ≤ sigma r b.coeff b.temp (m+2) z) :=
  ⟨compressedBath b r, compressedBath_count b r, compressed_admissible b r m hb,
    fun z hz => compressed_sigma_le b r m hm hb.1 z hz⟩

end
end GaussianRange
#print axioms GaussianRange.compressed_gram_coeff
#print axioms GaussianRange.compressed_weighted_gram_coeff
#print axioms GaussianRange.compressed_inverse_weight_sum
#print axioms GaussianRange.compress_admissible