import PhysicalInfimum
namespace GaussianRange
open Finset
open scoped RealInnerProductSpace
noncomputable section

-- The column space of the cyclic frame is the real path subspace.
def pathBath (r : ℕ) (m : ℝ) : BathFamily := compressedBath (rationalBath r m) r

def pathAdj (r : ℕ) : Matrix (Fin (r+1)) (Fin (r+1)) ℝ :=
  fun i j => if (i:ℕ)+1=j.val ∨ j.val+1=i.val then 1 else 0

def pathTemperatureMatrix (r : ℕ) (m : ℝ) : Matrix (Fin (r+1)) (Fin (r+1)) ℝ :=
  fun i j => (if i=j then m+2 else 0) - pathAdj r i j / rationalRho (r+1)

theorem rational_column_inner (r : ℕ) (m : ℝ) (i j : Fin (r+1)) :
    ⟪bathColumn (rationalBath r m) r i, bathColumn (rationalBath r m) r j⟫ =
      if i=j then (rationalWindow (r+1) i)^2 else 0 := by
  change (∑ v : ZMod (2*r+5) × Bool, realChannel (2*r+5) (rationalWindow (r+1)) v j *
    star (realChannel (2*r+5) (rationalWindow (r+1)) v i)) = _
  simp only [star_trivial]
  simp_rw [mul_comm (realChannel (2*r+5) (rationalWindow (r+1)) _ j)]
  rw [channel_gram]
  simp only [(no_alias_eq r i j (by omega) (by omega))]
  by_cases h : i=j
  · subst j; simp [pow_two]
  · have h' : (i:ℕ) ≠ (j:ℕ) := fun h' => h (Fin.ext h')
    simp [h,h']

theorem rationalWindow_pos_fin (r : ℕ) (hr : 0 < r) (i : Fin (r+1)) :
    0 < rationalWindow (r+1) i := by
  unfold rationalWindow rawWindow
  apply div_pos
  · have hi : (i.val:ℝ) < ((r+1:ℕ):ℝ) := by exact_mod_cast i.isLt
    exact mul_pos (by positivity) (sub_pos.mpr hi)
  · exact Real.sqrt_pos.2 (windowNorm_pos (r+1) (by omega))

theorem rational_column_independent (r : ℕ) (hr : 0 < r) (m : ℝ) :
    LinearIndependent ℝ (bathColumn (rationalBath r m) r) := by
  apply linearIndependent_of_ne_zero_of_inner_eq_zero
  · intro i hi
    have h := rational_column_inner r m i i
    rw [hi, inner_zero_left, if_pos rfl] at h
    exact (ne_of_gt (sq_pos_of_pos (rationalWindow_pos_fin r hr i))) h.symm
  · intro i j hij
    rw [rational_column_inner, if_neg hij]

theorem pathBath_count (r : ℕ) (hr : 0 < r) (m : ℝ) : Fintype.card (pathBath r m).ι = r+1 := by
  change Fintype.card (Fin (Module.finrank ℝ (bathSpan (rationalBath r m) r))) = r+1
  rw [Fintype.card_fin, bathSpan, finrank_span_eq_card (rational_column_independent r hr m), Fintype.card_fin]

theorem pathBath_normalization (r : ℕ) (hr : 0 < r) (m : ℝ) (z : ℂ) (hz : ‖z‖=1) :
    (∑ v, weight r ((pathBath r m).coeff v) z)=1 := by
  unfold pathBath
  rw [compressed_weight_sum]
  exact physical_channel_normalization r (rationalWindow (r+1)) (rationalWindow_norm _ (by omega)) z hz

theorem pathBath_weighted_normalization (r : ℕ) (hr : 0 < r) (m : ℝ) (z : ℂ) (hz : ‖z‖=1) :
    (∑ v, (pathBath r m).temp v * weight r ((pathBath r m).coeff v) z)=dispersion (m+2) z := by
  unfold pathBath
  rw [compressed_temp_weight_sum]
  exact physical_channel_weighted_normalization r hr (rationalWindow (r+1)) (m+2) (rationalRho (r+1))
    (ne_of_gt (rationalRho_pos _ (by omega))) (rationalWindow_norm _ (by omega)) (rationalWindow_correlation r hr) z hz

theorem pathBath_gram (r : ℕ) (m : ℝ) (i j : Fin (r+1)) :
    (∑ v, (pathBath r m).coeff v i * (pathBath r m).coeff v j) =
      if i=j then (rationalWindow (r+1) i)^2 else 0 := by
  unfold pathBath
  rw [compressed_gram_coeff]
  have h := rational_column_inner r m i j
  change (∑ v : ZMod (2*r+5) × Bool, realChannel (2*r+5) (rationalWindow (r+1)) v j *
    star (realChannel (2*r+5) (rationalWindow (r+1)) v i)) = _ at h
  simp only [star_trivial] at h
  simpa [rationalBath, mul_comm] using h

theorem pathBath_weighted_gram (r : ℕ) (m : ℝ) (i j : Fin (r+1)) :
    (∑ v, (pathBath r m).temp v * ((pathBath r m).coeff v i * (pathBath r m).coeff v j)) =
      rationalWindow (r+1) i * pathTemperatureMatrix r m i j * rationalWindow (r+1) j := by
  simp_rw [← mul_assoc]
  unfold pathBath
  rw [compressed_weighted_gram_coeff]
  simp_rw [mul_assoc]
  change (∑ v : ZMod (2*r+5) × Bool, channelTemp (2*r+5) (m+2) (rationalRho (r+1)) v *
    (realChannel (2*r+5) (rationalWindow (r+1)) v i * realChannel (2*r+5) (rationalWindow (r+1)) v j)) = _
  rw [channel_weighted_gram]
  simp only [(no_alias_eq r i j (by omega) (by omega)),
    (no_alias_succ r i j (by omega) (by omega)), (no_alias_pred r i j (by omega) (by omega))]
  unfold pathTemperatureMatrix pathAdj
  by_cases he : i=j
  · subst j; simp; ring
  · have h' : (i:ℕ) ≠ (j:ℕ) := fun h' => he (Fin.ext h')
    by_cases h₁ : (i:ℕ)+1=j.val
    · have h₂ : j.val+1 ≠ i.val := by omega
      simp [he,h',h₁,h₂]; ring
    · by_cases h₂ : j.val+1=i.val
      · simp [he,h',h₁,h₂]; ring
      · simp [he,h',h₁,h₂]

theorem pathBath_admissible_of_cyclic (r : ℕ) (hr : 0 < r) (m : ℝ) (hm : 0 < m)
    (hL : 5+10/m < windowL (r+1)) : (pathBath r m).admissible r m :=
  compressed_admissible (rationalBath r m) r m (rational_physical_realization r hr m hm hL)

theorem pathBath_sigma_le_cyclic (r : ℕ) (hr : 0 < r) (m : ℝ) (hm : 0 < m)
    (hL : 5+10/m < windowL (r+1)) (z : ℂ) (hz : ‖z‖=1) :
    sigma r (pathBath r m).coeff (pathBath r m).temp (m+2) z ≤
      sigma r (rationalBath r m).coeff (rationalBath r m).temp (m+2) z :=
  compressed_sigma_le (rationalBath r m) r m hm (rational_physical_realization r hr m hm hL).1 z hz

theorem pathBath_cost_le_cyclic (r : ℕ) (hr : 0 < r) (m : ℝ) (hm : 0 < m)
    (hL : 5+10/m < windowL (r+1)) : (pathBath r m).cost r m ≤ (rationalBath r m).cost r m :=
  BathFamily.cost_mono_unit (rationalBath r m) (pathBath r m) r m (pathBath_sigma_le_cyclic r hr m hm hL)

end
end GaussianRange
#print axioms GaussianRange.pathBath_count
#print axioms GaussianRange.pathBath_normalization
#print axioms GaussianRange.pathBath_weighted_normalization
#print axioms GaussianRange.pathBath_gram
#print axioms GaussianRange.pathBath_weighted_gram
#print axioms GaussianRange.pathBath_sigma_le_cyclic
#print axioms GaussianRange.pathBath_cost_le_cyclic