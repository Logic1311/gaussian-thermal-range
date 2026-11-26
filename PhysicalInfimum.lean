import PhysicalCompression
import Compression
import Boundary
namespace GaussianRange
noncomputable section

theorem compress_admissible_cost (b : BathFamily) (r : ℕ) (m : ℝ)
    (hm : 0 < m) (hb : b.admissible r m) :
    ∃ b' : BathFamily, Fintype.card b'.ι ≤ r+1 ∧ b'.admissible r m ∧
      b'.cost r m ≤ b.cost r m := by
  obtain ⟨b', hcard, ha, hp⟩ := compress_admissible b r m hm hb
  exact ⟨b', hcard, ha, BathFamily.cost_mono_unit b b' r m hp⟩

theorem restricted_inf_eq (r : ℕ) (hr : 0 < r) (m : ℝ) (hm : 0 < m) :
    sInf (restrictedCosts r m) = optimalEntropy r m :=
  restricted_inf_eq_of_compression r m hr hm (admissibleCosts_nonempty_all r hr m hm)
    (fun b hb => compress_admissible_cost b r m hm hb)

theorem compressed_rank_pos (b : BathFamily) (r : ℕ) (m : ℝ) (hb : b.admissible r m) :
    0 < Module.finrank ℝ (bathSpan b r) := by
  by_contra! h
  have he : Module.finrank ℝ (bathSpan b r) = 0 := by omega
  have hc := (compressed_admissible b r m hb).2.1 (1 : ℂ) (by norm_num)
  have hcard : Fintype.card (compressedBath b r).ι = 0 := by simp [compressedBath, he]
  letI : IsEmpty (compressedBath b r).ι := Fintype.card_eq_zero_iff.mp hcard
  simp at hc

end
end GaussianRange
#print axioms GaussianRange.compress_admissible_cost
#print axioms GaussianRange.restricted_inf_eq
#print axioms GaussianRange.compressed_rank_pos