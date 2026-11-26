import Integrated

namespace GaussianRange
open Finset
noncomputable section

theorem BathFamily.sigma_identity (b : BathFamily) (r : ℕ) (m : ℝ)
    (hm : 0 < m) (hb : b.admissible r m) (z : ℂ) (hz : ‖z‖ = 1) :
    sigma r b.coeff b.temp (m+2) z =
      ∑ v, weight r (b.coeff v) z * (b.temp v - dispersion (m+2) z)^2 /
        (b.temp v * dispersion (m+2) z) := by
  have hre := Complex.abs_re_le_norm z
  rw [hz] at hre
  have hd : 0 < dispersion (m+2) z := by
    unfold dispersion
    linarith [le_abs_self z.re]
  exact (entropy_identity (fun v => weight r (b.coeff v) z) b.temp
    (dispersion (m+2) z) hd hb.1 (hb.2.1 z hz) (hb.2.2 z hz)).symm

-- Variational inverse quadratic bound, without matrix square roots.
theorem inverse_variational {ι : Type} [Fintype ι] (T x y : ι → ℝ)
    (ht : ∀ i, 0 < T i) :
    (∑ i, (2*x i*y i - T i*(y i)^2)) ≤ ∑ i, (x i)^2/T i := by
  apply Finset.sum_le_sum
  intro i hi
  apply (le_div_iff₀ (ht i)).2
  nlinarith [sq_nonneg (x i - T i*y i)]

end
end GaussianRange
#print axioms GaussianRange.BathFamily.sigma_identity
#print axioms GaussianRange.inverse_variational
namespace GaussianRange
open Finset
noncomputable section

theorem BathFamily.cost_mono_unit (b b' : BathFamily) (r : ℕ) (m : ℝ)
    (h : ∀ z : ℂ, ‖z‖ = 1 → sigma r b'.coeff b'.temp (m+2) z ≤ sigma r b.coeff b.temp (m+2) z) :
    b'.cost r m ≤ b.cost r m := by
  unfold BathFamily.cost avg
  apply Real.circleAverage_mono ((cont_sigma r b'.coeff b'.temp (m+2)).continuousOn.circleIntegrable (by norm_num))
    ((cont_sigma r b.coeff b.temp (m+2)).continuousOn.circleIntegrable (by norm_num))
  intro z hz
  exact h z (norm_unit_of_mem z hz)

def restrictedCosts (r : ℕ) (m : ℝ) : Set ℝ :=
  {x | ∃ b : BathFamily, Fintype.card b.ι ≤ r+1 ∧ b.admissible r m ∧ b.cost r m = x}

theorem restricted_inf_eq_of_compression (r : ℕ) (m : ℝ) (hr : 0 < r) (hm : 0 < m)
    (hne : (admissibleCosts r m).Nonempty)
    (hc : ∀ b : BathFamily, b.admissible r m → ∃ b' : BathFamily,
      Fintype.card b'.ι ≤ r+1 ∧ b'.admissible r m ∧ b'.cost r m ≤ b.cost r m) :
    sInf (restrictedCosts r m) = optimalEntropy r m := by
  have hs : restrictedCosts r m ⊆ admissibleCosts r m := by
    rintro x ⟨b, _, hb, he⟩
    exact ⟨b, hb, he⟩
  have hlo : BddBelow (admissibleCosts r m) := ⟨_, fun x hx => admissible_lower r hr m hm x hx⟩
  have hlr : BddBelow (restrictedCosts r m) := hlo.mono hs
  have hnr : (restrictedCosts r m).Nonempty := by
    obtain ⟨x, b, hb, he⟩ := hne
    obtain ⟨b', hd, ha, _⟩ := hc b hb
    exact ⟨b'.cost r m, b', hd, ha, rfl⟩
  unfold optimalEntropy
  apply le_antisymm
  · apply le_csInf hne
    rintro x ⟨b, hb, he⟩
    obtain ⟨b', hd, ha, hle⟩ := hc b hb
    exact (csInf_le hlr (show b'.cost r m ∈ restrictedCosts r m from ⟨b', hd, ha, rfl⟩)).trans (he ▸ hle)
  · apply le_csInf hnr
    intro x hx
    exact csInf_le hlo (hs hx)

end
end GaussianRange
#print axioms GaussianRange.BathFamily.cost_mono_unit
#print axioms GaussianRange.restricted_inf_eq_of_compression