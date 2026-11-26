import TemperatureResourceLower

namespace GaussianRange
open Finset Polynomial
noncomputable section

def paletteCosts (r K : ℕ) (m : ℝ) : Set ℝ :=
  {x | ∃ b : BathFamily, b.admissible r m ∧ b.temperaturePalette K ∧ b.cost r m=x}

def optimalPaletteEntropy (r K : ℕ) (m : ℝ) : ℝ := sInf (paletteCosts r K m)

theorem palette_of_card (b : BathFamily) (K : ℕ)
    (hcard : Fintype.card b.ι≤K) : b.temperaturePalette K := by
  let e := Fintype.equivFin b.ι
  let τ : Fin K → ℝ := fun i =>
    if hi : i.val<Fintype.card b.ι then b.temp (e.symm ⟨i.val,hi⟩) else 1
  refine ⟨τ,?_⟩
  intro v
  let i : Fin K := ⟨(e v).val,lt_of_lt_of_le (e v).isLt hcard⟩
  refine ⟨i,?_⟩
  have hi : i.val<Fintype.card b.ι := (e v).isLt
  simp only [τ,dif_pos hi]
  have he : (⟨i.val,hi⟩ : Fin (Fintype.card b.ι))=e v := by rfl
  rw [he,e.symm_apply_apply]

theorem padded_amp (n r : ℕ) (hnr : n≤r) (a : ℕ → ℝ) :
    amp r (cutCoeff n a)=amp n a := by
  ext j
  rw [amp_coeff,amp_coeff]
  unfold cutCoeff
  by_cases hj : j≤n
  · simp [hj,hj.trans hnr]
  · simp [hj]

def paddedBath (b : BathFamily) (n : ℕ) : BathFamily where
  ι := b.ι
  finite := b.finite
  coeff := fun v => cutCoeff n (b.coeff v)
  temp := b.temp

theorem padded_weight (b : BathFamily) (n r : ℕ) (hnr : n≤r)
    (v : b.ι) (z : ℂ) :
    weight r ((paddedBath b n).coeff v) z=weight n (b.coeff v) z := by
  unfold paddedBath weight
  rw [padded_amp n r hnr]

theorem padded_admissible (b : BathFamily) (n r : ℕ) (hnr : n≤r)
    (m : ℝ) (hb : b.admissible n m) : (paddedBath b n).admissible r m := by
  refine ⟨hb.1,?_,?_⟩
  · intro z hz
    change (∑ v : b.ι,weight r ((paddedBath b n).coeff v) z)=1
    simp_rw [padded_weight b n r hnr]
    exact hb.2.1 z hz
  · intro z hz
    change (∑ v : b.ι,b.temp v*weight r ((paddedBath b n).coeff v) z)=_
    simp_rw [padded_weight b n r hnr]
    exact hb.2.2 z hz

theorem padded_cost (b : BathFamily) (n r : ℕ) (hnr : n≤r) (m : ℝ) :
    (paddedBath b n).cost r m=b.cost n m := by
  unfold BathFamily.cost sigma
  have he : (fun z => dispersion (m+2) z*
      (∑ v : b.ι,weight r ((paddedBath b n).coeff v) z/b.temp v)-1)=
      (fun z => dispersion (m+2) z*
      (∑ v : b.ι,weight n (b.coeff v) z/b.temp v)-1) := by
    funext z
    simp_rw [padded_weight b n r hnr]
  exact congrArg avg he

theorem padded_palette (b : BathFamily) (n K : ℕ) (hb : b.temperaturePalette K) :
    (paddedBath b n).temperaturePalette K := hb

theorem palette_nearest_mem (r K : ℕ) (hr : 0<r) (hK : 2≤K) (m : ℝ) (hm : 0<m) :
    2/(m*(m+4))∈paletteCosts r K m := by
  refine ⟨nearestBath m,nearest_admissible r hr m hm,?_,nearest_cost_exact r hr m hm⟩
  apply palette_of_card
  simpa [nearestBath] using hK

theorem palette_bddBelow (r K : ℕ) (hr : 0<r) (m : ℝ) (hm : 0<m) :
    BddBelow (paletteCosts r K m) := by
  refine ⟨1/((m+2)*(m+4)*(r:ℝ)^2),?_⟩
  rintro x ⟨b,hb,hpal,he⟩
  exact admissible_lower r hr m hm x ⟨b,hb,he⟩

theorem palette_inf_lower (r K : ℕ) (hr : 0<r) (hK : 2≤K) (m : ℝ) (hm : 0<m) :
    (1/((m+2)*(m+4)*(r:ℝ)^2)≤optimalPaletteEntropy r K m) ∧
    (1/(64*Real.pi*(m+4)^2*(K:ℝ)^2)≤optimalPaletteEntropy r K m) := by
  have hn : (paletteCosts r K m).Nonempty := ⟨_,palette_nearest_mem r K hr hK m hm⟩
  constructor
  · apply le_csInf hn
    rintro x ⟨b,hb,hpal,he⟩
    exact admissible_lower r hr m hm x ⟨b,hb,he⟩
  · apply le_csInf hn
    rintro x ⟨b,hb,hpal,rfl⟩
    exact palette_cost_lower b r K (by omega) m hm hb hpal

/-- Any degree-n family can be compressed to n+1 channels and zero-padded
to degree r. This is an upper bound on the actual palette-constrained infimum,
not a converse claim that a temperature constraint is a support constraint. -/
theorem palette_inf_le_range (r K n : ℕ) (hn : 0<n) (hnr : n≤r) (hnK : n+1≤K)
    (m : ℝ) (hm : 0<m) :
    optimalPaletteEntropy r K m≤optimalEntropy n m := by
  have hr : 0<r := hn.trans_le hnr
  have hbd := palette_bddBelow r K hr m hm
  apply le_csInf (admissibleCosts_nonempty_all n hn m hm)
  rintro x ⟨b,hb,rfl⟩
  obtain ⟨c,hcard,hc,hcost⟩ := compress_admissible_cost b n m hm hb
  let d := paddedBath c n
  have hdp : d.temperaturePalette K := padded_palette c n K (palette_of_card c K (hcard.trans hnK))
  have hda : d.admissible r m := padded_admissible c n r hnr m hc
  have hmem : d.cost r m∈paletteCosts r K m := ⟨d,hda,hdp,rfl⟩
  have hdc : d.cost r m=c.cost n m := padded_cost c n r hnr m
  exact (csInf_le hbd hmem).trans (hdc.symm ▸ hcost)

theorem palette_joint_resource_scaling (m : ℝ) (hm : 0<m) :
    ∃ A B : ℝ, 0<A ∧ 0<B ∧ ∀ r K : ℕ, 0<r → 2≤K →
      A/((min r K:ℕ):ℝ)^2 ≤ optimalPaletteEntropy r K m ∧
      optimalPaletteEntropy r K m≤ B/((min r (K-1):ℕ):ℝ)^2 := by
  let A₁ : ℝ := 1/((m+2)*(m+4))
  let A₂ : ℝ := 1/(64*Real.pi*(m+4)^2)
  let A := min A₁ A₂
  have hA₁ : 0<A₁ := by dsimp [A₁]; positivity
  have hA₂ : 0<A₂ := by dsimp [A₂]; positivity
  have hA : 0<A := lt_min hA₁ hA₂
  obtain ⟨C₁,C₂,hC₁,hC₂,R,hR,hθ⟩ := optimalEntropy_theta m hm
  let N : ℝ := 2/(m*(m+4))
  let B := max C₂ ((R:ℝ)^2*N)
  have hN : 0<N := by dsimp [N]; positivity
  have hB : 0<B := hC₂.trans_le (le_max_left _ _)
  refine ⟨A,B,hA,hB,?_⟩
  intro r K hr hK
  obtain ⟨hlr,hlK⟩ := palette_inf_lower r K hr hK m hm
  have hlr' : A₁/(r:ℝ)^2≤optimalPaletteEntropy r K m := by
    simpa [A₁,div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc] using hlr
  have hlK' : A₂/(K:ℝ)^2≤optimalPaletteEntropy r K m := by
    simpa [A₂,div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc] using hlK
  constructor
  · by_cases h : r≤K
    · rw [Nat.min_eq_left h]
      exact (div_le_div_of_nonneg_right (min_le_left _ _) (sq_nonneg _)).trans hlr'
    · rw [Nat.min_eq_right (by omega : K≤r)]
      exact (div_le_div_of_nonneg_right (min_le_right _ _) (sq_nonneg _)).trans hlK'
  · let n := min r (K-1)
    have hn : 0<n := by dsimp [n]; exact lt_min hr (by omega)
    have hnr : n≤r := min_le_left _ _
    have hnK : n+1≤K := by have h := min_le_right r (K-1); dsimp [n]; omega
    change optimalPaletteEntropy r K m≤B/(n:ℝ)^2
    by_cases h : R≤n
    · obtain ⟨hne,hl,hu⟩ := hθ n h
      exact (palette_inf_le_range r K n hn hnr hnK m hm).trans
        (hu.trans (div_le_div_of_nonneg_right (le_max_left _ _) (sq_nonneg _)))
    · have hu : optimalPaletteEntropy r K m≤N :=
        csInf_le (palette_bddBelow r K hr m hm) (palette_nearest_mem r K hr hK m hm)
      apply hu.trans
      apply (le_div_iff₀ (by positivity : 0<(n:ℝ)^2)).2
      have hnR : (n:ℝ)≤R := by exact_mod_cast (show n≤R by omega)
      have hnsq := pow_le_pow_left₀ (by positivity : 0≤(n:ℝ)) hnR 2
      have hmul := mul_le_mul_of_nonneg_left hnsq hN.le
      have hmul' : N*(n:ℝ)^2≤(R:ℝ)^2*N := by simpa [mul_comm] using hmul
      exact hmul'.trans (le_max_right _ _)

end
end GaussianRange
#check GaussianRange.palette_joint_resource_scaling
#print axioms GaussianRange.palette_inf_lower
#print axioms GaussianRange.palette_inf_le_range
#print axioms GaussianRange.palette_joint_resource_scaling
