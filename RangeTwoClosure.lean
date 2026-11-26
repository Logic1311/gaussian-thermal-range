import RangeTwoExact

namespace GaussianRange
open Finset
noncomputable section

/-- Rescale the physical root bracket to the unit interval. -/
def r2Scale (m t : ℝ) : ℝ := (m+2)/4+m*t/8
def r2Lin (m : ℝ) : ℝ := 32*m*(m+2)^2*(m^2+4*m+2)*(m^2+4*m+5)
def r2Quad (m : ℝ) : ℝ := 8*m^2*(m+2)*(5*m^4+40*m^3+115*m^2+140*m+46)
def r2Cub (m : ℝ) : ℝ := 8*m^3*(m^2+4*m+2)*(m^2+4*m+6)
def r2Quart (m : ℝ) : ℝ := m^4*(m+2)^3

theorem r2_rescaled_identity (m t : ℝ) :
    128*range2N (m+2) (r2Scale m t)=
      128*range2N (m+2) ((m+2)/4)-r2Lin m*t-r2Quad m*t^2-r2Cub m*t^3+r2Quart m*t^4 := by
  unfold r2Scale range2N r2Lin r2Quad r2Cub r2Quart
  ring

theorem r2_lin_dominates (m : ℝ) (hm : 0<m) : 4*r2Quart m<r2Lin m := by
  have h : r2Lin m-4*r2Quart m=
    4*m*(m+2)^2*(7*m^4+62*m^3+184*m^2+224*m+80) := by
    unfold r2Lin r2Quart
    ring
  have hp : 0<4*m*(m+2)^2*(7*m^4+62*m^3+184*m^2+224*m+80) := by positivity
  linarith

theorem r2_quart_lipschitz (s t : ℝ) (hs : 0≤s) (hst : s≤t) (ht : t≤1) :
    t^4-s^4≤4*(t-s) := by
  have ht0 : 0≤t := hs.trans hst
  have hs1 : s≤1 := hst.trans ht
  have ht2 : t^2≤1 := by simpa using pow_le_pow_left₀ ht0 ht 2
  have hs2 : s^2≤1 := by simpa using pow_le_pow_left₀ hs hs1 2
  have ht3 : t^3≤1 := by simpa using pow_le_pow_left₀ ht0 ht 3
  have hs3 : s^3≤1 := by simpa using pow_le_pow_left₀ hs hs1 3
  have hts : t^2*s≤1 := by
    simpa using mul_le_mul ht2 hs1 hs (by norm_num : (0:ℝ)≤1)
  have hst' : t*s^2≤1 := by
    simpa using mul_le_mul ht hs2 (sq_nonneg s) (by norm_num : (0:ℝ)≤1)
  have hsum : t^3+t^2*s+t*s^2+s^3≤4 := by linarith
  calc
    t^4-s^4 = (t-s)*(t^3+t^2*s+t*s^2+s^3) := by ring
    _ ≤ (t-s)*4 := mul_le_mul_of_nonneg_left hsum (sub_nonneg.mpr hst)
    _ = 4*(t-s) := by ring

/-- Direct monotonicity proof, independent of the optimal-matrix uniqueness argument. -/
theorem r2_rescaled_strict (m s t : ℝ) (hm : 0<m) (hs : 0≤s) (hst : s<t) (ht : t≤1) :
    range2N (m+2) (r2Scale m t)<range2N (m+2) (r2Scale m s) := by
  have h1 := r2_lin_dominates m hm
  have hq : 0≤r2Quad m := by unfold r2Quad; positivity
  have hc : 0≤r2Cub m := by unfold r2Cub; positivity
  have h4 : 0≤r2Quart m := by unfold r2Quart; positivity
  have hsq := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs hst.le 2) hq
  have hcu := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs hst.le 3) hc
  have hquart := mul_le_mul_of_nonneg_left (r2_quart_lipschitz s t hs hst.le ht) h4
  have hstrict := mul_pos (sub_pos.mpr h1) (sub_pos.mpr hst)
  have hS := r2_rescaled_identity m s
  have hT := r2_rescaled_identity m t
  linarith only [hS,hT,hsq,hcu,hquart,hstrict]

theorem range2N_strictAntiOn (m : ℝ) (hm : 0<m) :
    StrictAntiOn (range2N (m+2)) (Set.Icc ((m+2)/4) ((3*(m+2)-2)/8)) := by
  intro x hx y hy hxy
  let s := 8*(x-(m+2)/4)/m
  let t := 8*(y-(m+2)/4)/m
  have hs : 0≤s := div_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hx.1)) hm.le
  have ht : t≤1 := by
    dsimp [t]
    apply (div_le_iff₀ hm).2
    linarith [hy.2]
  have hst : s<t := by
    dsimp [s,t]
    exact div_lt_div_of_pos_right (by linarith) hm
  have hx' : r2Scale m s=x := by
    unfold r2Scale
    dsimp [s]
    field_simp [hm.ne']
    <;> ring
  have hy' : r2Scale m t=y := by
    unfold r2Scale
    dsimp [t]
    field_simp [hm.ne']
    <;> ring
  rw [← hy',← hx']
  exact r2_rescaled_strict m s t hm hs hst ht

theorem range2_root_strict (m e : ℝ) (hm : 0<m) (hr : Range2Root (m+2) e) :
    (m+2)/4<e ∧ e<(3*(m+2)-2)/8 := by
  obtain ⟨hl,hu,hN⟩ := hr
  have hp : 0<range2N (m+2) ((m+2)/4) := by rw [range2N_left]; positivity
  have hn : range2N (m+2) ((3*(m+2)-2)/8)<0 := by
    rw [range2N_right]
    have h : 0<m*(63*m^6+618*m^5+2380*m^4+4552*m^3+4368*m^2+2144*m+768)/128 := by positivity
    linarith
  constructor
  · by_contra! h
    have he : e=(m+2)/4 := le_antisymm h hl
    rw [he] at hN
    linarith
  · by_contra! h
    have he : e=(3*(m+2)-2)/8 := le_antisymm hu h
    rw [he] at hN
    linarith

theorem range2_root_unique (m : ℝ) (hm : 0<m) : ∃! e,Range2Root (m+2) e := by
  obtain ⟨e,he⟩ := range2_root_exists m hm
  refine ⟨e,he,?_⟩
  intro x hx
  have ha := range2N_strictAntiOn m hm
  have hem : e∈Set.Icc ((m+2)/4) ((3*(m+2)-2)/8) := ⟨he.1,he.2.1⟩
  have hxm : x∈Set.Icc ((m+2)/4) ((3*(m+2)-2)/8) := ⟨hx.1,hx.2.1⟩
  rcases lt_trichotomy x e with h|h|h
  · have h' := ha hxm hem h
    rw [hx.2.2,he.2.2] at h'
    exact (lt_irrefl _ h').elim
  · exact h
  · have h' := ha hem hxm h
    rw [hx.2.2,he.2.2] at h'
    exact (lt_irrefl _ h').elim

/-- The unique strict-bracket root determines the exact physical cost, not merely a relaxed value. -/
theorem range2_any_root_exact (m e : ℝ) (hm : 0<m) (hr : Range2Root (m+2) e) :
    optimalEntropy 2 m=range2Value (m+2) e ∧
      ∃ b : BathFamily, Fintype.card b.ι≤3 ∧ b.admissible 2 m ∧
        b.cost 2 m=optimalEntropy 2 m ∧ ¬b.twoTemperature := by
  obtain ⟨x,hx,hval,b,hcard,hb,hcost,ht⟩ := range2_exact_attained m hm
  obtain ⟨y,hy,hu⟩ := range2_root_unique m hm
  have hxe : x=e := (hu x hx).trans (hu e hr).symm
  rw [hxe] at hval
  exact ⟨hval,b,hcard,hb,hcost,ht⟩

theorem palette_two_is_twoTemperature (b : BathFamily) (hp : ∀ v,0<b.temp v)
    (h : b.temperaturePalette 2) : b.twoTemperature := by
  obtain ⟨τ,hτ⟩ := h
  let f (t : ℝ) := if 0<t then t else 1
  have hf (t : ℝ) : 0<f t := by dsimp [f]; split_ifs <;> positivity
  let a := f (τ 0)
  let d := f (τ 1)
  have ht (v : b.ι) : b.temp v=a ∨ b.temp v=d := by
    obtain ⟨i,hi⟩ := hτ v
    fin_cases i
    · left
      dsimp [a,f]
      rw [if_pos (hi ▸ hp v)]
      exact hi
    · right
      dsimp [d,f]
      rw [if_pos (hi ▸ hp v)]
      exact hi
  by_cases hle : a≤d
  · exact ⟨a,d,hf _,hle,ht⟩
  · exact ⟨d,a,hf _,le_of_not_ge hle,fun v => (ht v).symm⟩

theorem range2_every_optimum_resources (m : ℝ) (hm : 0<m) (b : BathFamily)
    (hb : b.admissible 2 m) (hc : b.cost 2 m=optimalEntropy 2 m) :
    3≤Fintype.card b.ι ∧ ¬b.temperaturePalette 2 := by
  have hnot : ¬ b.temperaturePalette 2 := by
    intro hpal
    have hlo := two_temperature_cost_lower b 2 (by decide) m hm hb
      (palette_two_is_twoTemperature b hb.1 hpal)
    rw [hc] at hlo
    have hhi := (unrestricted_strict_two_temperature_gap 2 (by decide) m hm).1
    have hpos : 0<m*(m+4) := by positivity
    have hs : 1/(m*(m+4))<2/(m*(m+4)) := div_lt_div_of_pos_right (by norm_num) hpos
    exact (not_le_of_gt (hhi.trans_lt hs)) hlo
  exact ⟨by by_contra! hn; exact hnot (palette_of_card b 2 (by omega)),hnot⟩

/-- All-mass exact formula and actual minimal-resource attainment; no assertion for r>2. -/
theorem range2_complete (m : ℝ) (hm : 0<m) :
    ∃! e : ℝ, (m+2)/4<e ∧ e<(3*(m+2)-2)/8 ∧ range2N (m+2) e=0 ∧
      optimalEntropy 2 m=range2Value (m+2) e ∧
      (∃ b : BathFamily, Fintype.card b.ι=3 ∧ b.admissible 2 m ∧
        b.cost 2 m=optimalEntropy 2 m ∧ b.temperaturePalette 3 ∧ ¬b.temperaturePalette 2) := by
  obtain ⟨e,he,hu⟩ := range2_root_unique m hm
  obtain ⟨hl,hr⟩ := range2_root_strict m e hm he
  obtain ⟨hv,b,hcard,hb,hcost,ht⟩ := range2_any_root_exact m e hm he
  obtain ⟨hlo,hn⟩ := range2_every_optimum_resources m hm b hb hcost
  refine ⟨e,⟨hl,hr,he.2.2,hv,b,le_antisymm hcard hlo,hb,hcost,palette_of_card b 3 hcard,hn⟩,?_⟩
  intro x hx
  exact hu x ⟨hx.1.le,hx.2.1.le,hx.2.2.1⟩

end
end GaussianRange
#check GaussianRange.range2_complete
#print axioms GaussianRange.range2N_strictAntiOn
#print axioms GaussianRange.range2_root_unique
#print axioms GaussianRange.range2_root_strict
#print axioms GaussianRange.range2_any_root_exact
#print axioms GaussianRange.range2_every_optimum_resources
#print axioms GaussianRange.range2_complete
