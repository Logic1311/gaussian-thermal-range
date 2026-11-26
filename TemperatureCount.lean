import CriticalScaling

namespace GaussianRange
open Finset Polynomial
noncomputable section

/-- At most two distinct positive temperature levels, without any restriction
on the number of FIR channels at either level. -/
def BathFamily.twoTemperature (b : BathFamily) : Prop :=
  ∃ a h : ℝ, 0<a ∧ a≤h ∧ ∀ v, b.temp v=a ∨ b.temp v=h

theorem two_temperature_endpoints (b : BathFamily) (r : ℕ) (m a h : ℝ)
    (hb : b.admissible r m) (hah : a≤h)
    (ht : ∀ v, b.temp v=a ∨ b.temp v=h) :
    a≤m ∧ m+4≤h := by
  have ha (z : ℂ) (hz : ‖z‖=1) : a≤dispersion (m+2) z := by
    have hs := hb.2.1 z hz
    have hd := hb.2.2 z hz
    have hle : (∑ v, a*weight r (b.coeff v) z)≤
        ∑ v, b.temp v*weight r (b.coeff v) z := by
      apply sum_le_sum
      intro v hv
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      rcases ht v with hv'|hv'
      · rw [hv']
      · rwa [hv']
    rw [← mul_sum,hs,mul_one,hd] at hle
    exact hle
  have hh (z : ℂ) (hz : ‖z‖=1) : dispersion (m+2) z≤h := by
    have hs := hb.2.1 z hz
    have hd := hb.2.2 z hz
    have hle : (∑ v, b.temp v*weight r (b.coeff v) z)≤
        ∑ v, h*weight r (b.coeff v) z := by
      apply sum_le_sum
      intro v hv
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      rcases ht v with hv'|hv'
      · rwa [hv']
      · rw [hv']
    rw [← mul_sum,hs,mul_one,hd] at hle
    exact hle
  constructor
  · simpa [dispersion] using ha 1 (by norm_num)
  · have he := hh (-1) (by norm_num)
    simp [dispersion] at he
    linarith

theorem two_temperature_sigma (b : BathFamily) (r : ℕ) (m a h : ℝ)
    (ha : 0<a) (hh : 0<h) (hb : b.admissible r m)
    (ht : ∀ v, b.temp v=a ∨ b.temp v=h) (z : ℂ) (hz : ‖z‖=1) :
    sigma r b.coeff b.temp (m+2) z =
      (dispersion (m+2) z/a-1)*(1-dispersion (m+2) z/h) := by
  let d := dispersion (m+2) z
  let g := ∑ v,weight r (b.coeff v) z/b.temp v
  have hg : a*h*g=a+h-d := by
    dsimp [g,d]
    rw [mul_sum]
    calc
      _ = ∑ v,(a+h-b.temp v)*weight r (b.coeff v) z := by
        apply sum_congr rfl
        intro v hv
        rcases ht v with hv'|hv'
        · rw [hv']
          field_simp [ha.ne']
          <;> ring
        · rw [hv']
          field_simp [hh.ne']
          <;> ring
      _ = _ := by
        simp only [sub_mul,sum_sub_distrib,← mul_sum,hb.2.1 z hz,mul_one,hb.2.2 z hz]
  have he : g=(a+h-d)/(a*h) := by
    apply (eq_div_iff (mul_ne_zero ha.ne' hh.ne')).2
    linarith only [hg,show g*(a*h)=a*h*g by ring]
  change d*g-1=(d/a-1)*(1-d/h)
  rw [he]
  field_simp [ha.ne',hh.ne']
  <;> ring

theorem two_temperature_pointwise (b : BathFamily) (r : ℕ) (hr : 0<r)
    (m : ℝ) (hm : 0<m) (hb : b.admissible r m)
    (ht : b.twoTemperature) (z : ℂ) (hz : ‖z‖=1) :
    sigma r (nearestBath m).coeff (nearestBath m).temp (m+2) z ≤
      sigma r b.coeff b.temp (m+2) z := by
  obtain ⟨a,h,ha,hah,ht⟩ := ht
  have hh := ha.trans_le hah
  obtain ⟨ham,hmh⟩ := two_temperature_endpoints b r m a h hb hah ht
  obtain ⟨hlo,hhi⟩ := unit_re_mem z hz
  let d := dispersion (m+2) z
  have hdm : m≤d := by dsimp [d,dispersion]; linarith
  have hdm4 : d≤m+4 := by dsimp [d,dispersion]; linarith
  have hd0 := hm.le.trans hdm
  have h₁ : d/m-1≤d/a-1 :=
    sub_le_sub_right (div_le_div_of_nonneg_left hd0 ha ham) _
  have h₂ : 1-d/(m+4)≤1-d/h :=
    sub_le_sub_left (div_le_div_of_nonneg_left hd0 (by linarith) hmh) _
  have h₁0 : 0≤d/m-1 := sub_nonneg.mpr ((le_div_iff₀ hm).2 (by simpa using hdm))
  have h₂0 : 0≤1-d/(m+4) := sub_nonneg.mpr ((div_le_iff₀ (by linarith : 0<m+4)).2 (by simpa using hdm4))
  have hprod := mul_le_mul h₁ h₂ h₂0 (h₁0.trans h₁)
  have hnear : sigma r (nearestBath m).coeff (nearestBath m).temp (m+2) z=
      (d/m-1)*(1-d/(m+4)) := by
    apply two_temperature_sigma (nearestBath m) r m m (m+4) hm (by linarith)
      (nearest_admissible r hr m hm) _ z hz
    intro v
    cases v <;> simp [nearestBath]
  rw [hnear,two_temperature_sigma b r m a h ha hh hb ht z hz]
  exact hprod

theorem two_temperature_cost_lower (b : BathFamily) (r : ℕ) (hr : 0<r)
    (m : ℝ) (hm : 0<m) (hb : b.admissible r m)
    (ht : b.twoTemperature) : 2/(m*(m+4))≤b.cost r m := by
  rw [← nearest_cost_exact r hr m hm]
  exact BathFamily.cost_mono_unit b (nearestBath m) r m
    (two_temperature_pointwise b r hr m hm hb ht)

def twoTemperatureCosts (r : ℕ) (m : ℝ) : Set ℝ :=
  {x | ∃ b : BathFamily, b.admissible r m ∧ b.twoTemperature ∧ b.cost r m=x}

theorem two_temperature_minimum (r : ℕ) (hr : 0<r) (m : ℝ) (hm : 0<m) :
    IsLeast (twoTemperatureCosts r m) (2/(m*(m+4))) := by
  constructor
  · refine ⟨nearestBath m,nearest_admissible r hr m hm,?_,nearest_cost_exact r hr m hm⟩
    refine ⟨m,m+4,hm,by linarith,?_⟩
    intro v
    cases v <;> simp [nearestBath]
  · rintro x ⟨b,hb,ht,rfl⟩
    exact two_temperature_cost_lower b r hr m hm hb ht

theorem two_temperature_scaled_floor (b : BathFamily) (r : ℕ) (hr : 0<r)
    (m : ℝ) (hm : 0<m) (hb : b.admissible r m) (ht : b.twoTemperature) :
    2/(m+4)≤m*b.cost r m := by
  have h := mul_le_mul_of_nonneg_left (two_temperature_cost_lower b r hr m hm hb ht) hm.le
  convert h using 1
  field_simp [hm.ne',show m+4≠0 by positivity]

theorem critical_const_le_fifth (r : ℕ) (hr : 2≤r) : criticalConst r≤1/5 := by
  rw [criticalConst_formula]
  have h1 : (2:ℝ)≤r := by exact_mod_cast hr
  have h2 : 0<((r:ℝ)+1)*(r+2)*(r+3) := by positivity
  apply (div_le_div_iff₀ h2 (by norm_num : (0:ℝ)<5)).2
  have h3 : (3:ℝ)*(4:ℝ)≤((r:ℝ)+1)*(r+2) :=
    mul_le_mul (by linarith) (by linarith) (by norm_num) (by positivity)
  have h4 : (3:ℝ)*4*5≤((r:ℝ)+1)*(r+2)*(r+3) :=
    mul_le_mul h3 (by linarith) (by norm_num) (by positivity)
  linarith

theorem critical_three_temperature_advantage (r : ℕ) (hr : 2≤r) (m : ℝ) (hm : 0<m)
    (hsmall : m≤1/(40*((r:ℝ)+1)^2)) :
    ∃ b : BathFamily, b.admissible r m ∧ Fintype.card b.ι=3 ∧
      ¬ b.twoTemperature ∧
      (∀ a : BathFamily, a.admissible r m → a.twoTemperature → b.cost r m<a.cost r m) := by
  obtain ⟨b,hb,hcard,hu⟩ := critical_realization_upper r (by omega) m hm
  have hA : 4/criticalA r=4*((r:ℝ)+1)^2 := by
    unfold criticalA
    rw [div_div_eq_mul_div]
    norm_num
  rw [hA] at hu
  have hmU := mul_le_mul_of_nonneg_left hu hm.le
  have he : m*(criticalConst r/m+4*((r:ℝ)+1)^2)=criticalConst r+4*m*((r:ℝ)+1)^2 := by
    field_simp [hm.ne']
    <;> ring
  rw [he] at hmU
  have hs := (le_div_iff₀ (by positivity : 0<40*((r:ℝ)+1)^2)).1 hsmall
  have hc := critical_const_le_fifth r hr
  have hscaled : m*b.cost r m≤3/10 := by nlinarith only [hmU,hs,hc]
  have hr0 : (2:ℝ)≤r := by exact_mod_cast hr
  have h1 : 1≤((r:ℝ)+1)^2 := by nlinarith [sq_nonneg (r:ℝ)]
  have hm1 : m≤1 := by
    have hh := mul_le_mul_of_nonneg_left h1 hm.le
    nlinarith only [hs,hh]
  have hfloor : (3:ℝ)/10<2/(m+4) := by
    apply (lt_div_iff₀ (by linarith : 0<m+4)).2
    linarith
  have hlt (a : BathFamily) (ha : a.admissible r m) (ht : a.twoTemperature) :
      b.cost r m<a.cost r m := by
    have hh := two_temperature_scaled_floor a r (by omega) m hm ha ht
    by_contra! hnot
    have hbad := mul_le_mul_of_nonneg_left hnot hm.le
    exact (not_lt_of_ge hbad) (hscaled.trans_lt (hfloor.trans_le hh))
  exact ⟨b,hb,hcard,fun ht => (lt_irrefl _ (hlt b hb ht)),hlt⟩

end
end GaussianRange
#check GaussianRange.two_temperature_minimum
#print axioms GaussianRange.two_temperature_minimum
#print axioms GaussianRange.two_temperature_pointwise
#check GaussianRange.critical_three_temperature_advantage
#print axioms GaussianRange.critical_three_temperature_advantage
