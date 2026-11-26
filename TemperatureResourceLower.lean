import ThreeTemperature
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

namespace GaussianRange
open Finset MeasureTheory Set
open scoped Interval
noncomputable section

/-- An upper bound on the number of distinct temperature values, not on
the number of channels. Repeated or unused palette entries are allowed. -/
def BathFamily.temperaturePalette (b : BathFamily) (K : ℕ) : Prop :=
  ∃ τ : Fin K → ℝ, ∀ v, ∃ i, b.temp v = τ i

def temperatureTent (δ t x : ℝ) : ℝ := max 0 (2 - |x-t|/δ)

def temperatureAvoidance {K : ℕ} (δ : ℝ) (τ : Fin K → ℝ) (x : ℝ) : ℝ :=
  1 - ∑ i, temperatureTent δ (τ i) x

theorem temperatureTent_cont (δ t : ℝ) : Continuous (temperatureTent δ t) := by
  unfold temperatureTent
  fun_prop

theorem temperatureAvoidance_cont {K : ℕ} (δ : ℝ) (τ : Fin K → ℝ) :
    Continuous (temperatureAvoidance δ τ) := by
  unfold temperatureAvoidance
  exact continuous_const.sub (continuous_finset_sum _ (fun i _ => temperatureTent_cont δ (τ i)))

theorem temperature_far_penalty (t d M δ : ℝ) (ht : 0<t) (hd : 0<d)
    (hM : d≤M) (hδ : 0<δ) (hδM : δ≤M) (hfar : δ≤|t-d|) :
    δ^2/(2*M^2) ≤ (t-d)^2/(t*d) := by
  have hM0 := hd.trans_le hM
  have hs : δ^2≤(t-d)^2 := by
    have h := pow_le_pow_left₀ hδ.le hfar 2
    simpa [sq_abs] using h
  have hden : 0<2*M^2 := by positivity
  by_cases hsmall : t≤2*M
  · apply (div_le_div_iff₀ hden (mul_pos ht hd)).2
    have htd : t*d≤2*M^2 := by
      calc
        _ ≤ (2*M)*d := mul_le_mul_of_nonneg_right hsmall hd.le
        _ ≤ (2*M)*M := mul_le_mul_of_nonneg_left hM (by positivity)
        _ = _ := by ring
    calc
      _ ≤ δ^2*(2*M^2) := mul_le_mul_of_nonneg_left htd (sq_nonneg _)
      _ ≤ (t-d)^2*(2*M^2) := mul_le_mul_of_nonneg_right hs hden.le
  · have hlarge : 2*d≤t := by linarith
    have hhalf : (1:ℝ)/2≤(t-d)^2/(t*d) := by
      apply (div_le_div_iff₀ (by norm_num : (0:ℝ)<2) (mul_pos ht hd)).2
      have h := mul_nonneg (sub_nonneg.mpr hlarge) (show 0≤2*t-d by linarith)
      nlinarith only [h]
    have hC : δ^2/(2*M^2)≤(1:ℝ)/2 := by
      apply (div_le_div_iff₀ hden (by norm_num : (0:ℝ)<2)).2
      nlinarith [pow_le_pow_left₀ hδ.le hδM 2]
    exact hC.trans hhalf

theorem resource_sigma_nonneg (b : BathFamily) (r : ℕ) (m : ℝ) (hm : 0<m)
    (hb : b.admissible r m) (z : ℂ) (hz : ‖z‖=1) :
    0≤sigma r b.coeff b.temp (m+2) z := by
  obtain ⟨hlo,hhi⟩ := unit_re_mem z hz
  have hd : 0<dispersion (m+2) z := by unfold dispersion; linarith
  rw [BathFamily.sigma_identity b r m hm hb z hz]
  exact sum_nonneg (fun v _ => div_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    (mul_pos (hb.1 v) hd).le)

theorem temperature_avoidance_pointwise (b : BathFamily) (r K : ℕ)
    (m δ : ℝ) (hm : 0<m) (hδ : 0<δ) (hδM : δ≤m+4)
    (hb : b.admissible r m) (τ : Fin K → ℝ) (ht : ∀ v, ∃ i, b.temp v=τ i)
    (z : ℂ) (hz : ‖z‖=1) :
    δ^2/(2*(m+4)^2)*temperatureAvoidance δ τ (dispersion (m+2) z)
      ≤sigma r b.coeff b.temp (m+2) z := by
  let d := dispersion (m+2) z
  let C := δ^2/(2*(m+4)^2)
  have hC : 0≤C := by dsimp [C]; positivity
  obtain ⟨hlo,hhi⟩ := unit_re_mem z hz
  have hd : 0<d := by dsimp [d,dispersion]; linarith
  have hdM : d≤m+4 := by dsimp [d,dispersion]; linarith
  have hnon := resource_sigma_nonneg b r m hm hb z hz
  by_cases hnear : ∃ i, |d-τ i|≤δ
  · obtain ⟨i,hi⟩ := hnear
    have htent : 1≤temperatureTent δ (τ i) d := by
      unfold temperatureTent
      have h := (div_le_iff₀ hδ).2 (show |d-τ i|≤1*δ by simpa using hi)
      exact (show 1≤2-|d-τ i|/δ by linarith).trans (le_max_right _ _)
    have hs : temperatureTent δ (τ i) d≤∑ j,temperatureTent δ (τ j) d :=
      single_le_sum (fun j _ => show 0≤temperatureTent δ (τ j) d from le_max_left _ _) (mem_univ i)
    have hF : temperatureAvoidance δ τ d≤0 := by unfold temperatureAvoidance; linarith
    change C*temperatureAvoidance δ τ d≤_
    exact (mul_nonpos_of_nonneg_of_nonpos hC hF).trans hnon
  · have hfar (v : b.ι) : δ≤|b.temp v-d| := by
      obtain ⟨i,hi⟩ := ht v
      rw [hi,abs_sub_comm]
      exact le_of_lt (lt_of_not_ge (fun h => hnear ⟨i,h⟩))
    have hsum : C≤sigma r b.coeff b.temp (m+2) z := by
      rw [BathFamily.sigma_identity b r m hm hb z hz]
      calc
        C = ∑ v, C*weight r (b.coeff v) z := by rw [← mul_sum,hb.2.1 z hz,mul_one]
        _ ≤ _ := by
          apply sum_le_sum
          intro v hv
          have hp := temperature_far_penalty (b.temp v) d (m+4) δ (hb.1 v) hd hdM hδ hδM (hfar v)
          have hw := mul_le_mul_of_nonneg_right hp (sq_nonneg ‖(amp r (b.coeff v)).eval z‖)
          change C*weight r (b.coeff v) z≤_
          simpa only [C,d,weight,mul_div_assoc,mul_comm,mul_left_comm,mul_assoc] using hw
    have hF : temperatureAvoidance δ τ d≤1 := by
      have hs : 0≤∑ i, temperatureTent δ (τ i) d :=
        sum_nonneg (fun i _ => show 0≤temperatureTent δ (τ i) d from le_max_left _ _)
      unfold temperatureAvoidance
      linarith
    change C*temperatureAvoidance δ τ d≤_
    exact (show C*temperatureAvoidance δ τ d≤C from by
      simpa using mul_le_mul_of_nonneg_left hF hC).trans hsum

theorem temperature_tent_integral (δ t a b : ℝ) (hδ : 0<δ) (hab : a≤b) :
    (∫ x in a..b, temperatureTent δ t x)≤8*δ := by
  let S : Set ℝ := Icc (t-2*δ) (t+2*δ)
  let g : ℝ → ℝ := S.indicator (fun _ => (2:ℝ))
  have hmeas : MeasurableSet S := measurableSet_Icc
  have hInt : IntervalIntegrable g volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    have hi : IntegrableOn (fun _ : ℝ => (2:ℝ)) (Ioc a b) volume :=
      integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
    exact hi.indicator hmeas
  have hpoint (x : ℝ) (hx : x∈Icc a b) : temperatureTent δ t x≤g x := by
    by_cases hs : x∈S
    · rw [show g x=2 by simp [g,hs] ]
      unfold temperatureTent
      exact max_le (by norm_num) (by linarith [div_nonneg (abs_nonneg (x-t)) hδ.le])
    · rw [show g x=0 by simp [g,hs] ]
      unfold S at hs
      have hfar : 2*δ≤|x-t| := by
        by_contra! hn
        exact hs ⟨by linarith [neg_abs_le (x-t)],by linarith [le_abs_self (x-t)]⟩
      unfold temperatureTent
      apply max_le le_rfl
      have h := (le_div_iff₀ hδ).2 hfar
      linarith
  have hmono := intervalIntegral.integral_mono_on hab ((temperatureTent_cont δ t).intervalIntegrable a b) hInt hpoint
  have hg : (∫ x in a..b, g x)≤8*δ := by
    rw [intervalIntegral.integral_of_le hab]
    dsimp [g]
    rw [setIntegral_indicator hmeas,setIntegral_const]
    have hm : volume.real (Ioc a b ∩ S)≤volume.real S :=
      measureReal_mono inter_subset_right (by unfold S; rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
    have hS : volume.real S=4*δ := by
      unfold S
      rw [measureReal_def,Real.volume_Icc,ENNReal.toReal_ofReal]
      · ring
      · linarith
    rw [hS] at hm
    simp only [smul_eq_mul]
    linarith
  exact hmono.trans hg

theorem temperature_avoidance_integral (K : ℕ) (hK : 0<K) (m : ℝ) (τ : Fin K → ℝ) :
    2≤∫ x in m..m+4, temperatureAvoidance (1/(4*(K:ℝ))) τ x := by
  let δ : ℝ := 1/(4*(K:ℝ))
  have hK0 : 0<(K:ℝ) := by exact_mod_cast hK
  have hδ : 0<δ := by dsimp [δ]; positivity
  have hc : Continuous (fun x : ℝ => ∑ i, temperatureTent δ (τ i) x) :=
    continuous_finset_sum _ (fun i _ => temperatureTent_cont δ (τ i))
  have hs : (∑ i : Fin K, ∫ x in m..m+4, temperatureTent δ (τ i) x)≤2 := by
    calc
      _ ≤ ∑ i : Fin K, 8*δ := sum_le_sum (fun i _ => temperature_tent_integral δ (τ i) m (m+4) hδ (by linarith))
      _ = 2 := by
        simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
        dsimp [δ]
        field_simp
        <;> ring
  change 2≤∫ x in m..m+4, temperatureAvoidance δ τ x
  unfold temperatureAvoidance
  rw [intervalIntegral.integral_sub (continuous_const.intervalIntegrable m (m+4)) (hc.intervalIntegrable m (m+4)),
    intervalIntegral.integral_finset_sum (fun i _ => (temperatureTent_cont δ (τ i)).intervalIntegrable m (m+4)),
    intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  linarith

theorem angle_dispersion_eq (m θ : ℝ) :
    dispersion (m+2) (circleMap 0 1 θ)=m+2-2*Real.cos θ := by
  simp [dispersion,circleMap,Complex.exp_re,Complex.mul_re,Complex.mul_im]

theorem angle_im_eq (θ : ℝ) : (circleMap 0 1 θ).im=Real.sin θ := by
  simp [circleMap,Complex.exp_im,Complex.mul_re,Complex.mul_im]

theorem angle_dispersion_deriv (m θ : ℝ) :
    HasDerivAt (fun x => dispersion (m+2) (circleMap 0 1 x)) (2*Real.sin θ) θ := by
  have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt θ (hasDerivAt_circleMap 0 1 θ)
  have hr : HasDerivAt (fun x => (circleMap 0 1 x).re) (-(circleMap 0 1 θ).im) θ := by
    simpa [Function.comp_def,Complex.mul_re] using h
  have h' := (hasDerivAt_const θ (m+2)).sub (hr.const_mul 2)
  convert h' using 1
  rw [angle_im_eq]
  ring

/-- Positive resource floor even with arbitrarily many channels and exterior
temperature levels. No Fourier-degree assumption is used in this step beyond
the continuity of the admitted physical model. -/
theorem palette_cost_lower (b : BathFamily) (r K : ℕ) (hK : 0<K)
    (m : ℝ) (hm : 0<m) (hb : b.admissible r m) (hpal : b.temperaturePalette K) :
    1/(64*Real.pi*(m+4)^2*(K:ℝ)^2)≤b.cost r m := by
  obtain ⟨τ,ht⟩ := hpal
  let δ : ℝ := 1/(4*(K:ℝ))
  let C : ℝ := δ^2/(2*(m+4)^2)
  let D : ℝ → ℝ := fun θ => dispersion (m+2) (circleMap 0 1 θ)
  let f : ℝ → ℝ := fun θ => sigma r b.coeff b.temp (m+2) (circleMap 0 1 θ)
  let G : ℝ → ℝ := temperatureAvoidance δ τ
  have hK0 : 0<(K:ℝ) := by exact_mod_cast hK
  have hK1 : 1≤(K:ℝ) := by exact_mod_cast hK
  have hδ : 0<δ := by dsimp [δ]; positivity
  have hδM : δ≤m+4 := by
    dsimp [δ]
    apply (div_le_iff₀ (by positivity : 0<4*(K:ℝ))).2
    nlinarith [mul_nonneg hm.le (sub_nonneg.mpr hK1)]
  have hC : 0<C := by dsimp [C]; positivity
  have hG : Continuous G := temperatureAvoidance_cont δ τ
  have hD : Continuous D := (cont_dispersion _).comp (continuous_circleMap 0 1)
  have hf : Continuous f := (cont_sigma r b.coeff b.temp (m+2)).comp (continuous_circleMap 0 1)
  have hunit (θ : ℝ) : ‖circleMap 0 1 θ‖=1 := by rw [norm_circleMap_zero]; norm_num
  have hn (θ : ℝ) : 0≤f θ := resource_sigma_nonneg b r m hm hb _ (hunit θ)
  have hp (θ : ℝ) : C * G (D θ)≤f θ :=
    temperature_avoidance_pointwise b r K m δ hm hδ hδM hb τ ht _ (hunit θ)
  have hchange : (∫ θ in 0..Real.pi, G (D θ)*(2*Real.sin θ)) =
      ∫ x in m..m+4, G x := by
    have hh := intervalIntegral.integral_comp_mul_deriv (a:=0) (b:=Real.pi) (f:=D)
      (f':=fun θ => 2*Real.sin θ) (g:=G)
      (fun θ _ => angle_dispersion_deriv m θ)
      ((continuous_const.mul Real.continuous_sin).continuousOn) hG
    have h0 : D 0=m := by dsimp [D]; rw [angle_dispersion_eq]; simp
    have hπ : D Real.pi=m+4 := by dsimp [D]; rw [angle_dispersion_eq]; simp; ring
    rw [h0,hπ] at hh
    exact hh
  have hweighted : (∫ θ in 0..Real.pi, (C/2)*(G (D θ)*(2*Real.sin θ)))≤
      ∫ θ in 0..Real.pi, f θ := by
    have hcw : Continuous (fun θ : ℝ => (C/2)*(G (D θ)*(2*Real.sin θ))) :=
      continuous_const.mul ((hG.comp hD).mul (continuous_const.mul Real.continuous_sin))
    apply intervalIntegral.integral_mono_on Real.pi_pos.le
      (hcw.intervalIntegrable _ _)
      (hf.intervalIntegrable _ _)
    intro θ hθ
    have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 hθ.2
    have hs1 := Real.sin_le_one θ
    have he : C/2*(G (D θ)*(2*Real.sin θ))=(C*G (D θ))*Real.sin θ := by ring
    rw [he]
    by_cases hsign : 0≤C*G (D θ)
    · calc
        _ ≤ (C*G (D θ))*1 := mul_le_mul_of_nonneg_left hs1 hsign
        _ ≤ _ := by simpa using hp θ
    · exact (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hsign) hs0).trans (hn θ)
  rw [intervalIntegral.integral_const_mul,hchange] at hweighted
  have hGint : 2≤∫ x in m..m+4, G x := temperature_avoidance_integral K hK m τ
  have hhalf : C≤∫ θ in 0..Real.pi, f θ := by
    have hh := mul_le_mul_of_nonneg_left hGint (show 0≤C/2 by positivity)
    linarith
  have hrest : 0≤∫ θ in Real.pi..2*Real.pi, f θ :=
    intervalIntegral.integral_nonneg (by linarith [Real.pi_pos]) (fun θ _ => hn θ)
  have hadd : (∫ θ in 0..Real.pi, f θ) + (∫ θ in Real.pi..2*Real.pi, f θ) =
      ∫ θ in 0..2*Real.pi, f θ :=
    intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable 0 Real.pi)
      (hf.intervalIntegrable Real.pi (2*Real.pi))
  have hfull : C≤∫ θ in 0..2*Real.pi, f θ := by
    rw [← hadd]
    exact hhalf.trans (le_add_of_nonneg_right hrest)
  have havg : C/(2*Real.pi)≤b.cost r m := by
    unfold BathFamily.cost avg Real.circleAverage
    change C/(2*Real.pi)≤(2*Real.pi)⁻¹*(∫ θ in 0..2*Real.pi, f θ)
    rw [div_eq_mul_inv,mul_comm C]
    exact mul_le_mul_of_nonneg_left hfull (by positivity)
  have he : C/(2*Real.pi)=1/(64*Real.pi*(m+4)^2*(K:ℝ)^2) := by
    dsimp [C,δ]
    field_simp [Real.pi_pos.ne',hK0.ne',show m+4≠0 by positivity]
    <;> ring
  rw [← he]
  exact havg

end
end GaussianRange
#check GaussianRange.palette_cost_lower
#print axioms GaussianRange.temperature_far_penalty
#print axioms GaussianRange.temperature_avoidance_pointwise
#print axioms GaussianRange.palette_cost_lower
