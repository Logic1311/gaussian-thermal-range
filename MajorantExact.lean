import MajorantBridge
import RateEquivalence
import RelaxationGap

namespace GaussianRange
open Finset Polynomial
noncomputable section

theorem even_majorant_bound (r : ℕ) (t : ℝ) (ht : 1<t) (g : ℝ[X])
    (hg : evenMajorant r (t+t⁻¹) g) :
    algebraicRelaxedValue (r+1) t≤majorantCost (t+t⁻¹) g := by
  apply even_majorant_lower r t ht g hg
  apply real_factor_weight _ _ (resOrd_degree r _ _ hg.1)
  intro z hz
  rw [resOrd_eval]
  exact sub_nonneg.mpr (hg.2 z hz)

theorem factor_to_even_majorant (r : ℕ) (t : ℝ) (ht : 1<t) (a : ℕ → ℝ)
    (ha : (amp (r+1) a).eval (t:ℂ)*(rev (r+1) a).eval (t:ℂ)= -(t:ℂ)^(r+1)) :
    ∃ g : ℝ[X], evenMajorant r (t+t⁻¹) g ∧
      majorantCost (t+t⁻¹) g=avg (weight (r+1) a) := by
  let p := r+1
  let q := evenRatePoly p (lagCoeff p a)
  have hq : q.natDegree≤p := evenRatePoly_degree _ _
  have he (z : ℂ) (hz : ‖z‖=1) : weight p a z=q.eval z.re := by
    rw [physical_weight_trig p a z hz]
    unfold q trigRate
    rw [evenRatePoly_eval p _ z hz]
    simp
  have hroot := (factor_root_iff p q hq a he t (by linarith)).1 ha
  have hd : X-C ((t+t⁻¹)/2) ∣ q+1 := by
    apply dvd_iff_isRoot.mpr
    change (q+1).eval ((t+t⁻¹)/2)=0
    simp [hroot]
  obtain ⟨s,hs⟩ := hd
  have hs0 : s≠0 := by
    intro h
    rw [h,mul_zero] at hs
    have hh := congrArg (fun f : ℝ[X] => f.eval 1) hs
    change (q+1).eval 1=(0:ℝ[X]).eval 1 at hh
    simp only [eval_add,eval_one,eval_zero] at hh
    have hh' := he 1 (by norm_num)
    simp only [Complex.one_re] at hh'
    unfold weight at hh'
    nlinarith [sq_nonneg ‖(amp p a).eval 1‖]
  have hqs : (q+1).natDegree≤p := by
    exact (natDegree_add_le _ _).trans (max_le hq (by simp))
  have hsdeg : s.natDegree≤r := by
    rw [hs,natDegree_mul (X_sub_C_ne_zero _) hs0,natDegree_X_sub_C] at hqs
    dsimp [p] at hqs
    omega
  let g := C (-1/2:ℝ)*s
  have hgd : g.natDegree≤r := (natDegree_C_mul_le _ _).trans hsdeg
  have heval (x : ℝ) : (t+t⁻¹-2*x)*g.eval x-1=q.eval x := by
    have h := congrArg (fun f : ℝ[X] => f.eval x) hs
    change (q+1).eval x=((X-C ((t+t⁻¹)/2))*s).eval x at h
    simp only [eval_add,eval_one,eval_mul,eval_sub,eval_X,eval_C] at h
    simp only [g,eval_mul,eval_C]
    linarith
  refine ⟨g,⟨hgd,?_⟩,?_⟩
  · intro z hz
    have hh := he z hz
    unfold weight at hh
    have h := heval z.re
    unfold dispersion
    nlinarith [sq_nonneg ‖(amp p a).eval z‖]
  · unfold majorantCost avg
    apply Real.circleAverage_congr_sphere
    intro z hz
    change (t+t⁻¹-2*z.re)*g.eval z.re-1=weight p a z
    rw [heval,he z (norm_unit_of_mem z hz)]

def trigMajorant (r : ℕ) (c : ℝ) (a b : ℕ → ℝ) : Prop :=
    ∀ z : ℂ, ‖z‖=1 → 1≤dispersion c z*trigRate r a b z

def trigMajorantCost (r : ℕ) (c : ℝ) (a b : ℕ → ℝ) : ℝ :=
    avg (fun z => dispersion c z*trigRate r a b z-1)

def majorantCosts (r : ℕ) (m : ℝ) : Set ℝ :=
    {x | ∃ a b : ℕ → ℝ, trigMajorant r (m+2) a b ∧ trigMajorantCost r (m+2) a b=x}

def relaxedEntropy (r : ℕ) (m : ℝ) : ℝ := sInf (majorantCosts r m)

theorem trig_majorant_evenize (r : ℕ) (c : ℝ) (a b : ℕ → ℝ)
    (h : trigMajorant r c a b) :
    evenMajorant r c (evenRatePoly r a) ∧
      majorantCost c (evenRatePoly r a)=trigMajorantCost r c a b := by
  have hd (z : ℂ) : dispersion c (star z)=dispersion c z := by simp [dispersion]
  constructor
  · refine ⟨evenRatePoly_degree r a,?_⟩
    intro z hz
    have hs : ‖star z‖=1 := by simpa using hz
    have h₁ := h z hz
    have h₂ := h (star z) hs
    rw [hd] at h₂
    rw [← trigRate_sym r a b z hz]
    linarith
  · unfold majorantCost trigMajorantCost
    let f : ℂ → ℝ := fun z => dispersion c z*trigRate r a b z-1
    have hf : Continuous f := ((cont_dispersion c).mul (trigRate_cont r a b)).sub continuous_const
    rw [← avg_sym f hf]
    unfold avg
    apply Real.circleAverage_congr_sphere
    intro z hz
    dsimp only
    rw [← trigRate_sym r a b z (norm_unit_of_mem z hz)]
    dsimp [f]
    have hds : dispersion c ((starRingEnd ℂ) z)=dispersion c z := hd z
    rw [hds]
    ring

theorem even_majorant_to_trig (r : ℕ) (c : ℝ) (g : ℝ[X]) (hg : evenMajorant r c g) :
    ∃ a : ℕ → ℝ, trigMajorant r c a (fun _ => 0) ∧
      trigMajorantCost r c a (fun _ => 0)=majorantCost c g := by
  obtain ⟨a,ha⟩ := poly_cos_repr r g hg.1
  have he (z : ℂ) (hz : ‖z‖=1) : trigRate r a (fun _ => 0) z=g.eval z.re := by
    rw [← ha,evenRatePoly_eval r a z hz]
    simp [trigRate]
  refine ⟨a,?_ ,?_⟩
  · intro z hz
    rw [he z hz]
    exact hg.2 z hz
  · unfold trigMajorantCost majorantCost avg
    apply Real.circleAverage_congr_sphere
    intro z hz
    dsimp only
    rw [he z (norm_unit_of_mem z hz)]

theorem majorant_exact_minimum (r : ℕ) (m t : ℝ) (ht : 1<t) (hc : m+2=t+t⁻¹) :
    IsLeast (majorantCosts r m) (algebraicRelaxedValue (r+1) t) := by
  obtain ⟨a,ha,hv,_⟩ := factor_relaxation_minimum (r+1) (by omega) t ht
  obtain ⟨g,hg,hgc⟩ := factor_to_even_majorant r t ht a ha
  obtain ⟨b,hb,hbc⟩ := even_majorant_to_trig r _ g hg
  refine ⟨?_,?_⟩
  · exact ⟨b,fun _=>0,hc.symm ▸ hb,by rw [hc,hbc,hgc,hv]⟩
  · rintro x ⟨a',b',h,he⟩
    rw [hc] at h he
    obtain ⟨hg',hcost⟩ := trig_majorant_evenize r _ a' b' h
    rw [← hcost] at he
    exact he ▸ even_majorant_bound r t ht _ hg'

theorem relaxedEntropy_eq (r : ℕ) (m t : ℝ) (ht : 1<t) (hc : m+2=t+t⁻¹) :
    relaxedEntropy r m=algebraicRelaxedValue (r+1) t := by
  exact (majorant_exact_minimum r m t ht hc).csInf_eq

theorem dispersion_root_exists (m : ℝ) (hm : 0<m) :
    ∃ t : ℝ, 1<t ∧ m+2=t+t⁻¹ := by
  let d := Real.sqrt (m*(m+4))
  let t := (m+2+d)/2
  have hd : 0≤d := Real.sqrt_nonneg _
  have hdd : d^2=m*(m+4) := Real.sq_sqrt (by positivity)
  have ht : 1<t := by dsimp [t]; linarith
  refine ⟨t,ht,?_⟩
  have ht0 : t≠0 := by linarith
  field_simp
  dsimp [t]
  nlinarith

theorem actual_gap_theta (m : ℝ) (hm : 0<m) :
    ∃ t : ℝ, 1<t ∧ m+2=t+t⁻¹ ∧
    ∃ A B : ℝ, 0<A ∧ 0<B ∧ ∃ R : ℕ, 0<R ∧
      ∀ r : ℕ, R≤r →
        A*t^(r+1)/(r:ℝ)^2 ≤ optimalEntropy r m/relaxedEntropy r m ∧
        optimalEntropy r m/relaxedEntropy r m ≤ B*t^(r+1)/(r:ℝ)^2 := by
  obtain ⟨t,ht,hc⟩ := dispersion_root_exists m hm
  obtain ⟨A,B,hA,hB,R,hR,h⟩ := factor_gap_theta m t hm ht
  refine ⟨t,ht,hc,A,B,hA,hB,R,hR,?_⟩
  intro r hr
  rw [relaxedEntropy_eq r m t ht hc]
  exact h r hr

theorem physical_cost_subset_majorant (r : ℕ) (m : ℝ) (hm : 0<m) :
    admissibleCosts r m ⊆ majorantCosts r m := by
  rintro x ⟨b,hb,he⟩
  let a : ℕ → ℝ := fun j => ∑ v, lagCoeff r (b.coeff v) j / b.temp v
  have hw (z : ℂ) (hz : ‖z‖=1) :
      trigRate r a (fun _=>0) z=∑ v, weight r (b.coeff v) z/b.temp v := by
    simp_rw [physical_weight_trig r _ z hz]
    unfold trigRate a
    simp only [zero_mul,add_zero]
    simp_rw [Finset.sum_div,Finset.sum_mul,div_mul_eq_mul_div]
    exact Finset.sum_comm
  refine ⟨a,fun _=>0,?_,?_⟩
  · intro z hz
    rw [hw z hz]
    have hs := b.sigma_identity r m hm hb z hz
    have hd : 0<dispersion (m+2) z := by
      have h := (unit_re_mem z hz).2
      unfold dispersion
      linarith
    have hnon : 0≤∑ v, weight r (b.coeff v) z*(b.temp v-dispersion (m+2) z)^2 /
        (b.temp v*dispersion (m+2) z) := by
      apply Finset.sum_nonneg
      intro v hv
      exact div_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (mul_pos (hb.1 v) hd).le
    unfold sigma at hs
    linarith
  · rw [← he]
    unfold trigMajorantCost BathFamily.cost avg
    apply Real.circleAverage_congr_sphere
    intro z hz
    dsimp only
    rw [hw z (norm_unit_of_mem z hz)]
    rfl

end
end GaussianRange
#print axioms GaussianRange.majorant_exact_minimum
#print axioms GaussianRange.relaxedEntropy_eq
#print axioms GaussianRange.actual_gap_theta
#print axioms GaussianRange.physical_cost_subset_majorant
