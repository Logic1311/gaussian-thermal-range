import RealFactorization
import TrigSymmetry
import Compression

namespace GaussianRange
open Finset Polynomial
noncomputable section

theorem amp_of_real_poly (p : ℝ[X]) (r : ℕ) (hp : p.natDegree≤r) :
    amp r p.coeff = p.map (algebraMap ℝ ℂ) := by
  ext j
  rw [amp_coeff,coeff_map]
  split_ifs with hj
  · rfl
  · have hzero : p.coeff j=0 := coeff_eq_zero_of_natDegree_lt (by omega)
    rw [hzero,map_zero]

/-- Real-even nonnegative trigonometric polynomials admit a single real FIR factor.
The ordinary polynomial is in the real part of a unit complex number. -/
theorem real_factor_weight (p : ℝ[X]) (r : ℕ) (hp : p.natDegree≤r)
    (hn : ∀ z : ℂ, ‖z‖=1 → 0≤p.eval z.re) :
    ∃ a : ℕ → ℝ, ∀ z : ℂ, ‖z‖=1 → weight r a z=p.eval z.re := by
  have h : IntervalNonneg p := by
    intro x hx hy
    obtain ⟨z,hz,he⟩ := interval_point_unit x hx hy
    rw [← he]
    exact hn z hz
  obtain ⟨q,hq,he⟩ := realFactor_interval p h
  refine ⟨q.coeff,?_⟩
  intro z hz
  unfold weight
  rw [amp_of_real_poly q r (hq.trans hp)]
  exact (he z hz).symm

theorem trigRate_sym_factor (r : ℕ) (a b : ℕ → ℝ)
    (hn : ∀ z : ℂ, ‖z‖=1 → 0≤trigRate r a b z) :
    ∃ c : ℕ → ℝ, ∀ z : ℂ, ‖z‖=1 → weight r c z=(trigRate r a b z+trigRate r a b (star z))/2 := by
  have h : ∀ z : ℂ, ‖z‖=1 → 0≤(evenRatePoly r a).eval z.re := by
    intro z hz
    rw [← trigRate_sym r a b z hz]
    have hs : ‖star z‖=1 := by simpa using hz
    exact div_nonneg (add_nonneg (hn z hz) (hn _ hs)) (by norm_num)
  obtain ⟨c,hc⟩ := real_factor_weight (evenRatePoly r a) r (evenRatePoly_degree r a) h
  exact ⟨c, fun z hz => (hc z hz).trans (trigRate_sym r a b z hz).symm⟩

structure RateFamily where
  ι : Type
  finite : Fintype ι
  cosine : ι → ℕ → ℝ
  sine : ι → ℕ → ℝ
  temp : ι → ℝ

attribute [instance] RateFamily.finite

def RateFamily.rate (b : RateFamily) (r : ℕ) (v : b.ι) : ℂ → ℝ :=
  trigRate r (b.cosine v) (b.sine v)

def RateFamily.admissible (b : RateFamily) (r : ℕ) (m : ℝ) : Prop :=
  (∀ v, 0<b.temp v) ∧
  (∀ v z, ‖z‖=1 → 0≤b.rate r v z) ∧
  (∀ z : ℂ, ‖z‖=1 → ∑ v, b.rate r v z=1) ∧
  (∀ z : ℂ, ‖z‖=1 → ∑ v, b.temp v*b.rate r v z=dispersion (m+2) z)

def RateFamily.sigma (b : RateFamily) (r : ℕ) (m : ℝ) (z : ℂ) : ℝ :=
  dispersion (m+2) z*(∑ v, b.rate r v z/b.temp v)-1

def RateFamily.cost (b : RateFamily) (r : ℕ) (m : ℝ) : ℝ := avg (b.sigma r m)

theorem RateFamily.cont_sigma (b : RateFamily) (r : ℕ) (m : ℝ) : Continuous (b.sigma r m) := by
  unfold RateFamily.sigma
  have hs : Continuous (fun z : ℂ => ∑ v, b.rate r v z/b.temp v) :=
    continuous_finset_sum _ (fun v _ => (trigRate_cont r (b.cosine v) (b.sine v)).div_const _)
  exact ((cont_dispersion (m+2)).mul hs).sub continuous_const

theorem rateFIR_realization (b : RateFamily) (r : ℕ) (m : ℝ) (hb : b.admissible r m) :
    ∃ b' : BathFamily, b'.admissible r m ∧ b'.cost r m=b.cost r m := by
  have h (v : b.ι) : ∃ c : ℕ → ℝ, ∀ z : ℂ, ‖z‖=1 →
      weight r c z=(b.rate r v z+b.rate r v (star z))/2 :=
    trigRate_sym_factor r (b.cosine v) (b.sine v) (hb.2.1 v)
  choose c hc using h
  let b' : BathFamily := ⟨b.ι,b.finite,c,b.temp⟩
  have hd (z : ℂ) : dispersion (m+2) (star z)=dispersion (m+2) z := by simp [dispersion]
  have hba : b'.admissible r m := by
    refine ⟨hb.1,?_,?_⟩
    · intro z hz
      change (∑ v, weight r (c v) z)=1
      simp_rw [hc _ z hz]
      rw [← Finset.sum_div,Finset.sum_add_distrib]
      have hs : ‖star z‖=1 := by simpa using hz
      rw [hb.2.2.1 z hz,hb.2.2.1 (star z) hs]
      norm_num
    · intro z hz
      change (∑ v, b.temp v*weight r (c v) z)=dispersion (m+2) z
      simp_rw [hc _ z hz,← mul_div_assoc,mul_add]
      rw [← Finset.sum_div,Finset.sum_add_distrib]
      have hs : ‖star z‖=1 := by simpa using hz
      rw [hb.2.2.2 z hz,hb.2.2.2 (star z) hs,hd]
      ring
  refine ⟨b',hba,?_⟩
  unfold BathFamily.cost RateFamily.cost
  calc
    _ = avg (fun z => (b.sigma r m z+b.sigma r m (star z))/2) := by
      unfold avg
      apply Real.circleAverage_congr_sphere
      intro z hz
      have hzu := norm_unit_of_mem z hz
      unfold sigma RateFamily.sigma
      change dispersion (m+2) z*(∑ v,weight r (c v) z/b.temp v)-1=_
      simp_rw [hc _ z hzu]
      have he (v : b.ι) : (b.rate r v z+b.rate r v (star z))/2/b.temp v =
          (b.rate r v z/b.temp v+b.rate r v (star z)/b.temp v)/2 := by ring
      simp_rw [he,← Finset.sum_div,Finset.sum_add_distrib,hd]
      ring
    _ = _ := avg_sym _ (b.cont_sigma r m)

def BathFamily.asRates (b : BathFamily) (r : ℕ) : RateFamily where
  ι := b.ι
  finite := b.finite
  cosine := fun v => lagCoeff r (b.coeff v)
  sine := fun _ _ => 0
  temp := b.temp

theorem bath_asRates_weight (b : BathFamily) (r : ℕ) (v : b.ι) (z : ℂ) (hz : ‖z‖=1) :
    (b.asRates r).rate r v z=weight r (b.coeff v) z :=
  (physical_weight_trig r (b.coeff v) z hz).symm

theorem bath_asRates_admissible (b : BathFamily) (r : ℕ) (m : ℝ) (hb : b.admissible r m) :
    (b.asRates r).admissible r m := by
  refine ⟨hb.1,?_,?_,?_⟩
  · intro v z hz
    rw [bath_asRates_weight b r v z hz]
    exact sq_nonneg _
  · intro z hz
    simp_rw [bath_asRates_weight b r _ z hz]
    exact hb.2.1 z hz
  · intro z hz
    simp_rw [bath_asRates_weight b r _ z hz]
    exact hb.2.2 z hz

theorem bath_asRates_cost (b : BathFamily) (r : ℕ) (m : ℝ) :
    (b.asRates r).cost r m=b.cost r m := by
  unfold RateFamily.cost BathFamily.cost avg
  apply Real.circleAverage_congr_sphere
  intro z hz
  unfold RateFamily.sigma sigma
  simp_rw [bath_asRates_weight b r _ z (norm_unit_of_mem z hz)]
  rfl

def rateCosts (r : ℕ) (m : ℝ) : Set ℝ :=
  {x | ∃ b : RateFamily, b.admissible r m ∧ b.cost r m=x}

theorem rateCosts_eq (r : ℕ) (m : ℝ) : rateCosts r m=admissibleCosts r m := by
  ext x
  constructor
  · rintro ⟨b,hb,he⟩
    obtain ⟨b',ha,hc⟩ := rateFIR_realization b r m hb
    exact ⟨b',ha,hc.trans he⟩
  · rintro ⟨b,hb,he⟩
    exact ⟨b.asRates r,bath_asRates_admissible b r m hb,(bath_asRates_cost b r m).trans he⟩

theorem rate_infimum_eq (r : ℕ) (m : ℝ) : sInf (rateCosts r m)=optimalEntropy r m := by
  rw [rateCosts_eq,optimalEntropy]

end
end GaussianRange
#print axioms GaussianRange.real_factor_weight
#print axioms GaussianRange.trigRate_sym_factor
#print axioms GaussianRange.rateFIR_realization
#print axioms GaussianRange.rateCosts_eq
#print axioms GaussianRange.rate_infimum_eq