import TemperatureCount

namespace GaussianRange
open Finset Polynomial
noncomputable section

def threePoly : Option Bool → ℝ[X]
  | none => C (1/2)*(1-X^2)
  | some true => C (1/4)*(1+X)^2
  | some false => C (1/4)*(1-X)^2

def threeRate (v : Option Bool) (z : ℂ) : ℝ :=
  match v with
  | none => (1-z.re^2)/2
  | some true => (1+z.re)^2/4
  | some false => (1-z.re)^2/4

def threeTemp (m : ℝ) : Option Bool → ℝ
  | none => m+2
  | some true => m
  | some false => m+4

theorem threePoly_degree (v : Option Bool) : (threePoly v).natDegree≤2 := by
  have ha : ((1:ℝ[X])+X).natDegree≤1 :=
    (natDegree_add_le _ _).trans (max_le (by simp) (by simp))
  have hb : ((1:ℝ[X])-X).natDegree≤1 :=
    (natDegree_sub_le _ _).trans (max_le (by simp) (by simp))
  have hc : ((X:ℝ[X])^2).natDegree≤2 := by simp
  cases v with
  | none =>
    unfold threePoly
    exact (natDegree_C_mul_le _ _).trans
      ((natDegree_sub_le _ _).trans (max_le (by simp) hc))
  | some v =>
    cases v
    · unfold threePoly
      apply (natDegree_C_mul_le _ _).trans
      rw [pow_two]
      calc
        _ ≤ ((1:ℝ[X])-X).natDegree+((1:ℝ[X])-X).natDegree := natDegree_mul_le
        _ ≤ 2 := by omega
    · unfold threePoly
      apply (natDegree_C_mul_le _ _).trans
      rw [pow_two]
      calc
        _ ≤ ((1:ℝ[X])+X).natDegree+((1:ℝ[X])+X).natDegree := natDegree_mul_le
        _ ≤ 2 := by omega

theorem threePoly_eval (v : Option Bool) (z : ℂ) :
    (threePoly v).eval z.re=threeRate v z := by
  cases v with
  | none => simp [threePoly,threeRate]; ring
  | some v => cases v <;> simp [threePoly,threeRate] <;> ring

theorem threeRate_nonneg (v : Option Bool) (z : ℂ) (hz : ‖z‖=1) :
    0≤threeRate v z := by
  cases v with
  | none =>
    have h := unit_re_sq_im_sq z hz
    simp only [threeRate]
    nlinarith [sq_nonneg z.im]
  | some v => cases v <;> simp only [threeRate] <;> positivity

theorem avg_re_im_square : avg (fun z : ℂ => z.re*z.im^2)=0 := by
  let f : ℂ → ℝ := fun z => z.re*z.im^2
  have he : avg (fun z => f (-z))=avg f := by
    unfold avg
    rw [← Real.circleAverage_neg_radius (f := f) (c := (0:ℂ)) (R := (1:ℝ))]
    unfold Real.circleAverage
    congr 1
    apply intervalIntegral.integral_congr
    intro θ hθ
    congr 1
    simp [circleMap]
  have hneg : (fun z : ℂ => f (-z))=(fun z : ℂ => (-1:ℝ)*f z) := by
    funext z
    simp [f]
  rw [hneg] at he
  have hsmul : avg (fun z : ℂ => (-1:ℝ)*f z)=(-1:ℝ)*avg f :=
    Real.circleAverage_fun_smul (a:=(-1:ℝ))
  rw [hsmul] at he
  change avg f=0
  linarith

theorem three_temperature_realization (r : ℕ) (hr : 2≤r) (m : ℝ) (hm : 0<m) :
    ∃ b : BathFamily, b.admissible r m ∧ Fintype.card b.ι=3 ∧
      (∀ z : ℂ, ‖z‖=1 → sigma r b.coeff b.temp (m+2) z =
        (2/(m*(m+4)))*z.im^2+
        (4/(m*(m+2)*(m+4)))*(z.re*z.im^2)) := by
  have hf (v : Option Bool) : ∃ a : ℕ → ℝ, ∀ z : ℂ, ‖z‖=1 →
      weight r a z=threeRate v z := by
    obtain ⟨a,ha⟩ := real_factor_weight (threePoly v) r ((threePoly_degree v).trans hr)
      (fun z hz => (threePoly_eval v z).symm ▸ threeRate_nonneg v z hz)
    exact ⟨a,fun z hz => (ha z hz).trans (threePoly_eval v z)⟩
  choose a ha using hf
  let b : BathFamily := ⟨Option Bool,inferInstance,a,threeTemp m⟩
  refine ⟨b,⟨?_,?_,?_⟩,by change Fintype.card (Option Bool)=3; decide,?_⟩
  · intro v
    cases v with
    | none => change 0<m+2; linarith
    | some v => cases v <;> simp [b,threeTemp] <;> linarith
  · intro z hz
    change (∑ v : Option Bool, weight r (a v) z)=1
    rw [Fintype.sum_option,Fintype.sum_bool,ha none z hz,ha (some false) z hz,ha (some true) z hz]
    simp [threeRate]
    ring
  · intro z hz
    change (∑ v : Option Bool, threeTemp m v*weight r (a v) z)=_
    rw [Fintype.sum_option,Fintype.sum_bool,ha none z hz,ha (some false) z hz,ha (some true) z hz]
    simp [threeRate,threeTemp,dispersion]
    ring
  · intro z hz
    unfold sigma
    change dispersion (m+2) z*(∑ v : Option Bool, weight r (a v) z/threeTemp m v)-1=_
    rw [Fintype.sum_option,Fintype.sum_bool,ha none z hz,ha (some false) z hz,ha (some true) z hz]
    simp only [threeRate,threeTemp,dispersion]
    have h2 : m+2≠0 := by positivity
    have h4 : m+4≠0 := by positivity
    have he := unit_re_sq_im_sq z hz
    field_simp [hm.ne',h2,h4]
    nlinarith [congrArg (fun t : ℝ => m*z.re*t) he,congrArg (fun t : ℝ => z.re*t) he,
      congrArg (fun t : ℝ => m*t) he]

theorem three_temperature_half_cost (r : ℕ) (hr : 2≤r) (m : ℝ) (hm : 0<m) :
    ∃ b : BathFamily, b.admissible r m ∧ Fintype.card b.ι=3 ∧
      ¬ b.twoTemperature ∧ b.cost r m=1/(m*(m+4)) := by
  obtain ⟨b,hb,hcard,hs⟩ := three_temperature_realization r hr m hm
  let f : ℂ → ℝ := fun z => (2/(m*(m+4)))*z.im^2
  let g : ℂ → ℝ := fun z => (4/(m*(m+2)*(m+4)))*(z.re*z.im^2)
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hg : Continuous g := by dsimp [g]; fun_prop
  have hcost : b.cost r m=1/(m*(m+4)) := by
    unfold BathFamily.cost
    rw [avg_congr_unit _ (fun z => f z+g z) (cont_sigma r _ _ _) (hf.add hg) hs]
    have havg : avg (fun z => f z+g z)=avg f+avg g := by
      unfold avg
      rw [Real.circleAverage_fun_add (hf.continuousOn.circleIntegrable (by norm_num))
        (hg.continuousOn.circleIntegrable (by norm_num))]
    rw [havg]
    have h₁ : avg f=(2/(m*(m+4)))*avg (fun z : ℂ => z.im^2) :=
      Real.circleAverage_fun_smul (a:=2/(m*(m+4)))
    have h₂ : avg g=(4/(m*(m+2)*(m+4)))*avg (fun z : ℂ => z.re*z.im^2) :=
      Real.circleAverage_fun_smul (a:=4/(m*(m+2)*(m+4)))
    rw [h₁,h₂,avg_im_square,avg_re_im_square]
    ring
  refine ⟨b,hb,hcard,?_,hcost⟩
  intro ht
  have h := two_temperature_cost_lower b r (by omega) m hm hb ht
  rw [hcost] at h
  have hp : 0<m*(m+4) := by positivity
  have h' : (2:ℝ)≤1 := (div_le_div_iff_of_pos_right hp).mp h
  norm_num at h'

theorem unrestricted_strict_two_temperature_gap (r : ℕ) (hr : 2≤r) (m : ℝ) (hm : 0<m) :
    optimalEntropy r m≤1/(m*(m+4)) ∧
      optimalEntropy r m<sInf (twoTemperatureCosts r m) := by
  obtain ⟨b,hb,hcard,ht,hcost⟩ := three_temperature_half_cost r hr m hm
  have hbd : BddBelow (admissibleCosts r m) :=
    ⟨_,fun x hx => admissible_lower r (by omega) m hm x hx⟩
  have hu : optimalEntropy r m≤b.cost r m :=
    csInf_le hbd ⟨b,hb,rfl⟩
  rw [hcost] at hu
  refine ⟨hu,?_⟩
  rw [(two_temperature_minimum r (by omega) m hm).csInf_eq]
  exact hu.trans_lt (div_lt_div_of_pos_right (by norm_num) (by positivity))

end
end GaussianRange
#check GaussianRange.three_temperature_half_cost
#print axioms GaussianRange.three_temperature_realization
#print axioms GaussianRange.three_temperature_half_cost
#print axioms GaussianRange.unrestricted_strict_two_temperature_gap
