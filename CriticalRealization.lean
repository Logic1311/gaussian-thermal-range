import CriticalEnergy

namespace GaussianRange
open Finset Polynomial
noncomputable section

theorem norm_one_sub_pow_le_critical (z : ℂ) (hz : ‖z‖=1) (n : ℕ) :
    ‖1-z^n‖ ≤ (n:ℝ)*‖1-z‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ,show 1-z^n*z=(1-z^n)+z^n*(1-z) by ring]
    calc
      _ ≤ ‖1-z^n‖+‖z^n*(1-z)‖ := norm_add_le _ _
      _ ≤ (n:ℝ)*‖1-z‖+‖z^n*(1-z)‖ := add_le_add ih le_rfl
      _ = _ := by rw [norm_mul,norm_pow,hz,one_pow,one_mul,Nat.cast_succ]; ring

def criticalResidual (r : ℕ) (z : ℂ) : ℝ :=
  1-weight r (criticalCoeff r) z

def criticalPair (r : ℕ) (z : ℂ) (i j : ℕ) : ℝ :=
  criticalCoeff r i*criticalCoeff r j*(1-(z^i*star (z^j)).re)

theorem criticalResidual_pairs (r : ℕ) (z : ℂ) :
    criticalResidual r z=∑ i ∈ range (r+1),∑ j ∈ range (r+1),criticalPair r z i j := by
  unfold criticalResidual criticalPair
  rw [weight_pair_sum]
  simp_rw [mul_sub,mul_one,sum_sub_distrib]
  have h : (∑ i ∈ range (r+1),∑ j ∈ range (r+1),criticalCoeff r i*criticalCoeff r j)=1 := by
    simp_rw [← mul_sum,criticalCoeff_sum,mul_one]
    exact criticalCoeff_sum r
  rw [h]

theorem critical_pair_defect (z : ℂ) (hz : ‖z‖=1) (i j : ℕ) :
    1-(z^i*star (z^j)).re=‖1-z^(if i≤j then j-i else i-j)‖^2/2 := by
  rw [unit_pair_re z hz]
  have hu : ‖z^(if i≤j then j-i else i-j)‖=1 := by rw [norm_pow,hz,one_pow]
  rw [norm_one_sub_sq _ hu]
  unfold dispersion
  ring

theorem criticalPair_nonneg (r : ℕ) (z : ℂ) (hz : ‖z‖=1)
    (i j : ℕ) (hi : i≤r) (hj : j≤r) : 0≤criticalPair r z i j := by
  unfold criticalPair
  rw [critical_pair_defect z hz]
  positivity [(criticalCoeff_pos r i hi).le,(criticalCoeff_pos r j hj).le]

theorem criticalResidual_nonneg (r : ℕ) (z : ℂ) (hz : ‖z‖=1) :
    0≤criticalResidual r z := by
  rw [criticalResidual_pairs]
  apply sum_nonneg
  intro i hi
  apply sum_nonneg
  intro j hj
  exact criticalPair_nonneg r z hz i j (by simpa using Nat.le_of_lt_succ (mem_range.mp hi))
    (by simpa using Nat.le_of_lt_succ (mem_range.mp hj))

theorem criticalResidual_upper (r : ℕ) (z : ℂ) (hz : ‖z‖=1) :
    criticalResidual r z≤((r:ℝ)+1)^2*dispersion 2 z := by
  have hd : 0≤dispersion 2 z := by rw [← norm_one_sub_sq z hz]; positivity
  rw [criticalResidual_pairs]
  calc
    _ ≤ ∑ i ∈ range (r+1),∑ j ∈ range (r+1),
        criticalCoeff r i*criticalCoeff r j*(((r:ℝ)+1)^2*dispersion 2 z) := by
      apply sum_le_sum
      intro i hi
      apply sum_le_sum
      intro j hj
      have hi' : i≤r := Nat.le_of_lt_succ (mem_range.mp hi)
      have hj' : j≤r := Nat.le_of_lt_succ (mem_range.mp hj)
      let d := if i≤j then j-i else i-j
      have hd' : d≤r+1 := by dsimp [d]; split_ifs <;> omega
      have hdd : (d:ℝ)≤(r:ℝ)+1 := by exact_mod_cast hd'
      have hnorm : ‖1-z^d‖≤((r:ℝ)+1)*‖1-z‖ :=
        (norm_one_sub_pow_le_critical z hz d).trans (mul_le_mul_of_nonneg_right hdd (norm_nonneg _))
      have hsq : ‖1-z^d‖^2≤(((r:ℝ)+1)*‖1-z‖)^2 :=
        pow_le_pow_left₀ (norm_nonneg _) hnorm 2
      rw [mul_pow,norm_one_sub_sq z hz] at hsq
      unfold criticalPair
      rw [critical_pair_defect z hz]
      change criticalCoeff r i*criticalCoeff r j*(‖1-z^d‖^2/2)≤_
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (criticalCoeff_pos r i hi').le (criticalCoeff_pos r j hj').le)
      nlinarith [sq_nonneg ‖1-z^d‖]
    _ = _ := by
      have h : (∑ i ∈ range (r+1),∑ j ∈ range (r+1),criticalCoeff r i*criticalCoeff r j)=1 := by
        simp_rw [← mul_sum,criticalCoeff_sum,mul_one]
        exact criticalCoeff_sum r
      calc
        _ = (∑ i ∈ range (r+1),∑ j ∈ range (r+1),criticalCoeff r i*criticalCoeff r j) *
            (((r:ℝ)+1)^2*dispersion 2 z) := by simp only [sum_mul]
        _ = _ := by rw [h,one_mul]

theorem criticalResidual_lower (r : ℕ) (hr : 0<r) (z : ℂ) (hz : ‖z‖=1) :
    criticalCoeff r 0*criticalCoeff r 1*dispersion 2 z/2≤criticalResidual r z := by
  have hrow : criticalPair r z 0 1≤∑ j ∈ range (r+1),criticalPair r z 0 j := by
    apply single_le_sum
    · intro j hj
      exact criticalPair_nonneg r z hz 0 j (Nat.zero_le _) (Nat.le_of_lt_succ (mem_range.mp hj))
    · simp; omega
  have htot : (∑ j ∈ range (r+1),criticalPair r z 0 j)≤
      ∑ i ∈ range (r+1),∑ j ∈ range (r+1),criticalPair r z i j := by
    apply single_le_sum (f := fun i : ℕ => ∑ j ∈ range (r+1),criticalPair r z i j)
    · intro i hi
      exact sum_nonneg (fun j hj => criticalPair_nonneg r z hz i j
        (Nat.le_of_lt_succ (mem_range.mp hi)) (Nat.le_of_lt_succ (mem_range.mp hj)))
    · simp
  rw [criticalResidual_pairs]
  have he : criticalPair r z 0 1=criticalCoeff r 0*criticalCoeff r 1*dispersion 2 z/2 := by
    unfold criticalPair
    rw [unit_pair_re z hz]
    norm_num [dispersion]
    ring
  rw [← he]
  exact hrow.trans htot

def criticalA (r : ℕ) : ℝ := 1/((r:ℝ)+1)^2

def criticalB (r : ℕ) : ℝ :=
  criticalA r+1+2/(criticalCoeff r 0*criticalCoeff r 1)

theorem criticalA_pos (r : ℕ) : 0<criticalA r := by unfold criticalA; positivity

theorem criticalA_lt_B (r : ℕ) (hr : 0<r) : criticalA r<criticalB r := by
  unfold criticalB
  have h := mul_pos (criticalCoeff_pos r 0 (Nat.zero_le _)) (criticalCoeff_pos r 1 (by omega))
  linarith [show 0<2/(criticalCoeff r 0*criticalCoeff r 1) by positivity]

theorem critical_mix_bounds (r : ℕ) (hr : 0<r) (z : ℂ) (hz : ‖z‖=1) :
    criticalA r*criticalResidual r z≤dispersion 2 z ∧
      dispersion 2 z≤criticalB r*criticalResidual r z := by
  constructor
  · have h := criticalResidual_upper r z hz
    unfold criticalA
    rw [one_div,mul_comm,← div_eq_mul_inv]
    exact (div_le_iff₀ (by positivity : 0<((r:ℝ)+1)^2)).2 (by simpa [mul_comm] using h)
  · have h := criticalResidual_lower r hr z hz
    have hp := mul_pos (criticalCoeff_pos r 0 (Nat.zero_le _)) (criticalCoeff_pos r 1 (by omega))
    have hb : dispersion 2 z≤(2/(criticalCoeff r 0*criticalCoeff r 1))*criticalResidual r z := by
      apply (le_div_iff₀ hp).2
        (show dispersion 2 z*(criticalCoeff r 0*criticalCoeff r 1)≤2*criticalResidual r z by nlinarith)
        |>.trans_eq (by ring)
    have hR := criticalResidual_nonneg r z hz
    exact hb.trans (mul_le_mul_of_nonneg_right (by unfold criticalB; linarith [criticalA_pos r]) hR)

def criticalColdPoly (r : ℕ) : ℝ[X] := evenRatePoly r (lagCoeff r (criticalCoeff r))
def criticalResidualPoly (r : ℕ) : ℝ[X] := 1-criticalColdPoly r
def criticalDispPoly : ℝ[X] := C 2-C 2*X

def criticalHotPoly (r : ℕ) (v : Bool) : ℝ[X] :=
  C (1/(criticalB r-criticalA r)) *
    (if v then criticalDispPoly-C (criticalA r)*criticalResidualPoly r
      else C (criticalB r)*criticalResidualPoly r-criticalDispPoly)

theorem criticalColdPoly_eval (r : ℕ) (z : ℂ) (hz : ‖z‖=1) :
    (criticalColdPoly r).eval z.re=weight r (criticalCoeff r) z := by
  rw [criticalColdPoly,evenRatePoly_eval r _ z hz,physical_weight_trig r _ z hz]
  simp [trigRate]

theorem criticalResidualPoly_degree (r : ℕ) : (criticalResidualPoly r).natDegree≤r := by
  apply (natDegree_sub_le _ _).trans
  exact max_le (by simp) (evenRatePoly_degree _ _)

theorem criticalDispPoly_degree : criticalDispPoly.natDegree≤1 := by
  unfold criticalDispPoly
  apply (natDegree_sub_le _ _).trans
  exact max_le (by simp) ((natDegree_C_mul_le _ _).trans (by simp))

theorem criticalHotPoly_degree (r : ℕ) (hr : 0<r) (v : Bool) :
    (criticalHotPoly r v).natDegree≤r := by
  unfold criticalHotPoly
  apply (natDegree_C_mul_le _ _).trans
  cases v <;> simp only [Bool.false_eq_true,if_false,if_true]
  · exact (natDegree_sub_le _ _).trans (max_le ((natDegree_C_mul_le _ _).trans (criticalResidualPoly_degree r)) (criticalDispPoly_degree.trans hr))
  · exact (natDegree_sub_le _ _).trans (max_le (criticalDispPoly_degree.trans hr) ((natDegree_C_mul_le _ _).trans (criticalResidualPoly_degree r)))

def criticalHotRate (r : ℕ) (v : Bool) (z : ℂ) : ℝ :=
  if v then (dispersion 2 z-criticalA r*criticalResidual r z)/(criticalB r-criticalA r)
  else (criticalB r*criticalResidual r z-dispersion 2 z)/(criticalB r-criticalA r)

theorem criticalHotPoly_eval (r : ℕ) (v : Bool) (z : ℂ) (hz : ‖z‖=1) :
    (criticalHotPoly r v).eval z.re=criticalHotRate r v z := by
  cases v <;> simp [criticalHotPoly,criticalHotRate,criticalDispPoly,criticalResidualPoly,
    criticalColdPoly_eval r z hz,criticalResidual,dispersion] <;> ring

theorem criticalHotRate_nonneg (r : ℕ) (hr : 0<r) (v : Bool) (z : ℂ) (hz : ‖z‖=1) :
    0≤criticalHotRate r v z := by
  have hb := sub_pos.mpr (criticalA_lt_B r hr)
  obtain ⟨h₁,h₂⟩ := critical_mix_bounds r hr z hz
  cases v <;> simp only [criticalHotRate,Bool.false_eq_true,if_false,if_true]
  · exact div_nonneg (sub_nonneg.mpr h₂) hb.le
  · exact div_nonneg (sub_nonneg.mpr h₁) hb.le

theorem criticalHotRate_sum (r : ℕ) (hr : 0<r) (z : ℂ) :
    criticalHotRate r false z+criticalHotRate r true z=criticalResidual r z := by
  simp only [criticalHotRate,Bool.false_eq_true,if_false,if_true]
  field_simp [(sub_pos.mpr (criticalA_lt_B r hr)).ne']
  <;> ring

theorem criticalHotRate_weighted (r : ℕ) (hr : 0<r) (z : ℂ) :
    criticalA r*criticalHotRate r false z+criticalB r*criticalHotRate r true z=dispersion 2 z := by
  simp only [criticalHotRate,Bool.false_eq_true,if_false,if_true]
  field_simp [(sub_pos.mpr (criticalA_lt_B r hr)).ne']
  <;> ring

def criticalTemperature (r : ℕ) (m : ℝ) : Option Bool → ℝ
  | none => m
  | some false => m+criticalA r
  | some true => m+criticalB r

theorem critical_realization (r : ℕ) (hr : 0<r) (m : ℝ) (hm : 0<m) :
    ∃ b : BathFamily, b.admissible r m ∧ Fintype.card b.ι=3 ∧
      (∀ z : ℂ, ‖z‖=1 → sigma r b.coeff b.temp (m+2) z =
        dispersion (m+2) z*(weight r (criticalCoeff r) z/m+
          criticalHotRate r false z/(m+criticalA r)+
          criticalHotRate r true z/(m+criticalB r))-1) := by
  have hf (v : Bool) : ∃ a : ℕ → ℝ, ∀ z : ℂ, ‖z‖=1 → weight r a z=criticalHotRate r v z := by
    obtain ⟨a,ha⟩ := real_factor_weight (criticalHotPoly r v) r (criticalHotPoly_degree r hr v)
      (fun z hz => (criticalHotPoly_eval r v z hz).symm ▸ criticalHotRate_nonneg r hr v z hz)
    exact ⟨a,fun z hz => (ha z hz).trans (criticalHotPoly_eval r v z hz)⟩
  choose a ha using hf
  let b : BathFamily := ⟨Option Bool,inferInstance,
    fun v => v.elim (criticalCoeff r) a,criticalTemperature r m⟩
  have hA := criticalA_pos r
  have hB := hA.trans (criticalA_lt_B r hr)
  refine ⟨b,⟨?_,?_,?_⟩,by change Fintype.card (Option Bool)=3; decide,?_⟩
  · intro v
    cases v with
    | none => exact hm
    | some v => cases v <;> simp [b,criticalTemperature] <;> linarith
  · intro z hz
    change (∑ v : Option Bool, weight r (v.elim (criticalCoeff r) a) z)=1
    rw [Fintype.sum_option,Fintype.sum_bool]
    simp only [Option.elim]
    rw [ha false z hz,ha true z hz]
    have he := criticalHotRate_sum r hr z
    unfold criticalResidual at he
    linarith
  · intro z hz
    change (∑ v : Option Bool, criticalTemperature r m v*weight r (v.elim (criticalCoeff r) a) z)=_
    rw [Fintype.sum_option,Fintype.sum_bool]
    simp only [Option.elim,criticalTemperature]
    rw [ha false z hz,ha true z hz]
    have hs := criticalHotRate_sum r hr z
    have hw := criticalHotRate_weighted r hr z
    unfold criticalResidual at hs
    unfold dispersion at *
    nlinarith
  · intro z hz
    unfold sigma
    change dispersion (m+2) z*(∑ v : Option Bool, weight r (v.elim (criticalCoeff r) a) z/criticalTemperature r m v)-1=_
    rw [Fintype.sum_option,Fintype.sum_bool]
    simp only [Option.elim,criticalTemperature]
    rw [ha false z hz,ha true z hz]
    ring

end
end GaussianRange
#print axioms GaussianRange.critical_mix_bounds
#print axioms GaussianRange.critical_realization
