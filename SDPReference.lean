import SDPMoments

namespace GaussianRange
open Finset Polynomial
open scoped RealInnerProductSpace
noncomputable section

def shiftCoeff (r : ℕ) (i : Fin r) (v : Bool) (j : ℕ) : ℝ :=
  if j=i.val then (1/2)/Real.sqrt r else
    if j=i.val+1 then (if v then 1/2 else -1/2)/Real.sqrt r else 0

def referenceBath (r : ℕ) (m : ℝ) : BathFamily where
  ι := Fin r × Bool
  finite := inferInstance
  coeff := fun v => shiftCoeff r v.1 v.2
  temp := fun v => if v.2 then m else m+4

theorem shift_amp (r : ℕ) (i : Fin r) (v : Bool) :
    amp r (shiftCoeff r i v) =
    monomial i.val (((1/2)/Real.sqrt r : ℝ):ℂ)+
    monomial (i.val+1) (((if v then 1/2 else -1/2)/Real.sqrt r : ℝ):ℂ) := by
  ext j
  rw [amp_coeff,coeff_add,coeff_monomial,coeff_monomial]
  unfold shiftCoeff
  have hi := i.isLt
  by_cases h : j=i.val
  · subst j
    simp [Nat.le_of_lt hi]
  · by_cases h' : j=i.val+1
    · subst j
      simp [show i.val+1≤r by omega]
    · have h₁ : i.val≠j := Ne.symm h
      have h₂ : i.val+1≠j := Ne.symm h'
      split_ifs <;> simp [h,h',h₁,h₂]

theorem shift_amp_eval (r : ℕ) (i : Fin r) (v : Bool) (z : ℂ) :
    (amp r (shiftCoeff r i v)).eval z =
    (z^i.val/((Real.sqrt r : ℝ):ℂ))*(1/2+(if v then 1/2 else -1/2)*z) := by
  have hr : 0<(r:ℝ) := by exact_mod_cast Nat.zero_lt_of_lt i.isLt
  have hsr : ((Real.sqrt r : ℝ):ℂ)≠0 := by exact_mod_cast (Real.sqrt_pos.2 hr).ne'
  rw [shift_amp,eval_add,eval_monomial,eval_monomial,pow_succ]
  push_cast
  cases v <;> simp <;> field_simp [hsr] <;> ring

theorem shift_weight (r : ℕ) (hr : 0<r) (i : Fin r) (v : Bool) (z : ℂ) (hz : ‖z‖=1) :
    weight r (shiftCoeff r i v) z=weight r (nearestCoeff v) z/(r:ℝ) := by
  have hrr : 0<(r:ℝ) := by exact_mod_cast hr
  unfold weight
  rw [shift_amp_eval,nearest_amp_eval r hr,norm_mul,norm_div,norm_pow,hz,one_pow,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),mul_pow,div_pow,one_pow,Real.sq_sqrt hrr.le]
  ring

theorem reference_admissible (r : ℕ) (hr : 0<r) (m : ℝ) (hm : 0<m) :
    (referenceBath r m).admissible r m := by
  have hrr : (r:ℝ)≠0 := by exact_mod_cast hr.ne'
  refine ⟨?_,?_,?_⟩
  · intro v
    change 0<(if v.2 then m else m+4)
    split_ifs <;> linarith
  · intro z hz
    change (∑ v : Fin r × Bool, weight r (shiftCoeff r v.1 v.2) z)=1
    rw [Fintype.sum_prod_type]
    simp_rw [shift_weight r hr _ _ z hz,← sum_div]
    have h := (nearest_admissible r hr m hm).2.1 z hz
    change (∑ v : Bool, weight r (nearestCoeff v) z)=1 at h
    simp_rw [h]
    simp [hrr]
  · intro z hz
    change (∑ v : Fin r × Bool,(if v.2 then m else m+4)*weight r (shiftCoeff r v.1 v.2) z)=_
    rw [Fintype.sum_prod_type]
    simp_rw [shift_weight r hr _ _ z hz,← mul_div_assoc,← sum_div]
    have h := (nearest_admissible r hr m hm).2.2 z hz
    change (∑ v : Bool,(if v then m else m+4)*weight r (nearestCoeff v) z)=_ at h
    simp_rw [h]
    simp [hrr,mul_div_cancel_left₀]

theorem shift_row_inner (r : ℕ) (i : Fin r) (v : Bool) (m : ℝ)
    (x : SDPSpace (r+1)) :
    ⟪sdpRow (referenceBath r m) r (i,v),x⟫ =
      ((1/2)/Real.sqrt r)*x ⟨i.val,by omega⟩+
      ((if v then 1/2 else -1/2)/Real.sqrt r)*x ⟨i.val+1,by omega⟩ := by
  rw [row_inner]
  let a : Fin (r+1) := ⟨i.val,by omega⟩
  let b : Fin (r+1) := ⟨i.val+1,by omega⟩
  have hab : a≠b := by intro he; have h := congrArg Fin.val he; dsimp [a,b] at h; omega
  change (∑ j : Fin (r+1),shiftCoeff r i v j*x j)=_
  have he (j : Fin (r+1)) : shiftCoeff r i v j*x j =
      (if j=a then ((1/2)/Real.sqrt r)*x a else 0)+
      (if j=b then ((if v then 1/2 else -1/2)/Real.sqrt r)*x b else 0) := by
    unfold shiftCoeff
    by_cases ha : j=a
    · subst j
      simp [a,hab]
    · by_cases hb : j=b
      · subst j
        simp [a,b,Ne.symm hab]
      · have ha' : j.val≠i.val := by intro h; exact ha (Fin.ext h)
        have hb' : j.val≠i.val+1 := by intro h; exact hb (Fin.ext h)
        simp [ha,hb,ha',hb']
  simp_rw [he]
  rw [sum_add_distrib]
  simp [a,b]

theorem reference_rows_separate (r : ℕ) (hr : 0<r) (m : ℝ) (x : SDPSpace (r+1))
    (hx : x≠0) : ∃ v : (referenceBath r m).ι, ⟪sdpRow (referenceBath r m) r v,x⟫≠0 := by
  by_contra! h
  have hrr : 0<(r:ℝ) := by exact_mod_cast hr
  have hs := Real.sqrt_pos.2 hrr
  have hzero (i : Fin r) : x ⟨i.val,by omega⟩=0 ∧ x ⟨i.val+1,by omega⟩=0 := by
    have h₁ := h (i,true)
    have h₂ := h (i,false)
    rw [shift_row_inner] at h₁ h₂
    norm_num at h₁ h₂
    field_simp [hs.ne'] at h₁ h₂
    constructor <;> linarith
  apply hx
  ext j
  change x j=0
  by_cases hj : j.val<r
  · exact (hzero ⟨j.val,hj⟩).1
  · have he : j.val=r := by omega
    let i : Fin r := ⟨r-1,by omega⟩
    have h := (hzero i).2
    have he' : (⟨i.val+1,by omega⟩ : Fin (r+1))=j := by apply Fin.ext; dsimp [i]; omega
    rwa [he'] at h

theorem reference_gram_positive (r : ℕ) (hr : 0<r) (m : ℝ)
    (t : (referenceBath r m).ι → ℝ) (ht : ∀ v,0<t v) :
    sdpPositive (gramOp (referenceBath r m) r t) := by
  intro x hx
  rw [gramOp_inner]
  obtain ⟨v,hv⟩ := reference_rows_separate r hr m x hx
  apply sum_pos' (fun u _ => by nlinarith [mul_nonneg (ht u).le (sq_nonneg ⟪sdpRow (referenceBath r m) r u,x⟫)])
  exact ⟨v,mem_univ _,by nlinarith [mul_pos (ht v) (sq_pos_of_ne_zero hv)]⟩

theorem reference_sdp (r : ℕ) (hr : 0<r) (m : ℝ) (hm : 0<m) :
    ∃ p : SDPMoments r, SDPFeasible p m ∧ sdpPositive p.G ∧ sdpPositive p.H := by
  have hb := reference_admissible r hr m hm
  exact ⟨bathMoments (referenceBath r m) r,bathMoments_feasible _ _ _ hb,
    reference_gram_positive r hr m _ (fun _ => by norm_num),
    reference_gram_positive r hr m _ hb.1⟩

end
end GaussianRange
#print axioms GaussianRange.reference_admissible
#print axioms GaussianRange.reference_sdp
