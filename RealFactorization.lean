import RealFactorBase

namespace GaussianRange
open Polynomial
open Set
noncomputable section

def IntervalNonneg (p : ℝ[X]) : Prop :=
  ∀ x : ℝ, -1 ≤ x → x ≤ 1 → 0 ≤ p.eval x

/-- Extend positivity from an open interval to either endpoint. -/
theorem nonneg_endpoints (f : ℝ → ℝ) (hf : Continuous f) {a b : ℝ} (hab : a < b)
    (h : ∀ x ∈ Ioo a b, 0 ≤ f x) : 0 ≤ f a ∧ 0 ≤ f b := by
  have hc : IsClosed {x : ℝ | 0 ≤ f x} := isClosed_le continuous_const hf
  have hs : closure (Ioo a b) ⊆ {x : ℝ | 0 ≤ f x} := closure_minimal h hc
  rw [closure_Ioo (ne_of_lt hab)] at hs
  exact ⟨hs ⟨le_rfl,hab.le⟩,hs ⟨hab.le,le_rfl⟩⟩

theorem intervalNonneg_remove_point (q : ℝ[X]) (a : ℝ)
    (h : ∀ x : ℝ, -1 ≤ x → x ≤ 1 → x ≠ a → 0 ≤ q.eval x) : IntervalNonneg q := by
  intro x hl hu
  by_cases he : x=a
  · subst x
    by_cases ha : a < 1
    · exact (nonneg_endpoints q.eval q.continuous ha (fun y hy => h y (hl.trans hy.1.le) hy.2.le (ne_of_gt hy.1))).1
    · have ha' : -1 < a := by linarith
      exact (nonneg_endpoints q.eval q.continuous ha' (fun y hy => h y hy.1.le (hy.2.le.trans hu) (ne_of_lt hy.2))).2
  · exact h x hl hu he

/-- A real root strictly inside the positivity interval occurs at least twice. -/
theorem interior_root_twice (p q : ℝ[X]) (a : ℝ) (ha : -1 < a) (hb : a < 1)
    (hpq : p=(X-C a)*q) (hp : IntervalNonneg p) : q.eval a=0 := by
  have hplus : 0 ≤ q.eval a := (nonneg_endpoints q.eval q.continuous hb (fun x hx => by
    have h := hp x (ha.le.trans hx.1.le) hx.2.le
    rw [hpq,eval_mul,eval_sub,eval_X,eval_C] at h
    exact nonneg_of_mul_nonneg_right h (sub_pos.mpr hx.1))).1
  have hminus : 0 ≤ -q.eval a := (nonneg_endpoints (fun x => -q.eval x) q.continuous.neg ha (fun x hx => by
    have h := hp x hx.1.le (hx.2.le.trans hb.le)
    rw [hpq,eval_mul,eval_sub,eval_X,eval_C] at h
    have h' : 0 ≤ (a-x)*(-q.eval x) := by nlinarith
    exact nonneg_of_mul_nonneg_right h' (sub_pos.mpr hx.2))).2
  linarith

theorem interval_quotient_nonneg (p f q : ℝ[X]) (a : ℝ)
    (hpq : p=f*q) (hp : IntervalNonneg p)
    (hf : ∀ x : ℝ, -1 ≤ x → x ≤ 1 → x ≠ a → 0 < f.eval x) : IntervalNonneg q := by
  apply intervalNonneg_remove_point q a
  intro x hl hu hne
  have h := hp x hl hu
  rw [hpq,eval_mul] at h
  exact nonneg_of_mul_nonneg_right h (hf x hl hu hne)

/-- Exact factorization for every real polynomial nonnegative on [-1,1],
with support degree no larger than its actual degree. No positivity margin assumed. -/
theorem realFactor_interval (p : ℝ[X]) (hp : IntervalNonneg p) :
    RealFactor p p.natDegree := by
  have aux : ∀ n : ℕ, ∀ p : ℝ[X], p.natDegree=n → IntervalNonneg p → RealFactor p n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro p hd hp
      by_cases hn : n=0
      · have he := eq_C_of_natDegree_eq_zero (hd.trans hn)
        have h0 := hp 0 (by norm_num) (by norm_num)
        rw [he,eval_C] at h0
        rw [he]
        simpa [hn] using realFactor_const _ h0
      have hpn : p ≠ 0 := by
        intro h
        subst p
        simp at hd
        exact hn hd.symm
      have hpd : p.degree ≠ 0 := by
        rw [degree_eq_natDegree hpn,hd]
        exact_mod_cast hn
      have combine : ∀ f q : ℝ[X], ∀ k : ℕ, p=f*q → f.natDegree=k → 0<k →
          RealFactor f k → IntervalNonneg q → RealFactor p n := by
        intro f q k he hf hk hfac hq
        have hf0 : f ≠ 0 := by
          intro h; subst f; simp at he; exact hpn he
        have hq0 : q ≠ 0 := by
          intro h; subst q; simp at he; exact hpn he
        have hnq : n=k+q.natDegree := by rw [← hd,he,natDegree_mul hf0 hq0,hf]
        have hlt : q.natDegree<n := by omega
        have hqf := ih q.natDegree hlt q rfl hq
        rw [he,hnq]
        exact realFactor_mul hfac hqf
      obtain ⟨z,hz⟩ : ∃ z : ℂ, aeval z p=0 := IsAlgClosed.exists_aeval_eq_zero ℂ p hpd
      by_cases hi : z.im=0
      · let a := z.re
        have hzreal : z=(a:ℂ) := by
          apply Complex.ext
          · rfl
          · simpa using hi
        have hroot : p.eval a=0 := by
          rw [hzreal] at hz
          change aeval (algebraMap ℝ ℂ a) p=0 at hz
          rw [aeval_algebraMap_apply_eq_algebraMap_eval] at hz
          change ((p.eval a : ℝ):ℂ)=0 at hz
          exact_mod_cast hz
        obtain ⟨q,hq⟩ := (dvd_iff_isRoot.mpr hroot : X-C a ∣ p)
        by_cases hl : a≤ -1
        · apply combine (X-C a) q 1 hq (by simp) (by omega)
          · have he : X-C a = C (1:ℝ)*X+C (-a) := by simp [sub_eq_add_neg]
            rw [he]
            exact realFactor_linear (-a) 1 (by linarith) (by linarith)
          · apply interval_quotient_nonneg p (X-C a) q a hq hp
            intro x hx hy hne
            simp
            exact lt_of_le_of_ne (hl.trans hx) (Ne.symm hne)
        · by_cases hu : 1≤a
          · have hq' : p=(C a-X)*(-q) := by rw [hq]; ring
            refine combine (C a-X) (-q) 1 hq' ?_ (by omega) ?_ ?_
            · have he : C a-X = C (-1:ℝ)*X+C a := by simp [sub_eq_add_neg,add_comm]
              rw [he]
              exact natDegree_linear (a := (-1:ℝ)) (b := a) (by norm_num)
            · have he : C a-X = C (-1:ℝ)*X+C a := by simp [sub_eq_add_neg,add_comm]
              rw [he]
              exact realFactor_linear a (-1) (by linarith) (by linarith)
            · apply interval_quotient_nonneg p (C a-X) (-q) a hq' hp
              intro x hx hy hne
              simp
              exact lt_of_le_of_ne (hy.trans hu) hne
          · have hqa := interior_root_twice p q a (by linarith) (by linarith) hq hp
            obtain ⟨s,hs⟩ := (dvd_iff_isRoot.mpr hqa : X-C a ∣ q)
            have he : p=(X^2-C (2*a)*X+C (a^2+0^2))*s := by
              rw [hq,hs]
              simp [map_mul,map_pow]
              rw [show (C (2:ℝ):ℝ[X]) = 2 by exact map_ofNat C 2]
              ring
            refine combine (X^2-C (2*a)*X+C (a^2+0^2)) s 2 he ?_ (by omega) ?_ ?_
            · have hh : (X^2-C (2*a)*X+C (a^2+0^2) : ℝ[X]) = C (1:ℝ)*X^2+C (-2*a)*X+C (a^2+0^2) := by simp [sub_eq_add_neg,neg_mul]
              rw [hh]
              exact natDegree_quadratic (a := (1:ℝ)) one_ne_zero
            · exact realFactor_quadratic a 0
            · apply interval_quotient_nonneg p _ s a he hp
              intro x hx hy hn
              simp
              nlinarith [sq_pos_of_ne_zero (sub_ne_zero.mpr hn)]
      · have hdiv := quadratic_dvd_of_aeval_eq_zero_im_ne_zero p hz hi
        have hnorm : ‖z‖^2=z.re^2+z.im^2 := by rw [← Complex.normSq_eq_norm_sq,Complex.normSq_apply]; ring
        rw [hnorm] at hdiv
        obtain ⟨q,hq⟩ := hdiv
        refine combine (X^2-C (2*z.re)*X+C (z.re^2+z.im^2)) q 2 hq ?_ (by omega) ?_ ?_
        · have he : (X^2-C (2*z.re)*X+C (z.re^2+z.im^2) : ℝ[X]) =
              C (1:ℝ)*X^2+C (-2*z.re)*X+C (z.re^2+z.im^2) := by simp [sub_eq_add_neg,neg_mul]
          rw [he]
          exact natDegree_quadratic (a := (1:ℝ)) one_ne_zero
        · exact realFactor_quadratic z.re z.im
        · intro x hl hu
          have h := hp x hl hu
          rw [hq,eval_mul] at h
          apply nonneg_of_mul_nonneg_right h
          simp
          nlinarith [sq_nonneg (x-z.re),sq_pos_of_ne_zero hi]
  exact aux p.natDegree p rfl hp

end
end GaussianRange
#print axioms GaussianRange.realFactor_interval