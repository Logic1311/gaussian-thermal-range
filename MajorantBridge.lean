import TrigSymmetry
import RealFactorization
import RelaxationPower

namespace GaussianRange
open Finset Polynomial
noncomputable section

theorem cosPoly_degree_exact (j : ℕ) : (cosPoly j).natDegree=j := by
  induction j using Nat.twoStepInduction with
  | zero => simp [cosPoly]
  | one => simp [cosPoly]
  | more n hn hm =>
    have h0 : cosPoly (n+1) ≠ 0 := by
      intro h
      rw [h,natDegree_zero] at hm
      omega
    have hd : (C (2:ℝ)*X*cosPoly (n+1)).natDegree=n+2 := by
      rw [natDegree_mul (mul_ne_zero (by simp) X_ne_zero) h0,
        natDegree_C_mul_X _ (by norm_num),hm]
      omega
    rw [cosPoly,natDegree_sub_eq_left_of_natDegree_lt (by rw [hd,hn]; omega),hd]

theorem poly_cos_repr (r : ℕ) (p : ℝ[X]) (hp : p.natDegree≤r) :
    ∃ a : ℕ → ℝ, evenRatePoly r a=p := by
  induction r generalizing p with
  | zero =>
    refine ⟨fun _ => p.coeff 0,?_⟩
    have he : p=C (p.coeff 0) := by
      ext j
      cases j with
      | zero => simp
      | succ j => simp [coeff_eq_zero_of_natDegree_lt (by omega : p.natDegree<j+1)]
    simpa only [evenRatePoly,zero_add,range_one,sum_singleton,cosPoly,mul_one] using he.symm
  | succ r ih =>
    let d := r+1
    let a := p.coeff d/(cosPoly d).leadingCoeff
    let q := p-C a*cosPoly d
    have hne : cosPoly d≠0 := by
      intro h
      have hh := cosPoly_degree_exact d
      rw [h,natDegree_zero] at hh
      dsimp [d] at hh
      omega
    have hl := leadingCoeff_ne_zero.mpr hne
    have hq : q.natDegree≤r := by
      rw [natDegree_le_iff_coeff_eq_zero]
      intro j hj
      by_cases he : j=d
      · subst j
        dsimp [q,a]
        have hc : (cosPoly d).coeff d=(cosPoly d).leadingCoeff := by
          exact (congrArg (fun k => (cosPoly d).coeff k) (cosPoly_degree_exact d).symm).trans coeff_natDegree
        rw [coeff_sub,coeff_C_mul,hc]
        field_simp <;> ring
      · have hj' : d<j := by dsimp [d] at *; omega
        dsimp [q]
        rw [coeff_sub,coeff_C_mul,coeff_eq_zero_of_natDegree_lt (by omega : p.natDegree<j),
          coeff_eq_zero_of_natDegree_lt (by rw [cosPoly_degree_exact]; exact hj')]
        ring
    obtain ⟨b,hb⟩ := ih q hq
    refine ⟨fun j => if j=d then a else b j,?_⟩
    unfold evenRatePoly
    rw [Finset.sum_range_succ]
    have he : (∑ j ∈ range (r+1), C (if j=d then a else b j)*cosPoly j) = evenRatePoly r b := by
      unfold evenRatePoly
      apply Finset.sum_congr rfl
      intro j hj
      have hh := Finset.mem_range.mp hj
      rw [if_neg (by dsimp [d]; omega)]
    rw [he,hb]
    simp only [show r+1=d from rfl,if_pos rfl]
    dsimp [q,d]
    ring

def laurentLift (p : ℕ) (q : ℝ[X]) : ℂ[X] :=
    ∑ j ∈ range (p+1), C (q.coeff j : ℂ) * (C (1/2:ℂ)*(X^2+1))^j * X^(p-j)

theorem laurentLift_eval (p : ℕ) (q : ℝ[X]) (hq : q.natDegree≤p) (z : ℂ) (hz : z≠0) :
    (laurentLift p q).eval z=z^p*q.eval₂ (algebraMap ℝ ℂ) ((z+z⁻¹)/2) := by
  unfold laurentLift
  rw [eval₂_eq_sum_range' _ (by omega : q.natDegree<p+1)]
  simp only [eval_finset_sum,eval_mul,eval_C,eval_pow,eval_add,eval_X,eval_one,mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j≤p := by simpa using Finset.mem_range.mp hj
  have he : (1/2:ℂ)*(z^2+1)=z*((z+z⁻¹)/2) := by field_simp <;> ring
  rw [he,mul_pow]
  have hh : z^j*z^(p-j)=z^p := by rw [← pow_add,Nat.add_sub_of_le hj']
  calc
    _ = (z^j*z^(p-j))*((q.coeff j:ℂ)*((z+z⁻¹)/2)^j) := by ring
    _ = _ := by rw [hh]; rfl

theorem eval₂_real (q : ℝ[X]) (x : ℝ) :
    q.eval₂ (algebraMap ℝ ℂ) (x:ℂ) = ((q.eval x : ℝ):ℂ) := by
  rw [eval₂_eq_sum_range,eval_eq_sum_range]
  simp [Complex.ofReal_sum]

theorem unit_average_re (z : ℂ) (hz : ‖z‖=1) :
    (z+z⁻¹)/2 = (z.re:ℂ) := by
  rw [← unit_star_inv z hz]
  apply Complex.ext <;> simp [Complex.add_re,Complex.add_im,Complex.div_re,Complex.div_im] <;> ring

theorem laurentLift_factor (p : ℕ) (q : ℝ[X]) (hq : q.natDegree≤p) (a : ℕ → ℝ)
    (he : ∀ z : ℂ, ‖z‖=1 → weight p a z=q.eval z.re) :
    laurentLift p q=amp p a*rev p a := by
  apply poly_unit_unique
  intro z hz
  have hz0 : z≠0 := by intro h; rw [h,norm_zero] at hz; norm_num at hz
  rw [laurentLift_eval p q hq z hz0,unit_average_re z hz,eval₂_real,spectral_eval p a z hz]
  rw [← he z hz]
  rfl

theorem factor_root_iff (p : ℕ) (q : ℝ[X]) (hq : q.natDegree≤p) (a : ℕ → ℝ)
    (he : ∀ z : ℂ, ‖z‖=1 → weight p a z=q.eval z.re) (t : ℝ) (ht : 0<t) :
    (amp p a).eval (t:ℂ)*(rev p a).eval (t:ℂ)= -(t:ℂ)^p ↔
    q.eval ((t+t⁻¹)/2) = -1 := by
  have h0 : (t:ℂ)≠0 := by exact_mod_cast ht.ne'
  have h := congrArg (fun f : ℂ[X] => f.eval (t:ℂ)) (laurentLift_factor p q hq a he)
  change (laurentLift p q).eval (t:ℂ)=(amp p a*rev p a).eval (t:ℂ) at h
  rw [laurentLift_eval p q hq _ h0,eval_mul] at h
  have hh : ((t:ℂ)+(t:ℂ)⁻¹)/2 = (((t+t⁻¹)/2:ℝ):ℂ) := by push_cast <;> ring
  rw [hh,eval₂_real] at h
  rw [← h]
  constructor
  · intro h'
    have hh' : (t:ℂ)^p*((q.eval ((t+t⁻¹)/2):ℝ):ℂ)=(t:ℂ)^p*(-1) := by simpa using h'
    have e := mul_left_cancel₀ (pow_ne_zero p h0) hh'
    exact_mod_cast e
  · intro h'
    rw [h']
    push_cast
    ring

def evenMajorant (r : ℕ) (c : ℝ) (q : ℝ[X]) : Prop :=
    q.natDegree≤r ∧ ∀ z : ℂ, ‖z‖=1 → 1≤dispersion c z*q.eval z.re

def majorantCost (c : ℝ) (q : ℝ[X]) : ℝ :=
    avg (fun z => dispersion c z*q.eval z.re-1)

def resOrd (c : ℝ) (q : ℝ[X]) : ℝ[X] := (C c-C 2*X)*q-1

theorem resOrd_eval (c : ℝ) (q : ℝ[X]) (x : ℝ) :
    (resOrd c q).eval x=(c-2*x)*q.eval x-1 := by simp [resOrd]

theorem resOrd_degree (r : ℕ) (c : ℝ) (q : ℝ[X]) (hq : q.natDegree≤r) :
    (resOrd c q).natDegree≤r+1 := by
  unfold resOrd
  apply (natDegree_sub_le _ _).trans
  apply max_le
  · apply natDegree_mul_le.trans
    have h : (C c-C (2:ℝ)*X).natDegree≤1 := by
      apply (natDegree_sub_le _ _).trans
      exact max_le (by simp) (natDegree_mul_le.trans (by simp))
    omega
  · simp

theorem even_majorant_lower (r : ℕ) (t : ℝ) (ht : 1<t) (g : ℝ[X])
    (hg : evenMajorant r (t+t⁻¹) g)
    (hf : ∃ a : ℕ → ℝ, ∀ z : ℂ, ‖z‖=1 → weight (r+1) a z=(resOrd (t+t⁻¹) g).eval z.re) :
    algebraicRelaxedValue (r+1) t≤majorantCost (t+t⁻¹) g := by
  obtain ⟨a,ha⟩ := hf
  obtain ⟨_,_,_,hmin⟩ := factor_relaxation_minimum (r+1) (by omega) t ht
  have hroot : (resOrd (t+t⁻¹) g).eval ((t+t⁻¹)/2) = -1 := by rw [resOrd_eval]; ring
  have he := (factor_root_iff (r+1) _ (resOrd_degree r _ _ hg.1) a ha t (by linarith)).2 hroot
  apply (hmin a he).trans_eq
  unfold majorantCost avg
  apply Real.circleAverage_congr_sphere
  intro z hz
  rw [ha z (norm_unit_of_mem z hz),resOrd_eval]
  rfl

end
end GaussianRange
#print axioms GaussianRange.poly_cos_repr
#print axioms GaussianRange.factor_root_iff
#print axioms GaussianRange.even_majorant_lower
