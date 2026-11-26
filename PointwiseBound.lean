import PointwiseBarrier

namespace GaussianRange
open Finset Polynomial
noncomputable section

def momentBudget (r : ℕ) : ℝ := ∑ j : Fin (r+1), (j.val:ℝ)^2

theorem momentBudget_ge_one (r : ℕ) (hr : 0<r) : 1≤momentBudget r := by
  let j : Fin (r+1) := ⟨1,by omega⟩
  have h := Finset.single_le_sum (f := fun j : Fin (r+1) => (j.val:ℝ)^2)
    (fun j _ => sq_nonneg _) (Finset.mem_univ j)
  simpa [j,momentBudget] using h

theorem moment_energy_bound (r : ℕ) (a : ℕ → ℝ) (z : ℂ) (hz : ‖z‖=1) :
    ‖(momentAmp r a).eval z‖^2 ≤ momentBudget r * (∑ j : Fin (r+1), (a j)^2) := by
  let u : Fin (r+1) → ℝ := fun j => j.val
  let v : Fin (r+1) → ℝ := fun j => a j*(z^j.val).re
  let w : Fin (r+1) → ℝ := fun j => a j*(z^j.val).im
  have h₁ := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ u v
  have h₂ := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ u w
  have h₃ : (∑ j, v j^2)+(∑ j,w j^2) = ∑ j : Fin (r+1), (a j)^2 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    have hh := unit_re_sq_im_sq (z^j.val) (by rw [norm_pow,hz,one_pow])
    dsimp [v,w]
    linear_combination (a j)^2*hh
  change weight r (fun j => (j:ℝ)*a j) z ≤ _
  rw [weight_fin]
  change (∑ j : Fin (r+1), ((j.val:ℝ)*a j)*(z^j.val).re)^2+
    (∑ j : Fin (r+1), ((j.val:ℝ)*a j)*(z^j.val).im)^2 ≤ _
  simp_rw [mul_assoc]
  change (∑ j, u j*v j)^2+(∑ j, u j*w j)^2 ≤ momentBudget r * _
  calc
    _ ≤ (∑ j,u j^2)*(∑ j,v j^2)+(∑ j,u j^2)*(∑ j,w j^2) := add_le_add h₁ h₂
    _ = _ := by rw [← mul_add,h₃]; rfl

theorem lag_zero_sq (r : ℕ) (a : ℕ → ℝ) :
    lag r 0 a = ∑ j : Fin (r+1), (a j)^2 := by
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => (a j)^2) (r+1)]
  unfold lag
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j≤r := by have := Finset.mem_range.mp hj; omega
  simp [hj',pow_two]

theorem bath_moment_energy_bound (b : BathFamily) (r : ℕ) (hr : 0<r) (m : ℝ)
    (hb : b.admissible r m) (z : ℂ) (hz : ‖z‖=1) :
    (∑ v, b.temp v * ‖(momentAmp r (b.coeff v)).eval z‖^2) ≤ (m+2)*momentBudget r := by
  have h := (physical_lags r hr b.coeff b.temp (m+2) hb.2.1 hb.2.2).1
  simp_rw [lag_zero_sq] at h
  calc
    _ ≤ ∑ v, b.temp v * (momentBudget r*(∑ j : Fin (r+1),(b.coeff v j)^2)) := by
      apply Finset.sum_le_sum
      intro v _
      exact mul_le_mul_of_nonneg_left (moment_energy_bound r (b.coeff v) z hz) (hb.1 v).le
    _ = _ := by
      simp_rw [show ∀ a b c : ℝ, a*(b*c)=b*(a*c) by intros; ring,← Finset.mul_sum]
      rw [h,mul_comm]

theorem two_coordinate_variational (T d l pr pi er ei : ℝ) (hT : 0<T) :
    2*l*(T-d)*(ei*pr-er*pi) ≤
      (T-d)^2*(pr^2+pi^2)/T+l^2*T*(er^2+ei^2) := by
  -- Multiplying by the positive temperature gives an exact sum-of-squares certificate.
  have h : 2*l*(T-d)*(ei*pr-er*pi)*T ≤
      (T-d)^2*(pr^2+pi^2)+l^2*T*(er^2+ei^2)*T := by
    nlinarith [sq_nonneg ((T-d)*pr-T*l*ei),sq_nonneg ((T-d)*pi+T*l*er)]
  have he : (T-d)^2*(pr^2+pi^2)/T+l^2*T*(er^2+ei^2) =
      ((T-d)^2*(pr^2+pi^2)+l^2*T*(er^2+ei^2)*T)/T := by field_simp <;> ring
  rw [he]
  exact (le_div_iff₀ hT).2 h

theorem bath_angular_variational (b : BathFamily) (r : ℕ) (hr : 0<r) (m : ℝ) (hm : 0<m)
    (hb : b.admissible r m) (z : ℂ) (hz : ‖z‖=1) (l : ℝ) :
    -2*l*z.im ≤ dispersion (m+2) z * sigma r b.coeff b.temp (m+2) z+
      l^2*((m+2)*momentBudget r) := by
  let d := dispersion (m+2) z
  have hd : 0<d := by
    have h := (unit_re_mem z hz).2
    dsimp [d,dispersion]
    linarith
  obtain ⟨h0,h1⟩ := angular_normalizations b r hr m hb z hz
  have hx : (∑ v, (b.temp v-d)*angularDot r (b.coeff v) z)=-z.im := by
    simp_rw [sub_mul,Finset.sum_sub_distrib,← Finset.mul_sum,h0,h1]
    ring
  have hH : (∑ v, (b.temp v-d)^2*weight r (b.coeff v) z/b.temp v)=
      d*sigma r b.coeff b.temp (m+2) z := by
    rw [b.sigma_identity r m hm hb z hz,mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    change _ = d*(weight r (b.coeff v) z*(b.temp v-d)^2/(b.temp v*d))
    field_simp [hd.ne',(hb.1 v).ne']
    <;> ring
  have hnorm (x : ℂ) : x.re^2+x.im^2=‖x‖^2 := by
    rw [← Complex.normSq_eq_norm_sq,Complex.normSq_apply]
    ring
  have hpoint (v : b.ι) : 2*l*((b.temp v-d)*angularDot r (b.coeff v) z) ≤
      (b.temp v-d)^2*weight r (b.coeff v) z/b.temp v+
      l^2*(b.temp v*‖(momentAmp r (b.coeff v)).eval z‖^2) := by
    have hh := two_coordinate_variational (b.temp v) d l
      ((amp r (b.coeff v)).eval z).re ((amp r (b.coeff v)).eval z).im
      ((momentAmp r (b.coeff v)).eval z).re ((momentAmp r (b.coeff v)).eval z).im (hb.1 v)
    rw [hnorm,hnorm] at hh
    rw [angularDot_formula]
    unfold weight
    convert hh using 1 <;> ring
  have h := Finset.sum_le_sum (s := Finset.univ) (fun v _ => hpoint v)
  rw [← Finset.mul_sum, hx, Finset.sum_add_distrib,← Finset.mul_sum,hH] at h
  have hJ := mul_le_mul_of_nonneg_left (bath_moment_energy_bound b r hr m hb z hz) (sq_nonneg l)
  change -2*l*z.im ≤ d*sigma r b.coeff b.temp (m+2) z+l^2*((m+2)*momentBudget r)
  linarith

/-- A uniform physical barrier at every continuous frequency. -/
theorem physical_pointwise_barrier (b : BathFamily) (r : ℕ) (hr : 0<r) (m : ℝ) (hm : 0<m)
    (hb : b.admissible r m) (z : ℂ) (hz : ‖z‖=1) :
    z.im^2/((m+2)*momentBudget r*dispersion (m+2) z) ≤ sigma r b.coeff b.temp (m+2) z := by
  let K := (m+2)*momentBudget r
  have hK : 0<K := mul_pos (by linarith) (lt_of_lt_of_le zero_lt_one (momentBudget_ge_one r hr))
  let d := dispersion (m+2) z
  have hd : 0<d := by
    have h := (unit_re_mem z hz).2
    dsimp [d,dispersion]
    linarith
  have h := bath_angular_variational b r hr m hm hb z hz (-z.im/K)
  change -2*(-z.im/K)*z.im ≤ d*sigma r b.coeff b.temp (m+2) z+(-z.im/K)^2*K at h
  have he : -2*(-z.im/K)*z.im-(-z.im/K)^2*K=z.im^2/K := by field_simp; ring
  have h' : z.im^2/K ≤ d*sigma r b.coeff b.temp (m+2) z := by linarith
  change z.im^2/(K*d) ≤ _
  rw [← div_div]
  exact (div_le_iff₀ hd).2 (by simpa [mul_comm] using h')

end
end GaussianRange
#print axioms GaussianRange.moment_energy_bound
#print axioms GaussianRange.physical_pointwise_barrier