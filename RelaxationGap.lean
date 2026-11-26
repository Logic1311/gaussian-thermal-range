import RelaxationPower

namespace GaussianRange
open Finset Filter Topology
noncomputable section

theorem forward_sq_ge_last (p : ℕ) (t : ℝ) :
    t^p*t^p ≤ realSq (forwardPower p t) := by
  unfold realSq forwardPower
  rw [← pow_two]
  exact Finset.single_le_sum (f := fun i : Fin (p+1) => (t^i.val)^2)
    (fun i _ => sq_nonneg _) (Finset.mem_univ (Fin.last p))

theorem forward_sq_geometric (p : ℕ) (t : ℝ) :
    (t^2-1)*realSq (forwardPower p t) = t^(2*(p+1))-1 := by
  unfold realSq
  simp only [forwardPower]
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => (t^j)^2) (p+1)]
  induction p with
  | zero => simp
  | succ p ih =>
    rw [Finset.sum_range_succ,mul_add,ih]
    rw [show 2*(p+1+1)=2*(p+1)+2 by omega,pow_add]
    rw [show t^(2*(p+1))=(t^(p+1))^2 by rw [mul_comm,pow_mul]]
    ring

theorem relaxed_denominator_pos (p : ℕ) (hp : 0<p) (t : ℝ) (ht : 1<t) :
    0 < realSq (forwardPower p t)-((p:ℝ)+1)*t^p := by
  have h := power_diff_pos p hp t ht
  rw [realSq_diff,← power_norm_eq p t,power_dot] at h
  linarith

theorem algebraic_relaxed_pos (p : ℕ) (hp : 0<p) (t : ℝ) (ht : 1<t) :
    0 < algebraicRelaxedValue p t := by
  unfold algebraicRelaxedValue
  exact div_pos (by positivity) (relaxed_denominator_pos p hp t ht)

theorem relaxed_scaled_bounds (p : ℕ) (hp : 0<p) (t : ℝ) (ht : 1<t)
    (hlarge : 2*((p:ℝ)+1)≤t^p) :
    2*(t^2-1)/t^2 ≤ algebraicRelaxedValue p t*t^p ∧
    algebraicRelaxedValue p t*t^p ≤ 4 := by
  let S := realSq (forwardPower p t)
  let d := S-((p:ℝ)+1)*t^p
  have ht0 : 0<t := by linarith
  have ht2 : 0<t^2-1 := by nlinarith
  have hp0 : 0<t^p := pow_pos ht0 _
  have hd : 0<d := relaxed_denominator_pos p hp t ht
  have hs := forward_sq_ge_last p t
  change t^p*t^p≤S at hs
  have hg := forward_sq_geometric p t
  change (t^2-1)*S=t^(2*(p+1))-1 at hg
  rw [show 2*(p+1)=p+p+2 by omega,pow_add,pow_add] at hg
  have hl : t^p*t^p/2≤d := by
    have h := mul_le_mul_of_nonneg_right hlarge hp0.le
    dsimp [d]
    nlinarith
  have hu : (t^2-1)*d≤t^p*t^p*t^2 := by
    have h : d≤S := by dsimp [d]; exact sub_le_self _ (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left h ht2.le]
  change 2*(t^2-1)/t^2 ≤ (2*t^p/d)*t^p ∧ (2*t^p/d)*t^p≤4
  rw [div_mul_eq_mul_div]
  constructor
  · apply (div_le_div_iff₀ (sq_pos_of_pos ht0) hd).2
    nlinarith
  · apply (div_le_iff₀ hd).2
    nlinarith

theorem powers_eventually_large (t : ℝ) (ht : 1<t) :
    ∃ P : ℕ, 0<P ∧ ∀ p : ℕ, P≤p → 2*((p:ℝ)+1)≤t^p := by
  have h := (tendsto_pow_const_div_const_pow_of_one_lt 1 ht).eventually
    (gt_mem_nhds (show (0:ℝ)<1/4 by norm_num))
  obtain ⟨P,hP⟩ := eventually_atTop.1 h
  refine ⟨max P 1,by omega,?_⟩
  intro p hp
  have he := hP p (by omega)
  change (p:ℝ)^1/t^p < 1/4 at he
  rw [pow_one,div_lt_iff₀ (pow_pos (by linarith : 0<t) _)] at he
  have hp1 : (1:ℝ)≤p := by exact_mod_cast (show 1≤p by omega)
  linarith

/-- The formal factor minimum has exponential scale at fixed t>1.
The physical optimum is the actual infimum from Integrated.lean. -/
theorem factor_gap_theta (m t : ℝ) (hm : 0<m) (ht : 1<t) :
    ∃ A B : ℝ, 0<A ∧ 0<B ∧ ∃ R : ℕ, 0<R ∧
      ∀ r : ℕ, R≤r →
      A*t^(r+1)/(r:ℝ)^2 ≤ optimalEntropy r m/algebraicRelaxedValue (r+1) t ∧
      optimalEntropy r m/algebraicRelaxedValue (r+1) t ≤ B*t^(r+1)/(r:ℝ)^2 := by
  obtain ⟨C₁,C₂,hC₁,hC₂,R,hR,hb⟩ := optimalEntropy_theta m hm
  obtain ⟨P,hP,hp⟩ := powers_eventually_large t ht
  let K := 2*(t^2-1)/t^2
  have ht0 : 0<t := by linarith
  have hK : 0<K := by dsimp [K]; exact div_pos (by nlinarith) (sq_pos_of_pos ht0)
  refine ⟨C₁/4,C₂/K,by positivity,by positivity,max R P,by omega,?_⟩
  intro r hr
  have hrr : 0<r := by omega
  have hr2 : 0<(r:ℝ)^2 := sq_pos_of_pos (by exact_mod_cast hrr)
  have hpow : 0<t^(r+1) := pow_pos ht0 _
  have hL : 0<algebraicRelaxedValue (r+1) t := algebraic_relaxed_pos _ (by omega) t ht
  obtain ⟨_,hlo,hhi⟩ := hb r (by omega)
  obtain ⟨hslo,hshi⟩ := relaxed_scaled_bounds (r+1) (by omega) t ht (hp _ (by omega))
  change K≤algebraicRelaxedValue (r+1) t*t^(r+1) at hslo
  constructor
  · apply (le_div_iff₀ hL).2
    apply le_trans _ hlo
    rw [div_mul_eq_mul_div]
    apply (div_le_div_iff_of_pos_right hr2).2
    nlinarith [mul_le_mul_of_nonneg_left hshi (show 0≤C₁/4 by positivity)]
  · apply (div_le_iff₀ hL).2
    apply le_trans hhi
    rw [div_mul_eq_mul_div]
    apply (div_le_div_iff_of_pos_right hr2).2
    have h := mul_le_mul_of_nonneg_left hslo (show 0≤C₂/K by positivity)
    have he : C₂/K*K=C₂ := by field_simp
    nlinarith

end
end GaussianRange
#print axioms GaussianRange.forward_sq_geometric
#print axioms GaussianRange.relaxed_scaled_bounds
#print axioms GaussianRange.factor_gap_theta
