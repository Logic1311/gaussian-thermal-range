import Integrated
import RelaxationAlgebra

namespace GaussianRange
open Finset Polynomial
noncomputable section

def forwardPower (p : ℕ) (t : ℝ) (i : Fin (p+1)) : ℝ := t^i.val

def reversePower (p : ℕ) (t : ℝ) (i : Fin (p+1)) : ℝ := t^(p-i.val)

theorem power_norm_eq (p : ℕ) (t : ℝ) : realSq (forwardPower p t) = realSq (reversePower p t) := by
  have h (i : Fin (p+1)) : reversePower p t i=forwardPower p t i.rev := by
    unfold reversePower forwardPower
    congr 1
    simp [Fin.val_rev]
  unfold realSq
  simp_rw [h]
  exact (Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin (p+1))) (fun i => (forwardPower p t i)^2)).symm

theorem power_diff_pos (p : ℕ) (hp : 0<p) (t : ℝ) (ht : 1<t) :
    0<realSq (fun i => forwardPower p t i-reversePower p t i) := by
  unfold realSq
  apply Finset.sum_pos' (fun i _ => sq_nonneg _)
  refine ⟨0,mem_univ _,?_⟩
  have h : 1<t^p := one_lt_pow₀ ht hp.ne'
  simp only [forwardPower,reversePower,Fin.val_zero,pow_zero,Nat.sub_zero]
  exact sq_pos_of_ne_zero (sub_ne_zero.mpr (ne_of_lt h))

theorem power_dot (p : ℕ) (t : ℝ) :
    realDot (forwardPower p t) (reversePower p t) = ((p:ℝ)+1)*t^p := by
  unfold realDot
  have h (i : Fin (p+1)) : forwardPower p t i*reversePower p t i=t^p := by
    unfold forwardPower reversePower
    rw [← pow_add, Nat.add_sub_of_le (by omega : i.val≤p)]
  simp_rw [h]
  simp

def algebraicRelaxedValue (p : ℕ) (t : ℝ) : ℝ :=
  2*t^p/(realSq (forwardPower p t)-((p:ℝ)+1)*t^p)

theorem power_relaxation_minimum (p : ℕ) (hp : 0<p) (t : ℝ) (ht : 1<t) :
    ∃ a : Fin (p+1) → ℝ, realDot a (forwardPower p t)*realDot a (reversePower p t)= -t^p ∧
      realSq a=algebraicRelaxedValue p t ∧
      ∀ b : Fin (p+1) → ℝ, realDot b (forwardPower p t)*realDot b (reversePower p t)= -t^p →
        algebraicRelaxedValue p t ≤ realSq b := by
  have hq := power_diff_pos p hp t ht
  have he : realSq (fun i => forwardPower p t i-reversePower p t i) =
    2*(realSq (forwardPower p t)-((p:ℝ)+1)*t^p) := by
    rw [realSq_diff,← power_norm_eq p t,power_dot]
    ring
  have hval : 4*t^p/realSq (fun i => forwardPower p t i-reversePower p t i)=algebraicRelaxedValue p t := by
    rw [he,algebraicRelaxedValue]
    have hn : realSq (forwardPower p t)-((p:ℝ)+1)*t^p≠0 := by linarith
    field_simp [hn]
    <;> ring
  obtain ⟨a,ha,hb,hc⟩ := rankTwo_exact_minimum (forwardPower p t) (reversePower p t) (t^p)
    (pow_pos (by linarith) p) (power_norm_eq p t) hq
  rw [hval] at hb hc
  exact ⟨a,ha,hb,hc⟩

theorem amp_real_dot (p : ℕ) (a : ℕ → ℝ) (t : ℝ) :
    (amp p a).eval (t:ℂ) = (realDot (fun i : Fin (p+1) => a i.val) (forwardPower p t):ℂ) := by
  rw [amp_eval,realDot]
  simp only [forwardPower]
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => a j*t^j) (p+1)]
  simp [Complex.ofReal_sum]

theorem rev_real_dot (p : ℕ) (a : ℕ → ℝ) (t : ℝ) :
    (rev p a).eval (t:ℂ) = (realDot (fun i : Fin (p+1) => a i.val) (reversePower p t):ℂ) := by
  rw [rev_eval,realDot]
  simp only [reversePower]
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => a j*t^(p-j)) (p+1)]
  simp [Complex.ofReal_sum]

theorem factor_relaxation_minimum (p : ℕ) (hp : 0<p) (t : ℝ) (ht : 1<t) :
    ∃ a : ℕ → ℝ, (amp p a).eval (t:ℂ)*(rev p a).eval (t:ℂ)= -(t:ℂ)^p ∧
      avg (weight p a)=algebraicRelaxedValue p t ∧
      ∀ b : ℕ → ℝ, (amp p b).eval (t:ℂ)*(rev p b).eval (t:ℂ)= -(t:ℂ)^p →
        algebraicRelaxedValue p t ≤ avg (weight p b) := by
  obtain ⟨a,ha,hb,hc⟩ := power_relaxation_minimum p hp t ht
  let aa : ℕ → ℝ := fun j => if h : j<p+1 then a ⟨j,h⟩ else 0
  have he (i : Fin (p+1)) : aa i.val=a i := by
    dsimp [aa]
    rw [if_pos i.isLt]
  refine ⟨aa,?_,?_,?_⟩
  · rw [amp_real_dot,rev_real_dot]
    simp only [he]
    exact_mod_cast ha
  · rw [avg_weight_parseval,← Fin.sum_univ_eq_sum_range (fun j : ℕ => (aa j)^2) (p+1)]
    simp_rw [he]
    exact hb
  · intro b h
    rw [amp_real_dot,rev_real_dot] at h
    have h' : realDot (fun i : Fin (p+1) => b i.val) (forwardPower p t)*
      realDot (fun i : Fin (p+1) => b i.val) (reversePower p t)= -t^p := by exact_mod_cast h
    have hh := hc _ h'
    rw [avg_weight_parseval]
    rw [realSq,Fin.sum_univ_eq_sum_range (fun j : ℕ => (b j)^2) (p+1)] at hh
    exact hh

end
end GaussianRange
#print axioms GaussianRange.power_relaxation_minimum
#print axioms GaussianRange.factor_relaxation_minimum