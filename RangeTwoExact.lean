import RangeTwoAlgebra
import RangeTwoCoordinates

namespace GaussianRange
open Finset
open scoped RealInnerProductSpace Matrix
noncomputable section
set_option maxHeartbeats 1000000

def r2vec (a b d : ℝ) : SDPSpace 3 :=
  WithLp.toLp 2 (fun i => if i.val=0 then a else if i.val=1 then b else d)

theorem r2vec_inner (M : R2Mat) (a b d : ℝ) :
    ⟪r2vec a b d,r2op M (r2vec a b d)⟫ =
      a*(M 0 0*a+M 0 1*b+M 0 2*d)+
      b*(M 1 0*a+M 1 1*b+M 1 2*d)+
      d*(M 2 0*a+M 2 1*b+M 2 2*d) := by
  rw [r2op_inner]
  norm_num [r2vec,Fin.sum_univ_three,Fin.val_natCast,WithLp.ofLp_toLp]
  <;> simp (disch := decide)
  <;> ring

theorem r2_traceQ_nonneg (c : ℝ) (hc : 2<c) (W : R2Mat)
    (hW : ∀ y,0≤⟪y,r2op W y⟫) : 0≤c*r2trace0 W-r2trace1 W := by
  have h0 := hW (r2vec 1 0 0)
  have h1 := hW (r2vec 0 1 0)
  have h2 := hW (r2vec 0 0 1)
  have h01 := hW (r2vec 1 (-1) 0)
  have h12 := hW (r2vec 0 1 (-1))
  rw [r2vec_inner] at h0 h1 h2 h01 h12
  norm_num at h0 h1 h2 h01 h12
  have a := mul_nonneg (show 0≤c-1 by linarith) h0
  have b := mul_nonneg (show 0≤c-2 by linarith) h1
  have d := mul_nonneg (show 0≤c-1 by linarith) h2
  unfold r2trace0 r2trace1
  linarith only [a,b,d,h01,h12]

theorem r2op_add_apply (A B : R2Mat) (x : SDPSpace 3) :
    r2op (A+B) x=r2op A x+r2op B x := by
  unfold r2op
  rw [map_add,LinearMap.add_apply]

theorem r2op_sub_apply (A B : R2Mat) (x : SDPSpace 3) :
    r2op (A-B) x=r2op A x-r2op B x := by
  unfold r2op
  rw [map_sub,LinearMap.sub_apply]

theorem r2_symmetry_transpose (A : R2Mat) (hA : (r2op A).IsSymmetric) : Aᵀ=A := by
  ext i j
  have h := hA (sdpStd 3 i) (sdpStd 3 j)
  rw [r2op_transpose] at h
  rw [r2op_inner,r2op_inner] at h
  simpa [sdpStd,EuclideanSpace.basisFun_apply,Pi.single_apply,Matrix.transpose_apply] using h

def r2Residual (G H J K : R2Mat) : R2Mat :=
  J-Kᵀ*G-G*K+Kᵀ*H*K

theorem r2_residual_nonneg (G H J K : R2Mat) {m : ℝ}
    (hp : SDPFeasible (⟨r2op G,r2op H,r2op J⟩ : SDPMoments 2) m)
    (y : SDPSpace 3) : 0≤⟪y,r2op (r2Residual G H J K) y⟫ := by
  have h := hp.block (-(r2op K y)) y
  change 0≤⟪-(r2op K y),r2op H (-(r2op K y))⟫+
    2*⟪-(r2op K y),r2op G y⟫+⟪y,r2op J y⟫ at h
  simp only [map_neg,inner_neg_left,inner_neg_right,neg_neg] at h
  have hG : ⟪r2op K y,r2op G y⟫=⟪y,r2op G (r2op K y)⟫ := by
    rw [← real_inner_comm, hp.gs]
  unfold r2Residual
  simp only [r2op_add_apply,r2op_sub_apply,r2op_mul,inner_add_right,inner_sub_right]
  rw [← r2op_transpose,← r2op_transpose,← hG]
  linarith only [h]

theorem r2_traceQ (c : ℝ) (M : R2Mat) :
    Matrix.trace (range2Q c*M)=c*r2trace0 M-r2trace1 M := by
  norm_num [Matrix.trace,Matrix.diag,range2Q,matrix3,Matrix.mul_apply,Fin.sum_univ_three,Fin.val_natCast,r2trace0,r2trace1]
  <;> simp (disch := decide) <;> ring

theorem r2_trace_toeplitz (a b d : ℝ) (M : R2Mat) :
    Matrix.trace (toeplitz3 a b d*M)=a*r2trace0 M+b*r2trace1 M+d*r2trace2 M := by
  norm_num [Matrix.trace,Matrix.diag,toeplitz3,matrix3,Matrix.mul_apply,Fin.sum_univ_three,Fin.val_natCast,r2trace0,r2trace1,r2trace2]
  <;> simp (disch := decide) <;> ring

theorem r2_trace_residual (c : ℝ) (G H J K : R2Mat) :
    Matrix.trace (range2Q c*r2Residual G H J K)=
    Matrix.trace (range2Q c*J)-
      Matrix.trace ((K*range2Q c+range2Q c*Kᵀ)*G)+
      Matrix.trace ((K*range2Q c*Kᵀ)*H) := by
  unfold r2Residual
  simp only [Matrix.mul_add,Matrix.mul_sub,Matrix.add_mul,Matrix.trace_add,Matrix.trace_sub,Matrix.mul_assoc]
  have hG : Matrix.trace (range2Q c*(G*K))=Matrix.trace (K*(range2Q c*G)) := by
    simpa only [Matrix.mul_assoc] using Matrix.trace_mul_cycle (range2Q c) G K
  have hH : Matrix.trace (range2Q c*(Kᵀ*(H*K)))=Matrix.trace (K*(range2Q c*(Kᵀ*H))) := by
    simpa only [Matrix.mul_assoc] using Matrix.trace_mul_cycle (range2Q c*Kᵀ) H K
  rw [hG,hH]
  ring

theorem range2G_symm (c e : ℝ) : (range2G c e)ᵀ=range2G c e := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [range2G,matrix3,Matrix.transpose_apply,Fin.val_natCast] <;> simp (disch := decide)

theorem range2H_symm (c e : ℝ) : (range2H c e)ᵀ=range2H c e := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [range2H,matrix3,Matrix.transpose_apply,Fin.val_natCast] <;> simp (disch := decide)

theorem range2J_form (c e : ℝ) (hD : range2D c e≠0) (hB : range2B c e≠0) :
    range2J c e=(range2K c e)ᵀ*range2H c e*range2K c e := by
  have h := congrArg Matrix.transpose (range2_HK c e hD hB)
  rw [Matrix.transpose_mul,range2H_symm,range2G_symm] at h
  unfold range2J
  rw [h]

theorem r2_nonzero_coord (x : SDPSpace 3) (hx : x≠0) :
    x 0≠0 ∨ x 1≠0 ∨ x 2≠0 := by
  by_contra! h
  apply hx
  ext i
  fin_cases i
  · exact h.1
  · exact h.2.1
  · exact h.2.2

theorem r2_diag_positive (a b d : ℝ) (ha : 0<a) (hb : 0<b) (hd : 0<d) :
    sdpPositive (r2op (matrix3 a 0 0 0 b 0 0 0 d)) := by
  intro x hx
  rw [r2op_inner]
  norm_num [matrix3,Fin.sum_univ_three,Fin.val_natCast]
  simp (disch := decide)
  have h0 := mul_nonneg ha.le (sq_nonneg (x 0))
  have h1 := mul_nonneg hb.le (sq_nonneg (x 1))
  have h2 := mul_nonneg hd.le (sq_nonneg (x 2))
  rcases r2_nonzero_coord x hx with h|h|h
  · nlinarith only [mul_pos ha (sq_pos_of_ne_zero h),h1,h2]
  · nlinarith only [h0,mul_pos hb (sq_pos_of_ne_zero h),h2]
  · nlinarith only [h0,h1,mul_pos hd (sq_pos_of_ne_zero h)]

theorem r2_H_positive (c e : ℝ) (hc : 2<c) (hl : c/4≤e) (hu : e≤(3*c-2)/8) :
    sdpPositive (r2op (range2H c e)) := by
  intro x hx
  rw [r2op_inner]
  norm_num [range2H,matrix3,Fin.sum_univ_three,Fin.val_natCast]
  simp (disch := decide)
  have he : 0<e-1/2 := by linarith
  have hq : 0<c-2*e-1 := by linarith
  have h0 := mul_nonneg he.le (sq_nonneg (x 0))
  have h1 := mul_nonneg hq.le (sq_nonneg (x 1))
  have h2 := mul_nonneg he.le (sq_nonneg (x 2))
  have h01 := sq_nonneg (x 0-x 1)
  have h12 := sq_nonneg (x 1-x 2)
  rcases r2_nonzero_coord x hx with h|h|h
  · nlinarith only [mul_pos he (sq_pos_of_ne_zero h),h1,h2,h01,h12]
  · nlinarith only [h0,mul_pos hq (sq_pos_of_ne_zero h),h2,h01,h12]
  · nlinarith only [h0,h1,mul_pos he (sq_pos_of_ne_zero h),h01,h12]

def range2Mom (c e : ℝ) : SDPMoments 2 :=
  ⟨r2op (range2G c e),r2op (range2H c e),r2op (range2J c e)⟩

theorem range2_lags (c e : ℝ) :
    r2trace0 (range2G c e)=1 ∧ r2trace1 (range2G c e)=0 ∧ r2trace2 (range2G c e)=0 ∧
    r2trace0 (range2H c e)=c ∧ r2trace1 (range2H c e)= -2 ∧ r2trace2 (range2H c e)=0 := by
  norm_num [r2trace0,r2trace1,r2trace2,range2G,range2H,matrix3,Fin.val_natCast]
  constructor <;> ring

theorem range2_feasible (m e : ℝ) (hm : 0<m) (hr : Range2Root (m+2) e) :
    SDPFeasible (range2Mom (m+2) e) m ∧
    sdpPositive (range2Mom (m+2) e).G ∧ sdpPositive (range2Mom (m+2) e).H := by
  let c := m+2
  obtain ⟨hl,hu,hN⟩ := hr
  have hc : 2<c := by dsimp [c]; linarith
  obtain ⟨he,hq,hD,hB,hL,ha,hb⟩ := range2_params_pos c e hc hl hu
  have hG : sdpPositive (r2op (range2G c e)) := r2_diag_positive _ _ _ ha hb ha
  have hH := r2_H_positive c e hc hl hu
  have hHK := range2_HK c e hD.ne' hB.ne'
  have hJ := range2J_form c e hD.ne' hB.ne'
  obtain ⟨g0,g1,g2,h0,h1,h2⟩ := range2_lags c e
  refine ⟨⟨r2op_symm _ (range2G_symm c e),r2op_symm _ (range2H_symm c e),r2op_symm _ ?_,?_,?_,?_,?_⟩,hG,hH⟩
  · change (range2J c e)ᵀ=range2J c e
    rw [hJ,Matrix.transpose_mul,Matrix.transpose_mul,Matrix.transpose_transpose,range2H_symm,Matrix.mul_assoc]
  · intro x
    by_cases hx : x=0
    · simp [hx]
    · exact (hG x hx).le
  · intro x y
    change 0≤⟪x,r2op (range2H c e) x⟫+2*⟪x,r2op (range2G c e) y⟫+
      ⟪y,r2op (range2J c e) y⟫
    rw [← hHK,hJ,r2op_mul,r2op_mul,r2op_mul,← r2op_transpose]
    let z := r2op (range2K c e) y
    have heq : ⟪z,r2op (range2H c e) x⟫=⟪x,r2op (range2H c e) z⟫ := by
      rw [← real_inner_comm, (r2op_symm _ (range2H_symm c e))]
    have hn : 0≤⟪x+z,r2op (range2H c e) (x+z)⟫ := by
      by_cases hz : x+z=0
      · simp [hz]
      · exact (hH _ hz).le
    rw [map_add,inner_add_left,inner_add_right,inner_add_right,heq] at hn
    change 0≤⟪x,r2op (range2H c e) x⟫+2*⟪x,r2op (range2H c e) z⟫+
      ⟪z,r2op (range2H c e) z⟫
    linarith only [hn]
  · intro z hz
    change sdpSpectrum 2 (r2op (range2G c e)) z=1
    rw [r2_spectrum _ _ hz,g0,g1,g2]
    ring
  · intro z hz
    change sdpSpectrum 2 (r2op (range2H c e)) z=dispersion c z
    rw [r2_spectrum _ _ hz,h0,h1,h2]
    unfold dispersion
    ring

theorem range2_cost_value (m e : ℝ) (hm : 0<m) (hr : Range2Root (m+2) e) :
    sdpCost (range2Mom (m+2) e) m=range2Value (m+2) e := by
  let c := m+2
  obtain ⟨hl,hu,hN⟩ := hr
  obtain ⟨he,hq,hD,hB,hL,ha,hb⟩ := range2_params_pos c e (by dsimp [c]; linarith) hl hu
  change avg (fun z => dispersion c z*sdpSpectrum 2 (r2op (range2J c e)) z-1)=range2Value c e
  rw [r2_avg_spectrum]
  norm_num [r2trace0,r2trace1,range2J,range2G,range2K,range2KNum,range2Value,range2A,
    range2L,matrix3,Matrix.mul_apply,Matrix.smul_apply,Fin.sum_univ_three,Fin.val_natCast]
  simp (disch := decide)
  have hd : -(2*c*e)+4*e^2+1= -2*range2D c e := by unfold range2D; ring
  rw [hd]
  field_simp [hD.ne',hB.ne',he.ne']
  <;> simp only [range2D,range2B] <;> ring

theorem range2_sdp_global (m e : ℝ) (hm : 0<m) (hr : Range2Root (m+2) e)
    (p : SDPMoments 2) (hp : SDPFeasible p m) :
    sdpCost (range2Mom (m+2) e) m≤sdpCost p m := by
  let c := m+2
  obtain ⟨hl,hu,hN⟩ := hr
  have hc : 2<c := by dsimp [c]; linarith
  obtain ⟨he,hq,hD,hB,hL,ha,hb⟩ := range2_params_pos c e hc hl hu
  obtain ⟨G,hG⟩ := r2_op_surj p.G
  obtain ⟨H,hH⟩ := r2_op_surj p.H
  obtain ⟨J,hJ⟩ := r2_op_surj p.J
  have hP : p=(⟨r2op G,r2op H,r2op J⟩ : SDPMoments 2) := by
    cases p
    simp_all
  subst p
  obtain ⟨g0,g1,g2⟩ := r2_lag_from_spectrum G 1 0 (fun z hz => by simpa using hp.normalization z hz)
  obtain ⟨h0,h1,h2⟩ := r2_lag_from_spectrum H c (-2) (fun z hz => by simpa [dispersion,c] using hp.weighted z hz)
  let K := range2K c e
  let U := range2U c e
  let V := range2V c e
  have hW := r2_traceQ_nonneg c hc (r2Residual G H J K) (r2_residual_nonneg G H J K hp)
  rw [← r2_traceQ] at hW
  rw [r2_trace_residual] at hW
  change 0≤Matrix.trace (range2Q c*J)-Matrix.trace (U*G)+Matrix.trace (V*H) at hW
  have hU := range2_U_toeplitz c e
  have hV := range2_V_toeplitz c e hN
  have htU : Matrix.trace (U*G)=U 0 0 := by
    change Matrix.trace (range2U c e*G)=range2U c e 0 0
    conv_lhs => rw [hU]
    rw [r2_trace_toeplitz,g0,g1,g2]
    ring
  have htV : Matrix.trace (V*H)=c*V 0 0-2*V 0 1 := by
    change Matrix.trace (range2V c e*H)=c*range2V c e 0 0-2*range2V c e 0 1
    conv_lhs => rw [hV]
    rw [r2_trace_toeplitz,h0,h1,h2]
    ring
  obtain ⟨gg0,gg1,gg2,hh0,hh1,hh2⟩ := range2_lags c e
  have htU0 : Matrix.trace (U*range2G c e)=U 0 0 := by
    change Matrix.trace (range2U c e*range2G c e)=range2U c e 0 0
    conv_lhs => rw [hU]
    rw [r2_trace_toeplitz,gg0,gg1,gg2]
    ring
  have htV0 : Matrix.trace (V*range2H c e)=c*V 0 0-2*V 0 1 := by
    change Matrix.trace (range2V c e*range2H c e)=c*range2V c e 0 0-2*range2V c e 0 1
    conv_lhs => rw [hV]
    rw [r2_trace_toeplitz,hh0,hh1,hh2]
    ring
  have hHK : range2H c e*K=range2G c e := range2_HK c e hD.ne' hB.ne'
  have hJ0 : range2J c e=Kᵀ*range2H c e*K := range2J_form c e hD.ne' hB.ne'
  have hzero : r2Residual (range2G c e) (range2H c e) (range2J c e) K=0 := by
    have hKT := congrArg Matrix.transpose hHK
    rw [Matrix.transpose_mul,range2G_symm,range2H_symm] at hKT
    have hkG : Kᵀ*range2G c e=range2G c e*K := by
      calc
        _ = Kᵀ*(range2H c e*K) := congrArg (fun M : R2Mat => Kᵀ*M) hHK.symm
        _ = (Kᵀ*range2H c e)*K := (Matrix.mul_assoc _ _ _).symm
        _ = _ := by rw [hKT]
    unfold r2Residual
    rw [hJ0,hKT,hkG]
    abel
  have heq := r2_trace_residual c (range2G c e) (range2H c e) (range2J c e) K
  rw [hzero,Matrix.mul_zero,Matrix.trace_zero] at heq
  change 0=Matrix.trace (range2Q c*range2J c e)-Matrix.trace (U*range2G c e)+Matrix.trace (V*range2H c e) at heq
  rw [htU,htV,r2_traceQ] at hW
  rw [htU0,htV0,r2_traceQ] at heq
  change avg (fun z => dispersion c z*sdpSpectrum 2 (r2op (range2J c e)) z-1)≤
    avg (fun z => dispersion c z*sdpSpectrum 2 (r2op J) z-1)
  rw [r2_avg_spectrum,r2_avg_spectrum]
  linarith only [hW,heq]

theorem range2_exact_attained (m : ℝ) (hm : 0<m) :
    ∃ e : ℝ, Range2Root (m+2) e ∧ optimalEntropy 2 m=range2Value (m+2) e ∧
      ∃ b : BathFamily, Fintype.card b.ι≤3 ∧ b.admissible 2 m ∧
        b.cost 2 m=optimalEntropy 2 m ∧ ¬b.twoTemperature := by
  obtain ⟨e,hr⟩ := range2_root_exists m hm
  obtain ⟨hp,hG,hH⟩ := range2_feasible m e hm hr
  let p := range2Mom (m+2) e
  have hmin : sdpCost p m=optimalEntropy 2 m := by
    rw [← exact_sdp_infimum 2 (by decide) m hm]
    apply le_antisymm
    · apply le_csInf (sdpCosts_nonempty 2 (by decide) m hm)
      rintro _ ⟨q,hq,rfl⟩
      exact range2_sdp_global m e hm hr q hq
    · exact csInf_le (sdpCosts_bddBelow 2 m hm) ⟨p,hp,rfl⟩
  obtain ⟨b,hcard,hb,hle⟩ := sdpRealization p m hm hp hG hH
  have hcost : b.cost 2 m≤sdpCost p m := by
    rw [← bathMoments_cost]
    apply sdpCost_mono
    intro z hz
    rw [bathMoments_sigma]
    exact hle z hz
  have heq : b.cost 2 m=optimalEntropy 2 m := by
    apply le_antisymm (hcost.trans_eq hmin)
    have hbd : BddBelow (admissibleCosts 2 m) :=
      ⟨_,fun x hx => admissible_lower 2 (by decide) m hm x hx⟩
    exact csInf_le hbd ⟨b,hb,rfl⟩
  have ht : ¬b.twoTemperature := by
    intro ht
    have hlo := two_temperature_cost_lower b 2 (by decide) m hm hb ht
    have hhi := unrestricted_strict_two_temperature_gap 2 (by decide) m hm
    rw [heq] at hlo
    have hpos : 0<m*(m+4) := mul_pos hm (by linarith)
    have hstrict : 1/(m*(m+4))<2/(m*(m+4)) :=
      div_lt_div_of_pos_right (by norm_num) hpos
    exact not_le_of_gt (hhi.1.trans_lt hstrict) hlo
  exact ⟨e,hr,hmin.symm.trans (range2_cost_value m e hm hr),b,hcard,hb,heq,ht⟩

end
end GaussianRange
#check GaussianRange.range2_exact_attained
#print axioms GaussianRange.range2_sdp_global
#print axioms GaussianRange.range2_exact_attained
