import SDPExact

namespace GaussianRange
open Finset Polynomial
open scoped RealInnerProductSpace Matrix
set_option maxHeartbeats 1000000
noncomputable section

def matrix3 (a b d e f g h i j : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun x y => if x.val=0 then (if y.val=0 then a else if y.val=1 then b else d)
    else if x.val=1 then (if y.val=0 then e else if y.val=1 then f else g)
    else (if y.val=0 then h else if y.val=1 then i else j)

def range2Q (c : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  matrix3 c (-1) 0 (-1) c (-1) 0 (-1) c
def range2D (c e : ℝ) : ℝ := e*(c-2*e)-1/2
def range2B (c e : ℝ) : ℝ := 4*c^2*e-c+8*e
def range2A (c e : ℝ) : ℝ := 2*e*(2*c*e+1)/range2B c e
def range2N (c e : ℝ) : ℝ :=
  16*c^5*e^2-64*c^4*e^3-8*c^4*e+32*c^3*e^4+
    20*c^3*e^2+c^3-40*c*e^2+2*c+128*e^3
def range2L (c e : ℝ) : ℝ := 2*range2D c e*range2B c e

def range2KNum (c e : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  let w := 2*c*e+1
  let u := w*(4*range2D c e+1)
  let v := range2B c e-4*e*w
  let x := 2*e*w
  let y := 2*e*v
  matrix3 u v w x y x w v u
def range2K (c e : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  (range2L c e)⁻¹ • range2KNum c e
def range2G (c e : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  matrix3 (range2A c e) 0 0 0 (1-2*range2A c e) 0 0 0 (range2A c e)
def range2H (c e : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  matrix3 e (-1/2) 0 (-1/2) (c-2*e) (-1/2) 0 (-1/2) e
def range2J (c e : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := range2G c e * range2K c e
def range2U (c e : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  range2K c e * range2Q c + range2Q c * (range2K c e)ᵀ
def range2V (c e : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  range2K c e * range2Q c * (range2K c e)ᵀ
def range2Value (c e : ℝ) : ℝ :=
  2*e*(-4*c^3*e+8*c^2*e^2+c^2+2)/( (-2*c*e+4*e^2+1)*range2B c e)-1

def Range2Root (c e : ℝ) : Prop :=
  c/4≤e ∧ e≤(3*c-2)/8 ∧ range2N c e=0

theorem range2N_left (m : ℝ) :
    range2N (m+2) ((m+2)/4)=
      m^7/8+7*m^6/4+39*m^5/4+55*m^4/2+81*m^3/2+27*m^2+4*m := by
  unfold range2N
  ring

theorem range2N_right (m : ℝ) :
    range2N (m+2) ((3*(m+2)-2)/8)=
      -m*(63*m^6+618*m^5+2380*m^4+4552*m^3+4368*m^2+2144*m+768)/128 := by
  unfold range2N
  ring

theorem range2_root_exists (m : ℝ) (hm : 0<m) :
    ∃ e,Range2Root (m+2) e := by
  have hl : 0<range2N (m+2) ((m+2)/4) := by rw [range2N_left]; positivity
  have hr : range2N (m+2) ((3*(m+2)-2)/8)<0 := by
    rw [range2N_right]
    have h : 0<m*(63*m^6+618*m^5+2380*m^4+4552*m^3+4368*m^2+2144*m+768)/128 := by positivity
    linarith
  have hc : Continuous (range2N (m+2)) := by unfold range2N; fun_prop
  have hab : (m+2)/4≤(3*(m+2)-2)/8 := by linarith
  have hz : (0:ℝ)∈Set.Icc (range2N (m+2) ((3*(m+2)-2)/8)) (range2N (m+2) ((m+2)/4)) :=
    ⟨hr.le,hl.le⟩
  obtain ⟨e,he,heq⟩ := intermediate_value_Icc' hab hc.continuousOn hz
  exact ⟨e,he.1,he.2,heq⟩

theorem range2_params_pos (c e : ℝ) (hc : 2<c) (hl : c/4≤e)
    (hu : e≤(3*c-2)/8) :
    0<e ∧ 0<c-2*e ∧ 0<range2D c e ∧ 0<range2B c e ∧
      0<range2L c e ∧ 0<range2A c e ∧ 0<1-2*range2A c e := by
  have hcp : 0<c := by linarith
  have he : 0<e := by linarith
  have hq : 0<c-2*e := by linarith
  have hD : 0<range2D c e := by
    unfold range2D
    have hp : c/4*((c+2)/4)≤e*(c-2*e) :=
      mul_le_mul hl (by linarith) (by positivity) he.le
    have hstrict : (1:ℝ)/2<c/4*((c+2)/4) := by
      nlinarith [mul_pos (sub_pos.mpr hc) (show 0<c+4 by positivity)]
    linarith
  have hB : 0<range2B c e := by
    unfold range2B
    have h := mul_nonneg (sub_nonneg.mpr hl) (show 0≤4*c^2+8 by positivity)
    nlinarith only [h,show 0<c^3+c by positivity]
  have ha : 0<range2A c e := by unfold range2A; positivity
  have hb : 0<1-2*range2A c e := by
    unfold range2A
    apply sub_pos.mpr
    have h : (2:ℝ)*(2*e*(2*c*e+1))<range2B c e := by
      have heq : range2B c e-2*(2*e*(2*c*e+1))=
        4*c*range2D c e+c+4*e := by unfold range2B range2D; ring
      linarith [show 0<4*c*range2D c e+c+4*e by positivity]
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ hB).2
    simpa using h
  exact ⟨he,hq,hD,hB,by unfold range2L; positivity,ha,hb⟩

theorem range2_HK (c e : ℝ) (hD : range2D c e≠0) (hB : range2B c e≠0) :
    range2H c e * range2K c e=range2G c e := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [range2H,range2K,range2KNum,range2G,range2A,range2L,
      matrix3,Matrix.smul_apply,Matrix.mul_apply,Fin.sum_univ_three,Fin.val_natCast] <;>
    (simp (disch := decide) [show (2:Nat) ≠ 0 by decide,show (2:Nat) ≠ 1 by decide,show (1:Nat) ≠ 0 by decide,show (0:Nat) ≠ 1 by decide]) <;> field_simp [hD,hB] <;> simp only [range2D,range2B] <;> ring

def toeplitz3 (a b d : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  matrix3 a b d b a b d b a

theorem range2_U_toeplitz (c e : ℝ) :
    range2U c e=toeplitz3 (range2U c e 0 0) (range2U c e 0 1) (range2U c e 0 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [range2U,range2K,range2KNum,range2Q,toeplitz3,
      matrix3,Matrix.smul_apply,Matrix.mul_apply,Fin.sum_univ_three,Fin.val_natCast,Matrix.transpose_apply] <;>
    (simp (disch := decide) [show (2:Nat) ≠ 0 by decide,show (2:Nat) ≠ 1 by decide,show (1:Nat) ≠ 0 by decide,show (0:Nat) ≠ 1 by decide]) <;> simp only [range2B,range2D] <;> ring

theorem range2_V_diag_diff (c e : ℝ) :
    range2V c e 0 0-range2V c e 1 1 =
      (range2L c e)⁻¹^2*range2N c e := by
  norm_num [range2V,range2K,range2KNum,range2Q,Matrix.mul_apply,
    matrix3,Matrix.smul_apply,Fin.sum_univ_three,Fin.val_natCast,Matrix.transpose_apply]
  simp (disch := decide) [show (2:Nat) ≠ 0 by decide,show (2:Nat) ≠ 1 by decide,show (1:Nat) ≠ 0 by decide,show (0:Nat) ≠ 1 by decide]
  unfold range2B range2D range2N
  ring

theorem range2_V_toeplitz (c e : ℝ) (hN : range2N c e=0) :
    range2V c e=toeplitz3 (range2V c e 0 0) (range2V c e 0 1) (range2V c e 0 2) := by
  have he : range2V c e 1 1=range2V c e 0 0 := by
    have h := range2_V_diag_diff c e
    rw [hN,mul_zero] at h
    linarith
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [toeplitz3,matrix3] <;>
    first | exact he | (norm_num [range2V,range2K,range2KNum,range2Q,
      matrix3,Matrix.smul_apply,Matrix.mul_apply,Fin.sum_univ_three,Fin.val_natCast,Matrix.transpose_apply] <;> (simp (disch := decide) [show (2:Nat) ≠ 0 by decide,show (2:Nat) ≠ 1 by decide,show (1:Nat) ≠ 0 by decide,show (0:Nat) ≠ 1 by decide]) <;> ring)

end
end GaussianRange
#print axioms GaussianRange.range2_root_exists
#print axioms GaussianRange.range2_HK
#print axioms GaussianRange.range2_U_toeplitz
#print axioms GaussianRange.range2_V_toeplitz
