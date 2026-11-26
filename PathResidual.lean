import PathSpectralLink

namespace GaussianRange
open Finset
open scoped RealInnerProductSpace
noncomputable section

-- An exact second-moment identity for every actual compressed column.
theorem path_second_column (r : ℕ) (hr : 0 < r) (m : ℝ) (j : Fin (r+1)) :
    (∑ v, (pathBath r m).temp v ^ 2 * ((pathBath r m).coeff v j)^2) =
      ∑ i : Fin (r+1), (pathTemperatureMatrix r m i j * rationalWindow (r+1) j)^2 := by
  let b := rationalBath r m
  let K := bathSpan b r
  let x := bathColumnIn b r j
  let y := compressedOperator b.temp K x
  let E := compressedBasis b.temp K
  let B := pathUnitBasis r hr m
  have he (v : (pathBath r m).ι) : ⟪E v,y⟫ = (pathBath r m).temp v * (pathBath r m).coeff v j := by
    change ⟪compressedBasis b.temp K v, compressedOperator b.temp K x⟫ = _
    rw [← (compressed_symmetric b.temp K) (compressedBasis b.temp K v) x,compressed_eigen,real_inner_smul_left]
    change (pathBath r m).temp v * ⟪E v,x⟫ = _
    rw [show (pathBath r m).coeff v j = ⟪E v,x⟫ from compressedCoeff_fin b r v j]
  have hx : x = rationalWindow (r+1) j • pathUnit r m j := by
    unfold x pathUnit
    rw [smul_smul,mul_inv_cancel₀ (ne_of_gt (rationalWindow_pos_fin r hr j)),one_smul]
  have hb (i : Fin (r+1)) : ⟪B i,y⟫ = pathTemperatureMatrix r m i j * rationalWindow (r+1) j := by
    change ⟪pathUnitBasis r hr m i,compressedOperator b.temp K x⟫ = _
    rw [hx,map_smul,real_inner_smul_right,pathUnitBasis_apply,pathUnit_entry r hr m]
    ring
  calc
    _ = ∑ v : (pathBath r m).ι, ⟪E v,y⟫^2 := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [he]
      ring
    _ = ‖y‖^2 := E.sum_sq_inner_right y
    _ = ∑ i : Fin (r+1), ⟪B i,y⟫^2 := (B.sum_sq_inner_right y).symm
    _ = _ := by simp_rw [hb]

theorem path_matrix_sq (r : ℕ) (m : ℝ) (i j : Fin (r+1)) :
    (pathTemperatureMatrix r m i j)^2 = (if i=j then (m+2)^2 else 0) + pathAdjacency r j i / (rationalRho (r+1))^2 := by
  unfold pathTemperatureMatrix pathAdj pathAdjacency
  by_cases h : i=j
  · subst j
    have hn : ¬ i.val+1=i.val := by omega
    simp [hn]
  · by_cases h₁ : i.val+1=j.val <;> by_cases h₂ : j.val+1=i.val <;> simp [h,h₁,h₂] <;> ring

theorem path_matrix_column_square (r : ℕ) (hr : 0 < r) (m : ℝ) (j : Fin (r+1)) :
    (∑ i : Fin (r+1), (pathTemperatureMatrix r m i j)^2) = (m+2)^2 +
      (2-(if j=0 then 1 else 0)-(if j=Fin.last r then 1 else 0))/(rationalRho (r+1))^2 := by
  simp_rw [path_matrix_sq,Finset.sum_add_distrib,← Finset.sum_div]
  have ha : (∑ i : Fin (r+1),pathAdjacency r j i) =
    (if j.val=0 then 0 else 1)+(if j.val+1<r+1 then 1 else 0) := by
    simpa using pathAdjacency_sum r j (fun _ => (1:ℝ))
  rw [ha]
  have he₀ : j.val=0 ↔ j=0 := by constructor <;> intro h <;> [exact Fin.ext h; simpa [h]]
  have he₁ : ¬ j.val+1<r+1 ↔ j=Fin.last r := by
    constructor
    · intro h; apply Fin.ext; simp; omega
    · intro h; subst j; simp
  have ha₀ : (∑ i : Fin (r+1), if i=j then (m+2)^2 else 0) = (m+2)^2 := by simp
  rw [ha₀]
  by_cases h₀ : j=0 <;> by_cases h₁ : j=Fin.last r
  · have h : j.val=0 := he₀.mpr h₀
    have h' : ¬j.val+1<r+1 := he₁.mpr h₁
    simp [h₀,h₁,h,h',hr,Nat.ne_of_gt hr] <;> ring
  · have h : j.val=0 := he₀.mpr h₀
    have h' : j.val+1<r+1 := by by_contra hn; exact h₁ (he₁.mp hn)
    simp [h₀,h₁,h,h',hr,Nat.ne_of_gt hr] <;> ring
  · have h : ¬j.val=0 := fun hn => h₀ (he₀.mp hn)
    have h' : ¬j.val+1<r+1 := he₁.mpr h₁
    simp [h₀,h₁,h,h',hr,Nat.ne_of_gt hr] <;> ring
  · have h : ¬j.val=0 := fun hn => h₀ (he₀.mp hn)
    have h' : j.val+1<r+1 := by by_contra hn; exact h₁ (he₁.mp hn)
    simp [h₀,h₁,h,h',hr,Nat.ne_of_gt hr] <;> ring

theorem bath_avg_second (b : BathFamily) (r : ℕ) :
    avg (fun z => ∑ v, weight r (b.coeff v) z * (b.temp v)^2) =
      ∑ j : Fin (r+1), ∑ v, (b.temp v)^2 * (b.coeff v j)^2 := by
  unfold avg
  rw [Real.circleAverage_fun_sum (fun v _ =>
    (show Continuous (fun z : ℂ => weight r (b.coeff v) z * (b.temp v)^2) from
      (cont_weight r _).mul continuous_const).continuousOn.circleIntegrable (by norm_num))]
  have he (v : b.ι) :
      Real.circleAverage (fun z => weight r (b.coeff v) z * (b.temp v)^2) 0 1 =
      (b.temp v)^2 * avg (weight r (b.coeff v)) := by
    simp_rw [mul_comm (weight r (b.coeff v) _)]
    exact Real.circleAverage_fun_smul (a := (b.temp v)^2)
  simp_rw [he, avg_weight_parseval, ← Fin.sum_univ_eq_sum_range, Finset.mul_sum]
  exact Finset.sum_comm

theorem path_avg_second (r : ℕ) (hr : 0 < r) (m : ℝ) :
    avg (fun z => ∑ v, weight r ((pathBath r m).coeff v) z * ((pathBath r m).temp v)^2) =
      (m+2)^2+(2-(rationalWindow (r+1) 0)^2-(rationalWindow (r+1) r)^2)/(rationalRho (r+1))^2 := by
  rw [bath_avg_second]
  simp_rw [path_second_column r hr m,mul_pow,← Finset.sum_mul,path_matrix_column_square r hr m]
  have hg : (∑ j : Fin (r+1), (rationalWindow (r+1) j)^2) = 1 := by
    exact (Fin.sum_univ_eq_sum_range (fun j : ℕ => (rationalWindow (r+1) j)^2) (r+1)).trans (rationalWindow_norm _ (by omega))
  have he (j : Fin (r+1)) : ((m+2)^2+(2-(if j=0 then 1 else 0)-(if j=Fin.last r then 1 else 0))/(rationalRho (r+1))^2) * (rationalWindow (r+1) j)^2 =
      (m+2)^2*(rationalWindow (r+1) j)^2 +
      (2*(rationalWindow (r+1) j)^2-(if j=0 then (rationalWindow (r+1) j)^2 else 0)-
      (if j=Fin.last r then (rationalWindow (r+1) j)^2 else 0))/(rationalRho (r+1))^2 := by
    split_ifs <;> ring
  simp_rw [he,Finset.sum_add_distrib,← Finset.mul_sum,← Finset.sum_div,Finset.sum_sub_distrib,hg]
  simp [← Finset.mul_sum,hg]

theorem path_avg_residual (r : ℕ) (hr : 0 < r) (m : ℝ) :
    avg (varianceFun r (pathBath r m).coeff (pathBath r m).temp (m+2)) =
      (2-(rationalWindow (r+1) 0)^2-(rationalWindow (r+1) r)^2)/(rationalRho (r+1))^2-2 := by
  rw [avg_variance_identity r _ _ _ (pathBath_normalization r hr m) (pathBath_weighted_normalization r hr m),path_avg_second r hr m]
  ring

theorem path_min_temperature_le (r : ℕ) (hr : 0 < r) (m : ℝ) (v : (pathBath r m).ι) :
    pathLambda r m 0 ≤ (pathBath r m).temp v := by
  have h : (pathBath r m).temp v ∈ Set.range (pathLambda r m) := by rw [← pathTemps_range_eq r hr m]; exact ⟨v,rfl⟩
  obtain ⟨k,hk⟩ := h
  rw [← hk]
  exact pathLambda_min r hr m k

theorem path_entropy_upper_exact (r : ℕ) (hr : 0 < r) (m : ℝ) (hm : 0<m)
    (ht : 0 < pathLambda r m 0) : (pathBath r m).cost r m ≤
      ((2-(rationalWindow (r+1) 0)^2-(rationalWindow (r+1) r)^2)/(rationalRho (r+1))^2-2)/(pathLambda r m 0*m) := by
  have h := physical_avg_entropy_upper r (pathBath r m).coeff (pathBath r m).temp m (pathLambda r m 0) hm ht
    (path_min_temperature_le r hr m) (pathBath_normalization r hr m) (pathBath_weighted_normalization r hr m)
  rw [path_avg_residual r hr m] at h
  exact h

end
end GaussianRange
#print axioms GaussianRange.path_second_column
#print axioms GaussianRange.path_avg_residual
#print axioms GaussianRange.path_entropy_upper_exact