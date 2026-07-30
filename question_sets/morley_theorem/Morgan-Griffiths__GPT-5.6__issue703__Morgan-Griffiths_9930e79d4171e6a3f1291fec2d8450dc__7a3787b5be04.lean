import ChallengeDeps
import Submission.Helpers

open LeanEval.Geometry.Morley
open scoped EuclideanGeometry

namespace Submission

/-ResultProofDefinitionsBegin-/
lemma morley_sin_three (x : ℝ) :
    Real.sin (3*x) =
      4 * Real.sin x * Real.sin (Real.pi/3 + x) * Real.sin (Real.pi/3 - x) := by
  rw [Real.sin_three_mul, Real.sin_add, Real.sin_sub, Real.sin_pi_div_three,
    Real.cos_pi_div_three]
  have h1 := Real.sin_sq_add_cos_sq x
  have h2 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  ring_nf
  rw [h2]
  ring_nf
  -- goal?
  linear_combination -3 * Real.sin x * h1

lemma morley_cosine (x y z : ℝ) (h : x + y + z = Real.pi/3) :
    Real.sin (Real.pi/3 + z)^2 + Real.sin (Real.pi/3 + x)^2 -
      2 * Real.sin (Real.pi/3+z) * Real.sin (Real.pi/3+x) * Real.cos y
      = Real.sin y ^ 2 := by
  have hy : y = Real.pi/3 - (x+z) := by linarith
  rw [hy]
  simp [Real.sin_add, Real.sin_sub, Real.cos_add, Real.cos_sub,
    Real.sin_pi_div_three, Real.cos_pi_div_three]
  have hx := Real.sin_sq_add_cos_sq x
  have hz := Real.sin_sq_add_cos_sq z
  have h3 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  ring_nf
  rw [h3]
  have h3' : (Real.sqrt (3:ℝ))^3 = 3 * Real.sqrt 3 := by
    calc
      (Real.sqrt (3:ℝ))^3 = (Real.sqrt 3)^2 * Real.sqrt 3 := by ring
      _ = _ := by rw [h3]
  rw [h3']
  ring_nf
  have hx' : Real.cos x ^2 = 1 - Real.sin x ^2 := by nlinarith [hx]
  have hz' : Real.cos z ^2 = 1 - Real.sin z ^2 := by nlinarith [hz]
  rw [hx', hz']
  ring

set_option maxHeartbeats 4000000
/-ResultProofDefinitionsEnd-/


theorem morley_theorem (A B C P Q R : Plane)
    (h : IsMorleyConfiguration A B C P Q R) :
    IsEquilateralTriple P Q R := by
  classical
  rcases h with ⟨hnc, hPin, hQin, hRin,
    ha0, hcar, hrap, ha3,
    hb0, habp, hpbq, hb3,
    hc0, hbcq, hqcr, hc3⟩
  let a : ℝ := ∠ P A B
  let b : ℝ := ∠ Q B C
  let c : ℝ := ∠ R C A
  have ha : 0 < a := by
    dsimp [a]
    rw [hcar, hrap] at ha0
    exact ha0
  have hb : 0 < b := by
    dsimp [b]
    rw [habp, hpbq] at hb0
    exact hb0
  have hc : 0 < c := by
    dsimp [c]
    rw [hbcq, hqcr] at hc0
    exact hc0
  have hA : ∠ C A B = 3*a := by simpa [a] using ha3.symm
  have hB : ∠ A B C = 3*b := by simpa [b] using hb3.symm
  have hC : ∠ B C A = 3*c := by simpa [c] using hc3.symm
  have hAB : A ≠ B := ne₁₂_of_not_collinear hnc
  have hBC : B ≠ C := ne₂₃_of_not_collinear hnc
  have hAC : A ≠ C := ne₁₃_of_not_collinear hnc
  have habc : a + b + c = Real.pi/3 := by
    have hs := EuclideanGeometry.angle_add_angle_add_angle_eq_pi (p₁:=A) (p₂:=B) C hAB.symm
    rw [hA, hB, hC] at hs
    linarith
  have ha_lt : a < Real.pi/3 := by linarith
  have hb_lt : b < Real.pi/3 := by linarith
  have hc_lt : c < Real.pi/3 := by linarith
  have hPAB0 : ¬ Collinear ℝ ({P,A,B} : Set Plane) := by
    intro hh
    rcases (EuclideanGeometry.collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi).1 hh with hPA | hBA | hzero | hpi
    · have heq : a = Real.pi/2 := by simp [a, hPA]
      linarith [Real.pi_pos]
    · exact hAB hBA.symm
    · have heq : a = 0 := by simpa [a] using hzero
      linarith
    · have heq : a = Real.pi := by simpa [a] using hpi
      linarith [Real.pi_pos]
  have hQBC0 : ¬ Collinear ℝ ({Q,B,C} : Set Plane) := by
    intro hh
    rcases (EuclideanGeometry.collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi).1 hh with hQB | hCB | hzero | hpi
    · have heq : b = Real.pi/2 := by simp [b, hQB]
      linarith [Real.pi_pos]
    · exact hBC hCB.symm
    · have heq : b = 0 := by simpa [b] using hzero
      linarith
    · have heq : b = Real.pi := by simpa [b] using hpi
      linarith [Real.pi_pos]
  have hRCA0 : ¬ Collinear ℝ ({R,C,A} : Set Plane) := by
    intro hh
    rcases (EuclideanGeometry.collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi).1 hh with hRC | hAC' | hzero | hpi
    · have heq : c = Real.pi/2 := by simp [c, hRC]
      linarith [Real.pi_pos]
    · exact hAC hAC'
    · have heq : c = 0 := by simpa [c] using hzero
      linarith
    · have heq : c = Real.pi := by simpa [c] using hpi
      linarith [Real.pi_pos]
  have hBPA0 : ¬ Collinear ℝ ({B,P,A} : Set Plane) := by
    have he : ({B,P,A} : Set Plane) = {P,A,B} := by
      ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; aesop
    rw [he]
    exact hPAB0
  have hAPB0 : ¬ Collinear ℝ ({A,P,B} : Set Plane) := by
    have he : ({A,P,B} : Set Plane) = {P,A,B} := by
      ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; aesop
    rw [he]
    exact hPAB0
  have hBQC0 : ¬ Collinear ℝ ({B,Q,C} : Set Plane) := by
    have he : ({B,Q,C} : Set Plane) = {Q,B,C} := by
      ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; aesop
    rw [he]
    exact hQBC0
  have hCBQ0 : ¬ Collinear ℝ ({C,Q,B} : Set Plane) := by
    have he : ({C,Q,B} : Set Plane) = {Q,B,C} := by
      ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; aesop
    rw [he]
    exact hQBC0
  have hCRA0 : ¬ Collinear ℝ ({C,R,A} : Set Plane) := by
    have he : ({C,R,A} : Set Plane) = {R,C,A} := by
      ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; aesop
    rw [he]
    exact hRCA0
  have hARC0 : ¬ Collinear ℝ ({A,R,C} : Set Plane) := by
    have he : ({A,R,C} : Set Plane) = {R,C,A} := by
      ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; aesop
    rw [he]
    exact hRCA0
  have hangABP : ∠ A B P = b := by
    dsimp [b]
    calc ∠ A B P = ∠ P B Q := habp
         _ = ∠ Q B C := hpbq
  have hangCAR : ∠ C A R = a := by
    dsimp [a]
    calc ∠ C A R = ∠ R A P := hcar
         _ = ∠ P A B := hrap
  have hangBCQ : ∠ B C Q = c := by
    dsimp [c]
    calc ∠ B C Q = ∠ Q C R := hbcq
         _ = ∠ R C A := hqcr
  have hangBPA : ∠ B P A = Real.pi - (a+b) := by
    have hs := EuclideanGeometry.angle_add_angle_add_angle_eq_pi (p₁:=A) (p₂:=B) P hAB.symm
    rw [hangABP] at hs
    change _ at hs
    -- P A B
    change b + ∠ B P A + a = Real.pi at hs
    linarith
  have hsinBPA : Real.sin (∠ B P A) = Real.sin (a+b) := by
    rw [hangBPA, Real.sin_pi_sub]
  have hangCQB : ∠ C Q B = Real.pi - (b+c) := by
    have hs := EuclideanGeometry.angle_add_angle_add_angle_eq_pi (p₁:=B) (p₂:=C) Q hBC.symm
    rw [hangBCQ] at hs
    change c + ∠ C Q B + b = Real.pi at hs
    linarith
  have hsinCQB : Real.sin (∠ C Q B) = Real.sin (b+c) := by
    rw [hangCQB, Real.sin_pi_sub]
  have hangARC : ∠ A R C = Real.pi - (a+c) := by
    have hs := EuclideanGeometry.angle_add_angle_add_angle_eq_pi (p₁:=C) (p₂:=A) R hAC -- p₂=A, p₁=C, need A≠C hAC
    rw [hangCAR] at hs
    change a + ∠ A R C + c = Real.pi at hs
    linarith
  have hsinARC : Real.sin (∠ A R C) = Real.sin (a+c) := by
    rw [hangARC, Real.sin_pi_sub]
  have hangPBA : ∠ P B A = b := by
    rw [EuclideanGeometry.angle_comm]
    exact hangABP
  have hangACR : ∠ A C R = c := by
    rw [EuclideanGeometry.angle_comm]
  have hangRAC : ∠ R A C = a := by
    rw [EuclideanGeometry.angle_comm]
    exact hangCAR
  have hangCBQ' : ∠ Q B C = b := rfl
  have hBP : dist B P = dist A B * Real.sin a / Real.sin (a+b) := by
    have hh := EuclideanGeometry.dist_eq_dist_mul_sin_angle_div_sin_angle
      (p₁:=B) (p₂:=P) (p₃:=A) hBPA0
    rw [hsinBPA] at hh
    change dist B P = dist A B * Real.sin a / Real.sin (a+b) at hh
    exact hh
  have hAP : dist A P = dist A B * Real.sin b / Real.sin (a+b) := by
    have hh := EuclideanGeometry.dist_eq_dist_mul_sin_angle_div_sin_angle
      (p₁:=A) (p₂:=P) (p₃:=B) hAPB0
    rw [EuclideanGeometry.angle_comm A P B, hsinBPA,
        EuclideanGeometry.angle_comm P B A, hangABP] at hh
    rw [dist_comm B A] at hh
    change dist A P = dist A B * Real.sin b / Real.sin (a+b) at hh
    exact hh
  have hBQ : dist B Q = dist B C * Real.sin c / Real.sin (b+c) := by
    have hh := EuclideanGeometry.dist_eq_dist_mul_sin_angle_div_sin_angle
      (p₁:=B) (p₂:=Q) (p₃:=C) hBQC0
    rw [EuclideanGeometry.angle_comm B Q C, hsinCQB,
        EuclideanGeometry.angle_comm Q C B] at hh
    -- angle B C Q equals c
    rw [hangBCQ] at hh
    rw [dist_comm C B] at hh
    -- oops dist p3 p1 is dist C B, want dist B C; comm done
    change dist B Q = dist B C * Real.sin c / Real.sin (b+c) at hh
    exact hh
  have hCQ : dist C Q = dist B C * Real.sin b / Real.sin (b+c) := by
    have hh := EuclideanGeometry.dist_eq_dist_mul_sin_angle_div_sin_angle
      (p₁:=C) (p₂:=Q) (p₃:=B) hCBQ0
    rw [hsinCQB] at hh
    -- angle Q B C = b
    change dist C Q = dist B C * Real.sin b / Real.sin (b+c) at hh
    exact hh
  have hCR : dist C R = dist A C * Real.sin a / Real.sin (a+c) := by
    have hh := EuclideanGeometry.dist_eq_dist_mul_sin_angle_div_sin_angle
      (p₁:=C) (p₂:=R) (p₃:=A) hCRA0
    rw [EuclideanGeometry.angle_comm C R A, hsinARC] at hh
    -- angle R A C = a
    rw [hangRAC] at hh
    change dist C R = dist A C * Real.sin a / Real.sin (a+c) at hh
    exact hh
  have hAR : dist A R = dist A C * Real.sin c / Real.sin (a+c) := by
    have hh := EuclideanGeometry.dist_eq_dist_mul_sin_angle_div_sin_angle
      (p₁:=A) (p₂:=R) (p₃:=C) hARC0
    rw [hsinARC] at hh
    -- angle R C A = c, dist C A -> AC
    rw [dist_comm C A] at hh
    change dist A R = dist A C * Real.sin c / Real.sin (a+c) at hh
    exact hh
  have hBCA0 : ¬ Collinear ℝ ({B,C,A} : Set Plane) := by
    have he : ({B,C,A} : Set Plane) = {A,B,C} := by
      ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; aesop
    rw [he]; exact hnc
  have hACB0 : ¬ Collinear ℝ ({A,C,B} : Set Plane) := by
    have he : ({A,C,B} : Set Plane) = {A,B,C} := by
      ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; aesop
    rw [he]; exact hnc
  have hBClen : dist B C = dist A B * Real.sin (3*a) / Real.sin (3*c) := by
    have hh := EuclideanGeometry.dist_eq_dist_mul_sin_angle_div_sin_angle
      (p₁:=B) (p₂:=C) (p₃:=A) hBCA0
    rw [hA, hC] at hh
    exact hh
  have hAClen : dist A C = dist A B * Real.sin (3*b) / Real.sin (3*c) := by
    have hh := EuclideanGeometry.dist_eq_dist_mul_sin_angle_div_sin_angle
      (p₁:=A) (p₂:=C) (p₃:=B) hACB0
    rw [EuclideanGeometry.angle_comm C B A,
        EuclideanGeometry.angle_comm A C B] at hh
    rw [hB, hC, dist_comm B A] at hh
    exact hh
  have hab : a+b = Real.pi/3 - c := by linarith
  have hbc : b+c = Real.pi/3 - a := by linarith
  have hac : a+c = Real.pi/3 - b := by linarith
  have hsinab : 0 < Real.sin (a+b) := by
    rw [← hsinBPA]
    exact EuclideanGeometry.sin_pos_of_not_collinear hBPA0
  have hsinbc : 0 < Real.sin (b+c) := by
    rw [← hsinCQB]
    exact EuclideanGeometry.sin_pos_of_not_collinear hCBQ0
  have hsinac : 0 < Real.sin (a+c) := by
    rw [← hsinARC]
    exact EuclideanGeometry.sin_pos_of_not_collinear hARC0
  have hsin3c : 0 < Real.sin (3*c) := by
    rw [← hC]
    have hh := EuclideanGeometry.sin_pos_of_not_collinear hBCA0
    -- angle B C A
    exact hh
  have hsinc : 0 < Real.sin c :=
    Real.sin_pos_of_pos_of_lt_pi hc (by linarith [hc_lt, Real.pi_pos])
  have hsina : 0 < Real.sin a :=
    Real.sin_pos_of_pos_of_lt_pi ha (by linarith [ha_lt, Real.pi_pos])
  have hsinb : 0 < Real.sin b :=
    Real.sin_pos_of_pos_of_lt_pi hb (by linarith [hb_lt, Real.pi_pos])
  have hsinUc : 0 < Real.sin (Real.pi/3+c) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hc, Real.pi_pos]) (by linarith [hc_lt, Real.pi_pos])
  have hsinUb : 0 < Real.sin (Real.pi/3+b) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hb, Real.pi_pos]) (by linarith [hb_lt, Real.pi_pos])
  have hsinUa : 0 < Real.sin (Real.pi/3+a) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [ha, Real.pi_pos]) (by linarith [ha_lt, Real.pi_pos])
  let k : ℝ := dist A B /
    (Real.sin (Real.pi/3-c) * Real.sin (Real.pi/3+c))
  have hkBP : dist B P = k * Real.sin a * Real.sin (Real.pi/3+c) := by
    rw [hBP, hab]
    dsimp [k]
    have hu : Real.sin (Real.pi/3+c) ≠ 0 := ne_of_gt hsinUc
    have hv : Real.sin (Real.pi/3-c) ≠ 0 := by
      rw [← hab]
      exact ne_of_gt hsinab
    field_simp [hu, hv]
    <;> (ring_nf at hu hv ⊢)
    <;> rw [mul_assoc, mul_inv_cancel₀ hu, mul_one]
    <;> ring
  have hkAP : dist A P = k * Real.sin b * Real.sin (Real.pi/3+c) := by
    rw [hAP, hab]
    dsimp [k]
    have hu : Real.sin (Real.pi/3+c) ≠ 0 := ne_of_gt hsinUc
    have hv : Real.sin (Real.pi/3-c) ≠ 0 := by
      rw [← hab]
      exact ne_of_gt hsinab
    field_simp [hu, hv]
    <;> (ring_nf at hu hv ⊢)
    <;> rw [mul_assoc, mul_inv_cancel₀ hu, mul_one]
    <;> ring
  have hkBQ : dist B Q = k * Real.sin a * Real.sin (Real.pi/3+a) := by
    rw [hBQ, hBClen, hbc]
    dsimp [k]
    rw [morley_sin_three a, morley_sin_three c]
    have hcN : Real.sin c ≠ 0 := ne_of_gt hsinc
    have hUcN : Real.sin (Real.pi/3+c) ≠ 0 := ne_of_gt hsinUc
    have hVcN : Real.sin (Real.pi/3-c) ≠ 0 := by
      rw [← hab]
      exact ne_of_gt hsinab
    have hVaN : Real.sin (Real.pi/3-a) ≠ 0 := by
      rw [← hbc]
      exact ne_of_gt hsinbc
    have hUcN' : Real.sin ((Real.pi + 3*c)/3) ≠ 0 := by
      convert hUcN using 1 <;> ring_nf
    have hVcN' : Real.sin ((Real.pi - 3*c)/3) ≠ 0 := by
      convert hVcN using 1 <;> ring_nf
    have hVaN' : Real.sin ((Real.pi - 3*a)/3) ≠ 0 := by
      convert hVaN using 1 <;> ring_nf
    field_simp [hcN, hUcN, hVcN, hVaN, hUcN', hVcN', hVaN']
  let t : ℝ := k * Real.sin a * Real.sin b / Real.sin c
  have hkCQ : dist C Q = t * Real.sin (Real.pi/3+a) := by
    rw [hCQ, hBClen, hbc]
    dsimp [t, k]
    rw [morley_sin_three a, morley_sin_three c]
    have hcN : Real.sin c ≠ 0 := ne_of_gt hsinc
    have hUcN : Real.sin (Real.pi/3+c) ≠ 0 := ne_of_gt hsinUc
    have hVcN : Real.sin (Real.pi/3-c) ≠ 0 := by
      rw [← hab]
      exact ne_of_gt hsinab
    have hVaN : Real.sin (Real.pi/3-a) ≠ 0 := by
      rw [← hbc]
      exact ne_of_gt hsinbc
    have hUcN' : Real.sin ((Real.pi + 3*c)/3) ≠ 0 := by
      convert hUcN using 1 <;> ring_nf
    have hVcN' : Real.sin ((Real.pi - 3*c)/3) ≠ 0 := by
      convert hVcN using 1 <;> ring_nf
    have hVaN' : Real.sin ((Real.pi - 3*a)/3) ≠ 0 := by
      convert hVaN using 1 <;> ring_nf
    field_simp [hcN, hUcN, hVcN, hVaN, hUcN', hVcN', hVaN']
  have hkCR : dist C R = t * Real.sin (Real.pi/3+b) := by
    rw [hCR, hAClen, hac]
    dsimp [t, k]
    rw [morley_sin_three b, morley_sin_three c]
    have hcN : Real.sin c ≠ 0 := ne_of_gt hsinc
    have hUcN : Real.sin (Real.pi/3+c) ≠ 0 := ne_of_gt hsinUc
    have hVcN : Real.sin (Real.pi/3-c) ≠ 0 := by
      rw [← hab]
      exact ne_of_gt hsinab
    have hVbN : Real.sin (Real.pi/3-b) ≠ 0 := by
      rw [← hac]
      exact ne_of_gt hsinac
    have hUcN' : Real.sin ((Real.pi + 3*c)/3) ≠ 0 := by
      convert hUcN using 1 <;> ring_nf
    have hVcN' : Real.sin ((Real.pi - 3*c)/3) ≠ 0 := by
      convert hVcN using 1 <;> ring_nf
    have hVbN' : Real.sin ((Real.pi - 3*b)/3) ≠ 0 := by
      convert hVbN using 1 <;> ring_nf
    field_simp [hcN, hUcN, hVcN, hVbN, hUcN', hVcN', hVbN']
  have hkAR : dist A R = k * Real.sin b * Real.sin (Real.pi/3+b) := by
    rw [hAR, hAClen, hac]
    dsimp [k]
    rw [morley_sin_three b, morley_sin_three c]
    have hcN : Real.sin c ≠ 0 := ne_of_gt hsinc
    have hUcN : Real.sin (Real.pi/3+c) ≠ 0 := ne_of_gt hsinUc
    have hVcN : Real.sin (Real.pi/3-c) ≠ 0 := by
      rw [← hab]
      exact ne_of_gt hsinab
    have hVbN : Real.sin (Real.pi/3-b) ≠ 0 := by
      rw [← hac]
      exact ne_of_gt hsinac
    have hUcN' : Real.sin ((Real.pi + 3*c)/3) ≠ 0 := by
      convert hUcN using 1 <;> ring_nf
    have hVcN' : Real.sin ((Real.pi - 3*c)/3) ≠ 0 := by
      convert hVcN using 1 <;> ring_nf
    have hVbN' : Real.sin ((Real.pi - 3*b)/3) ≠ 0 := by
      convert hVbN using 1 <;> ring_nf
    field_simp [hcN, hUcN, hVcN, hVbN, hUcN', hVcN', hVbN']
  have hkpos : 0 < k := by
    dsimp [k]
    have hD : 0 < dist A B := dist_pos.mpr hAB
    have hv : 0 < Real.sin (Real.pi/3-c) := by
      rw [← hab]
      exact hsinab
    exact div_pos hD (mul_pos hv hsinUc)
  have htpos : 0 < t := by
    dsimp [t]
    exact div_pos (mul_pos (mul_pos hkpos hsina) hsinb) hsinc
  have hangPBQ : ∠ P B Q = b := by
    calc
      ∠ P B Q = ∠ Q B C := hpbq
      _ = b := rfl
  have hangQCR : ∠ Q C R = c := by
    calc
      ∠ Q C R = ∠ R C A := hqcr
      _ = c := rfl
  have hangRAP : ∠ R A P = a := by
    calc
      ∠ R A P = ∠ P A B := hrap
      _ = a := rfl
  let s0 : ℝ := k * Real.sin a * Real.sin b
  have hs0pos : 0 < s0 := by
    dsimp [s0]
    exact mul_pos (mul_pos hkpos hsina) hsinb
  have hPQmul : dist P Q * dist P Q = s0*s0 := by
    dsimp [s0]
    have hlaw := EuclideanGeometry.law_cos P B Q
    rw [dist_comm P B, hkBP, dist_comm Q B, hkBQ, hangPBQ] at hlaw
    have htr := morley_cosine a b c habc
    linear_combination hlaw + (k * Real.sin a)^2 * htr
  have hPQ : dist P Q = s0 :=
    (mul_self_inj_of_nonneg dist_nonneg (le_of_lt hs0pos)).1 hPQmul
  have hts : t * Real.sin c = s0 := by
    dsimp [t, s0]
    field_simp [ne_of_gt hsinc]
  have hQRmul : dist Q R * dist Q R = (t*Real.sin c)*(t*Real.sin c) := by
    have hlaw := EuclideanGeometry.law_cos Q C R
    rw [dist_comm Q C, hkCQ, dist_comm R C, hkCR, hangQCR] at hlaw
    have htr := morley_cosine b c a (by linarith [habc])
    linear_combination hlaw + t^2 * htr
  have hQRmul' : dist Q R * dist Q R = s0*s0 := by
    rw [hQRmul, hts]
  have hQR : dist Q R = s0 :=
    (mul_self_inj_of_nonneg dist_nonneg (le_of_lt hs0pos)).1 hQRmul'
  have hRPmul : dist R P * dist R P = s0*s0 := by
    dsimp [s0]
    have hlaw := EuclideanGeometry.law_cos R A P
    rw [dist_comm R A, hkAR, dist_comm P A, hkAP, hangRAP] at hlaw
    have htr := morley_cosine c a b (by linarith [habc])
    linear_combination hlaw + (k * Real.sin b)^2 * htr
  have hRP : dist R P = s0 :=
    (mul_self_inj_of_nonneg dist_nonneg (le_of_lt hs0pos)).1 hRPmul
  exact ⟨hPQ.trans hQR.symm, hQR.trans hRP.symm⟩


end Submission
