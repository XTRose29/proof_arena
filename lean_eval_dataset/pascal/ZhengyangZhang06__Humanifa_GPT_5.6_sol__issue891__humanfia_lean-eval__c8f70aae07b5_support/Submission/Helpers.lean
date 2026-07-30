import ChallengeDeps

open LeanEval.Geometry.PascalPappus
open Matrix

namespace Submission.Helpers

def combine (a₁ a₂ a₃ : Fin 3 → ℝ) (x y z : ℝ) : Fin 3 → ℝ :=
  x • a₁ + y • a₂ + z • a₃

lemma samePoint_symm {v w : Fin 3 → ℝ} (h : SamePoint v w) : SamePoint w v := by
  rcases h with ⟨c, hc, rfl⟩
  refine ⟨c⁻¹, inv_ne_zero hc, ?_⟩
  rw [smul_smul, inv_mul_cancel₀ hc, one_smul]

lemma not_samePoint_symm {v w : Fin 3 → ℝ} (h : ¬ SamePoint v w) :
    ¬ SamePoint w v :=
  fun hwv => h (samePoint_symm hwv)

lemma linearIndependent_pair_of_not_samePoint {v w : Fin 3 → ℝ}
    (hv : v ≠ 0) (hw : w ≠ 0) (hvw : ¬ SamePoint v w) :
    LinearIndependent ℝ ![v, w] := by
  rw [LinearIndependent.pair_iff' hv]
  intro c hcvw
  apply hvw
  refine ⟨c, ?_, hcvw.symm⟩
  intro hc
  apply hw
  simpa [hc] using hcvw.symm

lemma pairing_symm (M : Matrix (Fin 3) (Fin 3) ℝ) (hM : M.IsSymm)
    (v w : Fin 3 → ℝ) :
    v ⬝ᵥ (M *ᵥ w) = w ⬝ᵥ (M *ᵥ v) := by
  calc
    v ⬝ᵥ (M *ᵥ w) = v ⬝ᵥ (Mᵀ *ᵥ w) := by rw [hM.eq]
    _ = w ⬝ᵥ (M *ᵥ v) := dotProduct_transpose_mulVec M v w

lemma quadratic_pair (M : Matrix (Fin 3) (Fin 3) ℝ) (hM : M.IsSymm)
    (v w : Fin 3 → ℝ) (a b : ℝ) :
    (a • v + b • w) ⬝ᵥ (M *ᵥ (a • v + b • w)) =
      a ^ 2 * (v ⬝ᵥ (M *ᵥ v)) + b ^ 2 * (w ⬝ᵥ (M *ᵥ w)) +
        2 * a * b * (v ⬝ᵥ (M *ᵥ w)) := by
  simp only [mulVec, dotProduct, Fin.sum_univ_three, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  rw [hM.apply 0 1, hM.apply 0 2, hM.apply 1 2]
  ring

lemma pairing_ne_zero (M : Matrix (Fin 3) (Fin 3) ℝ) (hM : M.IsSymm)
    (hMdet : M.det ≠ 0) {v w : Fin 3 → ℝ}
    (hv : v ≠ 0) (hw : w ≠ 0) (hvw : ¬ SamePoint v w)
    (hQv : v ⬝ᵥ (M *ᵥ v) = 0) (hQw : w ⬝ᵥ (M *ᵥ w) = 0) :
    v ⬝ᵥ (M *ᵥ w) ≠ 0 := by
  intro hpair
  have hLI := linearIndependent_pair_of_not_samePoint hv hw hvw
  have hinj : Function.Injective M.mulVec := by
    intro x y hxy
    apply sub_eq_zero.mp
    apply Matrix.eq_zero_of_mulVec_eq_zero hMdet
    rw [mulVec_sub, hxy, sub_self]
  have hMv : M *ᵥ v ≠ 0 := by
    intro hzero
    exact hv (Matrix.eq_zero_of_mulVec_eq_zero hMdet hzero)
  have hMw : M *ᵥ w ≠ 0 := by
    intro hzero
    exact hw (Matrix.eq_zero_of_mulVec_eq_zero hMdet hzero)
  have hImageNotSame : ¬ SamePoint (M *ᵥ v) (M *ᵥ w) := by
    rintro ⟨c, hc, himage⟩
    apply hvw
    refine ⟨c, hc, ?_⟩
    apply hinj
    rw [mulVec_smul, himage]
  have hImageLI : LinearIndependent ℝ ![M *ᵥ v, M *ᵥ w] :=
    linearIndependent_pair_of_not_samePoint hMv hMw hImageNotSame
  have hvwCross : v ⨯₃ w ≠ 0 :=
    crossProduct_ne_zero_iff_linearIndependent.mpr hLI
  have hImageCross : (M *ᵥ v) ⨯₃ (M *ᵥ w) ≠ 0 :=
    crossProduct_ne_zero_iff_linearIndependent.mpr hImageLI
  rcases Configuration.ofField.crossProduct_eq_zero_of_dotProduct_eq_zero
      hQv ((pairing_symm M hM w v).trans hpair)
      hpair hQw with hzero | hzero
  · exact hvwCross hzero
  · exact hImageCross hzero

lemma triple_product_ne_zero (M : Matrix (Fin 3) (Fin 3) ℝ) (hM : M.IsSymm)
    (hMdet : M.det ≠ 0) {u v w : Fin 3 → ℝ}
    (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0)
    (huv : ¬ SamePoint u v) (huw : ¬ SamePoint u w) (hvw : ¬ SamePoint v w)
    (hQu : u ⬝ᵥ (M *ᵥ u) = 0) (hQv : v ⬝ᵥ (M *ᵥ v) = 0)
    (hQw : w ⬝ᵥ (M *ᵥ w) = 0) :
    u ⬝ᵥ (v ⨯₃ w) ≠ 0 := by
  have hLI := linearIndependent_pair_of_not_samePoint hu hv huv
  have hpair := pairing_ne_zero M hM hMdet hu hv huv hQu hQv
  have hrange : Set.range ![u, v] = ({u, v} : Set (Fin 3 → ℝ)) := by
    ext t
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · intro ht
      rcases ht with (rfl | rfl)
      · exact ⟨0, by simp⟩
      · exact ⟨1, by simp⟩
  have hnotmem : w ∉ Submodule.span ℝ (Set.range ![u, v]) := by
    rw [hrange]
    intro hwspan
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hwspan
    have hquad : 2 * a * b * (u ⬝ᵥ (M *ᵥ v)) = 0 := by
      calc
        2 * a * b * (u ⬝ᵥ (M *ᵥ v)) =
            (a • u + b • v) ⬝ᵥ (M *ᵥ (a • u + b • v)) := by
              rw [quadratic_pair M hM, hQu, hQv]
              ring
        _ = w ⬝ᵥ (M *ᵥ w) := by rw [hab]
        _ = 0 := hQw
    have hfactor : (2 * (u ⬝ᵥ (M *ᵥ v))) * (a * b) = 0 := by
      calc
        (2 * (u ⬝ᵥ (M *ᵥ v))) * (a * b) =
            2 * a * b * (u ⬝ᵥ (M *ᵥ v)) := by ring
        _ = 0 := hquad
    have habzero : a * b = 0 :=
      (mul_eq_zero.mp hfactor).resolve_left (mul_ne_zero (by norm_num) hpair)
    rcases mul_eq_zero.mp habzero with ha | hb
    · have hwv : w = b • v := by
        simpa [ha] using hab.symm
      have hb0 : b ≠ 0 := by
        intro hb
        apply hw
        simpa [hb] using hwv
      exact hvw ⟨b, hb0, hwv⟩
    · have hwu : w = a • u := by
        simpa [hb] using hab.symm
      have ha0 : a ≠ 0 := by
        intro ha
        apply hw
        simpa [ha] using hwu
      exact huw ⟨a, ha0, hwu⟩
  have hLI₃ : LinearIndependent ℝ ![u, v, w] := by
    simpa using hLI.finSnoc hnotmem
  rw [triple_product_eq_det]
  let A : Matrix (Fin 3) (Fin 3) ℝ := fun i => ![u, v, w] i
  have hLIrows : LinearIndependent ℝ A.row := by
    simpa [A, Matrix.row] using hLI₃
  have hunit : IsUnit A :=
    Matrix.linearIndependent_rows_iff_isUnit.mp hLIrows
  have hdetA : A.det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp hunit).ne_zero
  simpa [A] using hdetA

lemma cramer (a₁ a₂ a₃ v : Fin 3 → ℝ) :
    (a₁ ⬝ᵥ (a₂ ⨯₃ a₃)) • v =
      combine a₁ a₂ a₃
        (v ⬝ᵥ (a₂ ⨯₃ a₃))
        (a₁ ⬝ᵥ (v ⨯₃ a₃))
        (a₁ ⬝ᵥ (a₂ ⨯₃ v)) := by
  simp_rw [cross_apply, vec3_dotProduct]
  ext i
  fin_cases i <;>
    simp only [Fin.isValue, Fin.reduceFinMk, combine, Matrix.cons_val, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul] <;>
    ring

lemma quadratic_combine (M : Matrix (Fin 3) (Fin 3) ℝ) (hM : M.IsSymm)
    (a₁ a₂ a₃ : Fin 3 → ℝ) (x y z : ℝ) :
    (combine a₁ a₂ a₃ x y z) ⬝ᵥ (M *ᵥ (combine a₁ a₂ a₃ x y z)) =
      x ^ 2 * (a₁ ⬝ᵥ (M *ᵥ a₁)) +
      y ^ 2 * (a₂ ⬝ᵥ (M *ᵥ a₂)) +
      z ^ 2 * (a₃ ⬝ᵥ (M *ᵥ a₃)) +
      2 * ((a₂ ⬝ᵥ (M *ᵥ a₃)) * y * z +
        (a₁ ⬝ᵥ (M *ᵥ a₃)) * z * x +
        (a₁ ⬝ᵥ (M *ᵥ a₂)) * x * y) := by
  simp only [combine, mulVec, dotProduct, Fin.sum_univ_three, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  rw [hM.apply 0 1, hM.apply 0 2, hM.apply 1 2]
  ring

lemma coordinate_conic (M : Matrix (Fin 3) (Fin 3) ℝ) (hM : M.IsSymm)
    (a₁ a₂ a₃ v : Fin 3 → ℝ) (D x y z : ℝ)
    (hA₁ : a₁ ⬝ᵥ (M *ᵥ a₁) = 0) (hA₂ : a₂ ⬝ᵥ (M *ᵥ a₂) = 0)
    (hA₃ : a₃ ⬝ᵥ (M *ᵥ a₃) = 0) (hV : v ⬝ᵥ (M *ᵥ v) = 0)
    (hrep : D • v = combine a₁ a₂ a₃ x y z) :
    (a₂ ⬝ᵥ (M *ᵥ a₃)) * y * z +
      (a₁ ⬝ᵥ (M *ᵥ a₃)) * z * x +
      (a₁ ⬝ᵥ (M *ᵥ a₂)) * x * y = 0 := by
  have hscaled :
      (combine a₁ a₂ a₃ x y z) ⬝ᵥ (M *ᵥ (combine a₁ a₂ a₃ x y z)) = 0 := by
    rw [← hrep, mulVec_smul, smul_dotProduct, dotProduct_smul, hV]
    simp
  rw [quadratic_combine M hM, hA₁, hA₂, hA₃] at hscaled
  linarith

lemma reciprocal_determinant_zero (A B C : ℝ)
    (u₁ v₁ w₁ u₂ v₂ w₂ u₃ v₃ w₃ : ℝ) (hA : A ≠ 0)
    (h₁ : A * u₁ + B * v₁ + C * w₁ = 0)
    (h₂ : A * u₂ + B * v₂ + C * w₂ = 0)
    (h₃ : A * u₃ + B * v₃ + C * w₃ = 0) :
    u₃ * v₂ * w₁ - u₂ * v₃ * w₁ - u₃ * v₁ * w₂ +
      u₁ * v₃ * w₂ + u₂ * v₁ * w₃ - u₁ * v₂ * w₃ = 0 := by
  have hu₁ : u₁ = -(B * v₁ + C * w₁) / A := by
    apply (eq_div_iff hA).2
    linarith
  have hu₂ : u₂ = -(B * v₂ + C * w₂) / A := by
    apply (eq_div_iff hA).2
    linarith
  have hu₃ : u₃ = -(B * v₃ + C * w₃) / A := by
    apply (eq_div_iff hA).2
    linarith
  rw [hu₁, hu₂, hu₃]
  ring

def pascalPolynomial
    (x₁ y₁ z₁ x₂ y₂ z₂ x₃ y₃ z₃ : ℝ) : ℝ :=
  x₁ * x₂ * y₁ * z₂ * y₃ * z₃ -
  x₁ * y₁ * y₂ * z₂ * z₃ * x₃ -
  x₁ * x₂ * y₂ * z₁ * y₃ * z₃ +
  x₂ * y₁ * y₂ * z₁ * z₃ * x₃ +
  x₁ * y₂ * z₁ * z₂ * y₃ * x₃ -
  x₂ * y₁ * z₁ * z₂ * y₃ * x₃

lemma pascalPolynomial_eq_zero (A B C : ℝ)
    (x₁ y₁ z₁ x₂ y₂ z₂ x₃ y₃ z₃ : ℝ)
    (hA : A ≠ 0)
    (hx₁ : x₁ ≠ 0) (hy₁ : y₁ ≠ 0) (hz₁ : z₁ ≠ 0)
    (hx₂ : x₂ ≠ 0) (hy₂ : y₂ ≠ 0) (hz₂ : z₂ ≠ 0)
    (hx₃ : x₃ ≠ 0) (hy₃ : y₃ ≠ 0) (hz₃ : z₃ ≠ 0)
    (hq₁ : A * y₁ * z₁ + B * z₁ * x₁ + C * x₁ * y₁ = 0)
    (hq₂ : A * y₂ * z₂ + B * z₂ * x₂ + C * x₂ * y₂ = 0)
    (hq₃ : A * y₃ * z₃ + B * z₃ * x₃ + C * x₃ * y₃ = 0) :
    pascalPolynomial x₁ y₁ z₁ x₂ y₂ z₂ x₃ y₃ z₃ = 0 := by
  have hr₁ : A * x₁⁻¹ + B * y₁⁻¹ + C * z₁⁻¹ = 0 := by
    field_simp [hx₁, hy₁, hz₁]
    linear_combination hq₁
  have hr₂ : A * x₂⁻¹ + B * y₂⁻¹ + C * z₂⁻¹ = 0 := by
    field_simp [hx₂, hy₂, hz₂]
    linear_combination hq₂
  have hr₃ : A * x₃⁻¹ + B * y₃⁻¹ + C * z₃⁻¹ = 0 := by
    field_simp [hx₃, hy₃, hz₃]
    linear_combination hq₃
  have hdet := reciprocal_determinant_zero A B C
    x₁⁻¹ y₁⁻¹ z₁⁻¹ x₂⁻¹ y₂⁻¹ z₂⁻¹ x₃⁻¹ y₃⁻¹ z₃⁻¹
    hA hr₁ hr₂ hr₃
  have hfactor :
      pascalPolynomial x₁ y₁ z₁ x₂ y₂ z₂ x₃ y₃ z₃ =
        (x₁ * x₂ * x₃ * y₁ * y₂ * y₃ * z₁ * z₂ * z₃) *
          (x₃⁻¹ * y₂⁻¹ * z₁⁻¹ - x₂⁻¹ * y₃⁻¹ * z₁⁻¹ -
            x₃⁻¹ * y₁⁻¹ * z₂⁻¹ + x₁⁻¹ * y₃⁻¹ * z₂⁻¹ +
            x₂⁻¹ * y₁⁻¹ * z₃⁻¹ - x₁⁻¹ * y₂⁻¹ * z₃⁻¹) := by
    unfold pascalPolynomial
    field_simp [hx₁, hy₁, hz₁, hx₂, hy₂, hz₂, hx₃, hy₃, hz₃]
  rw [hfactor, hdet, mul_zero]

lemma collinear_combinations_of_pascalPolynomial
    (a₁ a₂ a₃ : Fin 3 → ℝ)
    (x₁ y₁ z₁ x₂ y₂ z₂ x₃ y₃ z₃ : ℝ)
    (hpoly : pascalPolynomial x₁ y₁ z₁ x₂ y₂ z₂ x₃ y₃ z₃ = 0) :
    Collinear3
      (meet a₁ (combine a₁ a₂ a₃ x₂ y₂ z₂) a₂ (combine a₁ a₂ a₃ x₁ y₁ z₁))
      (meet a₁ (combine a₁ a₂ a₃ x₃ y₃ z₃) a₃ (combine a₁ a₂ a₃ x₁ y₁ z₁))
      (meet a₂ (combine a₁ a₂ a₃ x₃ y₃ z₃) a₃
        (combine a₁ a₂ a₃ x₂ y₂ z₂)) := by
  unfold pascalPolynomial at hpoly
  unfold Collinear3 meet combine
  simp_rw [cross_apply, vec3_dotProduct]
  dsimp only [Matrix.cons_val, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  set_option maxRecDepth 100000 in
    linear_combination
      -((a₁ 0 * (a₂ 1 * a₃ 2 - a₂ 2 * a₃ 1) +
        a₁ 1 * (a₂ 2 * a₃ 0 - a₂ 0 * a₃ 2) +
        a₁ 2 * (a₂ 0 * a₃ 1 - a₂ 1 * a₃ 0)) ^ 4) * hpoly

lemma collinear_of_scaled_second_points (c : ℝ) (hc : c ≠ 0)
    (a₁ a₂ a₃ b₁ b₂ b₃ : Fin 3 → ℝ)
    (h :
      Collinear3 (meet a₁ (c • b₂) a₂ (c • b₁))
        (meet a₁ (c • b₃) a₃ (c • b₁))
        (meet a₂ (c • b₃) a₃ (c • b₂))) :
    Collinear3 (meet a₁ b₂ a₂ b₁) (meet a₁ b₃ a₃ b₁)
      (meet a₂ b₃ a₃ b₂) := by
  unfold Collinear3 meet at h ⊢
  simp_rw [cross_apply, vec3_dotProduct] at h ⊢
  dsimp only [Matrix.cons_val, Pi.smul_apply, smul_eq_mul] at h ⊢
  have hscaled :
      c ^ 6 *
        (((a₁ ⨯₃ b₂) ⨯₃ (a₂ ⨯₃ b₁)) ⬝ᵥ
          (((a₁ ⨯₃ b₃) ⨯₃ (a₃ ⨯₃ b₁)) ⨯₃
            ((a₂ ⨯₃ b₃) ⨯₃ (a₃ ⨯₃ b₂)))) = 0 := by
    simp_rw [cross_apply, vec3_dotProduct]
    dsimp only [Matrix.cons_val]
    linear_combination h
  have horiginal :=
    (mul_eq_zero.mp hscaled).resolve_left (pow_ne_zero 6 hc)
  simp_rw [cross_apply, vec3_dotProduct] at horiginal
  dsimp only [Matrix.cons_val] at horiginal
  exact horiginal

end Submission.Helpers
