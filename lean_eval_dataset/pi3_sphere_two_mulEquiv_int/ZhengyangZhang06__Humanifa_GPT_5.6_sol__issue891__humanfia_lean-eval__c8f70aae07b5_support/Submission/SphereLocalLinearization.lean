import Submission.SphereLinearBubble

open scoped unitInterval

noncomputable section

namespace Submission.SphereLocalLinearization

open Submission.SphereRegularApprox

variable {m : ℕ}

/-- The straight interpolation between a local coordinate model and its
linearization. -/
def interpolation
    (φ : (Fin (m + 1) → I) → Domain m)
    (d : SphereBubble.LocalDatum m)
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (K : ℝ)
    (z : I × (Fin (m + 1) → I)) : Domain m :=
  (1 - (z.1 : ℝ)) • φ z.2 +
    (z.1 : ℝ) •
      (K • A.toEuclideanLin (SphereBubble.localCoordinates d z.2))

theorem continuous_interpolation
    (φ : (Fin (m + 1) → I) → Domain m)
    (hφ : Continuous φ)
    (d : SphereBubble.LocalDatum m)
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (K : ℝ) :
    Continuous (interpolation φ d A K) := by
  unfold interpolation
  have hlinear :
      Continuous
        (fun t : Fin (m + 1) → I =>
          K • A.toEuclideanLin
            (SphereBubble.localCoordinates d t)) :=
    (continuous_const_smul K).comp <|
      (SphereLinearBubble.continuous_matrix_apply A).comp
        (SphereBubble.continuous_localCoordinates d)
  have htime :
      Continuous (fun z : I × (Fin (m + 1) → I) =>
        (z.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  exact
    ((continuous_const.sub htime).smul
      (hφ.comp continuous_snd)).add
      (htime.smul (hlinear.comp continuous_snd))

/-- Glue the local coordinate interpolation to the constant map outside its
support ball.  The boundary lower bound is precisely what makes the gluing
continuous. -/
def homotopyMap
    (φ : (Fin (m + 1) → I) → Domain m)
    (d : SphereBubble.LocalDatum m)
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (K : ℝ)
    (z : I × (Fin (m + 1) → I)) : UnitSphere m :=
  if ‖SphereBubble.localCoordinates d z.2‖ ≤ 1 then
    SphereBubble.map m (interpolation φ d A K z)
  else
    SphereGenerator.canonicalBasepoint m

theorem continuous_homotopyMap
    (φ : (Fin (m + 1) → I) → Domain m)
    (hφ : Continuous φ)
    (d : SphereBubble.LocalDatum m)
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (K : ℝ)
    (hwall :
      ∀ (s : I) (t : Fin (m + 1) → I),
        ‖SphereBubble.localCoordinates d t‖ = 1 →
          1 ≤ ‖interpolation φ d A K (s, t)‖) :
    Continuous (homotopyMap φ d A K) := by
  let r : I × (Fin (m + 1) → I) → ℝ :=
    fun z => ‖SphereBubble.localCoordinates d z.2‖
  have hr : Continuous r :=
    ((SphereBubble.continuous_localCoordinates d).comp continuous_snd).norm
  have hinside :
      Continuous
        (fun z : I × (Fin (m + 1) → I) =>
          SphereBubble.map m (interpolation φ d A K z)) :=
    (SphereBubble.continuous_map m).comp
      (continuous_interpolation φ hφ d A K)
  change Continuous
    (fun z : I × (Fin (m + 1) → I) =>
      if r z ≤ (fun _ => (1 : ℝ)) z then
        SphereBubble.map m (interpolation φ d A K z)
      else SphereGenerator.canonicalBasepoint m)
  exact Continuous.if_le hinside continuous_const hr continuous_const
    fun z hz =>
      SphereBubble.map_eq_canonicalBasepoint_of_one_le_norm m <|
        hwall z.1 z.2 (by
          simpa only [r] using hz)

/-- A local coordinate model satisfying a quantitative boundary estimate is
homotopic, relative to the cubical boundary, to its scaled derivative
bubble. -/
def homotopyRel
    (p : GenLoop (Fin (m + 1)) (UnitSphere m)
      (SphereGenerator.canonicalBasepoint m))
    (φ : (Fin (m + 1) → I) → Domain m)
    (hφ : Continuous φ)
    (d : SphereBubble.LocalDatum m)
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (K : ℝ)
    (hK : ∀ v : Domain m, 1 ≤ ‖v‖ →
      1 ≤ ‖K • A.toEuclideanLin v‖)
    (hinside :
      ∀ t, ‖SphereBubble.localCoordinates d t‖ ≤ 1 →
        p t = SphereBubble.map m (φ t))
    (houtside :
      ∀ t, 1 ≤ ‖SphereBubble.localCoordinates d t‖ →
        p t = SphereGenerator.canonicalBasepoint m)
    (hwall :
      ∀ (s : I) (t : Fin (m + 1) → I),
        ‖SphereBubble.localCoordinates d t‖ = 1 →
          1 ≤ ‖interpolation φ d A K (s, t)‖) :
    p.1.HomotopyRel
      (SphereLinearBubble.scaledMatrixLocalGenLoop d A K hK).1
      (Cube.boundary (Fin (m + 1))) where
  toFun := homotopyMap φ d A K
  continuous_toFun :=
    continuous_homotopyMap φ hφ d A K hwall
  map_zero_left t := by
    by_cases ht :
        ‖SphereBubble.localCoordinates d t‖ ≤ 1
    · rw [homotopyMap, if_pos ht]
      calc
        SphereBubble.map m (interpolation φ d A K (0, t)) =
            SphereBubble.map m (φ t) := by
          apply congrArg (SphereBubble.map m)
          simp [interpolation]
        _ = p t := (hinside t ht).symm
    · rw [homotopyMap, if_neg ht]
      symm
      exact houtside t (le_of_not_ge ht)
  map_one_left t := by
    by_cases ht :
        ‖SphereBubble.localCoordinates d t‖ ≤ 1
    · rw [homotopyMap, if_pos ht]
      change
        SphereBubble.map m (interpolation φ d A K (1, t)) =
          SphereBubble.map m
            (K • A.toEuclideanLin
              (SphereBubble.localCoordinates d t))
      simp [interpolation]
    · rw [homotopyMap, if_neg ht]
      symm
      exact
        SphereBubble.map_eq_canonicalBasepoint_of_one_le_norm m <|
          hK _ (le_of_not_ge ht)
  prop' s t ht := by
    have hlocal :
        1 ≤ ‖SphereBubble.localCoordinates d t‖ :=
      SphereBubble.one_le_norm_localCoordinates_of_mem_boundary d t ht
    by_cases heq :
        ‖SphereBubble.localCoordinates d t‖ = 1
    · change
        (if ‖SphereBubble.localCoordinates d t‖ ≤ 1 then
          SphereBubble.map m (interpolation φ d A K (s, t))
        else SphereGenerator.canonicalBasepoint m) = p t
      rw [if_pos heq.le]
      calc
        SphereBubble.map m (interpolation φ d A K (s, t)) =
            SphereGenerator.canonicalBasepoint m :=
          SphereBubble.map_eq_canonicalBasepoint_of_one_le_norm m <|
            hwall s t heq
        _ = p t := (p.property t ht).symm
    · have hnotle :
          ¬ ‖SphereBubble.localCoordinates d t‖ ≤ 1 :=
        fun hle => heq (le_antisymm hle hlocal)
      change
        (if ‖SphereBubble.localCoordinates d t‖ ≤ 1 then
          SphereBubble.map m (interpolation φ d A K (s, t))
        else SphereGenerator.canonicalBasepoint m) = p t
      rw [if_neg hnotle]
      exact (p.property t ht).symm

theorem class_eq_or_eq_inverse
    (p : GenLoop (Fin (m + 1)) (UnitSphere m)
      (SphereGenerator.canonicalBasepoint m))
    (φ : (Fin (m + 1) → I) → Domain m)
    (hφ : Continuous φ)
    (d : SphereBubble.LocalDatum m)
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (hA : A.det ≠ 0)
    (K : ℝ)
    (hKone : 1 ≤ K)
    (hK : ∀ v : Domain m, 1 ≤ ‖v‖ →
      1 ≤ ‖K • A.toEuclideanLin v‖)
    (hinside :
      ∀ t, ‖SphereBubble.localCoordinates d t‖ ≤ 1 →
        p t = SphereBubble.map m (φ t))
    (houtside :
      ∀ t, 1 ≤ ‖SphereBubble.localCoordinates d t‖ →
        p t = SphereGenerator.canonicalBasepoint m)
    (hwall :
      ∀ (s : I) (t : Fin (m + 1) → I),
        ‖SphereBubble.localCoordinates d t‖ = 1 →
          1 ≤ ‖interpolation φ d A K (s, t)‖) :
    (Quotient.mk' p :
        HomotopyGroup.Pi (m + 1) (UnitSphere m)
          (SphereGenerator.canonicalBasepoint m)) =
        SphereGenerator.canonicalGeneratorClass m ∨
      (Quotient.mk' p :
        HomotopyGroup.Pi (m + 1) (UnitSphere m)
          (SphereGenerator.canonicalBasepoint m)) =
        (SphereGenerator.canonicalGeneratorClass m)⁻¹ := by
  have hp :
      GenLoop.Homotopic p
        (SphereLinearBubble.scaledMatrixLocalGenLoop d A K hK) :=
    ⟨homotopyRel p φ hφ d A K hK hinside houtside hwall⟩
  obtain ⟨K', hK'one, hK', hclass⟩ :=
    SphereLinearBubble.exists_scaledMatrixLocalGenLoop_classification
      d A hA
  have hscale :
      GenLoop.Homotopic
        (SphereLinearBubble.scaledMatrixLocalGenLoop d A K hK)
        (SphereLinearBubble.scaledMatrixLocalGenLoop d A K' hK') := by
    exact ⟨SphereLinearBubble.scaleMatrixHomotopyRel
      d A K K'
      (zero_lt_one.trans_le hKone)
      (zero_lt_one.trans_le hK'one)
      hK hK'⟩
  rcases hclass with hclass | hclass
  · exact Or.inl <|
      (Quotient.sound (hp.trans hscale)).trans hclass
  · exact Or.inr <|
      (Quotient.sound (hp.trans hscale)).trans hclass

end Submission.SphereLocalLinearization
