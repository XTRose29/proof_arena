import Submission.RealMatrixComponents
import Submission.SphereBubble

open scoped unitInterval

noncomputable section

namespace Submission.SphereLinearBubble

open Matrix
open Submission.SphereRegularApprox

variable {m : ℕ}

theorem continuous_matrix_apply (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) :
    Continuous (fun v : Domain m => A.toEuclideanLin v) := by
  refine (PiLp.continuous_toLp 2
    (fun _ : Fin (m + 1) => ℝ)).comp ?_
  apply continuous_pi
  intro i
  change Continuous (fun v : Domain m => ∑ j, A i j * v j)
  fun_prop

/-- A local bubble whose Euclidean coordinate is transformed by a matrix and
then by a positive scalar. -/
def scaledMatrixLocalCubicalMap
    (d : SphereBubble.LocalDatum m)
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (K : ℝ) (t : Fin (m + 1) → I) :
    UnitSphere m :=
  SphereBubble.map m
    (K • A.toEuclideanLin (SphereBubble.localCoordinates d t))

theorem continuous_scaledMatrixLocalCubicalMap
    (d : SphereBubble.LocalDatum m)
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (K : ℝ) :
    Continuous (scaledMatrixLocalCubicalMap d A K) := by
  apply (SphereBubble.continuous_map m).comp
  exact (continuous_const_smul K).comp <|
    (continuous_matrix_apply A).comp
      (SphereBubble.continuous_localCoordinates d)

/-- Bundle a scaled matrix bubble when the matrix has the required lower norm
bound on vectors of norm at least one. -/
def scaledMatrixLocalGenLoop
    (d : SphereBubble.LocalDatum m)
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (K : ℝ)
    (hK : ∀ v : Domain m, 1 ≤ ‖v‖ →
      1 ≤ ‖K • A.toEuclideanLin v‖) :
    GenLoop (Fin (m + 1)) (UnitSphere m)
      (SphereGenerator.canonicalBasepoint m) :=
  ⟨⟨scaledMatrixLocalCubicalMap d A K,
      continuous_scaledMatrixLocalCubicalMap d A K⟩,
    fun t ht =>
      SphereBubble.map_eq_canonicalBasepoint_of_one_le_norm m <|
        hK _ <|
          SphereBubble.one_le_norm_localCoordinates_of_mem_boundary
            d t ht⟩

theorem scaledMatrixLocalGenLoop_apply
    (d : SphereBubble.LocalDatum m)
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (K : ℝ)
    (hK : ∀ v : Domain m, 1 ≤ ‖v‖ →
      1 ≤ ‖K • A.toEuclideanLin v‖)
    (t : Fin (m + 1) → I) :
    scaledMatrixLocalGenLoop d A K hK t =
      SphereBubble.map m
        (K • A.toEuclideanLin
          (SphereBubble.localCoordinates d t)) :=
  rfl

private theorem matrixPathSourceBound
    {A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ}
    (p : RealMatrixComponents.SignedDiagonalPath A)
    (K : ℝ)
    (hK : ∀ (s : I) (v : Domain m), 1 ≤ ‖v‖ →
      1 ≤ ‖K • (p.path s).toEuclideanLin v‖) :
    ∀ v : Domain m, 1 ≤ ‖v‖ →
      1 ≤ ‖K • A.toEuclideanLin v‖ :=
  fun v hv => by simpa only [p.path.source] using hK 0 v hv

private theorem matrixPathTargetBound
    {A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ}
    (p : RealMatrixComponents.SignedDiagonalPath A)
    (K : ℝ)
    (hK : ∀ (s : I) (v : Domain m), 1 ≤ ‖v‖ →
      1 ≤ ‖K • (p.path s).toEuclideanLin v‖) :
    ∀ v : Domain m, 1 ≤ ‖v‖ →
      1 ≤ ‖K • (diagonal p.signs).toEuclideanLin v‖ :=
  fun v hv => by simpa only [p.path.target] using hK 1 v hv

private def matrixPathMap
    {A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ}
    (d : SphereBubble.LocalDatum m)
    (p : RealMatrixComponents.SignedDiagonalPath A)
    (K : ℝ)
    (z : I × (Fin (m + 1) → I)) :
    UnitSphere m :=
  SphereBubble.map m <|
    K • (p.path z.1).toEuclideanLin
      (SphereBubble.localCoordinates d z.2)

private theorem continuous_matrixPathMap
    {A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ}
    (d : SphereBubble.LocalDatum m)
    (p : RealMatrixComponents.SignedDiagonalPath A)
    (K : ℝ) :
    Continuous (matrixPathMap d p K) := by
  unfold matrixPathMap
  apply (SphereBubble.continuous_map m).comp
  apply (continuous_const_smul K).comp
  refine (PiLp.continuous_toLp 2
    (fun _ : Fin (m + 1) => ℝ)).comp ?_
  apply continuous_pi
  intro i
  change
    Continuous
      (fun z : I × (Fin (m + 1) → I) =>
        ∑ j, p.path z.1 i j *
          SphereBubble.localCoordinates d z.2 j)
  fun_prop

private theorem matrixPathMap_zero
    {A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ}
    (d : SphereBubble.LocalDatum m)
    (p : RealMatrixComponents.SignedDiagonalPath A)
    (K : ℝ)
    (hK : ∀ (s : I) (v : Domain m), 1 ≤ ‖v‖ →
      1 ≤ ‖K • (p.path s).toEuclideanLin v‖)
    (t : Fin (m + 1) → I) :
    matrixPathMap d p K (0, t) =
      scaledMatrixLocalGenLoop d A K
        (matrixPathSourceBound p K hK) t := by
  change
    SphereBubble.map m
        (K • (p.path 0).toEuclideanLin
          (SphereBubble.localCoordinates d t)) =
      SphereBubble.map m
        (K • A.toEuclideanLin
          (SphereBubble.localCoordinates d t))
  rw [p.path.source]

private theorem matrixPathMap_one
    {A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ}
    (d : SphereBubble.LocalDatum m)
    (p : RealMatrixComponents.SignedDiagonalPath A)
    (K : ℝ)
    (hK : ∀ (s : I) (v : Domain m), 1 ≤ ‖v‖ →
      1 ≤ ‖K • (p.path s).toEuclideanLin v‖)
    (t : Fin (m + 1) → I) :
    matrixPathMap d p K (1, t) =
      scaledMatrixLocalGenLoop d (diagonal p.signs) K
        (matrixPathTargetBound p K hK) t := by
  change
    SphereBubble.map m
        (K • (p.path 1).toEuclideanLin
          (SphereBubble.localCoordinates d t)) =
      SphereBubble.map m
        (K • (diagonal p.signs).toEuclideanLin
          (SphereBubble.localCoordinates d t))
  rw [p.path.target]

private theorem matrixPathMap_boundary
    {A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ}
    (d : SphereBubble.LocalDatum m)
    (p : RealMatrixComponents.SignedDiagonalPath A)
    (K : ℝ)
    (hK : ∀ (s : I) (v : Domain m), 1 ≤ ‖v‖ →
      1 ≤ ‖K • (p.path s).toEuclideanLin v‖)
    (s : I) (t : Fin (m + 1) → I)
    (ht : t ∈ Cube.boundary (Fin (m + 1))) :
    matrixPathMap d p K (s, t) =
      scaledMatrixLocalGenLoop d A K
        (matrixPathSourceBound p K hK) t := by
  change
    SphereBubble.map m
        (K • (p.path s).toEuclideanLin
          (SphereBubble.localCoordinates d t)) =
      SphereBubble.map m
        (K • A.toEuclideanLin
          (SphereBubble.localCoordinates d t))
  have hlocal :
      1 ≤ ‖SphereBubble.localCoordinates d t‖ :=
    SphereBubble.one_le_norm_localCoordinates_of_mem_boundary d t ht
  trans SphereGenerator.canonicalBasepoint m
  · exact SphereBubble.map_eq_canonicalBasepoint_of_one_le_norm m <|
      hK s _ hlocal
  · symm
    exact SphereBubble.map_eq_canonicalBasepoint_of_one_le_norm m <|
      matrixPathSourceBound p K hK _ hlocal

/-- Applying an invertible matrix path to a local bubble produces a
boundary-relative homotopy. -/
def matrixPathHomotopyRel
    {A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ}
    (d : SphereBubble.LocalDatum m)
    (p : RealMatrixComponents.SignedDiagonalPath A)
    (K : ℝ)
    (hK : ∀ (s : I) (v : Domain m), 1 ≤ ‖v‖ →
      1 ≤ ‖K • (p.path s).toEuclideanLin v‖) :
    (scaledMatrixLocalGenLoop d A K
      (matrixPathSourceBound p K hK)).1.HomotopyRel
      (scaledMatrixLocalGenLoop d (diagonal p.signs) K
        (matrixPathTargetBound p K hK)).1
      (Cube.boundary (Fin (m + 1))) where
  toFun := matrixPathMap d p K
  continuous_toFun := continuous_matrixPathMap d p K
  map_zero_left := matrixPathMap_zero d p K hK
  map_one_left := matrixPathMap_one d p K hK
  prop' := matrixPathMap_boundary d p K hK

theorem diagonal_toEuclideanLin_apply
    (signs : Fin (m + 1) → ℝ) (v : Domain m)
    (i : Fin (m + 1)) :
    (diagonal signs).toEuclideanLin v i = signs i * v i := by
  change ((diagonal signs) *ᵥ WithLp.ofLp v) i =
    signs i * WithLp.ofLp v i
  exact Matrix.mulVec_diagonal signs (WithLp.ofLp v) i

theorem norm_diagonal_signs
    (signs : Fin (m + 1) → ℝ)
    (hsigns : ∀ i, signs i = 1 ∨ signs i = -1)
    (v : Domain m) :
    ‖(diagonal signs).toEuclideanLin v‖ = ‖v‖ := by
  have hsquare :
      ‖(diagonal signs).toEuclideanLin v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq,
      EuclideanSpace.real_norm_sq_eq]
    apply Finset.sum_congr rfl
    intro i _
    rw [diagonal_toEuclideanLin_apply]
    rcases hsigns i with hi | hi <;> simp [hi]
  nlinarith [norm_nonneg ((diagonal signs).toEuclideanLin v),
    norm_nonneg v]

/-- Positive scaling constants satisfying the boundary lower bound can be
interpolated without changing the local matrix-bubble class. -/
def scaleMatrixHomotopyRel
    (d : SphereBubble.LocalDatum m)
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (K L : ℝ) (hKpos : 0 < K) (hLpos : 0 < L)
    (hsource : ∀ v : Domain m, 1 ≤ ‖v‖ →
      1 ≤ ‖K • A.toEuclideanLin v‖)
    (htarget : ∀ v : Domain m, 1 ≤ ‖v‖ →
      1 ≤ ‖L • A.toEuclideanLin v‖) :
    (scaledMatrixLocalGenLoop d A K hsource).1.HomotopyRel
      (scaledMatrixLocalGenLoop d A L htarget).1
      (Cube.boundary (Fin (m + 1))) where
  toFun z :=
    let c : ℝ := (1 - (z.1 : ℝ)) * K + (z.1 : ℝ) * L
    SphereBubble.map m <|
      c • A.toEuclideanLin
        (SphereBubble.localCoordinates d z.2)
  continuous_toFun := by
    apply (SphereBubble.continuous_map m).comp
    have hc :
        Continuous
          (fun z : I × (Fin (m + 1) → I) =>
            (1 - (z.1 : ℝ)) * K + (z.1 : ℝ) * L) := by
      fun_prop
    have hv :
        Continuous
          (fun z : I × (Fin (m + 1) → I) =>
            A.toEuclideanLin
              (SphereBubble.localCoordinates d z.2)) :=
      (continuous_matrix_apply A).comp <|
        (SphereBubble.continuous_localCoordinates d).comp continuous_snd
    exact hc.smul hv
  map_zero_left t := by
    change
      SphereBubble.map m
          (((1 - (0 : ℝ)) * K + (0 : ℝ) * L) •
            A.toEuclideanLin
              (SphereBubble.localCoordinates d t)) =
        SphereBubble.map m
          (K • A.toEuclideanLin
            (SphereBubble.localCoordinates d t))
    norm_num
  map_one_left t := by
    change
      SphereBubble.map m
          (((1 - (1 : ℝ)) * K + (1 : ℝ) * L) •
            A.toEuclideanLin
              (SphereBubble.localCoordinates d t)) =
        SphereBubble.map m
          (L • A.toEuclideanLin
            (SphereBubble.localCoordinates d t))
    norm_num
  prop' s t ht := by
    let c : ℝ := (1 - (s : ℝ)) * K + (s : ℝ) * L
    have hlocal :
        1 ≤ ‖SphereBubble.localCoordinates d t‖ :=
      SphereBubble.one_le_norm_localCoordinates_of_mem_boundary d t ht
    have hcpos : 0 < c := by
      dsimp only [c]
      by_cases hs : (s : ℝ) = 1
      · simp [hs, hLpos]
      · exact add_pos_of_pos_of_nonneg
          (mul_pos
            (sub_pos.mpr
              (lt_of_le_of_ne s.property.2 hs))
            hKpos)
          (mul_nonneg s.property.1 hLpos.le)
    have hcbound :
        1 ≤ ‖c • A.toEuclideanLin
          (SphereBubble.localCoordinates d t)‖ := by
      by_cases hKL : K ≤ L
      · have hKc : K ≤ c := by
          dsimp only [c]
          nlinarith [s.property.1, s.property.2,
            mul_le_mul_of_nonneg_left hKL s.property.1]
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hcpos]
        have hs := hsource _ hlocal
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hKpos] at hs
        exact
          hs.trans <|
            mul_le_mul_of_nonneg_right hKc (norm_nonneg _)
      · have hLK : L ≤ K := le_of_not_ge hKL
        have hLc : L ≤ c := by
          dsimp only [c]
          nlinarith [s.property.1, s.property.2,
            mul_le_mul_of_nonneg_left hLK
              (sub_nonneg.mpr s.property.2)]
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hcpos]
        have hs := htarget _ hlocal
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hLpos] at hs
        exact
          hs.trans <|
            mul_le_mul_of_nonneg_right hLc (norm_nonneg _)
    trans SphereGenerator.canonicalBasepoint m
    · exact SphereBubble.map_eq_canonicalBasepoint_of_one_le_norm m
        hcbound
    · exact
        ((scaledMatrixLocalGenLoop d A K hsource).property t ht).symm

/-- The unscaled local bubble obtained from a diagonal sign matrix. -/
def signLocalGenLoop
    (d : SphereBubble.LocalDatum m)
    (signs : Fin (m + 1) → ℝ)
    (hsigns : ∀ i, signs i = 1 ∨ signs i = -1) :
    GenLoop (Fin (m + 1)) (UnitSphere m)
      (SphereGenerator.canonicalBasepoint m) :=
  scaledMatrixLocalGenLoop d (diagonal signs) 1
    (fun v hv => by
      rw [one_smul, norm_diagonal_signs signs hsigns]
      exact hv)

/-- A scalar at least one can be removed from a diagonal-sign bubble without
changing its homotopy class. -/
def scaleSignHomotopyRel
    (d : SphereBubble.LocalDatum m)
    (signs : Fin (m + 1) → ℝ)
    (hsigns : ∀ i, signs i = 1 ∨ signs i = -1)
    (K : ℝ) (hK : 1 ≤ K)
    (hsource : ∀ v : Domain m, 1 ≤ ‖v‖ →
      1 ≤ ‖K • (diagonal signs).toEuclideanLin v‖) :
    (scaledMatrixLocalGenLoop d (diagonal signs) K hsource).1.HomotopyRel
      (signLocalGenLoop d signs hsigns).1
      (Cube.boundary (Fin (m + 1))) where
  toFun z :=
    let c : ℝ := (1 - (z.1 : ℝ)) * K + (z.1 : ℝ)
    SphereBubble.map m <|
      c • (diagonal signs).toEuclideanLin
        (SphereBubble.localCoordinates d z.2)
  continuous_toFun := by
    apply (SphereBubble.continuous_map m).comp
    have hc :
        Continuous
          (fun z : I × (Fin (m + 1) → I) =>
            (1 - (z.1 : ℝ)) * K + (z.1 : ℝ)) := by
      fun_prop
    have hv :
        Continuous
          (fun z : I × (Fin (m + 1) → I) =>
            (diagonal signs).toEuclideanLin
              (SphereBubble.localCoordinates d z.2)) :=
      (continuous_matrix_apply (diagonal signs)).comp <|
        (SphereBubble.continuous_localCoordinates d).comp continuous_snd
    exact hc.smul hv
  map_zero_left t := by
    change
      SphereBubble.map m
          (((1 - (0 : ℝ)) * K + (0 : ℝ)) •
            (diagonal signs).toEuclideanLin
              (SphereBubble.localCoordinates d t)) =
        SphereBubble.map m
          (K • (diagonal signs).toEuclideanLin
            (SphereBubble.localCoordinates d t))
    norm_num
  map_one_left t := by
    change
      SphereBubble.map m
          (((1 - (1 : ℝ)) * K + (1 : ℝ)) •
            (diagonal signs).toEuclideanLin
              (SphereBubble.localCoordinates d t)) =
        SphereBubble.map m
          (1 • (diagonal signs).toEuclideanLin
            (SphereBubble.localCoordinates d t))
    norm_num
  prop' s t ht := by
    let c : ℝ := (1 - (s : ℝ)) * K + (s : ℝ)
    have hc : 1 ≤ c := by
      dsimp only [c]
      nlinarith [s.property.1, s.property.2,
        mul_le_mul_of_nonneg_left hK
          (sub_nonneg.mpr s.property.2)]
    trans SphereGenerator.canonicalBasepoint m
    · apply SphereBubble.map_eq_canonicalBasepoint_of_one_le_norm
      rw [norm_smul, Real.norm_eq_abs,
        abs_of_pos (zero_lt_one.trans_le hc),
        norm_diagonal_signs signs hsigns]
      exact one_le_mul_of_one_le_of_one_le hc <|
        SphereBubble.one_le_norm_localCoordinates_of_mem_boundary d t ht
    · exact
        ((scaledMatrixLocalGenLoop d (diagonal signs) K
          hsource).property t ht).symm

/-- Moving the center and radius preserves the class of a diagonal-sign
local bubble. -/
def signLocalComparisonHomotopyRel
    (signs : Fin (m + 1) → ℝ)
    (hsigns : ∀ i, signs i = 1 ∨ signs i = -1)
    (d e : SphereBubble.LocalDatum m) :
    (signLocalGenLoop d signs hsigns).1.HomotopyRel
      (signLocalGenLoop e signs hsigns).1
      (Cube.boundary (Fin (m + 1))) where
  toFun z :=
    SphereBubble.map m <|
      (diagonal signs).toEuclideanLin <|
        SphereBubble.localCoordinates
          (SphereBubble.interpolateDatum d e z.1) z.2
  continuous_toFun := by
    apply (SphereBubble.continuous_map m).comp
    exact (continuous_matrix_apply (diagonal signs)).comp
      (SphereBubble.continuous_interpolatedLocalCoordinates d e)
  map_zero_left t := by
    change
      SphereBubble.map m
          ((diagonal signs).toEuclideanLin
            (SphereBubble.localCoordinates
              (SphereBubble.interpolateDatum d e 0) t)) =
        SphereBubble.map m
          (1 • (diagonal signs).toEuclideanLin
            (SphereBubble.localCoordinates d t))
    rw [SphereBubble.interpolateDatum_zero]
    simp
  map_one_left t := by
    change
      SphereBubble.map m
          ((diagonal signs).toEuclideanLin
            (SphereBubble.localCoordinates
              (SphereBubble.interpolateDatum d e 1) t)) =
        SphereBubble.map m
          (1 • (diagonal signs).toEuclideanLin
            (SphereBubble.localCoordinates e t))
    rw [SphereBubble.interpolateDatum_one]
    simp
  prop' s t ht := by
    trans SphereGenerator.canonicalBasepoint m
    · apply SphereBubble.map_eq_canonicalBasepoint_of_one_le_norm
      rw [norm_diagonal_signs signs hsigns]
      exact SphereBubble.one_le_norm_localCoordinates_of_mem_boundary
        (SphereBubble.interpolateDatum d e s) t ht
    · exact ((signLocalGenLoop d signs hsigns).property t ht).symm

def cubeReflection
    (S : Finset (Fin (m + 1)))
    (t : Fin (m + 1) → I) :
    Fin (m + 1) → I :=
  fun i => if i ∈ S then σ (t i) else t i

theorem continuous_cubeReflection
    (S : Finset (Fin (m + 1))) :
    Continuous (cubeReflection S) := by
  apply continuous_pi
  intro i
  by_cases hi : i ∈ S
  · simp only [cubeReflection, hi, if_true]
    fun_prop
  · simp only [cubeReflection, hi, if_false]
    fun_prop

theorem cubeReflection_mem_boundary
    (S : Finset (Fin (m + 1)))
    {t : Fin (m + 1) → I}
    (ht : t ∈ Cube.boundary (Fin (m + 1))) :
    cubeReflection S t ∈ Cube.boundary (Fin (m + 1)) := by
  obtain ⟨i, hi | hi⟩ := ht
  · by_cases hmem : i ∈ S
    · refine ⟨i, Or.inr ?_⟩
      simp [cubeReflection, hmem, hi]
    · refine ⟨i, Or.inl ?_⟩
      simp [cubeReflection, hmem, hi]
  · by_cases hmem : i ∈ S
    · refine ⟨i, Or.inl ?_⟩
      simp [cubeReflection, hmem, hi]
    · refine ⟨i, Or.inr ?_⟩
      simp [cubeReflection, hmem, hi]

/-- Precompose a generalized loop by reflections in a finite set of cube
coordinates. -/
def reflectGenLoop
    (S : Finset (Fin (m + 1)))
    (p : GenLoop (Fin (m + 1)) (UnitSphere m)
      (SphereGenerator.canonicalBasepoint m)) :
    GenLoop (Fin (m + 1)) (UnitSphere m)
      (SphereGenerator.canonicalBasepoint m) :=
  ⟨⟨fun t => p (cubeReflection S t),
      p.1.continuous.comp (continuous_cubeReflection S)⟩,
    fun t ht => p.property (cubeReflection S t)
      (cubeReflection_mem_boundary S ht)⟩

theorem reflectGenLoop_empty
    (p : GenLoop (Fin (m + 1)) (UnitSphere m)
      (SphereGenerator.canonicalBasepoint m)) :
    reflectGenLoop ∅ p = p := by
  ext t
  rfl

theorem reflectGenLoop_insert
    (p : GenLoop (Fin (m + 1)) (UnitSphere m)
      (SphereGenerator.canonicalBasepoint m))
    (S : Finset (Fin (m + 1))) (i : Fin (m + 1))
    (hi : i ∉ S) :
    reflectGenLoop (insert i S) p =
      GenLoop.symmAt i (reflectGenLoop S p) := by
  apply GenLoop.ext
  intro t
  simp only [reflectGenLoop, GenLoop.symmAt, GenLoop.coe_copy]
  apply congrArg p
  funext j
  by_cases hji : j = i
  · subst j
    simp [cubeReflection, hi]
  · simp [cubeReflection, hji]

private def loopClass
    (p : GenLoop (Fin (m + 1)) (UnitSphere m)
      (SphereGenerator.canonicalBasepoint m)) :
    HomotopyGroup.Pi (m + 1) (UnitSphere m)
      (SphereGenerator.canonicalBasepoint m) :=
  Quotient.mk' p

private theorem loopClass_cubicalGenLoop (m : ℕ) :
    loopClass (SphereBubble.cubicalGenLoop m) =
      SphereGenerator.canonicalGeneratorClass m := by
  change SphereBubble.bubbleClass m =
    SphereGenerator.canonicalGeneratorClass m
  exact SphereBubble.class_eq_canonicalGeneratorClass m

theorem reflectGenLoop_class_eq_or_eq_inverse
    (S : Finset (Fin (m + 1)))
    (p : GenLoop (Fin (m + 1)) (UnitSphere m)
      (SphereGenerator.canonicalBasepoint m)) :
    loopClass (reflectGenLoop S p) = loopClass p ∨
      loopClass (reflectGenLoop S p) = (loopClass p)⁻¹ := by
  classical
  induction S using Finset.induction with
  | empty =>
      exact Or.inl (by rw [reflectGenLoop_empty])
  | @insert i S hi ih =>
      have hclass :
          loopClass (reflectGenLoop (insert i S) p) =
            (loopClass (reflectGenLoop S p))⁻¹ := by
        rw [reflectGenLoop_insert p S i hi]
        exact (HomotopyGroup.inv_spec
          (X := UnitSphere m) (i := i)).symm
      rcases ih with ih | ih
      · exact Or.inr (hclass.trans (congrArg Inv.inv ih))
      · exact Or.inl <| hclass.trans <| by
          rw [ih, inv_inv]

def negativeSet
    (signs : Fin (m + 1) → ℝ) :
    Finset (Fin (m + 1)) :=
  Finset.univ.filter fun i => signs i = -1

theorem signLocalGenLoop_standardDatum
    (signs : Fin (m + 1) → ℝ)
    (hsigns : ∀ i, signs i = 1 ∨ signs i = -1) :
    signLocalGenLoop (SphereBubble.standardDatum m) signs hsigns =
      reflectGenLoop (negativeSet signs) (SphereBubble.cubicalGenLoop m) := by
  apply GenLoop.ext
  intro t
  apply congrArg (SphereBubble.map m)
  apply PiLp.ext
  intro i
  rw [one_smul, diagonal_toEuclideanLin_apply,
    SphereBubble.localCoordinates_standardDatum]
  rcases hsigns i with hi | hi
  · have himem : i ∉ negativeSet signs := by
      norm_num [negativeSet, hi]
    simp [cubeReflection, himem, hi,
      SphereGenerator.centered_apply]
  · have himem : i ∈ negativeSet signs := by
      simp [negativeSet, hi]
    simp [cubeReflection, himem, hi,
      SphereGenerator.centered_apply, unitInterval.coe_symm_eq]
    ring

theorem signLocalGenLoop_class_eq_or_eq_inverse
    (d : SphereBubble.LocalDatum m)
    (signs : Fin (m + 1) → ℝ)
    (hsigns : ∀ i, signs i = 1 ∨ signs i = -1) :
    loopClass (signLocalGenLoop d signs hsigns) =
        SphereGenerator.canonicalGeneratorClass m ∨
      loopClass (signLocalGenLoop d signs hsigns) =
        (SphereGenerator.canonicalGeneratorClass m)⁻¹ := by
  have hdatum :
      GenLoop.Homotopic
        (signLocalGenLoop d signs hsigns)
        (signLocalGenLoop (SphereBubble.standardDatum m)
          signs hsigns) :=
    ⟨signLocalComparisonHomotopyRel signs hsigns d
      (SphereBubble.standardDatum m)⟩
  have hstandard :=
    reflectGenLoop_class_eq_or_eq_inverse
      (negativeSet signs) (SphereBubble.cubicalGenLoop m)
  rw [← signLocalGenLoop_standardDatum signs hsigns] at hstandard
  rw [loopClass_cubicalGenLoop] at hstandard
  rcases hstandard with hstandard | hstandard
  · exact Or.inl ((Quotient.sound hdatum).trans hstandard)
  · exact Or.inr ((Quotient.sound hdatum).trans hstandard)

/-- The local bubble of any invertible real matrix represents either the
canonical generator or its inverse, after one harmless positive rescaling. -/
theorem exists_scaledMatrixLocalGenLoop_classification
    (d : SphereBubble.LocalDatum m)
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (hA : A.det ≠ 0) :
    ∃ (K : ℝ) (_hKone : 1 ≤ K)
      (hK : ∀ v : Domain m, 1 ≤ ‖v‖ →
        1 ≤ ‖K • A.toEuclideanLin v‖),
      (Quotient.mk' (scaledMatrixLocalGenLoop d A K hK) :
          HomotopyGroup.Pi (m + 1) (UnitSphere m)
            (SphereGenerator.canonicalBasepoint m)) =
          SphereGenerator.canonicalGeneratorClass m ∨
        (Quotient.mk' (scaledMatrixLocalGenLoop d A K hK) :
          HomotopyGroup.Pi (m + 1) (UnitSphere m)
            (SphereGenerator.canonicalBasepoint m)) =
          (SphereGenerator.canonicalGeneratorClass m)⁻¹ := by
  obtain ⟨p⟩ :=
    RealMatrixComponents.exists_signedDiagonalPath A hA
  obtain ⟨K, hKone, hKpath⟩ := p.exists_uniform_scale
  let hKsource : ∀ v : Domain m, 1 ≤ ‖v‖ →
      1 ≤ ‖K • A.toEuclideanLin v‖ :=
    fun v hv => by simpa using hKpath 0 v hv
  let hKtarget : ∀ v : Domain m, 1 ≤ ‖v‖ →
      1 ≤ ‖K • (diagonal p.signs).toEuclideanLin v‖ :=
    fun v hv => by simpa using hKpath 1 v hv
  have hpath :
      GenLoop.Homotopic
        (scaledMatrixLocalGenLoop d A K hKsource)
        (scaledMatrixLocalGenLoop d (diagonal p.signs) K
          hKtarget) :=
    ⟨matrixPathHomotopyRel d p K hKpath⟩
  have hscale :
      GenLoop.Homotopic
        (scaledMatrixLocalGenLoop d (diagonal p.signs) K
          hKtarget)
        (signLocalGenLoop d p.signs p.signs_eq_one_or_neg_one) :=
    ⟨scaleSignHomotopyRel d p.signs p.signs_eq_one_or_neg_one
      K hKone hKtarget⟩
  have hsign :=
    signLocalGenLoop_class_eq_or_eq_inverse
      d p.signs p.signs_eq_one_or_neg_one
  refine ⟨K, hKone, hKsource, ?_⟩
  rcases hsign with hsign | hsign
  · exact Or.inl <|
      (Quotient.sound (hpath.trans hscale)).trans hsign
  · exact Or.inr <|
      (Quotient.sound (hpath.trans hscale)).trans hsign

end Submission.SphereLinearBubble
