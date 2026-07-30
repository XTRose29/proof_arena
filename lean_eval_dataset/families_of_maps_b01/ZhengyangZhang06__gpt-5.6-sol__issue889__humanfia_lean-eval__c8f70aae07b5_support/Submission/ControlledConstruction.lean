import Submission.LipschitzWeights

open Set Geometry
open unitInterval

namespace Submission.ControlledConstruction

open Helpers FragmentationConstruction LipschitzWeights
open Polytope Polytope.ExposedFace
open ChainCoordinates GridDeformation MappedComplex

variable {k n : ℕ} {ι X : Type*} [MetricSpace X]
variable {U : ι → Set X}

theorem redistributedWeight_lipschitz (W : WeightSystem U n) (K : NNReal)
    (hW : ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      LipschitzWith K (fun x => cdf (W.weight x) s))
    (w : stdSimplex ℝ (Fin (k + 1))) (i : Fin (k + 1)) :
    LipschitzWith (K + K)
      (fun x => redistributedWeights (W.weight x) w i) := by
  unfold redistributedWeights
  apply (hW (prefixMass w.1 (i + 1))
    (prefixMass_nonneg w (i + 1))
    (prefixMass_le_one w (by omega))).sub
  exact hW (prefixMass w.1 i) (prefixMass_nonneg w i)
    (prefixMass_le_one w (by omega))

theorem redistribute_lipschitz (W : WeightSystem U n) (K : NNReal)
    (hW : ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      LipschitzWith K (fun x => cdf (W.weight x) s))
    (w : stdSimplex ℝ (Fin (k + 1))) :
    LipschitzWith (K + K)
      (fun x =>
        (redistribute (W.weight x) (W.nonneg x) (W.sum_eq_one x) w).1) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  apply (dist_pi_le_iff (mul_nonneg (K + K).2 dist_nonneg)).2
  intro i
  exact (redistributedWeight_lipschitz W K hW w i).dist_le_mul x y

noncomputable def decodeConstant (S : Finset (Fin k → ℝ)) : NNReal := by
  classical
  exact ∑ C : ChainIndex S,
    ‖(rankDecodeLinear S C.1 C.2).toContinuousLinearMap‖₊

theorem rankDecodeLinear_lipschitz (S : Finset (Fin k → ℝ))
    (C : ChainIndex S) :
    LipschitzWith (decodeConstant S) (rankDecodeLinear S C.1 C.2) := by
  classical
  apply (rankDecodeLinear S C.1 C.2).toContinuousLinearMap.lipschitz.weaken
  unfold decodeConstant
  exact Finset.single_le_sum
    (f := fun J : ChainIndex S =>
      ‖(rankDecodeLinear S J.1 J.2).toContinuousLinearMap‖₊)
    (fun _J _hJ => bot_le) (Finset.mem_univ C)

theorem endpointOnChain_lipschitz (W : WeightSystem U n) (K : NNReal)
    (hW : ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      LipschitzWith K (fun x => cdf (W.weight x) s))
    (S : Finset (Fin k → ℝ)) (C : ChainIndex S)
    (p : convexHull ℝ (chainVertices S C.1 : Set (Fin k → ℝ))) :
    LipschitzWith (decodeConstant S * (K + K))
      (fun x => endpointOnChain W S C (p, x)) := by
  change LipschitzWith (decodeConstant S * (K + K))
    (fun x => rankDecodeLinear S C.1 C.2
      (redistribute (W.weight x) (W.nonneg x) (W.sum_eq_one x)
        (rankCoordinates S C.1 C.2 p)).1)
  exact (rankDecodeLinear_lipschitz S C).comp
    (redistribute_lipschitz W K hW (rankCoordinates S C.1 C.2 p))

theorem endpointAmbient_lipschitz (W : WeightSystem U n) (K : NNReal)
    (hW : ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      LipschitzWith K (fun x => cdf (W.weight x) s))
    (S : Finset (Fin k → ℝ))
    (p : convexHull ℝ (S : Set (Fin k → ℝ))) :
    LipschitzWith (decodeConstant S * (K + K))
      (fun x => endpointAmbient W S (p, x)) := by
  let C := (chainChoice S p).1
  let pc : convexHull ℝ (chainVertices S C.1 : Set (Fin k → ℝ)) :=
    ⟨p.1, (chainChoice S p).2⟩
  simpa only [endpointAmbient, C, pc] using endpointOnChain_lipschitz W K hW S C pc

theorem endpoint_lipschitz (W : WeightSystem U n) (K : NNReal)
    (hW : ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      LipschitzWith K (fun x => cdf (W.weight x) s))
    (S : Finset (Fin k → ℝ))
    (p : convexHull ℝ (S : Set (Fin k → ℝ))) :
    LipschitzWith (decodeConstant S * (K + K))
      (fun x => endpoint W S (p, x)) := by
  exact (endpointAmbient_lipschitz W K hW S p).subtype_mk
    (fun x => endpointAmbient_mem W S (p, x))

theorem parameter_lipschitz (W : WeightSystem U n) (K : NNReal)
    (hW : ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      LipschitzWith K (fun x => cdf (W.weight x) s))
    (S : Finset (Fin k → ℝ)) (t : I)
    (p : convexHull ℝ (S : Set (Fin k → ℝ))) :
    LipschitzWith (decodeConstant S * (K + K))
      (fun x => parameter W S (t, p, x)) := by
  have hend := endpoint_lipschitz W K hW S p
  have hambient : LipschitzWith (decodeConstant S * (K + K))
      (fun x =>
        (1 - (t : ℝ)) • p.1 + (t : ℝ) • (endpoint W S (p, x)).1) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    calc
      dist ((1 - (t : ℝ)) • p.1 + (t : ℝ) • (endpoint W S (p, x)).1)
          ((1 - (t : ℝ)) • p.1 + (t : ℝ) • (endpoint W S (p, y)).1) =
          dist ((t : ℝ) • (endpoint W S (p, x)).1)
            ((t : ℝ) • (endpoint W S (p, y)).1) := by
        rw [dist_add_left]
      _ ≤ ‖(t : ℝ)‖ * dist (endpoint W S (p, x)) (endpoint W S (p, y)) :=
        dist_smul_le (t : ℝ) (endpoint W S (p, x)).1 (endpoint W S (p, y)).1
      _ ≤ 1 * (((decodeConstant S * (K + K) : NNReal) : ℝ) * dist x y) := by
        apply mul_le_mul
        · simpa only [Real.norm_of_nonneg t.2.1] using t.2.2
        · exact hend.dist_le_mul x y
        · exact dist_nonneg
        · exact zero_le_one
      _ = ((decodeConstant S * (K + K) : NNReal) : ℝ) * dist x y := one_mul _
  exact hambient.subtype_mk fun x =>
    (convex_convexHull ℝ (S : Set (Fin k → ℝ))) p.2
      (endpoint W S (p, x)).2 (sub_nonneg.mpr t.2.2) t.2.1 (by ring)

noncomputable def controlledFragmentation (W : WeightSystem U n)
    (S : Finset (Fin k → ℝ))
    (hn : 0 < n) (K : NNReal)
    (hW : ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      LipschitzWith K (fun x => cdf (W.weight x) s)) :
    ControlledFragmentation (P := convexHull ℝ (S : Set (Fin k → ℝ))) U
      (decodeConstant S * (K + K)) where
  toFragmentation := fragmentation W S hn
  parameter_lipschitz := parameter_lipschitz W K hW S

section Repetition

variable {X : Type*} [MetricSpace X] [CompactSpace X] [Nonempty X]
variable (D : CoverData ι X)

theorem repeatCoordinateConstant_eq_inv (M : ℕ) :
    repeatCoordinateConstant D M =
      (M : NNReal)⁻¹ * commonLipConstant D := by
  ext
  simp [repeatCoordinateConstant]

noncomputable def repetitionNumerator
    (S : Finset (Fin k → ℝ)) (L : NNReal) : NNReal :=
  L * L *
    (decodeConstant S *
      ((m D : NNReal) * commonLipConstant D +
        (m D : NNReal) * commonLipConstant D))

noncomputable def repetitionCount
    (S : Finset (Fin k → ℝ)) (L : NNReal) : ℕ :=
  Classical.choose (exists_nat_gt (repetitionNumerator D S L : ℝ))

theorem repetitionCount_spec (S : Finset (Fin k → ℝ)) (L : NNReal) :
    (repetitionNumerator D S L : ℝ) < repetitionCount D S L :=
  Classical.choose_spec (exists_nat_gt (repetitionNumerator D S L : ℝ))

theorem repetitionCount_pos (S : Finset (Fin k → ℝ)) (L : NNReal) :
    0 < repetitionCount D S L := by
  have h := repetitionCount_spec D S L
  have hnonneg : (0 : ℝ) ≤ repetitionNumerator D S L := by positivity
  exact_mod_cast lt_of_le_of_lt hnonneg h

theorem repeated_control_eq_inv_mul (S : Finset (Fin k → ℝ))
    (L : NNReal) (M : ℕ) :
    L * L *
        (decodeConstant S *
          (blockLipschitzConstant D M + blockLipschitzConstant D M)) =
      (M : NNReal)⁻¹ * repetitionNumerator D S L := by
  rw [blockLipschitzConstant, repeatCoordinateConstant_eq_inv D M]
  unfold repetitionNumerator
  ring

theorem repeated_control_small (S : Finset (Fin k → ℝ)) (L : NNReal) :
    L * L *
        (decodeConstant S *
          (blockLipschitzConstant D (repetitionCount D S L) +
            blockLipschitzConstant D (repetitionCount D S L))) < 1 := by
  let M := repetitionCount D S L
  have hM : 0 < M := repetitionCount_pos D S L
  rw [repeated_control_eq_inv_mul D S L M]
  rw [← NNReal.coe_lt_coe]
  simp only [NNReal.coe_mul, NNReal.coe_inv, NNReal.coe_natCast, NNReal.coe_one]
  rw [inv_mul_eq_div]
  exact (div_lt_one (show (0 : ℝ) < M by positivity)).mpr
    (repetitionCount_spec D S L)

end Repetition

end Submission.ControlledConstruction
