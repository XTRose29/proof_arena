import Submission.RuelleEntropyRate
import Mathlib.Data.Nat.Pairing
import Mathlib.MeasureTheory.Function.Floor

namespace Submission.Helpers

open LeanEval.Dynamics
open MeasureTheory

/-- The countable family of rational coordinate cuts used as a spatial
generator.  Pairing encodes a coordinate (modulo two) and a rational number. -/
noncomputable def rationalCutBit (k : ℕ) (x : EucPlane) : Bool :=
  let i : Fin 2 :=
    ⟨(Nat.unpair k).1 % 2, Nat.mod_lt _ (by omega)⟩
  let q : ℚ := (Encodable.decode (α := ℚ) (Nat.unpair k).2).getD 0
  {y : EucPlane | y.ofLp i < (q : ℝ)}.indicator (fun _ => true) x

lemma measurable_rationalCutBit (k : ℕ) :
    Measurable (rationalCutBit k) := by
  apply measurable_const.indicator
  exact (isOpen_lt
    (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) _)
    continuous_const).measurableSet

lemma measurableEmbedding_rationalCutCode :
    MeasurableEmbedding (fun x : EucPlane => fun k => rationalCutBit k x) := by
  have hmeas :
      Measurable (fun x : EucPlane => fun k => rationalCutBit k x) :=
    measurable_spatialCode rationalCutBit measurable_rationalCutBit
  apply hmeas.measurableEmbedding
  intro x y hxy
  ext i
  apply le_antisymm
  · by_contra hle
    have hyx : y.ofLp i < x.ofLp i := lt_of_not_ge hle
    obtain ⟨q, hyq, hqx⟩ := exists_rat_btwn hyx
    have hbit := congrFun hxy
      (Nat.pair i.val (Encodable.encode q))
    simp only [rationalCutBit, Nat.unpair_pair,
      Encodable.encodek, Option.getD_some] at hbit
    have himod : i.val % 2 = i.val := Nat.mod_eq_of_lt i.isLt
    simp only [himod] at hbit
    have hi :
        (⟨i.val, i.isLt⟩ : Fin 2) = i := by
      exact Fin.ext rfl
    rw [hi] at hbit
    simp [Set.indicator_of_mem, Set.indicator_of_notMem, hyq,
      not_lt_of_ge hqx.le] at hbit
  · by_contra hle
    have hxy' : x.ofLp i < y.ofLp i := lt_of_not_ge hle
    obtain ⟨q, hxq, hqy⟩ := exists_rat_btwn hxy'
    have hbit := congrFun hxy
      (Nat.pair i.val (Encodable.encode q))
    simp only [rationalCutBit, Nat.unpair_pair,
      Encodable.encodek, Option.getD_some] at hbit
    have himod : i.val % 2 = i.val := Nat.mod_eq_of_lt i.isLt
    simp only [himod] at hbit
    have hi :
        (⟨i.val, i.isLt⟩ : Fin 2) = i := by
      exact Fin.ext rfl
    rw [hi] at hbit
    simp [Set.indicator_of_mem, Set.indicator_of_notMem, hxq,
      not_lt_of_ge hqy.le] at hbit

/-- Integer square-grid coordinates at mesh `r`. -/
noncomputable def squareGridIndex (r : ℝ) (x : EucPlane) : ℤ × ℤ :=
  (⌊x.ofLp 0 / r⌋, ⌊x.ofLp 1 / r⌋)

lemma measurable_squareGridIndex (r : ℝ) :
    Measurable (squareGridIndex r) := by
  apply Measurable.prod
  · exact ((PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0).measurable
      |>.div_const r).floor
  · exact ((PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1).measurable
      |>.div_const r).floor

/-- A finite square-grid observation, with all grid squares outside `box`
collected into one overflow symbol. -/
noncomputable def squareGridObservation
    (r : ℝ) (box : Finset (ℤ × ℤ)) (x : EucPlane) : Option ↥box :=
  if h : squareGridIndex r x ∈ box then
    some ⟨squareGridIndex r x, h⟩
  else
    none

instance instMeasurableSpaceSquareGridObservation
    (box : Finset (ℤ × ℤ)) : MeasurableSpace (Option ↥box) := ⊤

instance instMeasurableSingletonClassSquareGridObservation
    (box : Finset (ℤ × ℤ)) :
    MeasurableSingletonClass (Option ↥box) := ⟨fun _ => trivial⟩

lemma measurable_squareGridObservation (r : ℝ) (box : Finset (ℤ × ℤ)) :
    Measurable (squareGridObservation r box) := by
  have hclip : Measurable (fun z : ℤ × ℤ =>
      if h : z ∈ box then some (⟨z, h⟩ : ↥box) else none) :=
    measurable_of_countable _
  exact hclip.comp (measurable_squareGridIndex r)

lemma squareGridObservation_eq_some_iff
    (r : ℝ) (box : Finset (ℤ × ℤ)) (x : EucPlane) (q : ↥box) :
    squareGridObservation r box x = some q ↔ squareGridIndex r x = q.1 := by
  classical
  simp only [squareGridObservation]
  split_ifs with hx
  · simp only [Option.some.injEq]
    constructor
    · exact fun h => congrArg Subtype.val h
    · exact fun h => Subtype.ext h
  · constructor
    · simp
    · intro h
      exact (hx (h.symm ▸ q.2)).elim

lemma abs_sub_lt_of_floor_div_eq
    {r a b : ℝ} (hr : 0 < r)
    (hfloor : ⌊a / r⌋ = ⌊b / r⌋) :
    |a - b| < r := by
  have hfloor_real :
      ((⌊a / r⌋ : ℤ) : ℝ) = ((⌊b / r⌋ : ℤ) : ℝ) :=
    congrArg (fun z : ℤ => (z : ℝ)) hfloor
  have halow : ((⌊a / r⌋ : ℤ) : ℝ) ≤ a / r := Int.floor_le _
  have hahigh : a / r < ((⌊b / r⌋ : ℤ) : ℝ) + 1 := by
    rw [← hfloor_real]
    exact Int.lt_floor_add_one _
  have hblow : ((⌊b / r⌋ : ℤ) : ℝ) ≤ b / r := Int.floor_le _
  have hbhigh : b / r < ((⌊a / r⌋ : ℤ) : ℝ) + 1 := by
    rw [hfloor_real]
    exact Int.lt_floor_add_one _
  rw [abs_lt]
  constructor
  · have hdiv : (b - a) / r < 1 := by
      rw [sub_div]
      linarith
    have hba : b - a < r := by
      simpa using (div_lt_iff₀ hr).mp hdiv
    linarith
  · have hdiv : (a - b) / r < 1 := by
      rw [sub_div]
      linarith
    simpa using (div_lt_iff₀ hr).mp hdiv

lemma abs_coordinate_sub_lt_of_squareGridIndex_eq
    {r : ℝ} (hr : 0 < r) {x y : EucPlane}
    (hxy : squareGridIndex r x = squareGridIndex r y) (i : Fin 2) :
    |x.ofLp i - y.ofLp i| < r := by
  fin_cases i
  · change |x.ofLp (0 : Fin 2) - y.ofLp 0| < r
    exact abs_sub_lt_of_floor_div_eq hr (congrArg Prod.fst hxy)
  · change |x.ofLp (1 : Fin 2) - y.ofLp 1| < r
    exact abs_sub_lt_of_floor_div_eq hr (congrArg Prod.snd hxy)

lemma norm_sub_lt_two_mul_of_squareGridIndex_eq
    {r : ℝ} (hr : 0 < r) {x y : EucPlane}
    (hxy : squareGridIndex r x = squareGridIndex r y) :
    ‖x - y‖ < 2 * r := by
  have hzero := abs_coordinate_sub_lt_of_squareGridIndex_eq hr hxy 0
  have hone := abs_coordinate_sub_lt_of_squareGridIndex_eq hr hxy 1
  have hzero_sq :
      ((x - y).ofLp 0) ^ 2 < r ^ 2 := by
    have hsq :=
      (sq_lt_sq₀ (abs_nonneg (x.ofLp 0 - y.ofLp 0)) hr.le).mpr hzero
    simpa only [PiLp.sub_apply, sq_abs] using hsq
  have hone_sq :
      ((x - y).ofLp 1) ^ 2 < r ^ 2 := by
    have hsq :=
      (sq_lt_sq₀ (abs_nonneg (x.ofLp 1 - y.ofLp 1)) hr.le).mpr hone
    simpa only [PiLp.sub_apply, sq_abs] using hsq
  rw [← sq_lt_sq₀ (norm_nonneg _) (by positivity)]
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  nlinarith [sq_nonneg r]

end Submission.Helpers
