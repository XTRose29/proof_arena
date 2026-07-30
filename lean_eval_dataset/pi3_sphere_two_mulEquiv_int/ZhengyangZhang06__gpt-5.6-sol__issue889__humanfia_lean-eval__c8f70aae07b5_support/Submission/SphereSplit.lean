import Submission.SphereUpperChart

open scoped unitInterval

noncomputable section

namespace Submission.SphereSplit

open Set

variable {N X : Type*} [TopologicalSpace X] [DecidableEq N]
variable {x : X}

/-- Affinely identify the unit interval with the interval to the left of a
cut. -/
def leftCoordinate (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1)
    (t : I) : I :=
  ⟨c * (t : ℝ), by
    constructor
    · exact mul_nonneg hc0.le t.property.1
    · exact (mul_le_of_le_one_right hc0.le t.property.2).trans hc1.le⟩

/-- Affinely identify the unit interval with the interval to the right of a
cut. -/
def rightCoordinate (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1)
    (t : I) : I :=
  ⟨c + (1 - c) * (t : ℝ), by
    constructor
    · exact add_nonneg hc0.le <|
        mul_nonneg (sub_nonneg.mpr hc1.le) t.property.1
    · have hmul :
          (1 - c) * (t : ℝ) ≤ (1 - c) * 1 :=
        mul_le_mul_of_nonneg_left t.property.2
          (sub_nonneg.mpr hc1.le)
      calc
        c + (1 - c) * (t : ℝ) ≤ c + (1 - c) * 1 :=
          add_le_add le_rfl hmul
        _ = 1 := by ring⟩

@[simp]
theorem leftCoordinate_zero (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) :
    leftCoordinate c hc0 hc1 0 = 0 := by
  apply Subtype.ext
  simp [leftCoordinate]

@[simp]
theorem leftCoordinate_one (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) :
    (leftCoordinate c hc0 hc1 1 : ℝ) = c := by
  simp [leftCoordinate]

@[simp]
theorem rightCoordinate_zero (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) :
    (rightCoordinate c hc0 hc1 0 : ℝ) = c := by
  simp [rightCoordinate]

@[simp]
theorem rightCoordinate_one (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) :
    rightCoordinate c hc0 hc1 1 = 1 := by
  apply Subtype.ext
  simp [rightCoordinate]

theorem continuous_leftCoordinate (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) :
    Continuous (leftCoordinate c hc0 hc1) := by
  apply Continuous.subtype_mk
  fun_prop

theorem continuous_rightCoordinate (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) :
    Continuous (rightCoordinate c hc0 hc1) := by
  apply Continuous.subtype_mk
  fun_prop

/-- Rescale a cube onto the part to the left of a coordinate hyperplane. -/
def leftCube (i : N) (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1)
    (t : N → I) : N → I :=
  Function.update t i (leftCoordinate c hc0 hc1 (t i))

/-- Rescale a cube onto the part to the right of a coordinate hyperplane. -/
def rightCube (i : N) (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1)
    (t : N → I) : N → I :=
  Function.update t i (rightCoordinate c hc0 hc1 (t i))

theorem continuous_leftCube (i : N) (c : ℝ)
    (hc0 : 0 < c) (hc1 : c < 1) :
    Continuous (leftCube i c hc0 hc1) := by
  apply continuous_pi
  intro j
  by_cases hji : j = i
  · subst j
    simp only [leftCube, Function.update_self]
    exact (continuous_leftCoordinate c hc0 hc1).comp (continuous_apply i)
  · simp only [leftCube, Function.update_of_ne hji]
    exact continuous_apply j

theorem continuous_rightCube (i : N) (c : ℝ)
    (hc0 : 0 < c) (hc1 : c < 1) :
    Continuous (rightCube i c hc0 hc1) := by
  apply continuous_pi
  intro j
  by_cases hji : j = i
  · subst j
    simp only [rightCube, Function.update_self]
    exact (continuous_rightCoordinate c hc0 hc1).comp (continuous_apply i)
  · simp only [rightCube, Function.update_of_ne hji]
    exact continuous_apply j

/-- Restrict a cubical loop to the left of a hyperplane on which it is
constant. -/
def leftGenLoop (p : GenLoop N X x) (i : N)
    (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1)
    (hcut : ∀ t, (t i : ℝ) = c → p t = x) :
    GenLoop N X x :=
  ⟨⟨fun t => p (leftCube i c hc0 hc1 t),
      p.1.continuous.comp (continuous_leftCube i c hc0 hc1)⟩,
    fun t ht => by
      obtain ⟨j, hj | hj⟩ := ht
      · by_cases hji : j = i
        · subst j
          have hleft :
              leftCube i c hc0 hc1 t ∈ Cube.boundary N :=
            ⟨i, Or.inl (by simp [leftCube, hj])⟩
          exact p.property _ hleft
        · exact p.property _ ⟨j, Or.inl (by
            simp [leftCube, Function.update_of_ne hji, hj])⟩
      · by_cases hji : j = i
        · subst j
          apply hcut
          simp [leftCube, hj]
        · exact p.property _ ⟨j, Or.inr (by
            simp [leftCube, Function.update_of_ne hji, hj])⟩⟩

/-- Restrict a cubical loop to the right of a hyperplane on which it is
constant. -/
def rightGenLoop (p : GenLoop N X x) (i : N)
    (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1)
    (hcut : ∀ t, (t i : ℝ) = c → p t = x) :
    GenLoop N X x :=
  ⟨⟨fun t => p (rightCube i c hc0 hc1 t),
      p.1.continuous.comp (continuous_rightCube i c hc0 hc1)⟩,
    fun t ht => by
      obtain ⟨j, hj | hj⟩ := ht
      · by_cases hji : j = i
        · subst j
          apply hcut
          simp [rightCube, hj]
        · exact p.property _ ⟨j, Or.inl (by
            simp [rightCube, Function.update_of_ne hji, hj])⟩
      · by_cases hji : j = i
        · subst j
          have hright :
              rightCube i c hc0 hc1 t ∈ Cube.boundary N :=
            ⟨i, Or.inr (by simp [rightCube, hj])⟩
          exact p.property _ hright
        · exact p.property _ ⟨j, Or.inr (by
            simp [rightCube, Function.update_of_ne hji, hj])⟩⟩

/-- The underlying real-valued piecewise-linear reparametrization. -/
def splitValue (c : ℝ) (t : I) : ℝ :=
  if (t : ℝ) ≤ 1 / 2 then
    2 * c * (t : ℝ)
  else
    c + (1 - c) * (2 * (t : ℝ) - 1)

theorem splitValue_mem (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1)
    (t : I) :
    splitValue c t ∈ Set.Icc (0 : ℝ) 1 := by
  rw [Set.mem_Icc]
  unfold splitValue
  split_ifs with ht
  · constructor
    · exact mul_nonneg (mul_nonneg (by norm_num) hc0.le) t.property.1
    · calc
        2 * c * (t : ℝ) = c * (2 * (t : ℝ)) := by ring
        _ ≤ c * 1 :=
          mul_le_mul_of_nonneg_left (by linarith) hc0.le
        _ ≤ 1 := by simpa using hc1.le
  · constructor
    · exact add_nonneg hc0.le <|
        mul_nonneg (sub_nonneg.mpr hc1.le)
          (by linarith [lt_of_not_ge ht])
    · have htone : 2 * (t : ℝ) - 1 ≤ 1 := by
        linarith [t.property.2]
      have hmul :
          (1 - c) * (2 * (t : ℝ) - 1) ≤ (1 - c) * 1 :=
        mul_le_mul_of_nonneg_left htone
          (sub_nonneg.mpr hc1.le)
      calc
        c + (1 - c) * (2 * (t : ℝ) - 1) ≤
            c + (1 - c) * 1 :=
          add_le_add le_rfl hmul
        _ = 1 := by ring

/-- The piecewise-linear reparametrization associated to a cut. -/
def splitCoordinate (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1)
    (t : I) : I :=
  ⟨splitValue c t, splitValue_mem c hc0 hc1 t⟩

@[simp]
theorem splitCoordinate_zero (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) :
    splitCoordinate c hc0 hc1 0 = 0 := by
  apply Subtype.ext
  norm_num [splitCoordinate, splitValue]

@[simp]
theorem splitCoordinate_one (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) :
    splitCoordinate c hc0 hc1 1 = 1 := by
  apply Subtype.ext
  norm_num [splitCoordinate, splitValue]

theorem continuous_splitCoordinate (c : ℝ)
    (hc0 : 0 < c) (hc1 : c < 1) :
    Continuous (splitCoordinate c hc0 hc1) := by
  apply Continuous.subtype_mk
  unfold splitValue
  apply Continuous.if_le (by fun_prop) (by fun_prop)
    continuous_subtype_val continuous_const
  intro t ht
  rw [ht]
  ring

def splitCube (i : N) (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1)
    (t : N → I) : N → I :=
  Function.update t i (splitCoordinate c hc0 hc1 (t i))

theorem continuous_splitCube (i : N) (c : ℝ)
    (hc0 : 0 < c) (hc1 : c < 1) :
    Continuous (splitCube i c hc0 hc1) := by
  apply continuous_pi
  intro j
  by_cases hji : j = i
  · subst j
    simp only [splitCube, Function.update_self]
    exact (continuous_splitCoordinate c hc0 hc1).comp (continuous_apply i)
  · simp only [splitCube, Function.update_of_ne hji]
    exact continuous_apply j

/-- Interpolate between the identity cube parametrization and a split
parametrization. -/
def splitHomotopyCube (i : N) (c : ℝ)
    (hc0 : 0 < c) (hc1 : c < 1)
    (z : I × (N → I)) : N → I :=
  fun j =>
    if j = i then
      Icc.convexComb (z.2 i)
        (splitCoordinate c hc0 hc1 (z.2 i)) z.1
    else z.2 j

theorem continuous_splitHomotopyCube (i : N) (c : ℝ)
    (hc0 : 0 < c) (hc1 : c < 1) :
    Continuous (splitHomotopyCube i c hc0 hc1) := by
  apply continuous_pi
  intro j
  by_cases hji : j = i
  · subst j
    simp only [splitHomotopyCube, if_pos]
    have ht : Continuous
        (fun z : I × (N → I) => z.2 i) :=
      (continuous_apply i).comp continuous_snd
    have hs : Continuous
        (fun z : I × (N → I) =>
          splitCoordinate c hc0 hc1 (z.2 i)) :=
      (continuous_splitCoordinate c hc0 hc1).comp ht
    have hu : Continuous
        (fun z : I × (N → I) => z.1) :=
      continuous_fst
    apply Continuous.subtype_mk
    change Continuous
      (fun z : I × (N → I) =>
        (1 - (z.1 : ℝ)) * (z.2 i : ℝ) +
          (z.1 : ℝ) *
            (splitCoordinate c hc0 hc1 (z.2 i) : ℝ))
    exact
      (continuous_const.sub (continuous_subtype_val.comp hu)).mul
          (continuous_subtype_val.comp ht) |>.add <|
        (continuous_subtype_val.comp hu).mul
          (continuous_subtype_val.comp hs)
  · simp only [splitHomotopyCube, if_neg hji]
    exact (continuous_apply j).comp continuous_snd

@[simp]
theorem splitHomotopyCube_zero (i : N) (c : ℝ)
    (hc0 : 0 < c) (hc1 : c < 1) (t : N → I) :
    splitHomotopyCube i c hc0 hc1 (0, t) = t := by
  ext j
  by_cases hji : j = i
  · subst j
    simp [splitHomotopyCube]
  · simp [splitHomotopyCube, hji]

@[simp]
theorem splitHomotopyCube_one (i : N) (c : ℝ)
    (hc0 : 0 < c) (hc1 : c < 1) (t : N → I) :
    splitHomotopyCube i c hc0 hc1 (1, t) =
      splitCube i c hc0 hc1 t := by
  ext j
  by_cases hji : j = i
  · subst j
    simp [splitHomotopyCube, splitCube]
  · simp [splitHomotopyCube, splitCube, hji]

theorem splitHomotopyCube_mem_boundary (i : N) (c : ℝ)
    (hc0 : 0 < c) (hc1 : c < 1) (s : I)
    {t : N → I} (ht : t ∈ Cube.boundary N) :
    splitHomotopyCube i c hc0 hc1 (s, t) ∈ Cube.boundary N := by
  obtain ⟨j, hj | hj⟩ := ht
  · by_cases hji : j = i
    · subst j
      exact ⟨i, Or.inl (by simp [splitHomotopyCube, hj])⟩
    · exact ⟨j, Or.inl (by simp [splitHomotopyCube, hji, hj])⟩
  · by_cases hji : j = i
    · subst j
      exact ⟨i, Or.inr (by simp [splitHomotopyCube, hj])⟩
    · exact ⟨j, Or.inr (by simp [splitHomotopyCube, hji, hj])⟩

theorem splitCube_apply_of_le (i : N) (c : ℝ)
    (hc0 : 0 < c) (hc1 : c < 1) (t : N → I)
    (ht : (t i : ℝ) ≤ 1 / 2) :
    splitCube i c hc0 hc1 t =
      leftCube i c hc0 hc1
        (Function.update t i
          (projIcc 0 1 zero_le_one (2 * (t i : ℝ)))) := by
  ext j
  by_cases hji : j = i
  · subst j
    simp only [splitCube, leftCube, Function.update_self]
    simp only [splitCoordinate, splitValue, if_pos ht, leftCoordinate]
    rw [coe_projIcc,
      min_eq_right (by linarith [(t i).property.1]),
      max_eq_right (by linarith [(t i).property.1])]
    ring
  · simp [splitCube, leftCube, hji]

theorem splitCube_apply_of_not_le (i : N) (c : ℝ)
    (hc0 : 0 < c) (hc1 : c < 1) (t : N → I)
    (ht : ¬(t i : ℝ) ≤ 1 / 2) :
    splitCube i c hc0 hc1 t =
      rightCube i c hc0 hc1
        (Function.update t i
          (projIcc 0 1 zero_le_one (2 * (t i : ℝ) - 1))) := by
  ext j
  by_cases hji : j = i
  · subst j
    simp only [splitCube, rightCube, Function.update_self]
    simp only [splitCoordinate, splitValue, if_neg ht, rightCoordinate]
    rw [coe_projIcc,
      min_eq_right (by linarith [(t i).property.2]),
      max_eq_right (by linarith [lt_of_not_ge ht])]
  · simp [splitCube, rightCube, hji]

/-- Cutting a cubical loop along a hyperplane on which it is constant
expresses its class as the concatenation of its two restrictions. -/
theorem homotopic_transAt_restrictions
    (p : GenLoop N X x) (i : N)
    (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1)
    (hcut : ∀ t, (t i : ℝ) = c → p t = x) :
    GenLoop.Homotopic p
      (GenLoop.transAt i
        (leftGenLoop p i c hc0 hc1 hcut)
        (rightGenLoop p i c hc0 hc1 hcut)) := by
  let q := GenLoop.transAt i
    (leftGenLoop p i c hc0 hc1 hcut)
    (rightGenLoop p i c hc0 hc1 hcut)
  have hq :
      ∀ t, q t = p (splitCube i c hc0 hc1 t) := by
    intro t
    change
      GenLoop.transAt i
          (leftGenLoop p i c hc0 hc1 hcut)
          (rightGenLoop p i c hc0 hc1 hcut) t =
        p (splitCube i c hc0 hc1 t)
    simp only [GenLoop.transAt, GenLoop.coe_copy]
    split_ifs with ht
    · change
        p (leftCube i c hc0 hc1
            (Function.update t i
              (projIcc 0 1 zero_le_one (2 * (t i : ℝ))))) =
          p (splitCube i c hc0 hc1 t)
      exact congrArg p (splitCube_apply_of_le i c hc0 hc1 t ht).symm
    · change
        p (rightCube i c hc0 hc1
            (Function.update t i
              (projIcc 0 1 zero_le_one
                (2 * (t i : ℝ) - 1)))) =
          p (splitCube i c hc0 hc1 t)
      exact congrArg p
        (splitCube_apply_of_not_le i c hc0 hc1 t ht).symm
  refine ⟨{
    toFun z := p (splitHomotopyCube i c hc0 hc1 z)
    continuous_toFun := by
      change Continuous
        (p.1 ∘ splitHomotopyCube i c hc0 hc1)
      exact p.1.continuous.comp
        (continuous_splitHomotopyCube i c hc0 hc1)
    map_zero_left t := by simp
    map_one_left t := by
      rw [splitHomotopyCube_one]
      exact (hq t).symm
    prop' s t ht := by
      exact
        (p.property _
          (splitHomotopyCube_mem_boundary i c hc0 hc1 s ht)).trans
            (p.property t ht).symm
  }⟩

end Submission.SphereSplit
