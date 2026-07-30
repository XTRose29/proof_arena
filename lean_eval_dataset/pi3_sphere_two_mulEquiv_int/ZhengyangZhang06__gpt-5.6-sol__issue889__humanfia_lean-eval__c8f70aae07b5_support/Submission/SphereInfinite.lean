import Submission.SphereSmoothBubbleDegree
import Submission.SphereSmoothJoin
import Submission.SphereTransverseInduction

open scoped ContDiff unitInterval Topology

noncomputable section

namespace Submission.SphereInfinite

open Set
open MeasureTheory
open Submission.SphereRegularApprox
open Submission.SphereSmoothRepresentative
open Submission.SphereDegreeHomotopy
open Submission.SphereSmoothJoin

abbrev Space :=
  Fin 3 → ℝ

abbrev GroupThree :=
  HomotopyGroup.Pi (2 + 1) (UnitSphere 2)
    (SphereGenerator.canonicalBasepoint 2)

abbrev canonicalGenerator : GroupThree :=
  SphereGenerator.canonicalGeneratorClass 2

abbrev bubbleClass : GroupThree :=
  Quotient.mk' bubble.toMap.genLoop

/-- The positive powers of the canonical bubble, realized by smooth connected
sums with a collar at every stage. -/
def iteratedBubble : ℕ → CollaredMap
  | 0 => bubble
  | n + 1 => join (iteratedBubble n) bubble

theorem iteratedBubble_class (n : ℕ) :
    (Quotient.mk' (iteratedBubble n).toMap.genLoop :
        GroupThree) =
      bubbleClass ^ (n + 1) := by
  induction n with
  | zero =>
      simp [iteratedBubble, bubbleClass]
  | succ n ih =>
      rw [iteratedBubble, join_genLoop]
      calc
        (Quotient.mk'
            (GenLoop.transAt (0 : Fin 3)
              (iteratedBubble n).toMap.genLoop
              bubble.toMap.genLoop) : GroupThree) =
            Mul.mul (α := GroupThree)
              (Quotient.mk' bubble.toMap.genLoop : GroupThree)
              (Quotient.mk' (iteratedBubble n).toMap.genLoop :
                GroupThree) :=
          HomotopyGroup.mul_spec.symm
        _ = bubbleClass * bubbleClass ^ (n + 1) := by
          rw [ih]
          rfl
        _ = bubbleClass ^ (n.succ + 1) := by
          rw [← pow_succ']

theorem iteratedBubble_neg_density_nonneg
    (n : ℕ) (x : Space) :
    0 ≤ -density (iteratedBubble n) x := by
  induction n generalizing x with
  | zero =>
      exact
        SphereSmoothBubbleDegree.neg_density_smoothMap_nonneg x
  | succ n ih =>
      exact neg_density_join_nonneg
        (iteratedBubble n) bubble ih
        SphereSmoothBubbleDegree.neg_density_smoothMap_nonneg x

/-- A point whose right-half rescaling is the center of the standard bubble. -/
def rightCenter : Space :=
  fun i => if i = 0 then 3 / 4 else 1 / 2

@[simp]
theorem rightCenter_zero :
    rightCenter 0 = 3 / 4 := by
  simp [rightCenter]

theorem rightTransform_rightCenter :
    rightTransform rightCenter =
      SphereSmoothBubbleDegree.center := by
  funext i
  by_cases hi : i = 0
  · subst i
    norm_num [rightTransform, rightCenter,
      SphereSmoothBubbleDegree.center]
  · simp [rightTransform, rightCenter,
      SphereSmoothBubbleDegree.center, hi]

theorem iteratedBubble_density_nonzero (n : ℕ) :
    ∃ x : Space, density (iteratedBubble n) x ≠ 0 := by
  cases n with
  | zero =>
      exact ⟨SphereSmoothBubbleDegree.center,
        SphereSmoothBubbleDegree.density_smoothMap_center_ne⟩
  | succ n =>
      refine ⟨rightCenter,
        density_join_right_nonzero
          (iteratedBubble n) bubble (by norm_num [rightCenter]) ?_⟩
      rw [rightTransform_rightCenter]
      exact SphereSmoothBubbleDegree.density_smoothMap_center_ne

/-- Beyond the ambient unit cube, an outer-coordinate condition is stable on
a neighborhood, so the derivative and hence the pulled-back density vanish. -/
theorem density_eq_zero_of_not_mem_cube
    (F : Map 2) {x : Space}
    (hx : x ∉ Set.Icc (0 : Space) 1) :
    density F x = 0 := by
  rw [Set.mem_Icc, not_and_or] at hx
  rcases hx with hx | hx
  · change ¬ ∀ i, 0 ≤ x i at hx
    push Not at hx
    obtain ⟨i, hi⟩ := hx
    have heq :
        (F : Space → Target 2) =ᶠ[𝓝 x]
          fun _ =>
            (SphereGenerator.canonicalBasepoint 2 : Target 2) := by
      have hopen : IsOpen {y : Space | y i < 0} :=
        isOpen_lt (continuous_apply i) continuous_const
      filter_upwards [hopen.mem_nhds hi] with y hy
      exact F.map_outer y i (Or.inl hy.le)
    rw [density, SphereDegreeInvariant.pulledVolumeForm,
      heq.fderiv_eq, fderiv_const_apply]
    simp
    apply (SphereDegreeForm.determinantForm 2).map_coord_zero
      (1 : Fin 4)
    simp
  · change ¬ ∀ i, x i ≤ 1 at hx
    push Not at hx
    obtain ⟨i, hi⟩ := hx
    have heq :
        (F : Space → Target 2) =ᶠ[𝓝 x]
          fun _ =>
            (SphereGenerator.canonicalBasepoint 2 : Target 2) := by
      have hopen : IsOpen {y : Space | 1 < y i} :=
        isOpen_lt continuous_const (continuous_apply i)
      filter_upwards [hopen.mem_nhds hi] with y hy
      exact F.map_outer y i (Or.inr hy.le)
    rw [density, SphereDegreeInvariant.pulledVolumeForm,
      heq.fderiv_eq, fderiv_const_apply]
    simp
    apply (SphereDegreeForm.determinantForm 2).map_coord_zero
      (1 : Fin 4)
    simp

theorem hasCompactSupport_neg_density (F : Map 2) :
    HasCompactSupport (fun x => -density F x) := by
  apply isCompact_Icc.of_isClosed_subset isClosed_closure
  apply closure_minimal
  · intro x hx
    by_contra hxcube
    have hd := density_eq_zero_of_not_mem_cube F hxcube
    exact hx (by simp [hd])
  · exact isClosed_Icc

theorem neg_degree_iteratedBubble_pos (n : ℕ) :
    0 < -degree (iteratedBubble n).toMap := by
  obtain ⟨x, hx⟩ := iteratedBubble_density_nonzero n
  have hwhole :
      0 < ∫ y : Space, -density (iteratedBubble n) y := by
    apply
      ((continuous_density
        (iteratedBubble n).contDiff).neg
        |>.integral_pos_of_hasCompactSupport_nonneg_nonzero
          (hasCompactSupport_neg_density
            (iteratedBubble n).toMap)
          (iteratedBubble_neg_density_nonneg n))
    simpa using hx
  have hzero :
      ∀ y : Space, y ∉ Set.Icc (0 : Space) 1 →
        -density (iteratedBubble n) y = 0 := by
    intro y hy
    rw [density_eq_zero_of_not_mem_cube
      (iteratedBubble n).toMap hy, neg_zero]
  have hset :
      (∫ y in Set.Icc (0 : Space) 1,
          -density (iteratedBubble n) y) =
        ∫ y : Space, -density (iteratedBubble n) y :=
    setIntegral_eq_integral_of_forall_compl_eq_zero hzero
  have hdegree :
      -degree (iteratedBubble n).toMap =
        ∫ y in Set.Icc (0 : Space) 1,
          -density (iteratedBubble n) y := by
    rw [degree, MeasureTheory.integral_neg]
  rw [hdegree, hset]
  exact hwhole

theorem degree_const_eq_zero :
    degree (const 2) = 0 := by
  have hzero :
      density
        (fun _ : Space =>
          (SphereGenerator.canonicalBasepoint 2 : Target 2)) = 0 := by
    funext x
    simp [density, SphereDegreeInvariant.pulledVolumeForm,
      SphereDegreeForm.volumeForm_apply]
    apply (SphereDegreeForm.determinantForm 2).map_coord_zero
      (1 : Fin 4)
    simp
  rw [degree]
  change
    (∫ x in Set.Icc (0 : Space) 1,
      density
        (fun _ : Space =>
          (SphereGenerator.canonicalBasepoint 2 : Target 2)) x) = 0
  rw [hzero]
  simp

theorem iteratedBubble_class_ne_one (n : ℕ) :
    (Quotient.mk' (iteratedBubble n).toMap.genLoop :
      GroupThree) ≠ (1 : GroupThree) := by
  intro hclass
  have hhom :
      GenLoop.Homotopic
        (iteratedBubble n).toMap.genLoop
        (const 2).genLoop :=
    Quotient.exact (hclass.trans HomotopyGroup.one_def)
  have hdegree :=
    degree_eq_of_homotopic hhom
  have hpos := neg_degree_iteratedBubble_pos n
  rw [hdegree, degree_const_eq_zero] at hpos
  norm_num at hpos

theorem bubbleClass_pow_ne_one
    (n : ℕ) (hn : 0 < n) :
    bubbleClass ^ n ≠ (1 : GroupThree) := by
  cases n with
  | zero => omega
  | succ n =>
      intro h
      apply iteratedBubble_class_ne_one n
      rw [iteratedBubble_class]
      change (bubbleClass ^ (n + 1) : GroupThree) =
        (1 : GroupThree)
      exact h

theorem groupThree_infinite : Infinite GroupThree := by
  apply not_finite_iff_infinite.mp
  intro hfinite
  letI : Finite GroupThree := hfinite
  have horder : orderOf bubbleClass = 0 :=
    orderOf_eq_zero_iff'.mpr bubbleClass_pow_ne_one
  have horderPos : 0 < orderOf bubbleClass :=
    orderOf_pos bubbleClass
  omega

/-- The canonical generator class classifies the third homotopy group of the
real unit 3-sphere at its standard cubical base point. -/
def northMulEquivInt :
    GroupThree ≃* Multiplicative ℤ := by
  letI : Infinite GroupThree := groupThree_infinite
  have hsurjective :=
    SphereTransverseInduction.canonicalZPowersHom_surjective
      (m := 2)
  have htop : Subgroup.zpowers canonicalGenerator = ⊤ := by
    rw [← Subgroup.range_zpowersHom]
    exact MonoidHom.range_eq_top.mpr hsurjective
  exact (intEquivOfZPowersEqTop canonicalGenerator htop).symm

end Submission.SphereInfinite
