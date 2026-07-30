import Submission.Helpers

open LeanEval.Geometry.FaryMilnorProblem
open Set
open Filter
open scoped Real
open scoped Topology
open scoped RealInnerProductSpace
open WithLp

namespace Submission.Helpers

noncomputable def planarBridgeCurve (r : ℝ → Space) (u : Space) (t : ℝ) : Space :=
  toLp 2 ![height r u t, directionalUnitTangent r u t, 0]

theorem contDiff_height {r : ℝ → Space} (hknot : IsSmoothKnot r) (u : Space) :
    ContDiff ℝ ⊤ (height r u) := by
  exact (innerSL ℝ u).contDiff.comp hknot.smooth

theorem contDiff_directionalUnitTangent {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) :
    ContDiff ℝ ⊤ (directionalUnitTangent r u) := by
  exact (innerSL ℝ u).contDiff.comp (contDiff_unitTangent hknot)

theorem contDiff_planarBridgeCurve {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) :
    ContDiff ℝ ⊤ (planarBridgeCurve r u) := by
  rw [contDiff_euclidean]
  intro i
  fin_cases i
  · simpa [planarBridgeCurve] using contDiff_height hknot u
  · simpa [planarBridgeCurve] using contDiff_directionalUnitTangent hknot u
  · simpa [planarBridgeCurve] using (contDiff_const : ContDiff ℝ ⊤ (fun _ : ℝ => (0 : ℝ)))

theorem periodic_planarBridgeCurve {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) :
    Function.Periodic (planarBridgeCurve r u) period := by
  intro t
  ext i
  fin_cases i
  · simp [planarBridgeCurve, periodic_height hknot u t]
  · simp [planarBridgeCurve, periodic_directionalUnitTangent hknot u t]
  · simp [planarBridgeCurve]

theorem hasDerivAt_planarBridgeCurve {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) (t : ℝ) :
    HasDerivAt (planarBridgeCurve r u)
      (toLp 2 ![deriv (height r u) t,
        deriv (directionalUnitTangent r u) t, 0]) t := by
  have hraw :
      HasDerivAt
        (fun t : ℝ => ![height r u t, directionalUnitTangent r u t, 0])
        ![deriv (height r u) t, deriv (directionalUnitTangent r u) t, 0] t := by
    rw [hasDerivAt_pi]
    intro i
    fin_cases i
    · exact (((contDiff_height hknot u).differentiable (by simp)).differentiableAt).hasDerivAt
    · exact (((contDiff_directionalUnitTangent hknot u).differentiable
        (by simp)).differentiableAt).hasDerivAt
    · simpa using hasDerivAt_const (x := t) (c := (0 : ℝ))
  convert toLpContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hraw using 1 <;>
    ext <;> rfl

theorem velocity_planarBridgeCurve {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) (t : ℝ) :
    velocity (planarBridgeCurve r u) t =
      toLp 2 ![deriv (height r u) t,
        deriv (directionalUnitTangent r u) t, 0] := by
  exact (hasDerivAt_planarBridgeCurve hknot u t).deriv

noncomputable def periodLift (a t : ℝ) : ℝ :=
  if t < a then t + period else t

theorem periodLift_mem_Ico {a t : ℝ} (ha : a ∈ Ico (0 : ℝ) period)
    (ht : t ∈ Ico (0 : ℝ) period) :
    periodLift a t ∈ Ico a (a + period) := by
  rw [periodLift]
  split_ifs with hta
  · constructor <;> linarith [ht.1, ht.2, ha.1, ha.2]
  · constructor
    · exact le_of_not_gt hta
    · linarith [ht.2, ha.1]

theorem periodLift_injective_on_Ico {a x y : ℝ}
    (ha : a ∈ Ico (0 : ℝ) period)
    (hx : x ∈ Ico (0 : ℝ) period) (hy : y ∈ Ico (0 : ℝ) period)
    (hxy : periodLift a x = periodLift a y) : x = y := by
  have ha0 : 0 ≤ a := ha.1
  rw [periodLift, periodLift] at hxy
  split_ifs at hxy with hxa hya
  · linarith
  · exfalso
    linarith [hx.1, hy.2]
  · exfalso
    linarith [hy.1, hx.2]
  · exact hxy

theorem planarBridgeCurve_periodLift {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a t : ℝ} :
    planarBridgeCurve r u (periodLift a t) = planarBridgeCurve r u t := by
  rw [periodLift]
  split_ifs
  · exact periodic_planarBridgeCurve hknot u t
  · rfl

theorem directionalUnitTangent_periodLift {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a t : ℝ} :
    directionalUnitTangent r u (periodLift a t) = directionalUnitTangent r u t := by
  rw [periodLift]
  split_ifs
  · exact periodic_directionalUnitTangent hknot u t
  · rfl

theorem regular_planarBridgeCurve_of_nondegenerate {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space)
    (hgeneric : IsNondegenerateDirection r u) :
    ∀ t : ℝ, velocity (planarBridgeCurve r u) t ≠ 0 := by
  intro t hzero
  have hcoord0 := congrArg (fun v : Space => v 0) hzero
  have hcoord1 := congrArg (fun v : Space => v 1) hzero
  have hheightZero : deriv (height r u) t = 0 := by
    simpa [velocity_planarBridgeCurve hknot u t] using hcoord0
  have hdirZero : deriv (directionalUnitTangent r u) t = 0 := by
    simpa [velocity_planarBridgeCurve hknot u t] using hcoord1
  have hgZero : directionalUnitTangent r u t = 0 := by
    rw [deriv_height_eq_speed_mul_directionalUnitTangent hknot u t] at hheightZero
    exact (mul_eq_zero.mp hheightZero).resolve_left
      (norm_ne_zero_iff.mpr (hknot.regular t))
  have hp : 0 < period := by simp [period, Real.pi_pos]
  have hpair : Function.Periodic
      (fun z => (directionalUnitTangent r u z,
        deriv (directionalUnitTangent r u) z)) period := by
    intro z
    apply Prod.ext
    · exact periodic_directionalUnitTangent hknot u z
    · exact periodic_deriv_directionalUnitTangent hknot u z
  obtain ⟨z, hz, hzt⟩ := hpair.exists_mem_Ico₀ hp t
  have hzg : directionalUnitTangent r u z = 0 := by
    have heq := congrArg Prod.fst hzt
    dsimp at heq
    rw [← heq]
    exact hgZero
  have hzd : deriv (directionalUnitTangent r u) z = 0 := by
    have heq := congrArg Prod.snd hzt
    dsimp at heq
    rw [← heq]
    exact hdirZero
  have hzIcc : z ∈ tangentGreatCircleIntersectionsIcc r u :=
    ⟨⟨hz.1, hz.2.le⟩, hzg⟩
  have hne := hgeneric z hzIcc
  rw [← (hasDerivAt_directionalUnitTangent hknot u z).deriv] at hne
  exact hne hzd

theorem injOn_planarBridgeCurve_of_two_monotone_arcs {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space)
    (hgeneric : IsNondegenerateDirection r u)
    (hcard : (tangentGreatCircleIntersections r u).ncard = 2) :
    Set.InjOn (planarBridgeCurve r u) (Ico (0 : ℝ) period) := by
  obtain ⟨tmax, tmin, hne, htmax, htmin, hset, hmax, hmin, harcs⟩ :=
    exists_two_monotone_height_arcs_of_ncard_intersections_eq_two
      hknot u hgeneric hcard
  let S := tangentGreatCircleIntersections r u
  have hsetS : S = {tmax, tmin} := by simpa [S] using hset
  have htmaxS : tmax ∈ S := by rw [hsetS]; simp
  have htminS : tmin ∈ S := by rw [hsetS]; simp
  have htmaxIcc : tmax ∈ tangentGreatCircleIntersectionsIcc r u :=
    ⟨⟨htmax.1, htmax.2.le⟩, htmaxS.2⟩
  have htminIcc : tmin ∈ tangentGreatCircleIntersectionsIcc r u :=
    ⟨⟨htmin.1, htmin.2.le⟩, htminS.2⟩
  have hmaxDeriv : deriv (directionalUnitTangent r u) tmax < 0 := by
    rw [(hasDerivAt_directionalUnitTangent hknot u tmax).deriv]
    exact inner_deriv_unitTangent_neg_of_isLocalMax_height
      hknot u hgeneric htmaxIcc hmax
  have hminDeriv : 0 < deriv (directionalUnitTangent r u) tmin := by
    rw [(hasDerivAt_directionalUnitTangent hknot u tmin).deriv]
    exact inner_deriv_unitTangent_pos_of_isLocalMin_height
      hknot u hgeneric htminIcc hmin
  have hnoBetween : ∀ {a b : ℝ}, a ∈ S → b ∈ S → a < b → S = {a, b} →
      ∀ z ∈ Ioo a b, directionalUnitTangent r u z ≠ 0 := by
    intro a b haS hbS hab hpair z hz hz0
    have hzIco : z ∈ Ico (0 : ℝ) period :=
      ⟨haS.1.1.trans hz.1.le, hz.2.trans hbS.1.2⟩
    have hzS : z ∈ S := ⟨hzIco, hz0⟩
    rw [hpair] at hzS
    rcases hzS with rfl | hzS
    · exact (lt_irrefl _ hz.1)
    · have : z = b := by simpa using hzS
      subst z
      exact (lt_irrefl _ hz.2)
  have hnoWrap : ∀ {low high : ℝ}, low ∈ S → high ∈ S → low < high →
      S = {low, high} →
      ∀ z ∈ Ioo high (low + period), directionalUnitTangent r u z ≠ 0 := by
    intro low high hlowS hhighS hlowhigh hpair z hz hz0
    by_cases hzp : z < period
    · have hzIco : z ∈ Ico (0 : ℝ) period :=
        ⟨hhighS.1.1.trans hz.1.le, hzp⟩
      have hzS : z ∈ S := ⟨hzIco, hz0⟩
      rw [hpair] at hzS
      rcases hzS with rfl | hzS
      · exact (not_lt_of_ge hlowhigh.le) hz.1
      · have : z = high := by simpa using hzS
        subst z
        exact (lt_irrefl _ hz.1)
    · have hpz : period ≤ z := le_of_not_gt hzp
      let z' := z - period
      have hz'zero : directionalUnitTangent r u z' = 0 := by
        have hper := periodic_directionalUnitTangent hknot u z'
        have hz'eq : z' + period = z := by dsimp [z']; ring
        rw [hz'eq] at hper
        rw [← hper]
        exact hz0
      have hz'Ico : z' ∈ Ico (0 : ℝ) period := by
        constructor
        · dsimp [z']
          linarith
        · dsimp [z']
          linarith [hz.2, hlowS.1.2]
      have hz'S : z' ∈ S := ⟨hz'Ico, hz'zero⟩
      rw [hpair] at hz'S
      have hz'lt : z' < low := by
        dsimp [z']
        linarith [hz.2]
      rcases hz'S with hzEq | hzEq
      · have : z' = low := by simpa using hzEq
        exact (lt_irrefl low (this ▸ hz'lt))
      · have : z' = high := by simpa using hzEq
        exact (not_lt_of_ge hlowhigh.le) (this ▸ hz'lt)
  intro x hx y hy hxy
  rcases harcs with hminmax | hmaxmin
  · rcases hminmax with ⟨hminmax, hmono, hanti⟩
    have hsetSwap : S = {tmin, tmax} := by simpa [Set.pair_comm] using hsetS
    have hpos : ∀ z ∈ Ioo tmin tmax, 0 < directionalUnitTangent r u z :=
      pos_on_Ioo_of_deriv_pos_of_no_zeros
        (continuous_directionalUnitTangent hknot u) hminmax htminS.2 hminDeriv
        (hnoBetween htminS htmaxS hminmax hsetSwap)
    have hneg : ∀ z ∈ Ioo tmax (tmin + period),
        directionalUnitTangent r u z < 0 :=
      neg_on_Ioo_of_deriv_neg_of_no_zeros
        (continuous_directionalUnitTangent hknot u)
        (by linarith [htmax.2, htmin.1]) htmaxS.2 hmaxDeriv
        (hnoWrap htminS htmaxS hminmax hsetSwap)
    let x' := periodLift tmin x
    let y' := periodLift tmin y
    have hx' : x' ∈ Ico tmin (tmin + period) := periodLift_mem_Ico htmin hx
    have hy' : y' ∈ Ico tmin (tmin + period) := periodLift_mem_Ico htmin hy
    have hxy' : planarBridgeCurve r u x' = planarBridgeCurve r u y' := by
      calc
        planarBridgeCurve r u x' = planarBridgeCurve r u x :=
          planarBridgeCurve_periodLift hknot u
        _ = planarBridgeCurve r u y := hxy
        _ = planarBridgeCurve r u y' :=
          (planarBridgeCurve_periodLift hknot u).symm
    have hheight : height r u x' = height r u y' := by
      have := congrArg (fun v : Space => v 0) hxy'
      simpa [planarBridgeCurve] using this
    have hdir : directionalUnitTangent r u x' =
        directionalUnitTangent r u y' := by
      have := congrArg (fun v : Space => v 1) hxy'
      simpa [planarBridgeCurve] using this
    by_cases hxsplit : x' ≤ tmax
    · by_cases hysplit : y' ≤ tmax
      · have hxeq : x' = y' := hmono.injOn
          ⟨hx'.1, hxsplit⟩ ⟨hy'.1, hysplit⟩ hheight
        exact periodLift_injective_on_Ico htmin hx hy hxeq
      · have hygt : tmax < y' := lt_of_not_ge hysplit
        have hygNeg : directionalUnitTangent r u y' < 0 :=
          hneg y' ⟨hygt, hy'.2⟩
        have hxgNonneg : 0 ≤ directionalUnitTangent r u x' := by
          rcases eq_or_lt_of_le hx'.1 with hxmin | hxmin
          · rw [← hxmin, htminS.2]
          · rcases eq_or_lt_of_le hxsplit with hxmax | hxmax
            · rw [hxmax, htmaxS.2]
            · exact (hpos x' ⟨hxmin, hxmax⟩).le
        linarith
    · have hxgt : tmax < x' := lt_of_not_ge hxsplit
      by_cases hysplit : y' ≤ tmax
      · have hxgNeg : directionalUnitTangent r u x' < 0 :=
          hneg x' ⟨hxgt, hx'.2⟩
        have hygNonneg : 0 ≤ directionalUnitTangent r u y' := by
          rcases eq_or_lt_of_le hy'.1 with hymin | hymin
          · rw [← hymin, htminS.2]
          · rcases eq_or_lt_of_le hysplit with hymax | hymax
            · rw [hymax, htmaxS.2]
            · exact (hpos y' ⟨hymin, hymax⟩).le
        linarith
      · have hxeq : x' = y' := hanti.injOn
          ⟨hxgt.le, hx'.2.le⟩ ⟨(lt_of_not_ge hysplit).le, hy'.2.le⟩ hheight
        exact periodLift_injective_on_Ico htmin hx hy hxeq
  · rcases hmaxmin with ⟨hmaxmin, hanti, hmono⟩
    have hneg : ∀ z ∈ Ioo tmax tmin, directionalUnitTangent r u z < 0 :=
      neg_on_Ioo_of_deriv_neg_of_no_zeros
        (continuous_directionalUnitTangent hknot u) hmaxmin htmaxS.2 hmaxDeriv
        (hnoBetween htmaxS htminS hmaxmin hsetS)
    have hpos : ∀ z ∈ Ioo tmin (tmax + period),
        0 < directionalUnitTangent r u z :=
      pos_on_Ioo_of_deriv_pos_of_no_zeros
        (continuous_directionalUnitTangent hknot u)
        (by linarith [htmin.2, htmax.1]) htminS.2 hminDeriv
        (hnoWrap htmaxS htminS hmaxmin hsetS)
    let x' := periodLift tmax x
    let y' := periodLift tmax y
    have hx' : x' ∈ Ico tmax (tmax + period) := periodLift_mem_Ico htmax hx
    have hy' : y' ∈ Ico tmax (tmax + period) := periodLift_mem_Ico htmax hy
    have hxy' : planarBridgeCurve r u x' = planarBridgeCurve r u y' := by
      calc
        planarBridgeCurve r u x' = planarBridgeCurve r u x :=
          planarBridgeCurve_periodLift hknot u
        _ = planarBridgeCurve r u y := hxy
        _ = planarBridgeCurve r u y' :=
          (planarBridgeCurve_periodLift hknot u).symm
    have hheight : height r u x' = height r u y' := by
      have := congrArg (fun v : Space => v 0) hxy'
      simpa [planarBridgeCurve] using this
    have hdir : directionalUnitTangent r u x' =
        directionalUnitTangent r u y' := by
      have := congrArg (fun v : Space => v 1) hxy'
      simpa [planarBridgeCurve] using this
    by_cases hxsplit : x' ≤ tmin
    · by_cases hysplit : y' ≤ tmin
      · have hxeq : x' = y' := hanti.injOn
          ⟨hx'.1, hxsplit⟩ ⟨hy'.1, hysplit⟩ hheight
        exact periodLift_injective_on_Ico htmax hx hy hxeq
      · have hygt : tmin < y' := lt_of_not_ge hysplit
        have hygPos : 0 < directionalUnitTangent r u y' :=
          hpos y' ⟨hygt, hy'.2⟩
        have hxgNonpos : directionalUnitTangent r u x' ≤ 0 := by
          rcases eq_or_lt_of_le hx'.1 with hxmax | hxmax
          · rw [← hxmax, htmaxS.2]
          · rcases eq_or_lt_of_le hxsplit with hxmin | hxmin
            · rw [hxmin, htminS.2]
            · exact (hneg x' ⟨hxmax, hxmin⟩).le
        linarith
    · have hxgt : tmin < x' := lt_of_not_ge hxsplit
      by_cases hysplit : y' ≤ tmin
      · have hxgPos : 0 < directionalUnitTangent r u x' :=
          hpos x' ⟨hxgt, hx'.2⟩
        have hygNonpos : directionalUnitTangent r u y' ≤ 0 := by
          rcases eq_or_lt_of_le hy'.1 with hymax | hymax
          · rw [← hymax, htmaxS.2]
          · rcases eq_or_lt_of_le hysplit with hymin | hymin
            · rw [hymin, htminS.2]
            · exact (hneg y' ⟨hymax, hymin⟩).le
        linarith
      · have hxeq : x' = y' := hmono.injOn
          ⟨hxgt.le, hx'.2.le⟩ ⟨(lt_of_not_ge hysplit).le, hy'.2.le⟩ hheight
        exact periodLift_injective_on_Ico htmax hx hy hxeq

theorem isSmoothKnot_planarBridgeCurve_of_nondegenerate_of_ncard_eq_two
    {r : ℝ → Space} (hknot : IsSmoothKnot r) (u : Space)
    (hgeneric : IsNondegenerateDirection r u)
    (hcard : (tangentGreatCircleIntersections r u).ncard = 2) :
    IsSmoothKnot (planarBridgeCurve r u) where
  smooth := contDiff_planarBridgeCurve hknot u
  periodic := periodic_planarBridgeCurve hknot u
  injective_on_period :=
    injOn_planarBridgeCurve_of_two_monotone_arcs hknot u hgeneric hcard
  regular := regular_planarBridgeCurve_of_nondegenerate hknot u hgeneric

end Submission.Helpers
