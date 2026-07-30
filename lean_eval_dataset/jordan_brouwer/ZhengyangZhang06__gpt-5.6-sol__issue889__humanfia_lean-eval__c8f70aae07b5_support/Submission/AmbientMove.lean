import Submission.Components

namespace Submission.Helpers

open Set

noncomputable section

/-- A perturbation of the identity by a map with Lipschitz constant strictly
less than one is a homeomorphism. -/
def lipschitzPerturbationHomeomorph
    {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (h : E → E) (K : NNReal) (hK : K < 1) (hh : LipschitzWith K h) :
    E ≃ₜ E := by
  have hcontract (y : E) : ContractingWith K (fun x ↦ y - h x) := by
    refine ⟨hK, ?_⟩
    simpa using (LipschitzWith.const y).sub hh
  let inv : E → E := fun y ↦ (hcontract y).fixedPoint (fun x ↦ y - h x)
  have hinv (y : E) : y - h (inv y) = inv y := by
    exact (hcontract y).fixedPoint_isFixedPt
  have hright (y : E) : inv y + h (inv y) = y := by
    calc
      inv y + h (inv y) = (y - h (inv y)) + h (inv y) := by rw [hinv y]
      _ = y := sub_add_cancel _ _
  have hleft (x : E) : inv (x + h x) = x := by
    have hxfix : Function.IsFixedPt (fun w ↦ x + h x - h w) x := by
      change x + h x - h x = x
      exact add_sub_cancel_right x (h x)
    exact ((hcontract (x + h x)).fixedPoint_unique hxfix).symm
  have hdenom : 0 < 1 - (K : ℝ) := sub_pos.mpr hK
  let L : NNReal := ⟨(1 - (K : ℝ))⁻¹, (inv_pos.mpr hdenom).le⟩
  have hinvLipschitz : LipschitzWith L inv := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro y z
    have hbound := (hcontract y).fixedPoint_lipschitz_in_map
      (hcontract z) (C := dist y z) (fun w ↦ by
        simpa only [dist_sub_right] using (show dist y z ≤ dist y z from le_rfl))
    change dist (inv y) (inv z) ≤
      (1 - (K : ℝ))⁻¹ * dist y z
    simpa [inv, L, div_eq_inv_mul] using hbound
  exact Homeomorph.mk
    { toFun := fun x ↦ x + h x
      invFun := inv
      left_inv := hleft
      right_inv := hright }
    (continuous_id.add hh.continuous) hinvLipschitz.continuous

private def radialBump {E : Type*} [PseudoMetricSpace E]
    (c : E) (R : ℝ) (x : E) : ℝ :=
  max 0 (1 - dist x c / R)

private theorem abs_radialBump_sub_le
    {E : Type*} [PseudoMetricSpace E]
    (c : E) {R : ℝ} (hR : 0 < R) (x y : E) :
    |radialBump c R x - radialBump c R y| ≤ R⁻¹ * dist x y := by
  have hmax := abs_max_sub_max_le_max (0 : ℝ)
    (1 - dist x c / R) 0 (1 - dist y c / R)
  calc
    |radialBump c R x - radialBump c R y| ≤
        |(1 - dist x c / R) - (1 - dist y c / R)| := by
      simpa [radialBump] using hmax
    _ = |dist x c - dist y c| / R := by
      rw [show (1 - dist x c / R) - (1 - dist y c / R) =
          (dist y c - dist x c) / R by ring,
        abs_div, abs_of_pos hR, abs_sub_comm]
    _ ≤ dist x y / R :=
      (div_le_div_iff_of_pos_right hR).2 (abs_dist_sub_le x y c)
    _ = R⁻¹ * dist x y := by rw [div_eq_inv_mul]

/-- A small radial bump moves `c` by `v`, is the identity outside the ball of
radius `R`, and is a homeomorphism when `‖v‖ < R`. -/
def radialMoveHomeomorph
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (c v : E) (R : ℝ) (hR : 0 < R) (hv : ‖v‖ < R) : E ≃ₜ E := by
  let h : E → E := fun x ↦ radialBump c R x • v
  have hh : LipschitzWith (Real.toNNReal (R⁻¹ * ‖v‖)) h := by
    apply LipschitzWith.of_dist_le'
    intro x y
    calc
      dist (h x) (h y) =
          ‖(radialBump c R x - radialBump c R y) • v‖ := by
        rw [dist_eq_norm, sub_smul]
      _ = |radialBump c R x - radialBump c R y| * ‖v‖ := by
        rw [norm_smul, Real.norm_eq_abs]
      _ ≤ (R⁻¹ * dist x y) * ‖v‖ :=
        mul_le_mul_of_nonneg_right
          (abs_radialBump_sub_le c hR x y) (norm_nonneg v)
      _ = (R⁻¹ * ‖v‖) * dist x y := by ring
  have hcoef : R⁻¹ * ‖v‖ < 1 := by
    rw [← div_eq_inv_mul]
    exact (div_lt_one hR).2 hv
  exact lipschitzPerturbationHomeomorph h
    (Real.toNNReal (R⁻¹ * ‖v‖))
    (Real.toNNReal_lt_one.mpr hcoef) hh

theorem radialMoveHomeomorph_apply_center
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (c v : E) (R : ℝ) (hR : 0 < R) (hv : ‖v‖ < R) :
    radialMoveHomeomorph c v R hR hv c = c + v := by
  change c + radialBump c R c • v = c + v
  simp [radialBump]

theorem radialMoveHomeomorph_apply_of_le_dist
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (c v : E) (R : ℝ) (hR : 0 < R) (hv : ‖v‖ < R)
    {x : E} (hx : R ≤ dist x c) :
    radialMoveHomeomorph c v R hR hv x = x := by
  change x + radialBump c R x • v = x
  have hquot : 1 ≤ dist x c / R := (le_div_iff₀ hR).2 (by simpa using hx)
  have hbump : radialBump c R x = 0 := by
    rw [radialBump, max_eq_left (sub_nonpos.mpr hquot)]
  rw [hbump, zero_smul, add_zero]

/-- In real dimension at least two, a ball with its center removed is path
connected. -/
theorem isPathConnected_ball_sdiff_center
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hrank : 1 < Module.rank ℝ E) (c : E) {R : ℝ} (hR : 0 < R) :
    IsPathConnected (Metric.ball c R \ {c}) := by
  let W : Set E := {x | 0 < ‖x‖}
  have hW : IsPathConnected W :=
    isPathConnected_norm_gt hrank 0 (by norm_num)
  let e : OpenPartialHomeomorph E E :=
    OpenPartialHomeomorph.univBall c R
  have heSource : e.source = Set.univ := by
    exact OpenPartialHomeomorph.univBall_source c R
  have heTarget : e.target = Metric.ball c R := by
    exact OpenPartialHomeomorph.univBall_target c hR
  have himage : e '' W = Metric.ball c R \ {c} := by
    ext y
    constructor
    · rintro ⟨x, hxW, rfl⟩
      have hxSource : x ∈ e.source := by rw [heSource]; exact Set.mem_univ _
      have hxTarget : e x ∈ e.target := e.map_source hxSource
      refine ⟨heTarget ▸ hxTarget, ?_⟩
      rw [Set.mem_singleton_iff]
      intro hexc
      have hx0 : x = 0 := by
        apply e.injOn hxSource
          (by rw [heSource]; exact Set.mem_univ _)
        simpa [e] using hexc
      change 0 < ‖x‖ at hxW
      subst x
      norm_num at hxW
    · rintro ⟨hyBall, hyc⟩
      have hyTarget : y ∈ e.target := heTarget.symm ▸ hyBall
      let x := e.symm y
      have hxSource : x ∈ e.source := e.map_target hyTarget
      have hexy : e x = y := e.right_inv hyTarget
      have hx0 : x ≠ 0 := by
        intro hxzero
        apply hyc
        rw [Set.mem_singleton_iff]
        calc
          y = e x := hexy.symm
          _ = e 0 := by rw [hxzero]
          _ = c := by simp [e]
      exact ⟨x, norm_pos_iff.mpr hx0, hexy⟩
  rw [← himage]
  exact hW.image (OpenPartialHomeomorph.continuous_univBall c R)

/-- Removing finitely many points from an open preconnected subset of a real
space of dimension at least two preserves preconnectedness.  This is the
single-point step. -/
theorem isPreconnected_sdiff_singleton_of_isOpen
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hrank : 1 < Module.rank ℝ E) {U : Set E}
    (hUOpen : IsOpen U) (hUPreconnected : IsPreconnected U) (p : E) :
    IsPreconnected (U \ {p}) := by
  by_cases hpU : p ∈ U
  · let V : Set E := U \ {p}
    have hVOpen : IsOpen V := hUOpen.sdiff isClosed_singleton
    obtain ⟨R, hR, hballU⟩ :=
      (Metric.isOpen_iff.mp hUOpen) p hpU
    let B : Set E := Metric.ball p R \ {p}
    have hBPath : IsPathConnected B :=
      isPathConnected_ball_sdiff_center hrank p hR
    have hBSubset : B ⊆ V := by
      rintro z ⟨hzBall, hzp⟩
      exact ⟨hballU hzBall, hzp⟩
    obtain ⟨b, hbB⟩ := hBPath.nonempty
    have hbV : b ∈ V := hBSubset hbB
    have hfrontier (x : E) (hxV : x ∈ V) :
        p ∈ closure (connectedComponentIn V x) := by
      by_contra hpClosure
      let C : Set E := connectedComponentIn V x
      have hCOpen : IsOpen C := hVOpen.connectedComponentIn
      have hCClosure : C ⊆ closure C := subset_closure
      have hCDisjoint : Disjoint C (closure C)ᶜ := by
        rw [Set.disjoint_left]
        intro z hzC hzClosure
        exact hzClosure (hCClosure hzC)
      have hUCover : U ⊆ C ∪ (closure C)ᶜ := by
        intro z hzU
        by_cases hzC : z ∈ C
        · exact Or.inl hzC
        · apply Or.inr
          rw [Set.mem_compl_iff]
          intro hzClosure
          have hzp : z = p := by
            by_contra hzp
            have hzV : z ∈ V := ⟨hzU, hzp⟩
            have hzComponent : z ∈ C := by
              have hzInter : z ∈ closure C ∩ V := ⟨hzClosure, hzV⟩
              change z ∈ connectedComponentIn V x
              rw [← closure_connectedComponentIn_inter hVOpen x]
              exact hzInter
            exact hzC hzComponent
          exact hpClosure (hzp ▸ hzClosure)
      have hUCNonempty : (U ∩ C).Nonempty := by
        refine ⟨x, hxV.1, ?_⟩
        exact mem_connectedComponentIn hxV
      have hUC := hUPreconnected.subset_left_of_subset_union
        hCOpen isClosed_closure.isOpen_compl hCDisjoint hUCover hUCNonempty
      have hpC : p ∈ C := hUC hpU
      exact (connectedComponentIn_subset V x hpC).2 rfl
    have hBMemComponent (x : E) (hxV : x ∈ V) :
        b ∈ connectedComponentIn V x := by
      obtain ⟨z, hzComponent, hpz⟩ :=
        (Metric.mem_closure_iff.mp (hfrontier x hxV)) R hR
      have hzB : z ∈ B := by
        refine ⟨?_, ?_⟩
        · simpa only [Metric.mem_ball, dist_comm] using hpz
        · intro hzp
          rw [Set.mem_singleton_iff] at hzp
          subst z
          exact (connectedComponentIn_subset V x hzComponent).2 rfl
      have hBComponent : B ⊆ connectedComponentIn V z :=
        hBPath.isConnected.isPreconnected.subset_connectedComponentIn
          hzB hBSubset
      have hcomponentEq : connectedComponentIn V x =
          connectedComponentIn V z := connectedComponentIn_eq hzComponent
      rw [hcomponentEq]
      exact hBComponent hbB
    have hVSubset : V ⊆ connectedComponentIn V b := by
      intro x hxV
      have hbx := hBMemComponent x hxV
      have hxOwn : x ∈ connectedComponentIn V x :=
        mem_connectedComponentIn hxV
      rw [connectedComponentIn_eq hbx] at hxOwn
      exact hxOwn
    have hcomponent : connectedComponentIn V b = V :=
      Set.Subset.antisymm (connectedComponentIn_subset V b) hVSubset
    change IsPreconnected V
    rw [← hcomponent]
    exact isPreconnected_connectedComponentIn
  · simpa [Set.sdiff_singleton_eq_self hpU] using hUPreconnected

/-- Removing a finite set from an open preconnected subset of a real space
of dimension at least two preserves preconnectedness. -/
theorem isPreconnected_sdiff_finite_of_isOpen
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hrank : 1 < Module.rank ℝ E) {U F : Set E}
    (hUOpen : IsOpen U) (hUPreconnected : IsPreconnected U)
    (hF : F.Finite) : IsPreconnected (U \ F) := by
  induction F, hF using Set.Finite.induction_on with
  | empty => simpa
  | @insert p F hpF hF ih =>
      have hUFOpen : IsOpen (U \ F) := hUOpen.sdiff hF.isClosed
      have hUFPreconnected : IsPreconnected (U \ F) := ih
      have heq : (U \ F) \ {p} = U \ insert p F := by
        ext z
        simp only [Set.mem_sdiff, Set.mem_singleton_iff,
          Set.mem_insert_iff]
        tauto
      rw [← heq]
      exact isPreconnected_sdiff_singleton_of_isOpen
        hrank hUFOpen hUFPreconnected p

/-- Two points of a preconnected open set can be interchanged by composing
small radial moves, while fixing the complement of the open set pointwise. -/
theorem exists_homeomorph_apply_eq_of_isOpen_isPreconnected
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {U : Set E} (hUOpen : IsOpen U) (hUPreconnected : IsPreconnected U)
    {x y : E} (hx : x ∈ U) (hy : y ∈ U) :
    ∃ e : E ≃ₜ E, e x = y ∧ ∀ z, z ∉ U → e z = z := by
  let A : Set U := {p | ∃ e : E ≃ₜ E,
    e x = (p : E) ∧ ∀ z, z ∉ U → e z = z}
  have hAOpen : IsOpen A := by
    rw [Metric.isOpen_iff]
    intro p hpA
    obtain ⟨R, hR, hball⟩ :=
      (Metric.isOpen_iff.mp hUOpen) (p : E) p.2
    refine ⟨R, hR, ?_⟩
    intro q hqp
    change ∃ e : E ≃ₜ E,
      e x = (q : E) ∧ ∀ z, z ∉ U → e z = z
    change ∃ e : E ≃ₜ E,
      e x = (p : E) ∧ ∀ z, z ∉ U → e z = z at hpA
    obtain ⟨e, hep, hefix⟩ := hpA
    have hv : ‖(q : E) - (p : E)‖ < R := by
      change dist (q : E) (p : E) < R at hqp
      simpa only [dist_eq_norm] using hqp
    let m : E ≃ₜ E := radialMoveHomeomorph
      (p : E) ((q : E) - (p : E)) R hR hv
    have hmpq : m (p : E) = (q : E) := by
      rw [radialMoveHomeomorph_apply_center]
      abel
    have hmfix (z : E) (hz : z ∉ U) : m z = z := by
      apply radialMoveHomeomorph_apply_of_le_dist
      apply le_of_not_gt
      intro hzball
      exact hz (hball hzball)
    refine ⟨e.trans m, ?_, ?_⟩
    · change m (e x) = (q : E)
      rw [hep, hmpq]
    · intro z hz
      change m (e z) = z
      rw [hefix z hz, hmfix z hz]
  have hAComplOpen : IsOpen Aᶜ := by
    rw [Metric.isOpen_iff]
    intro p hpA
    obtain ⟨R, hR, hball⟩ :=
      (Metric.isOpen_iff.mp hUOpen) (p : E) p.2
    refine ⟨R, hR, ?_⟩
    intro q hqp hqA
    apply hpA
    change ∃ e : E ≃ₜ E,
      e x = (p : E) ∧ ∀ z, z ∉ U → e z = z
    change ∃ e : E ≃ₜ E,
      e x = (q : E) ∧ ∀ z, z ∉ U → e z = z at hqA
    obtain ⟨e, heq, hefix⟩ := hqA
    have hv : ‖(q : E) - (p : E)‖ < R := by
      change dist (q : E) (p : E) < R at hqp
      simpa only [dist_eq_norm] using hqp
    let m : E ≃ₜ E := radialMoveHomeomorph
      (p : E) ((q : E) - (p : E)) R hR hv
    have hmpq : m (p : E) = (q : E) := by
      rw [radialMoveHomeomorph_apply_center]
      abel
    have hmfix (z : E) (hz : z ∉ U) : m z = z := by
      apply radialMoveHomeomorph_apply_of_le_dist
      apply le_of_not_gt
      intro hzball
      exact hz (hball hzball)
    have hmsymmfix (z : E) (hz : z ∉ U) : m.symm z = z := by
      calc
        m.symm z = m.symm (m z) := by rw [hmfix z hz]
        _ = z := m.symm_apply_apply z
    refine ⟨e.trans m.symm, ?_, ?_⟩
    · change m.symm (e x) = (p : E)
      rw [heq, ← hmpq, m.symm_apply_apply]
    · intro z hz
      change m.symm (e z) = z
      rw [hefix z hz, hmsymmfix z hz]
  have hAClopen : IsClopen A :=
    ⟨isOpen_compl_iff.mp hAComplOpen, hAOpen⟩
  letI : PreconnectedSpace U := Subtype.preconnectedSpace hUPreconnected
  have hxA : (⟨x, hx⟩ : U) ∈ A := by
    change ∃ e : E ≃ₜ E,
      e x = x ∧ ∀ z, z ∉ U → e z = z
    exact ⟨Homeomorph.refl E, rfl, fun _ _ ↦ rfl⟩
  have hAeq : A = Set.univ := hAClopen.eq_univ ⟨⟨x, hx⟩, hxA⟩
  have hyA : (⟨y, hy⟩ : U) ∈ A := hAeq.symm ▸ Set.mem_univ _
  exact hyA

private theorem homeomorph_mapsTo_of_fixes_compl
    {E : Type*} [TopologicalSpace E] {U : Set E} (e : E ≃ₜ E)
    (hfix : ∀ z, z ∉ U → e z = z) : Set.MapsTo e U U := by
  intro z hzU
  by_contra hezU
  have hefixed : e (e z) = e z := hfix (e z) hezU
  have hez : e z = z := e.injective hefixed
  exact hezU (hez.symm ▸ hzU)

/-- A finite set in an unbounded open preconnected region can be moved off
any bounded set by an ambient homeomorphism supported in that region. -/
theorem exists_homeomorph_image_finite_disjoint_bounded
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (hrank : 1 < Module.rank ℝ E) {U P C : Set E}
    (hUOpen : IsOpen U) (hUPreconnected : IsPreconnected U)
    (hUUnbounded : ¬ Bornology.IsBounded U)
    (hP : P.Finite) (hPU : P ⊆ U) (hC : Bornology.IsBounded C) :
    ∃ e : E ≃ₜ E, Disjoint (e '' P) C ∧
      ∀ z, z ∉ U → e z = z := by
  classical
  revert hPU
  induction P, hP using Set.Finite.induction_on with
  | empty =>
      intro _hPU
      refine ⟨Homeomorph.refl E, ?_, fun _ _ ↦ rfl⟩
      simp
  | @insert p P hpP hP ih =>
      intro hPU
      have hpU : p ∈ U := hPU (Set.mem_insert p P)
      have hPU' : P ⊆ U := fun q hqP ↦ hPU (Set.mem_insert_of_mem p hqP)
      obtain ⟨e, heDisjoint, heFix⟩ := ih hPU'
      let Q : Set E := e '' P
      have hQFinite : Q.Finite := hP.image e
      have hUQOpen : IsOpen (U \ Q) := hUOpen.sdiff hQFinite.isClosed
      have hUQPreconnected : IsPreconnected (U \ Q) :=
        isPreconnected_sdiff_finite_of_isOpen
          hrank hUOpen hUPreconnected hQFinite
      have hepU : e p ∈ U :=
        homeomorph_mapsTo_of_fixes_compl e heFix hpU
      have hepQ : e p ∉ Q := by
        rintro ⟨q, hqP, heqp⟩
        apply hpP
        exact (e.injective heqp) ▸ hqP
      have hyExists : ∃ y ∈ U, y ∉ C ∧ y ∉ Q := by
        by_contra hnone
        push Not at hnone
        apply hUUnbounded
        apply (hC.union hQFinite.isBounded).subset
        intro y hyU
        by_cases hyC : y ∈ C
        · exact Or.inl hyC
        · exact Or.inr (hnone y hyU hyC)
      obtain ⟨y, hyU, hyC, hyQ⟩ := hyExists
      obtain ⟨m, hm, hmFix⟩ :=
        exists_homeomorph_apply_eq_of_isOpen_isPreconnected
          hUQOpen hUQPreconnected ⟨hepU, hepQ⟩ ⟨hyU, hyQ⟩
      have hmQ (q : E) (hqQ : q ∈ Q) : m q = q := by
        apply hmFix q
        intro hqUQ
        exact hqUQ.2 hqQ
      refine ⟨e.trans m, ?_, ?_⟩
      · rw [Set.disjoint_left]
        intro z hzImage hzC
        obtain ⟨q, hq, rfl⟩ := hzImage
        rw [Set.mem_insert_iff] at hq
        rcases hq with hqp | hqP
        · subst q
          change m (e p) ∈ C at hzC
          rw [hm] at hzC
          exact hyC hzC
        · have heqQ : e q ∈ Q := ⟨q, hqP, rfl⟩
          change m (e q) ∈ C at hzC
          rw [hmQ (e q) heqQ] at hzC
          exact Set.disjoint_left.mp heDisjoint heqQ hzC
      · intro z hzU
        change m (e z) = z
        rw [heFix z hzU]
        exact hmFix z (fun hzUQ ↦ hzU hzUQ.1)

end

end Submission.Helpers
