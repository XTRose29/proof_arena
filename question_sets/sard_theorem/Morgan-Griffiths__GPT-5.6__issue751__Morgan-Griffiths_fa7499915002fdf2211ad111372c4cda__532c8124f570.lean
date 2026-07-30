import Mathlib

-- BEGIN INLINED FILE: Mathlib/Support/sard_theorem_8feee3b75b/FlatTaylor.lean
open MeasureTheory Module
open scoped ContDiff NNReal ENNReal
namespace SardSupport
-- uniform Holder estimate for a bounded flat set
lemma holderOnWith_nat_of_flat
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E]
      [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {s : Set E} {R : ℝ} {k : ℕ} (hk : 0 < k)
    (hf : ContDiff ℝ (∞ : WithTop ℕ∞) f)
    (hs : s ⊆ Metric.closedBall (0:E) R)
    (hz : ∀ x ∈ s, ∀ j : ℕ, 1 ≤ j → j < k → iteratedFDeriv ℝ j f x = 0) :
    ∃ C : NNReal, HolderOnWith C (k : NNReal) f s := by
  classical
  -- the norm of the kth derivative has a bound on the closed ball
  let B : Set E := Metric.closedBall (0:E) R
  let u : E → ℝ := fun z => ‖iteratedFDeriv ℝ k f z‖
  have huc : Continuous u := by
    exact ((hf.continuous_iteratedFDeriv (by exact_mod_cast (le_top : (k:ℕ∞) ≤ ⊤))).norm)
  have hcomp : IsCompact B := by
    dsimp [B]
    exact ProperSpace.isCompact_closedBall _ _
  rcases (bddAbove_def.mp (hcomp.image_of_continuousOn huc.continuousOn).bddAbove) with
    ⟨A0,hA0⟩
  -- enlarge to a nonnegative bound
  let A : ℝ := max A0 0
  have hA : 0 ≤ A := le_max_right _ _
  have hbound : ∀ z ∈ B, ‖iteratedFDeriv ℝ k f z‖ ≤ A := by
    intro z hz'
    apply le_trans ?_ (le_max_left _ _)
    exact hA0 _ ⟨z,hz',rfl⟩
  -- we use the slightly larger constant A/(k-1)! from Taylor, but A itself
  -- already bounds it since the factorial is at least one. The bound lemma
  -- has factorial in the denominator; keeping A is convenient.
  refine ⟨⟨A, hA⟩, ?_⟩
  intro x hx y hy
  -- first a real norm estimate
  have hnorm : ‖f x - f y‖ ≤ A * ‖x-y‖ ^ k := by
    by_cases hxy : x = y
    · subst y; simp; positivity
    · -- affine line from x to y
      let v : E := y-x
      let L : ℝ →L[ℝ] E := (1 : ℝ →L[ℝ] ℝ).smulRight v
      let g : ℝ → F := fun t => f (x + L t)
      have hL (t : ℝ) : L t = t • v := by simp [L]
      have hL1 : L (1:ℝ) = v := by simp [L]
      have hL0 : L (0:ℝ) = (0:E) := by simp [L]
      have hg : ContDiff ℝ (∞ : WithTop ℕ∞) g := by
        dsimp [g]
        exact hf.comp (contDiff_const.add L.contDiff)
      have hk1 : k - 1 + 1 = k := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hk))
      have ht : ContDiffOn ℝ ((k-1)+1 : ℕ) g (Set.Icc (0:ℝ) 1) :=
        (hg.of_le (by rw [hk1]; exact_mod_cast (le_top : (k:ℕ∞) ≤ ⊤))).contDiffOn
      -- all smaller derivatives of this path at zero vanish
      have hpath_iter (i:ℕ) (hi : 1 ≤ i) (hi' : i < k) :
          iteratedDerivWithin i g (Set.Icc (0:ℝ) 1) 0 = 0 := by
        have huq : UniqueDiffOn ℝ (Set.Icc (0:ℝ) 1) :=
          uniqueDiffOn_Icc (by norm_num)
        have heq := iteratedDerivWithin_eq_iteratedDeriv (n:=i) (f:=g)
          (x:=(0:ℝ)) huq
          ((hg.of_le (by exact_mod_cast (le_top : (i:ℕ∞) ≤ ⊤))).contDiffAt)
          (by constructor <;> norm_num : (0:ℝ) ∈ Set.Icc 0 1)
        rw [heq]
        rw [iteratedDeriv_eq_iteratedFDeriv]
        -- formula for composition with the affine map
        have hformula : iteratedFDeriv ℝ i g 0 =
            (iteratedFDeriv ℝ i f x).compContinuousLinearMap (fun _ : Fin i => L) := by
          -- translate then compose with L
          let fx : E → F := fun z => f (x + z)
          have hfx : ContDiff ℝ (∞ : WithTop ℕ∞) fx :=
            hf.comp (contDiff_const.add contDiff_id)
          have hcomp' := L.iteratedFDeriv_comp_right hfx (0:ℝ) (i := i) (by exact_mod_cast (le_top : (i:ℕ∞) ≤ ⊤))
          change iteratedFDeriv ℝ i (fx ∘ (fun t => L t)) 0 = _ at hcomp'
          change iteratedFDeriv ℝ i g 0 = _
          -- orientation of addition in g agrees
          have hxzero : x + L (0:ℝ) = x := by simp [L]
          simpa only [fx, g, Function.comp_def, iteratedFDeriv_comp_add_left, hxzero] using hcomp'
        rw [hformula]
        have hzi := hz x hx i hi hi'
        -- evaluate the multilinear map at ones
        change ((iteratedFDeriv ℝ i f x).compContinuousLinearMap
          (fun _ : Fin i => L)) (fun _ : Fin i => (1:ℝ)) = 0
        simp [ContinuousMultilinearMap.compContinuousLinearMap_apply, hzi]
      -- the Taylor polynomial based at zero is just g 0
      have hpoly : taylorWithinEval g (k-1) (Set.Icc (0:ℝ) 1) 0 1 = g 0 := by
        rw [taylor_within_apply]
        -- range ((k-1)+1)=k
        have hrange : k-1+1 = k := hk1
        rw [hrange]
        -- isolate term zero
        have hkdecomp : Finset.range k = insert 0 ((Finset.range k).erase 0) := by
          exact (Finset.insert_erase (Finset.mem_range.mpr hk)).symm
        rw [hkdecomp, Finset.sum_insert]
        · -- other terms zero
          have hsum : ∑ j ∈ (Finset.range k).erase 0,
              (((j.factorial:ℝ)⁻¹ * ((1:ℝ)-0)^j) •
                iteratedDerivWithin j g (Set.Icc (0:ℝ) 1) 0) = 0 := by
            apply Finset.sum_eq_zero
            intro j hj
            have hj0 : j ≠ 0 := (Finset.mem_erase.mp hj).1
            have hjlt : j < k := Finset.mem_range.mp (Finset.mem_of_mem_erase hj)
            rw [hpath_iter j (Nat.one_le_iff_ne_zero.mpr hj0) hjlt]
            exact smul_zero _
          rw [hsum]
          simp
        · simp
      -- kth derivative along the line is bounded by A*‖v‖^k
      have hderivbound : ∀ t ∈ Set.Icc (0:ℝ) 1,
          ‖iteratedDerivWithin ((k-1)+1) g (Set.Icc (0:ℝ) 1) t‖
            ≤ A * ‖v‖^k := by
        intro t ht'
        have huq : UniqueDiffOn ℝ (Set.Icc (0:ℝ) 1) := uniqueDiffOn_Icc (by norm_num)
        rw [hk1]
        have heq := iteratedDerivWithin_eq_iteratedDeriv (n:=k) (f:=g)
          (x:=t) huq
          ((hg.of_le (by exact_mod_cast (le_top : (k:ℕ∞) ≤ ⊤))).contDiffAt) ht'
        rw [heq]
        rw [iteratedDeriv_eq_iteratedFDeriv]
        -- formula as before
        let fx : E → F := fun z => f (x + z)
        have hfx : ContDiff ℝ (∞ : WithTop ℕ∞) fx :=
          hf.comp (contDiff_const.add contDiff_id)
        have hcomp' := L.iteratedFDeriv_comp_right hfx t (i := k) (by exact_mod_cast (le_top : (k:ℕ∞) ≤ ⊤))
        have hformula : iteratedFDeriv ℝ k g t =
            (iteratedFDeriv ℝ k f (x + L t)).compContinuousLinearMap
              (fun _ : Fin k => L) := by
          simpa only [fx, g, Function.comp_def, iteratedFDeriv_comp_add_left] using hcomp'
        rw [hformula]
        change ‖((iteratedFDeriv ℝ k f (x + L t)).compContinuousLinearMap
            (fun _ : Fin k => L)) (fun _ : Fin k => (1:ℝ))‖ ≤ _
        have hle := (iteratedFDeriv ℝ k f (x + L t)).le_opNorm
          (fun _ : Fin k => v)
        have hmem : x + L t ∈ B := by
          -- convexity of the ball
          have hbconv : Convex ℝ B := convex_closedBall (0:E) R
          have htx : x ∈ B := hs hx
          have hty : y ∈ B := hs hy
          have heq : x + L t = (1-t) • x + t • y := by
            rw [hL]
            dsimp [v]
            module
          rw [heq]
          exact hbconv htx hty (by linarith [ht'.1, ht'.2]) (by linarith [ht'.1]) (by ring)
        have hb := hbound _ hmem
        -- product of norms of a constant vector
        simpa [ContinuousMultilinearMap.compContinuousLinearMap_apply, hL1,
          hb] using
          (hle.trans (mul_le_mul_of_nonneg_right hb
            (by positivity : 0 ≤ ∏ _i : Fin k, ‖v‖)))
      have hTaylor := taylor_mean_remainder_bound (a:=(0:ℝ)) (b:=1)
        (n:=k-1) (f:=g) (by norm_num : (0:ℝ) ≤ 1) ht (by constructor <;> norm_num : (1:ℝ) ∈ Set.Icc 0 1)
        hderivbound
      rw [hpoly] at hTaylor
      -- simplify end points and factorial / unit powers
      have hfac : (1:ℝ) ≤ (Nat.factorial (k-1) : ℝ) := by
        exact_mod_cast (Nat.factorial_pos _)
      have hfacpos : 0 < (Nat.factorial (k-1) : ℝ) := by exact_mod_cast (Nat.factorial_pos (k-1))
      have hT' : ‖f y - f x‖ ≤ A * ‖v‖^k := by
        calc
          ‖f y - f x‖ = ‖g 1 - g 0‖ := by simp [g, L, v]
          _ ≤ (A * ‖v‖^k) * ((1:ℝ)-0)^((k-1)+1) / (Nat.factorial (k-1)) := hTaylor
          _ ≤ A * ‖v‖^k := by
            norm_num
            apply div_le_self
            · positivity
            · exact hfac
      simpa [v, norm_sub_rev] using hT'
  -- pass to extended distances
  rw [edist_dist, edist_dist, dist_eq_norm, dist_eq_norm]
  have hA' : (⟨A,hA⟩ : NNReal).val = A := rfl
  -- holder uses real power; here exponent is a natural number
  change ENNReal.ofReal ‖f x - f y‖ ≤
      ENNReal.ofNNReal (⟨A,hA⟩ : NNReal) * (ENNReal.ofReal ‖x-y‖) ^ ((k : NNReal) : ℝ)
  rw [show ((k : NNReal) : ℝ) = (k : ℕ) by simp,
      ENNReal.rpow_natCast]
  rw [ENNReal.coe_nnreal_eq (⟨A,hA⟩ : NNReal)]
  rw [← ENNReal.ofReal_pow (norm_nonneg _) k]
  change _ ≤ ENNReal.ofReal A * ENNReal.ofReal (‖x-y‖^k)
  · rw [← ENNReal.ofReal_mul hA]
    exact ENNReal.ofReal_le_ofReal hnorm
end SardSupport

-- END INLINED FILE: Mathlib/Support/sard_theorem_8feee3b75b/FlatTaylor.lean

-- BEGIN INLINED FILE: Mathlib/Support/sard_theorem_8feee3b75b/Inverse.lean
open MeasureTheory Module Filter Set Topology
open scoped ContDiff
namespace SardSupport
/-- A global smooth substitute for a local inverse.  Multiplying the smooth local
 inverse by a bump supported in its target is useful when slicing by fibres. -/
theorem exists_global_contDiff_localInverse_target
    {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    [FiniteDimensional ℝ A] [FiniteDimensional ℝ B]
    {P : A → B} (hP : ContDiff ℝ (∞ : WithTop ℕ∞) P)
    (a : A) (e : A ≃L[ℝ] B)
    (he : fderiv ℝ P a = (e : A →L[ℝ] B)) :
    ∃ Q : B → A, ContDiff ℝ (∞ : WithTop ℕ∞) Q ∧
      ∃ O : Set A, O ∈ 𝓝 a ∧
        (∀ x ∈ O, Q (P x) = x) ∧
        (∀ x ∈ O, P (Q (P x)) = P x) := by
  classical
  have hp : HasStrictFDerivAt P (e : A →L[ℝ] B) a := by
    convert hP.contDiffAt.hasStrictFDerivAt (by simp) using 1
    exact he.symm
  let p : OpenPartialHomeomorph A B := hp.toOpenPartialHomeomorph P
  -- Nonvanishing of the determinant of the derivative is needed not only at the
  -- centre but on the inverse chart. We use e as fixed coordinates on the target.
  let T : A → (A →L[ℝ] A) := fun x => (e.symm : B →L[ℝ] A).comp (fderiv ℝ P x)
  let W : Set A := {x | (T x).det ≠ 0}
  have hCW : IsOpen W := by
    have hder : Continuous (fderiv ℝ P) :=
      (contDiff_one_iff_fderiv.mp (hP.of_le (by simp))).2
    have ht : Continuous T :=
      (((ContinuousLinearMap.compL ℝ A B A) (e.symm : B →L[ℝ] A)).continuous.comp hder)
    exact isOpen_compl_singleton.preimage
      (ContinuousLinearMap.continuous_det.comp ht)
  have haW : a ∈ W := by
    change (T a).det ≠ 0
    have hTa : T a = (1 : A →L[ℝ] A) := by
      ext v
      simp [T, he]
    norm_num [hTa, ContinuousLinearMap.det]
  let V : Set B := p.target ∩ p.symm ⁻¹' W
  have hVo : IsOpen V := p.isOpen_inter_preimage_symm hCW
  have haS : a ∈ p.source := hp.mem_toOpenPartialHomeomorph_source
  have hPa : P a ∈ V := by
    refine ⟨hp.image_mem_toOpenPartialHomeomorph_target, ?_⟩
    change p.symm (P a) ∈ W
    have hp' : p.symm (P a) = a := by
      change hp.localInverse P e a (P a) = a
      exact hp.localInverse_apply_image
    rw [hp']
    exact haW
  -- On V the inverse supplied by the open partial homeomorphism is smooth.
  have hinv : ∀ y ∈ V, ContDiffAt ℝ (∞ : WithTop ℕ∞) p.symm y := by
    intro y hy
    have hyT : y ∈ p.target := hy.1
    have hyW : p.symm y ∈ W := hy.2
    let D : A →L[ℝ] A := T (p.symm y)
    have hD : D.det ≠ 0 := hyW
    let de : A ≃L[ℝ] A := D.toContinuousLinearEquivOfDetNeZero hD
    let fe : A ≃L[ℝ] B := de.trans e
    have hcoe : (fe : A →L[ℝ] B) = fderiv ℝ P (p.symm y) := by
      -- compose back with e; D was e^{-1} times the derivative
      ext v
      simp [fe, de, ContinuousLinearMap.toContinuousLinearEquivOfDetNeZero_apply,
        D, T]
    have hfat : HasFDerivAt (p : A → B) (fe : A →L[ℝ] B) (p.symm y) := by
      change HasFDerivAt P (fe : A →L[ℝ] B) (p.symm y)
      rw [hcoe]
      exact (hP.differentiable (by simp)).differentiableAt.hasFDerivAt
    apply p.contDiffAt_symm (f₀' := fe) hyT hfat
    -- p is definitionally P, and P is smooth everywhere
    change ContDiffAt ℝ (∞ : WithTop ℕ∞) P (p.symm y)
    exact hP.contDiffAt
  obtain ⟨d, hd, hdV⟩ := Metric.isOpen_iff.1 hVo (P a) hPa
  -- hd : 0 < d and ball subset; choose a bump with support still in that ball
  let b : ContDiffBump (P a) :=
    ⟨d / 4, d / 2, by linarith, by linarith⟩
  have hbpos : 0 < d := hd
  have hbsub : Metric.closedBall (P a) b.rOut ⊆ V := by
    intro z hz
    apply hdV
    have hz' : dist z (P a) ≤ d / 2 := by simpa [b] using (Metric.mem_closedBall.1 hz)
    have : dist z (P a) < d := lt_of_le_of_lt hz' (by linarith)
    exact Metric.mem_ball.2 this
  let q : B → A := fun z => (b z) • (p.symm z)
  have hq : ContDiff ℝ (∞ : WithTop ℕ∞) q := by
    rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z ∈ Metric.closedBall (P a) b.rOut
    · have hzV : z ∈ V := hbsub hz
      exact (b.contDiffAt (x:=z)).smul (hinv z hzV)
    · have hzU : (Metric.closedBall (P a) b.rOut)ᶜ ∈ 𝓝 z :=
        (Metric.isClosed_closedBall).isOpen_compl.mem_nhds hz
      have heq : q =ᶠ[𝓝 z] (fun _ : B => (0 : A)) := by
        filter_upwards [hzU] with t ht
        have ht0 : b t = 0 := by
          -- outside the closed ball is outside support
          have : b.rOut ≤ dist t (P a) := by
            have : ¬ dist t (P a) ≤ b.rOut := by
              intro hle
              exact ht (Metric.mem_closedBall.2 hle)
            exact le_of_not_gt (fun hlt => this (le_of_lt hlt))
          exact b.zero_of_le_dist this
        simp [q, ht0]
      exact (contDiffAt_const (c := (0 : A))).congr_of_eventuallyEq heq
  refine ⟨q, hq, P ⁻¹' (Metric.ball (P a) b.rIn) ∩ p.source, ?_, ?_, ?_⟩
  · apply Filter.inter_mem
    · exact (hP.continuous.continuousAt.preimage_mem_nhds
          (Metric.ball_mem_nhds _ b.rIn_pos))
    · exact p.open_source.mem_nhds haS
  · intro x hx
    have hx1 : x ∈ p.source := hx.2
    have hxPa : P x ∈ p.target := p.map_source hx1
    have hxinv : p.symm (P x) = x := p.left_inv hx1
    have hb1 : b (P x) = 1 :=
      b.one_of_mem_closedBall (Metric.ball_subset_closedBall hx.1)
    simp [q, hxinv, hb1]
  · intro x hx
    have hqpx : q (P x) = x := by
      have hx1 : x ∈ p.source := hx.2
      have hxinv : p.symm (P x) = x := p.left_inv hx1
      have hb1 : b (P x) = 1 :=
        b.one_of_mem_closedBall (Metric.ball_subset_closedBall hx.1)
      simp [q, hxinv, hb1]
    rw [hqpx]
end SardSupport

-- END INLINED FILE: Mathlib/Support/sard_theorem_8feee3b75b/Inverse.lean

-- BEGIN INLINED FILE: Mathlib/Support/sard_theorem_8feee3b75b/LocalZero.lean
/-!
A small Lindelof null-cover lemma.  The sets which occur in the rank
stratification are not assumed measurable; using ``measure_mono_null`` avoids
that issue.  Second countability of the source, rather than compactness of a
stratum, is the correct hypothesis for this gluing step.
-/
open MeasureTheory Filter Topology Set
namespace SardSupport

 theorem null_image_of_pointwise_nhds
    {X : Type*} [TopologicalSpace X] [SecondCountableTopology X]
    {Z : Type*} [MeasurableSpace Z]
    (μ : Measure Z := by volume_tac)
    {F : X → Z} {s : Set X}
    (h : ∀ a ∈ s, ∃ V ∈ 𝓝 a, μ (F '' (s ∩ V)) = 0) :
    μ (F '' s) = 0 := by
  classical
  -- We choose one of the good neighbourhoods at each of the points of the set.
  -- Values away from the set play no role.
  let V : X → Set X := fun x =>
    if hx : x ∈ s then Classical.choose (h x hx) else Set.univ
  have hVmem : ∀ x ∈ s, V x ∈ 𝓝 x := by
    intro x hx
    dsimp [V]
    rw [dif_pos hx]
    exact (Classical.choose_spec (h x hx)).1
  have hVnull : ∀ x ∈ s, μ (F '' (s ∩ V x)) = 0 := by
    intro x hx
    dsimp [V]
    rw [dif_pos hx]
    exact (Classical.choose_spec (h x hx)).2
  obtain ⟨c, hc, hcsub, hsc⟩ :=
    (HereditarilyLindelofSpace.isLindelof s).elim_nhds_subcover V hVmem
  have hz : μ (⋃ x ∈ c, F '' (s ∩ V x)) = 0 :=
    (measure_biUnion_null_iff hc).2 (by
      intro x hx
      exact hVnull x (hcsub x hx))
  refine measure_mono_null (t := ⋃ x ∈ c, F '' (s ∩ V x)) ?_ hz
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  have hx' := hsc hx
  rcases Set.mem_iUnion.1 hx' with ⟨z, hz⟩
  rcases Set.mem_iUnion.1 hz with ⟨hzc, hxz⟩
  refine Set.mem_iUnion.2 ⟨z, Set.mem_iUnion.2 ⟨hzc, ?_⟩⟩
  exact ⟨x, ⟨hx, hxz⟩, rfl⟩

-- The version for volume is usually inferred from the goal.  Keeping the measure
-- explicit made the statement usable for arbitrary Haar normalisations as well.
end SardSupport

-- END INLINED FILE: Mathlib/Support/sard_theorem_8feee3b75b/LocalZero.lean

-- BEGIN INLINED FILE: Mathlib/Support/sard_theorem_8feee3b75b/FlatDim.lean
open MeasureTheory Module
open scoped ContDiff ENNReal
namespace SardSupport
 theorem nullFlat
    {m n k : ℕ}
    (hk : 0 < k) (hmk : m < n*k)
    {f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    (hf : ContDiff ℝ (∞ : WithTop ℕ∞) f) (R : ℝ)
    {s : Set (EuclideanSpace ℝ (Fin m))}
    (hs : s ⊆ Metric.closedBall 0 R)
    (hzero : ∀ x ∈ s, ∀ j : ℕ, 1 ≤ j → j < k → iteratedFDeriv ℝ j f x = 0) :
    volume (f '' s) = 0 := by
  classical
  obtain ⟨C,hC⟩ := holderOnWith_nat_of_flat hk hf hs hzero
  have hpos : 0 < (k : NNReal) := by exact_mod_cast hk
  have hd0 := hC.dimH_image_le hpos
  have hsle : dimH s ≤ (m : ENNReal) := by
    calc
      dimH s ≤ dimH (Set.univ : Set (EuclideanSpace ℝ (Fin m))) :=
        dimH_mono (Set.subset_univ _)
      _ = (finrank ℝ (EuclideanSpace ℝ (Fin m)) : ℕ) :=
        Real.dimH_univ_eq_finrank _
      _ = (m:ℕ) := by simp
  have hd1 : dimH (f '' s) ≤ (m:ENNReal) / ((k:NNReal):ENNReal) := by
    exact hd0.trans (ENNReal.div_le_div_right hsle _)
  have har : (m:ENNReal) / ((k:NNReal):ENNReal) < (n:ENNReal) := by
    apply (ENNReal.div_lt_iff ?_ ?_).2
    · exact_mod_cast hmk
    · left; exact_mod_cast (Nat.ne_of_gt hk)
    · left; simp
  have hd : dimH (f '' s) < (n:ENNReal) := hd1.trans_lt har
  have H : (μH[(n:ℕ)] : Measure (EuclideanSpace ℝ (Fin n))) (f '' s) = 0 := by
    simpa using (hausdorffMeasure_of_dimH_lt (s:= f '' s) (d := (n:ℕ)) hd)
  rw [← EuclideanSpace.euclideanHausdorffMeasure_eq_volume n]
  rw [MeasureTheory.Measure.euclideanHausdorffMeasure_def]
  simp [H]

/-- bounded flat image, with arbitrary finite-dimensional real source -/
theorem nullFlat_general {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [FiniteDimensional ℝ U]
    {n k : ℕ} (hk : 0 < k) (hdk : finrank ℝ U < n*k)
    {f : U → EuclideanSpace ℝ (Fin n)}
    (hf : ContDiff ℝ (∞ : WithTop ℕ∞) f) (R : ℝ) {s : Set U}
    (hs : s ⊆ Metric.closedBall 0 R)
    (hz : ∀ x ∈ s, ∀ j : ℕ, 1 ≤ j → j < k → iteratedFDeriv ℝ j f x = 0) :
    volume (f '' s) = 0 := by
  classical
  obtain ⟨C,hC⟩ := holderOnWith_nat_of_flat hk hf hs hz
  have hp : 0 < (k : NNReal) := by exact_mod_cast hk
  have hd0 := hC.dimH_image_le hp
  have hsle : dimH s ≤ (finrank ℝ U : ENNReal) := by
    calc
      dimH s ≤ dimH (Set.univ : Set U) := dimH_mono (Set.subset_univ _)
      _ = _ := Real.dimH_univ_eq_finrank _
  have hd1 : dimH (f '' s) ≤ (finrank ℝ U : ENNReal) / ((k:NNReal):ENNReal) :=
    hd0.trans (ENNReal.div_le_div_right hsle _)
  have ha : (finrank ℝ U : ENNReal) / ((k:NNReal):ENNReal) < (n:ENNReal) := by
    apply (ENNReal.div_lt_iff ?_ ?_).2
    · exact_mod_cast hdk
    · left; exact_mod_cast (Nat.ne_of_gt hk)
    · left; simp
  have hd : dimH (f '' s) < (n:ENNReal) := hd1.trans_lt ha
  have H : (μH[(n:ℕ)] : Measure (EuclideanSpace ℝ (Fin n))) (f '' s) = 0 := by
    simpa using (hausdorffMeasure_of_dimH_lt (s:= f '' s) (d:= (n:ℕ)) hd)
  rw [← EuclideanSpace.euclideanHausdorffMeasure_eq_volume n]
  rw [MeasureTheory.Measure.euclideanHausdorffMeasure_def]
  simp [H]
end SardSupport

-- END INLINED FILE: Mathlib/Support/sard_theorem_8feee3b75b/FlatDim.lean

-- BEGIN INLINED FILE: Mathlib/Support/sard_theorem_8feee3b75b/LocalSmooth.lean
namespace SardSupport
end SardSupport

-- END INLINED FILE: Mathlib/Support/sard_theorem_8feee3b75b/LocalSmooth.lean

-- BEGIN INLINED FILE: Mathlib/Support/sard_theorem_8feee3b75b/RankLinear.lean
open Module
namespace SardSupport
/-- If a quotient of a linear map is onto and has the same (finite) rank,
all tangent vectors killed by that quotient were already killed by the
map.  This is the little rank calculation in the positive-rank chart of
Sard; formulating it with the range subspace avoids any choice of bases. -/
theorem map_eq_zero_of_comp_eq_zero_of_finrank_range_eq
    {K U V W : Type*} [DivisionRing K]
    [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (T : U →ₗ[K] V) (p : V →ₗ[K] W)
    (onto : LinearMap.range (p.comp T) = ⊤)
    (rankT : finrank K (LinearMap.range T) = finrank K W)
    {v : U} (hv : (p.comp T) v = 0) : T v = 0 := by
  let r : LinearMap.range T →ₗ[K] W := p.domRestrict (LinearMap.range T)
  have hr : Function.Surjective r := by
    intro w
    have hw : w ∈ LinearMap.range (p.comp T) := by rw [onto]; trivial
    rcases hw with ⟨u, hu⟩
    refine ⟨⟨T u, ⟨u, rfl⟩⟩, ?_⟩
    exact hu
  have hi : Function.Injective r :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rankT).2 hr
  let tv : LinearMap.range T := ⟨T v, ⟨v, rfl⟩⟩
  have hrv : r tv = r 0 := by
    change p (T v) = p 0
    simpa using hv
  have hz : tv = 0 := hi hrv
  exact congrArg Subtype.val hz

/-- A version saying that a linear variation in a fibre has zero derivative. -/
theorem comp_eq_zero_of_finrank_range_eq
    {K U V W Z : Type*} [DivisionRing K]
    [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    [AddCommGroup Z] [Module K Z]
    (T : U →ₗ[K] V) (p : V →ₗ[K] W) (i : Z →ₗ[K] U)
    (onto : LinearMap.range (p.comp T) = ⊤)
    (rankT : finrank K (LinearMap.range T) = finrank K W)
    (fib : (p.comp T).comp i = 0) : T.comp i = 0 := by
  ext z
  exact map_eq_zero_of_comp_eq_zero_of_finrank_range_eq T p onto rankT
    (by simpa using LinearMap.congr_fun fib z)
end SardSupport

-- END INLINED FILE: Mathlib/Support/sard_theorem_8feee3b75b/RankLinear.lean

-- BEGIN INLINED FILE: Mathlib/Support/sard_theorem_8feee3b75b/Flat.lean
open MeasureTheory Module
open scoped ContDiff
namespace SardSupport
/-- The Taylor covering (very flat stratum) part of Sard.  Kept separately because it
is also the base case of the kernel induction. -/
theorem null_image_of_iteratedFDeriv_eq_zero
    {m n k : ℕ}
    (hk : 0 < k) (hmk : m < n*k)
    {f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    (hf : ContDiff ℝ (∞ : WithTop ℕ∞) f) (R : ℝ)
    {s : Set (EuclideanSpace ℝ (Fin m))}
    (hs : s ⊆ Metric.closedBall 0 R)
    (hzero : ∀ x ∈ s, ∀ j : ℕ, 1 ≤ j → j < k → iteratedFDeriv ℝ j f x = 0) :
    volume (f '' s) = 0 := by
  exact nullFlat hk hmk hf R hs hzero
end SardSupport

-- END INLINED FILE: Mathlib/Support/sard_theorem_8feee3b75b/Flat.lean

-- BEGIN INLINED FILE: Mathlib/Support/sard_theorem_8feee3b75b/SliceGeneral.lean
open MeasureTheory Set Filter Module Topology
namespace SardSupport
/-- Safe Fubini step for a chart.  The compactness hypothesis is intentional: the
rank strata themselves need not be measurable a priori, but their relatively
closed compact pieces have compact image. -/
theorem null_image_fiber_compact_left
    {A B C : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
    [MeasureSpace A] [BorelSpace A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]
    [MeasureSpace B] [BorelSpace B]
    [NormedAddCommGroup C] [NormedSpace ℝ C] [FiniteDimensional ℝ C]
    [MeasureSpace C] [BorelSpace C]
    {s : Set (A × B)} (hs : IsCompact s)
    {F : A × B → C} (hF : Continuous F)
    (hz : ∀ y : A,
      (volume : Measure C)
        ( (fun z : B => F (y,z)) '' {z : B | (y,z) ∈ s}) = 0) :
    ((volume : Measure A).prod (volume : Measure C))
      ((fun z : A × B => (z.1, F z)) '' s) = 0 := by
  classical
  let T : Set (A × C) := (fun z : A × B => (z.1, F z)) '' s
  have hcont : Continuous (fun z : A × B => (z.1, F z)) :=
    continuous_fst.prodMk hF
  have hTm : MeasurableSet T := (hs.image hcont).isClosed.measurableSet
  -- Work with the product definition of volume. Every section is contained in
  -- the corresponding fibre image; no equality or measurability of the
  -- pre-chart set is required here.
  apply MeasureTheory.Measure.measure_prod_null_of_ae_null hTm
  filter_upwards [] with y
  have hsub : Prod.mk y ⁻¹' T ⊆
      (fun z : B => F (y,z)) '' {z : B | (y,z) ∈ s} := by
    intro c hc
    rcases hc with ⟨u, hu, huc⟩
    -- equality of first and second coordinates
    have h1 : u.1 = y := by
      have := congrArg Prod.fst huc
      simpa using this
    -- rewrite the first coordinate before taking the second one
    rcases u with ⟨u1, u2⟩
    dsimp at h1 ⊢
    subst u1
    refine ⟨u2, ?_, ?_⟩
    · exact hu
    · simpa using congrArg Prod.snd huc
  exact measure_mono_null hsub (hz y)
end SardSupport

-- END INLINED FILE: Mathlib/Support/sard_theorem_8feee3b75b/SliceGeneral.lean

-- BEGIN INLINED FILE: Mathlib/Support/sard_theorem_8feee3b75b/ZeroAll.lean
open MeasureTheory Module Filter Set Topology
open scoped ContDiff ENNReal
namespace SardSupport

/-- The zero-rank part of Morse's argument.  We state the induction with the
source dimension as an explicit argument; this makes it possible to apply it
to the kernel of a scalar submersion. -/
theorem null_rankzero_dim {n : ℕ} (hn : 0 < n) :
    ∀ d : ℕ, ∀ (U : Type*) [NormedAddCommGroup U] [NormedSpace ℝ U]
      [FiniteDimensional ℝ U], finrank ℝ U = d →
      ∀ (f : U → EuclideanSpace ℝ (Fin n)),
        ContDiff ℝ (∞ : WithTop ℕ∞) f → ∀ s : Set U,
        (∀ x ∈ s, finrank ℝ (LinearMap.range (fderiv ℝ f x).toLinearMap) = 0) →
        volume (f '' s) = 0 := by
  classical
  intro d
  induction d using Nat.strong_induction_on with
  | h d IH =>
    intro U _ _ _ hdim f hf s hs0
    -- first isolate the set on which all the first `d` derivatives vanish.
    let k : ℕ := d + 1
    have hk : 0 < k := by simp [k]
    have hdk : finrank ℝ U < n * k := by
      rw [hdim]
      dsimp [k]
      nlinarith
    let u : Set U :=
      {x ∈ s | ∀ j : ℕ, 1 ≤ j → j < k → iteratedFDeriv ℝ j f x = 0}
    have hflat : volume (f '' u) = 0 := by
      -- On a bounded ball this is the Taylor covering lemma; exhaust the
      -- source by closed balls.
      suffices H : ∀ R : ℕ, volume (f '' (u ∩ Metric.closedBall (0:U) R)) = 0 by
        rw [← nonpos_iff_eq_zero, ← Metric.iUnion_inter_closedBall_nat u 0]
        calc
          volume (f '' ⋃ R : ℕ, u ∩ Metric.closedBall 0 (R:ℝ)) ≤
              ∑' R : ℕ, volume (f '' (u ∩ Metric.closedBall 0 (R:ℝ))) := by
                rw [Set.image_iUnion]
                exact measure_iUnion_le _
          _ ≤ 0 := by simp only [H, tsum_zero, nonpos_iff_eq_zero]
      intro R
      apply nullFlat_general (n:=n) (k:=k) hk hdk hf (R:ℝ)
        (by intro x hx; exact hx.2)
      intro x hx j hj hj'
      exact hx.1.2 j hj hj'
    -- The other pieces have a first non-zero derivative.  The preceding
    -- derivative supplies a scalar equation with non-zero gradient.
    let v : ℕ → Set U := fun j =>
      {x ∈ s | 2 ≤ j ∧ j < k ∧
        (∀ i : ℕ, 1 ≤ i → i < j → iteratedFDeriv ℝ i f x = 0) ∧
        iteratedFDeriv ℝ j f x ≠ 0}
    have hv : ∀ j : ℕ, volume (f '' v j) = 0 := by
      intro j
      -- the proof only uses the data carried by a point of this set
      apply null_image_of_pointwise_nhds
      intro a ha
      have hj2 : 2 ≤ j := ha.2.1
      obtain ⟨l, rfl⟩ : ∃ l : ℕ, j = l + 1 := by
        refine ⟨j-1, ?_⟩; omega
      have hl : 1 ≤ l := by omega
      -- choose entries on which the first nonzero multilinear form is visible
      have hnon : iteratedFDeriv ℝ (l+1) f a ≠ 0 := ha.2.2.2.2
      have harg : ∃ m : Fin (l+1) → U,
          iteratedFDeriv ℝ (l+1) f a m ≠ 0 := by
        by_contra hbad
        push_neg at hbad
        have hz' : iteratedFDeriv ℝ (l+1) f a = 0 := by
          apply ContinuousMultilinearMap.ext
          intro t
          simpa using hbad t
        exact hnon hz'
      choose m hm using harg
      have hcoord : ∃ i : Fin n, (iteratedFDeriv ℝ (l+1) f a m) i ≠ 0 := by
        by_contra hbad
        push_neg at hbad
        have hz' : iteratedFDeriv ℝ (l+1) f a m = 0 := by
          ext i
          exact hbad i
        exact hm hz'
      choose i hi using hcoord
      let ev : (U[×l]→L[ℝ] EuclideanSpace ℝ (Fin n)) →L[ℝ]
          EuclideanSpace ℝ (Fin n) :=
        ContinuousMultilinearMap.apply ℝ (fun _ : Fin l => U)
          (EuclideanSpace ℝ (Fin n)) (Fin.tail m)
      let pi : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
        PiLp.proj (p := (2:ENNReal)) (𝕜 := ℝ) (fun _ : Fin n => ℝ) i
      let out : (U[×l]→L[ℝ] EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ := pi.comp ev
      let gg : U → ℝ := fun x => out (iteratedFDeriv ℝ l f x)
      have hfl : ContDiff ℝ (∞ : WithTop ℕ∞)
          (iteratedFDeriv ℝ l f) :=
        (by
          rw [contDiff_infty]
          intro t
          exact hf.iteratedFDeriv_right (m := (t : WithTop ℕ∞)) (by
            exact_mod_cast (show (t:ℕ∞) + l ≤ (⊤ : ℕ∞) from le_top)))
      have hg : ContDiff ℝ (∞ : WithTop ℕ∞) gg := out.contDiff.comp hfl
      let D : U →L[ℝ] ℝ := fderiv ℝ gg a
      have hDform : fderiv ℝ gg a = out.comp (fderiv ℝ (iteratedFDeriv ℝ l f) a) := by
        have h1 :=
          (out.hasFDerivAt (x := iteratedFDeriv ℝ l f a)).comp a
            ((hfl.differentiable (by simp)).differentiableAt.hasFDerivAt)
        exact h1.fderiv
      have hDv : D (m 0) ≠ 0 := by
        change fderiv ℝ gg a (m 0) ≠ 0
        rw [hDform]
        change ((fderiv ℝ (iteratedFDeriv ℝ l f) a (m 0)) (Fin.tail m)) i ≠ 0
        rw [← iteratedFDeriv_succ_apply_left m]
        exact hi
      have honto : LinearMap.range D.toLinearMap = ⊤ := by
        apply LinearMap.range_eq_top.mpr
        intro y
        refine ⟨(y / D (m 0)) • (m 0), ?_⟩
        change D ((y / D (m 0)) • (m 0)) = y
        rw [map_smul]
        dsimp
        field_simp
      let hdg : HasStrictFDerivAt gg D a := by
        dsimp [D]
        exact hg.contDiffAt.hasStrictFDerivAt (by simp)
      let hker := D.ker_closedComplemented_of_finiteDimensional_range
      let chart : OpenPartialHomeomorph U (ℝ × D.toLinearMap.ker) :=
        hdg.implicitToOpenPartialHomeomorph gg D honto
      have ha_chart : a ∈ chart.source := by
        dsimp [chart]
        exact HasStrictFDerivAt.mem_implicitToOpenPartialHomeomorph_source hdg honto
      let P : U → (ℝ × D.toLinearMap.ker) := fun x => chart x
      have hP : ContDiff ℝ (∞ : WithTop ℕ∞) P := by
        change ContDiff ℝ (∞ : WithTop ℕ∞)
          (fun x : U => (gg x, (Classical.choose hker) (x-a)))
        exact hg.prodMk ((Classical.choose hker).contDiff.comp
          (contDiff_id.sub contDiff_const))
      let phi := HasStrictFDerivAt.implicitFunctionDataOfComplemented
          gg D hdg honto hker
      let be : U ≃L[ℝ] (ℝ × D.toLinearMap.ker) :=
        (phi.leftDeriv.equivProdOfSurjectiveOfIsCompl phi.rightDeriv
          phi.range_leftDeriv phi.range_rightDeriv phi.isCompl_ker).toContinuousLinearEquiv
      have hbe : fderiv ℝ P a = (be : U →L[ℝ] (ℝ × D.toLinearMap.ker)) := by
        exact phi.hasStrictFDerivAt.hasFDerivAt.fderiv
      obtain ⟨Q,hQ,O,hO,hleft,_⟩ :=
        exists_global_contDiff_localInverse_target hP a be hbe
      -- Every point of the stratum has value zero for the scalar equation.
      have hgeq {x : U} (hx : x ∈ v (l+1)) : gg x = 0 := by
        have hzero := hx.2.2.2.1 l (by omega) (by omega)
        -- evaluate the zero multilinear map on the fixed tuple
        change out (iteratedFDeriv ℝ l f x) = 0
        rw [hzero]
        simp
      refine ⟨O, hO, ?_⟩
      let emb : D.toLinearMap.ker →L[ℝ] (ℝ × D.toLinearMap.ker) :=
        ContinuousLinearMap.inr ℝ ℝ D.toLinearMap.ker
      let FF : D.toLinearMap.ker → EuclideanSpace ℝ (Fin n) :=
        fun z => f (Q (emb z))
      let ss : Set D.toLinearMap.ker :=
        {z | Q (emb z) ∈ v (l+1) ∩ O}
      have hFF : ContDiff ℝ (∞ : WithTop ℕ∞) FF := by
        exact hf.comp (hQ.comp emb.contDiff)
      have hdimker : finrank ℝ D.toLinearMap.ker < d := by
        have htot := LinearMap.finrank_range_add_finrank_ker D.toLinearMap
        have hr : finrank ℝ (LinearMap.range D.toLinearMap) = 1 := by
          rw [honto, finrank_top]
          simp
        rw [hr, hdim] at htot
        omega
      have hzFF : ∀ z ∈ ss,
          finrank ℝ (LinearMap.range (fderiv ℝ FF z).toLinearMap) = 0 := by
        intro z hz
        have hx : Q (emb z) ∈ s := hz.1.1
        have hzx := hs0 _ hx
        have hsub : Subsingleton
            (LinearMap.range (fderiv ℝ f (Q (emb z))).toLinearMap) :=
          (Module.finrank_zero_iff).1 hzx
        have hb : LinearMap.range (fderiv ℝ f (Q (emb z))).toLinearMap = ⊥ :=
          Submodule.subsingleton_iff_eq_bot.mp hsub
        have hlin : (fderiv ℝ f (Q (emb z))).toLinearMap = 0 :=
          LinearMap.range_eq_bot.mp hb
        have hfz : fderiv ℝ f (Q (emb z)) = 0 := by
          apply ContinuousLinearMap.ext
          intro w
          exact LinearMap.congr_fun hlin w
        have hchain : HasFDerivAt FF
            ((fderiv ℝ f (Q (emb z))).comp
              ((fderiv ℝ Q (emb z)).comp emb)) z := by
          have hqz : HasFDerivAt Q (fderiv ℝ Q (emb z)) (emb z) :=
            (hQ.differentiable (by simp)).differentiableAt.hasFDerivAt
          have hez : HasFDerivAt (fun w : D.toLinearMap.ker => Q (emb w))
              ((fderiv ℝ Q (emb z)).comp emb) z := by
            convert hqz.comp z (emb.hasFDerivAt) using 1 <;> rfl
          have hf0 := (hf.differentiable (by simp)).differentiableAt.hasFDerivAt
            (x := Q (emb z))
          convert hf0.comp z hez using 1 <;> rfl
        have hz' : fderiv ℝ FF z = 0 := by
          simpa [hfz] using hchain.fderiv
        rw [hz']
        change finrank ℝ (LinearMap.range (0 :
          D.toLinearMap.ker →ₗ[ℝ] EuclideanSpace ℝ (Fin n))) = 0
        rw [LinearMap.range_zero]
        simp
      have Hker : volume (FF '' ss) = 0 :=
        IH (finrank ℝ D.toLinearMap.ker) hdimker
          D.toLinearMap.ker rfl FF hFF ss hzFF
      refine measure_mono_null ?_ Hker
      intro y hy
      rcases hy with ⟨x,hx,rfl⟩
      have hgx : gg x = 0 := hgeq hx.1
      have hpx : P x = (0, (P x).2) := by
        apply Prod.ext
        · change gg x = 0
          exact hgx
        · rfl
      have hqpx : Q (emb (P x).2) = x := by
        have := hleft x hx.2
        change Q (P x) = x at this
        have hemb : emb (P x).2 = (0, (P x).2) := rfl
        rw [hemb, ← hpx]
        exact this
      refine ⟨(P x).2, ?_, ?_⟩
      · change Q (emb (P x).2) ∈ v (l+1) ∩ O
        rw [hqpx]
        exact hx
      · change f (Q (emb (P x).2)) = f x
        rw [hqpx]
    -- put the pieces and the flat part back together
    have hvU : volume (⋃ j : ℕ, f '' v j) = 0 := by
      rw [← nonpos_iff_eq_zero]
      calc
        volume (⋃ j : ℕ, f '' v j) ≤ ∑' j : ℕ, volume (f '' v j) :=
          measure_iUnion_le _
        _ ≤ 0 := by simp only [hv, tsum_zero, nonpos_iff_eq_zero]
    have hrest : volume (f '' (s \ u)) = 0 := by
      apply measure_mono_null (t := ⋃ j : ℕ, f '' v j) ?_ hvU
      intro y hy
      rcases hy with ⟨x,hx,rfl⟩
      have hnot : ¬ ∀ j : ℕ, 1 ≤ j → j < k → iteratedFDeriv ℝ j f x = 0 := by
        intro hh
        exact hx.2 ⟨hx.1, hh⟩
      push_neg at hnot
      obtain ⟨j,hj,hjk,hne⟩ := hnot
      -- take the least nonzero order
      let T : Set ℕ := {r | 1 ≤ r ∧ r < k ∧ iteratedFDeriv ℝ r f x ≠ 0}
      have hT : T.Nonempty := ⟨j,hj,hjk,hne⟩
      let r := sInf T
      have hrT : r ∈ T := Nat.sInf_mem hT
      have hrzero : ∀ i : ℕ, 1 ≤ i → i < r →
          iteratedFDeriv ℝ i f x = 0 := by
        intro i hi hir
        by_contra hn0
        have hiT : i ∈ T := ⟨hi, lt_of_lt_of_le hir (Nat.sInf_mem hT).2.1.le, hn0⟩
        have := Nat.sInf_le hiT
        omega
      have hfirstzero : iteratedFDeriv ℝ 1 f x = 0 := by
        have hzx := hs0 x hx.1
        have hsub : Subsingleton (LinearMap.range
            (fderiv ℝ f x).toLinearMap) := (Module.finrank_zero_iff).1 hzx
        have hbot : LinearMap.range (fderiv ℝ f x).toLinearMap = ⊥ :=
          Submodule.subsingleton_iff_eq_bot.mp hsub
        have hlin : (fderiv ℝ f x).toLinearMap = 0 :=
          LinearMap.range_eq_bot.mp hbot
        apply ContinuousMultilinearMap.ext
        intro a
        rw [iteratedFDeriv_one_apply]
        change fderiv ℝ f x _ = _
        exact LinearMap.congr_fun hlin (a 0)
      have hr2 : 2 ≤ r := by
        have hrpos := hrT.1
        have hrne : r ≠ 1 := by
          intro e
          have hne := hrT.2.2
          rw [e] at hne
          exact hne hfirstzero
        omega
      have hxv : x ∈ v r :=
        ⟨hx.1, hr2, hrT.2.1, hrzero, hrT.2.2⟩
      exact Set.mem_iUnion.2 ⟨r, ⟨x,hxv,rfl⟩⟩
    apply measure_mono_null (t := f '' u ∪ f '' (s \ u)) ?_
      (MeasureTheory.measure_union_null hflat hrest)
    intro y hy
    rcases hy with ⟨x,hx,rfl⟩
    by_cases hxu : x ∈ u
    · exact Or.inl ⟨x,hxu,rfl⟩
    · exact Or.inr ⟨x,⟨hx,hxu⟩,rfl⟩
end SardSupport

-- END INLINED FILE: Mathlib/Support/sard_theorem_8feee3b75b/ZeroAll.lean

-- BEGIN INLINED FILE: Mathlib/Support/sard_theorem_8feee3b75b/FirstNonzero.lean
namespace SardSupport
end SardSupport

-- END INLINED FILE: Mathlib/Support/sard_theorem_8feee3b75b/FirstNonzero.lean

-- BEGIN INLINED FILE: Mathlib/Support/sard_theorem_8feee3b75b/RankZero.lean
open MeasureTheory Module
open scoped ContDiff
namespace SardSupport
/-- Morse's zero-rank induction, valid with an arbitrary finite-dimensional real domain.
The codomain is Euclidean, so that its Haar measure is the canonical volume. -/
theorem null_image_of_rankzero_all
    {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [FiniteDimensional ℝ U]
    {n : ℕ} (hn : 0 < n)
    {f : U → EuclideanSpace ℝ (Fin n)}
    (hf : ContDiff ℝ (∞ : WithTop ℕ∞) f)
    (s : Set U)
    (hz : ∀ x ∈ s, finrank ℝ (LinearMap.range (fderiv ℝ f x).toLinearMap) = 0) :
    volume (f '' s) = 0 := by
  classical
  by_cases hsmall : finrank ℝ U < n * 2
  · suffices H : ∀ R : ℕ, volume (f '' (s ∩ Metric.closedBall (0:U) R)) = 0 by
      rw [← nonpos_iff_eq_zero, ← Metric.iUnion_inter_closedBall_nat s 0]
      calc
        volume (f '' ⋃ R : ℕ, s ∩ Metric.closedBall 0 (R:ℝ)) ≤
            ∑' R : ℕ, volume (f '' (s ∩ Metric.closedBall 0 (R:ℝ))) := by
              rw [Set.image_iUnion]
              exact measure_iUnion_le _
        _ ≤ 0 := by simp only [H, tsum_zero, nonpos_iff_eq_zero]
    intro R
    apply nullFlat_general (n:=n) (k:=2) (by omega) hsmall hf (R:ℝ)
      (by intro x hx; exact hx.2)
    intro x hx j hj hj'
    have hjone : j = 1 := by omega
    subst j
    have h0 := hz x hx.1
    have hsub : Subsingleton (LinearMap.range
        (fderiv ℝ f x).toLinearMap) := (Module.finrank_zero_iff).1 h0
    have hbot : LinearMap.range (fderiv ℝ f x).toLinearMap = ⊥ :=
      Submodule.subsingleton_iff_eq_bot.mp hsub
    have hlin : (fderiv ℝ f x).toLinearMap = 0 :=
      LinearMap.range_eq_bot.mp hbot
    apply ContinuousMultilinearMap.ext
    intro a
    rw [iteratedFDeriv_one_apply]
    change fderiv ℝ f x _ = _
    simpa using LinearMap.congr_fun hlin (a 0)
  · -- in the remaining dimensions use the scalar-hypersurface induction
    -- (it also proves the smaller-dimensional case).
    exact null_rankzero_dim hn (finrank ℝ U) U rfl f hf s hz
end SardSupport

-- END INLINED FILE: Mathlib/Support/sard_theorem_8feee3b75b/RankZero.lean

-- BEGIN INLINED FILE: Mathlib/Support/sard_theorem_8feee3b75b/Pos.lean
open MeasureTheory Set Filter Module Topology
open scoped ContDiff
namespace SardSupport
/-- The rank-zero lemma after an orthonormal change of coordinates.  It is handy for
orthogonal complements in a rank chart. -/
theorem null_image_of_deriv_zero_inner
    {U C : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [FiniteDimensional ℝ U]
    [NormedAddCommGroup C] [InnerProductSpace ℝ C]
    [FiniteDimensional ℝ C] [MeasurableSpace C] [BorelSpace C]
    (hn : 0 < finrank ℝ C)
    {h : U → C} (hh : ContDiff ℝ (∞ : WithTop ℕ∞) h)
    (s : Set U) (hz : ∀ x ∈ s, fderiv ℝ h x = 0) :
    (volume : Measure C) (h '' s) = 0 := by
  classical
  let e := (stdOrthonormalBasis ℝ C).repr
  let d := finrank ℝ C
  let h' : U → EuclideanSpace ℝ (Fin d) := fun x => e (h x)
  have hec : ContDiff ℝ (∞ : WithTop ℕ∞) (e : C → EuclideanSpace ℝ (Fin d)) := e.contDiff
  have hh' : ContDiff ℝ (∞ : WithTop ℕ∞) h' := hec.comp hh
  have hz' : ∀ x ∈ s,
      finrank ℝ (LinearMap.range (fderiv ℝ h' x).toLinearMap) = 0 := by
    intro x hx
    have hzero : fderiv ℝ h' x = 0 := by
      have hc := (e : C →L[ℝ] EuclideanSpace ℝ (Fin d)).hasFDerivAt (x := h x)
      have hv : HasFDerivAt h (0 : U →L[ℝ] C) x := by
        have hx0 : HasFDerivAt h (fderiv ℝ h x) x :=
          (hh.differentiable (by simp)).differentiableAt.hasFDerivAt
        rwa [hz x hx] at hx0
      have H := hc.comp x hv
      change fderiv ℝ (e ∘ h) x = 0
      simpa using H.fderiv
    rw [hzero]
    simp
  have hnull : volume (h' '' s) = 0 :=
    null_image_of_rankzero_all (U:=U) (n:=d) hn hh' s hz'
  have heq : h' '' s = e '' (h '' s) := by
    ext z
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact ⟨h x, ⟨x,hx,rfl⟩, rfl⟩
    · rintro ⟨y,⟨x,hx,rfl⟩,rfl⟩
      exact ⟨x,hx,rfl⟩
  -- pull a null set back by the measure preserving isometry
  have hp := e.measurePreserving
  have hpre := hp.quasiMeasurePreserving.preimage_null (heq ▸ hnull)
  have hset : (e : C → EuclideanSpace ℝ (Fin d)) ⁻¹' (e '' (h '' s)) = h '' s := by
    ext y
    constructor
    · intro hy
      rcases hy with ⟨z,hz,hez⟩
      have : y = z := e.injective hez.symm
      simpa [this] using hz
    · intro hy
      exact ⟨y, hy, rfl⟩
  simpa [hset] using hpre

/-- A linear equivalence carries a product-Haar null set to a null set.  We use
this rather than any normalization of Haar on products. -/
theorem linearEquiv_image_prod_null
    {A C N : Type*}
    [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
    [MeasureSpace A] [BorelSpace A]
    [NormedAddCommGroup C] [InnerProductSpace ℝ C] [FiniteDimensional ℝ C]
    [MeasureSpace C] [BorelSpace C]
    [NormedAddCommGroup N] [InnerProductSpace ℝ N] [FiniteDimensional ℝ N]
    [MeasureSpace N] [BorelSpace N]
    [(volume : Measure A).IsAddHaarMeasure]
    [(volume : Measure C).IsAddHaarMeasure]
    [(volume : Measure N).IsAddHaarMeasure]
    (L : (A × C) ≃L[ℝ] N) {T : Set (A × C)} (hT : IsCompact T)
    (h0 : ((volume : Measure A).prod (volume : Measure C)) T = 0) :
    (volume : Measure N) (L '' T) = 0 := by
  classical
  let μ : Measure (A × C) := (volume : Measure A).prod (volume : Measure C)
  have hc := (L : (A × C) →ₗ[ℝ] N).exists_map_addHaar_eq_smul_addHaar
      μ (volume : Measure N) L.surjective
  rcases hc with ⟨c, hcpos, hcmap⟩
  have hTm : MeasurableSet (L '' T) :=
    (hT.image L.continuous).isClosed.measurableSet
  have hpre : (L : (A × C) → N) ⁻¹' (L '' T) = T := by
    ext z
    constructor
    · rintro ⟨w,hw,eqw⟩
      have : z = w := L.injective eqw.symm
      simpa [this] using hw
    · intro hz
      exact ⟨z,hz,rfl⟩
  have hmzero : (Measure.map (L : (A × C) → N) μ) (L '' T) = 0 := by
    rw [Measure.map_apply L.continuous.measurable hTm, hpre]
    exact h0
  change (Measure.map (L : (A × C) → N) μ) (L '' T) = 0 at hmzero
  have hcmap' : Measure.map (L : (A × C) → N) μ = c • (volume : Measure N) := hcmap
  rw [hcmap'] at hmzero
  -- a positive scalar cannot kill a nonzero value
  change c * (volume : Measure N) (L '' T) = 0 at hmzero
  exact (mul_eq_zero.mp hmzero).resolve_left (ne_of_gt hcpos)

/-- In finite dimensions the last open rank condition says precisely surjectivity. -/
theorem range_eq_top_of_finrank_le_rank
    {U V : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [FiniteDimensional ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (T : U →ₗ[ℝ] V)
    (h : (finrank ℝ V : Cardinal) ≤ T.rank) :
    LinearMap.range T = ⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  apply le_antisymm
  · exact Submodule.finrank_le _
  · have h' : (finrank ℝ V : Cardinal) ≤
          Module.rank ℝ (LinearMap.range T) := h
    rw [← Module.finrank_eq_rank ℝ (LinearMap.range T)] at h'
    exact_mod_cast h'


/-- Compact portion of a positive-rank chart.  The open partial homeomorphism
has first coordinate the projected map.  A smooth global inverse is only
required on an open piece containing the compact set. -/
theorem null_image_compact_rank_chart
    {X N B : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup N] [InnerProductSpace ℝ N] [FiniteDimensional ℝ N]
      [MeasurableSpace N] [BorelSpace N]
    [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B]
      [MeasureSpace B] [BorelSpace B]
    (Y : Submodule ℝ N)
    {f : X → N} (hf : ContDiff ℝ (∞ : WithTop ℕ∞) f)
    (P : OpenPartialHomeomorph X (Y × B))
    (hfirst : ∀ x : X, (P x).1 = Y.orthogonalProjectionOnto (f x))
    {Q : Y × B → X} (hQ : ContDiff ℝ (∞ : WithTop ℕ∞) Q)
    {H Cset : Set X} (hHop : IsOpen H) (hCH : Cset ⊆ H)
    (hC : IsCompact Cset)
    (hsource : H ⊆ P.source)
    (hleft : ∀ x ∈ H, Q (P x) = x)
    (honto : ∀ x ∈ Cset,
      LinearMap.range
        ((Y.orthogonalProjectionOnto : N →L[ℝ] Y).toLinearMap.comp
          (fderiv ℝ f x).toLinearMap) = ⊤)
    (hrank : ∀ x ∈ Cset,
      finrank ℝ (LinearMap.range (fderiv ℝ f x).toLinearMap) = finrank ℝ Y)
    (hperp : 0 < finrank ℝ (Yᗮ)) :
    (volume : Measure N) (f '' Cset) = 0 := by
  classical
  let pc : N →L[ℝ] (Yᗮ) := (Yᗮ).orthogonalProjectionOnto
  let F : Y × B → (Yᗮ) := fun z => pc (f (Q z))
  have hFsm : ContDiff ℝ (∞ : WithTop ℕ∞) F :=
    pc.contDiff.comp (hf.comp hQ)
  let S : Set (Y × B) := P '' Cset
  have hS : IsCompact S := by
    exact hC.image_of_continuousOn (P.continuousOn.mono (fun x hx => hsource (hCH hx)))
  -- On the image of the open piece the bumped inverse is the true inverse.
  have hnear : ∀ x ∈ Cset,
      (fun z : Y × B => Y.orthogonalProjectionOnto (f (Q z))) =ᶠ[𝓝 (P x)]
        (fun z : Y × B => z.1) := by
    intro x hx
    have hxH : x ∈ H := hCH hx
    let W : Set (Y × B) := P.target ∩ (P.symm : (Y × B) → X) ⁻¹' H
    have hWo : IsOpen W := P.isOpen_inter_preimage_symm hHop
    have hxsrc : x ∈ P.source := hsource hxH
    have hxW : P x ∈ W := by
      refine ⟨P.map_source hxsrc, ?_⟩
      simpa [P.left_inv hxsrc] using hxH
    have hnh : W ∈ 𝓝 (P x) := hWo.mem_nhds hxW
    filter_upwards [hnh] with z hz
    have ztar : z ∈ P.target := hz.1
    have zH : P.symm z ∈ H := hz.2
    have zeq : P (P.symm z) = z := P.right_inv ztar
    have qeq : Q z = P.symm z := by
      have t := hleft (P.symm z) zH
      rw [zeq] at t
      exact t
    rw [qeq]
    exact (hfirst (P.symm z)).symm.trans (congrArg Prod.fst zeq)
  have hzder : ∀ y : Y,
      (volume : Measure (Yᗮ))
        ((fun b : B => F (y,b)) '' {b : B | (y,b) ∈ S}) = 0 := by
    intro y
    -- every derivative along this fibre vanishes on its compact section
    have hzero : ∀ b ∈ {b : B | (y,b) ∈ S},
        fderiv ℝ (fun b : B => F (y,b)) b = 0 := by
      intro b hb
      rcases hb with ⟨x,hx,hxb⟩
      -- hxb : P x = (y,b)
      have hxq : Q (y,b) = x := by
        have := hleft x (hCH hx)
        simpa [hxb] using this
      let T : X →L[ℝ] N := fderiv ℝ f x
      let D : (Y × B) →L[ℝ] X := fderiv ℝ Q (y,b)
      let i : B →L[ℝ] (Y × B) := ContinuousLinearMap.inr ℝ Y B
      -- differentiate the first-coordinate identity on a neighborhood
      have hdev :
          (Y.orthogonalProjectionOnto : N →L[ℝ] Y).comp (T.comp D) =
            ContinuousLinearMap.fst ℝ Y B := by
        have hev := hnear x hx
        rw [hxb] at hev
        have hdEq := hev.fderiv_eq (𝕜 := ℝ)
        -- compute derivative of the composition
        have hQd : HasFDerivAt Q D (y,b) := by
          exact (hQ.differentiable (by simp)).differentiableAt.hasFDerivAt
        have hfd : HasFDerivAt f T x := by
          exact (hf.differentiable (by simp)).differentiableAt.hasFDerivAt
        have hfd' : HasFDerivAt f T (Q (y,b)) := by simpa [hxq] using hfd
        have hpfd := (Y.orthogonalProjectionOnto : N →L[ℝ] Y).hasFDerivAt
          (x := f (Q (y,b)))
        have compd := hpfd.comp (y,b) (hfd'.comp (y,b) hQd)
        have hfstD : fderiv ℝ (fun z : Y × B => z.1) (y,b) =
            ContinuousLinearMap.fst ℝ Y B :=
          (ContinuousLinearMap.fderiv (ContinuousLinearMap.fst ℝ Y B))
        have calcD : fderiv ℝ
            (fun z : Y × B => Y.orthogonalProjectionOnto (f (Q z))) (y,b) =
            (Y.orthogonalProjectionOnto : N →L[ℝ] Y).comp (T.comp D) := by
          simpa [ContinuousLinearMap.comp_assoc, Function.comp_def] using compd.fderiv
        rw [calcD, hfstD] at hdEq
        exact hdEq
      have hTi : (T.toLinearMap.comp D.toLinearMap).comp i.toLinearMap =
          (T.comp (D.comp i)).toLinearMap := by rfl
      have hkill : T.toLinearMap.comp (D.comp i).toLinearMap = 0 := by
        -- rank argument, directions in the second coordinate
        apply SardSupport.comp_eq_zero_of_finrank_range_eq
          T.toLinearMap (Y.orthogonalProjectionOnto : N →L[ℝ] Y).toLinearMap
            (D.comp i).toLinearMap (honto x hx) (hrank x hx)
        -- the projected derivative is fst, hence vanishes on inr
        apply LinearMap.ext
        intro v
        have hv := congrArg (fun k : (Y × B →L[ℝ] Y) => k (i v)) hdev
        change Y.orthogonalProjectionOnto (T (D (0,v))) = 0
        change Y.orthogonalProjectionOnto (T (D (0,v))) = ( (0,v) : Y × B).1 at hv
        simpa using hv
      -- derivative of the perpendicular component restricted to the fibre
      have hQd : HasFDerivAt Q D (y,b) := (hQ.differentiable (by simp)).differentiableAt.hasFDerivAt
      have hi' : HasFDerivAt (fun z : B => (y,z)) i b := by
        -- affine insertion
        convert (hasFDerivAt_const (x:=b) (c:=y)).prodMk
          ((ContinuousLinearMap.id ℝ B).hasFDerivAt (x:=b)) using 1 <;>
          ext z <;> simp [i]
      have hfd : HasFDerivAt f T (Q (y,b)) := by
        have := (hf.differentiable (by simp)).differentiableAt.hasFDerivAt
          (x := x)
        simpa [T, hxq] using this
      have hpc := pc.hasFDerivAt (x := f (Q (y,b)))
      have hall := hpc.comp b ((hfd.comp (y,b) hQd).comp b hi')
      have hall' : fderiv ℝ (fun b : B => F (y,b)) b =
           pc.comp (T.comp (D.comp i)) := by
        simpa [F, ContinuousLinearMap.comp_assoc, Function.comp_def] using hall.fderiv
      rw [hall']
      have hzlin : (T.comp (D.comp i)) = 0 := by
        ext v
        exact LinearMap.congr_fun hkill v
      simp [hzlin]
    exact null_image_of_deriv_zero_inner hperp
      (hFsm.comp (contDiff_const.prodMk contDiff_id)) _ hzero
  have hT0 : ((volume : Measure Y).prod (volume : Measure (Yᗮ)))
      ((fun z : Y × B => (z.1, F z)) '' S) = 0 :=
    null_image_fiber_compact_left hS hFsm.continuous hzder
  let L : (Y × (Yᗮ)) ≃L[ℝ] N :=
    (Y.prodEquivOfIsCompl (Yᗮ) Y.isCompl_orthogonal).toContinuousLinearEquiv
  let Tset : Set (Y × (Yᗮ)) := (fun z : Y × B => (z.1, F z)) '' S
  have hTcomp : IsCompact Tset := hS.image (continuous_fst.prodMk hFsm.continuous)
  have hsum (z : N) :
      ((Y.orthogonalProjectionOnto z : Y) : N) +
        (((pc z : Yᗮ) : N)) = z := by
    simpa [pc, Submodule.orthogonalProjectionOnto_apply_eq_projectionOnto]
      using (Y.projection_add_projection_eq_self Y.isCompl_orthogonal z)
  have hLapply (u : Y) (v : Yᗮ) : L (u,v) = (u : N) + (v : N) := by
    rfl
  have hLT : (L : Y × (Yᗮ) → N) '' Tset = f '' Cset := by
    ext z
    constructor
    · rintro ⟨u,⟨v,hv,rfl⟩,rfl⟩
      rcases hv with ⟨x,hx,hxv⟩
      subst v
      have hxq : Q (P x) = x := hleft x (hCH hx)
      refine ⟨x,hx,?_⟩
      simp only [hLapply, F]
      rw [hxq, hfirst]
      exact (hsum (f x)).symm
    · rintro ⟨x,hx,rfl⟩
      refine ⟨((P x).1, pc (f (Q (P x)))), ?_, ?_⟩
      · exact ⟨P x, ⟨x,hx,rfl⟩, rfl⟩
      have hxq : Q (P x) = x := hleft x (hCH hx)
      simp only [hLapply]
      rw [hxq, hfirst]
      exact hsum (f x)

  rw [← hLT]
  exact linearEquiv_image_prod_null L hTcomp hT0
end SardSupport

-- END INLINED FILE: Mathlib/Support/sard_theorem_8feee3b75b/Pos.lean

-- BEGIN INLINED FILE: Mathlib/Support/sard_theorem_8feee3b75b/ZeroInduction.lean
namespace SardSupport
end SardSupport

-- END INLINED FILE: Mathlib/Support/sard_theorem_8feee3b75b/ZeroInduction.lean

-- BEGIN INLINED FILE: Mathlib/Support/sard_theorem_8feee3b75b/Slice.lean
namespace SardSupport
end SardSupport

-- END INLINED FILE: Mathlib/Support/sard_theorem_8feee3b75b/Slice.lean

namespace Submission

-- BEGIN INLINED FILE: Main.lean
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 200000

namespace LeanEval
namespace Geometry
namespace SardTheoremProblem

/-!
# Sard's theorem (Morse 1939 / Sard 1942), Knill's rank-deficient form

For a smooth map `f : ℝᵐ → ℝⁿ`, the image of the rank-deficient set
`{x | rank df(x) < m ∧ rank df(x) < n}` — points where the Jacobian
`df(x)` is neither injective nor surjective — has Lebesgue measure
zero. The manifold form follows from this Euclidean version
chart-by-chart, so the substance of the theorem lives at the
Euclidean level used here. §125 of Knill's *Some Fundamental Theorems
in Mathematics*.

This is Knill's specific phrasing: "rank smaller than both `m` and
`n`". The standard textbook Sard theorem instead defines critical
points by `rank df(x) < n` (failure of surjectivity), which is a
weaker condition than Knill's and produces a larger critical set; the
textbook statement therefore *implies* the form proved here. The two
agree when `m ≥ n`; for `m < n` a smooth immersion has every point
critical under the textbook definition but no critical points under
Knill's.

Mathlib has the equal-dimension case `μ (f '' s) = 0` when
`det (f' x) = 0` on `s`
(`MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero`)
plus topological corollaries via Hausdorff dimension, but no general
critical-value / Sard statement.
-/

open MeasureTheory Module
open scoped ContDiff

/-- The Euclidean model space `ℝⁿ`. -/
abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The rank of the Fréchet derivative of `f` at `x`. -/
noncomputable def fderivRank {m n : ℕ} (f : E m → E n) (x : E m) : ℕ :=
  finrank ℝ (LinearMap.range (fderiv ℝ f x).toLinearMap)

/-- A **critical point** of `f` (Knill's definition): a point where
`df(x)` has rank less than both `m` and `n`, so `df(x)` fails to have
full rank `min m n`. Weaker than the textbook condition
`rank df(x) < n`; see the module docstring. -/
def IsCriticalPoint {m n : ℕ} (f : E m → E n) (x : E m) : Prop :=
  fderivRank f x < m ∧ fderivRank f x < n

/-- The **critical values** of `f`: the image in `ℝⁿ` of the
rank-deficient locus. -/
def criticalValues {m n : ℕ} (f : E m → E n) : Set (E n) :=
  f '' {x | IsCriticalPoint f x}



end SardTheoremProblem
end Geometry
end LeanEval

open LeanEval.Geometry.SardTheoremProblem
open MeasureTheory Module
open scoped ContDiff
/-ResultDefinitionsBegin-/
/-ResultProofDefinitionsBegin-/
/-ResultProofDefinitionsEnd-/
/-ResultDefinitionsEnd-/

/-ResultBegin-/

theorem sard {m n : ℕ} (f : E m → E n) (_hf : ContDiff ℝ ∞ f) :
    volume (criticalValues f) = 0 :=
/-ResultProofBegin-/ by
  rcases lt_trichotomy m n with hmn | hmn | hnm
  · -- Maps to a higher dimensional Euclidean space already have a null range.  This
    -- useful easy part of Sard only uses the Hausdorff-dimension bound for C¹ maps.
    have hf1 : ContDiff ℝ 1 f := _hf.of_le (by simp)
    have hdim_le : dimH (Set.range f) ≤ (m : ℕ) := by
      simpa using hf1.dimH_range_le
    have hdim : dimH (Set.range f) < (n : ℕ) := by
      exact hdim_le.trans_lt (by exact_mod_cast hmn)
    have H : (μH[(n:ℕ)] : Measure (E n)) (Set.range f) = 0 := by
      simpa using (hausdorffMeasure_of_dimH_lt (s := Set.range f)
        (d := (n : ℕ)) hdim)
    have Hrange : volume (Set.range f) = 0 := by
      rw [← EuclideanSpace.euclideanHausdorffMeasure_eq_volume n]
      rw [MeasureTheory.Measure.euclideanHausdorffMeasure_def]
      simp [H]
    exact measure_mono_null (Set.image_subset_range f {x | IsCriticalPoint f x})
      Hrange
  · -- In equal dimensions the Jacobian/determinant lemma in mathlib is enough.
    subst n
    let s : Set (E m) := {x | IsCriticalPoint f x}
    change volume (f '' s) = 0
    apply MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero (volume)
      (s := s) (f' := fun x => fderiv ℝ f x)
    · intro x hx
      exact (_hf.differentiable (by simp)).differentiableAt.hasFDerivAt.hasFDerivWithinAt
    · intro x hx
      by_contra hdet
      have hrange : LinearMap.range (fderiv ℝ f x).toLinearMap = ⊤ := by
        apply LinearMap.range_eq_top.mpr
        intro y
        let e := (fderiv ℝ f x).toContinuousLinearEquivOfDetNeZero hdet
        obtain ⟨z, hz⟩ := e.surjective y
        refine ⟨z, ?_⟩
        change (fderiv ℝ f x) z = y
        simpa [e] using hz
      have hfin : finrank ℝ (LinearMap.range (fderiv ℝ f x).toLinearMap) = m := by
        rw [hrange, finrank_top]
        simp
      have hxrank : fderivRank f x < m := hx.1
      exact (Nat.ne_of_lt hxrank) hfin
  · -- Except for the zero-dimensional target, this is the
    -- positive-codimension-fibre case of Sard.
    cases n with
    | zero =>
      have hs : criticalValues f = (∅ : Set (E 0)) := by
        apply Set.not_nonempty_iff_eq_empty.mp
        intro hy
        rcases hy with ⟨y, x, hx, hxy⟩
        change f x = y at hxy
        exact (Nat.not_lt_zero _ hx.2)
      rw [hs]
      exact measure_empty
    | succ q =>
      -- At this point only the textbook Sard statement remains: for `m > n > 0`
      -- the image of the non-surjective-derivative locus is null.  Notice that no
      -- measurability of that locus is needed for either reduction.
      have htextbook :
          volume (f '' {x : E m | fderivRank f x < q.succ}) = 0 := by
        let t : Set (E m) := {x : E m | fderivRank f x < q.succ}
        change volume (f '' t) = 0
        -- The nonsurjective locus is closed.  Writing this using cardinal rank makes it
        -- an immediate consequence of the openness of the `rank ≥ k` condition on
        -- continuous linear maps; in finite dimensions cardinal rank is `finrank`.
        have htclosed : IsClosed t := by
          have hf1' : ContDiff ℝ 1 f := _hf.of_le (by simp)
          have hcont : Continuous (fderiv ℝ f) := (contDiff_one_iff_fderiv.mp hf1').2
          have hopen : IsOpen
              {x : E m | (q.succ : Cardinal) ≤ (fderiv ℝ f x).toLinearMap.rank} := by
            exact
              (isOpen_setOf_nat_le_rank (𝕜 := ℝ) (E := E m)
                  (F := E q.succ) q.succ).preimage hcont
          have heq : tᶜ =
              {x : E m | (q.succ : Cardinal) ≤
                (fderiv ℝ f x).toLinearMap.rank} := by
            ext x
            change (¬ fderivRank f x < q.succ) ↔
              (q.succ : Cardinal) ≤ (fderiv ℝ f x).toLinearMap.rank
            have hr := Module.finrank_eq_rank ℝ
              (LinearMap.range (fderiv ℝ f x).toLinearMap)
            constructor
            · intro h
              have hn : q.succ ≤
                  finrank ℝ (LinearMap.range (fderiv ℝ f x).toLinearMap) :=
                Nat.le_of_not_gt h
              have hc : (q.succ : Cardinal) ≤
                  (finrank ℝ (LinearMap.range
                    (fderiv ℝ f x).toLinearMap) : Cardinal) := by
                exact_mod_cast hn
              change (q.succ : Cardinal) ≤
                Module.rank ℝ (LinearMap.range (fderiv ℝ f x).toLinearMap)
              rwa [← hr]
            · intro h
              change (q.succ : Cardinal) ≤
                Module.rank ℝ (LinearMap.range
                  (fderiv ℝ f x).toLinearMap) at h
              rw [← hr] at h
              have hn : q.succ ≤
                  finrank ℝ (LinearMap.range (fderiv ℝ f x).toLinearMap) := by
                exact_mod_cast h
              exact Nat.not_lt_of_ge hn
          rw [← isOpen_compl_iff, heq]
          exact hopen

        suffices H : ∀ R : ℕ, volume (f '' (t ∩ Metric.closedBall 0 R)) = 0 by
          rw [← nonpos_iff_eq_zero, ← Metric.iUnion_inter_closedBall_nat t 0]
          calc
            volume (f '' ⋃ R : ℕ, t ∩ Metric.closedBall 0 R) ≤
                ∑' R : ℕ, volume (f '' (t ∩ Metric.closedBall 0 R)) := by
                  rw [Set.image_iUnion]
                  exact measure_iUnion_le _
            _ ≤ 0 := by simp only [H, tsum_zero, nonpos_iff_eq_zero]
        intro R
        have hcomp : IsCompact (t ∩ Metric.closedBall (0 : E m) R) :=
          (ProperSpace.isCompact_closedBall (0 : E m) R).inter_left htclosed
        have hcomp' : IsCompact (f '' (t ∩ Metric.closedBall (0 : E m) R)) :=
          hcomp.image _hf.continuous
        -- Separate the very flat stratum.  The Taylor/Holder estimate for this
        -- one is independent of the normal-form part of Sard.
        classical
        let K : Set (E m) := t ∩ Metric.closedBall (0 : E m) R
        let k : ℕ := m + 1
        let u : Set (E m) :=
          {x ∈ K | ∀ j : ℕ, 1 ≤ j → j < k → iteratedFDeriv ℝ j f x = 0}
        have hk : 0 < k := by simp [k]
        have hmk : m < q.succ * k := by
          dsimp [k]
          have hq : 0 < q.succ := Nat.succ_pos _
          nlinarith
        have hu_ball : u ⊆ Metric.closedBall (0 : E m) (R:ℝ) := by
          intro x hx
          exact hx.1.2
        have hflat : volume (f '' u) = 0 := by
          apply SardSupport.null_image_of_iteratedFDeriv_eq_zero
            (m := m) (n := q.succ) (k := k) hk hmk _hf (R:ℝ) hu_ball
          intro x hx j hj hj'
          exact hx.2 j hj hj'
        -- Break the complement up by the first non-zero higher derivative. This is countable
        -- (indeed finite), so after this step the remaining local problem has fixed order.
        let v : ℕ → Set (E m) := fun j =>
          {x ∈ K | 1 ≤ j ∧ j < k ∧ iteratedFDeriv ℝ j f x ≠ 0}
        have hpieces : ∀ j : ℕ, volume (f '' v j) = 0 := by
          intro j
          by_cases hjok : 1 ≤ j ∧ j < k
          · -- Also fix the rank.  This finite/countable decomposition is often useful before
            -- applying the constant-rank normal form.
            let w : ℕ → Set (E m) := fun r => {x ∈ v j | fderivRank f x = r}
            have hw : ∀ r : ℕ, volume (f '' w r) = 0 := by
              intro r
              by_cases hr : r < q.succ
              · by_cases hc : r = 0 ∧ j = 1
                · obtain ⟨rfl, rfl⟩ := hc
                  -- On the rank-zero stratum the first derivative vanishes. Thus the
                  -- "nonzero order one" piece is actually empty.
                  have hempty0 : w 0 = (∅ : Set (E m)) := by
                    ext x
                    constructor
                    · intro hx
                      have hxne : iteratedFDeriv ℝ 1 f x ≠ 0 := hx.1.2.2.2
                      have hzero : fderivRank f x = 0 := hx.2
                      change finrank ℝ (LinearMap.range
                        (fderiv ℝ f x).toLinearMap) = 0 at hzero
                      have hs0 : Subsingleton (LinearMap.range
                          (fderiv ℝ f x).toLinearMap) :=
                        (Module.finrank_zero_iff).1 hzero
                      have hbot : LinearMap.range (fderiv ℝ f x).toLinearMap = ⊥ :=
                        Submodule.subsingleton_iff_eq_bot.mp hs0
                      have hlin : (fderiv ℝ f x).toLinearMap = 0 :=
                        LinearMap.range_eq_bot.mp hbot
                      have happ (a : E m) : fderiv ℝ f x a = 0 := by
                        have za := LinearMap.congr_fun hlin a
                        exact za
                      have hiter : iteratedFDeriv ℝ 1 f x = 0 := by
                        apply ContinuousMultilinearMap.ext
                        intro a
                        rw [iteratedFDeriv_one_apply]
                        change fderiv ℝ f x _ = _
                        simpa using happ (a 0)
                      exact False.elim (hxne hiter)
                    · intro hx
                      cases hx
                  rw [hempty0]
                  simp
                · -- The entire zero-rank part is now the dimension induction on
                  -- kernels.  Thus the only remaining stratum really has
                  -- positive rank.
                  by_cases hz0 : r = 0
                  · subst r
                    apply SardSupport.null_image_of_rankzero_all
                      (U := E m) (n := q.succ) (Nat.succ_pos q) _hf (w 0)
                    intro x hx
                    exact hx.2
                  · -- positive-rank constant-rank stratum
                    -- It is enough to produce a null coordinate patch at each point;
                    -- second countability, not any measurability of this stratum, patches
                    -- them (the centres are chosen by the Lindelöf lemma).
                    apply SardSupport.null_image_of_pointwise_nhds
                    intro a ha
                    -- Choose the visible block as the actual range at the centre.
                    -- Orthogonal projection onto this range is a submersion after
                    -- composing with `f`; this is the input to the implicit chart.
                    let L : (E m →L[ℝ] E q.succ) := fderiv ℝ f a
                    let Y : Submodule ℝ (E q.succ) := LinearMap.range L.toLinearMap
                    let pr : E q.succ →L[ℝ] Y := Y.orthogonalProjection
                    let g : E m → Y := fun x => pr (f x)
                    have hg : ContDiff ℝ (∞ : WithTop ℕ∞) g := by
                      exact pr.contDiff.comp _hf
                    have hgd : fderiv ℝ g a = pr.comp L := by
                      have h1 := pr.hasFDerivAt (x := f a)
                      have h2 : HasFDerivAt f (fderiv ℝ f a) a :=
                        (_hf.differentiable (by simp)).differentiableAt.hasFDerivAt
                      have h3 := h1.comp a h2
                      exact h3.fderiv
                    have hsur : (fderiv ℝ g a).toLinearMap.range = ⊤ := by
                      rw [hgd]
                      apply LinearMap.range_eq_top.mpr
                      intro y
                      rcases y.property with ⟨z,hz⟩
                      refine ⟨z, ?_⟩
                      change pr (L z) = y
                      change Y.orthogonalProjectionOnto (L z) = y
                      have hz' : L z = (y : E q.succ) := hz
                      rw [hz']
                      exact Y.orthogonalProjectionOnto_mem_subspace_eq_self y
                    let dg : E m →L[ℝ] Y := fderiv ℝ g a
                    let echart : OpenPartialHomeomorph (E m) (Y × dg.ker) :=
                      ((hg.contDiffAt.hasStrictFDerivAt (by simp)).implicitToOpenPartialHomeomorph
                        g dg hsur)
                    have ha_chart : a ∈ echart.source := by
                      dsimp [echart]
                      exact HasStrictFDerivAt.mem_implicitToOpenPartialHomeomorph_source
                        (hg.contDiffAt.hasStrictFDerivAt (by simp)) hsur
                    -- It remains to use this product chart and orthogonal decomposition
                    -- of the codomain on a smaller relatively closed compact piece;
                    -- `null_image_fiber_rankzero_compact_left` is the Fubini step.
                    let hk := dg.ker_closedComplemented_of_finiteDimensional_range
                    let hdg : HasStrictFDerivAt g dg a :=
                      hg.contDiffAt.hasStrictFDerivAt (by simp)
                    let Ψ : E m → (Y × dg.ker) := fun x => echart x
                    have hΨ : ContDiff ℝ (∞ : WithTop ℕ∞) Ψ := by
                      change ContDiff ℝ (∞ : WithTop ℕ∞)
                        (fun x : E m => (g x, (Classical.choose hk) (x-a)))
                      exact hg.prodMk ((Classical.choose hk).contDiff.comp
                        (contDiff_id.sub contDiff_const))
                    let φ := HasStrictFDerivAt.implicitFunctionDataOfComplemented
                      g dg hdg hsur hk
                    let be : E m ≃L[ℝ] (Y × dg.ker) :=
                      (φ.leftDeriv.equivProdOfSurjectiveOfIsCompl φ.rightDeriv
                        φ.range_leftDeriv φ.range_rightDeriv
                        φ.isCompl_ker).toContinuousLinearEquiv
                    have hbe : fderiv ℝ Ψ a = (be : E m →L[ℝ] (Y × dg.ker)) := by
                      exact φ.hasStrictFDerivAt.hasFDerivAt.fderiv
                    obtain ⟨Q,hQ,O,hO,hOsrc,hrep⟩ :=
                      SardSupport.exists_global_contDiff_localInverse_target hΨ a be hbe
                    -- We record carefully the neighbourhood on which the *global*
                    -- smooth inverse is the inverse of the partial chart.  This avoids
                    -- extending a chart by zero (that extension is not smooth).
                    have hlocal : ∃ V : Set (E m), V ∈ nhds a ∧
                        ∀ x ∈ V, echart x ∈ echart.target ∧ Q (echart x) = x := by
                      refine ⟨O ∩ echart.source, Filter.inter_mem hO
                        (echart.open_source.mem_nhds ha_chart), ?_⟩
                      intro x hx
                      have xs : x ∈ echart.source := hx.2
                      constructor
                      · exact echart.map_source xs
                      · change Q (Ψ x) = x
                        -- hOsrc is the left inverse part of the bumped inverse;
                        -- hrep is its image equality.
                        exact hOsrc x hx.1
                    -- The remaining step is the Fubini calculation in these
                    -- coordinates. `map_eq_zero_of_comp_eq_zero_of_finrank_range_eq`
                    -- is the purely linear rank calculation: since projection to `Y`
                    -- is onto and both ranks are `r`, every derivative in a `dg.ker`
                    -- direction is zero. On relatively closed compact coordinate
                    -- pieces `null_image_fiber_compact_left` then reduces the assertion
                    -- to the zero-rank theorem on each fixed `Y` fibre.

                    -- Work on a small ball in this chart.  We enlarge the stratum to the
                    -- closed rank-≤ r part of the compact set; on the open set where the
                    -- chosen minor is onto this has exactly rank r.  Thus its ball cut is
                    -- compact and the compact chart lemma applies.
                    have hYr : finrank ℝ Y = r := by
                      change finrank ℝ (LinearMap.range
                        (fderiv ℝ f a).toLinearMap) = r
                      exact ha.2
                    have hperp : 0 < finrank ℝ (Yᗮ) := by
                      have hd := Y.finrank_add_finrank_orthogonal
                      have hE : finrank ℝ (E q.succ) = q.succ := by simp
                      rw [hYr, hE] at hd
                      omega
                    let Aproj : (E q.succ →L[ℝ] Y) := Y.orthogonalProjectionOnto
                    let dproj : E m → (E m →L[ℝ] Y) :=
                      fun x => Aproj.comp (fderiv ℝ f x)
                    let Uonto : Set (E m) :=
                      {x | (finrank ℝ Y : Cardinal) ≤
                        (dproj x).toLinearMap.rank}
                    have hdercont : Continuous (fderiv ℝ f) :=
                      (contDiff_one_iff_fderiv.mp (_hf.of_le (by simp))).2
                    have hdc : Continuous dproj := by
                      dsimp [dproj]
                      exact (((ContinuousLinearMap.compL ℝ (E m)
                        (E q.succ) Y) Aproj).continuous.comp hdercont)
                    have hUopen : IsOpen Uonto := by
                      exact (isOpen_setOf_nat_le_rank (𝕜 := ℝ)
                        (E := E m) (F := Y) (finrank ℝ Y)).preimage hdc
                    have honto_a : LinearMap.range
                        ((Aproj.comp (fderiv ℝ f a)).toLinearMap) = ⊤ := by
                      -- this is precisely the surjectivity used to build the chart
                      have hs := hsur
                      rw [hgd] at hs
                      simpa [Aproj, pr, L] using hs
                    have haU : a ∈ Uonto := by
                      change (finrank ℝ Y : Cardinal) ≤
                        ((Aproj.comp (fderiv ℝ f a)).toLinearMap).rank
                      change (finrank ℝ Y : Cardinal) ≤
                        Module.rank ℝ
                          (LinearMap.range ((Aproj.comp (fderiv ℝ f a)).toLinearMap))
                      rw [honto_a, ← Module.finrank_eq_rank ℝ (⊤ : Submodule ℝ Y)]
                      simp
                    -- take an actually open neighbourhood inside the one supplied by the
                    -- bumped inverse
                    rcases (mem_nhds_iff.mp hO) with ⟨O', hO'sub, hO'op, haO'⟩
                    let H : Set (E m) := (O' ∩ echart.source) ∩ Uonto
                    have hHop : IsOpen H :=
                      (hO'op.inter echart.open_source).inter hUopen
                    have haH : a ∈ H := ⟨⟨haO', ha_chart⟩, haU⟩
                    have hsourceH : H ⊆ echart.source := by
                      intro x hx
                      exact hx.1.2
                    have hHO : H ⊆ O := by
                      intro x hx
                      exact hO'sub hx.1.1
                    have hleftH : ∀ x ∈ H, Q (echart x) = x := by
                      intro x hx
                      change Q (Ψ x) = x
                      exact hOsrc x (hHO hx)
                    -- the closed rank at most r condition
                    let sr : Set (E m) := {x : E m | fderivRank f x < r.succ}
                    have hsr : IsClosed sr := by
                      have hopen' : IsOpen
                          {x : E m | (r.succ : Cardinal) ≤
                            (fderiv ℝ f x).toLinearMap.rank} :=
                        (isOpen_setOf_nat_le_rank (𝕜 := ℝ)
                          (E := E m) (F := E q.succ) r.succ).preimage hdercont
                      have heq' : srᶜ =
                          {x : E m | (r.succ : Cardinal) ≤
                            (fderiv ℝ f x).toLinearMap.rank} := by
                        ext x
                        change (¬ fderivRank f x < r.succ) ↔
                          (r.succ : Cardinal) ≤
                            (fderiv ℝ f x).toLinearMap.rank
                        have hh := Module.finrank_eq_rank ℝ
                          (LinearMap.range (fderiv ℝ f x).toLinearMap)
                        constructor
                        · intro hx
                          have hn : r.succ ≤ finrank ℝ
                              (LinearMap.range (fderiv ℝ f x).toLinearMap) :=
                            Nat.le_of_not_gt hx
                          have hc' : (r.succ : Cardinal) ≤
                              (finrank ℝ
                                (LinearMap.range (fderiv ℝ f x).toLinearMap) :
                                  Cardinal) := by
                            exact_mod_cast hn
                          change (r.succ : Cardinal) ≤
                            Module.rank ℝ
                              (LinearMap.range (fderiv ℝ f x).toLinearMap)
                          rwa [← hh]
                        · intro hx
                          change (r.succ : Cardinal) ≤ Module.rank ℝ
                            (LinearMap.range (fderiv ℝ f x).toLinearMap) at hx
                          rw [← hh] at hx
                          have hn : r.succ ≤ finrank ℝ
                              (LinearMap.range (fderiv ℝ f x).toLinearMap) := by
                            exact_mod_cast hx
                          exact Nat.not_lt_of_ge hn
                      rw [← isOpen_compl_iff, heq']
                      exact hopen'
                    -- a closed ball still contained in H
                    rcases (Metric.isOpen_iff.1 hHop a haH) with
                      ⟨δ, hδ, hδH⟩
                    let epsi : ℝ := δ / 2
                    have hepsi : 0 < epsi := by dsimp [epsi]; linarith
                    have hcb : Metric.closedBall a epsi ⊆ H := by
                      intro x hx
                      apply hδH
                      exact Metric.closedBall_subset_ball (by
                        dsimp [epsi]; linarith) hx
                    let Cset : Set (E m) :=
                      (K ∩ sr) ∩ Metric.closedBall a epsi
                    have hKcomp : IsCompact K := by
                      simpa [K] using hcomp
                    have hCcomp : IsCompact Cset := by
                      dsimp [Cset]
                      exact (hKcomp.inter_right hsr).inter_right
                        Metric.isClosed_closedBall
                    have hCH : Cset ⊆ H := by
                      intro x hx
                      exact hcb hx.2
                    have hontoC : ∀ x ∈ Cset,
                        LinearMap.range
                          ((Y.orthogonalProjectionOnto : E q.succ →L[ℝ] Y).toLinearMap.comp
                            (fderiv ℝ f x).toLinearMap) = ⊤ := by
                      intro x hx
                      have hxU : x ∈ Uonto := (hCH hx).2
                      change (finrank ℝ Y : Cardinal) ≤
                        (dproj x).toLinearMap.rank at hxU
                      have := SardSupport.range_eq_top_of_finrank_le_rank
                        ((Aproj.comp (fderiv ℝ f x)).toLinearMap) hxU
                      simpa [dproj, Aproj] using this
                    have hrankC : ∀ x ∈ Cset,
                        finrank ℝ
                          (LinearMap.range (fderiv ℝ f x).toLinearMap) =
                            finrank ℝ Y := by
                      intro x hx
                      have hxlt : fderivRank f x < r.succ := hx.1.2
                      have hxle : finrank ℝ
                          (LinearMap.range (fderiv ℝ f x).toLinearMap) ≤ r := by
                        exact (Nat.lt_succ_iff.mp hxlt)
                      have hxU : x ∈ Uonto := (hCH hx).2
                      change (finrank ℝ Y : Cardinal) ≤
                        ((Aproj.comp (fderiv ℝ f x)).toLinearMap).rank at hxU
                      have hcard : (finrank ℝ Y : Cardinal) ≤
                          ((fderiv ℝ f x).toLinearMap).rank :=
                        le_trans hxU
                          (LinearMap.rank_comp_le_right
                            (fderiv ℝ f x).toLinearMap Aproj.toLinearMap)
                      change (finrank ℝ Y : Cardinal) ≤
                        Module.rank ℝ
                          (LinearMap.range (fderiv ℝ f x).toLinearMap) at hcard
                      rw [← Module.finrank_eq_rank ℝ
                          (LinearMap.range (fderiv ℝ f x).toLinearMap)] at hcard
                      have hxge : finrank ℝ Y ≤
                          finrank ℝ
                            (LinearMap.range (fderiv ℝ f x).toLinearMap) := by
                        exact_mod_cast hcard
                      omega
                    have hfirst : ∀ x : E m,
                        (echart x).1 = Y.orthogonalProjectionOnto (f x) := by
                      intro x
                      change pr (f x) = Y.orthogonalProjectionOnto (f x)
                      rfl
                    have hCnull : volume (f '' Cset) = 0 := by
                      apply SardSupport.null_image_compact_rank_chart
                        (Y := Y) (f := f) _hf (P := echart) hfirst
                        (Q := Q) hQ hHop hCH hCcomp hsourceH hleftH hontoC
                        hrankC hperp
                    refine ⟨Metric.ball a epsi,
                      Metric.ball_mem_nhds _ hepsi, ?_⟩
                    apply measure_mono_null (t := f '' Cset) ?_ hCnull
                    intro z hz
                    rcases hz with ⟨x, hx, rfl⟩
                    have hxw : x ∈ w r := hx.1
                    have hxball : x ∈ Metric.ball a epsi := hx.2
                    have hxK : x ∈ K := hxw.1.1
                    have hxrank : fderivRank f x = r := hxw.2
                    have hxsr : x ∈ sr := by
                      change fderivRank f x < r.succ
                      omega
                    have hxclosed : x ∈ Metric.closedBall a epsi :=
                      Metric.ball_subset_closedBall hxball
                    exact ⟨x, ⟨⟨hxK, hxsr⟩, hxclosed⟩, rfl⟩
              · have hempty : w r = (∅ : Set (E m)) := by
                  ext x
                  constructor
                  · intro hx
                    have hxK : x ∈ K := hx.1.1
                    have hxT : x ∈ t := hxK.1
                    have hxlt : fderivRank f x < q.succ := hxT
                    have hxeq : fderivRank f x = r := hx.2
                    exact (False.elim ((not_lt_of_ge (Nat.le_of_not_gt hr))
                      (hxeq ▸ hxlt)))
                  · intro hx
                    cases hx
                rw [hempty]
                simp
            have hU : volume (⋃ r : ℕ, f '' w r) = 0 := by
              rw [← nonpos_iff_eq_zero]
              calc
                volume (⋃ r : ℕ, f '' w r) ≤ ∑' r : ℕ, volume (f '' w r) :=
                  measure_iUnion_le _
                _ ≤ 0 := by simp only [hw, tsum_zero, nonpos_iff_eq_zero]
            apply measure_mono_null (t := ⋃ r : ℕ, f '' w r) ?_ hU
            intro z hz
            rcases hz with ⟨x, hx, rfl⟩
            exact Set.mem_iUnion.2 ⟨fderivRank f x,
              ⟨x, ⟨hx, rfl⟩, rfl⟩⟩
          · have hempty : v j = (∅ : Set (E m)) := by
              ext x
              constructor
              · intro hx
                exact False.elim (hjok ⟨hx.2.1, hx.2.2.1⟩)
              · intro hx
                cases hx
            rw [hempty]
            simp
        have hvunion : volume (⋃ j : ℕ, f '' v j) = 0 := by
          rw [← nonpos_iff_eq_zero]
          calc
            volume (⋃ j : ℕ, f '' v j) ≤ ∑' j : ℕ, volume (f '' v j) :=
              measure_iUnion_le _
            _ ≤ 0 := by simp only [hpieces, tsum_zero, nonpos_iff_eq_zero]
        have hrest : volume (f '' (K \ u)) = 0 := by
          apply measure_mono_null (t := ⋃ j : ℕ, f '' v j) ?_ hvunion
          intro z hz
          rcases hz with ⟨x, hx, rfl⟩
          rcases hx with ⟨hxK, hxu⟩
          have hnot : ¬ ∀ j : ℕ, 1 ≤ j → j < k →
              iteratedFDeriv ℝ j f x = 0 := by
            intro hh
            exact hxu ⟨hxK, hh⟩
          push_neg at hnot
          obtain ⟨j, hj, hj', hn⟩ := hnot
          have hxv : x ∈ v j := ⟨hxK, hj, hj', hn⟩
          exact Set.mem_iUnion.2 ⟨j, ⟨x, hxv, rfl⟩⟩
        apply measure_mono_null (t := f '' u ∪ f '' (K \ u)) ?_
          (MeasureTheory.measure_union_null hflat hrest)
        intro z hz
        rcases hz with ⟨x, hx, rfl⟩
        change x ∈ K at hx
        by_cases hxu : x ∈ u
        · exact Or.inl ⟨x, hxu, rfl⟩
        · exact Or.inr ⟨x, ⟨hx, hxu⟩, rfl⟩
      apply measure_mono_null (t := f '' {x : E m | fderivRank f x < q.succ}) ?_ htextbook
      intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      refine ⟨x, ?_, rfl⟩
      exact hx.2
/-ResultProofEnd-/
/-ResultEnd-/
-- END INLINED FILE: Main.lean

end Submission
