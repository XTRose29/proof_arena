import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Convex.Contractible
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Algebra.Group.Equiv.TypeTags

open Real Set Filter Topology

namespace Submission.Helpers

/-! ### Phase 1: the fiber `Circle.exp ⁻¹' {1} ≃ ℤ` -/

/-- `Circle.exp r = 1` iff `r = n · 2π` for some integer `n`. (mathlib already has this.) -/
lemma exp_eq_one_iff (r : ℝ) : Circle.exp r = 1 ↔ ∃ n : ℤ, r = n * (2 * Real.pi) :=
  Circle.exp_eq_one

/-- The unique integer `n` with `r = n · 2π`, when `Circle.exp r = 1`. -/
noncomputable def fiberToInt (x : (Circle.exp ⁻¹' {1} : Set ℝ)) : ℤ :=
  ((exp_eq_one_iff x.val).mp x.property).choose

lemma fiberToInt_spec (x : (Circle.exp ⁻¹' {1} : Set ℝ)) :
    x.val = (fiberToInt x : ℝ) * (2 * Real.pi) :=
  ((exp_eq_one_iff x.val).mp x.property).choose_spec

/-- Inverse: given `n : ℤ`, the point `n · 2π` lies in the fiber. -/
noncomputable def intToFiber (n : ℤ) : (Circle.exp ⁻¹' {1} : Set ℝ) :=
  ⟨n * (2 * Real.pi), by
    show Circle.exp (n * (2 * Real.pi)) = 1
    rw [exp_eq_one_iff]
    exact ⟨n, rfl⟩⟩

/-- `2 * π ≠ 0`. -/
lemma two_pi_ne_zero : (2 * Real.pi : ℝ) ≠ 0 :=
  mul_ne_zero two_ne_zero Real.pi_ne_zero

/-- The fiber of `Circle.exp` over `1` is in bijection with `ℤ`. -/
noncomputable def fiberEquivInt : (Circle.exp ⁻¹' {1} : Set ℝ) ≃ ℤ where
  toFun := fiberToInt
  invFun := intToFiber
  left_inv x := by
    apply Subtype.ext
    show ((intToFiber (fiberToInt x)).val) = x.val
    show ((fiberToInt x : ℤ) : ℝ) * (2 * Real.pi) = x.val
    exact (fiberToInt_spec x).symm
  right_inv n := by
    show fiberToInt (intToFiber n) = n
    have h : (intToFiber n).val = (fiberToInt (intToFiber n) : ℝ) * (2 * Real.pi) :=
      fiberToInt_spec _
    have hval : (intToFiber n).val = (n : ℝ) * (2 * Real.pi) := rfl
    rw [hval] at h
    have : (n : ℝ) = ((fiberToInt (intToFiber n) : ℤ) : ℝ) := by
      have hπ : (2 * Real.pi : ℝ) ≠ 0 := two_pi_ne_zero
      field_simp at h
      linarith [h]
    exact_mod_cast this.symm

@[simp] lemma fiberEquivInt_apply (x) : fiberEquivInt x = fiberToInt x := rfl

@[simp] lemma fiberEquivInt_symm_apply (n : ℤ) :
    (fiberEquivInt.symm n : (Circle.exp ⁻¹' {1} : Set ℝ)) = intToFiber n := rfl

/-! ### Phase 2: monodromy as a winding number -/

/-- The basepoint `0 : ℝ` lies in the fiber over `1 : Circle`. -/
noncomputable def basepointFiber : (Circle.exp ⁻¹' {1} : Set ℝ) :=
  ⟨0, by show Circle.exp 0 = 1; exact Circle.exp_zero⟩

/-- Monodromy of `Circle.isCoveringMap_exp` at the basepoint, applied to a homotopy class. -/
noncomputable def monodromyAtBase (γ : Path.Homotopic.Quotient (1:Circle) 1) :
    (Circle.exp ⁻¹' {1} : Set ℝ) :=
  Circle.isCoveringMap_exp.monodromy γ basepointFiber

/-- Winding number of a homotopy class. -/
noncomputable def winding (γ : Path.Homotopic.Quotient (1:Circle) 1) : ℤ :=
  fiberEquivInt (monodromyAtBase γ)

/-! ### Phase 3: the inverse loop -/

/-- The integer-`n` loop on the circle: `t ↦ Circle.exp (2π·n·t)`. -/
noncomputable def circleLoop (n : ℤ) : Path (1 : Circle) (1 : Circle) where
  toFun := fun t => Circle.exp ((n : ℝ) * (2 * Real.pi) * t.1)
  source' := by
    show Circle.exp ((n : ℝ) * (2 * Real.pi) * (0 : unitInterval).1) = 1
    show Circle.exp ((n : ℝ) * (2 * Real.pi) * 0) = 1
    rw [mul_zero, Circle.exp_zero]
  target' := by
    show Circle.exp ((n : ℝ) * (2 * Real.pi) * (1 : unitInterval).1) = 1
    show Circle.exp ((n : ℝ) * (2 * Real.pi) * 1) = 1
    rw [mul_one, exp_eq_one_iff]
    exact ⟨n, rfl⟩
  continuous_toFun := by
    refine Continuous.comp Circle.exp.continuous ?_
    fun_prop

/-- The integer-`n` loop as an element of the homotopy quotient. -/
noncomputable def circleLoopQuotient (n : ℤ) : Path.Homotopic.Quotient (1:Circle) 1 :=
  ⟦circleLoop n⟧

/-! ### Phase 4a: `winding (circleLoopQuotient n) = n` -/

/-- The canonical lift in ℝ of `circleLoop n`, as `t ↦ n · 2π · t`. -/
noncomputable def circleLoopLift (n : ℤ) : C(unitInterval, ℝ) :=
  ⟨fun t => (n : ℝ) * (2 * Real.pi) * t.1, by fun_prop⟩

@[simp] lemma circleLoopLift_zero (n : ℤ) : circleLoopLift n 0 = 0 := by
  show (n : ℝ) * (2 * Real.pi) * (0 : unitInterval).1 = 0
  simp

@[simp] lemma circleLoopLift_one (n : ℤ) :
    circleLoopLift n 1 = (n : ℝ) * (2 * Real.pi) := by
  show (n : ℝ) * (2 * Real.pi) * (1 : unitInterval).1 = (n : ℝ) * (2 * Real.pi)
  simp

lemma exp_circleLoopLift (n : ℤ) :
    Circle.exp ∘ circleLoopLift n = circleLoop n := by
  rfl

/-- The lifted path of `circleLoop n` from `0 ∈ ℝ` is `circleLoopLift n`. -/
lemma liftPath_circleLoop (n : ℤ)
    (h0 : (circleLoop n) 0 = Circle.exp basepointFiber.val) :
    Circle.isCoveringMap_exp.liftPath (circleLoop n) basepointFiber.val h0
      = circleLoopLift n := by
  symm
  refine (Circle.isCoveringMap_exp.eq_liftPath_iff' h0).mpr ⟨?_, ?_⟩
  · funext t
    show Circle.exp (circleLoopLift n t) = circleLoop n t
    rfl
  · simp [basepointFiber]

lemma monodromy_circleLoop (n : ℤ) :
    (Circle.isCoveringMap_exp.monodromy ⟦circleLoop n⟧ basepointFiber).val =
    (n : ℝ) * (2 * Real.pi) := by
  -- monodromy on ⟦γ⟧ reduces to liftPath γ ... 1 (def). Then use liftPath_circleLoop.
  have h0 : (circleLoop n) 0 = Circle.exp basepointFiber.val := by
    simp [circleLoop, basepointFiber]
  have heq : (Circle.isCoveringMap_exp.monodromy ⟦circleLoop n⟧ basepointFiber).val =
       Circle.isCoveringMap_exp.liftPath (circleLoop n) basepointFiber.val h0 1 := rfl
  rw [heq, liftPath_circleLoop n h0]
  exact circleLoopLift_one n

lemma winding_circleLoopQuotient (n : ℤ) :
    winding (circleLoopQuotient n) = n := by
  show fiberEquivInt (Circle.isCoveringMap_exp.monodromy ⟦circleLoop n⟧ basepointFiber) = n
  -- Use that monodromy ⟦circleLoop n⟧ basepoint = intToFiber n (by val).
  have h_eq :
      Circle.isCoveringMap_exp.monodromy ⟦circleLoop n⟧ basepointFiber = intToFiber n := by
    apply Subtype.ext
    show (Circle.isCoveringMap_exp.monodromy ⟦circleLoop n⟧ basepointFiber).val = (intToFiber n).val
    rw [monodromy_circleLoop n]
    rfl
  rw [h_eq]
  exact fiberEquivInt.right_inv n

/-! ### Phase 4b: `winding` is injective -/

/-- ℝ is simply connected (contractible ⟹ simply connected). -/
instance instSimplyConnectedReal : SimplyConnectedSpace ℝ :=
  SimplyConnectedSpace.ofContractible ℝ

/-- Helper: a `Path 1 1` in Circle whose underlying function equals the projection of a path
in ℝ via `Circle.exp`. -/
private noncomputable def projectPath {a b : ℝ} (Γ : Path a b)
    (ha : Circle.exp a = (1:Circle)) (hb : Circle.exp b = (1:Circle)) :
    Path (1:Circle) 1 :=
  Path.cast (Γ.map Circle.exp.continuous) ha.symm hb.symm

private lemma projectPath_apply {a b : ℝ} (Γ : Path a b)
    (ha : Circle.exp a = (1:Circle)) (hb : Circle.exp b = (1:Circle)) (t : unitInterval) :
    projectPath Γ ha hb t = Circle.exp (Γ t) := rfl

/-- For ℝ → S¹, the lift of a representative path determines its homotopy class.
Proof: build a `Path.Homotopy p p'` directly by composing `Circle.exp` with
a homotopy of the lifts in ℝ (which exists since ℝ is simply connected). -/
private lemma path_homotopic_quotient_eq_of_lift_eq
    (p p' : Path (1:Circle) 1)
    (h0 : p 0 = Circle.exp basepointFiber.val)
    (h0' : p' 0 = Circle.exp basepointFiber.val)
    (h_endpoint :
      (Circle.isCoveringMap_exp.liftPath p basepointFiber.val h0) 1 =
      (Circle.isCoveringMap_exp.liftPath p' basepointFiber.val h0') 1) :
    (⟦p⟧ : Path.Homotopic.Quotient (1:Circle) 1) = ⟦p'⟧ := by
  set Γ := Circle.isCoveringMap_exp.liftPath p basepointFiber.val h0
  set Γ' := Circle.isCoveringMap_exp.liftPath p' basepointFiber.val h0'
  have hΓ0 : Γ 0 = (0 : ℝ) := by
    show Γ 0 = basepointFiber.val
    exact Circle.isCoveringMap_exp.liftPath_zero ..
  have hΓ'0 : Γ' 0 = (0 : ℝ) := by
    show Γ' 0 = basepointFiber.val
    exact Circle.isCoveringMap_exp.liftPath_zero ..
  have hexp_Γ : ⇑Circle.exp ∘ ⇑Γ = ⇑p := Circle.isCoveringMap_exp.liftPath_lifts ..
  have hexp_Γ' : ⇑Circle.exp ∘ ⇑Γ' = ⇑p' := Circle.isCoveringMap_exp.liftPath_lifts ..
  -- View Γ and Γ' as Paths in ℝ from 0 to Γ 1.
  let Γ_path : Path (0:ℝ) (Γ 1) :=
    { toFun := Γ, continuous_toFun := Γ.continuous, source' := hΓ0, target' := rfl }
  let Γ'_path : Path (0:ℝ) (Γ 1) :=
    { toFun := Γ', continuous_toFun := Γ'.continuous, source' := hΓ'0,
      target' := h_endpoint.symm }
  haveI : SimplyConnectedSpace ℝ := instSimplyConnectedReal
  -- Get a homotopy in ℝ between Γ_path and Γ'_path.
  obtain ⟨H⟩ : Nonempty (Path.Homotopy Γ_path Γ'_path) :=
    SimplyConnectedSpace.paths_homotopic Γ_path Γ'_path
  -- Endpoint identifications in Circle.
  have hΓend : Circle.exp (Γ 1) = (1 : Circle) := by
    have hm : (⇑Circle.exp ∘ ⇑Γ) 1 = p 1 := congr_fun hexp_Γ 1
    simp only [Function.comp_apply] at hm
    rw [hm]; exact p.target
  -- Build a Path.Homotopy p p' by composing exp with H.
  apply Quotient.sound
  refine ⟨?_⟩
  refine
    { toFun := fun ts => Circle.exp (H ts)
      continuous_toFun := Circle.exp.continuous.comp H.continuous
      map_zero_left := ?_
      map_one_left := ?_
      prop' := ?_ }
  · -- (0, s) ↦ Circle.exp (Γ_path s) = p s
    intro s
    show Circle.exp (H (0, s)) = p s
    rw [show H (0, s) = Γ_path s from H.map_zero_left s]
    exact congr_fun hexp_Γ s
  · -- (1, s) ↦ Circle.exp (Γ'_path s) = p' s
    intro s
    show Circle.exp (H (1, s)) = p' s
    rw [show H (1, s) = Γ'_path s from H.map_one_left s]
    exact congr_fun hexp_Γ' s
  · -- prop': for x ∈ {0,1}, the curried map equals p.
    intro t x hx
    rcases hx with hx0 | hx1
    · -- x = 0
      subst hx0
      show Circle.exp (H (t, 0)) = p 0
      rw [show H (t, 0) = (0:ℝ) from H.source t, Circle.exp_zero, p.source]
    · -- x = 1
      simp at hx1
      subst hx1
      show Circle.exp (H (t, 1)) = p 1
      rw [show H (t, 1) = Γ 1 from H.target t, hΓend, p.target]

/-- `winding` is injective on `Path.Homotopic.Quotient (1:Circle) 1`. -/
lemma winding_injective :
    Function.Injective (winding : Path.Homotopic.Quotient (1:Circle) 1 → ℤ) := by
  intro γ γ' h_eq
  -- monodromyAtBase γ = monodromyAtBase γ' (via fiberEquivInt injectivity)
  have h_mono : monodromyAtBase γ = monodromyAtBase γ' := fiberEquivInt.injective h_eq
  -- Apply the technical lemma via Quotient.ind on both γ and γ'.
  refine Quotient.inductionOn₂ γ γ' ?_ h_mono
  intros p p' h_mono_p
  -- Compute lift endpoints from monodromy.
  have h0 : p 0 = Circle.exp basepointFiber.val := by
    show p 0 = Circle.exp 0
    rw [p.source, Circle.exp_zero]
  have h0' : p' 0 = Circle.exp basepointFiber.val := by
    show p' 0 = Circle.exp 0
    rw [p'.source, Circle.exp_zero]
  have h_endpoint := Subtype.mk.inj h_mono_p
  exact path_homotopic_quotient_eq_of_lift_eq p p' h0 h0' h_endpoint

/-! ### Phase 5: `winding` is a group homomorphism -/

/-- Translation property of `Circle.exp`-lifts: shifting the starting point by `n · 2π`
shifts the entire lift by `n · 2π`. -/
private lemma liftPath_translate (β : Path (1:Circle) 1) (n : ℤ)
    (h0 : β 0 = Circle.exp 0) (h0' : β 0 = Circle.exp ((n:ℝ) * (2 * Real.pi))) (t : unitInterval) :
    (Circle.isCoveringMap_exp.liftPath β ((n:ℝ) * (2 * Real.pi)) h0') t =
    (Circle.isCoveringMap_exp.liftPath β 0 h0) t + (n:ℝ) * (2 * Real.pi) := by
  set L₀ := Circle.isCoveringMap_exp.liftPath β 0 h0
  let Γ' : C(unitInterval, ℝ) :=
    ⟨fun t => L₀ t + (n:ℝ) * (2 * Real.pi), by fun_prop⟩
  have hexp : ⇑Circle.exp ∘ ⇑Γ' = ⇑β := by
    funext s
    show Circle.exp (L₀ s + (n:ℝ) * (2 * Real.pi)) = β s
    rw [Circle.exp_add]
    have h1 : Circle.exp ((n:ℝ) * (2 * Real.pi)) = 1 := by
      rw [exp_eq_one_iff]; exact ⟨n, rfl⟩
    rw [h1, mul_one]
    exact congr_fun (Circle.isCoveringMap_exp.liftPath_lifts β 0 h0) s
  have hΓ'_zero : Γ' 0 = (n:ℝ) * (2 * Real.pi) := by
    show L₀ 0 + (n:ℝ) * (2 * Real.pi) = (n:ℝ) * (2 * Real.pi)
    rw [Circle.isCoveringMap_exp.liftPath_zero β 0 h0, zero_add]
  have heq : Γ' = Circle.isCoveringMap_exp.liftPath β ((n:ℝ) * (2 * Real.pi)) h0' :=
    (Circle.isCoveringMap_exp.eq_liftPath_iff' h0').mpr ⟨hexp, hΓ'_zero⟩
  show (Circle.isCoveringMap_exp.liftPath β ((n:ℝ) * (2 * Real.pi)) h0') t =
       L₀ t + (n:ℝ) * (2 * Real.pi)
  rw [← heq]
  rfl

/-- Monodromy on the fiber: applying monodromy to `intToFiber n` adds `winding β` to `n`. -/
private lemma monodromy_intToFiber (β : Path.Homotopic.Quotient (1:Circle) 1) (n : ℤ) :
    Circle.isCoveringMap_exp.monodromy β (intToFiber n) =
    intToFiber (winding β + n) := by
  refine Quotient.inductionOn β ?_
  intro β
  apply Subtype.ext
  -- LHS evaluates to `liftPath β (n·2π) ... 1` via def of monodromy.
  have h0 : β 0 = Circle.exp 0 := by rw [β.source, Circle.exp_zero]
  have h0' : β 0 = Circle.exp ((n:ℝ) * (2 * Real.pi)) := by
    rw [β.source]
    have : Circle.exp ((n:ℝ) * (2 * Real.pi)) = 1 := by
      rw [exp_eq_one_iff]; exact ⟨n, rfl⟩
    rw [this]
  -- monodromy ⟦β⟧ (intToFiber n) = liftPath β ((n:ℝ) * 2π) ... 1.
  show (Circle.isCoveringMap_exp.liftPath β (intToFiber n).val
        ((Path.source β).trans (intToFiber n).property.symm)) 1 = (intToFiber (winding ⟦β⟧ + n)).val
  -- Use translation lemma.
  have h_trans :
      (Circle.isCoveringMap_exp.liftPath β ((n:ℝ) * (2 * Real.pi)) h0') 1 =
      (Circle.isCoveringMap_exp.liftPath β 0 h0) 1 + (n:ℝ) * (2 * Real.pi) :=
    liftPath_translate β n h0 h0' 1
  -- Rewrite (intToFiber n).val = (n:ℝ) * (2 * Real.pi).
  have hint_val : (intToFiber n).val = (n:ℝ) * (2 * Real.pi) := rfl
  -- Now liftPath β (n·2π) ... 1 with the right proof equals the version with h0' (since proofs
  -- of equality are unique).
  have h_lift_eq :
      Circle.isCoveringMap_exp.liftPath β (intToFiber n).val
        ((Path.source β).trans (intToFiber n).property.symm) =
      Circle.isCoveringMap_exp.liftPath β ((n:ℝ) * (2 * Real.pi)) h0' := rfl
  rw [h_lift_eq, h_trans]
  -- Now: liftPath β 0 h0 1 = (winding ⟦β⟧) * 2π via def of winding.
  have h_w : (Circle.isCoveringMap_exp.liftPath β 0 h0) 1 = (winding ⟦β⟧ : ℝ) * (2 * Real.pi) := by
    -- winding ⟦β⟧ = fiberToInt (monodromy ⟦β⟧ basepointFiber); and
    -- (monodromy ⟦β⟧ basepointFiber).val = liftPath β 0 ... 1.
    have h_bp : (basepointFiber : (Circle.exp ⁻¹' {1} : Set ℝ)).val = (0 : ℝ) := rfl
    have h_mono :
        (Circle.isCoveringMap_exp.monodromy ⟦β⟧ basepointFiber).val =
        Circle.isCoveringMap_exp.liftPath β 0 h0 1 := rfl
    have h_spec := fiberToInt_spec
        (Circle.isCoveringMap_exp.monodromy ⟦β⟧ basepointFiber)
    rw [h_mono] at h_spec
    have hwind : winding ⟦β⟧ =
        fiberToInt (Circle.isCoveringMap_exp.monodromy ⟦β⟧ basepointFiber) := rfl
    rw [hwind]
    exact h_spec
  rw [h_w]
  show (winding ⟦β⟧ : ℝ) * (2 * Real.pi) + (n:ℝ) * (2 * Real.pi) =
       ((winding ⟦β⟧ + n : ℤ) : ℝ) * (2 * Real.pi)
  push_cast
  ring

/-- The key group-homomorphism property: `winding` of a concatenation is the sum of windings. -/
lemma winding_trans (α β : Path.Homotopic.Quotient (1:Circle) 1) :
    winding (α.trans β) = winding α + winding β := by
  have h_mono :
      Circle.isCoveringMap_exp.monodromy (α.trans β) basepointFiber =
      Circle.isCoveringMap_exp.monodromy β
        (Circle.isCoveringMap_exp.monodromy α basepointFiber) :=
    Circle.isCoveringMap_exp.monodromy_trans_apply α β basepointFiber
  have h_α_eq :
      Circle.isCoveringMap_exp.monodromy α basepointFiber = intToFiber (winding α) := by
    apply Subtype.ext
    show (Circle.isCoveringMap_exp.monodromy α basepointFiber).val = (intToFiber (winding α)).val
    have h_spec := fiberToInt_spec (Circle.isCoveringMap_exp.monodromy α basepointFiber)
    have hwind : winding α =
        fiberToInt (Circle.isCoveringMap_exp.monodromy α basepointFiber) := rfl
    show (Circle.isCoveringMap_exp.monodromy α basepointFiber).val =
         ((winding α : ℤ) : ℝ) * (2 * Real.pi)
    rw [hwind]; exact h_spec
  rw [h_α_eq] at h_mono
  show fiberEquivInt (monodromyAtBase (α.trans β)) = winding α + winding β
  show fiberEquivInt (Circle.isCoveringMap_exp.monodromy (α.trans β) basepointFiber)
       = winding α + winding β
  rw [h_mono, monodromy_intToFiber β (winding α)]
  show fiberEquivInt (intToFiber (winding β + winding α)) = winding α + winding β
  rw [show fiberEquivInt (intToFiber (winding β + winding α)) = winding β + winding α from
      fiberEquivInt.right_inv (winding β + winding α)]
  ring

/-! ### Phase 6: assemble the MulEquiv -/

/-- Surjective inverse: every integer is the winding number of `circleLoopQuotient`. -/
lemma winding_surjective : Function.Surjective
    (winding : Path.Homotopic.Quotient (1:Circle) 1 → ℤ) :=
  fun n => ⟨circleLoopQuotient n, winding_circleLoopQuotient n⟩

/-- The fundamental group of the circle is `Multiplicative ℤ`. -/
noncomputable def fundEquivInt :
    FundamentalGroup Circle 1 ≃* Multiplicative ℤ where
  toFun γ := Multiplicative.ofAdd (winding γ.toPath)
  invFun n := FundamentalGroup.fromPath (circleLoopQuotient n.toAdd)
  left_inv γ := by
    show FundamentalGroup.fromPath (circleLoopQuotient (winding γ.toPath)) = γ
    apply winding_injective
    show winding (circleLoopQuotient (winding γ.toPath)) = winding γ.toPath
    exact winding_circleLoopQuotient _
  right_inv n := by
    show Multiplicative.ofAdd (winding (circleLoopQuotient n.toAdd)) = n
    rw [winding_circleLoopQuotient]
    rfl
  map_mul' γ γ' := by
    show Multiplicative.ofAdd (winding (γ * γ').toPath) =
         Multiplicative.ofAdd (winding γ.toPath) * Multiplicative.ofAdd (winding γ'.toPath)
    -- (γ * γ').toPath = γ'.toPath ≫ γ.toPath = γ'.toPath.trans γ.toPath
    have h_mul : ((γ * γ').toPath : Path.Homotopic.Quotient (1:Circle) 1) =
                 γ'.toPath.trans γ.toPath := rfl
    rw [h_mul, winding_trans]
    show Multiplicative.ofAdd (winding γ'.toPath + winding γ.toPath) =
         Multiplicative.ofAdd (winding γ.toPath) * Multiplicative.ofAdd (winding γ'.toPath)
    rw [add_comm, ofAdd_add]

/-- π₁(S¹) ≅ ℤ as multiplicative groups. -/
noncomputable def pi1CircleMulEquivIntAux :
    HomotopyGroup.Pi 1 Circle (1:Circle) ≃* Multiplicative ℤ :=
  HomotopyGroup.pi1MulEquivFundamentalGroup.trans fundEquivInt

end Submission.Helpers
