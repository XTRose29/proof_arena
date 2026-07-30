import Submission.CyclicCover

namespace Submission.CoverSymmetry

noncomputable section

open CyclicCover

structure PhaseReversing (S : Symmetry.NegativeSymmetry AlgebraicTrefoil.knot) where
  phase_map : ∀ q : Complement,
    phase (CompactifiedSymmetry.complementHomeomorph S q) = (phase q)⁻¹

def lift {S : Symmetry.NegativeSymmetry AlgebraicTrefoil.knot}
    (P : PhaseReversing S) : Cover ≃ Cover where
  toFun x := ⟨(CompactifiedSymmetry.complementHomeomorph S x.1.1, -x.1.2), by
    rw [P.phase_map, Circle.exp_neg]
    exact congrArg Inv.inv x.2⟩
  invFun x := ⟨((CompactifiedSymmetry.complementHomeomorph S).symm x.1.1, -x.1.2), by
    have h := P.phase_map ((CompactifiedSymmetry.complementHomeomorph S).symm x.1.1)
    rw [Homeomorph.apply_symm_apply] at h
    rw [Circle.exp_neg]
    have hinv : phase ((CompactifiedSymmetry.complementHomeomorph S).symm x.1.1) =
        (phase x.1.1)⁻¹ := by
      simpa using (congrArg Inv.inv h).symm
    exact hinv.trans (congrArg Inv.inv x.2)⟩
  left_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · exact (CompactifiedSymmetry.complementHomeomorph S).symm_apply_apply x.1.1
    · simp
  right_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · exact (CompactifiedSymmetry.complementHomeomorph S).apply_symm_apply x.1.1
    · simp

def liftHomeomorph {S : Symmetry.NegativeSymmetry AlgebraicTrefoil.knot}
    (P : PhaseReversing S) : Cover ≃ₜ Cover where
  toEquiv := lift P
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact ((CompactifiedSymmetry.complementHomeomorph S).continuous.comp
      (continuous_fst.comp continuous_subtype_val)).prodMk
        ((continuous_snd.comp continuous_subtype_val).neg)
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact ((CompactifiedSymmetry.complementHomeomorph S).symm.continuous.comp
      (continuous_fst.comp continuous_subtype_val)).prodMk
        ((continuous_snd.comp continuous_subtype_val).neg)

@[simp] theorem lift_fst {S : Symmetry.NegativeSymmetry AlgebraicTrefoil.knot}
    (P : PhaseReversing S) (x : Cover) :
    (lift P x).1.1 = CompactifiedSymmetry.complementHomeomorph S x.1.1 :=
  rfl

@[simp] theorem lift_height {S : Symmetry.NegativeSymmetry AlgebraicTrefoil.knot}
    (P : PhaseReversing S) (x : Cover) : (lift P x).1.2 = -x.1.2 :=
  rfl

theorem lift_deck {S : Symmetry.NegativeSymmetry AlgebraicTrefoil.knot}
    (P : PhaseReversing S) (x : Cover) :
    lift P (deck x) = deck.symm (lift P x) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · simp [lift, deck]
    ring

def onProduct {S : Symmetry.NegativeSymmetry AlgebraicTrefoil.knot}
    (P : PhaseReversing S) : Milnor.Fiber × ℝ ≃ Milnor.Fiber × ℝ :=
  fiberCoverEquiv.trans ((lift P).trans fiberCoverEquiv.symm)

def onProductHomeomorph {S : Symmetry.NegativeSymmetry AlgebraicTrefoil.knot}
    (P : PhaseReversing S) : Milnor.Fiber × ℝ ≃ₜ Milnor.Fiber × ℝ :=
  CyclicCover.fiberCoverHomeomorph.trans
    ((liftHomeomorph P).trans CyclicCover.fiberCoverHomeomorph.symm)

@[simp] theorem onProduct_height {S : Symmetry.NegativeSymmetry AlgebraicTrefoil.knot}
    (P : PhaseReversing S) (x : Milnor.Fiber × ℝ) :
    (onProduct P x).2 = -x.2 :=
  rfl

@[simp] theorem onProduct_symm_height
    {S : Symmetry.NegativeSymmetry AlgebraicTrefoil.knot}
    (P : PhaseReversing S) (x : Milnor.Fiber × ℝ) :
    ((onProduct P).symm x).2 = -x.2 := by
  have h := onProduct_height P ((onProduct P).symm x)
  rw [Equiv.apply_symm_apply] at h
  linarith

def fiberEquivAt {S : Symmetry.NegativeSymmetry AlgebraicTrefoil.knot}
    (P : PhaseReversing S) (s : ℝ) : Milnor.Fiber ≃ Milnor.Fiber where
  toFun x := (onProduct P (x, s)).1
  invFun x := ((onProduct P).symm (x, -s)).1
  left_inv x := by
    change ((onProduct P).symm ((onProduct P (x, s)).1, -s)).1 = x
    have hpair : ((onProduct P (x, s)).1, -s) = onProduct P (x, s) := by
      apply Prod.ext
      · rfl
      · exact (onProduct_height P (x, s)).symm
    rw [hpair, Equiv.symm_apply_apply]
  right_inv x := by
    change (onProduct P (((onProduct P).symm (x, -s)).1, s)).1 = x
    have hpair : (((onProduct P).symm (x, -s)).1, s) =
        (onProduct P).symm (x, -s) := by
      apply Prod.ext
      · rfl
      · rw [onProduct_symm_height]
        simp
    rw [hpair, Equiv.apply_symm_apply]

theorem fiberEquivAt_continuous
    {S : Symmetry.NegativeSymmetry AlgebraicTrefoil.knot}
    (P : PhaseReversing S) :
    Continuous (fun x : ℝ × Milnor.Fiber => fiberEquivAt P x.1 x.2) := by
  exact continuous_fst.comp ((onProductHomeomorph P).continuous.comp
    (continuous_snd.prodMk continuous_fst))

theorem fiberEquivAt_symm_continuous
    {S : Symmetry.NegativeSymmetry AlgebraicTrefoil.knot}
    (P : PhaseReversing S) :
    Continuous (fun x : ℝ × Milnor.Fiber => (fiberEquivAt P x.1).symm x.2) := by
  exact continuous_fst.comp ((onProductHomeomorph P).symm.continuous.comp
    (continuous_snd.prodMk continuous_fst.neg))

def fiberHomeomorphAt {S : Symmetry.NegativeSymmetry AlgebraicTrefoil.knot}
    (P : PhaseReversing S) (s : ℝ) : Milnor.Fiber ≃ₜ Milnor.Fiber where
  toFun x := (onProduct P (x, s)).1
  invFun x := ((onProduct P).symm (x, -s)).1
  left_inv := (fiberEquivAt P s).left_inv
  right_inv := (fiberEquivAt P s).right_inv
  continuous_toFun := by
    exact continuous_fst.comp ((onProductHomeomorph P).continuous.comp
      (continuous_id.prodMk continuous_const))
  continuous_invFun := by
    exact continuous_fst.comp ((onProductHomeomorph P).symm.continuous.comp
      (continuous_id.prodMk continuous_const.neg))

def fiberContinuousMapAt {S : Symmetry.NegativeSymmetry AlgebraicTrefoil.knot}
    (P : PhaseReversing S) (s : ℝ) : C(Milnor.Fiber, Milnor.Fiber) :=
  ⟨fun x => (onProduct P (x, s)).1,
    continuous_fst.comp ((onProductHomeomorph P).continuous.comp
      (continuous_id.prodMk continuous_const))⟩

def fiberHomotopyZeroTwoPi
    {S : Symmetry.NegativeSymmetry AlgebraicTrefoil.knot}
    (P : PhaseReversing S) :
    (fiberContinuousMapAt P 0).Homotopy (fiberContinuousMapAt P (2 * Real.pi)) :=
  ContinuousMap.Homotopy.mk
    ⟨fun x : unitInterval × Milnor.Fiber =>
        (onProduct P (x.2, 2 * Real.pi * (x.1 : ℝ))).1,
      by
        exact continuous_fst.comp ((onProductHomeomorph P).continuous.comp
          (continuous_snd.prodMk
            (continuous_const.mul (continuous_subtype_val.comp continuous_fst))))⟩
    (by intro x; simp [fiberContinuousMapAt])
    (by intro x; simp [fiberContinuousMapAt])

theorem fromFiber_monodromy_add_two_pi (x : Milnor.Fiber × ℝ) :
    fromFiber (Milnor.fiberMonodromy.symm x.1, x.2 + 2 * Real.pi) =
      deck (fromFiber x) := by
  apply fiberCoverEquiv.symm.injective
  change toFiber (fromFiber _) = toFiber (deck (fromFiber x))
  rw [toFiber_fromFiber, toFiber_deck, toFiber_fromFiber]

theorem onProduct_deck {S : Symmetry.NegativeSymmetry AlgebraicTrefoil.knot}
    (P : PhaseReversing S) (x : Milnor.Fiber × ℝ) :
    onProduct P (Milnor.fiberMonodromy.symm x.1, x.2 + 2 * Real.pi) =
      (Milnor.fiberMonodromy (onProduct P x).1, (onProduct P x).2 - 2 * Real.pi) := by
  change toFiber (lift P (fromFiber _)) = _
  rw [fromFiber_monodromy_add_two_pi, lift_deck, toFiber_deck_symm]
  rfl

theorem fiberEquivAt_add_two_pi
    {S : Symmetry.NegativeSymmetry AlgebraicTrefoil.knot}
    (P : PhaseReversing S) (s : ℝ) (x : Milnor.Fiber) :
    fiberEquivAt P (s + 2 * Real.pi) (Milnor.fiberMonodromy.symm x) =
      Milnor.fiberMonodromy (fiberEquivAt P s x) := by
  exact congrArg Prod.fst (onProduct_deck P (x, s))

end

end Submission.CoverSymmetry
