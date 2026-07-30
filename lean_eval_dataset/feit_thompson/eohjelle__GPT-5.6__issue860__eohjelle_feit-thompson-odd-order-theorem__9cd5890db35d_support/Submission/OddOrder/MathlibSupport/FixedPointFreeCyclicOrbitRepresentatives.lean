import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Submission.OddOrder.MathlibSupport.FixedOneMulActionOrbitCount

/-!
Canonical representatives for the nonidentity orbits of a fixed-point-free
cyclic action.
-/

namespace Submission.OddOrder.MathlibSupport

universe u v

variable {G : Type u} {X : Type v}
variable [Group G] [Group X] [MulAction G X]

/-- Use an identification with `ZMod |G|` to enumerate every nonidentity
orbit from the representative selected by `Quotient.out`. -/
noncomputable def fixedPointFreeCyclicOrbitRepresentative
    (e : Multiplicative (ZMod (Nat.card G)) ≃* G)
    (j : nonidentityFixedOneOrbitQuotient (G := G) (X := X))
    (t : ZMod (Nat.card G)) : X :=
  e (Multiplicative.ofAdd t) • j.1.out

theorem fixedPointFreeCyclicOrbitRepresentative_ne_one
    (e : Multiplicative (ZMod (Nat.card G)) ≃* G)
    (hone : ∀ g : G, g • (1 : X) = 1)
    (j : nonidentityFixedOneOrbitQuotient (G := G) (X := X))
    (t : ZMod (Nat.card G)) :
    fixedPointFreeCyclicOrbitRepresentative e j t ≠ 1 := by
  intro h
  have hout : j.1.out ≠ (1 : X) := by
    intro hout
    apply j.2
    rw [← Quotient.out_eq' j.1, hout]
  apply hout
  have := congrArg (fun x ↦ e (Multiplicative.ofAdd t)⁻¹ • x) h
  simpa [fixedPointFreeCyclicOrbitRepresentative, hone] using this

theorem fixedPointFreeCyclicOrbitRepresentative_mk
    (e : Multiplicative (ZMod (Nat.card G)) ≃* G)
    (j : nonidentityFixedOneOrbitQuotient (G := G) (X := X))
    (t : ZMod (Nat.card G)) :
    (Quotient.mk'' (fixedPointFreeCyclicOrbitRepresentative e j t) :
      MulAction.orbitRel.Quotient G X) = j.1 := by
  rw [← MulAction.orbitRel.Quotient.mem_orbit]
  rw [MulAction.orbitRel.Quotient.orbit_eq_orbit_out j.1 Quotient.out_eq']
  exact ⟨e (Multiplicative.ofAdd t), rfl⟩

/-- The cyclic parameters and the selected orbit labels enumerate distinct
nonidentity points. -/
theorem fixedPointFreeCyclicOrbitRepresentative_injective
    (e : Multiplicative (ZMod (Nat.card G)) ≃* G)
    (hfixed : ∀ g : G, g ≠ 1 -> ∀ x : X, g • x = x -> x = 1) :
    Function.Injective
      (fun jt : nonidentityFixedOneOrbitQuotient (G := G) (X := X) ×
          ZMod (Nat.card G) ↦
        fixedPointFreeCyclicOrbitRepresentative e jt.1 jt.2) := by
  rintro ⟨j, t⟩ ⟨j', t'⟩ heq
  have hj : j = j' := by
    apply Subtype.ext
    calc
      j.1 = Quotient.mk'' (fixedPointFreeCyclicOrbitRepresentative e j t) :=
        (fixedPointFreeCyclicOrbitRepresentative_mk e j t).symm
      _ = Quotient.mk'' (fixedPointFreeCyclicOrbitRepresentative e j' t') :=
        congrArg Quotient.mk'' heq
      _ = j'.1 := fixedPointFreeCyclicOrbitRepresentative_mk e j' t'
  subst j'
  have hx : j.1.out ≠ (1 : X) := by
    intro hout
    apply j.2
    rw [← Quotient.out_eq' j.1, hout]
  have hstab :
      ((e (Multiplicative.ofAdd t'))⁻¹ * e (Multiplicative.ofAdd t)) •
          j.1.out = j.1.out := by
    change e (Multiplicative.ofAdd t) • j.1.out =
      e (Multiplicative.ofAdd t') • j.1.out at heq
    rw [mul_smul, heq, inv_smul_smul]
  have hg :
      (e (Multiplicative.ofAdd t'))⁻¹ * e (Multiplicative.ofAdd t) = 1 := by
    by_contra hne
    exact hx (hfixed _ hne _ hstab)
  have het : e (Multiplicative.ofAdd t) =
      e (Multiplicative.ofAdd t') := by
    exact (inv_mul_eq_one.mp hg).symm
  have ht : t = t' := by
    have := e.injective het
    exact Multiplicative.ofAdd.injective this
  subst t'
  rfl

/-- Adjoining the identity to the cyclic orbit enumeration remains
injective. -/
theorem fixedPointFreeCyclicOrbitRepresentative_option_injective
    (e : Multiplicative (ZMod (Nat.card G)) ≃* G)
    (hone : ∀ g : G, g • (1 : X) = 1)
    (hfixed : ∀ g : G, g ≠ 1 -> ∀ x : X, g • x = x -> x = 1) :
    Function.Injective
      (fun o : Option
          (nonidentityFixedOneOrbitQuotient (G := G) (X := X) ×
            ZMod (Nat.card G)) ↦
        match o with
        | none => 1
        | some jt => fixedPointFreeCyclicOrbitRepresentative e jt.1 jt.2) := by
  intro x y hxy
  cases x with
  | none =>
      cases y with
      | none => rfl
      | some jt =>
          exact False.elim
            (fixedPointFreeCyclicOrbitRepresentative_ne_one e hone
              jt.1 jt.2 hxy.symm)
  | some jt =>
      cases y with
      | none =>
          exact False.elim
            (fixedPointFreeCyclicOrbitRepresentative_ne_one e hone
              jt.1 jt.2 hxy)
      | some jt' =>
          exact congrArg some
            (fixedPointFreeCyclicOrbitRepresentative_injective e hfixed hxy)

end Submission.OddOrder.MathlibSupport
