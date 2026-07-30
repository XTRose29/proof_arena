import Mathlib.RepresentationTheory.Maschke
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Finiteness
import Submission.OddOrder.BG.Section03.SemidirectProperKernel
import Submission.OddOrder.BG.Section03.SemiregularConjugation
import Submission.OddOrder.MathlibSupport.FaithfulQuotientRepresentation
import Submission.OddOrder.MathlibSupport.ElementaryAbelian
import Submission.OddOrder.MathlibSupport.ElementaryAbelianRepresentation
import Submission.OddOrder.MathlibSupport.MaschkeNormalConstituent
import Submission.OddOrder.MathlibSupport.NormalRestrictionCyclicIrreducible
import Submission.OddOrder.MathlibSupport.OneDimensionalEndomorphism
import Submission.OddOrder.MathlibSupport.PPrimeCore
import Submission.OddOrder.MathlibSupport.PrimeOrderCentralizer
import Submission.OddOrder.MathlibSupport.PrimeIndex
import Submission.OddOrder.MathlibSupport.RepresentationBaseChange
import Submission.OddOrder.MathlibSupport.RepresentationDeterminant
import Submission.OddOrder.MathlibSupport.RepresentationIsotypic
import Submission.OddOrder.MathlibSupport.RepresentationIrreducibleComp
import Submission.OddOrder.MathlibSupport.RepresentationSubgroupRestriction
import Submission.OddOrder.MathlibSupport.SubgroupCardinality
import Submission.OddOrder.MathlibSupport.SubrepresentationInvariants

/-!
# A prime Frobenius complement with a one-dimensional fixed space

This file ports Bender--Glauberman Theorem 3.5 (`Frobenius_prime_rfix1`)
and its internal elementary-abelian-action corollary
(`Frobenius_prime_cent_prime`).  The Clifford-theory part is phrased in
terms of intrinsic isotypic components, so it works in every nonmodular
characteristic.
-/

namespace Submission.OddOrder.BG.Section03

open Submission.OddOrder.MathlibSupport
open scoped MonoidAlgebra TensorProduct commutatorElement IsMulCommutative

noncomputable section

universe u v w x

section IsotypicComponents

variable {k : Type v} [Field k]
variable {G : Type u} [Group G]
variable {V : Type w} [AddCommGroup V] [Module k V]

/-- The intrinsic isotypic component belonging to a simple
subrepresentation.  The definition makes the bridge to mathlib's module
isotypic decomposition transparent. -/
private noncomputable def repIsotypicComponent
    {N : Type*} [Group N] (tau : Representation k N V)
    (U : Subrepresentation tau) : Subrepresentation tau :=
  (Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := tau)).symm
    (isotypicComponent k[N] tau.asModule U.asSubmodule)

@[simp]
private theorem repIsotypicComponent_asSubmodule
    {N : Type*} [Group N] (tau : Representation k N V)
    (U : Subrepresentation tau) :
    (repIsotypicComponent tau U).asSubmodule =
      isotypicComponent k[N] tau.asModule U.asSubmodule :=
  (Subrepresentation.subrepresentationSubmoduleOrderIso
    (ρ := tau)).apply_symm_apply _

private theorem le_repIsotypicComponent
    {N : Type*} [Group N] (tau : Representation k N V)
    (U : Subrepresentation tau) : U ≤ repIsotypicComponent tau U := by
  change U.asSubmodule ≤ (repIsotypicComponent tau U).asSubmodule
  rw [repIsotypicComponent_asSubmodule]
  exact U.asSubmodule.le_isotypicComponent

/-- Equivalent simple constituents determine the same intrinsic component,
and equality of their components detects equivalence. -/
private theorem repIsotypicComponent_eq_iff
    {N : Type*} [Group N] (tau : Representation k N V)
    (U W : Subrepresentation tau)
    [Representation.IsIrreducible U.toRepresentation]
    [Representation.IsIrreducible W.toRepresentation] :
    repIsotypicComponent tau U = repIsotypicComponent tau W ↔
      Nonempty (Representation.Equiv U.toRepresentation W.toRepresentation) := by
  letI : IsSimpleModule k[N] U.asSubmodule :=
    (irreducible_toRepresentation_iff_isSimpleModule_asSubmodule tau U).mp
      inferInstance
  letI : IsSimpleModule k[N] W.asSubmodule :=
    (irreducible_toRepresentation_iff_isSimpleModule_asSubmodule tau W).mp
      inferInstance
  constructor
  · intro h
    have hle : U.asSubmodule ≤
        isotypicComponent k[N] tau.asModule W.asSubmodule := by
      rw [← repIsotypicComponent_asSubmodule tau W, ← h]
      exact le_repIsotypicComponent tau U
    obtain ⟨e⟩ :=
      (isIsotypicOfType_submodule_iff.mp
        (IsIsotypicOfType.isotypicComponent
          k[N] tau.asModule W.asSubmodule)) U.asSubmodule hle
    exact (nonempty_subrepresentationEquiv_iff_nonempty_submoduleEquiv
      tau U W).mpr ⟨e⟩
  · rintro ⟨e⟩
    obtain ⟨e'⟩ :=
      (nonempty_subrepresentationEquiv_iff_nonempty_submoduleEquiv
        tau U W).mp ⟨e⟩
    apply SetLike.ext
    intro x
    change x ∈ isotypicComponent k[N] tau.asModule U.asSubmodule ↔
      x ∈ isotypicComponent k[N] tau.asModule W.asSubmodule
    rw [e'.isotypicComponent_eq]

/-- Translating equivalent normal constituents preserves equivalence. -/
private noncomputable def conjugateNormalSubrepresentationEquiv
    (rho : Representation k G V) (N : Subgroup G) [N.Normal]
    (g : G) (U W : Subrepresentation (rho.comp N.subtype))
    (e : Representation.Equiv U.toRepresentation W.toRepresentation) :
    Representation.Equiv
      (conjugateNormalSubrepresentation rho N g U).toRepresentation
      (conjugateNormalSubrepresentation rho N g W).toRepresentation := by
  let etwist : Representation.Equiv
      (U.toRepresentation.comp (MulAut.conjNormal g).symm.toMonoidHom)
      (W.toRepresentation.comp (MulAut.conjNormal g).symm.toMonoidHom) :=
    Representation.Equiv.mk e.toLinearEquiv (fun n =>
      e.toIntertwiningMap.isIntertwining'
        ((MulAut.conjNormal g).symm n))
  exact (normalConstituentTwistEquiv rho N g U).symm |>.trans
    etwist |>.trans (normalConstituentTwistEquiv rho N g W)

/-- Translation transported to the complete lattice of group-algebra
submodules. -/
private noncomputable def conjugateNormalSubmoduleOrderIso
    (rho : Representation k G V) (N : Subgroup G) [N.Normal]
    (g : G) :
    Submodule k[N] (Representation.asModule
        (rho.comp N.subtype : Representation k N V)) ≃o
      Submodule k[N] (Representation.asModule
        (rho.comp N.subtype : Representation k N V)) :=
  ((Subrepresentation.subrepresentationSubmoduleOrderIso
      (ρ := (rho.comp N.subtype : Representation k N V))).symm.trans
    (conjugateNormalSubrepresentationOrderIso rho N g)).trans
      (Subrepresentation.subrepresentationSubmoduleOrderIso
        (ρ := (rho.comp N.subtype : Representation k N V)))

/-- Ambient translation carries an isotypic component to the isotypic
component of the translated constituent. -/
private theorem conjugate_repIsotypicComponent
    (rho : Representation k G V) (N : Subgroup G) [N.Normal]
    (g : G) (U : Subrepresentation (rho.comp N.subtype))
    [Representation.IsIrreducible U.toRepresentation] :
    conjugateNormalSubrepresentation rho N g
        (repIsotypicComponent (rho.comp N.subtype) U) =
      repIsotypicComponent (rho.comp N.subtype)
        (conjugateNormalSubrepresentation rho N g U) := by
  let tau : Representation k N V := rho.comp N.subtype
  let q := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := tau)
  let E := conjugateNormalSubmoduleOrderIso rho N g
  have hE (M : Submodule k[N] tau.asModule) :
      Nonempty (M ≃ₗ[k[N]] U.asSubmodule) ↔
        Nonempty (E M ≃ₗ[k[N]]
          (conjugateNormalSubrepresentation rho N g U).asSubmodule) := by
    let Y : Subrepresentation tau := q.symm M
    have hYM : Y.asSubmodule = M := q.apply_symm_apply M
    have hEY : E M =
        (conjugateNormalSubrepresentation rho N g Y).asSubmodule := by
      rfl
    have hcancel (X : Subrepresentation tau) :
        conjugateNormalSubrepresentation rho N g⁻¹
            (conjugateNormalSubrepresentation rho N g X) = X := by
      rw [← conjugateNormalSubrepresentation_mul]
      simp
    constructor
    · intro hM
      have hYU : Nonempty (Representation.Equiv
          Y.toRepresentation U.toRepresentation) :=
        (nonempty_subrepresentationEquiv_iff_nonempty_submoduleEquiv
          tau Y U).mpr (by
            rw [hYM]
            exact hM)
      obtain ⟨eYU⟩ := hYU
      have hconj :=
        (nonempty_subrepresentationEquiv_iff_nonempty_submoduleEquiv tau
          (conjugateNormalSubrepresentation rho N g Y)
          (conjugateNormalSubrepresentation rho N g U)).mp
            ⟨conjugateNormalSubrepresentationEquiv rho N g Y U eYU⟩
      rw [hEY]
      exact hconj
    · intro hM
      have hconj : Nonempty
          ((conjugateNormalSubrepresentation rho N g Y).asSubmodule
            ≃ₗ[k[N]]
          (conjugateNormalSubrepresentation rho N g U).asSubmodule) := by
        rw [← hEY]
        exact hM
      have hconjRep : Nonempty (Representation.Equiv
          (conjugateNormalSubrepresentation rho N g Y).toRepresentation
          (conjugateNormalSubrepresentation rho N g U).toRepresentation) :=
        (nonempty_subrepresentationEquiv_iff_nonempty_submoduleEquiv tau
          (conjugateNormalSubrepresentation rho N g Y)
          (conjugateNormalSubrepresentation rho N g U)).mpr hconj
      obtain ⟨econj⟩ := hconjRep
      have hback :=
        (nonempty_subrepresentationEquiv_iff_nonempty_submoduleEquiv tau
          (conjugateNormalSubrepresentation rho N g⁻¹
            (conjugateNormalSubrepresentation rho N g Y))
          (conjugateNormalSubrepresentation rho N g⁻¹
            (conjugateNormalSubrepresentation rho N g U))).mp
              ⟨conjugateNormalSubrepresentationEquiv rho N g⁻¹
                (conjugateNormalSubrepresentation rho N g Y)
                (conjugateNormalSubrepresentation rho N g U) econj⟩
      rw [hcancel Y, hcancel U] at hback
      rw [← hYM]
      exact hback
  have hmodule :
      E
          (isotypicComponent k[N] tau.asModule U.asSubmodule) =
        isotypicComponent k[N] tau.asModule
          (conjugateNormalSubrepresentation rho N g U).asSubmodule := by
    rw [isotypicComponent, E.map_sSup]
    apply le_antisymm
    · exact iSup_le fun M ↦ iSup_le fun hM ↦
        le_sSup ((hE M).mp hM)
    · apply sSup_le
      intro P hP
      rw [← E.apply_symm_apply P]
      have hP' : Nonempty
          (E (E.symm P) ≃ₗ[k[N]]
            (conjugateNormalSubrepresentation rho N g U).asSubmodule) := by
        rw [E.apply_symm_apply]
        change Nonempty
          (P ≃ₗ[k[N]]
            (conjugateNormalSubrepresentation rho N g U).asSubmodule) at hP
        exact hP
      exact le_iSup_of_le (E.symm P)
        (le_iSup_of_le ((hE (E.symm P)).mpr hP') le_rfl)
  apply SetLike.ext
  intro x
  change x ∈ E
      (isotypicComponent k[N] tau.asModule U.asSubmodule) ↔
    x ∈ isotypicComponent k[N] tau.asModule
      (conjugateNormalSubrepresentation rho N g U).asSubmodule
  rw [hmodule]

/-- The characteristic-free Clifford inertia subgroup: the stabilizer of
the intrinsic isotypic component. -/
private noncomputable def repIsotypicComponentStabilizer
    (rho : Representation k G V) (N : Subgroup G) [N.Normal]
    (U : Subrepresentation (rho.comp N.subtype)) : Subgroup G :=
  normalConstituentSubspaceStabilizer rho N
    (repIsotypicComponent (rho.comp N.subtype) U)

private theorem mem_repIsotypicComponentStabilizer_iff
    (rho : Representation k G V) (N : Subgroup G) [N.Normal]
    (U : Subrepresentation (rho.comp N.subtype))
    [Representation.IsIrreducible U.toRepresentation] (g : G) :
    g ∈ repIsotypicComponentStabilizer rho N U ↔
      Nonempty (Representation.Equiv U.toRepresentation
        (conjugateNormalSubrepresentation rho N g U).toRepresentation) := by
  letI : Representation.IsIrreducible
      (conjugateNormalSubrepresentation rho N g U).toRepresentation :=
    (irreducible_conjugateNormalSubrepresentation_iff rho N g U).mpr
      inferInstance
  rw [repIsotypicComponentStabilizer,
    mem_normalConstituentSubspaceStabilizer_iff,
    conjugate_repIsotypicComponent]
  rw [repIsotypicComponent_eq_iff (rho.comp N.subtype)
    (conjugateNormalSubrepresentation rho N g U) U]
  constructor
  · rintro ⟨e⟩
    exact ⟨e.symm⟩
  · rintro ⟨e⟩
    exact ⟨e.symm⟩

private theorem normal_le_repIsotypicComponentStabilizer
    (rho : Representation k G V) (N : Subgroup G) [N.Normal]
    (U : Subrepresentation (rho.comp N.subtype)) :
    N ≤ repIsotypicComponentStabilizer rho N U :=
  normal_le_normalConstituentSubspaceStabilizer rho N
    (repIsotypicComponent (rho.comp N.subtype) U)

end IsotypicComponents

section IsotypicOrbits

variable {k : Type v} [Field k]
variable {G : Type u} [Group G] [Finite G]
variable {V : Type w} [AddCommGroup V] [Module k V]
variable (rho : Representation k G V) (N : Subgroup G) [N.Normal]

/-- Restrict ambient translation of normal-restriction subspaces to an
arbitrary subgroup of the ambient group. -/
@[reducible] private def subgroupNormalRestrictionMulAction
    (H : Subgroup G) :
    MulAction H (Subrepresentation (rho.comp N.subtype)) where
  smul h := conjugateNormalSubrepresentation rho N (h : G)
  one_smul := conjugateNormalSubrepresentation_one rho N
  mul_smul g h := conjugateNormalSubrepresentation_mul rho N (g : G) (h : G)

/-- The finite orbit of a normal-restriction subspace under an ambient
subgroup. -/
private noncomputable def subgroupConstituentOrbitFinset
    (H : Subgroup G) (C : Subrepresentation (rho.comp N.subtype)) :
    Finset (Subrepresentation (rho.comp N.subtype)) := by
  classical
  letI := Fintype.ofFinite H
  exact Finset.univ.image
    (fun h : H => conjugateNormalSubrepresentation rho N (h : G) C)

private theorem mem_subgroupConstituentOrbitFinset_iff
    (H : Subgroup G) (C X : Subrepresentation (rho.comp N.subtype)) :
    X ∈ subgroupConstituentOrbitFinset rho N H C ↔
      ∃ h : H, conjugateNormalSubrepresentation rho N (h : G) C = X := by
  classical
  letI := Fintype.ofFinite H
  simp [subgroupConstituentOrbitFinset]

/-- Orbit--stabilizer for the orbit restricted to an ambient subgroup. -/
private theorem subgroupConstituentOrbitFinset_card
    (H : Subgroup G) (C : Subrepresentation (rho.comp N.subtype)) :
    (subgroupConstituentOrbitFinset rho N H C).card =
      ((normalConstituentSubspaceStabilizer rho N C).comap H.subtype).index := by
  classical
  letI := Fintype.ofFinite H
  letI := subgroupNormalRestrictionMulAction rho N H
  have hstab : MulAction.stabilizer H C =
      (normalConstituentSubspaceStabilizer rho N C).comap H.subtype := by
    ext h
    rfl
  rw [← hstab, MulAction.index_stabilizer]
  symm
  rw [← Set.ncard_coe_finset]
  congr 1
  ext X
  rw [MulAction.mem_orbit_iff]
  change (∃ h : H, conjugateNormalSubrepresentation rho N (h : G) C = X) ↔
    X ∈ subgroupConstituentOrbitFinset rho N H C
  exact (mem_subgroupConstituentOrbitFinset_iff rho N H C X).symm

/-- If the restriction to `H` is irreducible, the `H`-orbit of every
nonzero normal-restriction subspace spans the whole representation. -/
private theorem subgroupConstituentOrbitFinset_sup_eq_top
    (H : Subgroup G) (C : Subrepresentation (rho.comp N.subtype))
    [Representation.IsIrreducible (rho.comp H.subtype)] (hC : C ≠ ⊥) :
    (subgroupConstituentOrbitFinset rho N H C).sup id = ⊤ := by
  classical
  letI := Fintype.ofFinite H
  let S : Subrepresentation (rho.comp N.subtype) :=
    Finset.univ.sup
      (fun h : H => conjugateNormalSubrepresentation rho N (h : G) C)
  have hstable (a : H) :
      conjugateNormalSubrepresentation rho N (a : G) S = S := by
    have hforward (b : H) :
        conjugateNormalSubrepresentation rho N (b : G) S ≤ S := by
      let e := conjugateNormalSubrepresentationOrderIso rho N (b : G)
      change e (Finset.univ.sup
        (fun h : H => conjugateNormalSubrepresentation rho N (h : G) C)) ≤ _
      rw [map_finset_sup]
      apply Finset.sup_le
      intro h _
      change conjugateNormalSubrepresentation rho N (b : G)
        (conjugateNormalSubrepresentation rho N (h : G) C) ≤ S
      rw [← conjugateNormalSubrepresentation_mul]
      exact Finset.le_sup (f := fun z : H =>
        conjugateNormalSubrepresentation rho N (z : G) C)
        (Finset.mem_univ (b * h))
    apply le_antisymm (hforward a)
    have hmapped := conjugateNormalSubrepresentation_mono rho N (a : G)
      (hforward a⁻¹)
    simpa [← conjugateNormalSubrepresentation_mul] using hmapped
  let W : Subrepresentation (rho.comp H.subtype) :=
    { toSubmodule := S.toSubmodule
      apply_mem_toSubmodule h v hv := by
        have hv' : rho (h : G) v ∈
            conjugateNormalSubrepresentation rho N (h : G) S :=
          ⟨v, hv, rfl⟩
        rwa [hstable h] at hv' }
  have hW : W ≠ ⊥ := by
    intro hbot
    apply hC
    apply le_antisymm _ bot_le
    intro v hv
    have hv1 : v ∈ conjugateNormalSubrepresentation rho N (1 : G) C := by
      simpa
    have hvS : v ∈ S := Finset.le_sup
      (f := fun h : H =>
        conjugateNormalSubrepresentation rho N (h : G) C)
      (Finset.mem_univ 1) hv1
    change v ∈ W at hvS
    have : v ∈ (⊥ : Subrepresentation (rho.comp H.subtype)) := by
      simpa [hbot] using hvS
    exact this
  have hWtop : W = ⊤ :=
    (IsSimpleOrder.eq_bot_or_eq_top W).resolve_left hW
  have hStop : S = ⊤ := by
    apply SetLike.ext
    intro v
    change v ∈ W ↔ v ∈ (⊤ : Subrepresentation (rho.comp H.subtype))
    rw [hWtop]
  simpa [subgroupConstituentOrbitFinset, S] using hStop

/-- The module isotypic components occurring in a subgroup orbit. -/
private noncomputable def subgroupIsotypicOrbitSet
    (H : Subgroup G) (U : Subrepresentation (rho.comp N.subtype)) :
    Set (Submodule k[N]
      (Representation.asModule
        (rho.comp N.subtype : Representation k N V))) :=
  Set.range (fun h : H =>
    (conjugateNormalSubrepresentation rho N (h : G)
      (repIsotypicComponent (rho.comp N.subtype) U)).asSubmodule)

/-- For an irreducible ambient restriction, the orbit of one intrinsic
isotypic component is exactly the set of all isotypic components of the
normal restriction. -/
private theorem subgroupIsotypicOrbitSet_eq
    (H : Subgroup G) (U : Subrepresentation (rho.comp N.subtype))
    [Representation.IsIrreducible U.toRepresentation]
    [Representation.IsIrreducible (rho.comp H.subtype)] :
    subgroupIsotypicOrbitSet rho N H U =
      isotypicComponents k[N]
        (Representation.asModule
          (rho.comp N.subtype : Representation k N V)) := by
  let tau : Representation k N V := rho.comp N.subtype
  letI := Fintype.ofFinite H
  let C : Subrepresentation tau := repIsotypicComponent tau U
  let O : Set (Submodule k[N] tau.asModule) :=
    subgroupIsotypicOrbitSet rho N H U
  change O = isotypicComponents k[N] tau.asModule
  have hsubset : O ⊆ isotypicComponents k[N] tau.asModule := by
    rintro D ⟨h, rfl⟩
    let T := conjugateNormalSubrepresentation rho N (h : G) U
    letI : Representation.IsIrreducible T.toRepresentation :=
      (irreducible_conjugateNormalSubrepresentation_iff
        rho N (h : G) U).mpr inferInstance
    refine ⟨T.asSubmodule,
      (irreducible_toRepresentation_iff_isSimpleModule_asSubmodule
        tau T).mp inferInstance, ?_⟩
    rw [← repIsotypicComponent_asSubmodule tau T,
      ← conjugate_repIsotypicComponent rho N (h : G) U]
  have hCne : C ≠ ⊥ := by
    intro hbot
    have hle := le_repIsotypicComponent tau U
    have hUbot : U = ⊥ := le_bot_iff.mp (by simpa [C, hbot] using hle)
    exact ((irreducible_toRepresentation_iff_isAtom tau U).mp
      (inferInstance : Representation.IsIrreducible U.toRepresentation)).1 hUbot
  have hsupSub :
      (subgroupConstituentOrbitFinset rho N H C).sup id = ⊤ :=
    subgroupConstituentOrbitFinset_sup_eq_top rho N H C hCne
  have hmoduleTop :
      Finset.univ.sup (fun h : H ↦
        (conjugateNormalSubrepresentation rho N (h : G) C).asSubmodule) =
          ⊤ := by
    let e := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := tau)
    calc
      Finset.univ.sup (fun h : H ↦
          (conjugateNormalSubrepresentation rho N (h : G) C).asSubmodule) =
          e (Finset.univ.sup (fun h : H ↦
            conjugateNormalSubrepresentation rho N (h : G) C)) := by
              exact (map_finset_sup e Finset.univ
                (fun h : H ↦
                  conjugateNormalSubrepresentation rho N (h : G) C)).symm
      _ = e ((subgroupConstituentOrbitFinset rho N H C).sup id) := by
        apply congrArg e
        simp [subgroupConstituentOrbitFinset]
      _ = ⊤ := by rw [hsupSub, e.map_top]
  have hsup : sSup O = ⊤ := by
    calc
      sSup O = ⨆ h : H,
          (conjugateNormalSubrepresentation rho N (h : G) C).asSubmodule := by
        change sSup (Set.range (fun h : H ↦
          (conjugateNormalSubrepresentation rho N (h : G) C).asSubmodule)) = _
        rw [sSup_range]
      _ = Finset.univ.sup (fun h : H ↦
          (conjugateNormalSubrepresentation rho N (h : G) C).asSubmodule) := by
        rw [Finset.sup_univ_eq_iSup]
      _ = ⊤ := hmoduleTop
  apply Set.Subset.antisymm hsubset
  intro D hD
  by_contra hnot
  have hdis := (sSupIndep_isotypicComponents k[N] tau.asModule).disjoint_sSup
    hD hsubset hnot
  rw [hsup] at hdis
  have hDbot : D = ⊥ := disjoint_top.mp hdis
  exact (bot_lt_isotypicComponents hD).ne' hDbot

/-- The number of intrinsic components in such an orbit is independent of
which irreducible ambient subgroup is used. -/
private theorem subgroupConstituentOrbitFinset_card_eq
    (H L : Subgroup G) (U : Subrepresentation (rho.comp N.subtype))
    [Representation.IsIrreducible U.toRepresentation]
    [Representation.IsIrreducible (rho.comp H.subtype)]
    [Representation.IsIrreducible (rho.comp L.subtype)] :
    (subgroupConstituentOrbitFinset rho N H
        (repIsotypicComponent (rho.comp N.subtype) U)).card =
      (subgroupConstituentOrbitFinset rho N L
        (repIsotypicComponent (rho.comp N.subtype) U)).card := by
  let C := repIsotypicComponent (rho.comp N.subtype) U
  have hcard (A : Subgroup G)
      [Representation.IsIrreducible (rho.comp A.subtype)] :
      (subgroupConstituentOrbitFinset rho N A C).card =
        Set.ncard (subgroupIsotypicOrbitSet rho N A U) := by
    let q := Subrepresentation.subrepresentationSubmoduleOrderIso
      (ρ := (rho.comp N.subtype : Representation k N V))
    have hset : q ''
        (((subgroupConstituentOrbitFinset rho N A C : Finset _)) :
          Set (Subrepresentation (rho.comp N.subtype))) =
        subgroupIsotypicOrbitSet rho N A U := by
      ext D
      constructor
      · rintro ⟨X, hX, rfl⟩
        obtain ⟨a, rfl⟩ :=
          (mem_subgroupConstituentOrbitFinset_iff rho N A C X).mp hX
        exact ⟨a, rfl⟩
      · rintro ⟨a, rfl⟩
        refine ⟨conjugateNormalSubrepresentation rho N (a : G) C, ?_, rfl⟩
        exact (mem_subgroupConstituentOrbitFinset_iff rho N A C _).mpr
          ⟨a, rfl⟩
    rw [← hset, Set.ncard_image_of_injective _ q.injective,
      Set.ncard_coe_finset]
  rw [hcard H, hcard L,
    subgroupIsotypicOrbitSet_eq rho N H U,
    subgroupIsotypicOrbitSet_eq rho N L U]

end IsotypicOrbits

section LinearHelpers

variable {k : Type v} [Field k]
variable {G : Type u} [Group G]
variable {V : Type w} [AddCommGroup V] [Module k V]

/-- Inclusion of the fixed space of a subrepresentation in the ambient
fixed space. -/
private def subrepresentationInvariantsIncl
    (rho : Representation k G V) (R : Subgroup G)
    (U : Subrepresentation rho) :
    Representation.invariants
        (U.toRepresentation.comp R.subtype :
          Representation k R U.toSubmodule) →ₗ[k]
      Representation.invariants
        (rho.comp R.subtype : Representation k R V) where
  toFun x := ⟨(x : U.toSubmodule), by
    rw [Representation.mem_invariants]
    intro r
    exact congrArg Subtype.val
      ((Representation.mem_invariants _ _).mp x.property r)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := by
    apply Subtype.ext
    rfl

private theorem subrepresentationInvariantsIncl_injective
    (rho : Representation k G V) (R : Subgroup G)
    (U : Subrepresentation rho) :
    Function.Injective (subrepresentationInvariantsIncl rho R U) := by
  intro x y hxy
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : Representation.invariants
    (rho.comp R.subtype : Representation k R V) ↦ (z : V)) hxy

/-- A commutator acts trivially on a one-dimensional representation. -/
private theorem commutator_le_ker_of_finrank_eq_one
    (rho : Representation k G V) (hdim : Module.finrank k V = 1) :
    _root_.commutator G ≤ rho.ker := by
  let f : G →* V ≃ₗ[k] V := representationLinearEquivHom rho
  have hf : _root_.commutator G ≤ f.ker := by
    rw [commutator_eq_closure, Subgroup.closure_le]
    rintro z ⟨a, b, rfl⟩
    change f ⁅a, b⁆ = 1
    rw [map_commutatorElement,
      commutatorElement_eq_one_iff_commute]
    rw [commute_iff_eq]
    apply LinearEquiv.toLinearMap_injective
    exact (endomorphisms_commute_of_finrank_eq_one hdim (rho a) (rho b)).eq
  intro g hg
  rw [MonoidHom.mem_ker]
  apply LinearMap.ext
  intro v
  have hfg := MonoidHom.mem_ker.mp (hf hg)
  exact DFunLike.congr_fun hfg v

/-- Invariants of a cyclic representation have the same finite dimension
after extension of scalars. -/
private theorem finrank_representationBaseChange_invariants_of_cyclic
    {F : Type v} {A : Type x} [Field F] [Field A] [Algebra F A]
    {H : Type u} [Group H] [IsCyclic H]
    {W : Type w} [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    (rho : Representation F H W) :
    Module.finrank A
        (representationBaseChange (A := A) rho).invariants =
      Module.finrank F rho.invariants := by
  obtain ⟨z, hzpow⟩ := IsCyclic.exists_generator (α := H)
  have hz : rho.invariants =
      LinearMap.ker (rho z - 1 : Module.End F W) := by
    ext x
    rw [Representation.mem_invariants_iff_of_forall_mem_zpowers
      rho z hzpow x]
    simp [LinearMap.mem_ker, sub_eq_zero]
  have hzA : (representationBaseChange (A := A) rho).invariants =
      LinearMap.ker ((rho z - 1 : Module.End F W).baseChange A) := by
    ext x
    rw [Representation.mem_invariants_iff_of_forall_mem_zpowers
      (representationBaseChange (A := A) rho) z hzpow x]
    simp [representationBaseChange_apply, LinearMap.mem_ker,
      LinearMap.baseChange_sub, LinearMap.baseChange_one, sub_eq_zero]
  rw [hz, hzA]
  calc
    Module.finrank A
        (LinearMap.ker ((rho z - 1 : Module.End F W).baseChange A)) =
      Module.finrank A
        (A ⊗[F] LinearMap.ker (rho z - 1 : Module.End F W)) :=
      (LinearMap.tensorKerEquiv A A
        (rho z - 1 : Module.End F W)).finrank_eq.symm
    _ = Module.finrank F
        (LinearMap.ker (rho z - 1 : Module.End F W)) :=
      Module.finrank_baseChange

end LinearHelpers

section SubgroupInvariantTransport

variable {k : Type v} [Field k]
variable {G : Type u} [Group G]
variable {V : Type w} [AddCommGroup V] [Module k V]

/-- Viewing a subgroup through an intermediate subgroup does not change its
fixed space. -/
private theorem invariants_comp_subgroupOf_eq
    (rho : Representation k G V) {J R : Subgroup G} (hRJ : R ≤ J) :
    Representation.invariants
        ((rho.comp J.subtype).comp (R.subgroupOf J).subtype :
          Representation k (R.subgroupOf J) V) =
      Representation.invariants
        (rho.comp R.subtype : Representation k R V) := by
  apply SetLike.ext
  intro v
  rw [Representation.mem_invariants, Representation.mem_invariants]
  constructor
  · intro hv r
    let rJ : J := ⟨(r : G), hRJ r.property⟩
    let rRJ : R.subgroupOf J := ⟨rJ, r.property⟩
    change rho (r : G) v = v
    exact hv rRJ
  · intro hv r
    let rR : R := ⟨(((r : R.subgroupOf J) : J) : G), r.property⟩
    change rho (((r : R.subgroupOf J) : J) : G) v = v
    exact hv rR

end SubgroupInvariantTransport

section FixedSpaceDichotomy

variable {k : Type v} [Field k]
variable {G : Type u} [Group G] [Finite G]
variable {V : Type w} [AddCommGroup V] [Module k V]
  [FiniteDimensional k V]
variable {K R : Subgroup G}

/-- In a Frobenius representation whose complement-fixed space is a line,
one of two complementary invariant summands is fixed by the kernel. -/
private theorem fixedLine_complement_dichotomy
    (rho : Representation k G V) (hFrob : IsFrobeniusDecomposition K R)
    (hKcard : (Nat.card K : k) ≠ 0)
    (hfix : Module.finrank k
      (Representation.invariants
        (rho.comp R.subtype : Representation k R V)) = 1)
    (U W : Subrepresentation rho) (hUW : IsCompl U W) :
    K ≤ U.toRepresentation.ker ∨ K ≤ W.toRepresentation.ker := by
  classical
  letI := Fintype.ofFinite G
  have hKcardF : (Fintype.card K : k) ≠ 0 := by
    rw [Fintype.card_eq_nat_card]
    exact hKcard
  by_contra h
  push_neg at h
  have hUfix : Representation.invariants
      (U.toRepresentation.comp R.subtype :
        Representation k R U.toSubmodule) ≠ ⊥ :=
    hFrob.complement_invariants_ne_bot U.toRepresentation
      hKcardF h.1
  have hWfix : Representation.invariants
      (W.toRepresentation.comp R.subtype :
        Representation k R W.toSubmodule) ≠ ⊥ :=
    hFrob.complement_invariants_ne_bot W.toRepresentation
      hKcardF h.2
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hUfix
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWfix
  let rhoR : Representation k R V := rho.comp R.subtype
  let uR : rhoR.invariants :=
    subrepresentationInvariantsIncl rho R U ⟨u, hu⟩
  let wR : rhoR.invariants :=
    subrepresentationInvariantsIncl rho R W ⟨w, hw⟩
  have huR0 : uR ≠ 0 := by
    intro hz
    apply hu0
    apply Subtype.ext
    exact congrArg (fun z : rhoR.invariants ↦ (z : V)) hz
  have hwR0 : wR ≠ 0 := by
    intro hz
    apply hw0
    apply Subtype.ext
    exact congrArg (fun z : rhoR.invariants ↦ (z : V)) hz
  have hli : LinearIndependent k ![uR, wR] := by
    rw [LinearIndependent.pair_iff' huR0]
    intro a ha
    have haV : a • ((u : U.toSubmodule) : V) =
        ((w : W.toSubmodule) : V) := congrArg Subtype.val ha
    have hwU : ((w : W.toSubmodule) : V) ∈ U := by
      rw [← haV]
      exact U.toSubmodule.smul_mem a u.property
    have hwbot : ((w : W.toSubmodule) : V) ∈ (⊥ : Submodule k V) := by
      have : ((w : W.toSubmodule) : V) ∈ U ⊓ W := ⟨hwU, w.property⟩
      rw [hUW.disjoint.eq_bot] at this
      exact this
    apply hwR0
    apply Subtype.ext
    exact (Submodule.mem_bot k).mp hwbot
  have htwo : 2 ≤ Module.finrank k rhoR.invariants := by
    simpa using hli.fintype_card_le_finrank
  change 2 ≤ Module.finrank k
    (Representation.invariants
      (rho.comp R.subtype : Representation k R V)) at htwo
  rw [hfix] at htwo
  omega

/-- A nontrivial kernel action on a constituent consumes the unique fixed
line. -/
private theorem constituent_fixed_finrank_eq_one
    (rho : Representation k G V) (hFrob : IsFrobeniusDecomposition K R)
    (hKcard : (Nat.card K : k) ≠ 0)
    (hfix : Module.finrank k
      (Representation.invariants
        (rho.comp R.subtype : Representation k R V)) = 1)
    (U : Subrepresentation rho) (hUK : ¬ K ≤ U.toRepresentation.ker) :
    Module.finrank k
      (Representation.invariants
        (U.toRepresentation.comp R.subtype :
          Representation k R U.toSubmodule)) = 1 := by
  classical
  letI := Fintype.ofFinite G
  have hKcardF : (Fintype.card K : k) ≠ 0 := by
    rw [Fintype.card_eq_nat_card]
    exact hKcard
  have hne := hFrob.complement_invariants_ne_bot U.toRepresentation
    hKcardF hUK
  have hpos : 0 < Module.finrank k
      (Representation.invariants
        (U.toRepresentation.comp R.subtype :
          Representation k R U.toSubmodule)) := by
    exact Nat.pos_of_ne_zero (mt Submodule.finrank_eq_zero.mp hne)
  have hle : Module.finrank k
      (Representation.invariants
        (U.toRepresentation.comp R.subtype :
          Representation k R U.toSubmodule)) ≤
      Module.finrank k
        (Representation.invariants
          (rho.comp R.subtype : Representation k R V)) :=
    (subrepresentationInvariantsIncl rho R U).finrank_le_finrank_of_injective
      (subrepresentationInvariantsIncl_injective rho R U)
  rw [hfix] at hle
  omega

end FixedSpaceDichotomy

section SubgroupRestrictionTransport

variable {k : Type v} [Field k]
variable {G : Type u} [Group G]
variable {V : Type w} [AddCommGroup V] [Module k V]

/-- View a subrepresentation for a subgroup `N` as a subrepresentation for
the subgroup-of copy of `N` inside an intermediate subgroup. -/
private def subgroupOfNormalSubrepresentation
    (rho : Representation k G V) (N H : Subgroup G) (hNH : N ≤ H)
    (U : Subrepresentation (rho.comp N.subtype)) :
    Subrepresentation
      ((rho.comp H.subtype).comp (N.subgroupOf H).subtype :
        Representation k (N.subgroupOf H) V) where
  toSubmodule := U.toSubmodule
  apply_mem_toSubmodule n v hv :=
    U.apply_mem_toSubmodule ⟨((n : N.subgroupOf H) : H), n.property⟩ hv

private noncomputable def subgroupOfNormalSubrepresentationEquiv
    (rho : Representation k G V) (N H : Subgroup G) (hNH : N ≤ H)
    (U W : Subrepresentation (rho.comp N.subtype))
    (e : Representation.Equiv U.toRepresentation W.toRepresentation) :
    Representation.Equiv
      (subgroupOfNormalSubrepresentation rho N H hNH U).toRepresentation
      (subgroupOfNormalSubrepresentation rho N H hNH W).toRepresentation :=
  Representation.Equiv.mk e.toLinearEquiv (fun n =>
    e.toIntertwiningMap.isIntertwining'
      ⟨(((n : N.subgroupOf H) : H) : G), n.property⟩)

private theorem subgroupOfNormalSubrepresentation_conjugate
    (rho : Representation k G V) (N H : Subgroup G) [N.Normal]
    (hNH : N ≤ H) (h : H) (U : Subrepresentation (rho.comp N.subtype)) :
    subgroupOfNormalSubrepresentation rho N H hNH
        (conjugateNormalSubrepresentation rho N (h : G) U) =
      conjugateNormalSubrepresentation (rho.comp H.subtype)
        (N.subgroupOf H) h
        (subgroupOfNormalSubrepresentation rho N H hNH U) := by
  apply Subrepresentation.toSubmodule_injective
  rfl

private theorem irreducible_subgroupOfNormalSubrepresentation
    (rho : Representation k G V) (N H : Subgroup G) (hNH : N ≤ H)
    (U : Subrepresentation (rho.comp N.subtype))
    [Representation.IsIrreducible U.toRepresentation] :
    Representation.IsIrreducible
      (subgroupOfNormalSubrepresentation rho N H hNH U).toRepresentation := by
  let e : N.subgroupOf H ≃* N := Subgroup.subgroupOfEquivOfLe hNH
  let sigma : Representation k (N.subgroupOf H) U.toSubmodule :=
    (subgroupOfNormalSubrepresentation rho N H hNH U).toRepresentation
  have hcomp : sigma.comp e.symm.toMonoidHom = U.toRepresentation := by
    rfl
  letI : Representation.IsIrreducible
      (sigma.comp e.symm.toMonoidHom) := by
    rw [hcomp]
    infer_instance
  exact representation_isIrreducible_of_comp sigma e.symm.toMonoidHom

end SubgroupRestrictionTransport

section CliffordPrimeHelpers

variable {k : Type v} [Field k]
variable {G : Type u} [Group G] [Finite G]
variable {V : Type w} [AddCommGroup V] [Module k V]
  [FiniteDimensional k V]

/-- In the full prime orbit case, the complement norm embeds an intrinsic
component into the fixed line. -/
private theorem constituent_finrank_eq_one_of_componentStabilizer_eq_kernel
    (rho : Representation k G V) (K R : Subgroup G) [K.Normal]
    (hKR : K.IsComplement' R)
    (hfix : Module.finrank k
      (Representation.invariants
        (rho.comp R.subtype : Representation k R V)) = 1)
    (M : Subrepresentation (rho.comp K.subtype))
    [Representation.IsIrreducible M.toRepresentation]
    (hI : repIsotypicComponentStabilizer rho K M = K) :
    Module.finrank k M.toSubmodule = 1 := by
  classical
  letI := Fintype.ofFinite R
  let tauK : Representation k K V := rho.comp K.subtype
  let rhoR : Representation k R V := rho.comp R.subtype
  let C : Subrepresentation tauK := repIsotypicComponent tauK M
  let comps := isotypicComponents k[K] tauK.asModule
  let others : Submodule k[K] tauK.asModule :=
    sSup (comps \ {C.asSubmodule})
  have hCmem : C.asSubmodule ∈ comps := by
    refine ⟨M.asSubmodule, ?_, ?_⟩
    · exact (irreducible_toRepresentation_iff_isSimpleModule_asSubmodule
        tauK M).mp inferInstance
    · simpa [C] using repIsotypicComponent_asSubmodule tauK M
  have hCdis : Disjoint C.asSubmodule others := by
    dsimp [others]
    exact (sSupIndep_isotypicComponents k[K] tauK.asModule).disjoint_sSup
      hCmem Set.diff_subset (by simp)
  let normC : C.toSubmodule →ₗ[k]
      Representation.invariants rhoR :=
    { toFun := fun x ↦ ⟨rhoR.norm (x : V),
        Representation.norm_mem_invariants rhoR (x : V)⟩
      map_add' := by intro x y; apply Subtype.ext; simp
      map_smul' := by intro a x; apply Subtype.ext; simp }
  have hnormC : Function.Injective normC := by
    intro x y hxy
    let z : C.toSubmodule := x - y
    have hxy' : rhoR.norm (x : V) = rhoR.norm (y : V) :=
      congrArg Subtype.val hxy
    have hzNorm : rhoR.norm (z : V) = 0 := by
      dsimp [z]
      rw [map_sub, hxy', sub_self]
    dsimp [rhoR, Representation.norm] at hzNorm
    rw [← Finset.sum_erase_add Finset.univ _
      (Finset.mem_univ (1 : R))] at hzNorm
    have hsumZero :
        (∑ r ∈ Finset.univ.erase (1 : R), rho (r : G) (z : V)) +
          (z : V) = 0 := by
      simpa using hzNorm
    have hsumOthers :
        (∑ r ∈ Finset.univ.erase (1 : R), rho (r : G) (z : V)) ∈
          others := by
      apply Submodule.sum_mem
      intro r hr
      have hrne : r ≠ 1 := (Finset.mem_erase.mp hr).1
      let Cr := conjugateNormalSubrepresentation rho K (r : G) C
      have hCrne : Cr ≠ C := by
        intro heq
        have hrI : (r : G) ∈ repIsotypicComponentStabilizer rho K M := by
          rw [repIsotypicComponentStabilizer,
            mem_normalConstituentSubspaceStabilizer_iff]
          simpa [Cr] using heq
        rw [hI] at hrI
        have hrbot : (r : G) ∈ (⊥ : Subgroup G) := by
          have hrinf : (r : G) ∈ K ⊓ R := ⟨hrI, r.property⟩
          rw [hKR.disjoint.eq_bot] at hrinf
          exact hrinf
        apply hrne
        apply Subtype.ext
        exact Subgroup.mem_bot.mp hrbot
      have hCrmem : Cr.asSubmodule ∈ comps := by
        let Mr := conjugateNormalSubrepresentation rho K (r : G) M
        letI : Representation.IsIrreducible Mr.toRepresentation :=
          (irreducible_conjugateNormalSubrepresentation_iff
            rho K (r : G) M).mpr inferInstance
        refine ⟨Mr.asSubmodule, ?_, ?_⟩
        · exact (irreducible_toRepresentation_iff_isSimpleModule_asSubmodule
            tauK Mr).mp inferInstance
        · rw [← repIsotypicComponent_asSubmodule tauK Mr,
            ← conjugate_repIsotypicComponent rho K (r : G) M]
      have hCrAsNe : Cr.asSubmodule ≠ C.asSubmodule := fun heq ↦
        hCrne ((Subrepresentation.subrepresentationSubmoduleOrderIso
          (ρ := tauK)).injective heq)
      have hdiff : Cr.asSubmodule ∈ comps \ {C.asSubmodule} :=
        ⟨hCrmem, by simpa using hCrAsNe⟩
      have hzCr : rho (r : G) (z : V) ∈ Cr.asSubmodule :=
        ⟨(z : V), z.property, rfl⟩
      exact (show Cr.asSubmodule ≤ others from by
        dsimp [others]; exact le_sSup hdiff) hzCr
    have hzOthers : (z : V) ∈ others := by
      rw [eq_neg_of_add_eq_zero_right hsumZero]
      exact others.neg_mem hsumOthers
    have hzbot : ((z : V) : tauK.asModule) ∈
        C.asSubmodule ⊓ others :=
      ⟨z.property, hzOthers⟩
    rw [hCdis.eq_bot] at hzbot
    change ((z : V) : tauK.asModule) = 0 at hzbot
    have hz0 : ((z : V) : tauK.asModule) = 0 := hzbot
    apply sub_eq_zero.mp
    apply Subtype.ext
    simpa [z] using hz0
  have hCdim : Module.finrank k C.toSubmodule ≤ 1 := by
    calc
      _ ≤ Module.finrank k (Representation.invariants rhoR) :=
        normC.finrank_le_finrank_of_injective hnormC
      _ = 1 := hfix
  have hMne : M.toSubmodule ≠ ⊥ := by
    intro hm
    exact ((irreducible_toRepresentation_iff_isAtom tauK M).mp
      (inferInstance : Representation.IsIrreducible M.toRepresentation)).1
      (Subrepresentation.toSubmodule_injective hm)
  have hMpos : 1 ≤ Module.finrank k M.toSubmodule :=
    Submodule.one_le_finrank_iff.mpr hMne
  have hMC : M.toSubmodule ≤ C.toSubmodule :=
    le_repIsotypicComponent tauK M
  have hMle : Module.finrank k M.toSubmodule ≤
      Module.finrank k C.toSubmodule := Submodule.finrank_mono hMC
  omega

/-- The common Clifford component orbit under two irreducible restrictions
has one element when its cardinality divides coprime ambient orders. -/
private theorem subgroupIsotypicOrbit_card_eq_one
    (rho : Representation k G V)
    (D K R J : Subgroup G) [D.Normal]
    (hDJ : D ≤ J) (hRJ : R ≤ J)
    (hcompJ : (D.subgroupOf J).IsComplement' (R.subgroupOf J))
    (hcop : Nat.Coprime (Nat.card K) (Nat.card R))
    (M : Subrepresentation (rho.comp D.subtype))
    [Representation.IsIrreducible M.toRepresentation]
    [Representation.IsIrreducible (rho.comp K.subtype)]
    [Representation.IsIrreducible (rho.comp J.subtype)] :
    (subgroupConstituentOrbitFinset rho D J
      (repIsotypicComponent (rho.comp D.subtype) M)).card = 1 := by
  let C := repIsotypicComponent (rho.comp D.subtype) M
  have heq :
      (subgroupConstituentOrbitFinset rho D K C).card =
        (subgroupConstituentOrbitFinset rho D J C).card :=
    subgroupConstituentOrbitFinset_card_eq rho D K J M
  have hdivK :
      (subgroupConstituentOrbitFinset rho D K C).card ∣ Nat.card K := by
    rw [subgroupConstituentOrbitFinset_card]
    exact ((normalConstituentSubspaceStabilizer rho D C).comap
      K.subtype).index_dvd_card
  have hDJstab : D.subgroupOf J ≤
      (normalConstituentSubspaceStabilizer rho D C).comap J.subtype := by
    intro d hd
    change (d : G) ∈
      normalConstituentSubspaceStabilizer rho D C
    exact normal_le_normalConstituentSubspaceStabilizer rho D C hd
  have hindexDvd :
      ((normalConstituentSubspaceStabilizer rho D C).comap J.subtype).index ∣
        (D.subgroupOf J).index :=
    Subgroup.index_dvd_of_le hDJstab
  have hDJindex : (D.subgroupOf J).index = Nat.card R := by
    calc
      (D.subgroupOf J).index = Nat.card (R.subgroupOf J) :=
        hcompJ.symm.index_eq_card
      _ = Nat.card R := natCard_subgroupOf_eq hRJ
  have hdivR :
      (subgroupConstituentOrbitFinset rho D J C).card ∣ Nat.card R := by
    rw [subgroupConstituentOrbitFinset_card]
    simpa [hDJindex] using hindexDvd
  have hdivK' :
      (subgroupConstituentOrbitFinset rho D J C).card ∣ Nat.card K := by
    rw [← heq]
    exact hdivK
  exact Nat.eq_one_of_dvd_coprimes hcop hdivK' hdivR

end CliffordPrimeHelpers

section FrobeniusPrimeFixedPointTheorem

/-- Nonvanishing of the ambient group order in a field descends to every
subgroup. -/
private theorem subgroup_natCard_cast_ne_zero
    {k : Type v} [Field k] {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) (hG : (Nat.card G : k) ≠ 0) :
    (Nat.card H : k) ≠ 0 := by
  obtain ⟨m, hm⟩ := H.card_subgroup_dvd_card
  rw [hm, Nat.cast_mul] at hG
  exact left_ne_zero_of_mul hG

private def FrobeniusPrimeRfix1Statement
    (k : Type v) [Field k] [IsAlgClosed k] (n : ℕ) : Prop :=
  ∀ (G : Type u) [Group G] [Finite G],
    Nat.card G = n →
    ∀ (V : Type w) [AddCommGroup V] [Module k V] [FiniteDimensional k V],
      ∀ (rho : Representation k G V) (K R : Subgroup G),
        K.IsComplement' R →
        K.Normal →
        IsSolvable G →
        (Nat.card R).Prime →
        centralizerWithin K R = ⊥ →
        (Nat.card G : k) ≠ 0 →
        Module.finrank k
            (Representation.invariants
              (rho.comp R.subtype : Representation k R V)) = 1 →
        ⁅K, K⁆ ≤ rho.ker

private theorem FrobeniusPrimeRfix1Statement_all
    (k : Type v) [Field k] [IsAlgClosed k] (n : ℕ) :
    FrobeniusPrimeRfix1Statement k n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro G _ _ hcard V _ _ _ rho K R hKR hKnormal hsol hRprime hCKR
        hGcard hfix
      classical
      letI : Fintype G := Fintype.ofFinite G
      letI : K.Normal := hKnormal
      letI : IsSolvable G := hsol
      by_cases hKbot : K = ⊥
      · subst K
        simp
      have hRne : R ≠ ⊥ := by
        rw [← R.one_lt_card_iff_ne_bot]
        exact hRprime.one_lt
      have hreg : IsSemiregularConjugation K R := by
        intro r hr x hx
        have hcomm : Commute (r : G) (x : G) := by
          rw [Commute]
          calc
            (r : G) * (x : G) =
                ((r : G) * (x : G) * (r : G)⁻¹) * (r : G) := by group
            _ = (x : G) * (r : G) := by rw [hx]
        have hcyclic : Subgroup.zpowers (r : G) = R :=
          zpowers_eq_of_mem_subgroup_prime_card
            R hRprime r.property (by
              intro hrG
              apply hr
              apply Subtype.ext
              exact hrG)
        have hxcent : (x : G) ∈ centralizerWithin K R := by
          refine ⟨x.property, ?_⟩
          intro y hy
          have hy' : y ∈ Subgroup.zpowers (r : G) := by rwa [hcyclic]
          obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy'
          exact (hcomm.zpow_left m).eq
        have hxbot : (x : G) ∈ (⊥ : Subgroup G) := by
          rw [← hCKR]
          exact hxcent
        apply Subtype.ext
        exact Subgroup.mem_bot.mp hxbot
      have hRnormK : R ≤ Subgroup.normalizer (K : Set G) := by
        rw [Subgroup.normalizer_eq_top_iff.mpr
          (inferInstance : K.Normal)]
        exact le_top
      have hFrob : IsFrobeniusDecomposition K R :=
        hreg.isFrobeniusDecomposition
          hRnormK hKR.sup_eq_top hKbot hRne
      let D : Subgroup G := ⁅K, K⁆
      have hDK : D ≤ K := by
        dsimp [D]
        exact Subgroup.commutator_le_self K
      letI : D.Normal := by
        dsimp [D]
        infer_instance
      by_contra hconclusion
      have hDnot : ¬ D ≤ rho.ker := by
        simpa [D] using hconclusion
      have hDne : D ≠ ⊥ := by
        intro hDbot
        apply hDnot
        rw [hDbot]
        exact bot_le
      have hDlt : D < K := by
        dsimp [D]
        exact IsSolvable.commutator_lt_of_ne_bot hKbot
      have hRnormD : R ≤ Subgroup.normalizer (D : Set G) := by
        rw [D.normalizer_eq_top]
        exact le_top
      have hKcard : (Nat.card K : k) ≠ 0 :=
        subgroup_natCard_cast_ne_zero K hGcard
      have hDcard : (Nat.card D : k) ≠ 0 :=
        subgroup_natCard_cast_ne_zero D hGcard
      obtain ⟨U, hUirr, hUD⟩ :=
        exists_irreducible_subrepresentation_not_le_ker_of_normal
          rho D hGcard hDnot
      letI : Representation.IsIrreducible U.toRepresentation := hUirr
      let rhoU : Representation k G U.toSubmodule := U.toRepresentation
      have hUK : ¬ K ≤ rhoU.ker := fun h ↦ hUD (hDK.trans h)
      have hUfix : Module.finrank k
          (Representation.invariants
            (rhoU.comp R.subtype : Representation k R U.toSubmodule)) = 1 :=
        constituent_fixed_finrank_eq_one rho hFrob hKcard hfix U hUK
      have hDinv : Representation.invariants
          (rhoU.comp D.subtype : Representation k D U.toSubmodule) = ⊥ := by
        let F := normalInvariantsSubrepresentation rhoU D
        have hF : F = ⊥ := by
          rcases eq_bot_or_eq_top F with hFbot | hFtop
          · exact hFbot
          · exfalso
            apply hUD
            intro d hd
            rw [MonoidHom.mem_ker]
            apply LinearMap.ext
            intro u
            have huF : (u : U.toSubmodule) ∈ F := by
              rw [hFtop]
              trivial
            exact (Representation.mem_invariants _ _).mp huF ⟨d, hd⟩
        change F.toSubmodule = (⊥ : Submodule k U.toSubmodule)
        exact congrArg Subrepresentation.toSubmodule hF

      let J : Subgroup G := R ⊔ D
      let DJ : Subgroup J := D.subgroupOf J
      let RJ : Subgroup J := R.subgroupOf J
      have hDJ : D ≤ J := by exact le_sup_right
      have hRJ : R ≤ J := by exact le_sup_left
      letI : DJ.Normal :=
        Subgroup.normal_subgroupOf_sup_of_le_normalizer hRnormD
      have hcompJ : DJ.IsComplement' RJ := by
        simpa [J, DJ, RJ] using
          properKernel_subgroupOf_isComplement hKR hDK hRnormD
      have hJlt : Nat.card J < Nat.card G := by
        simpa [J] using
          natCard_sup_lt_of_properKernel hKR hDlt hRnormD
      have hsolJ : IsSolvable J := isSolvable_sup
      have hRJprime : (Nat.card RJ).Prime := by
        rw [natCard_subgroupOf_eq hRJ]
        exact hRprime
      have hcentJ : centralizerWithin DJ RJ = ⊥ := by
        apply le_bot_iff.mp
        intro x hx
        have hxG : (x : G) ∈ centralizerWithin K R := by
          refine ⟨hDK hx.1, ?_⟩
          intro r hr
          let rJ : J := ⟨r, hRJ hr⟩
          have hrJ : rJ ∈ RJ := hr
          exact congrArg Subtype.val (hx.2 rJ hrJ)
        have hxbotG : (x : G) ∈ (⊥ : Subgroup G) := by
          rw [← hCKR]
          exact hxG
        exact Subgroup.mem_bot.mpr
          (Subtype.ext (Subgroup.mem_bot.mp hxbotG))
      have hJcard : (Nat.card J : k) ≠ 0 :=
        subgroup_natCard_cast_ne_zero J hGcard
      have hDJcard : (Nat.card DJ : k) ≠ 0 := by
        rw [natCard_subgroupOf_eq hDJ]
        exact hDcard
      let rhoJ : Representation k J U.toSubmodule := rhoU.comp J.subtype
      have hfixJ : Module.finrank k
          (Representation.invariants
            (rhoJ.comp RJ.subtype : Representation k RJ U.toSubmodule)) = 1 := by
        rw [invariants_comp_subgroupOf_eq rhoU hRJ]
        exact hUfix
      have hDinvJ : Representation.invariants
          (rhoJ.comp DJ.subtype : Representation k DJ U.toSubmodule) = ⊥ :=
        invariants_comp_subgroupOf_eq_bot rhoU hDJ hDinv
      have hrecJ : ⁅DJ, DJ⁆ ≤ rhoJ.ker := by
        apply ih (Nat.card J)
        · rwa [← hcard]
        · rfl
        · exact hcompJ
        · infer_instance
        · exact hsolJ
        · exact hRJprime
        · exact hcentJ
        · exact hJcard
        · exact hfixJ

      letI : IsSimpleModule k[G] rhoU.asModule :=
        (Representation.irreducible_iff_isSimpleModule_asModule rhoU).mp
          inferInstance
      letI : Nontrivial rhoU.asModule :=
        IsSimpleModule.nontrivial k[G] rhoU.asModule
      letI : Nontrivial U.toSubmodule :=
        Function.Injective.nontrivial rhoU.asModuleEquiv.injective
      let rhoK : Representation k K U.toSubmodule := rhoU.comp K.subtype
      letI : Nontrivial rhoK.asModule :=
        Function.Injective.nontrivial rhoK.asModuleEquiv.symm.injective
      letI : NeZero (Nat.card K : k) := ⟨hKcard⟩
      letI : IsSemisimpleModule k[K] rhoK.asModule := by infer_instance
      obtain ⟨mK, hmK⟩ :=
        IsSemisimpleModule.exists_simple_submodule k[K] rhoK.asModule
      let M : Subrepresentation rhoK := Subrepresentation.ofSubmodule' mK
      letI : Representation.IsIrreducible M.toRepresentation :=
        (irreducible_toRepresentation_iff_isSimpleModule_asSubmodule
          rhoK M).mpr hmK
      let I : Subgroup G := repIsotypicComponentStabilizer rhoU K M
      have hKI : K ≤ I :=
        normal_le_repIsotypicComponentStabilizer rhoU K M
      have hKindex : K.index = Nat.card R := hKR.symm.index_eq_card
      have hco : IsCoatom K := isCoatom_of_index_eq_prime hRprime hKindex
      have hKirr : Representation.IsIrreducible rhoK := by
        by_cases hIK : I = K
        · have hMdim : Module.finrank k M.toSubmodule = 1 :=
            constituent_finrank_eq_one_of_componentStabilizer_eq_kernel
              rhoU K R hKR hUfix M hIK
          have hcommM : _root_.commutator K ≤ M.toRepresentation.ker :=
            commutator_le_ker_of_finrank_eq_one M.toRepresentation hMdim
          letI : IsSimpleModule k[K] M.toRepresentation.asModule :=
            (Representation.irreducible_iff_isSimpleModule_asModule _).mp
              inferInstance
          letI : Nontrivial M.toRepresentation.asModule :=
            IsSimpleModule.nontrivial k[K] M.toRepresentation.asModule
          letI : Nontrivial M.toSubmodule :=
            Function.Injective.nontrivial
              M.toRepresentation.asModuleEquiv.injective
          obtain ⟨m, hm⟩ := exists_ne (0 : M.toSubmodule)
          have hmD : (m : U.toSubmodule) ∈
              Representation.invariants
                (rhoU.comp D.subtype : Representation k D U.toSubmodule) := by
            rw [Representation.mem_invariants]
            intro d
            have hd := d.property
            change (d : G) ∈ ⁅K, K⁆ at hd
            rw [← K.map_subtype_commutator] at hd
            rcases hd with ⟨x, hx, hxd⟩
            change rhoU (d : G) (m : U.toSubmodule) = (m : U.toSubmodule)
            rw [← hxd]
            have hxker := MonoidHom.mem_ker.mp (hcommM hx)
            have hmfix := DFunLike.congr_fun hxker m
            exact congrArg Subtype.val (by simpa using hmfix)
          have hm0 : (m : U.toSubmodule) = 0 := by
            have hmBot : (m : U.toSubmodule) ∈
                (⊥ : Submodule k U.toSubmodule) := by
              rw [← hDinv]
              exact hmD
            exact (Submodule.mem_bot k).mp hmBot
          exact False.elim (hm (Subtype.ext hm0))
        · have hItop : I = ⊤ := (hco.ne_iff_eq_top hKI).mp hIK
          letI : Fact (Nat.card R).Prime := ⟨hRprime⟩
          letI : IsCyclic R := isCyclic_of_prime_card rfl
          letI : IsCyclic (G ⧸ K) := by
            let e : G ⧸ K ≃* R := hKR.symm.QuotientMulEquiv
            exact isCyclic_of_injective e.toMonoidHom e.injective
          apply normalRestriction_irreducible_of_quotient_isCyclic rhoU K M
          intro g
          apply (mem_repIsotypicComponentStabilizer_iff rhoU K M g).mp
          change g ∈ I
          rw [hItop]
          exact Subgroup.mem_top g
      letI : Representation.IsIrreducible rhoK := hKirr

      have hregD : IsSemiregularConjugation D R := hreg.mono_left hDK
      have hFrobJ : IsFrobeniusDecomposition DJ RJ := by
        simpa [J, DJ, RJ] using
          hregD.isFrobeniusDecomposition_sup hRnormD hDne hRne
      have hJirr : Representation.IsIrreducible rhoJ := by
        letI : NeZero (Nat.card J : k) := ⟨hJcard⟩
        letI : Representation.IsSemisimpleRepresentation rhoJ := by
          infer_instance
        have hFbot : normalInvariantsSubrepresentation rhoJ DJ = ⊥ := by
          apply Subrepresentation.toSubmodule_injective
          exact hDinvJ
        refine { toNontrivial := ?_, eq_bot_or_eq_top := ?_ }
        · refine ⟨⊥, ⊤, fun h ↦ ?_⟩
          have hsub := congrArg
            (fun X : Subrepresentation rhoJ ↦ X.toSubmodule) h
          change (⊥ : Submodule k U.toSubmodule) = ⊤ at hsub
          exact (show (⊥ : Submodule k U.toSubmodule) ≠ ⊤ from bot_ne_top) hsub
        · intro X
          obtain ⟨Y, hXY⟩ := exists_isCompl X
          rcases fixedLine_complement_dichotomy
              rhoJ hFrobJ hDJcard hfixJ X Y hXY with hX | hY
          · left
            have hXF : X ≤ normalInvariantsSubrepresentation rhoJ DJ :=
              (le_normalInvariantsSubrepresentation_iff rhoJ DJ X).mpr hX
            rw [hFbot] at hXF
            exact le_bot_iff.mp hXF
          · right
            have hYF : Y ≤ normalInvariantsSubrepresentation rhoJ DJ :=
              (le_normalInvariantsSubrepresentation_iff rhoJ DJ Y).mpr hY
            rw [hFbot] at hYF
            have hYbot : Y = ⊥ := le_bot_iff.mp hYF
            rw [hYbot] at hXY
            exact eq_top_of_isCompl_bot hXY
      letI : Representation.IsIrreducible rhoJ := hJirr

      let rhoD : Representation k D U.toSubmodule := rhoU.comp D.subtype
      letI : Nontrivial rhoD.asModule :=
        Function.Injective.nontrivial rhoD.asModuleEquiv.symm.injective
      letI : NeZero (Nat.card D : k) := ⟨hDcard⟩
      letI : IsSemisimpleModule k[D] rhoD.asModule := by infer_instance
      obtain ⟨mD, hmD⟩ :=
        IsSemisimpleModule.exists_simple_submodule k[D] rhoD.asModule
      let MD : Subrepresentation rhoD := Subrepresentation.ofSubmodule' mD
      letI : Representation.IsIrreducible MD.toRepresentation :=
        (irreducible_toRepresentation_iff_isSimpleModule_asSubmodule
          rhoD MD).mpr hmD
      have hcop : Nat.Coprime (Nat.card K) (Nat.card R) :=
        hreg.natCard_coprime hRnormK
      have horbit1 := subgroupIsotypicOrbit_card_eq_one
        rhoU D K R J hDJ hRJ hcompJ hcop MD
      let C := repIsotypicComponent (rhoU.comp D.subtype) MD
      let ID := repIsotypicComponentStabilizer rhoU D MD
      have hindex1 : (ID.comap J.subtype).index = 1 := by
        change ((normalConstituentSubspaceStabilizer rhoU D C).comap
          J.subtype).index = 1
        rw [← subgroupConstituentOrbitFinset_card rhoU D J C]
        exact horbit1
      have hIDtop : ID.comap J.subtype = ⊤ :=
        Subgroup.index_eq_one.mp hindex1
      have hequivG (j : J) : Nonempty (Representation.Equiv
          MD.toRepresentation
          (conjugateNormalSubrepresentation rhoU D (j : G) MD).toRepresentation) := by
        apply (mem_repIsotypicComponentStabilizer_iff
          rhoU D MD (j : G)).mp
        change j ∈ ID.comap J.subtype
        rw [hIDtop]
        exact Subgroup.mem_top j
      let MDJ := subgroupOfNormalSubrepresentation rhoU D J hDJ MD
      letI : Representation.IsIrreducible MDJ.toRepresentation :=
        irreducible_subgroupOfNormalSubrepresentation rhoU D J hDJ MD
      have hequivJ (j : J) : Nonempty (Representation.Equiv
          MDJ.toRepresentation
          (conjugateNormalSubrepresentation rhoJ DJ j MDJ).toRepresentation) := by
        obtain ⟨e⟩ := hequivG j
        let eJ := subgroupOfNormalSubrepresentationEquiv rhoU D J hDJ MD
          (conjugateNormalSubrepresentation rhoU D (j : G) MD) e
        exact ⟨by
          change Representation.Equiv
            (subgroupOfNormalSubrepresentation rhoU D J hDJ MD).toRepresentation
            (conjugateNormalSubrepresentation (rhoU.comp J.subtype)
              (D.subgroupOf J) j
              (subgroupOfNormalSubrepresentation rhoU D J hDJ MD)).toRepresentation
          rw [← subgroupOfNormalSubrepresentation_conjugate
            rhoU D J hDJ j MD]
          exact eJ⟩
      letI : Fact (Nat.card RJ).Prime := ⟨hRJprime⟩
      letI : IsCyclic RJ := isCyclic_of_prime_card rfl
      letI : IsCyclic (J ⧸ DJ) := by
        let e : J ⧸ DJ ≃* RJ := hcompJ.symm.QuotientMulEquiv
        exact isCyclic_of_injective e.toMonoidHom e.injective
      have hDJirr : Representation.IsIrreducible
          (rhoJ.comp DJ.subtype : Representation k DJ U.toSubmodule) :=
        normalRestriction_irreducible_of_quotient_isCyclic
          rhoJ DJ MDJ hequivJ
      let sigmaDJ : Representation k DJ U.toSubmodule := rhoJ.comp DJ.subtype
      letI : Representation.IsIrreducible sigmaDJ := hDJirr
      have hder : _root_.commutator DJ ≤ sigmaDJ.ker := by
        intro d hd
        apply (mem_ker_comp_subtype_iff rhoJ DJ d).mpr
        apply hrecJ
        rw [← DJ.map_subtype_commutator]
        exact ⟨d, hd, rfl⟩
      let Q := DJ ⧸ sigmaDJ.ker
      let sigmaQ : Representation k Q U.toSubmodule :=
        quotientKerRepresentation sigmaDJ
      let q : DJ →* Q := QuotientGroup.mk' sigmaDJ.ker
      letI : IsMulCommutative Q :=
        Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hder
      letI : Representation.IsIrreducible (sigmaQ.comp q) := by
        change Representation.IsIrreducible sigmaDJ
        infer_instance
      letI : Representation.IsIrreducible sigmaQ :=
        representation_isIrreducible_of_comp sigmaQ q
      have hdim : Module.finrank k U.toSubmodule = 1 :=
        Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative sigmaQ
      have hcommK : _root_.commutator K ≤ rhoK.ker :=
        commutator_le_ker_of_finrank_eq_one rhoK hdim
      apply hUD
      intro d hd
      change (d : G) ∈ ⁅K, K⁆ at hd
      rw [← K.map_subtype_commutator] at hd
      rcases hd with ⟨x, hx, rfl⟩
      exact (mem_ker_comp_subtype_iff rhoU K x).mp (hcommK hx)

/-- Bender--Glauberman Theorem 3.5 over an algebraically closed field. -/
private theorem Frobenius_prime_rfix1_algClosed
    {k : Type v} [Field k] [IsAlgClosed k]
    {G : Type u} [Group G] [Finite G] [IsSolvable G]
    {V : Type w} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (rho : Representation k G V) (K R : Subgroup G) [K.Normal]
    (hKR : K.IsComplement' R)
    (hRprime : (Nat.card R).Prime)
    (hCKR : centralizerWithin K R = ⊥)
    (hGcard : (Nat.card G : k) ≠ 0)
    (hfix : Module.finrank k
      (Representation.invariants
        (rho.comp R.subtype : Representation k R V)) = 1) :
    ⁅K, K⁆ ≤ rho.ker := by
  exact FrobeniusPrimeRfix1Statement_all k (Nat.card G)
    G rfl V rho K R hKR inferInstance inferInstance
      hRprime hCKR hGcard hfix

/-- Bender--Glauberman Theorem 3.5: for a solvable Frobenius group with
prime complement, a representation with a one-dimensional complement-fixed
space is trivial on the derived subgroup of the kernel. -/
theorem Frobenius_prime_rfix1
    {k : Type v} [Field k]
    {G : Type u} [Group G] [Finite G] [IsSolvable G]
    {V : Type w} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (rho : Representation k G V) (K R : Subgroup G) [K.Normal]
    (hKR : K.IsComplement' R)
    (hRprime : (Nat.card R).Prime)
    (hCKR : centralizerWithin K R = ⊥)
    (hGcard : (Nat.card G : k) ≠ 0)
    (hfix : Module.finrank k
      (Representation.invariants
        (rho.comp R.subtype : Representation k R V)) = 1) :
    ⁅K, K⁆ ≤ rho.ker := by
  classical
  let A := AlgebraicClosure k
  let W := A ⊗[k] V
  let sigma : Representation A G W := representationBaseChange rho
  have hGcardA : (Nat.card G : A) ≠ 0 := by
    intro hzero
    apply hGcard
    apply (algebraMap k A).injective
    simpa [A] using hzero
  letI : Fact (Nat.card R).Prime := ⟨hRprime⟩
  letI : IsCyclic R := isCyclic_of_prime_card rfl
  have hfixA : Module.finrank A
      (Representation.invariants
        (sigma.comp R.subtype : Representation A R W)) = 1 := by
    change Module.finrank A
        (Representation.invariants
          ((representationBaseChange rho).comp R.subtype :
            Representation A R W)) = 1
    rw [show (representationBaseChange rho).comp R.subtype =
        representationBaseChange
          (rho.comp R.subtype : Representation k R V) by rfl,
      finrank_representationBaseChange_invariants_of_cyclic, hfix]
  have hsigma : ⁅K, K⁆ ≤ sigma.ker :=
    Frobenius_prime_rfix1_algClosed sigma K R
      hKR hRprime hCKR hGcardA hfixA
  intro g hg
  apply MonoidHom.mem_ker.mpr
  apply moduleEnd_baseChangeHom_injective (F := k) (A := A)
  rw [map_one]
  simpa [sigma, W, representationBaseChange] using
    (MonoidHom.mem_ker.mp (hsigma hg))

/-- Fixed vectors in the elementary-abelian conjugation representation are
the elements of the corresponding centralizer. -/
private noncomputable def
    subgroupOfConjugationInvariantsEquivCentralizer
    {E : Type*} [Group E] (V J A : Subgroup E) (p : ℕ)
    [IsMulCommutative V] [Module (ZMod p) (Additive V)]
    (hJ : J ≤ Subgroup.normalizer (V : Set E)) (hAJ : A ≤ J) :
    Representation.invariants
        (((normalizerConjugationRepresentation V p).comp
          (Subgroup.inclusion hJ)).comp
            (A.subgroupOf J).subtype) ≃
      Additive (centralizerWithin V A) where
  toFun x := Additive.ofMul
    ⟨(x : Additive V).toMul, ⟨x.val.toMul.2, by
      intro a ha
      let aJ : J := ⟨a, hAJ ha⟩
      let aAJ : A.subgroupOf J := ⟨aJ, ha⟩
      have hxE := congrArg
        (fun y : Additive V ↦ (y.toMul : E))
        (x.property aAJ)
      change a * (x.val.toMul : E) * a⁻¹ =
        (x.val.toMul : E) at hxE
      calc
        a * (x.val.toMul : E) =
            (a * (x.val.toMul : E) * a⁻¹) * a := by group
        _ = (x.val.toMul : E) * a := by rw [hxE]⟩⟩
  invFun z :=
    ⟨Additive.ofMul ⟨(z.toMul : E), z.toMul.2.1⟩, by
      intro a
      apply Additive.toMul.injective
      apply Subtype.ext
      change
        (((a : A.subgroupOf J) : J) : E) *
            (z.toMul : E) *
            (((a : A.subgroupOf J) : J) : E)⁻¹ =
          (z.toMul : E)
      have hcomm := z.toMul.2.2
        ((((a : A.subgroupOf J) : J) : E)) a.property
      rw [hcomm]
      group⟩
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv z := by
    apply Additive.toMul.injective
    apply Subtype.ext
    rfl

/-- A fixed space over `ZMod p` equivalent to a type of cardinality `p` is
one-dimensional.  Keeping this argument outside the concrete conjugation
construction avoids any dependence on its local endomorphism instances. -/
private theorem invariants_finrank_eq_one_of_equiv_card_prime
    {p : ℕ} [Fact p.Prime]
    {H : Type*} [Group H]
    {M : Type*} [AddCommGroup M] [Module (ZMod p) M]
    (rho : Representation (ZMod p) H M)
    (hfinite : Module.Finite (ZMod p) M)
    {C : Type*} (e : rho.invariants ≃ C)
    (hcard : Nat.card C = p) :
    Module.finrank (ZMod p) rho.invariants = 1 := by
  letI : Module.Finite (ZMod p) M := hfinite
  have hcardInv : Nat.card rho.invariants = p :=
    (Nat.card_congr e).trans hcard
  have hcardFormula :
      Nat.card rho.invariants =
        p ^ Module.finrank (ZMod p) rho.invariants := by
    simpa only [Nat.card_zmod] using
      (Module.natCard_eq_pow_finrank
        (K := ZMod p) (V := rho.invariants))
  apply Nat.pow_right_injective (Fact.out : p.Prime).two_le
  calc
    p ^ Module.finrank (ZMod p) rho.invariants =
        Nat.card rho.invariants := hcardFormula.symm
    _ = p := hcardInv
    _ = p ^ 1 := by simp

/-- Internal elementary-abelian action form of Bender--Glauberman
Theorem 3.5. -/
theorem commutator_le_centralizerWithin_of_frobenius_prime_fixed
    {A : Type u} [Group A] [Finite A]
    {k : ℕ} [Fact k.Prime]
    (J K R V : Subgroup A)
    [IsSolvable J] [(K.subgroupOf J).Normal]
    (hKJ : K ≤ J) (hRJ : R ≤ J)
    (hKR : (K.subgroupOf J).IsComplement' (R.subgroupOf J))
    (hRprime : (Nat.card R).Prime)
    (hCKR : centralizerWithin K R = ⊥)
    (hVelem : IsElementaryAbelianGroup k V)
    (hJV : J ≤ Subgroup.normalizer (V : Set A))
    (hJprime : IsPPrimeSubgroup k J)
    (hCVR : Nat.card (centralizerWithin V R) = k) :
    ⁅K, K⁆ ≤ centralizerWithin K V := by
  classical
  letI : IsMulCommutative V := hVelem.commutative
  letI : Semiring (ZMod k) := (ZMod.commRing k).toSemiring
  letI : AddCommGroup (Additive V) := inferInstance
  letI : AddCommMonoid (Additive V) :=
    (inferInstance : AddCommGroup (Additive V)).toAddCommMonoid
  letI : Module (ZMod k) (Additive V) :=
    elementaryAbelianZModModule V k hVelem.pow_eq_one
  let hVmoduleFinite : Module.Finite (ZMod k) (Additive V) :=
    Module.Finite.of_fg_top (by
      rw [← Submodule.span_univ]
      exact Submodule.fg_span Set.finite_univ)
  letI : Module.Finite (ZMod k) (Additive V) := hVmoduleFinite
  let endMonoid : Monoid (Module.End (ZMod k) (Additive V)) :=
    Module.End.instMonoid
  letI : Monoid (Module.End (ZMod k) (Additive V)) := endMonoid
  letI : MulOne (Module.End (ZMod k) (Additive V)) :=
    endMonoid.toMulOne
  letI : MulOneClass (Module.End (ZMod k) (Additive V)) :=
    endMonoid.toMulOneClass
  let rhoN : Representation (ZMod k)
      (Subgroup.normalizer (V : Set A)) (Additive V) :=
    normalizerConjugationRepresentation V k
  let inclusion : J →* Subgroup.normalizer (V : Set A) :=
    Subgroup.inclusion hJV
  let rho : J →* (Additive V →ₗ[ZMod k] Additive V) :=
    @MonoidHom.comp J (Subgroup.normalizer (V : Set A))
      (Module.End (ZMod k) (Additive V)) _ _ inferInstance rhoN inclusion
  have hRprimeJ : (Nat.card (R.subgroupOf J)).Prime := by
    rw [natCard_subgroupOf_eq hRJ]
    exact hRprime
  have hCKRJ :
      centralizerWithin (K.subgroupOf J) (R.subgroupOf J) = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hxA : (x : A) ∈ centralizerWithin K R := by
      refine ⟨hx.1, ?_⟩
      intro r hr
      let rJ : J := ⟨r, hRJ hr⟩
      have hrRJ : rJ ∈ R.subgroupOf J := hr
      exact congrArg Subtype.val (hx.2 rJ hrRJ)
    have hxbot : (x : A) ∈ (⊥ : Subgroup A) := by
      rw [← hCKR]
      exact hxA
    exact Subgroup.mem_bot.mpr
      (Subtype.ext (Subgroup.mem_bot.mp hxbot))
  have hJcard : (Nat.card J : ZMod k) ≠ 0 := by
    intro hzero
    have hkdiv : k ∣ Nat.card J :=
      (ZMod.natCast_eq_zero_iff (Nat.card J) k).mp hzero
    exact
      (Nat.not_coprime_of_dvd_of_dvd
        (Fact.out : k.Prime).one_lt dvd_rfl hkdiv)
        (show Nat.Coprime k (Nat.card J) from hJprime)
  have hcentralizerCard :
      Nat.card (Additive (centralizerWithin V R)) = k := by
    calc
      Nat.card (Additive (centralizerWithin V R)) =
          Nat.card (centralizerWithin V R) :=
        Nat.card_congr Additive.toMul
      _ = k := hCVR
  have hfix :=
    invariants_finrank_eq_one_of_equiv_card_prime
      (rho.comp (R.subgroupOf J).subtype :
        Representation (ZMod k) (R.subgroupOf J) (Additive V))
      hVmoduleFinite
      (C := Additive (centralizerWithin V R))
      (by
        simpa only [rho, rhoN, inclusion] using
          (subgroupOfConjugationInvariantsEquivCentralizer
            V J R k hJV hRJ))
      hcentralizerCard
  have hlocal :
      ⁅K.subgroupOf J, K.subgroupOf J⁆ ≤ rho.ker :=
    @Frobenius_prime_rfix1
      (ZMod k) inferInstance
      J inferInstance inferInstance inferInstance
      (Additive V) inferInstance inferInstance hVmoduleFinite rho
      (K.subgroupOf J) (R.subgroupOf J)
      (inferInstance : (K.subgroupOf J).Normal)
      hKR hRprimeJ hCKRJ hJcard hfix
  intro x hx
  have hxmap :
      x ∈ ⁅K.subgroupOf J, K.subgroupOf J⁆.map J.subtype := by
    rw [map_subgroupOf_commutator hKJ hKJ]
    exact hx
  rcases hxmap with ⟨j, hj, rfl⟩
  refine ⟨(Subgroup.commutator_le_left
    (K.subgroupOf J) (K.subgroupOf J)) hj, ?_⟩
  intro v hv
  have hjrho := MonoidHom.mem_ker.mp (hlocal hj)
  have hfixed := LinearMap.congr_fun hjrho
    (Additive.ofMul (⟨v, hv⟩ : V))
  change
    Additive.ofMul
        ((Subgroup.inclusion hJV j) • (⟨v, hv⟩ : V)) =
      Additive.ofMul (⟨v, hv⟩ : V) at hfixed
  have hfixedV := congrArg Additive.toMul hfixed
  have hconj := congrArg Subtype.val hfixedV
  change (j : A) * v * (j : A)⁻¹ = v at hconj
  symm
  calc
    (j : A) * v =
        ((j : A) * v * (j : A)⁻¹) * (j : A) := by group
    _ = v * (j : A) := by rw [hconj]

alias Frobenius_prime_cent_prime :=
  commutator_le_centralizerWithin_of_frobenius_prime_fixed

end FrobeniusPrimeFixedPointTheorem

end

end Submission.OddOrder.BG.Section03
