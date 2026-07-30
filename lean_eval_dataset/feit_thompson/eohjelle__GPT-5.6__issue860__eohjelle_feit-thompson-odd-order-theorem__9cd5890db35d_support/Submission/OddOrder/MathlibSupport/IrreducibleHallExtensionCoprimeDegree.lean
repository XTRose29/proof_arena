import Mathlib.GroupTheory.SchurZassenhaus
import Mathlib.GroupTheory.SemidirectProduct
import Submission.OddOrder.MathlibSupport.IrreducibleCharacterRigidity
import Submission.OddOrder.MathlibSupport.IrreducibleCommutantScalar
import Submission.OddOrder.MathlibSupport.IrreducibleHallExtensionFDRep
import Submission.OddOrder.MathlibSupport.IrreducibleHallExtensionProjective
import Submission.OddOrder.MathlibSupport.RepresentationAutomorphismTwist
import Submission.OddOrder.MathlibSupport.RepresentationDeterminant
import Submission.OddOrder.MathlibSupport.RepresentationIrreducibleComp
import Submission.OddOrder.PF.Section01.CharacterCompleteness
import Submission.OddOrder.PF.Section01.NormalSubgroupInduction

/-!
# Extending an invariant Hall character in coprime degree

This file contains the representation-theoretic construction behind the
Hall-character extension used in Peterfalvi 1.7(c).  The final elementary
degree-divisibility input is deliberately separated: here the degree is
assumed coprime to the Hall index.
-/

namespace Submission.OddOrder.MathlibSupport

noncomputable section

open Submission.OddOrder.PF
open scoped MonoidAlgebra

universe u v

variable {T k : Type u} [Group T] [Fintype T]
variable [Field k] [IsAlgClosed k] [CharZero k]

omit [CharZero k] in
/-- Two invertible intertwiners from an irreducible representation to the
same target differ by multiplication by a nonzero scalar. -/
theorem exists_units_smul_eq_of_equiv
    {G V : Type v} [Group G] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V]
    (rho sigma : Representation k G V)
    [Representation.IsIrreducible rho]
    (e f : Representation.Equiv rho sigma) :
    ∃ c : kˣ, e.toLinearEquiv = c • f.toLinearEquiv := by
  let q : Representation.Equiv rho rho := e.trans f.symm
  obtain ⟨c, hc⟩ := exists_eq_smul_one_of_commute_irreducible rho
    q.toLinearMap fun g ↦ by
      change q.toLinearMap ∘ₗ rho g = rho g ∘ₗ q.toLinearMap
      exact q.toIntertwiningMap.isIntertwining' g
  have hq (x : V) : q x = c • x := by
    have hx := congrArg (fun F : Module.End k V ↦ F x) hc
    simpa [q] using hx
  letI : Nontrivial rho.asModule :=
    IsSimpleModule.nontrivial k[G] rho.asModule
  letI : Nontrivial V := inferInstanceAs (Nontrivial rho.asModule)
  have hc0 : c ≠ 0 := by
    intro hc0
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    have hqx : q x = 0 := by rw [hq, hc0, zero_smul]
    exact hx (q.injective (by simpa using hqx))
  refine ⟨Units.mk0 c hc0, ?_⟩
  ext x
  change e x = c • f x
  apply f.symm.injective
  calc
    f.symm (e x) = q x := rfl
    _ = c • x := hq x
    _ = f.symm (c • f x) := by rw [map_smul, f.symm_apply_apply]

omit [CharZero k] in
/-- A coherent family of conjugation-twist equivalences is initially only
projective.  In coprime degree its factor set can be killed, producing an
honest linear action. -/
theorem exists_linearEquivHom_of_equiv_twists_of_coprime
    {G Q V : Type v} [Group G] [Group Q] [Fintype Q]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (rho : Representation k G V) [Representation.IsIrreducible rho]
    (phi : Q →* MulAut G)
    (e : ∀ q : Q, Representation.Equiv rho
      (rho.comp (phi q).toMonoidHom))
    (hcop : Nat.Coprime (Module.finrank k V) (Fintype.card Q)) :
    ∃ R : Q →* V ≃ₗ[k] V, ∀ q, ∃ c : kˣ,
      R q = c • (e q).toLinearEquiv := by
  let L : Q → V ≃ₗ[k] V := fun q ↦ (e q).toLinearEquiv
  have hL_intertwines (q : Q) (g : G) (x : V) :
      L q (rho g x) = rho (phi q g) (L q x) := by
    have hx := LinearMap.congr_fun
      ((e q).toIntertwiningMap.isIntertwining' g) x
    simpa [L, LinearMap.comp_apply] using hx
  let E (a b : Q) : Representation.Equiv rho
      (rho.comp (phi (a * b)).toMonoidHom) :=
    Representation.Equiv.mk (L a * L b) (fun g ↦ by
      ext x
      change L a (L b (rho g x)) =
        rho (phi (a * b) g) (L a (L b x))
      rw [hL_intertwines b g, hL_intertwines a (phi b g)]
      simp)
  have hscalar (a b : Q) : ∃ c : kˣ,
      L a * L b = c • L (a * b) := by
    obtain ⟨c, hc⟩ := exists_units_smul_eq_of_equiv rho
      (rho.comp (phi (a * b)).toMonoidHom) (E a b) (e (a * b))
    refine ⟨c, ?_⟩
    change L a * L b = c • L (a * b) at hc
    exact hc
  let alpha : Q → Q → kˣ := fun a b ↦ (hscalar a b).choose
  have hL (a b : Q) : L a * L b = alpha a b • L (a * b) :=
    (hscalar a b).choose_spec
  have halpha : IsScalarFactorSet alpha := by
    intro a b c
    letI : Nontrivial rho.asModule :=
      IsSimpleModule.nontrivial k[G] rho.asModule
    letI : Nontrivial V := inferInstanceAs (Nontrivial rho.asModule)
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    have hLx : L (a * b * c) x ≠ 0 := by
      intro hzero
      apply hx
      apply (L (a * b * c)).injective
      simpa using hzero
    have hL_apply (p q : Q) (y : V) :
        L p (L q y) = (alpha p q : k) • L (p * q) y := by
      have hy := congrArg (fun f : V ≃ₗ[k] V ↦ f y) (hL p q)
      simpa only [LinearEquiv.mul_apply, LinearEquiv.smul_apply] using hy
    apply Units.ext
    apply smul_left_injective k hLx
    calc
      ((alpha a b * alpha (a * b) c : kˣ) : k) • L (a * b * c) x =
          (alpha a b : k) •
            ((alpha (a * b) c : k) • L (a * b * c) x) := by
        rw [Units.val_mul, smul_smul]
      _ = (alpha a b : k) • L (a * b) (L c x) := by
        rw [hL_apply (a * b) c]
      _ = L a (L b (L c x)) := (hL_apply a b (L c x)).symm
      _ = L a ((alpha b c : k) • L (b * c) x) := by
        rw [hL_apply b c]
      _ = (alpha b c : k) • L a (L (b * c) x) := by
        rw [map_smul]
      _ = (alpha b c : k) •
          ((alpha a (b * c) : k) • L (a * (b * c)) x) := by
        rw [hL_apply a (b * c)]
      _ = ((alpha b c * alpha a (b * c) : kˣ) : k) •
          L (a * b * c) x := by
        rw [Units.val_mul, smul_smul, mul_assoc]
  exact exists_linearEquivHom_of_projective_of_coprime L alpha halpha hL hcop

/-- Full character inertia supplies an intertwiner from the chosen
realization to each direct conjugation twist. -/
theorem nonempty_equiv_conjugate_of_inertia_eq_top
    (K : Subgroup T) [K.Normal]
    (theta : IrreducibleCharacter K k)
    (hInv : ClassFunction.inertia K (theta : ClassFunction K k) = ⊤)
    (t : T) :
    Nonempty (Representation.Equiv theta.representation.ρ
      (theta.representation.ρ.comp
        (MulAut.conjNormal t).toMonoidHom)) := by
  let V := theta.representation
  let rho := V.ρ
  letI : CategoryTheory.Simple V := theta.representation_simple
  letI : Representation.IsIrreducible rho :=
    representation_isIrreducible_of_simple_fdRep V
  let twist : Representation k K V :=
    rho.comp (MulAut.conjNormal t).toMonoidHom
  letI : Representation.IsIrreducible twist :=
    representation_irreducible_comp_mulAut rho (MulAut.conjNormal t)
  apply nonempty_representationEquiv_of_irreducible_character_eq rho twist
  funext x
  rw [representation_comp_mulAut_character]
  have ht : t⁻¹ ∈ ClassFunction.inertia K (theta : ClassFunction K k) := by
    rw [hInv]
    exact Subgroup.mem_top _
  have hfix :=
    (ClassFunction.mem_inertia_iff K (theta : ClassFunction K k) t⁻¹).mp ht
  have hx := congrArg (fun f : ClassFunction K k ↦ f x) hfix
  rw [ClassFunction.normalConjugate_apply] at hx
  have harg : (MulAut.conjNormal t⁻¹).symm x =
      MulAut.conjNormal t x := by
    apply Subtype.ext
    rw [MulAut.conjNormal_symm_apply, MulAut.conjNormal_apply]
    simp
  rw [harg] at hx
  calc
    _root_.Representation.character rho x = theta x :=
      theta.representation_character x
    _ = theta (MulAut.conjNormal t x) := hx.symm
    _ = _root_.Representation.character rho (MulAut.conjNormal t x) :=
      (theta.representation_character _).symm

/-- An invariant irreducible character of a normal Hall subgroup extends
when its degree is coprime to the Hall index. -/
theorem exists_irreducible_extension_of_normal_hall_of_coprime_degree
    (K : Subgroup T) [K.Normal]
    (theta : IrreducibleCharacter K k)
    (hHall : Nat.Coprime (Nat.card K) K.index)
    (hDegree : Nat.Coprime
      (Module.finrank k theta.representation) K.index)
    (hInv : ClassFunction.inertia K (theta : ClassFunction K k) = ⊤) :
    ∃ psi : IrreducibleCharacter T k,
      ClassFunction.restrict K (psi : ClassFunction T k) =
        (theta : ClassFunction K k) := by
  obtain ⟨C, hcomp⟩ := K.exists_right_complement'_of_coprime hHall
  let V := theta.representation
  let rho := V.ρ
  letI : CategoryTheory.Simple V := theta.representation_simple
  letI : Representation.IsIrreducible rho :=
    representation_isIrreducible_of_simple_fdRep V
  let phi : C →* MulAut K :=
    K.normalizerMonoidHom.comp
      (Subgroup.inclusion (K.normalizer_eq_top ▸ le_top))
  letI : Fintype C := Fintype.ofFinite C
  let e : ∀ c : C, Representation.Equiv rho
      (rho.comp (phi c).toMonoidHom) := fun c ↦
    Classical.choice
      (nonempty_equiv_conjugate_of_inertia_eq_top K theta hInv (c : T))
  have hcopC : Nat.Coprime (Module.finrank k V) (Fintype.card C) := by
    rw [Fintype.card_eq_nat_card, ← hcomp.symm.index_eq_card]
    exact hDegree
  obtain ⟨R, hR⟩ :=
    exists_linearEquivHom_of_equiv_twists_of_coprime rho phi e hcopC
  have he_intertwines (c : C) (g : K) (x : V) :
      (e c) (rho g x) = rho (phi c g) ((e c) x) := by
    change (((e c).toLinearMap ∘ₗ rho g) x) =
      (((rho (phi c g)) ∘ₗ (e c).toLinearMap) x)
    rw [(e c).toIntertwiningMap.isIntertwining' g]
    rfl
  have hR_intertwines (c : C) (g : K) (x : V) :
      R c (rho g x) = rho (phi c g) (R c x) := by
    obtain ⟨d, hd⟩ := hR c
    rw [hd]
    change (d : k) • (e c) (rho g x) =
      rho (phi c g) ((d : k) • (e c) x)
    calc
      (d : k) • (e c) (rho g x) =
          (d : k) • rho (phi c g) ((e c) x) :=
        congrArg (fun y : V ↦ (d : k) • y)
          (he_intertwines c g x)
      _ = rho (phi c g) ((d : k) • (e c) x) :=
        (map_smul (rho (phi c g)) (d : k) ((e c) x)).symm
  have hcompat (c : C) :
      (representationLinearEquivHom rho).comp (phi c).toMonoidHom =
        (MulAut.conj (R c)).toMonoidHom.comp
          (representationLinearEquivHom rho) := by
    ext g x
    change rho (phi c g) x = R c (rho g ((R c)⁻¹ x))
    rw [hR_intertwines]
    simp
  let rhoSemiEquiv : SemidirectProduct K C phi →* V ≃ₗ[k] V :=
    SemidirectProduct.lift (representationLinearEquivHom rho) R hcompat
  let rhoSemi : Representation k (SemidirectProduct K C phi) V :=
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp rhoSemiEquiv
  let tau : SemidirectProduct K C phi ≃* T :=
    SemidirectProduct.mulEquivSubgroup hcomp
  let rhoT : Representation k T V := rhoSemi.comp tau.symm.toMonoidHom
  have htau_inl (g : K) :
      tau (SemidirectProduct.inl g) = (g : T) := by
    simp [tau, phi, SemidirectProduct.mulEquivSubgroup,
      SemidirectProduct.monoidHomSubgroup]
  have htau_symm_coe (g : K) :
      tau.symm (g : T) = SemidirectProduct.inl g := by
    apply tau.injective
    rw [tau.apply_symm_apply, htau_inl]
  have hrhoRestrict : rhoT.comp K.subtype = rho := by
    ext g x
    change rhoSemi (tau.symm (g : T)) x = rho g x
    rw [htau_symm_coe]
    simp [rhoSemi, rhoSemiEquiv, representationLinearEquivHom]
  letI : Representation.IsIrreducible (rhoT.comp K.subtype) := by
    rw [hrhoRestrict]
    infer_instance
  letI : Representation.IsIrreducible rhoT :=
    representation_isIrreducible_of_comp rhoT K.subtype
  let W : FDRep k T := FDRep.of rhoT
  letI : CategoryTheory.Simple W := simple_fdRep_of_isIrreducible rhoT
  let psi : IrreducibleCharacter T k := IrreducibleCharacter.ofFDRep W
  refine ⟨psi, ?_⟩
  change ClassFunction.restrict K (ClassFunction.ofRepresentation rhoT) =
    (theta : ClassFunction K k)
  rw [ClassFunction.restrict_ofRepresentation, hrhoRestrict]
  exact theta.ofRepresentation_representation

end

end Submission.OddOrder.MathlibSupport
