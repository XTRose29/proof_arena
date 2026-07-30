import Submission.OddOrder.MathlibSupport.FaithfulIrreducibleCenter
import Submission.OddOrder.MathlibSupport.FaithfulQuotientRepresentation
import Submission.OddOrder.MathlibSupport.Centralizer
import Submission.OddOrder.MathlibSupport.MinimalNormalUnderElementaryAbelian
import Submission.OddOrder.MathlibSupport.MinimalNormalUnderExistence
import Submission.OddOrder.MathlibSupport.RepresentationIrreducibleComp

/-!
# Cocyclic fixed points for abelian actions on prime groups

This is the prime-group specialization of the centralizer-generation input
used in `BGsection7.v`, Theorem 7.2.  It produces exactly the cocyclic
subgroup needed there, without porting the substantially more general
`BGsection1.coprime_abelian_gen_cent`.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped IsMulCommutative

universe u

variable {G : Type u} [Group G] [Finite G]

/-- If an abelian subgroup `A` normalizes a nontrivial finite `q`-group
`Q`, then some normal cocyclic subgroup of `A` has a nontrivial centralizer
in `Q`.

The proof chooses a minimal nontrivial `A`-invariant subgroup of `Q`.  Its
conjugation representation is elementary abelian and irreducible.  After
quotienting `A` by the representation kernel, faithfulness and Schur's
lemma make the (abelian) quotient cyclic, while the minimal subgroup is
fixed pointwise by that kernel. -/
theorem exists_normal_cocyclic_centralizerWithin_ne_bot_of_isPGroup
    {q : ℕ} [Fact q.Prime] (A Q : Subgroup G)
    (hAcomm : IsMulCommutative A)
    (hAQ : A ≤ Subgroup.normalizer (Q : Set G))
    (hQp : IsPGroup q Q) (hQne : Q ≠ ⊥) :
    ∃ C : Subgroup G,
      C ≤ A ∧
      (C.subgroupOf A).Normal ∧
      IsCyclic (A ⧸ C.subgroupOf A) ∧
      centralizerWithin Q C ≠ ⊥ := by
  classical
  obtain ⟨E, hEQ, hEmin⟩ :=
    exists_minimalNormalUnder_le hQne hAQ
  have hEp : IsPGroup q E := hQp.to_le hEQ
  letI : IsMulCommutative A := hAcomm
  letI : Group.IsNilpotent E := hEp.isNilpotent
  letI : IsMulCommutative E :=
    hEmin.isMulCommutative_of_isSolvable
  have hEpow : ∀ x : E, x ^ q = 1 :=
    hEmin.pow_eq_one_of_isPGroup hEp
  letI : Semiring (ZMod q) := (ZMod.commRing q).toSemiring
  letI : AddCommGroup (Additive E) := inferInstance
  letI : AddCommMonoid (Additive E) :=
    (inferInstance : AddCommGroup (Additive E)).toAddCommMonoid
  letI : Module (ZMod q) (Additive E) :=
    elementaryAbelianZModModule E q hEpow
  let endMonoid : Monoid (Module.End (ZMod q) (Additive E)) :=
    Module.End.instMonoid
  letI : Monoid (Module.End (ZMod q) (Additive E)) := endMonoid
  letI : MulOne (Module.End (ZMod q) (Additive E)) := endMonoid.toMulOne
  letI : MulOneClass (Module.End (ZMod q) (Additive E)) :=
    endMonoid.toMulOneClass
  let actor : A →* Subgroup.normalizer (E : Set G) :=
    Subgroup.inclusion hEmin.le_normalizer
  let rho : Representation (ZMod q) A (Additive E) :=
    (normalizerConjugationRepresentation E q).comp actor
  have hirr : Representation.IsIrreducible rho := by
    let restrict : A.subgroupOf (Subgroup.normalizer (E : Set G)) →* A :=
      (Subgroup.subgroupOfEquivOfLe hEmin.le_normalizer).toMonoidHom
    have hcomp : rho.comp restrict =
        (normalizerConjugationRepresentation E q).comp
          (A.subgroupOf (Subgroup.normalizer (E : Set G))).subtype := by
      rfl
    letI : Representation.IsIrreducible (rho.comp restrict) := by
      rw [hcomp]
      exact normalizerConjugation_isIrreducible_of_isMinimalNormalUnder
        E A q hEmin
    exact representation_isIrreducible_of_comp rho restrict
  let rhoFaithful : Representation (ZMod q) (A ⧸ rho.ker) (Additive E) :=
    quotientKerRepresentation rho
  letI : Representation.IsIrreducible rho := hirr
  letI : Representation.IsIrreducible rhoFaithful := by
    letI : Representation.IsIrreducible
        (rhoFaithful.comp (QuotientGroup.mk' rho.ker)) := by
      change Representation.IsIrreducible rho
      exact hirr
    apply representation_isIrreducible_of_comp rhoFaithful
      (QuotientGroup.mk' rho.ker)
  have hquotCyclic : IsCyclic (A ⧸ rho.ker) := by
    have hcenterCyclic : IsCyclic (Subgroup.center (A ⧸ rho.ker)) :=
      center_isCyclic_of_faithful_irreducible rhoFaithful
        (by simpa [rhoFaithful] using
          quotientKerRepresentation_injective rho)
    have htopCyclic : IsCyclic (⊤ : Subgroup (A ⧸ rho.ker)) := by
      rw [Subgroup.center_eq_top] at hcenterCyclic
      exact hcenterCyclic
    exact Subgroup.topEquiv.isCyclic.mp htopCyclic
  let C : Subgroup G := rho.ker.map A.subtype
  have hCA : C ≤ A := Subgroup.map_subtype_le rho.ker
  have hCsub : C.subgroupOf A = rho.ker := by
    ext x
    constructor
    · rintro ⟨y, hy, hxy⟩
      have hyx : y = x := Subtype.ext hxy
      simpa [hyx] using hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hEcentral : E ≤ centralizerWithin Q C := by
    intro e he
    refine ⟨hEQ he, ?_⟩
    intro c hc
    rcases hc with ⟨a, ha, rfl⟩
    have haKer := MonoidHom.mem_ker.mp ha
    have hfixed := LinearMap.congr_fun haKer (Additive.ofMul ⟨e, he⟩)
    have hconj : (a : G) * e * (a : G)⁻¹ = e := by
      exact congrArg (fun z : Additive E ↦ ((z.toMul : E) : G)) hfixed
    calc
      (a : G) * e = ((a : G) * e * (a : G)⁻¹) * (a : G) := by group
      _ = e * (a : G) := by rw [hconj]
  refine ⟨C, hCA, ?_, ?_, ?_⟩
  · rw [hCsub]
    infer_instance
  · rw [hCsub]
    exact hquotCyclic
  · intro hbot
    apply hEmin.ne_bot
    exact eq_bot_iff.mpr (hEcentral.trans (le_of_eq hbot))

end Submission.OddOrder.MathlibSupport
