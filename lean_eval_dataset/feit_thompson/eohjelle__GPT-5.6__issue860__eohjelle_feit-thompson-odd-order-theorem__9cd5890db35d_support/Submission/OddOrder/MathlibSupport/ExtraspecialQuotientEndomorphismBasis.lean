import Submission.OddOrder.MathlibSupport.DistinctCharacterEigenvectors
import Submission.OddOrder.MathlibSupport.EndomorphismConjugationRepresentation
import Submission.OddOrder.MathlibSupport.ExtraspecialQuotientAlternating
import Submission.OddOrder.MathlibSupport.IrreducibleCenterScalar
import Submission.OddOrder.MathlibSupport.RepresentationBurnsideDensity

/-!
The center quotient of an extraspecial group indexes a basis of the
endomorphism algebra of every faithful irreducible nonmodular
representation.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped BigOperators MonoidAlgebra commutatorElement IsMulCommutative

universe u v w

variable {k : Type u} {G : Type v} {V : Type w}
variable [Field k] [IsAlgClosed k] [Group G] [Finite G]
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- A fixed representative of a coset modulo the center. -/
noncomputable def centerQuotientRepresentative
    (x : G ⧸ Subgroup.center G) : G :=
  Classical.choose (QuotientGroup.mk'_surjective (Subgroup.center G) x)

@[simp]
theorem centerQuotientRepresentative_mk
    (x : G ⧸ Subgroup.center G) :
    QuotientGroup.mk' (Subgroup.center G) (centerQuotientRepresentative x) = x :=
  Classical.choose_spec
    (QuotientGroup.mk'_surjective (Subgroup.center G) x)

/-- The represented endomorphism attached to a center quotient class. -/
noncomputable def centerQuotientRepresentationEnd
    (rho : Representation k G V) (x : G ⧸ Subgroup.center G) :
    Module.End k V :=
  rho (centerQuotientRepresentative x)

namespace IsExtraspecial

/-- The scalar commutator character associated to a center quotient class. -/
noncomputable def quotientCommutatorScalarCharacter
    (hG : IsExtraspecial G) (rho : Representation k G V)
    [Representation.IsIrreducible rho]
    (x : G ⧸ Subgroup.center G) :
    (G ⧸ Subgroup.center G) →* kˣ where
  toFun y := schurCenterScalarCharacter rho
    (hG.toIsSpecial.quotientCommutatorPairing y x)
  map_one' := by simp
  map_mul' y z := by
    change schurCenterScalarCharacter rho
        (hG.toIsSpecial.quotientCommutatorPairing (y * z) x) = _
    rw [map_mul]
    change schurCenterScalarCharacter rho
        (hG.toIsSpecial.quotientCommutatorPairing y x *
          hG.toIsSpecial.quotientCommutatorPairing z x) = _
    rw [map_mul]

/-- Faithfulness and nondegeneracy make the scalar commutator characters
pairwise distinct. -/
theorem quotientCommutatorScalarCharacter_injective
    (hG : IsExtraspecial G) {p : ℕ} [Fact p.Prime]
    (hpG : IsPGroup p G)
    (rho : Representation k G V) [Representation.IsIrreducible rho]
    (hrho : Function.Injective rho) :
    Function.Injective (hG.quotientCommutatorScalarCharacter rho) := by
  have hscalar : Function.Injective (schurCenterScalarCharacter rho) :=
    (IsPGroup.representation_injective_iff_schurCenterScalarCharacter rho hpG).mp hrho
  intro x y hxy
  apply hG.toIsSpecial.quotientCommutatorPairing_injective
  apply MonoidHom.ext
  intro t
  calc
    hG.toIsSpecial.quotientCommutatorPairing x t =
        (hG.toIsSpecial.quotientCommutatorPairing t x)⁻¹ :=
      hG.toIsSpecial.quotientCommutatorPairing_swap x t
    _ = (hG.toIsSpecial.quotientCommutatorPairing t y)⁻¹ := by
      apply congrArg Inv.inv
      apply hscalar
      exact DFunLike.congr_fun hxy t
    _ = hG.toIsSpecial.quotientCommutatorPairing y t :=
      (hG.toIsSpecial.quotientCommutatorPairing_swap y t).symm

/-- Conjugation on the endomorphism algebra descends through the center. -/
noncomputable def centerQuotientEndomorphismConjugationRepresentation
    (rho : Representation k G V) [Representation.IsIrreducible rho] :
    Representation k (G ⧸ Subgroup.center G) (Module.End k V) :=
  QuotientGroup.lift (Subgroup.center G)
    (endomorphismConjugationRepresentation rho) (by
      intro z hz
      rw [MonoidHom.mem_ker]
      apply LinearMap.ext
      intro T
      let zc : Subgroup.center G := ⟨z, hz⟩
      have hzscalar : rho z =
          (schurCenterScalarCharacter rho zc : k) •
            (1 : Module.End k V) := by
        ext v
        exact schurCenterScalarCharacter_smul rho zc v
      have hzInvScalar : rho z⁻¹ =
          (schurCenterScalarCharacter rho zc : k)⁻¹ •
            (1 : Module.End k V) := by
        have hzinv := schurCenterScalarCharacter_smul rho zc⁻¹
        ext v
        simpa using hzinv v
      rw [endomorphismConjugationRepresentation_apply,
        hzscalar, hzInvScalar]
      ext v
      simp [Module.End.mul_apply])

@[simp]
theorem centerQuotientEndomorphismConjugationRepresentation_mk
    (rho : Representation k G V) [Representation.IsIrreducible rho]
    (g : G) :
    centerQuotientEndomorphismConjugationRepresentation rho
        (QuotientGroup.mk' (Subgroup.center G) g) =
      endomorphismConjugationRepresentation rho g :=
  rfl

/-- The quotient-indexed represented operators carry their corresponding
scalar commutator characters. -/
theorem centerQuotientRepresentationEnd_eigen
    (hG : IsExtraspecial G)
    (rho : Representation k G V) [Representation.IsIrreducible rho]
    (x y : G ⧸ Subgroup.center G) :
    centerQuotientEndomorphismConjugationRepresentation rho y
        (centerQuotientRepresentationEnd rho x) =
      (hG.quotientCommutatorScalarCharacter rho x y : k) •
        centerQuotientRepresentationEnd rho x := by
  obtain ⟨g, rfl⟩ :=
    QuotientGroup.mk'_surjective (Subgroup.center G) y
  let r : G := centerQuotientRepresentative x
  have hr : QuotientGroup.mk' (Subgroup.center G) r = x :=
    centerQuotientRepresentative_mk x
  rw [centerQuotientEndomorphismConjugationRepresentation_mk]
  change endomorphismConjugationRepresentation rho g
      (rho r) =
    (schurCenterScalarCharacter rho
      (hG.toIsSpecial.quotientCommutatorPairing
        (QuotientGroup.mk' (Subgroup.center G) g) x) : k) • rho r
  rw [endomorphismConjugationRepresentation_apply]
  rw [← hr]
  rw [IsSpecial.quotientCommutatorPairing_mk_mk]
  let z : Subgroup.center G :=
    hG.toIsSpecial.commutatorPairing g r
  calc
    rho g * rho r * rho g⁻¹ = rho (g * r * g⁻¹) := by
      rw [rho.map_mul, rho.map_mul]
    _ = rho ((z : G) * r) := by
      apply congrArg rho
      change g * r * g⁻¹ = ⁅g, r⁆ * r
      simpa using (conj_eq_commutatorElement_mul (g₁ := g) (g₂ := r))
    _ = rho z * rho r := by
      rw [rho.map_mul]
    _ = (schurCenterScalarCharacter rho z : k) • rho r := by
      ext v
      simp

/-- Any represented element carries the scalar commutator character indexed
by its class modulo the center. -/
theorem representationEnd_eigen_quotientCommutatorScalarCharacter
    (hG : IsExtraspecial G)
    (rho : Representation k G V) [Representation.IsIrreducible rho]
    (x : G) (y : G ⧸ Subgroup.center G) :
    centerQuotientEndomorphismConjugationRepresentation rho y (rho x) =
      (hG.quotientCommutatorScalarCharacter rho
        (QuotientGroup.mk' (Subgroup.center G) x) y : k) • rho x := by
  obtain ⟨g, rfl⟩ :=
    QuotientGroup.mk'_surjective (Subgroup.center G) y
  rw [centerQuotientEndomorphismConjugationRepresentation_mk]
  change endomorphismConjugationRepresentation rho g (rho x) =
    (schurCenterScalarCharacter rho
      (hG.toIsSpecial.commutatorPairing g x) : k) • rho x
  rw [endomorphismConjugationRepresentation_apply]
  let z : Subgroup.center G := hG.toIsSpecial.commutatorPairing g x
  calc
    rho g * rho x * rho g⁻¹ = rho (g * x * g⁻¹) := by
      rw [rho.map_mul, rho.map_mul]
    _ = rho ((z : G) * x) := by
      apply congrArg rho
      change g * x * g⁻¹ = ⁅g, x⁆ * x
      simpa using (conj_eq_commutatorElement_mul (g₁ := g) (g₂ := x))
    _ = rho z * rho x := by rw [rho.map_mul]
    _ = (schurCenterScalarCharacter rho z : k) • rho x := by
      ext v
      simp

/-- Represented elements belonging to pairwise distinct center cosets are
linearly independent in a faithful irreducible extraspecial
representation. -/
theorem representationEnd_linearIndependent_of_quotient_injective
    (hG : IsExtraspecial G) {p : ℕ} [Fact p.Prime]
    (hpG : IsPGroup p G)
    (rho : Representation k G V) [Representation.IsIrreducible rho]
    (hrho : Function.Injective rho)
    (hcard : (Nat.card G : k) ≠ 0)
    {I : Type*} [Fintype I] (a : I → G)
    (ha : Function.Injective
      (fun i ↦ QuotientGroup.mk' (Subgroup.center G) (a i))) :
    LinearIndependent k (fun i ↦ rho (a i)) := by
  letI := Fintype.ofFinite (G ⧸ Subgroup.center G)
  letI : IsSimpleModule k[G] rho.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule _).mp inferInstance
  letI : Nontrivial rho.asModule :=
    IsSimpleModule.nontrivial k[G] rho.asModule
  letI : Nontrivial V :=
    Function.Injective.nontrivial rho.asModuleEquiv.injective
  have hquotientCard :
      (Fintype.card (G ⧸ Subgroup.center G) : k) ≠ 0 := by
    rw [← Nat.card_eq_fintype_card]
    intro hzero
    apply hcard
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
      (Subgroup.center G), Nat.cast_mul, hzero, zero_mul]
  apply linearIndependent_of_distinct_unitsCharacters
    (centerQuotientEndomorphismConjugationRepresentation rho)
    (fun i ↦ hG.quotientCommutatorScalarCharacter rho
      (QuotientGroup.mk' (Subgroup.center G) (a i)))
    ((hG.quotientCommutatorScalarCharacter_injective hpG rho hrho).comp ha)
    (fun i ↦ rho (a i))
  · intro i hi
    have hunit : rho (a i) * rho (a i)⁻¹ = 1 := by
      rw [← rho.map_mul]
      simp
    rw [hi, zero_mul] at hunit
    exact zero_ne_one hunit
  · exact fun i ↦ hG.representationEnd_eigen_quotientCommutatorScalarCharacter
      rho (a i)
  · exact hquotientCard

/-- The represented center-quotient operators are linearly independent. -/
theorem centerQuotientRepresentationEnd_linearIndependent
    (hG : IsExtraspecial G) {p : ℕ} [Fact p.Prime]
    (hpG : IsPGroup p G)
    (rho : Representation k G V) [Representation.IsIrreducible rho]
    (hrho : Function.Injective rho)
    (hcard : (Nat.card G : k) ≠ 0) :
    LinearIndependent k (centerQuotientRepresentationEnd rho) := by
  letI := Fintype.ofFinite (G ⧸ Subgroup.center G)
  letI : IsSimpleModule k[G] rho.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule _).mp inferInstance
  letI : Nontrivial rho.asModule :=
    IsSimpleModule.nontrivial k[G] rho.asModule
  letI : Nontrivial V :=
    Function.Injective.nontrivial rho.asModuleEquiv.injective
  have hquotientCard :
      (Fintype.card (G ⧸ Subgroup.center G) : k) ≠ 0 := by
    rw [← Nat.card_eq_fintype_card]
    intro hzero
    apply hcard
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
      (Subgroup.center G), Nat.cast_mul, hzero, zero_mul]
  apply linearIndependent_of_distinct_unitsCharacters
    (centerQuotientEndomorphismConjugationRepresentation rho)
    (hG.quotientCommutatorScalarCharacter rho)
    (hG.quotientCommutatorScalarCharacter_injective hpG rho hrho)
    (centerQuotientRepresentationEnd rho)
  · intro x hx
    change rho (centerQuotientRepresentative x) = 0 at hx
    have hunit :
        rho (centerQuotientRepresentative x) *
            rho (centerQuotientRepresentative x)⁻¹ = 1 := by
      rw [← rho.map_mul]
      simp
    rw [hx, zero_mul] at hunit
    exact zero_ne_one hunit
  · exact hG.centerQuotientRepresentationEnd_eigen rho
  · exact hquotientCard

/-- The represented center-quotient operators span the full endomorphism
algebra by Burnside density. -/
theorem span_centerQuotientRepresentationEnd_eq_top
    (hG : IsExtraspecial G)
    (rho : Representation k G V) [Representation.IsIrreducible rho] :
    Submodule.span k (Set.range (centerQuotientRepresentationEnd rho)) = ⊤ := by
  let S : Submodule k (Module.End k V) :=
    Submodule.span k (Set.range (centerQuotientRepresentationEnd rho))
  have hrepresented (g : G) : rho g ∈ S := by
    let x : G ⧸ Subgroup.center G :=
      QuotientGroup.mk' (Subgroup.center G) g
    have hx : centerQuotientRepresentative x / g ∈ Subgroup.center G :=
      QuotientGroup.eq_iff_div_mem.mp (centerQuotientRepresentative_mk x)
    let z : Subgroup.center G :=
      ⟨centerQuotientRepresentative x / g, hx⟩
    have hg : g = (z : G)⁻¹ * centerQuotientRepresentative x := by
      dsimp [z]
      rw [div_eq_mul_inv]
      group
    have hscalar : rho (z : G)⁻¹ =
        (schurCenterScalarCharacter rho z : k)⁻¹ •
          (1 : Module.End k V) := by
      have hz := schurCenterScalarCharacter_smul rho z⁻¹
      ext v
      simpa using hz v
    rw [hg, rho.map_mul, hscalar]
    change (schurCenterScalarCharacter rho z : k)⁻¹ •
      rho (centerQuotientRepresentative x) ∈ S
    exact S.smul_mem _ (Submodule.subset_span ⟨x, rfl⟩)
  have halgebra (a : k[G]) : rho.asAlgebraHom a ∈ S := by
    induction a using MonoidAlgebra.induction_on with
    | hM g =>
        simpa using hrepresented g
    | hadd a b ha hb =>
        simpa only [map_add] using S.add_mem ha hb
    | hsmul c a ha =>
        simpa only [map_smul] using S.smul_mem c ha
  apply top_unique
  intro T _
  obtain ⟨a, rfl⟩ :=
    Representation.IsIrreducible.asAlgebraHom_surjective rho T
  exact halgebra a

/-- In nonmodular characteristic, a faithful irreducible extraspecial
representation has endomorphism dimension equal to the center-quotient
order. -/
theorem faithful_irreducible_finrank_end_eq_quotient_center_card
    (hG : IsExtraspecial G) {p : ℕ} [Fact p.Prime]
    (hpG : IsPGroup p G)
    (rho : Representation k G V) [Representation.IsIrreducible rho]
    (hrho : Function.Injective rho)
    (hcard : (Nat.card G : k) ≠ 0) :
    Module.finrank k (Module.End k V) =
      Nat.card (G ⧸ Subgroup.center G) := by
  letI := Fintype.ofFinite (G ⧸ Subgroup.center G)
  have hli := hG.centerQuotientRepresentationEnd_linearIndependent
    hpG rho hrho hcard
  have hdim := finrank_span_eq_card hli
  rw [hG.span_centerQuotientRepresentationEnd_eq_top rho,
    finrank_top k (Module.End k V)] at hdim
  simpa only [Nat.card_eq_fintype_card] using hdim

end IsExtraspecial

end Submission.OddOrder.MathlibSupport
