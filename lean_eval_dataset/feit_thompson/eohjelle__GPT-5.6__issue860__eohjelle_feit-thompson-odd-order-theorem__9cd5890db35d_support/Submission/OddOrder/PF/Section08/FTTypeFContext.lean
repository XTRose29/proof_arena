import Submission.OddOrder.BG.Section12.Tau2CoprimeCyclicSplit
import Submission.OddOrder.MathlibSupport.CoprimeHallConjugatorAdjustment
import Submission.OddOrder.PF.Section03.CyclicTIGroupFacts
import Submission.OddOrder.PF.Section06.FrobeniusKernelInduction
import Submission.OddOrder.PF.Section08.FTContextDefinitions

/-!
# Peterfalvi Section 8: the type-F context

This module proves the type-F part of Peterfalvi Section 8.  It records the
all-type-one alternative, transports type F between complements of the same
Fitting core, and packages the three consequences used by the later
character-theoretic phases.
-/

namespace Submission.OddOrder.PF

noncomputable section

open Submission.OddOrder.BG.Section03
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section10
open Submission.OddOrder.BG.Section12
open Submission.OddOrder.BG.Section14
open Submission.OddOrder.BG.Section15
open Submission.OddOrder.BG.Section16
open Submission.OddOrder.MathlibSupport
open CategoryTheory Limits
open scoped BigOperators Classical Pointwise IsMulCommutative

universe u v w

variable {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]

/-! The existing character-transport wrapper uses one universe for the
group and coefficient field.  Section 8 needs the same construction with
`G : Type u` and ordinary complex characters, so keep the polymorphic
version local to this implementation. -/

private instance repInjectiveTypeF8
    {A : Type u} {k : Type v} [Group A] [Finite A] [Field k]
    [NeZero (Nat.card A : k)] (V : Rep.{w} k A) : Injective V := by
  rw [← Rep.equivalenceModuleMonoidAlgebra.map_injective_iff,
    ← Module.injective_iff_injective_object]
  exact Module.injective_of_isSemisimpleRing _ _

private instance fdRepInjectiveTypeF8
    {A : Type u} {k : Type v} [Group A] [Finite A] [Field k]
    [NeZero (Nat.card A : k)] (V : FDRep k A) : Injective V :=
  (forget₂ (FDRep k A) (Rep k A)).injective_of_map_injective inferInstance

private theorem simple_iff_end_rank_one_typeF8
    {A : Type u} {k : Type v} [Group A] [Finite A] [Field k]
    [IsAlgClosed k] [NeZero (Nat.card A : k)] (V : FDRep k A) :
    Simple V ↔ Module.finrank k (V ⟶ V) = 1 where
  mp h := finrank_endomorphism_simple_eq_one k V
  mpr h := by
    refine { mono_isIso_iff_nonzero {W} f _ :=
      ⟨fun hf habs ↦ ?_, fun hf ↦ ?_⟩ }
    · rw [habs, isIsoZero_iff_source_target_isZero] at hf
      obtain ⟨g, hg⟩ : ∃ g : V ⟶ V, g ≠ 0 :=
        (Module.finrank_pos_iff_exists_ne_zero (R := k)).mp (by grind)
      exact hg (hf.2.eq_zero_of_src g)
    · suffices Epi f by exact isIso_of_mono_of_epi f
      suffices Epi (Abelian.image.ι f) by
        rw [← Abelian.image.fac f]
        exact epi_comp _ _
      rw [← Abelian.image.fac f] at hf
      set ι := Abelian.image.ι f
      set φ := Injective.factorThru (𝟙 _) ι
      have hφι : φ ≫ ι ≠ 0 := by
        intro habs
        have hιφ : 𝟙 _ = ι ≫ φ := (Injective.comp_factorThru (𝟙 _) ι).symm
        apply_fun (· ≫ ι) at hιφ
        simp_all
      obtain ⟨c, hc⟩ : ∃ c : k, c • _ = 𝟙 V :=
        (finrank_eq_one_iff_of_nonzero' _ hφι).mp h (𝟙 V)
      refine Preadditive.epi_of_cancel_zero _ (fun g hg ↦ ?_)
      apply_fun (· ≫ g) at hc
      simpa [hg] using hc.symm

private theorem simple_iff_char_norm_one_typeF8
    {A : Type u} {k : Type v} [Group A] [Fintype A] [Field k]
    [IsAlgClosed k] [CharZero k] (V : FDRep k A) :
    Simple V ↔
      ∑ a : A, V.character a * V.character a⁻¹ = Nat.card A where
  mp h := by
    have : NeZero (Nat.card A : k) := by
      rw [← @Fintype.card_eq_nat_card A (by assumption)]
      exact NeZero.charZero
    have := invertibleOfNonzero (NeZero.ne (Nat.card A : k))
    have := invertibleOfNonzero (NeZero.ne (Fintype.card A : k))
    classical
    have hnorm : ⅟(Nat.card A : k) •
        ∑ a, V.character a * V.character a⁻¹ = 1 := by
      simpa only [Nonempty.intro (Iso.refl V), ↓reduceIte,
        Fintype.card_eq_nat_card] using FDRep.char_orthonormal V V
    apply_fun (· * (Fintype.card A : k)) at hnorm
    rwa [mul_comm, ← smul_eq_mul, smul_smul, Fintype.card_eq_nat_card,
      mul_invOf_self, smul_eq_mul, one_mul, one_mul] at hnorm
  mpr h := by
    have : NeZero (Nat.card A : k) := by
      rw [← @Fintype.card_eq_nat_card A (by assumption)]
      exact NeZero.charZero
    have := invertibleOfNonzero (NeZero.ne (Fintype.card A : k))
    have := invertibleOfNonzero (NeZero.ne (Nat.card A : k))
    have eq := FDRep.scalar_product_char_eq_finrank_equivariant V V
    rw [h] at eq
    simp only [invOf_eq_inv, smul_eq_mul, inv_mul_cancel_of_invertible,
      Fintype.card_eq_nat_card] at eq
    rw [simple_iff_end_rank_one_typeF8, ← Nat.cast_inj (R := k),
      ← eq, Nat.cast_one]

private theorem compMulEquivFDRep_simple8
    {A B : Type u} {k : Type v}
    [Group A] [Group B] [Fintype A] [Fintype B]
    [Field k] [IsAlgClosed k] [CharZero k]
    (e : A ≃* B) (V : FDRep k B) [CategoryTheory.Simple V] :
    CategoryTheory.Simple (FDRep.of (V.ρ.comp e.toMonoidHom)) := by
  rw [simple_iff_char_norm_one_typeF8]
  have hV := (simple_iff_char_norm_one_typeF8 V).mp (by infer_instance)
  calc
    (∑ a : A,
        (FDRep.of (V.ρ.comp e.toMonoidHom)).character a *
          (FDRep.of (V.ρ.comp e.toMonoidHom)).character a⁻¹) =
        ∑ b : B, V.character b * V.character b⁻¹ := by
      apply Fintype.sum_equiv e.toEquiv
      intro a
      change V.character (e a) * V.character (e a⁻¹) =
        V.character (e a) * V.character (e a)⁻¹
      rw [map_inv]
    _ = (Nat.card B : k) := hV
    _ = (Nat.card A : k) := by
      exact_mod_cast (Nat.card_congr e.toEquiv).symm

private def comapIrreducibleTypeF8
    {A B : Type u} {k : Type v}
    [Group A] [Group B] [Fintype A] [Fintype B]
    [Field k] [IsAlgClosed k] [CharZero k]
    (e : A ≃* B) (chi : IrreducibleCharacter B k) :
    IrreducibleCharacter A k := by
  letI : CategoryTheory.Simple chi.representation :=
    chi.representation_simple
  letI : CategoryTheory.Simple
      (FDRep.of (chi.representation.ρ.comp e.toMonoidHom)) :=
    compMulEquivFDRep_simple8 e chi.representation
  exact IrreducibleCharacter.ofFDRep
    (FDRep.of (chi.representation.ρ.comp e.toMonoidHom))

@[simp]
private theorem comapIrreducibleTypeF8_apply
    {A B : Type u} {k : Type v}
    [Group A] [Group B] [Fintype A] [Fintype B]
    [Field k] [IsAlgClosed k] [CharZero k]
    (e : A ≃* B) (chi : IrreducibleCharacter B k) (a : A) :
    comapIrreducibleTypeF8 e chi a = chi (e a) := by
  letI : CategoryTheory.Simple chi.representation :=
    chi.representation_simple
  change chi.representation.character (e a) = chi (e a)
  exact IrreducibleCharacter.representation_character chi (e a)

/-! ## The all-type-one alternative -/

/-- Peterfalvi (8.8)(a): every maximal subgroup has FT type one. -/
def all_FTtype1 : Prop :=
  ∀ M : Subgroup G,
    M ∈ minSimple_max_groups (G := G) → FTtype M = 1

/-! ## Transport between type-F complements -/

/-- The remark after Peterfalvi Definition (8.1): any complement of the
Fitting core in a type-F subgroup is itself a type-F complement. -/
theorem compl_of_typeF
    (M U V : Subgroup G)
    (hdecomp : IsInternalSemidirectProductIn (Fitting_core M) U M)
    (hV : of_typeF M V) :
    of_typeF M U := by
  let F := Fitting_core M
  let A : Subgroup M := V.subgroupOf M
  let B : Subgroup M := U.subgroupOf M
  let FM : Subgroup M := F.subgroupOf M
  have hsol : IsSolvable M := by
    have hFproper : F < ⊤ :=
      (mFT_sol_proper F).2 inferInstance
    have hnormProper : Subgroup.normalizer (F : Set G) < ⊤ :=
      mFT_norm_proper F hV.1 hFproper
    have hMnorm : M ≤ Subgroup.normalizer (F : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (Fcore_sub M)).1
        (Fcore_normal M)
    exact mFT_sol (hMnorm.trans_lt hnormProper)
  have hcopF : (Nat.card FM).Coprime FM.index := by
    simpa [FM, F] using (Fcore_Hall M).coprime_card_index
  have hcardA : Nat.card A = FM.index := by
    simpa [A, FM, F] using
      hV.2.2.1.2.2.2.symm.index_eq_card.symm
  have hindexA : A.index = Nat.card FM := by
    simpa [A, FM, F] using
      hV.2.2.1.2.2.2.index_eq_card
  have hcopA : (Nat.card A).Coprime A.index := by
    rw [hcardA, hindexA]
    exact hcopF.symm
  let pi := primeSupport (Nat.card A)
  have hHallA : IsHall pi A := isHall_primeSupport A hcopA
  have hcardB : Nat.card B = Nat.card A := by
    calc
      Nat.card B = FM.index := by
        simpa [B, FM, F] using
          hdecomp.2.2.2.symm.index_eq_card.symm
      _ = Nat.card A := hcardA.symm
  have hindexB : B.index = A.index := by
    calc
      B.index = Nat.card FM := by
        simpa [B, FM, F] using hdecomp.2.2.2.index_eq_card
      _ = A.index := hindexA.symm
  have hHallB : IsHall pi B := by
    constructor
    · simpa [hcardB] using hHallA.isPiNumber_card
    · simpa [hindexB] using hHallA.isPiNumber_index
  obtain ⟨x, hx⟩ :=
    exists_map_conj_eq_of_isHall_of_isSolvable hsol hHallA hHallB
  have hVU : conjugateSubgroup8 V (x : G) = U :=
    FTContextInternal.ambient_conjugate_eq_of_subgroupOf8
      hV.2.2.1.2.1 hdecomp.2.1 x hx
  have hMfix : conjugateSubgroup8 M (x : G) = M :=
    FTContextInternal.conjugateSubgroup8_eq_self_of_mem_normalizer
      (Subgroup.le_normalizer x.property)
  have hmap := FTContextInternal.ofTypeF_map_mulEquiv8 hV
    (MulAut.conj (x : G))
  change of_typeF (conjugateSubgroup8 M (x : G))
    (conjugateSubgroup8 V (x : G)) at hmap
  rwa [hMfix, hVU] at hmap

/-! ## Frobenius and coprime-action ingredients -/

/-- Every Sylow subgroup of an odd Frobenius complement is cyclic when the
nontrivial kernel is solvable. -/
private theorem zGroup8_of_frobenius
    {H U M : Subgroup G}
    (hHsol : IsSolvable H) (hHne : H ≠ ⊥)
    (hFrob : IsFrobeniusIn H U M) :
    IsZGroup8 U := by
  intro p hp P
  let A : Subgroup G := (P : Subgroup U).map U.subtype
  have hAU : A ≤ U := Subgroup.map_subtype_le _
  have hAp : IsPGroup p A := P.isPGroup'.map U.subtype
  have hAodd : Odd (Nat.card A) := mFT_odd A
  have hJnorm : H ⊔ U ≤ Subgroup.normalizer (H : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hFrob.2.1.1).1
      hFrob.2.1.2.2.1
  have hAnorm : A ≤ Subgroup.normalizer (H : Set G) :=
    (hAU.trans hFrob.2.1.2.1).trans hJnorm
  have hreg : IsSemiregularConjugation H A := by
    intro a ha h hhfix
    let aU : U := ⟨(a : G), hAU a.property⟩
    let aJ : U.subgroupOf (H ⊔ U) :=
      ⟨⟨(a : G), hFrob.2.1.2.1 aU.property⟩, aU.property⟩
    let hJ : H.subgroupOf (H ⊔ U) :=
      ⟨⟨(h : G), hFrob.2.1.1 h.property⟩, h.property⟩
    have haJ : aJ ≠ 1 := by
      intro haOne
      apply ha
      apply Subtype.ext
      exact congrArg
        (fun z : U.subgroupOf (H ⊔ U) ↦ (((z : ↑(H ⊔ U)) : G)))
        haOne
    have hfixJ :
        (aJ : ↑(H ⊔ U)) * (hJ : ↑(H ⊔ U)) *
            (aJ : ↑(H ⊔ U))⁻¹ =
          (hJ : ↑(H ⊔ U)) := by
      apply Subtype.ext
      exact hhfix
    have hOne := hFrob.2.2.fixedPointFree aJ haJ hJ hfixJ
    apply Subtype.ext
    exact congrArg
      (fun z : H.subgroupOf (H ⊔ U) ↦ (((z : ↑(H ⊔ U)) : G)))
      hOne
  have hAcyclic : IsCyclic A :=
    quotient_regular_qgroup_isCyclic_12_12 hAp hAodd hAnorm
      hHsol hHne hreg
  let eP : (P : Subgroup U) ≃* A :=
    Subgroup.equivMapOfInjective (P : Subgroup U) U.subtype
      U.subtype_injective
  exact eP.isCyclic.mpr hAcyclic

/-- Coprime conjugation fixes a representative of every invariant conjugacy
class of a normal subgroup. -/
private theorem exists_fixed_rep_of_coprime_conjugation
    {A : Type u} [Group A] [Finite A]
    (H : Subgroup A) [H.Normal]
    (a : A) (hcop : Nat.Coprime (Nat.card H) (orderOf a))
    (C : ConjClasses H)
    (hC : PrimeTIInductionCasesAux.conjClassesEquiv
      (MulAut.conjNormal a) C = C) :
    ∃ x : H, ConjClasses.mk x = C ∧
      MulAut.conjNormal a x = x := by
  obtain ⟨r, hrC⟩ := ConjClasses.exists_rep C
  have hclass :
      ConjClasses.mk (MulAut.conjNormal a r) = ConjClasses.mk r := by
    change PrimeTIInductionCasesAux.conjClassesEquiv
      (MulAut.conjNormal a) (ConjClasses.mk r) = ConjClasses.mk r
    rw [hrC, hC]
  obtain ⟨h, hh⟩ :=
    isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp hclass)
  let t : A := (h : A) * a
  have htfix : t * (r : A) * t⁻¹ = (r : A) := by
    have hhA := congrArg (fun z : H ↦ (z : A)) hh
    simpa [t, MulAut.conjNormal_apply, mul_assoc] using hhA
  have htcomm : Commute t (r : A) :=
    mul_inv_eq_iff_eq_mul.mp htfix
  have haNorm : a ∈ Subgroup.normalizer (H : Set A) := by
    rw [H.normalizer_eq_top]
    exact Subgroup.mem_top a
  let conjugationAction := subgroupConjugationActionOnAmbient H
  letI : SMul H A := conjugationAction.toSMul
  letI : MulAction H A := conjugationAction.toMulAction
  letI : MulAction H (Set A) := Set.mulActionSet
  let D := centralizerWithin H (Subgroup.zpowers a)
  have hpartition := partition_cent_rcoset H a haNorm hcop
  have htCoset : t ∈ (H : Set A) * ({a} : Set A) :=
    ⟨(h : A), h.property, a, by simp, rfl⟩
  have htOrbit : t ∈
      ⋃₀ (MulAction.orbit H ((D : Set A) * ({a} : Set A))) := by
    rw [hpartition.1.1]
    exact htCoset
  rcases Set.mem_sUnion.mp htOrbit with ⟨S, hS, htS⟩
  rcases hS with ⟨y, rfl⟩
  rcases Set.mem_smul_set.mp htS with ⟨z, hz, hzt⟩
  rcases Set.mem_mul.mp hz with ⟨c, hc, b, hb, hcb⟩
  have hbEq : b = a := Set.mem_singleton_iff.mp hb
  subst b
  have hyzt : (y : A) * z * (y : A)⁻¹ = t := hzt
  let q : H := y⁻¹ * r * y
  have hyq : MulAut.conj (y : A) (q : A) = (r : A) := by
    change (y : A) * ((y : A)⁻¹ * (r : A) * (y : A)) *
      (y : A)⁻¹ = (r : A)
    group
  have hzq : Commute z (q : A) := by
    apply (MulAut.conj (y : A)).injective
    rw [map_mul, map_mul, hyq]
    change (y : A) * z * (y : A)⁻¹ * (r : A) =
      (r : A) * ((y : A) * z * (y : A)⁻¹)
    rw [hyzt, htcomm.eq]
  have hca : Commute c a :=
    (hc.2 a (Subgroup.mem_zpowers a)).symm
  have hcOrder : orderOf c ∣ Nat.card H :=
    H.orderOf_dvd_natCard hc.1
  have hcopca : (orderOf c).Coprime (orderOf a) :=
    hcop.coprime_dvd_left hcOrder
  let n : ℕ := Nat.chineseRemainder hcopca 0 1
  have hnc : n ≡ 0 [MOD orderOf c] :=
    (Nat.chineseRemainder hcopca 0 1).property.1
  have hna : n ≡ 1 [MOD orderOf a] :=
    (Nat.chineseRemainder hcopca 0 1).property.2
  have hcpow : c ^ n = 1 := pow_eq_one_iff_modEq.mpr hnc
  have hapow : a ^ n = a := by
    simpa using (pow_eq_pow_iff_modEq.mpr hna : a ^ n = a ^ 1)
  have hzpow : z ^ n = a := by
    rw [← hcb, hca.mul_pow, hcpow, hapow, one_mul]
  have haq : Commute a (q : A) := by
    simpa only [hzpow] using hzq.pow_left n
  have hqfix : MulAut.conjNormal a q = q := by
    apply Subtype.ext
    change a * (q : A) * a⁻¹ = (q : A)
    rw [haq.eq]
    simp
  refine ⟨q, ?_, hqfix⟩
  calc
    ConjClasses.mk q = ConjClasses.mk r := by
      apply ConjClasses.mk_eq_mk_iff_isConj.mpr
      apply isConj_iff.mpr
      refine ⟨y, ?_⟩
      apply Subtype.ext
      exact hyq
    _ = C := hrC

/-! ## The type-F context -/

/-- Peterfalvi (8.2): cardinality, Frobenius, and inertia consequences of
the type-F hypothesis. -/
theorem typeF_context
    (M U : Subgroup G) (hTypeF : of_typeF M U) :
    TypeFContext M U := by
  classical
  let F := Fitting_core M
  refine
    { complement_card := ?_
      frobenius_iff_zgroup := ?_
      inertia_le := ?_ }
  · intro U₀ hU₀
    have hFrob₀ : IsFrobeniusIn F U₀ (F ⊔ U₀) :=
      ⟨rfl, hU₀.2.2.1, hU₀.2.2.2⟩
    have hZU₀ : IsZGroup8 U₀ :=
      zGroup8_of_frobenius
        (inferInstance : IsSolvable F) hTypeF.1 hFrob₀
    letI : IsZGroup U₀ :=
      ⟨fun p hp P ↦ by
        letI : Fact p.Prime := ⟨hp⟩
        exact hZU₀ p P⟩
    calc
      Nat.card U₀ = Monoid.exponent U₀ :=
        (IsZGroup.exponent_eq_card U₀).symm
      _ = Monoid.exponent U := hU₀.2.1
  · constructor
    · intro hFrob
      exact zGroup8_of_frobenius
        (inferInstance : IsSolvable F) hTypeF.1 hFrob
    · intro hZU
      obtain ⟨U₀, hU₀⟩ := hTypeF.2.2.2.2
      letI : IsZGroup U :=
        ⟨fun p hp P ↦ by
          letI : Fact p.Prime := ⟨hp⟩
          exact hZU p P⟩
      have hcard : Nat.card U₀ = Nat.card U := by
        calc
          Nat.card U₀ = Monoid.exponent U := by
            have hFrob₀ : IsFrobeniusIn F U₀ (F ⊔ U₀) :=
              ⟨rfl, hU₀.2.2.1, hU₀.2.2.2⟩
            have hZU₀ : IsZGroup8 U₀ :=
              zGroup8_of_frobenius
                (inferInstance : IsSolvable F) hTypeF.1 hFrob₀
            letI : IsZGroup U₀ :=
              ⟨fun p hp P ↦ by
                letI : Fact p.Prime := ⟨hp⟩
                exact hZU₀ p P⟩
            exact (IsZGroup.exponent_eq_card U₀).symm.trans
              hU₀.2.1
          _ = Nat.card U := IsZGroup.exponent_eq_card U
      have hU₀eq : U₀ = U :=
        Subgroup.eq_of_le_of_card_ge hU₀.1 hcard.ge
      subst U₀
      exact ⟨FTContextInternal.semidirect_sup_eq8 hTypeF.2.2.1,
        hU₀.2.2.1, hU₀.2.2.2⟩
  · intro U₁ i hU₁ hi
    let H : Subgroup M := (Fitting_core M).subgroupOf M
    letI : H.Normal := by
      dsimp only [H]
      infer_instance
    let eH : H ≃* Fitting_core M :=
      Subgroup.subgroupOfEquivOfLe (Fcore_sub M)
    letI : Fintype H := Fintype.ofFinite H
    letI : Fintype (Fitting_core M) := Fintype.ofFinite _
    let iH : IrreducibleCharacter H ℂ :=
      comapIrreducibleTypeF8 eH i
    let jH : ClassFunction H ℂ :=
      ⟨fun h ↦ i (eH h), by
        intro x h
        change i (eH (x * h * x⁻¹)) = i (eH h)
        simpa only [map_mul, map_inv] using
          ClassFunction.conj_apply
            (i : ClassFunction (Fitting_core M) ℂ) (eH x) (eH h)⟩
    have hiHj : (iH : ClassFunction H ℂ) = jH := by
      ext h
      exact comapIrreducibleTypeF8_apply eH i h
    change ((U.subgroupOf M) ⊓ ClassFunction.inertia H jH).map
      M.subtype ≤ U₁
    rw [← hiHj]
    intro g hg
    rcases hg with ⟨gM, hgM, rfl⟩
    by_contra hgU₁
    have hcopHU : Nat.Coprime (Nat.card H)
        (Nat.card (U.subgroupOf M)) := by
      rw [← hTypeF.2.2.1.2.2.2.symm.index_eq_card]
      simpa only [H] using (Fcore_Hall M).coprime_card_index
    have hcopHg : Nat.Coprime (Nat.card H) (orderOf gM) :=
      hcopHU.coprime_dvd_right
        ((U.subgroupOf M).orderOf_dvd_natCard hgM.1)
    letI : Fintype M := Fintype.ofFinite M
    let rowPerm : Equiv.Perm (IrreducibleCharacter H ℂ) :=
      FrobeniusKernelInductionAux.irreducibleConjPerm
        (H := H) (k := ℂ) gM
    let classPerm : Equiv.Perm (ConjClasses H) :=
      FrobeniusKernelInductionAux.conjugacyClassPerm
        (H := H) gM
    let FixedIrr := Function.fixedPoints rowPerm
    let FixedClass := Function.fixedPoints classPerm
    have hbrauer : Nat.card FixedIrr = Nat.card FixedClass :=
      FrobeniusKernelInductionAux.brauerPermutationCardinality_inner
        (H := H) (k := ℂ) gM
    have fixedClass_has_rep (C : FixedClass) :
        ∃ x : H, ConjClasses.mk x = C.1 ∧
          MulAut.conjNormal gM x = x := by
      apply exists_fixed_rep_of_coprime_conjugation H gM hcopHg C.1
      have hCfixed := C.property
      change classPerm C.1 = C.1 at hCfixed
      simpa only [classPerm,
        FrobeniusKernelInductionAux.conjugacyClassPerm] using hCfixed
    let fixedClassRep (C : FixedClass) : H :=
      Classical.choose (fixedClass_has_rep C)
    have fixedClassRep_spec (C : FixedClass) :
        ConjClasses.mk (fixedClassRep C) = C.1 ∧
          MulAut.conjNormal gM (fixedClassRep C) = fixedClassRep C :=
      Classical.choose_spec (fixedClass_has_rep C)
    have fixedClassRep_eq_one (C : FixedClass) :
        fixedClassRep C = 1 := by
      by_contra hxOne
      have hxGne : (((fixedClassRep C : H) : M) : G) ≠ 1 := by
        intro hxG
        apply hxOne
        apply Subtype.ext
        apply Subtype.ext
        exact hxG
      have hfixG :
          (gM : G) * (((fixedClassRep C : H) : M) : G) * (gM : G)⁻¹ =
            (((fixedClassRep C : H) : M) : G) := by
        have hfixM := congrArg (fun x : H ↦ (x : M))
          (fixedClassRep_spec C).2
        change M.subtype gM *
            M.subtype ((fixedClassRep C : H) : M) *
            (M.subtype gM)⁻¹ =
          M.subtype ((fixedClassRep C : H) : M)
        calc
          M.subtype gM * M.subtype ((fixedClassRep C : H) : M) *
                (M.subtype gM)⁻¹ =
              M.subtype
                (gM * ((fixedClassRep C : H) : M) * gM⁻¹) := by
            simp only [map_mul, map_inv]
          _ = M.subtype ((fixedClassRep C : H) : M) :=
            congrArg M.subtype hfixM
      have hgcommx : Commute (gM : G)
          (((fixedClassRep C : H) : M) : G) :=
        mul_inv_eq_iff_eq_mul.mp hfixG
      have hgCent : (gM : G) ∈ elementCentralizerWithin U
          (((fixedClassRep C : H) : M) : G) := by
        refine ⟨hgM.1, ?_⟩
        intro z hz
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
        exact (hgcommx.symm.zpow_left n).eq
      exact hgU₁
        ((hU₁.2.2.2 (((fixedClassRep C : H) : M) : G)
          ⟨(fixedClassRep C).property, hxGne⟩) hgCent)
    let fixedOne : FixedClass :=
      ⟨ConjClasses.mk (1 : H), by
        change classPerm (ConjClasses.mk (1 : H)) =
          ConjClasses.mk (1 : H)
        change ConjClasses.mk (MulAut.conjNormal gM (1 : H)) =
          ConjClasses.mk (1 : H)
        simp⟩
    letI : Subsingleton FixedClass :=
      ⟨by
        intro C D
        apply Subtype.ext
        calc
          C.1 = ConjClasses.mk (fixedClassRep C) :=
            (fixedClassRep_spec C).1.symm
          _ = ConjClasses.mk (1 : H) :=
            congrArg ConjClasses.mk (fixedClassRep_eq_one C)
          _ = ConjClasses.mk (fixedClassRep D) :=
            congrArg ConjClasses.mk (fixedClassRep_eq_one D).symm
          _ = D.1 := (fixedClassRep_spec D).1⟩
    letI : Nonempty FixedClass := ⟨fixedOne⟩
    have hcardFixedClass : Nat.card FixedClass = 1 := Nat.card_unique
    have hcardFixedIrr : Nat.card FixedIrr = 1 :=
      hbrauer.trans hcardFixedClass
    letI : Subsingleton FixedIrr :=
      (Nat.card_eq_one_iff_unique.mp hcardFixedIrr).1
    have hgiH : iH.normalConjugate H gM = iH := by
      apply Subtype.ext
      exact (ClassFunction.mem_inertia_iff H
        (iH : ClassFunction H ℂ) gM).mp hgM.2
    let iFixed : FixedIrr :=
      ⟨iH, by
        change iH.normalConjugate H gM = iH
        exact hgiH⟩
    let trivialFixed : FixedIrr :=
      ⟨IrreducibleCharacter.trivial, by
        change IrreducibleCharacter.trivial.normalConjugate H gM =
          IrreducibleCharacter.trivial
        apply IrreducibleCharacter.ext
        intro x
        change (IrreducibleCharacter.trivial :
          IrreducibleCharacter H ℂ) ((MulAut.conjNormal gM).symm x) =
            IrreducibleCharacter.trivial x
        simp⟩
    have hiHtriv : iH = IrreducibleCharacter.trivial :=
      congrArg (fun q : FixedIrr ↦ q.1)
        (Subsingleton.elim iFixed trivialFixed)
    apply hi
    apply IrreducibleCharacter.ext
    intro x
    have hx := congrArg
      (fun chi : IrreducibleCharacter H ℂ ↦ chi (eH.symm x))
      hiHtriv
    simpa [iH] using hx

end

end Submission.OddOrder.PF
