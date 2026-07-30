import Mathlib.GroupTheory.SpecificGroups.ZGroup
import Mathlib.GroupTheory.NoncommPiCoprod
import Submission.OddOrder.BG.AppendixC.ElementaryAbelianDecomposition
import Submission.OddOrder.BG.Section01.PLengthOneFunctorial
import Submission.OddOrder.BG.Section03.OddPrimeSemidirectTheorem
import Submission.OddOrder.BG.Section03.FrobeniusPrimeFixedPoint
import Submission.OddOrder.BG.Section03.SemidirectProperKernel
import Submission.OddOrder.BG.Section04.RankTwoAutomorphismDerived
import Submission.OddOrder.BG.Section06.CoprimeDerivedSemidirect
import Submission.OddOrder.MathlibSupport.AmbientFitting
import Submission.OddOrder.MathlibSupport.Centralizer
import Submission.OddOrder.MathlibSupport.CharacteristicPerfectCoprimePGroup
import Submission.OddOrder.MathlibSupport.CharacteristicUnderNormalizer
import Submission.OddOrder.MathlibSupport.ComplementQuotient
import Submission.OddOrder.MathlibSupport.CoprimeAbelianCocyclicCentralizerGeneration
import Submission.OddOrder.MathlibSupport.CoprimeCommutatorIdempotent
import Submission.OddOrder.MathlibSupport.CoprimeElementaryAbelianComplement
import Submission.OddOrder.MathlibSupport.CoprimeInvariantHall
import Submission.OddOrder.MathlibSupport.CoprimeSolvableCentralProduct
import Submission.OddOrder.MathlibSupport.CoprimeSolvableInvariantSylowConjugacy
import Submission.OddOrder.MathlibSupport.CoprimeSolvableInvariantSylowExtension
import Submission.OddOrder.MathlibSupport.CyclicNormalizerCommutator
import Submission.OddOrder.MathlibSupport.ElementaryAbelian
import Submission.OddOrder.MathlibSupport.ElementaryAbelianSup
import Submission.OddOrder.MathlibSupport.FittingPCore
import Submission.OddOrder.MathlibSupport.FrattiniQuotientAutomorphism
import Submission.OddOrder.MathlibSupport.NilpotentPrimeCores
import Submission.OddOrder.MathlibSupport.OddPGroupOmegaAction
import Submission.OddOrder.MathlibSupport.OmegaOneCyclicMaximal
import Submission.OddOrder.MathlibSupport.OmegaOneSmallNilpotency
import Submission.OddOrder.MathlibSupport.PCoreFunctorial
import Submission.OddOrder.MathlibSupport.PCoreSelfQuotient
import Submission.OddOrder.MathlibSupport.PPrimeCoreFunctorial
import Submission.OddOrder.MathlibSupport.PPrimeCoreQuotient
import Submission.OddOrder.MathlibSupport.PPrimePCoreThirdIsomorphism
import Submission.OddOrder.MathlibSupport.PSubgroupAbsentPrime
import Submission.OddOrder.MathlibSupport.PrimeIndex
import Submission.OddOrder.MathlibSupport.RepresentationSubgroupRestriction
import Submission.OddOrder.MathlibSupport.SolvableComplementActorConjugacy
import Submission.OddOrder.MathlibSupport.SubgroupConjugationFactor
import Submission.OddOrder.MathlibSupport.SubgroupCardinality

/-!
# The odd semidirect-product Z-group p-length theorem

This file ports `BGsection3.v: odd_sdprod_Zgroup_cent_prime_plength1`,
Bender--Glauberman Theorem 3.6.  We also record the isomorphism transport
used by the Section 10 application, where the semidirect product is formed
inside a maximal subgroup but its factors are named in the original ambient
group.
-/

namespace Submission.OddOrder.BG.Section03

open Submission.OddOrder.MathlibSupport
open Submission.OddOrder.BG.Section01
open scoped BigOperators IsMulCommutative Pointwise commutatorElement

noncomputable section

universe u v

section EquivalenceTransport

variable {A : Type u} {B : Type v} [Group A] [Group B]

/-- The equivalence induced on the quotients by the `p'`-cores. -/
private def pPrimeCoreQuotientMulEquiv
    [Finite A] [Finite B] (p : ℕ) (e : A ≃* B) :
    (A ⧸ pPrimeCore p A) ≃* (B ⧸ pPrimeCore p B) := by
  let f : A →* B ⧸ pPrimeCore p B :=
    (QuotientGroup.mk' (pPrimeCore p B)).comp e.toMonoidHom
  have hf : Function.Surjective f := by
    intro z
    obtain ⟨b, rfl⟩ :=
      QuotientGroup.mk'_surjective (pPrimeCore p B) z
    exact ⟨e.symm b, by simp [f]⟩
  have hker : pPrimeCore p A = f.ker := by
    ext x
    change x ∈ pPrimeCore p A ↔
      QuotientGroup.mk' (pPrimeCore p B) (e x) = 1
    constructor
    · intro hx
      apply (QuotientGroup.eq_one_iff (e x)).mpr
      rw [← map_pPrimeCore_eq_mulEquiv (p := p) e]
      exact Subgroup.mem_map_of_mem e.toMonoidHom hx
    · intro hx
      have hex : e x ∈ pPrimeCore p B :=
        (QuotientGroup.eq_one_iff (e x)).mp hx
      rw [← map_pPrimeCore_eq_mulEquiv (p := p) e] at hex
      exact (Subgroup.mem_map_iff_mem e.injective).mp hex
  exact QuotientGroup.liftEquiv (pPrimeCore p A) hf hker

/-- A group equivalence carries the `p`-core onto the `p`-core. -/
private theorem map_pCore_eq_mulEquiv
    {p : ℕ} (e : A ≃* B) :
    (pCore p A).map e.toMonoidHom = pCore p B := by
  apply le_antisymm
  · exact map_pCore_le_of_surjective e.toMonoidHom e.surjective
  · rw [← Subgroup.map_le_map_iff_of_injective
        (f := e.symm.toMonoidHom) e.symm.injective]
    have h := map_pCore_le_of_surjective
      (p := p) e.symm.toMonoidHom e.symm.surjective
    simpa [Subgroup.map_map] using h

/-- Transport `IsPLengthOne` along an isomorphism of finite groups. -/
theorem isPLengthOne_of_mulEquiv
    [Finite A] [Finite B] {p : ℕ} [Fact p.Prime]
    (hA : IsPLengthOne p A) (e : A ≃* B) :
    IsPLengthOne p B := by
  let qe := pPrimeCoreQuotientMulEquiv p e
  obtain ⟨P, hP⟩ := hA
  let Q : Sylow p (B ⧸ pPrimeCore p B) :=
    P.mapSurjective (f := qe.toMonoidHom) qe.surjective
  refine ⟨Q, ?_⟩
  calc
    (Q : Subgroup (B ⧸ pPrimeCore p B)) =
        (P : Subgroup (A ⧸ pPrimeCore p A)).map
          qe.toMonoidHom := rfl
    _ = (pCore p (A ⧸ pPrimeCore p A)).map
          qe.toMonoidHom := by rw [hP]
    _ = pCore p (B ⧸ pPrimeCore p B) :=
      map_pCore_eq_mulEquiv qe

/-- `IsPLengthOne` is invariant under isomorphism of finite groups. -/
theorem isPLengthOne_mulEquiv_iff
    [Finite A] [Finite B] {p : ℕ} [Fact p.Prime]
    (e : A ≃* B) :
    IsPLengthOne p A ↔ IsPLengthOne p B := by
  exact ⟨fun hA ↦ isPLengthOne_of_mulEquiv hA e,
    fun hB ↦ isPLengthOne_of_mulEquiv hB e.symm⟩

variable {G : Type*} [Group G]

/-- Forming a commutator inside an intermediate subgroup gives the
subgroup-of form of the ambient commutator. -/
theorem subgroupOf_commutator_eq
    {J H R : Subgroup G} (hHJ : H ≤ J) (hRJ : R ≤ J) :
    (⁅H, R⁆ : Subgroup G).subgroupOf J =
      ⁅H.subgroupOf J, R.subgroupOf J⁆ := by
  apply Subgroup.map_injective J.subtype_injective
  rw [Subgroup.map_subgroupOf_eq_of_le
    ((Subgroup.commutator_le_sup H R).trans (sup_le hHJ hRJ))]
  exact
    (map_subgroupOf_commutator
      (J := J) (H := R) (R := H) hRJ hHJ).symm

end EquivalenceTransport

section PLengthLifting

variable {A : Type u} [Group A] [Finite A]
variable {p : ℕ} [Fact p.Prime]

/-- Cardinal form of the defining Sylow condition for `IsPLengthOne`. -/
private theorem isPLengthOne_iff_not_dvd_finalQuotientCard :
    IsPLengthOne p A ↔
      ¬ p ∣ Nat.card (A ⧸ pPrimePCore p A) := by
  have hcard :
      Nat.card ((A ⧸ pPrimeCore p A) ⧸
          pCore p (A ⧸ pPrimeCore p A)) =
        Nat.card (A ⧸ pPrimePCore p A) :=
    Nat.card_congr (pPrimePCoreQuotientEquiv p A).toEquiv
  constructor
  · rintro ⟨P, hP⟩
    have hnot : ¬ p ∣
        (pCore p (A ⧸ pPrimeCore p A)).index := by
      rw [← hP]
      exact P.not_dvd_index
    rw [Subgroup.index_eq_card, hcard] at hnot
    exact hnot
  · intro hnot
    have hindex : ¬ p ∣
        (pCore p (A ⧸ pPrimeCore p A)).index := by
      rw [Subgroup.index_eq_card, hcard]
      exact hnot
    let P : Sylow p (A ⧸ pPrimeCore p A) :=
      pCore_isPGroup.toSylow hindex
    exact ⟨P, rfl⟩

private theorem isPLengthOne_of_subsingleton [Subsingleton A] :
    IsPLengthOne p A := by
  apply isPLengthOne_iff_not_dvd_finalQuotientCard.mpr
  simpa using (Fact.out : p.Prime).not_dvd_one

/-- Lifting p-length one across the `p'`-core quotient (MathComp's
`p'quo_plength1`, in the direction used in Theorem 3.6). -/
private theorem isPLengthOne_of_quotient_pPrimeCore
    (hQ : IsPLengthOne p (A ⧸ pPrimeCore p A)) :
    IsPLengthOne p A := by
  let Q := A ⧸ pPrimeCore p A
  have hOQ : pPrimeCore p Q = ⊥ := by
    simpa [Q] using
      (pPrimeCore_quotient_self_eq_bot (G := A) (p := p))
  have hKQ : pPrimePCore p Q = pCore p Q :=
    pPrimePCore_eq_pCore_of_pPrimeCore_eq_bot hOQ
  have hnotQ : ¬ p ∣ Nat.card (Q ⧸ pPrimePCore p Q) :=
    isPLengthOne_iff_not_dvd_finalQuotientCard.mp hQ
  apply isPLengthOne_iff_not_dvd_finalQuotientCard.mpr
  intro hp
  apply hnotQ
  rw [hKQ]
  rw [Nat.card_congr (pPrimePCoreQuotientEquiv p A).toEquiv]
  exact hp

/-- In the special form used in the Frattini reduction, `p`-length one
lifts across a normal `p`-subgroup.  The additional core-free hypothesis on
the quotient turns the two final quotients into an instance of the third
isomorphism theorem. -/
private theorem isPLengthOne_of_isPGroup_quotient
    (N : Subgroup A) [N.Normal]
    (hNp : IsPGroup p N)
    (hOQ : pPrimeCore p (A ⧸ N) = ⊥)
    (hQ : IsPLengthOne p (A ⧸ N)) :
    IsPLengthOne p A := by
  let q : A →* A ⧸ N := QuotientGroup.mk' N
  have hOmap : (pPrimeCore p A).map q = ⊥ := by
    apply le_antisymm
    · have hprime : IsPPrimeSubgroup p ((pPrimeCore p A).map q) := by
        rw [IsPPrimeSubgroup]
        exact (pPrimeCore_coprime_card (G := A) (p := p)).coprime_dvd_right
          (Subgroup.card_map_dvd (pPrimeCore p A) q)
      have hnormal : ((pPrimeCore p A).map q).Normal :=
        Subgroup.Normal.map (by infer_instance) q
          (QuotientGroup.mk'_surjective N)
      have hle := le_pPrimeCore hprime hnormal
      rwa [hOQ] at hle
    · exact bot_le
  have hOleN : pPrimeCore p A ≤ N := by
    rw [← QuotientGroup.ker_mk' N]
    exact (Subgroup.map_eq_bot_iff (pPrimeCore p A)).mp hOmap
  have hOA : pPrimeCore p A = ⊥ := by
    calc
      pPrimeCore p A = N ⊓ pPrimeCore p A :=
        (inf_eq_right.mpr hOleN).symm
      _ = ⊥ := disjoint_iff.mp
        (disjoint_pPrimeCore_of_isPGroup hNp)
  have hNcore : N ≤ pCore p A := le_pCore hNp (by infer_instance)
  let e : ((A ⧸ N) ⧸ pCore p (A ⧸ N)) ≃*
      (A ⧸ pCore p A) :=
    (QuotientGroup.quotientMulEquivOfEq
        (map_pCore_quotient_eq hNp).symm).trans
      (QuotientGroup.quotientQuotientEquivQuotient
        N (pCore p A) hNcore)
  have hKA : pPrimePCore p A = pCore p A :=
    pPrimePCore_eq_pCore_of_pPrimeCore_eq_bot hOA
  have hKQ : pPrimePCore p (A ⧸ N) = pCore p (A ⧸ N) :=
    pPrimePCore_eq_pCore_of_pPrimeCore_eq_bot hOQ
  have hnotQ : ¬ p ∣ Nat.card ((A ⧸ N) ⧸ pPrimePCore p (A ⧸ N)) :=
    isPLengthOne_iff_not_dvd_finalQuotientCard.mp hQ
  apply isPLengthOne_iff_not_dvd_finalQuotientCard.mpr
  rw [hKA]
  intro hp
  apply hnotQ
  rw [hKQ, Nat.card_congr e.toEquiv]
  exact hp

/-- The `p'`-core of a direct product is the product of the two cores. -/
private theorem pPrimeCore_prod
    {B : Type v} [Group B] [Finite B] :
    pPrimeCore p (A × B) =
      (pPrimeCore p A).prod (pPrimeCore p B) := by
  apply le_antisymm
  · rw [Subgroup.le_prod_iff]
    constructor
    · apply le_pPrimeCore
      · rw [IsPPrimeSubgroup]
        exact (pPrimeCore_coprime_card (G := A × B) (p := p)).coprime_dvd_right
          ((pPrimeCore p (A × B)).card_map_dvd (MonoidHom.fst A B))
      · exact Subgroup.Normal.map (by infer_instance) _ Prod.fst_surjective
    · apply le_pPrimeCore
      · rw [IsPPrimeSubgroup]
        exact (pPrimeCore_coprime_card (G := A × B) (p := p)).coprime_dvd_right
          ((pPrimeCore p (A × B)).card_map_dvd (MonoidHom.snd A B))
      · exact Subgroup.Normal.map (by infer_instance) _ Prod.snd_surjective
  · apply le_pPrimeCore
    · rw [IsPPrimeSubgroup,
          Nat.card_congr
            (Subgroup.prodEquiv (pPrimeCore p A) (pPrimeCore p B)).toEquiv,
          Nat.card_prod, Nat.coprime_mul_iff_right]
      exact ⟨pPrimeCore_coprime_card, pPrimeCore_coprime_card⟩
    · infer_instance

/-- Being a `p`-element is componentwise in a direct product. -/
private theorem isPElement_prod_iff
    {B : Type v} [Group B] (x : A) (y : B) :
    IsPElement p (x, y) ↔ IsPElement p x ∧ IsPElement p y := by
  constructor
  · intro h
    exact ⟨h.map (MonoidHom.fst A B), h.map (MonoidHom.snd A B)⟩
  · rintro ⟨⟨m, hm⟩, ⟨n, hn⟩⟩
    refine ⟨m + n, ?_⟩
    apply Prod.ext
    · change x ^ p ^ (m + n) = 1
      rw [pow_add, pow_mul, hm, one_pow]
    · change y ^ p ^ (m + n) = 1
      rw [pow_add, mul_comm, pow_mul, hn, one_pow]

/-- The subgroup generated by `p`-elements commutes with direct products. -/
private theorem pElementGenerated_prod
    {B : Type v} [Group B] :
    pElementGenerated p (A × B) =
      (pElementGenerated p A).prod (pElementGenerated p B) := by
  rw [pElementGenerated, pElementGenerated, pElementGenerated]
  have hs : {z : A × B | IsPElement p z} =
      {x : A | IsPElement p x} ×ˢ {y : B | IsPElement p y} := by
    ext z
    exact isPElement_prod_iff z.1 z.2
  rw [hs, Subgroup.closure_prod IsPElement.one IsPElement.one]

/-- Hall `p'`-cores transport through a group equivalence. -/
private theorem pPrimeCore_isPrimeComplement_mulEquiv
    {B : Type v} [Group B] [Finite B]
    (e : A ≃* B)
    (h : IsPrimeComplement p (pPrimeCore p A)) :
    IsPrimeComplement p (pPrimeCore p B) := by
  rw [← map_pPrimeCore_eq_mulEquiv (p := p) e]
  constructor
  · rw [Subgroup.card_map_of_injective e.injective]
    exact h.1
  · obtain ⟨n, hn⟩ := h.2
    exact ⟨n,
      (Subgroup.index_map_equiv (pPrimeCore p A) e).trans hn⟩

/-- Products of Hall `p'`-subgroups are Hall in the direct product. -/
private theorem isPrimeComplement_prod
    {B : Type v} [Group B] [Finite B]
    {HA : Subgroup A} {HB : Subgroup B}
    (hA : IsPrimeComplement p HA)
    (hB : IsPrimeComplement p HB) :
    IsPrimeComplement p (HA.prod HB) := by
  constructor
  · rw [Nat.card_congr (Subgroup.prodEquiv HA HB).toEquiv,
        Nat.card_prod, Nat.coprime_mul_iff_left]
    exact ⟨hA.1, hB.1⟩
  · obtain ⟨m, hm⟩ := hA.2
    obtain ⟨n, hn⟩ := hB.2
    exact ⟨m + n, by rw [Subgroup.index_prod, hm, hn, pow_add]⟩

/-- Direct products preserve `p`-length one. -/
private theorem isPLengthOne_prod
    {B : Type v} [Group B] [Finite B]
    (hA : IsPLengthOne p A) (hB : IsPLengthOne p B) :
    IsPLengthOne p (A × B) := by
  let UA := pElementGenerated p A
  let UB := pElementGenerated p B
  have hHA : IsPrimeComplement p (pPrimeCore p UA) :=
    (Submission.OddOrder.BG.Section01.p_elt_gen_length1
      (G := A) (p := p)).mp hA
  have hHB : IsPrimeComplement p (pPrimeCore p UB) :=
    (Submission.OddOrder.BG.Section01.p_elt_gen_length1
      (G := B) (p := p)).mp hB
  have hHP : IsPrimeComplement p (pPrimeCore p (UA × UB)) := by
    rw [pPrimeCore_prod]
    exact isPrimeComplement_prod hHA hHB
  let U := pElementGenerated p (A × B)
  have hU : U = UA.prod UB := pElementGenerated_prod
  let e : U ≃* UA × UB :=
    (MulEquiv.subgroupCongr hU).trans (Subgroup.prodEquiv UA UB)
  apply (Submission.OddOrder.BG.Section01.p_elt_gen_length1
    (G := A × B) (p := p)).mpr
  exact pPrimeCore_isPrimeComplement_mulEquiv e.symm hHP

/-- If two disjoint normal quotients have `p`-length one, so does the
original group.  This is MathComp's `quo2_plength1`. -/
private theorem isPLengthOne_of_two_quotients
    {N M : Subgroup A} [N.Normal] [M.Normal]
    (hdis : Disjoint N M)
    (hN : IsPLengthOne p (A ⧸ N))
    (hM : IsPLengthOne p (A ⧸ M)) :
    IsPLengthOne p A := by
  let qN : A →* A ⧸ N := QuotientGroup.mk' N
  let qM : A →* A ⧸ M := QuotientGroup.mk' M
  let f : A →* (A ⧸ N) × (A ⧸ M) := qN.prod qM
  have hf : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff]
    dsimp only [f, qN, qM]
    rw [MonoidHom.ker_prod,
      QuotientGroup.ker_mk', QuotientGroup.ker_mk', disjoint_iff.mp hdis]
  have hProd : IsPLengthOne p ((A ⧸ N) × (A ⧸ M)) :=
    isPLengthOne_prod hN hM
  have hRange : IsPLengthOne p f.range :=
    Submission.OddOrder.BG.Section01.plength1S f.range hProd
  let e : A ≃* f.range := MulEquiv.ofBijective f.rangeRestrict
    ⟨MonoidHom.rangeRestrict_injective_iff.mpr hf,
      f.rangeRestrict_surjective⟩
  exact isPLengthOne_of_mulEquiv hRange e.symm

end PLengthLifting

section SubgroupCentralizerTransport

variable {G : Type u} [Group G]

/-- A centralizer formed after restricting all groups to an intermediate
subgroup embeds in the corresponding ambient centralizer. -/
theorem isZGroup_centralizerWithin_subgroupOf
    {J H D R0 : Subgroup G}
    (hDH : D ≤ H) (hR0J : R0 ≤ J)
    (hZ : IsZGroup (centralizerWithin H R0)) :
    IsZGroup
      (centralizerWithin (D.subgroupOf J) (R0.subgroupOf J)) := by
  letI : IsZGroup (centralizerWithin H R0) := hZ
  let f :
      centralizerWithin (D.subgroupOf J) (R0.subgroupOf J) →*
        centralizerWithin H R0 :=
    { toFun := fun x ↦ ⟨((x : J) : G), by
          refine ⟨hDH x.property.1, ?_⟩
          intro r hr
          let rJ : J := ⟨r, hR0J hr⟩
          have hrJ : rJ ∈ R0.subgroupOf J := hr
          exact congrArg Subtype.val
            ((mem_centralizerWithin.mp x.property).2 rJ hrJ)⟩
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl }
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg
      (fun z : centralizerWithin H R0 => (z : G)) hxy
  exact IsZGroup.of_injective hf

end SubgroupCentralizerTransport

section FrattiniCoprimeAction

variable {A : Type u} [Group A] [Finite A]
variable {p : ℕ} [Fact p.Prime]

/-- A `p'`-subgroup whose action on a normal `p`-subgroup is trivial modulo
the Frattini subgroup centralizes that subgroup.  This is the form of
MathComp's `coprime_cent_Phi` used in the Frattini reduction below. -/
private theorem le_centralizer_of_commutator_le_frattini
    (P X : Subgroup A) [P.Normal]
    (hPp : IsPGroup p P)
    (hXp : IsPPrimeSubgroup p X)
    (hcomm : ⁅X, P⁆ ≤ (frattini P).map P.subtype) :
    X ≤ Subgroup.centralizer (P : Set A) := by
  let phi : X →* MulAut P := MulAut.conjNormal.comp X.subtype
  let psi : X →* MulAut (P ⧸ frattini P) :=
    (frattiniQuotientMulAutHom P).comp phi
  have hpsi : psi = 1 := by
    apply MonoidHom.ext
    intro x
    apply MulEquiv.ext
    intro y
    obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (frattini P) y
    change frattiniQuotientMulAutHom P (phi x)
      (QuotientGroup.mk' (frattini P) z) =
        QuotientGroup.mk' (frattini P) z
    rw [frattiniQuotientMulAutHom_apply_mk]
    apply QuotientGroup.eq_iff_div_mem.mpr
    apply (Subgroup.mem_map_iff_mem P.subtype_injective).mp
    simpa [phi, div_eq_mul_inv, MulAut.conjNormal_apply,
      commutatorElement_def] using
      hcomm (Subgroup.commutator_mem_commutator x.property z.property)
  have hrangeKer : phi.range ≤ (frattiniQuotientMulAutHom P).ker := by
    rintro a ⟨x, rfl⟩
    change frattiniQuotientMulAutHom P (phi x) = 1
    have hx := DFunLike.congr_fun hpsi x
    exact hx
  have hrangeP : IsPGroup p phi.range :=
    (frattiniQuotientMulAutHom_ker_isPGroup hPp).to_le hrangeKer
  have hrangePrime : IsPPrimeSubgroup p phi.range := by
    rw [IsPPrimeSubgroup]
    exact hXp.coprime_dvd_right
      (Subgroup.card_range_dvd phi)
  have hrangeBot : phi.range = ⊥ := by
    obtain ⟨n, hn⟩ := hrangeP.exists_card_eq
    have hself : Nat.Coprime (Nat.card phi.range) (Nat.card phi.range) := by
      simpa only [hn] using hrangePrime.pow_left n
    simpa using Subgroup.disjoint_of_coprime_natCard hself
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  let xx : X := ⟨x, hx⟩
  let yy : P := ⟨y, hy⟩
  have hphi : phi xx = 1 := by
    have : phi xx ∈ phi.range := ⟨xx, rfl⟩
    rw [hrangeBot] at this
    exact Subgroup.mem_bot.mp this
  have hfix : phi xx yy = yy := by rw [hphi]; rfl
  have hamb : x * y * x⁻¹ = y := congrArg Subtype.val hfix
  calc
    y * x = (x * y * x⁻¹) * x := by rw [hamb]
    _ = x * y := by group

/-- If the `p'`-core is trivial, it remains trivial after quotienting by the
ambient image of the Frattini subgroup of the `p`-core. -/
private theorem pPrimeCore_quotient_frattini_pCore_eq_bot
    [IsSolvable A]
    (hOA : pPrimeCore p A = ⊥) :
    let P : Subgroup A := pCore p A
    let N : Subgroup A := (frattini P).map P.subtype
    pPrimeCore p (A ⧸ N) = ⊥ := by
  let P : Subgroup A := pCore p A
  let N : Subgroup A := (frattini P).map P.subtype
  letI : N.Normal := by
    dsimp only [N, P]
    infer_instance
  let q : A →* A ⧸ N := QuotientGroup.mk' N
  let Oq : Subgroup (A ⧸ N) := pPrimeCore p (A ⧸ N)
  let W : Subgroup A := Oq.comap q
  letI : W.Normal := by
    dsimp only [W, Oq]
    infer_instance
  have hWmap : W.map q = Oq := by
    dsimp only [W]
    exact Subgroup.map_comap_eq_self_of_surjective
      (QuotientGroup.mk'_surjective N) Oq
  have hPp : IsPGroup p P := by
    dsimp only [P]
    exact pCore_isPGroup
  have hPmapP : IsPGroup p (P.map q) := hPp.map q
  have hPW : P ⊓ W ≤ N := by
    intro x hx
    have hxP : q x ∈ P.map q := ⟨x, hx.1, rfl⟩
    have hxW : q x ∈ W.map q := ⟨x, hx.2, rfl⟩
    rw [hWmap] at hxW
    have hxbot : q x ∈ (⊥ : Subgroup (A ⧸ N)) := by
      rw [← disjoint_iff.mp
        (disjoint_pPrimeCore_of_isPGroup hPmapP)]
      exact ⟨hxP, hxW⟩
    have hqx : q x = 1 := Subgroup.mem_bot.mp hxbot
    exact QuotientGroup.eq_one_iff x |>.mp hqx
  have hcentP : Subgroup.centralizer (P : Set A) ≤ P := by
    simpa [P] using
      (centralizer_pCore_le_pCore_of_pPrimeCore_eq_bot hOA)
  have hWp : IsPGroup p W := by
    apply isPGroup_of_prime_order_elements
    intro ell hell hellp x hxorder
    letI : Fact ell.Prime := ⟨hell⟩
    have hxAorder : orderOf (x : A) = ell := by
      exact (Subgroup.orderOf_mk (x : A) x.property).symm.trans hxorder
    let X : Subgroup A := Subgroup.zpowers (x : A)
    have hXW : X ≤ W := Subgroup.zpowers_le.mpr x.property
    have hXell : IsPGroup ell X := by
      apply IsPGroup.of_card (n := 1)
      rw [Nat.card_zpowers, hxAorder, pow_one]
    have hXprime : IsPPrimeSubgroup p X := by
      rw [IsPPrimeSubgroup, Nat.card_zpowers, hxAorder]
      exact (Nat.coprime_primes (Fact.out : p.Prime) hell).mpr
        (Ne.symm hellp)
    have hcommXP : ⁅X, P⁆ ≤ (frattini P).map P.subtype := by
      change ⁅X, P⁆ ≤ N
      apply (le_inf
        (Subgroup.commutator_le_right X P)
        ((Subgroup.commutator_mono hXW le_rfl).trans
          (Subgroup.commutator_le_left W P))).trans
      exact hPW
    have hXcent : X ≤ Subgroup.centralizer (P : Set A) :=
      le_centralizer_of_commutator_le_frattini P X hPp hXprime hcommXP
    have hXleP : X ≤ P := hXcent.trans hcentP
    have hdis : Disjoint X P :=
      IsPGroup.disjoint_of_ne ell p hellp X P hXell hPp
    have hXbot : X = ⊥ := by
      calc
        X = X ⊓ P := (inf_eq_left.mpr hXleP).symm
        _ = ⊥ := disjoint_iff.mp hdis
    apply Subtype.ext
    apply Subgroup.mem_bot.mp
    rw [← hXbot]
    exact Subgroup.mem_zpowers (x : A)
  have hOqP : IsPGroup p Oq := by
    rw [← hWmap]
    exact hWp.map q
  apply disjoint_self.mp
  simpa only [Oq] using
    (disjoint_pPrimeCore_of_isPGroup hOqP)

/-- A finite `p`-group with trivial Frattini subgroup is elementary
abelian. -/
private theorem isElementaryAbelianGroup_of_frattini_eq_bot
    {P : Type u} [Group P] [Finite P]
    (hP : IsPGroup p P) (hPhi : frattini P = ⊥) :
    IsElementaryAbelianGroup p P := by
  have hderived : _root_.commutator P = ⊥ := by
    apply le_bot_iff.mp
    rw [← hPhi]
    exact IsPGroup.commutator_le_frattini hP
  letI : IsMulCommutative P :=
    (_root_.commutator_eq_bot_iff P).mp hderived
  refine ⟨hP, inferInstance, ?_⟩
  intro x
  have hx := IsPGroup.pow_prime_mem_frattini hP x
  rw [hPhi] at hx
  exact Subgroup.mem_bot.mp hx

/-- Images of elementary-abelian subgroups remain elementary abelian. -/
private theorem isElementaryAbelianGroup_map
    {G : Type u} {A : Type v} [Group G] [Group A]
    {E : Subgroup G} {p : ℕ}
    (hE : IsElementaryAbelianGroup p E) (f : G →* A) :
    IsElementaryAbelianGroup p (E.map f) := by
  letI : IsMulCommutative E := hE.commutative
  refine
    { isPGroup := hE.isPGroup.map f
      commutative := Subgroup.map_isMulCommutative E f
      pow_eq_one := ?_ }
  intro x
  rcases x.property with ⟨e, he, hxe⟩
  apply Subtype.ext
  change (x : A) ^ p = 1
  rw [← hxe, ← map_pow]
  have hep : e ^ p = 1 :=
    congrArg Subtype.val (hE.pow_eq_one ⟨e, he⟩)
  rw [hep, map_one]

end FrattiniCoprimeAction

/-- The normal factor has no nontrivial decomposition into two disjoint
ambient-normal factors. -/
private def NormalIndecomposableFactor
    {G : Type u} [Group G] (V : Subgroup G) : Prop :=
  ∀ U W : Subgroup G,
    U.Normal → W.Normal → U ⊔ W = V → Disjoint U W →
      U = ⊥ ∨ U = V

section CentralizerBlockArithmetic

/-- A transitive finite set for an odd-order finite group has odd
cardinality. -/
private theorem odd_natCard_of_pretransitive
    {L Ω : Type*} [Group L] [Finite L] [Finite Ω]
    [Nonempty Ω] [MulAction L Ω]
    [MulAction.IsPretransitive L Ω]
    (hodd : Odd (Nat.card L)) :
    Odd (Nat.card Ω) := by
  let x : Ω := Classical.choice (inferInstance : Nonempty Ω)
  have hdiv : Nat.card Ω ∣ Nat.card L := by
    rw [← MulAction.index_stabilizer_of_transitive L x]
    exact (MulAction.stabilizer L x).index_dvd_card
  exact hodd.of_dvd_nat hdiv

/-- A nonfixed orbit for a group of prime order is the whole prime-sized
orbit. -/
private theorem natCard_orbit_eq_of_prime_card_not_fixed
    {R Ω : Type*} [Group R] [Finite R] [Finite Ω]
    [MulAction R Ω]
    (hRprime : (Nat.card R).Prime) (x : Ω)
    (hnot : x ∉ MulAction.fixedPoints R Ω) :
    (MulAction.orbit R x).ncard = Nat.card R := by
  letI : Fact (Nat.card R).Prime := ⟨hRprime⟩
  have hstab : MulAction.stabilizer R x = ⊥ := by
    rcases (MulAction.stabilizer R x).eq_bot_or_eq_top_of_prime_card with
      hbot | htop
    · exact hbot
    · exfalso
      apply hnot
      rw [MulAction.mem_fixedPoints]
      intro r
      have hr : r ∈ MulAction.stabilizer R x := by
        rw [htop]
        trivial
      exact hr
  rw [← MulAction.index_stabilizer R x, hstab, Subgroup.index_bot]

/-- A `p`-group acting on a set of a distinct prime cardinality has a fixed
point. -/
private theorem fixedPoint_of_card_eq_distinct_prime
    {P Ω : Type*} [Group P] [Finite P] [Finite Ω]
    [MulAction P Ω] {p r : ℕ} [Fact p.Prime]
    (hP : IsPGroup p P) (hr : r.Prime)
    (hpr : p ≠ r) (hcard : Nat.card Ω = r) :
    (MulAction.fixedPoints P Ω).Nonempty := by
  apply hP.nonempty_fixed_point_of_prime_not_dvd_card Ω
  rw [hcard, Nat.prime_dvd_prime_iff_eq Fact.out hr]
  exact hpr

/-- An odd prime-sized subset with a unique point outside it cannot live in
an odd-cardinality finite type. -/
private theorem false_of_odd_card_of_prime_set_with_singleton_compl
    {Ω : Type*} [Finite Ω] (D : Set Ω) {r : ℕ}
    (hrOdd : Odd r) (hDcard : D.ncard = r)
    (hDne : D ≠ Set.univ)
    (huniq : ∀ x ∈ Dᶜ, ∀ y ∈ Dᶜ, x = y)
    (hΩodd : Odd (Nat.card Ω)) :
    False := by
  obtain ⟨x, hx⟩ := (Set.ne_univ_iff_exists_notMem D).mp hDne
  have hx' : x ∈ Dᶜ := by simpa
  have hcomp : Dᶜ = {x} := by
    apply Set.eq_singleton_iff_unique_mem.mpr
    exact ⟨hx', fun y hy ↦ huniq y hy x hx'⟩
  have hcard : Nat.card Ω = r + 1 := by
    calc
      Nat.card Ω = D.ncard + Dᶜ.ncard :=
        (Set.ncard_add_ncard_compl D).symm
      _ = r + 1 := by rw [hDcard, hcomp, Set.ncard_singleton]
  have heven : Even (Nat.card Ω) := by
    rw [hcard]
    exact hrOdd.add_one
  exact (Nat.not_even_iff_odd.mpr hΩodd) heven

/-- The final orbit-counting contradiction, separated from the group
theory that identifies the complement of the chosen prime orbit. -/
private theorem false_of_prime_orbit_with_singleton_compl
    {L P R Ω : Type*}
    [Group L] [Finite L] [Group P] [Finite P]
    [Group R] [Finite R] [Finite Ω] [Nonempty Ω]
    [MulAction L Ω] [MulAction.IsPretransitive L Ω]
    [MulAction P Ω] [MulAction R Ω]
    {p : ℕ} [Fact p.Prime]
    (hLodd : Odd (Nat.card L))
    (hP : IsPGroup p P)
    (hRprime : (Nat.card R).Prime)
    (hRodd : Odd (Nat.card R))
    (hpR : p ≠ Nat.card R)
    (x : Ω) (hx : x ∉ MulAction.fixedPoints R Ω)
    (hPnoFixed : ∀ y : Ω, y ∉ MulAction.fixedPoints P Ω)
    (huniq : ∀ y ∈ (MulAction.orbit R x)ᶜ,
      ∀ z ∈ (MulAction.orbit R x)ᶜ, y = z) :
    False := by
  let D : Set Ω := MulAction.orbit R x
  have hDcard : D.ncard = Nat.card R := by
    simpa only [D] using
      natCard_orbit_eq_of_prime_card_not_fixed hRprime x hx
  by_cases hDuniv : D = Set.univ
  · have hΩcard : Nat.card Ω = Nat.card R := by
      rw [← Set.ncard_univ Ω, ← hDuniv]
      exact hDcard
    obtain ⟨y, hy⟩ :=
      fixedPoint_of_card_eq_distinct_prime hP hRprime hpR hΩcard
    exact hPnoFixed y hy
  · exact false_of_odd_card_of_prime_set_with_singleton_compl
      D hRodd hDcard hDuniv
      (by simpa only [D] using huniq)
      (odd_natCard_of_pretransitive hLodd)

/-- The multiplicative norm embeds a nontrivial subgroup into the
prime-cardinality fixed-point subgroup whenever its translates lie in an
independent family. -/
private theorem actionNorm_independent_family_card_and_fixed_le
    {R : Type u} {A : Type v}
    [Group R] [Fintype R]
    [CommGroup A] [MulDistribMulAction R A]
    {p : ℕ} [Fact p.Prime]
    (W : Subgroup A)
    (B : R → Subgroup A)
    (hWne : W ≠ ⊥)
    (hind : iSupIndep B)
    (hsmul : ∀ r : R, ∀ a : A, a ∈ W → r • a ∈ B r)
    (hfixcard : Nat.card (FixedPoints.subgroup R A) = p) :
    Nat.card W = p ∧
      FixedPoints.subgroup R A ≤ ⨆ r : R, B r := by
  classical
  let N : A →* A :=
    Submission.OddOrder.BG.Section06.actionNormHom R A
  have hNfix (a : A) :
      N a ∈ FixedPoints.subgroup R A := by
    rw [FixedPoints.mem_subgroup R A (N a)]
    intro r
    change r • (∏ x : R, x • a) = ∏ x : R, x • a
    rw [Finset.smul_prod']
    exact Fintype.prod_equiv (Equiv.mulLeft r)
      (fun x : R ↦ r • (x • a))
      (fun x : R ↦ x • a)
      (fun x ↦ (mul_smul r x a).symm)
  let f : W →* FixedPoints.subgroup R A :=
    (N.comp W.subtype).codRestrict
      (FixedPoints.subgroup R A)
      (fun w ↦ hNfix (w : A))
  have hf_inj : Function.Injective f := by
    intro x y hxy
    have hxyN : N (x : A) = N (y : A) := by
      simpa [f] using
        congrArg
          (fun z : FixedPoints.subgroup R A ↦ (z : A)) hxy
    have hNxy : N ((x : A) * (y : A)⁻¹) = 1 := by
      rw [map_mul, map_inv, hxyN, mul_inv_cancel]
    let z : A := (x : A) * (y : A)⁻¹
    have hzW : z ∈ W := by
      simpa [z] using W.mul_mem x.2 (W.inv_mem y.2)
    have hzprod : (∏ r : R, r • z) = 1 := by
      simpa [N,
        Submission.OddOrder.BG.Section06.actionNormHom,
        z] using hNxy
    have hnoncomm :
        Finset.noncommProd Finset.univ
          (fun r : R ↦ r • z)
          (fun _ _ _ _ _ ↦ Commute.all _ _) = 1 := by
      exact
        (Finset.noncommProd_eq_prod
          (Finset.univ : Finset R)
          (fun r : R ↦ r • z)).trans hzprod
    have hall :=
      Subgroup.eq_one_of_noncommProd_eq_one_of_iSupIndep
        (Finset.univ : Finset R)
        (fun r : R ↦ r • z)
        (fun _ _ _ _ _ ↦ Commute.all _ _)
        B hind
        (fun r _ ↦ hsmul r z hzW)
        hnoncomm
    have hz1 : z = 1 := by
      simpa using hall (1 : R) (Finset.mem_univ _)
    apply Subtype.ext
    exact mul_inv_eq_one.mp (by simpa [z] using hz1)
  have hfrange_ne : f.range ≠ ⊥ := by
    intro hfrange
    apply hWne
    apply (Subgroup.eq_bot_iff_forall W).mpr
    intro a ha
    let w : W := ⟨a, ha⟩
    have hfw_mem : f w ∈ f.range := ⟨w, rfl⟩
    rw [hfrange] at hfw_mem
    have hfw_one : f w = 1 := Subgroup.mem_bot.mp hfw_mem
    have hw_one : w = 1 := hf_inj (by simpa using hfw_one)
    simpa [w] using congrArg Subtype.val hw_one
  have hfixprime :
      (Nat.card (FixedPoints.subgroup R A)).Prime := by
    rw [hfixcard]
    exact Fact.out
  letI : Fact (Nat.card (FixedPoints.subgroup R A)).Prime :=
    ⟨hfixprime⟩
  have hfrange_top : f.range = ⊤ :=
    f.range.eq_bot_or_eq_top_of_prime_card.resolve_left hfrange_ne
  have hf_surj : Function.Surjective f :=
    MonoidHom.range_eq_top.mp hfrange_top
  have hcard :
      Nat.card W = Nat.card (FixedPoints.subgroup R A) :=
    Nat.card_congr
      (MulEquiv.ofBijective f ⟨hf_inj, hf_surj⟩).toEquiv
  refine ⟨hcard.trans hfixcard, ?_⟩
  intro a ha
  obtain ⟨w, hw⟩ := hf_surj ⟨a, ha⟩
  have hwa : N (w : A) = a := by
    simpa [f] using
      congrArg
        (fun z : FixedPoints.subgroup R A ↦ (z : A)) hw
  rw [← hwa]
  have hprodmem :
      (∏ r : R, r • (w : A)) ∈ ⨆ r : R, B r := by
    apply Subgroup.prod_mem
    intro r _
    exact (le_iSup B r) (hsmul r (w : A) w.2)
  simpa [N,
    Submission.OddOrder.BG.Section06.actionNormHom] using hprodmem

/-- Fixed points for the conjugation action on a normalized subgroup are
exactly the corresponding ambient relative centralizer. -/
private theorem map_fixedPoints_eq_centralizerWithin
    {G : Type u} [Group G]
    {V R : Subgroup G}
    [MulDistribMulAction R V]
    (hsmul : ∀ (r : R) (v : V),
      ((r • v : V) : G) =
        (r : G) * (v : G) * (r : G)⁻¹) :
    (FixedPoints.subgroup R V).map V.subtype =
      centralizerWithin V R := by
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨v.2, ?_⟩
    intro r hr
    let rr : R := ⟨r, hr⟩
    have hfix : rr • v = v :=
      (FixedPoints.mem_subgroup R V v).mp hv rr
    have hfixG := congrArg Subtype.val hfix
    rw [hsmul rr v] at hfixG
    exact mul_inv_eq_iff_eq_mul.mp hfixG
  · rintro ⟨hxV, hxC⟩
    let v : V := ⟨x, hxV⟩
    refine ⟨v, (FixedPoints.mem_subgroup R V v).2 ?_, rfl⟩
    intro r
    apply Subtype.ext
    rw [hsmul r v]
    exact mul_inv_eq_iff_eq_mul.mpr
      (hxC (r : G) r.2)

/-- The centralizer blocks used in the final orbit argument. -/
private def IsCentralizerBlock
    {G : Type*} [Group G] (V K W : Subgroup G) : Prop :=
  centralizerWithin V (centralizerWithin K W) = W ∧
    IsCoatom ((centralizerWithin K W).subgroupOf K)

private abbrev CentralizerBlocks
    {G : Type*} [Group G] (V K : Subgroup G) :=
  {W : Subgroup G // IsCentralizerBlock V K W}

/-- A proper cocyclic subgroup of an elementary abelian group is maximal. -/
private theorem isCoatom_subgroupOf_of_elementaryAbelian_cocyclic
    {G : Type*} [Group G] [Finite G]
    {q : ℕ} [Fact q.Prime]
    (K C : Subgroup G)
    (hKelem : IsElementaryAbelianGroup q K)
    (hCK : C ≤ K)
    (hCnormal : (C.subgroupOf K).Normal)
    (hCcyclic : IsCyclic (K ⧸ C.subgroupOf K))
    (hCneK : C ≠ K) :
    IsCoatom (C.subgroupOf K) := by
  let CK : Subgroup K := C.subgroupOf K
  letI : CK.Normal := by
    simpa only [CK] using hCnormal
  have hCKneTop : CK ≠ ⊤ := by
    intro htop
    apply hCneK
    apply le_antisymm hCK
    intro k hk
    let kk : K := ⟨k, hk⟩
    have hkk : kk ∈ CK := by
      rw [htop]
      trivial
    change k ∈ C at hkk
    exact hkk
  let Q := K ⧸ CK
  letI : Nontrivial Q := QuotientGroup.nontrivial_iff.mpr hCKneTop
  letI : IsCyclic Q := by
    simpa only [Q, CK] using hCcyclic
  have hQp : IsPGroup q Q := by
    dsimp only [Q]
    exact hKelem.isPGroup.to_quotient CK
  have hQpow : ∀ x : Q, x ^ q = 1 := by
    intro x
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective CK x
    simpa only [map_pow, map_one] using
      congrArg (QuotientGroup.mk' CK) (hKelem.pow_eq_one k)
  letI : Fintype Q := Fintype.ofFinite Q
  letI : DecidableEq Q := Classical.decEq Q
  have hQle : Nat.card Q ≤ q := by
    rw [Nat.card_eq_fintype_card]
    simpa only [hQpow, Finset.filter_true, Finset.card_univ] using
      (IsCyclic.card_pow_eq_one_le (α := Q)
        (Fact.out : q.Prime).pos)
  have hQneOne : Nat.card Q ≠ 1 :=
    (Finite.one_lt_card (α := Q)).ne'
  have hqdvd : q ∣ Nat.card Q :=
    hQp.card_eq_or_dvd.resolve_left hQneOne
  have hQcard : Nat.card Q = q :=
    le_antisymm hQle
      (Nat.le_of_dvd (Nat.card_pos (α := Q)) hqdvd)
  have hCKindex : CK.index = q := by
    rw [Subgroup.index_eq_card]
    exact hQcard
  simpa only [CK] using
    isCoatom_of_index_eq_prime
      (H := CK) (Fact.out : q.Prime) hCKindex

/-- The canonical centralizer blocks span the elementary abelian normal
factor. -/
private theorem centralizerBlocks_span
    {G : Type*} [Group G] [Finite G]
    {q : ℕ} [Fact q.Prime]
    (V K : Subgroup G)
    (hKelem : IsElementaryAbelianGroup q K)
    (hKncyc : ¬ IsCyclic K)
    (hKV : K ≤ Subgroup.normalizer (V : Set G))
    (hcop : Nat.Coprime (Nat.card V) (Nat.card K))
    (hVsol : IsSolvable V)
    (hCVK : centralizerWithin V K = ⊥) :
    sSup {W : Subgroup G | IsCentralizerBlock V K W} = V := by
  let S : Set (Subgroup G) :=
    {W : Subgroup G | IsCentralizerBlock V K W}
  change sSup S = V
  apply le_antisymm
  · rw [sSup_le_iff]
    intro W hW
    change IsCentralizerBlock V K W at hW
    rw [← hW.1]
    exact centralizerWithin_le_left _ _
  · apply le_of_centralizerWithin_cocyclic_le_of_coprime_abelian_solvable
      hKelem.commutative hKncyc hKV hcop hVsol
    intro C hCK hCnormal hCcyclic
    let W : Subgroup G := centralizerWithin V C
    change W ≤ sSup S
    by_cases hWbot : W = ⊥
    · rw [hWbot]
      exact bot_le
    have hCneK : C ≠ K := by
      intro hCKeq
      subst C
      apply hWbot
      simpa only [W] using hCVK
    have hCmax : IsCoatom (C.subgroupOf K) :=
      isCoatom_subgroupOf_of_elementaryAbelian_cocyclic
        K C hKelem hCK hCnormal hCcyclic hCneK
    let D : Subgroup G := centralizerWithin K W
    have hDK : D ≤ K := centralizerWithin_le_left K W
    have hCD : C ≤ D := by
      intro c hc
      refine ⟨hCK hc, ?_⟩
      intro w hw
      change w ∈ centralizerWithin V C at hw
      exact (hw.2 c hc).symm
    have hCDsub : C.subgroupOf K ≤ D.subgroupOf K :=
      Subgroup.subgroupOf_mono K hCD
    have hDC : D = C := by
      rcases hCmax.le_iff.mp hCDsub with hDtop | hDeq
      · have hKD : K ≤ D := by
          intro k hk
          let kk : K := ⟨k, hk⟩
          have hkk : kk ∈ D.subgroupOf K := by
            rw [hDtop]
            trivial
          change k ∈ D at hkk
          exact hkk
        have hWCVK : W ≤ centralizerWithin V K := by
          intro w hw
          have hwVC : w ∈ centralizerWithin V C := by
            simpa only [W] using hw
          refine ⟨hwVC.1, ?_⟩
          intro k hk
          have hkD : k ∈ D := hKD hk
          change k ∈ centralizerWithin K W at hkD
          exact (hkD.2 w hw).symm
        have hWbot' : W = ⊥ := by
          apply le_bot_iff.mp
          exact hWCVK.trans (le_of_eq hCVK)
        exact (hWbot hWbot').elim
      · apply le_antisymm
        · intro d hd
          let dk : K := ⟨d, hDK hd⟩
          have hdk : dk ∈ D.subgroupOf K := hd
          rw [hDeq] at hdk
          change d ∈ C at hdk
          exact hdk
        · exact hCD
    have hWinS : W ∈ S := by
      change IsCentralizerBlock V K W
      constructor
      · calc
          centralizerWithin V (centralizerWithin K W) =
              centralizerWithin V D := rfl
          _ = centralizerWithin V C :=
            congrArg (centralizerWithin V) hDC
          _ = W := rfl
      · have hsub :
            (centralizerWithin K W).subgroupOf K = C.subgroupOf K := by
          change D.subgroupOf K = C.subgroupOf K
          rw [hDC]
        rw [hsub]
        exact hCmax
    exact le_sSup hWinS

private theorem not_isCyclic_of_elementaryAbelian_card_gt_sq
    {G : Type*} [Group G] [Finite G]
    {q : ℕ} [Fact q.Prime]
    (hG : IsElementaryAbelianGroup q G)
    (hcard : q ^ 2 < Nat.card G) :
    ¬ IsCyclic G := by
  classical
  intro hcyclic
  letI : IsCyclic G := hcyclic
  letI : Fintype G := Fintype.ofFinite G
  letI : DecidableEq G := Classical.decEq G
  have hpow : ∀ x : G, x ^ q = 1 := hG.pow_eq_one
  have hle : Nat.card G ≤ q := by
    rw [Nat.card_eq_fintype_card]
    simpa only [hpow, Finset.filter_true, Finset.card_univ] using
      (IsCyclic.card_pow_eq_one_le (α := G)
        (Fact.out : q.Prime).pos)
  have hqsq : q ≤ q ^ 2 := by
    nlinarith [(Fact.out : q.Prime).pos]
  exact (not_lt_of_ge (hle.trans hqsq)) hcard

/-- Every centralizer block is normalized by the abelian acting subgroup. -/
private theorem centralizerBlock_le_normalizer
    {G : Type*} [Group G]
    (V K W : Subgroup G)
    (hKcomm : IsMulCommutative K)
    (hKV : K ≤ Subgroup.normalizer (V : Set G))
    (hW : IsCentralizerBlock V K W) :
    K ≤ Subgroup.normalizer (W : Set G) := by
  rw [← hW.1, Subgroup.le_normalizer_iff]
  intro g hg x hx
  refine ⟨(Subgroup.le_normalizer_iff.mp hKV g hg x hx.1), ?_⟩
  intro c hc
  have hgc : Commute g c := by
    exact congrArg Subtype.val
      ((isMulCommutative_iff.mp hKcomm)
        (⟨g, hg⟩ : K) (⟨c, hc.1⟩ : K))
  have hcx : Commute c x := hx.2 c hc
  calc
    c * (g * x * g⁻¹) = (c * g) * x * g⁻¹ := by group
    _ = (g * c) * x * g⁻¹ := by rw [hgc.eq.symm]
    _ = g * (c * x) * g⁻¹ := by group
    _ = g * (x * c) * g⁻¹ := by rw [hcx.eq]
    _ = g * x * (c * g⁻¹) := by group
    _ = g * x * (g⁻¹ * c) := by rw [(hgc.symm.inv_right).eq]
    _ = (g * x * g⁻¹) * c := by group

/-- Distinct blocks have centralizers whose join is all of `K`. -/
private theorem centralizerBlock_centralizers_sup_eq
    {G : Type*} [Group G]
    (V K W₁ W₂ : Subgroup G)
    (hW₁ : IsCentralizerBlock V K W₁)
    (hW₂ : IsCentralizerBlock V K W₂)
    (hne : W₁ ≠ W₂) :
    centralizerWithin K W₁ ⊔ centralizerWithin K W₂ = K := by
  let C₁ : Subgroup G := centralizerWithin K W₁
  let C₂ : Subgroup G := centralizerWithin K W₂
  have hC₁K : C₁ ≤ K := by
    simpa only [C₁] using centralizerWithin_le_left K W₁
  have hC₂K : C₂ ≤ K := by
    simpa only [C₂] using centralizerWithin_le_left K W₂
  have hC₁coatom : IsCoatom (C₁.subgroupOf K) := by
    simpa only [C₁] using hW₁.2
  have hC₂coatom : IsCoatom (C₂.subgroupOf K) := by
    simpa only [C₂] using hW₂.2
  have hCne : C₁.subgroupOf K ≠ C₂.subgroupOf K := by
    intro hsub
    have hCeq : C₁ = C₂ := by
      calc
        C₁ = (C₁.subgroupOf K).map K.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hC₁K).symm
        _ = (C₂.subgroupOf K).map K.subtype :=
          congrArg (fun C : Subgroup K => C.map K.subtype) hsub
        _ = C₂ := Subgroup.map_subgroupOf_eq_of_le hC₂K
    apply hne
    calc
      W₁ = centralizerWithin V C₁ := by
        simpa only [C₁] using hW₁.1.symm
      _ = centralizerWithin V C₂ := congrArg (centralizerWithin V) hCeq
      _ = W₂ := by simpa only [C₂] using hW₂.1
  have htop : C₁.subgroupOf K ⊔ C₂.subgroupOf K = ⊤ :=
    hC₁coatom.sup_eq_top_of_ne hC₂coatom hCne
  apply le_antisymm
  · exact sup_le hC₁K hC₂K
  · intro k hk
    let kk : K := ⟨k, hk⟩
    have hkk : kk ∈ C₁.subgroupOf K ⊔ C₂.subgroupOf K := by
      rw [htop]
      exact Subgroup.mem_top kk
    rw [← Subgroup.subgroupOf_sup hC₁K hC₂K] at hkk
    change k ∈ C₁ ⊔ C₂ at hkk
    exact hkk

/-- The canonical centralizer blocks form an internal direct product. -/
private theorem centralizerBlocks_sSupIndep
    {G : Type*} [Group G] [Finite G]
    (V K : Subgroup G)
    (hVcomm : IsMulCommutative V)
    (hKcomm : IsMulCommutative K)
    (hKV : K ≤ Subgroup.normalizer (V : Set G))
    (hCVK : centralizerWithin V K = ⊥) :
    sSupIndep {W : Subgroup G | IsCentralizerBlock V K W} := by
  classical
  letI : Finite (Subgroup G) :=
    Finite.of_injective (fun W : Subgroup G => (W : Set G))
      SetLike.coe_injective
  letI : Fintype (CentralizerBlocks V K) := Fintype.ofFinite _
  letI : IsMulCommutative V := hVcomm
  have hblockV (W : CentralizerBlocks V K) :
      (W : Subgroup G) ≤ V := by
    rw [← W.property.1]
    exact centralizerWithin_le_left _ _
  have hfin : ∀ D : Finset (CentralizerBlocks V K),
      D.SupIndep
        (fun W : CentralizerBlocks V K => W.1.subgroupOf V) := by
    intro D
    induction D using Finset.induction_on with
    | empty => exact Finset.supIndep_empty _
    | @insert i D hi ih =>
      apply ih.insert
      rw [disjoint_iff_inf_le]
      intro x hx
      apply Subgroup.mem_bot.mpr
      let B : D → Subgroup V :=
        (fun W : CentralizerBlocks V K => W.1.subgroupOf V) ∘
          Subtype.val
      have hcomm : Pairwise fun a b : D =>
          ∀ x y : V, x ∈ B a → y ∈ B b → Commute x y := by
        intro _ _ _ _ _ _ _
        exact Commute.all _ _
      let φ : (∀ a : D, B a) →* V :=
        Subgroup.noncommPiCoprod hcomm
      have hφrange : φ.range =
          D.sup (fun W : CentralizerBlocks V K => W.1.subgroupOf V) := by
        calc
          φ.range = ⨆ a : D, B a := by
            dsimp only [φ]
            exact Subgroup.noncommPiCoprod_range
          _ = D.sup (fun W : CentralizerBlocks V K =>
              W.1.subgroupOf V) := by
            rw [Finset.sup_eq_iSup, iSup_subtype']
            rfl
      have hφinj : Function.Injective φ := by
        dsimp only [φ]
        apply Subgroup.injective_noncommPiCoprod_of_iSupIndep
        change iSupIndep B
        exact ih.independent
      have hxrange : x ∈ φ.range := by
        rw [hφrange]
        exact hx.2
      rcases hxrange with ⟨u, hu⟩
      have hpairu : Pairwise fun a b : D =>
          Commute (u a : V) (u b : V) := by
        intro a b hab
        exact hcomm hab _ _ (u a).property (u b).property
      have huj : ∀ j : D, u j = 1 := by
        intro j
        have huCi : (u j : G) ∈ centralizerWithin V
            (centralizerWithin K (i : Subgroup G)) := by
          refine ⟨hblockV j.1 (u j).property, ?_⟩
          intro g hg
          let ug : ∀ a : D, B a := fun a => by
            have hmem : g * (u a : G) * g⁻¹ ∈
                (a.1 : Subgroup G) :=
              Subgroup.le_normalizer_iff.mp
                (centralizerBlock_le_normalizer V K (a.1 : Subgroup G)
                  hKcomm hKV a.1.property)
                g hg.1 (u a : G) (u a).property
            exact ⟨⟨g * (u a : G) * g⁻¹,
              hblockV a.1 hmem⟩, hmem⟩
          have hφug : ((φ ug : V) : G) =
              (MulAut.conj g) ((φ u : V) : G) := by
            have hug (a : D) :
                (ug a : V) =
                  V.normalizerMonoidHom ⟨g, hKV hg.1⟩ (u a : V) := by
              apply Subtype.ext
              rfl
            have hφugV : φ ug =
                V.normalizerMonoidHom ⟨g, hKV hg.1⟩ (φ u) := by
              dsimp only [φ]
              rw [Subgroup.noncommPiCoprod_apply hcomm ug,
                Subgroup.noncommPiCoprod_apply hcomm u]
              simpa only [hug] using
                (Finset.map_noncommProd (Finset.univ : Finset D)
                  (fun a : D => (u a : V)) (hpairu.set_pairwise _)
                  (V.normalizerMonoidHom ⟨g, hKV hg.1⟩)).symm
            rw [MulAut.conj_apply]
            change ((φ ug : V) : G) =
              ((V.normalizerMonoidHom ⟨g, hKV hg.1⟩ (φ u) : V) : G)
            exact congrArg Subtype.val hφugV
          have hφsame : φ ug = φ u := by
            apply Subtype.ext
            rw [hφug, MulAut.conj_apply,
              congrArg Subtype.val hu]
            calc
              g * (x : G) * g⁻¹ = (x : G) * g * g⁻¹ := by
                rw [(hg.2 (x : G) hx.1).symm]
              _ = (x : G) := by group
          have hugu : ug = u := hφinj hφsame
          have hfixed : g * (u j : G) * g⁻¹ = (u j : G) := by
            simpa only [ug] using
              congrArg (fun z : B j => ((z : V) : G))
                (congrFun hugu j)
          calc
            g * (u j : G) = (g * (u j : G) * g⁻¹) * g := by group
            _ = (u j : G) * g := by rw [hfixed]
        have huCj : (u j : G) ∈ centralizerWithin V
            (centralizerWithin K (j.1 : Subgroup G)) := by
          rw [j.1.property.1]
          exact (u j).property
        have hij : (i : Subgroup G) ≠ (j.1 : Subgroup G) := by
          intro hij
          apply hi
          have hij' : i = j.1 := Subtype.ext hij
          simpa only [hij'] using j.property
        have hsup := centralizerBlock_centralizers_sup_eq
          V K (i : Subgroup G) (j.1 : Subgroup G)
          i.property j.1.property hij
        have hCiCent : centralizerWithin K (i : Subgroup G) ≤
            Subgroup.centralizer ({(u j : G)} : Set G) := by
          intro g hg
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact huCi.2 g hg
        have hCjCent : centralizerWithin K (j.1 : Subgroup G) ≤
            Subgroup.centralizer ({(u j : G)} : Set G) := by
          intro g hg
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact huCj.2 g hg
        have hKCent : K ≤
            Subgroup.centralizer ({(u j : G)} : Set G) := by
          rw [← hsup]
          exact sup_le hCiCent hCjCent
        have huCVK : (u j : G) ∈ centralizerWithin V K := by
          refine ⟨huCi.1, ?_⟩
          intro k hk
          exact Subgroup.mem_centralizer_singleton_iff.mp (hKCent hk)
        rw [hCVK] at huCVK
        apply Subtype.ext
        apply Subtype.ext
        exact Subgroup.mem_bot.mp huCVK
      have huone : u = 1 := by
        funext j
        exact huj j
      calc
        x = φ u := hu.symm
        _ = φ 1 := congrArg (fun z => φ z) huone
        _ = 1 := map_one φ
  rw [sSupIndep_iff]
  have hindV :
      iSupIndep
        (fun W : CentralizerBlocks V K => W.1.subgroupOf V) :=
    iSupIndep_iff_supIndep_univ.mpr (hfin Finset.univ)
  have hindG : iSupIndep
      (fun W : CentralizerBlocks V K =>
        (W.1.subgroupOf V).map V.subtype) := by
    intro W
    simpa only [Subgroup.map_iSup] using
      Subgroup.disjoint_map V.subtype_injective (hindV W)
  have hmap (W : CentralizerBlocks V K) :
      (W.1.subgroupOf V).map V.subtype = W.1 :=
    Subgroup.map_subgroupOf_eq_of_le (hblockV W)
  have hfam :
      (fun W : CentralizerBlocks V K =>
          (W.1.subgroupOf V).map V.subtype) =
        (fun W : CentralizerBlocks V K => W.1) :=
    funext hmap
  rw [hfam] at hindG
  change iSupIndep (fun W : CentralizerBlocks V K => W.1)
  exact hindG

/-- Centralizers commute with transport by an ambient automorphism that
stabilizes the left-hand subgroup. -/
private theorem map_centralizerWithin_equiv
    {G : Type u} [Group G]
    {D A : Subgroup G} (e : G ≃* G)
    (hD : D.map e.toMonoidHom = D) :
    (centralizerWithin D A).map e.toMonoidHom =
      centralizerWithin D (A.map e.toMonoidHom) := by
  ext y
  rw [Subgroup.mem_map_equiv]
  constructor
  · intro hy
    refine ⟨?_, ?_⟩
    · have hyMap : y ∈ D.map e.toMonoidHom :=
        Subgroup.mem_map_equiv.mpr hy.1
      rwa [hD] at hyMap
    · intro z hz
      have hz' : e.symm z ∈ A := Subgroup.mem_map_equiv.mp hz
      have hcomm := hy.2 (e.symm z) hz'
      simpa using congrArg e hcomm
  · intro hy
    refine ⟨?_, ?_⟩
    · have hyMap : y ∈ D.map e.toMonoidHom := by
        rw [hD]
        exact hy.1
      exact Subgroup.mem_map_equiv.mp hyMap
    · intro z hz
      have hzMap : e z ∈ A.map e.toMonoidHom :=
        (Subgroup.mem_map_iff_mem e.injective).mpr hz
      have hcomm := hy.2 (e z) hzMap
      simpa using congrArg e.symm hcomm

private theorem centralizerBlock_le_left
    {G : Type u} [Group G] {V K : Subgroup G}
    (W : CentralizerBlocks V K) :
    W.1 ≤ V := by
  rw [← W.2.1]
  exact centralizerWithin_le_left _ _

private theorem centralizerBlock_ne_bot
    {G : Type u} [Group G] {V K : Subgroup G}
    (W : CentralizerBlocks V K) :
    W.1 ≠ ⊥ := by
  intro hW
  have hCK : centralizerWithin K W.1 = K := by
    rw [hW]
    ext x
    constructor
    · exact fun hx => hx.1
    · intro hx
      refine ⟨hx, ?_⟩
      intro a ha
      rw [Subgroup.mem_bot.mp ha]
      simp
  apply W.2.2.ne_top
  rw [hCK, Subgroup.subgroupOf_self]

private theorem centralizerBlock_map_conj
    {G : Type u} [Group G]
    {V K W : Subgroup G} (g : G)
    (hV : V.map (MulAut.conj g).toMonoidHom = V)
    (hK : K.map (MulAut.conj g).toMonoidHom = K)
    (hW : IsCentralizerBlock V K W) :
    IsCentralizerBlock V K
      (W.map (MulAut.conj g).toMonoidHom) := by
  let e : G ≃* G := MulAut.conj g
  have hCK :
      (centralizerWithin K W).map e.toMonoidHom =
        centralizerWithin K (W.map e.toMonoidHom) :=
    map_centralizerWithin_equiv e hK
  have hCV :
      (centralizerWithin V (centralizerWithin K W)).map
          e.toMonoidHom =
        centralizerWithin V
          ((centralizerWithin K W).map e.toMonoidHom) :=
    map_centralizerWithin_equiv e hV
  constructor
  · rw [← hCK, ← hCV, hW.1]
  · let C : Subgroup G := centralizerWithin K W
    have hCKle : C ≤ K := centralizerWithin_le_left _ _
    have hCmapK : C.map e.toMonoidHom ≤ K := by
      rw [show C.map e.toMonoidHom =
          centralizerWithin K (W.map e.toMonoidHom) from hCK]
      exact centralizerWithin_le_left _ _
    let eK : K ≃* K :=
      ((MulAut.conj g).subgroupMap K).trans
        (MulEquiv.subgroupCongr hK)
    have hcomp :
        K.subtype.comp eK.toMonoidHom =
          e.toMonoidHom.comp K.subtype := by
      ext x
      rfl
    have hsub :
        (C.subgroupOf K).map eK.toMonoidHom =
          (C.map e.toMonoidHom).subgroupOf K := by
      apply Subgroup.map_injective K.subtype_injective
      calc
        ((C.subgroupOf K).map eK.toMonoidHom).map K.subtype =
            (C.subgroupOf K).map
              (K.subtype.comp eK.toMonoidHom) := by
                rw [Subgroup.map_map]
        _ = (C.subgroupOf K).map
              (e.toMonoidHom.comp K.subtype) := by rw [hcomp]
        _ = ((C.subgroupOf K).map K.subtype).map
              e.toMonoidHom := by rw [Subgroup.map_map]
        _ = C.map e.toMonoidHom := by
              rw [Subgroup.map_subgroupOf_eq_of_le hCKle]
        _ = ((C.map e.toMonoidHom).subgroupOf K).map
              K.subtype :=
            (Subgroup.map_subgroupOf_eq_of_le hCmapK).symm
    have hc :
        IsCoatom ((C.subgroupOf K).map eK.toMonoidHom) :=
      (OrderIso.isCoatom_iff eK.mapSubgroup (C.subgroupOf K)).mpr (by
        simpa only [C] using hW.2)
    rw [hsub, show C.map e.toMonoidHom =
      centralizerWithin K (W.map e.toMonoidHom) from hCK] at hc
    exact hc

@[reducible] private def centralizerBlocksConjAction
    {G : Type u} [Group G]
    (V K L : Subgroup G)
    (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hLK : L ≤ Subgroup.normalizer (K : Set G)) :
    MulAction L (CentralizerBlocks V K) where
  smul x W :=
    ⟨W.1.map (MulAut.conj (x : G)).toMonoidHom,
      centralizerBlock_map_conj (x : G)
        (Subgroup.mem_normalizer_iff_map_conj_eq.mp
          (hLV x.2))
        (Subgroup.mem_normalizer_iff_map_conj_eq.mp
          (hLK x.2))
        W.2⟩
  one_smul W := by
    apply Subtype.ext
    change W.1.map (MulAut.conj (1 : G)).toMonoidHom = W.1
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (Subgroup.one_mem _)
  mul_smul x y W := by
    apply Subtype.ext
    change
      W.1.map
          (MulAut.conj ((x : G) * (y : G))).toMonoidHom =
        (W.1.map (MulAut.conj (y : G)).toMonoidHom).map
          (MulAut.conj (x : G)).toMonoidHom
    rw [Subgroup.map_map]
    ext z
    simp [MulAut.conj_apply, mul_assoc]

private theorem left_le_normalizer_centralizerBlock
    {G : Type u} [Group G]
    {V K : Subgroup G} [IsMulCommutative V]
    (W : CentralizerBlocks V K) :
    V ≤ Subgroup.normalizer (W.1 : Set G) :=
  (Subgroup.le_centralizer V).trans <|
    (Subgroup.centralizer_le
      (centralizerBlock_le_left W)).trans <|
        Subgroup.centralizer_le_normalizer (W.1 : Set G)

private theorem right_le_normalizer_centralizerBlock
    {G : Type u} [Group G]
    {V K : Subgroup G} [IsMulCommutative K]
    (hKV : K ≤ Subgroup.normalizer (V : Set G))
    (W : CentralizerBlocks V K) :
    K ≤ Subgroup.normalizer (W.1 : Set G) := by
  let C : Subgroup G := centralizerWithin K W.1
  have hCK : C ≤ K := centralizerWithin_le_left _ _
  have hKnormC : K ≤ Subgroup.normalizer (C : Set G) :=
    (Subgroup.le_centralizer K).trans <|
      (Subgroup.centralizer_le hCK).trans <|
        Subgroup.centralizer_le_normalizer (C : Set G)
  intro k hk
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  let e : G ≃* G := MulAut.conj k
  have hVmap :
      V.map e.toMonoidHom = V :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hKV hk)
  have hCmap :
      C.map e.toMonoidHom = C :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hKnormC hk)
  calc
    W.1.map e.toMonoidHom =
        (centralizerWithin V C).map e.toMonoidHom :=
      congrArg (Subgroup.map e.toMonoidHom) W.2.1.symm
    _ = centralizerWithin V (C.map e.toMonoidHom) :=
      map_centralizerWithin_equiv e hVmap
    _ = centralizerWithin V C := by rw [hCmap]
    _ = W.1 := W.2.1

/-- The span of an action-stable family of blocks is normal once the
blockwise normalizers and the acting subgroup generate the ambient group. -/
private theorem stableBlockSpan_normal
    {G : Type u} [Group G]
    {L B : Subgroup G}
    {Ω : Type v} [MulAction L Ω]
    (F : Ω → Subgroup G)
    (hconj : ∀ x : L, ∀ W : Ω,
      F (x • W) =
        (F W).map (MulAut.conj (x : G)).toMonoidHom)
    (hBnorm : ∀ W : Ω,
      B ≤ Subgroup.normalizer (F W : Set G))
    (hgen : B ⊔ L = ⊤)
    (D : Set Ω)
    (hD : ∀ x : L, Set.MapsTo (x • ·) D D) :
    ((⨆ W : Ω, ⨆ (_ : W ∈ D), F W) :
      Subgroup G).Normal := by
  let S : Subgroup G := ⨆ W : Ω, ⨆ (_ : W ∈ D), F W
  have hBn : B ≤ Subgroup.normalizer (S : Set G) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    dsimp only [S]
    rw [Subgroup.map_iSup]
    apply iSup_congr
    intro W
    rw [Subgroup.map_iSup]
    apply iSup_congr
    intro _
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (hBnorm W hb)
  have hLn : L ≤ Subgroup.normalizer (S : Set G) := by
    intro g hg
    let x : L := ⟨g, hg⟩
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    apply le_antisymm
    · dsimp only [S]
      rw [Subgroup.map_iSup]
      refine iSup_le fun W => ?_
      rw [Subgroup.map_iSup]
      refine iSup_le fun hWD => ?_
      calc
        (F W).map (MulAut.conj (x : G)).toMonoidHom =
            F (x • W) := (hconj x W).symm
        _ ≤ ⨆ Y : Ω, ⨆ (_ : Y ∈ D), F Y :=
          le_iSup_of_le (x • W) <|
            le_iSup_of_le (hD x hWD) le_rfl
    · change
        (⨆ W : Ω, ⨆ (_ : W ∈ D), F W) ≤
          S.map (MulAut.conj (x : G)).toMonoidHom
      refine iSup_le fun W => iSup_le fun hWD => ?_
      have hxD : x⁻¹ • W ∈ D := hD x⁻¹ hWD
      have hle : F (x⁻¹ • W) ≤ S :=
        le_iSup_of_le (x⁻¹ • W) <|
          le_iSup_of_le hxD le_rfl
      calc
        F W = F (x • (x⁻¹ • W)) := by simp
        _ = (F (x⁻¹ • W)).map
            (MulAut.conj (x : G)).toMonoidHom :=
          hconj x (x⁻¹ • W)
        _ ≤ S.map (MulAut.conj (x : G)).toMonoidHom :=
          Subgroup.map_mono hle
  apply Subgroup.normalizer_eq_top_iff.mp
  apply top_unique
  rw [← hgen]
  exact sup_le hBn hLn

/-- Independent spanning blocks in an ambient-normal indecomposable factor
form one orbit under any action for which stable block spans are normal. -/
private theorem centralizerBlocks_pretransitive_of_independent_spanning
    {G : Type u} [Group G]
    {Q : Type v} [Group Q] [Finite Q]
    {V K : Subgroup G} [IsMulCommutative V]
    [MulAction Q (CentralizerBlocks V K)]
    (hindecomp : NormalIndecomposableFactor V)
    (hind : iSupIndep
      (fun W : CentralizerBlocks V K => W.1))
    (hspan :
      (⨆ W : CentralizerBlocks V K, W.1) = V)
    (hnormal : ∀ D : Set (CentralizerBlocks V K),
      (∀ q : Q, Set.MapsTo (q • ·) D D) →
      ((⨆ W : CentralizerBlocks V K,
          ⨆ (_ : W ∈ D), W.1) : Subgroup G).Normal) :
    MulAction.IsPretransitive Q (CentralizerBlocks V K) := by
  let Ω := CentralizerBlocks V K
  let F : Ω → Set.Iic V :=
    fun W => ⟨W.1, centralizerBlock_le_left W⟩
  have hindF : iSupIndep F := by
    apply iSupIndep.of_coe_Iic_comp
    simpa [F, Function.comp_def] using hind
  have hindV :
      iSupIndep (fun W : Ω => W.1.subgroupOf V) := by
    have h := iSupIndep.map_orderIso
      (Subgroup.MapSubtype.orderIso V).symm hindF
    change iSupIndep (fun W : Ω => W.1.subgroupOf V) at h
    exact h
  have htopmap :
      (⊤ : Subgroup V).map V.subtype = V :=
    (MonoidHom.range_eq_map V.subtype).symm.trans V.range_subtype
  have hmapAll :
      ((⨆ W : Ω, W.1.subgroupOf V) : Subgroup V).map
          V.subtype =
        ⨆ W : Ω, W.1 := by
    rw [Subgroup.map_iSup]
    apply iSup_congr
    intro W
    exact Subgroup.map_subgroupOf_eq_of_le
      (centralizerBlock_le_left W)
  have hspanV :
      (⨆ W : Ω, W.1.subgroupOf V) = ⊤ := by
    apply Subgroup.map_injective V.subtype_injective
    rw [hmapAll, hspan, htopmap]
  refine ⟨fun W₀ W₁ => ?_⟩
  let O : Set Ω := MulAction.orbit Q W₀
  let U : Subgroup G :=
    ⨆ W : Ω, ⨆ (_ : W ∈ O), W.1
  let T : Subgroup G :=
    ⨆ W : Ω, ⨆ (_ : W ∉ O), W.1
  let UV : Subgroup V :=
    ⨆ W : Ω, ⨆ (_ : W ∈ O), W.1.subgroupOf V
  let TV : Subgroup V :=
    ⨆ W : Ω, ⨆ (_ : W ∉ O), W.1.subgroupOf V
  have hmapPart (D : Set Ω) :
      ((⨆ W : Ω, ⨆ (_ : W ∈ D), W.1.subgroupOf V) :
          Subgroup V).map V.subtype =
        ⨆ W : Ω, ⨆ (_ : W ∈ D), W.1 := by
    rw [Subgroup.map_iSup]
    apply iSup_congr
    intro W
    rw [Subgroup.map_iSup]
    apply iSup_congr
    intro _
    exact Subgroup.map_subgroupOf_eq_of_le
      (centralizerBlock_le_left W)
  have hUmap : UV.map V.subtype = U := hmapPart O
  have hTmap : TV.map V.subtype = T := by
    simpa only [Set.mem_compl_iff] using hmapPart Oᶜ
  have hpart :
      UV ⊔ TV = ⨆ W : Ω, W.1.subgroupOf V := by
    apply le_antisymm
    · apply sup_le
      · refine iSup_le fun W => iSup_le fun _ => ?_
        exact le_iSup (fun Y : Ω => Y.1.subgroupOf V) W
      · refine iSup_le fun W => iSup_le fun _ => ?_
        exact le_iSup (fun Y : Ω => Y.1.subgroupOf V) W
    · refine iSup_le fun W => ?_
      by_cases hWO : W ∈ O
      · exact le_sup_of_le_left <|
          le_iSup_of_le W <| le_iSup_of_le hWO le_rfl
      · exact le_sup_of_le_right <|
          le_iSup_of_le W <| le_iSup_of_le hWO le_rfl
  have hsupV : UV ⊔ TV = ⊤ := hpart.trans hspanV
  have hOfin : O.Finite := by
    simpa [O, MulAction.orbit] using
      (Set.finite_range (fun q : Q => q • W₀))
  have hdisV : Disjoint UV TV := by
    simpa only [Set.mem_compl_iff] using
      (iSupIndep.disjoint_biSup_biSup'
        hindV
        (show Disjoint O Oᶜ from disjoint_compl_right)
        hOfin)
  have hdis : Disjoint U T := by
    rw [← hUmap, ← hTmap]
    exact Subgroup.disjoint_map V.subtype_injective hdisV
  have hsup : U ⊔ T = V := by
    calc
      U ⊔ T =
          UV.map V.subtype ⊔ TV.map V.subtype := by
            rw [hUmap, hTmap]
      _ = (UV ⊔ TV).map V.subtype :=
        (Subgroup.map_sup UV TV V.subtype).symm
      _ = (⊤ : Subgroup V).map V.subtype := by rw [hsupV]
      _ = V := htopmap
  have hOstable :
      ∀ q : Q, Set.MapsTo (q • ·) O O :=
    fun q _ h => MulAction.mem_orbit_of_mem_orbit q h
  have hOcstable :
      ∀ q : Q, Set.MapsTo (q • ·) Oᶜ Oᶜ := by
    intro q W hW
    rw [Set.mem_compl_iff] at hW ⊢
    intro hqW
    apply hW
    have hback :=
      MulAction.mem_orbit_of_mem_orbit q⁻¹ hqW
    simpa using hback
  have hUnormal : U.Normal := by
    dsimp only [U]
    exact hnormal O hOstable
  have hTnormal : T.Normal := by
    dsimp only [T]
    simpa only [Set.mem_compl_iff] using
      hnormal Oᶜ hOcstable
  have hW₀U : W₀.1 ≤ U :=
    le_iSup_of_le W₀ <|
      le_iSup_of_le (MulAction.mem_orbit_self W₀) le_rfl
  have hUne : U ≠ ⊥ := by
    intro hU
    apply centralizerBlock_ne_bot W₀
    apply le_antisymm
    · rw [← hU]
      exact hW₀U
    · exact bot_le
  have hUV : U = V := by
    rcases hindecomp U T hUnormal hTnormal hsup hdis with
      hbot | hUV
    · exact (hUne hbot).elim
    · exact hUV
  have hW₁O : W₁ ∈ O := by
    by_contra hnot
    have hW₁T : W₁.1 ≤ T :=
      le_iSup_of_le W₁ <| le_iSup_of_le hnot le_rfl
    have hW₁U : W₁.1 ≤ U := by
      rw [hUV]
      exact centralizerBlock_le_left W₁
    have hlebot : W₁.1 ≤ ⊥ := by
      rw [← hdis.eq_bot]
      exact le_inf hW₁U hW₁T
    exact centralizerBlock_ne_bot W₁
      (le_bot_iff.mp hlebot)
  exact MulAction.mem_orbit_iff.mp hW₁O

private theorem centralizerBlocks_iSupIndep_subgroupOf
    {G : Type u} [Group G]
    {V K : Subgroup G} [IsMulCommutative V]
    (hind : iSupIndep
      (fun W : CentralizerBlocks V K => W.1)) :
    iSupIndep
      (fun W : CentralizerBlocks V K => W.1.subgroupOf V) := by
  let F : CentralizerBlocks V K → Set.Iic V :=
    fun W => ⟨W.1, centralizerBlock_le_left W⟩
  have hindF : iSupIndep F := by
    apply iSupIndep.of_coe_Iic_comp
    simpa [F, Function.comp_def] using hind
  have h := iSupIndep.map_orderIso
    (Subgroup.MapSubtype.orderIso V).symm hindF
  change iSupIndep
    (fun W : CentralizerBlocks V K => W.1.subgroupOf V) at h
  exact h

/-- Norm control for a nonfixed centralizer block under a prime-order
conjugation action. -/
private theorem nonfixed_centralizerBlock_card_and_fixed_le_orbitSpan
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime]
    (V K R : Subgroup G) [IsMulCommutative V]
    [MulAction R (CentralizerBlocks V K)]
    [MulDistribMulAction R V]
    (hblockSmul : ∀ (r : R) (W : CentralizerBlocks V K),
      (r • W).1 =
        W.1.map (MulAut.conj (r : G)).toMonoidHom)
    (hVSmul : ∀ (r : R) (v : V),
      ((r • v : V) : G) =
        (r : G) * (v : G) * (r : G)⁻¹)
    (hRprime : (Nat.card R).Prime)
    (hind : iSupIndep
      (fun W : CentralizerBlocks V K => W.1))
    (hCVRcard : Nat.card (centralizerWithin V R) = p)
    (W : CentralizerBlocks V K)
    (hWnot : W ∉ MulAction.fixedPoints R
      (CentralizerBlocks V K)) :
    Nat.card W.1 = p ∧
      centralizerWithin V R ≤ (⨆ r : R, (r • W).1) := by
  classical
  letI : Fintype R := Fintype.ofFinite R
  have hstab : MulAction.stabilizer R W = ⊥ := by
    letI : Fact (Nat.card R).Prime := ⟨hRprime⟩
    rcases (MulAction.stabilizer R W).eq_bot_or_eq_top_of_prime_card with
      hbot | htop
    · exact hbot
    · exfalso
      apply hWnot
      rw [MulAction.mem_fixedPoints]
      intro r
      have hr : r ∈ MulAction.stabilizer R W := by
        rw [htop]
        trivial
      exact hr
  have horbitInj : Function.Injective (fun r : R => r • W) := by
    intro a b hab
    have hm : b⁻¹ * a ∈ MulAction.stabilizer R W := by
      rw [MulAction.mem_stabilizer_iff]
      calc
        (b⁻¹ * a) • W = b⁻¹ • (a • W) := by rw [mul_smul]
        _ = b⁻¹ • (b • W) :=
          congrArg (fun Z : CentralizerBlocks V K => b⁻¹ • Z) hab
        _ = W := by simp
    rw [hstab] at hm
    have hba : b⁻¹ * a = 1 := Subgroup.mem_bot.mp hm
    exact (inv_mul_eq_one.mp hba).symm
  let B : R → Subgroup V :=
    fun r => (r • W).1.subgroupOf V
  have hindV := centralizerBlocks_iSupIndep_subgroupOf hind
  have hindB : iSupIndep B := by
    simpa [B, Function.comp_def] using hindV.comp horbitInj
  let WV : Subgroup V := W.1.subgroupOf V
  have hWVne : WV ≠ ⊥ := by
    intro hbot
    apply centralizerBlock_ne_bot W
    calc
      W.1 = WV.map V.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le
          (centralizerBlock_le_left W)).symm
      _ = (⊥ : Subgroup V).map V.subtype := by rw [hbot]
      _ = ⊥ := Subgroup.map_bot V.subtype
  have htranslate : ∀ r : R, ∀ a : V,
      a ∈ WV → r • a ∈ B r := by
    intro r a ha
    change ((r • a : V) : G) ∈ (r • W).1
    rw [hblockSmul r W, hVSmul r a]
    exact ⟨(a : G), ha, rfl⟩
  have hfixedMap := map_fixedPoints_eq_centralizerWithin hVSmul
  have hfixedCard : Nat.card (FixedPoints.subgroup R V) = p := by
    have hc := Subgroup.card_map_of_injective
      (K := FixedPoints.subgroup R V) V.subtype_injective
    rw [hfixedMap] at hc
    exact hc.symm.trans hCVRcard
  have hnorm := actionNorm_independent_family_card_and_fixed_le
    WV B hWVne hindB htranslate hfixedCard
  have hWcard : Nat.card W.1 = p :=
    (natCard_subgroupOf_eq
      (centralizerBlock_le_left W)).symm.trans hnorm.1
  have hmapRange :
      ((⨆ r : R, B r) : Subgroup V).map V.subtype =
        ⨆ r : R, (r • W).1 := by
    rw [Subgroup.map_iSup]
    apply iSup_congr
    intro r
    exact Subgroup.map_subgroupOf_eq_of_le
      (centralizerBlock_le_left (r • W))
  have hle :
      (FixedPoints.subgroup R V).map V.subtype ≤
        ((⨆ r : R, B r) : Subgroup V).map V.subtype :=
    Subgroup.map_mono hnorm.2
  rw [hfixedMap, hmapRange] at hle
  exact ⟨hWcard, hle⟩

/-- The terminal centralizer-block contradiction in the reduced case of
Bender--Glauberman Theorem 3.6. -/
private theorem false_of_final_centralizerBlock_configuration
    {G : Type u} [Group G] [Finite G]
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (V K P R : Subgroup G)
    (hVelem : IsElementaryAbelianGroup p V)
    (hKelem : IsElementaryAbelianGroup q K)
    (hVne : V ≠ ⊥)
    (hCVK : centralizerWithin V K = ⊥)
    (hCKV : centralizerWithin K V = ⊥)
    (hKV : K ≤ Subgroup.normalizer (V : Set G))
    (hPnormV : P ≤ Subgroup.normalizer (V : Set G))
    (hRnormV : R ≤ Subgroup.normalizer (V : Set G))
    (hPnormK : P ≤ Subgroup.normalizer (K : Set G))
    (hRnormK : R ≤ Subgroup.normalizer (K : Set G))
    (hPp : IsPGroup p P)
    (hRprime : (Nat.card R).Prime)
    (hpR : p ≠ Nat.card R)
    (hcopVK : Nat.Coprime (Nat.card V) (Nat.card K))
    (hcopKR : Nat.Coprime (Nat.card K) (Nat.card R))
    (hCVRcard : Nat.card (centralizerWithin V R) = p)
    (hCKRcard : Nat.card (centralizerWithin K R) = q)
    (hKP : ⁅K, P⁆ = K)
    (hPR : ⁅P, R⁆ = P)
    (hKlarge : q ^ 2 < Nat.card K)
    (hindecomp : NormalIndecomposableFactor V)
    (hgenerated : (V ⊔ K) ⊔ (P ⊔ R) = ⊤)
    (hodd : Odd (Nat.card G)) :
    False := by
  classical
  letI : IsMulCommutative V := hVelem.commutative
  letI : IsMulCommutative K := hKelem.commutative
  have hKncyc : ¬ IsCyclic K :=
    not_isCyclic_of_elementaryAbelian_card_gt_sq hKelem hKlarge
  have hVsol : IsSolvable V := by
    letI : Group.IsNilpotent V := hVelem.isPGroup.isNilpotent
    infer_instance
  have hblocksSpanSet := centralizerBlocks_span V K hKelem hKncyc
    hKV hcopVK hVsol hCVK
  have hblocksIndepSet := centralizerBlocks_sSupIndep
    V K hVelem.commutative hKelem.commutative hKV hCVK
  have hblocksSpan :
      (⨆ W : CentralizerBlocks V K, W.1) = V := by
    calc
      (⨆ W : CentralizerBlocks V K, W.1) =
          sSup {W : Subgroup G | IsCentralizerBlock V K W} :=
        (sSup_eq_iSup'
          {W : Subgroup G | IsCentralizerBlock V K W}).symm
      _ = V := hblocksSpanSet
  have hblocksIndep :
      iSupIndep (fun W : CentralizerBlocks V K => W.1) := by
    exact (sSupIndep_iff _).mp hblocksIndepSet
  have hΩnonempty : Nonempty (CentralizerBlocks V K) := by
    by_contra hempty
    haveI : IsEmpty (CentralizerBlocks V K) :=
      not_nonempty_iff.mp hempty
    apply hVne
    rw [← hblocksSpan]
    simp
  letI : Nonempty (CentralizerBlocks V K) := hΩnonempty
  let L : Subgroup G := P ⊔ R
  have hLnormV : L ≤ Subgroup.normalizer (V : Set G) :=
    sup_le hPnormV hRnormV
  have hLnormK : L ≤ Subgroup.normalizer (K : Set G) :=
    sup_le hPnormK hRnormK
  letI : MulAction L (CentralizerBlocks V K) :=
    centralizerBlocksConjAction V K L hLnormV hLnormK
  letI : MulAction P (CentralizerBlocks V K) :=
    centralizerBlocksConjAction V K P hPnormV hPnormK
  letI : MulAction R (CentralizerBlocks V K) :=
    centralizerBlocksConjAction V K R hRnormV hRnormK
  have hBnorm (W : CentralizerBlocks V K) :
      V ⊔ K ≤ Subgroup.normalizer (W.1 : Set G) :=
    sup_le
      (left_le_normalizer_centralizerBlock W)
      (right_le_normalizer_centralizerBlock hKV W)
  have hnormal : ∀ D : Set (CentralizerBlocks V K),
      (∀ l : L, Set.MapsTo (l • ·) D D) →
      ((⨆ W : CentralizerBlocks V K,
          ⨆ (_ : W ∈ D), W.1) : Subgroup G).Normal := by
    intro D hD
    exact stableBlockSpan_normal
      (L := L) (B := V ⊔ K)
      (F := fun W : CentralizerBlocks V K => W.1)
      (fun _ _ => rfl) hBnorm hgenerated D hD
  letI : MulAction.IsPretransitive L (CentralizerBlocks V K) :=
    centralizerBlocks_pretransitive_of_independent_spanning
      hindecomp hblocksIndep hblocksSpan hnormal
  have hRnotall : ¬ ∀ W : CentralizerBlocks V K,
      W ∈ MulAction.fixedPoints R (CentralizerBlocks V K) := by
    intro hRall
    let φ : L →* Equiv.Perm (CentralizerBlocks V K) :=
      MulAction.toPermHom L (CentralizerBlocks V K)
    let PL : Subgroup L := P.subgroupOf L
    let RL : Subgroup L := R.subgroupOf L
    have hPL : P ≤ L := le_sup_left
    have hRL : R ≤ L := le_sup_right
    have hPLRL : PL ⊔ RL = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hPL hRL]
      exact Subgroup.subgroupOf_self L
    have hPRL : ⁅PL, RL⁆ = PL := by
      rw [← subgroupOf_commutator_eq hPL hRL, hPR]
    have hRLker : RL ≤ φ.ker := by
      intro r hr
      rw [MonoidHom.mem_ker]
      apply Equiv.ext
      intro W
      let rr : R := ⟨(((r : L) : G)), hr⟩
      have hfix :=
        (MulAction.mem_fixedPoints.mp (hRall W)) rr
      apply Subtype.ext
      change W.1.map (MulAut.conj (((r : L) : G))).toMonoidHom = W.1
      exact congrArg Subtype.val hfix
    have hPLker : PL ≤ φ.ker := by
      rw [← hPRL]
      exact (Subgroup.commutator_mono le_rfl hRLker).trans
        (Subgroup.commutator_le_right PL φ.ker)
    have hkerTop : φ.ker = ⊤ := by
      apply top_unique
      rw [← hPLRL]
      exact sup_le hPLker hRLker
    have htriv (l : L) (W : CentralizerBlocks V K) :
        l • W = W := by
      have hl : l ∈ φ.ker := by
        rw [hkerTop]
        trivial
      rw [MonoidHom.mem_ker] at hl
      change φ l W = W
      rw [hl]
      rfl
    let W₀ : CentralizerBlocks V K := Classical.choice hΩnonempty
    have hsubsingleton : Subsingleton (CentralizerBlocks V K) :=
      ⟨fun W Y => by
        obtain ⟨l, hl⟩ :=
          MulAction.exists_smul_eq L W Y
        rw [htriv l W] at hl
        exact hl⟩
    letI : Subsingleton (CentralizerBlocks V K) := hsubsingleton
    have hiSup :
        (⨆ W : CentralizerBlocks V K, W.1) = W₀.1 := by
      apply le_antisymm
      · refine iSup_le fun W => ?_
        rw [Subsingleton.elim W W₀]
      · exact le_iSup (fun W : CentralizerBlocks V K => W.1) W₀
    have hW₀V : W₀.1 = V := hiSup.symm.trans hblocksSpan
    have hcoatomBot : IsCoatom (⊥ : Subgroup K) := by
      have hCKW : centralizerWithin K W₀.1 = ⊥ := by
        rw [hW₀V, hCKV]
      simpa only [hCKW, Subgroup.bot_subgroupOf] using W₀.2.2
    have hKcard : Nat.card K = q := by
      rw [← Nat.card_congr QuotientGroup.quotientBot.toEquiv]
      exact
        hKelem.isPGroup.card_quotient_isCoatom hcoatomBot
    rw [hKcard] at hKlarge
    nlinarith [(Fact.out : q.Prime).pos]
  obtain ⟨W₁, hW₁not⟩ := not_forall.mp hRnotall
  let actV : R →* MulAut V :=
    V.normalizerMonoidHom.comp (Subgroup.inclusion hRnormV)
  letI : MulDistribMulAction R V :=
    MulDistribMulAction.compHom V actV
  have hVSmul (r : R) (v : V) :
      ((r • v : V) : G) =
        (r : G) * (v : G) * (r : G)⁻¹ := by
    rfl
  have hW₁norm :=
    nonfixed_centralizerBlock_card_and_fixed_le_orbitSpan
      V K R (fun _ _ => rfl) hVSmul hRprime
      hblocksIndep hCVRcard W₁ hW₁not
  have hblockCard (W : CentralizerBlocks V K) :
      Nat.card W.1 = p := by
    obtain ⟨l, hl⟩ := MulAction.exists_smul_eq L W₁ W
    have hc :
        Nat.card (W₁.1.map (MulAut.conj (l : G)).toMonoidHom) =
          Nat.card W₁.1 :=
      Subgroup.card_map_of_injective (MulAut.conj (l : G)).injective
    change Nat.card (l • W₁).1 = Nat.card W₁.1 at hc
    rw [hl] at hc
    exact hc.trans hW₁norm.1
  have hPnoFixed (W : CentralizerBlocks V K) :
      W ∉ MulAction.fixedPoints P (CentralizerBlocks V K) := by
    intro hWfix
    have hPnormW : P ≤ Subgroup.normalizer (W.1 : Set G) := by
      intro x hx
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      let xx : P := ⟨x, hx⟩
      have hfix := (MulAction.mem_fixedPoints.mp hWfix) xx
      exact congrArg Subtype.val hfix
    have hWcyc : IsCyclic W.1 := isCyclic_of_prime_card (hblockCard W)
    have hKcentW : K ≤ Subgroup.centralizer (W.1 : Set G) := by
      calc
        K = ⁅K, P⁆ := hKP.symm
        _ ≤ Subgroup.centralizer (W.1 : Set G) :=
          commutator_le_centralizer_of_normalizes_isCyclic
            W.1 K P hWcyc
            (right_le_normalizer_centralizerBlock hKV W) hPnormW
    have hWCVK : W.1 ≤ centralizerWithin V K := by
      intro w hw
      refine ⟨centralizerBlock_le_left W hw, ?_⟩
      intro k hk
      exact (Subgroup.mem_centralizer_iff.mp (hKcentW hk) w hw).symm
    apply centralizerBlock_ne_bot W
    apply le_bot_iff.mp
    simpa only [hCVK] using hWCVK
  have hdecKR :=
    Submission.OddOrder.BG.AppendixC.elementaryAbelian_centralizer_commutator_decomposition
        K R hKelem hRnormK hcopKR
  let D : Set (CentralizerBlocks V K) := MulAction.orbit R W₁
  have houtsideCent (W : CentralizerBlocks V K) (hWout : W ∉ D) :
      centralizerWithin K W.1 = ⁅K, R⁆ := by
    by_cases hWfix : W ∈
        MulAction.fixedPoints R (CentralizerBlocks V K)
    · have hRnormW : R ≤ Subgroup.normalizer (W.1 : Set G) := by
        intro x hx
        rw [Subgroup.mem_normalizer_iff_map_conj_eq]
        let xx : R := ⟨x, hx⟩
        have hfix := (MulAction.mem_fixedPoints.mp hWfix) xx
        exact congrArg Subtype.val hfix
      have hWcyc : IsCyclic W.1 :=
        isCyclic_of_prime_card (hblockCard W)
      have hcommCent : ⁅K, R⁆ ≤
          Subgroup.centralizer (W.1 : Set G) :=
        commutator_le_centralizer_of_normalizes_isCyclic
          W.1 K R hWcyc
          (right_le_normalizer_centralizerBlock hKV W) hRnormW
      have hcommK : ⁅K, R⁆ ≤ K := by
        rw [Subgroup.commutator_comm]
        exact Subgroup.le_normalizer_iff_commutator_le_right.mp hRnormK
      have hcommCKW : ⁅K, R⁆ ≤ centralizerWithin K W.1 :=
        le_inf hcommK hcommCent
      let C : Subgroup K :=
        (centralizerWithin K R).subgroupOf K
      let T : Subgroup K := (⁅K, R⁆ : Subgroup G).subgroupOf K
      let M : Subgroup K := (centralizerWithin K W.1).subgroupOf K
      have hTindex : T.index = q := by
        calc
          T.index = Nat.card C := hdecKR.2.index_eq_card
          _ = Nat.card (centralizerWithin K R) :=
            natCard_subgroupOf_eq (centralizerWithin_le_left K R)
          _ = q := hCKRcard
      have hMindex : M.index = q := by
        rw [Subgroup.index_eq_card]
        exact hKelem.isPGroup.card_quotient_isCoatom W.2.2
      have hcardTM : Nat.card T = Nat.card M := by
        apply Nat.mul_right_cancel (Fact.out : q.Prime).pos
        calc
          Nat.card T * q = Nat.card T * T.index := by rw [hTindex]
          _ = Nat.card K := T.card_mul_index
          _ = Nat.card M * M.index := M.card_mul_index.symm
          _ = Nat.card M * q := by rw [hMindex]
      have hTM : T = M :=
        Subgroup.eq_of_le_of_card_ge
          (Subgroup.subgroupOf_mono K hcommCKW) hcardTM.ge
      simpa only [T, M,
        Subgroup.map_subgroupOf_eq_of_le hcommK,
        Subgroup.map_subgroupOf_eq_of_le
          (centralizerWithin_le_left K W.1)] using
        congrArg (fun X : Subgroup K => X.map K.subtype) hTM.symm
    · have hWnorm :=
        nonfixed_centralizerBlock_card_and_fixed_le_orbitSpan
          V K R (fun _ _ => rfl) hVSmul hRprime
          hblocksIndep hCVRcard W hWfix
      let O₁ : Set (CentralizerBlocks V K) := MulAction.orbit R W₁
      let OW : Set (CentralizerBlocks V K) := MulAction.orbit R W
      have hOneq : O₁ ≠ OW := by
        intro heq
        apply hWout
        change W ∈ O₁
        rw [heq]
        exact MulAction.mem_orbit_self W
      have hOdis : Disjoint O₁ OW :=
        (MulAction.orbit.eq_or_disjoint W₁ W).resolve_left hOneq
      have hO₁fin : O₁.Finite := by
        simpa [O₁, MulAction.orbit] using
          Set.finite_range (fun r : R => r • W₁)
      have hindV := centralizerBlocks_iSupIndep_subgroupOf hblocksIndep
      let S₁V : Subgroup V :=
        ⨆ X : CentralizerBlocks V K,
          ⨆ (_ : X ∈ O₁), X.1.subgroupOf V
      let SWV : Subgroup V :=
        ⨆ X : CentralizerBlocks V K,
          ⨆ (_ : X ∈ OW), X.1.subgroupOf V
      have hdisV : Disjoint S₁V SWV := by
        exact iSupIndep.disjoint_biSup_biSup'
          hindV hOdis hO₁fin
      have hmapPart (O : Set (CentralizerBlocks V K)) :
          ((⨆ X : CentralizerBlocks V K,
              ⨆ (_ : X ∈ O), X.1.subgroupOf V) : Subgroup V).map
              V.subtype =
            ⨆ X : CentralizerBlocks V K, ⨆ (_ : X ∈ O), X.1 := by
        rw [Subgroup.map_iSup]
        apply iSup_congr
        intro X
        rw [Subgroup.map_iSup]
        apply iSup_congr
        intro _
        exact Subgroup.map_subgroupOf_eq_of_le
          (centralizerBlock_le_left X)
      have hS₁map : S₁V.map V.subtype =
          ⨆ X : CentralizerBlocks V K, ⨆ (_ : X ∈ O₁), X.1 :=
        hmapPart O₁
      have hSWmap : SWV.map V.subtype =
          ⨆ X : CentralizerBlocks V K, ⨆ (_ : X ∈ OW), X.1 :=
        hmapPart OW
      have hdisG : Disjoint
          (⨆ X : CentralizerBlocks V K, ⨆ (_ : X ∈ O₁), X.1)
          (⨆ X : CentralizerBlocks V K, ⨆ (_ : X ∈ OW), X.1) := by
        rw [← hS₁map, ← hSWmap]
        exact Subgroup.disjoint_map V.subtype_injective hdisV
      have hC₁ : centralizerWithin V R ≤
          ⨆ X : CentralizerBlocks V K, ⨆ (_ : X ∈ O₁), X.1 :=
        hW₁norm.2.trans <| iSup_le fun r =>
          le_iSup_of_le (r • W₁) <|
            le_iSup_of_le (show r • W₁ ∈ O₁ from ⟨r, rfl⟩) le_rfl
      have hCW : centralizerWithin V R ≤
          ⨆ X : CentralizerBlocks V K, ⨆ (_ : X ∈ OW), X.1 :=
        hWnorm.2.trans <| iSup_le fun r =>
          le_iSup_of_le (r • W) <|
            le_iSup_of_le (show r • W ∈ OW from ⟨r, rfl⟩) le_rfl
      have hCbot : centralizerWithin V R = ⊥ := by
        apply le_bot_iff.mp
        rw [← hdisG.eq_bot]
        exact le_inf hC₁ hCW
      have hcardOne : Nat.card (centralizerWithin V R) = 1 := by
        rw [hCbot]
        exact Subgroup.card_bot
      rw [hCVRcard] at hcardOne
      exfalso
      exact (Fact.out : p.Prime).ne_one hcardOne
  have huniqOutside : ∀ W ∈ Dᶜ, ∀ Y ∈ Dᶜ, W = Y := by
    intro W hW Y hY
    rw [Set.mem_compl_iff] at hW hY
    apply Subtype.ext
    calc
      W.1 = centralizerWithin V (centralizerWithin K W.1) := W.2.1.symm
      _ = centralizerWithin V ⁅K, R⁆ := by rw [houtsideCent W hW]
      _ = centralizerWithin V (centralizerWithin K Y.1) := by
        rw [houtsideCent Y hY]
      _ = Y.1 := Y.2.1
  have hLodd : Odd (Nat.card L) :=
    hodd.of_dvd_nat L.card_subgroup_dvd_card
  have hRodd : Odd (Nat.card R) :=
    hodd.of_dvd_nat R.card_subgroup_dvd_card
  exact false_of_prime_orbit_with_singleton_compl
    (L := L) (P := P) (R := R)
    hLodd hPp hRprime hRodd hpR W₁ hW₁not
    hPnoFixed huniqOutside

end CentralizerBlockArithmetic

section HallFrattiniHelpers

/-- Frattini's argument for a solvable normal Hall factor: if `K` is a
complement to `V` inside the ambient-normal subgroup `U`, then `U` together
with the ambient normalizer of `K` generates the whole group. -/
private theorem normal_sup_normalizer_eq_top_of_solvable_complement
    {A : Type u} [Group A] [Finite A]
    (U V K : Subgroup A) [U.Normal] [V.Normal] [IsSolvable V]
    (hVU : V ≤ U) (hKU : K ≤ U)
    (hcomp : (V.subgroupOf U).IsComplement' (K.subgroupOf U))
    (hcop : Nat.Coprime (Nat.card V) (Nat.card K)) :
    U ⊔ Subgroup.normalizer (K : Set A) = ⊤ := by
  classical
  let VU : Subgroup U := V.subgroupOf U
  let KU : Subgroup U := K.subgroupOf U
  letI : VU.Normal :=
    Subgroup.Normal.subgroupOf (inferInstance : V.Normal) U
  let eVU : VU ≃* V := Subgroup.subgroupOfEquivOfLe hVU
  letI : IsSolvable VU :=
    solvable_of_solvable_injective
      (f := eVU.toMonoidHom) eVU.injective
  have hcardVU : Nat.card VU = Nat.card V :=
    natCard_subgroupOf_eq hVU
  have hcardKU : Nat.card KU = Nat.card K :=
    natCard_subgroupOf_eq hKU
  have hcopIndex : Nat.Coprime (Nat.card VU) VU.index := by
    rw [hcomp.symm.index_eq_card, hcardVU, hcardKU]
    exact hcop
  apply top_unique
  intro a _
  have hUmap :
      U.map (MulAut.conj a).toMonoidHom = U :=
    Subgroup.Normal.map_conj_eq U a
  have hKaU : K.map (MulAut.conj a).toMonoidHom ≤ U := by
    calc
      K.map (MulAut.conj a).toMonoidHom ≤
          U.map (MulAut.conj a).toMonoidHom := Subgroup.map_mono hKU
      _ = U := hUmap
  let C : Subgroup U :=
    (K.map (MulAut.conj a).toMonoidHom).subgroupOf U
  have hcardC : Nat.card C = Nat.card K := by
    calc
      Nat.card C =
          Nat.card (K.map (MulAut.conj a).toMonoidHom) :=
        natCard_subgroupOf_eq hKaU
      _ = Nat.card K :=
        Subgroup.card_map_of_injective (MulAut.conj a).injective
  have hdisC : Disjoint VU C := by
    apply Subgroup.disjoint_of_coprime_natCard
    rw [hcardVU, hcardC]
    exact hcop
  have hcardComp : Nat.card VU * Nat.card C = Nat.card U := by
    calc
      Nat.card VU * Nat.card C = Nat.card VU * Nat.card K := by
        rw [hcardC]
      _ = Nat.card VU * Nat.card KU := by rw [hcardKU]
      _ = Nat.card U := hcomp.card_mul
  have hCcomp : VU.IsComplement' C :=
    Subgroup.isComplement'_of_card_mul_and_disjoint hcardComp hdisC
  obtain ⟨v, hv⟩ :=
    Subgroup.solvable_complement_conjugacy
      hcopIndex hcomp hCcomp
  have hvAmbient :
      K.map (MulAut.conj a).toMonoidHom =
        K.map (MulAut.conj ((v : U) : A)).toMonoidHom := by
    have hvMap :=
      congrArg (fun S : Subgroup U => S.map U.subtype) hv
    have hcompConj :
        U.subtype.comp (MulAut.conj (v : U)).toMonoidHom =
          (MulAut.conj ((v : U) : A)).toMonoidHom.comp U.subtype := by
      ext x
      rfl
    dsimp only [C, KU] at hvMap
    rw [Subgroup.map_subgroupOf_eq_of_le hKaU, Subgroup.map_map,
      hcompConj, ← Subgroup.map_map,
      Subgroup.map_subgroupOf_eq_of_le hKU] at hvMap
    simpa using hvMap
  let n : A := ((v : U) : A)⁻¹ * a
  have hn : n ∈ Subgroup.normalizer (K : Set A) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    calc
      K.map (MulAut.conj n).toMonoidHom =
          (K.map (MulAut.conj a).toMonoidHom).map
            (MulAut.conj ((v : U) : A)⁻¹).toMonoidHom := by
        rw [Subgroup.map_map]
        ext x
        simp [n, MulAut.conj_apply, mul_assoc]
      _ = (K.map (MulAut.conj ((v : U) : A)).toMonoidHom).map
            (MulAut.conj ((v : U) : A)⁻¹).toMonoidHom := by
        rw [hvAmbient]
      _ = K := by
        rw [Subgroup.map_map]
        have hcompId :
            (MulAut.conj ((v : U) : A)⁻¹).toMonoidHom.comp
                (MulAut.conj ((v : U) : A)).toMonoidHom =
              MonoidHom.id A := by
          ext x
          simp [MulAut.conj_apply, mul_assoc]
        rw [hcompId, Subgroup.map_id]
  have hvU : ((v : U) : A) ∈ U := (v : U).property
  have hprod : ((v : U) : A) * n ∈
      U ⊔ Subgroup.normalizer (K : Set A) :=
    Subgroup.mul_mem_sup hvU hn
  simpa [n] using hprod

/-- Lifting a Sylow subgroup from `N` across a normal `p`-subgroup `V`
when `V ⊔ N = H`. -/
private theorem exists_sylow_map_eq_sup_of_normal_sup_eq
    {A : Type u} [Group A] [Finite A]
    {p : ℕ} [Fact p.Prime]
    (H V N P : Subgroup A) [V.Normal]
    (hVH : V ≤ H) (hNH : N ≤ H) (hVN : V ⊔ N = H)
    (hVp : IsPGroup p V) (PN : Sylow p N)
    (hP : P = (PN : Subgroup N).map N.subtype) :
    ∃ S : Sylow p H,
      (S : Subgroup H).map H.subtype = V ⊔ P := by
  let VH : Subgroup H := V.subgroupOf H
  letI : VH.Normal := Subgroup.Normal.subgroupOf
    (inferInstance : V.Normal) H
  let iN : N →* H := Subgroup.inclusion hNH
  let qH : H →* H ⧸ VH := QuotientGroup.mk' VH
  let f : N →* H ⧸ VH := qH.comp iN
  have hf : Function.Surjective f := by
    intro z
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective VH z
    have hh : (h : A) ∈ V ⊔ N := by
      rw [hVN]
      exact h.property
    have hprod : (h : A) ∈ (V : Set A) * (N : Set A) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left V N
        (by rw [V.normalizer_eq_top]; exact le_top)]
      exact hh
    obtain ⟨v, hv, n, hn, hvn⟩ := hprod
    let vH : H := ⟨v, hVH hv⟩
    let nH : H := ⟨n, hNH hn⟩
    refine ⟨⟨n, hn⟩, ?_⟩
    change qH nH = qH h
    have hvone : qH vH = 1 :=
      (QuotientGroup.eq_one_iff vH).mpr hv
    have heq : vH * nH = h := Subtype.ext hvn
    rw [← heq, map_mul, hvone, one_mul]
  let Qs : Sylow p (H ⧸ VH) := PN.mapSurjective hf
  have hkerp : IsPGroup p qH.ker := by
    rw [QuotientGroup.ker_mk']
    exact hVp.of_equiv (Subgroup.subgroupOfEquivOfLe hVH).symm
  have hqsurj : Function.Surjective qH :=
    QuotientGroup.mk'_surjective VH
  let S : Sylow p H := Qs.comapOfKerIsPGroup qH hkerp
    (by rw [MonoidHom.range_eq_top.mpr hqsurj]; exact le_top)
  have hSco : (S : Subgroup H) =
      (PN : Subgroup N).map iN ⊔ VH := by
    dsimp only [S, Qs]
    rw [Sylow.coe_comapOfKerIsPGroup, Sylow.coe_mapSurjective]
    change (((PN : Subgroup N).map f).comap qH) = _
    rw [show f = qH.comp iN from rfl, ← Subgroup.map_map,
      Subgroup.comap_map_eq, QuotientGroup.ker_mk']
  refine ⟨S, ?_⟩
  rw [hSco, Subgroup.map_sup]
  have hiN : H.subtype.comp iN = N.subtype := by
    ext x
    rfl
  rw [Subgroup.map_map, hiN, ← hP,
    Subgroup.map_subgroupOf_eq_of_le hVH, sup_comm]

end HallFrattiniHelpers

section KStructureHelpers

/-- The Fitting core is functorial under a group equivalence. -/
private theorem map_fittingCore_mulEquiv
    {A : Type u} {B : Type v} [Group A] [Group B]
    (e : A ≃* B) :
    (fittingCore A).map e.toMonoidHom = fittingCore B := by
  rw [fittingCore, fittingCore, Subgroup.map_iSup]
  apply iSup_congr
  intro q
  letI : Fact (q : ℕ).Prime := ⟨q.property⟩
  exact map_pCore_eq_mulEquiv (p := (q : ℕ)) e

/-- In the reduced Theorem 3.6 configuration, the normalized-subgroup
dichotomy forces a nilpotent kernel to be a group of prime-power order. -/
private theorem isPGroup_of_nilpotent_prime_core_dichotomy
    {G : Type u} [Group G] [Finite G]
    (K P R : Subgroup G) {q : ℕ} (hq : q.Prime)
    (hKnil : Group.IsNilpotent K) (hqK : q ∣ Nat.card K)
    (hnormK : P ⊔ R ≤ Subgroup.normalizer (K : Set G))
    (hsub : ∀ X : Subgroup G,
      P ⊔ R ≤ Subgroup.normalizer (X : Set G) → X ≤ K →
      X = K ∨ X ≤ Subgroup.centralizer (P : Set G))
    (hKP : ⁅K, P⁆ = K) : IsPGroup q K := by
  classical
  letI : Fact q.Prime := ⟨hq⟩
  letI : Group.IsNilpotent K := hKnil
  let Kq : Subgroup G := (pCore q K).map K.subtype
  let Kq' : Subgroup G := (pPrimeCore q K).map K.subtype
  have hKqle : Kq ≤ K := by
    dsimp only [Kq]
    exact Subgroup.map_subtype_le _
  have hKq'le : Kq' ≤ K := by
    dsimp only [Kq']
    exact Subgroup.map_subtype_le _
  have hKqnorm : P ⊔ R ≤ Subgroup.normalizer (Kq : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    exact characteristic_map_subtype_invariant_under_normalizer
      K (P ⊔ R) (pCore q K) hnormK
  have hKq'norm : P ⊔ R ≤ Subgroup.normalizer (Kq' : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    exact characteristic_map_subtype_invariant_under_normalizer
      K (P ⊔ R) (pPrimeCore q K) hnormK
  rcases hsub Kq hKqnorm hKqle with hKqeq | hKqcent
  · rw [← hKqeq]
    exact pCore_isPGroup.map K.subtype
  rcases hsub Kq' hKq'norm hKq'le with hKq'eq | hKq'cent
  · have hcard : Nat.card Kq' = Nat.card (pPrimeCore q K) := by
      dsimp only [Kq']
      exact Subgroup.card_map_of_injective K.subtype_injective
    have hqCore : q ∣ Nat.card (pPrimeCore q K) := by
      rw [← hcard, hKq'eq]
      exact hqK
    exact (hq.coprime_iff_not_dvd.mp
      (pPrimeCore_coprime_card (G := K) (p := q)) hqCore).elim
  · have hdecomp : Kq ⊔ Kq' = K := by
      calc
        Kq ⊔ Kq' = ((pCore q K) ⊔ pPrimeCore q K).map K.subtype := by
          simp only [Kq, Kq', Subgroup.map_sup]
        _ = (⊤ : Subgroup K).map K.subtype := by
          rw [sup_pCore_pPrimeCore_eq_top_of_isNilpotent]
        _ = K := by
          rw [← MonoidHom.range_eq_map, K.range_subtype]
    have hKcent : K ≤ Subgroup.centralizer (P : Set G) := by
      rw [← hdecomp]
      exact sup_le hKqcent hKq'cent
    have hcommBot : ⁅K, P⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hKcent
    have hKbot : K = ⊥ := hKP.symm.trans hcommBot
    exact (hq.not_dvd_one (by simpa [hKbot] using hqK)).elim

/-- A faithful coprime action of a noncommutative odd group on a `q`-group
requires strictly more than `q^2` elements. -/
private theorem prime_sq_lt_natCard_of_odd_faithful_coprime_action
    {q : ℕ} [Fact q.Prime]
    {A : Type u} [Group A] [Finite A]
    {E : Type v} [Group E] [Finite E]
    (hsolA : IsSolvable A) (hE : IsPGroup q E)
    (hoddE : Odd (Nat.card E)) (hoddA : Odd (Nat.card A))
    (hqA : ¬ q ∣ Nat.card A)
    (rho : A →* MulAut E) (hrho : Function.Injective rho)
    (hnoncommA : ¬ IsMulCommutative A) :
    q ^ 2 < Nat.card E := by
  by_contra hnot
  have hcardLe : Nat.card E ≤ q ^ 2 := Nat.le_of_not_gt hnot
  have hRank : ¬ ∃ F : Subgroup E,
      IsElementaryAbelianOfRank q 3 F := by
    rintro ⟨F, hF⟩
    have hFle : Nat.card F ≤ Nat.card E :=
      Nat.le_of_dvd Nat.card_pos F.card_subgroup_dvd_card
    have hbad : q ^ 3 ≤ q ^ 2 := by
      calc
        q ^ 3 = Nat.card F := hF.card_eq.symm
        _ ≤ Nat.card E := hFle
        _ ≤ q ^ 2 := hcardLe
    exact (not_lt_of_ge hbad)
      (Nat.pow_lt_pow_right (Fact.out : q.Prime).one_lt (by omega))
  letI : IsSolvable A := hsolA
  let B : Subgroup (MulAut E) := rho.range
  have hBsol : IsSolvable B := by
    dsimp only [B]
    exact solvable_of_surjective rho.rangeRestrict_surjective
  have hBdvdA : Nat.card B ∣ Nat.card A := by
    simpa only [B] using Subgroup.card_range_dvd rho
  have hBodd : Odd (Nat.card B) := hoddA.of_dvd_nat hBdvdA
  have hBderived : IsPGroup q (_root_.commutator B) :=
    Submission.OddOrder.BG.Section04.der1_Aut_rank2_pgroup
      hE hoddE hRank B hBsol hBodd
  have hqB : ¬ q ∣ Nat.card B := fun h ↦ hqA (h.trans hBdvdA)
  have hBderivedBot : _root_.commutator B = ⊥ :=
    subgroup_eq_bot_of_isPGroup_of_not_dvd_natCard
      (_root_.commutator B) hBderived hqB
  have hBcomm : IsMulCommutative B :=
    (_root_.commutator_eq_bot_iff B).mp hBderivedBot
  apply hnoncommA
  apply isMulCommutative_iff.mpr
  intro a b
  apply hrho
  let ar : B := ⟨rho a, ⟨a, rfl⟩⟩
  let br : B := ⟨rho b, ⟨b, rfl⟩⟩
  have hab : ar * br = br * ar :=
    (isMulCommutative_iff.mp hBcomm) ar br
  have hab' := congrArg Subtype.val hab
  change rho a * rho b = rho b * rho a at hab'
  simpa only [map_mul] using hab'

/-- A coprime actor with trivial centralizer acts faithfully on the
Frattini quotient of a `q`-group. -/
private theorem frattiniQuotientAction_injective_of_pPrime_of_trivial_centralizer
    {G : Type u} [Group G] [Finite G]
    {q : ℕ} [Fact q.Prime]
    (K L : Subgroup G)
    (hKq : IsPGroup q K)
    (hLK : L ≤ Subgroup.normalizer (K : Set G))
    (hLprime : IsPPrimeSubgroup q L)
    (hCLK : centralizerWithin L K = ⊥) :
    Function.Injective
      ((frattiniQuotientMulAutHom K).comp
        (K.normalizerMonoidHom.comp (Subgroup.inclusion hLK))) := by
  classical
  let phi : L →* MulAut K :=
    K.normalizerMonoidHom.comp (Subgroup.inclusion hLK)
  let qPhi : MulAut K →* MulAut (K ⧸ frattini K) :=
    frattiniQuotientMulAutHom K
  let rho : L →* MulAut (K ⧸ frattini K) := qPhi.comp phi
  change Function.Injective rho
  have hkerPrime : IsPPrimeSubgroup q rho.ker := by
    rw [IsPPrimeSubgroup]
    exact hLprime.coprime_dvd_right rho.ker.card_subgroup_dvd_card
  let psi : rho.ker →* MulAut K := phi.comp rho.ker.subtype
  have hrangeLe : psi.range ≤ qPhi.ker := by
    rintro a ⟨x, rfl⟩
    change qPhi (phi (x : L)) = 1
    simpa only [rho, MonoidHom.comp_apply] using
      MonoidHom.mem_ker.mp x.property
  have hrangeQ : IsPGroup q psi.range :=
    (frattiniQuotientMulAutHom_ker_isPGroup hKq).to_le hrangeLe
  have hrangePrime : IsPPrimeSubgroup q psi.range := by
    rw [IsPPrimeSubgroup]
    exact hkerPrime.coprime_dvd_right
      (Subgroup.card_range_dvd psi)
  have hrangeBot : psi.range = ⊥ := by
    obtain ⟨n, hn⟩ := hrangeQ.exists_card_eq
    have hself : Nat.Coprime (Nat.card psi.range)
        (Nat.card psi.range) := by
      simpa only [hn] using hrangePrime.pow_left n
    simpa using Subgroup.disjoint_of_coprime_natCard hself
  have hkerBot : rho.ker = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    let xx : rho.ker := ⟨x, hx⟩
    have hphi : phi x = 1 := by
      have hm : psi xx ∈ psi.range := ⟨xx, rfl⟩
      rw [hrangeBot] at hm
      have hmone : psi xx = 1 := Subgroup.mem_bot.mp hm
      change phi x = 1 at hmone
      exact hmone
    have hxCent : (x : G) ∈ Subgroup.centralizer (K : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      let kk : K := ⟨k, hk⟩
      have hfix : phi x kk = kk := by
        rw [hphi]
        rfl
      have heq : (x : G) * k * (x : G)⁻¹ = k :=
        congrArg Subtype.val hfix
      calc
        k * (x : G) = ((x : G) * k * (x : G)⁻¹) * (x : G) := by
          rw [heq]
        _ = (x : G) * k := by group
    have hxWithin : (x : G) ∈ centralizerWithin L K :=
      ⟨x.property, hxCent⟩
    have hxOne : (x : G) = 1 := by
      apply Subgroup.mem_bot.mp
      rw [← hCLK]
      exact hxWithin
    exact Subtype.ext hxOne
  exact rho.ker_eq_bot_iff.mp hkerBot

/-- Contrapositive form of Theorem 3.4 for a faithful elementary-abelian
action. -/
private theorem false_of_faithful_elementary_action_zero_fixed
    {A E : Type*} [Group A] [Finite A] [IsSolvable A]
    [Group E] [Finite E]
    {q : ℕ} [Fact q.Prime]
    (P R : Subgroup A) [P.Normal]
    (hcomp : P.IsComplement' R)
    (hcop : Nat.Coprime (Nat.card P) (Nat.card R))
    (hodd : Odd (Nat.card A))
    (hRprime : (Nat.card R).Prime)
    (hAcard : (Nat.card A : ZMod q) ≠ 0)
    (hE : IsElementaryAbelianGroup q E)
    (a : A →* MulAut E) (ha : Function.Injective a)
    (hperfect : ⁅R, P⁆ = P) (hPne : P ≠ ⊥)
    (hfix : ∀ x : E, (∀ r : R, a (r : A) x = x) → x = 1) : False := by
  letI : IsMulCommutative E := hE.commutative
  letI : Module (ZMod q) (Additive E) :=
    AddCommGroup.zmodModule fun x => hE.pow_eq_one x.toMul
  let endMonoid : Monoid (Module.End (ZMod q) (Additive E)) :=
    Module.End.instMonoid
  letI : Monoid (Module.End (ZMod q) (Additive E)) := endMonoid
  letI : MulOne (Module.End (ZMod q) (Additive E)) :=
    endMonoid.toMulOne
  letI : MulOneClass (Module.End (ZMod q) (Additive E)) :=
    endMonoid.toMulOneClass
  let sigma : Representation (ZMod q) A (Additive E) :=
    elementaryAbelianActionRepresentation E A q a
  letI : Fintype A := Fintype.ofFinite A
  have hsigma : Function.Injective sigma := by
    intro x y hxy
    apply ha
    apply MulEquiv.ext
    intro z
    have hz := LinearMap.congr_fun hxy (Additive.ofMul z)
    change Additive.ofMul (a x z) = Additive.ofMul (a y z) at hz
    exact congrArg Additive.toMul hz
  have hfixSigma :=
      (Submodule.eq_bot_iff (Representation.invariants
        (sigma.comp R.subtype :
          Representation (ZMod q) R (Additive E)))).mpr (by
    intro x hx
    change x.toMul = 1
    apply hfix x.toMul
    intro r
    have hr := (Representation.mem_invariants _ x).mp hx r
    change Additive.ofMul (a (r : A) x.toMul) = x at hr
    exact congrArg Additive.toMul hr)
  have hkill := odd_prime_sdprod_rfix0 sigma P R hcomp hcop hodd
    hRprime hAcard hfixSigma
  rw [sigma.ker_eq_bot hsigma, hperfect] at hkill
  exact hPne (le_bot_iff.mp hkill)

/-- A fixed coset in a coprime conjugation factor comes from the original
centralizer. -/
private theorem factor_fixed_eq_one_of_centralizer_le
    {G : Type u} [Group G] [Finite G] [IsSolvable G]
    (K D L R : Subgroup G) [(D.subgroupOf K).Normal]
    (hDK : D ≤ K) (hRL : R ≤ L)
    (hLK : L ≤ Subgroup.normalizer (K : Set G))
    (hLD : L ≤ Subgroup.normalizer (D : Set G))
    (hKD : K ≤ Subgroup.normalizer (D : Set G))
    (hcopDR : Nat.Coprime (Nat.card D) (Nat.card R))
    (hCD : centralizerWithin K R ≤ D) :
    let a := subgroupConjugationFactorHom D K L hLK hLD
    ∀ x : K ⧸ D.subgroupOf K,
      (∀ r : R.subgroupOf L, a (r : L) x = x) → x = 1 := by
  dsimp only
  let A : Subgroup G := K ⊔ L
  have hKA : K ≤ A := le_sup_left
  have hLA : L ≤ A := le_sup_right
  have hRA : R ≤ A := hRL.trans hLA
  have hDA : D ≤ A := hDK.trans hKA
  let DA : Subgroup A := D.subgroupOf A
  let KA : Subgroup A := K.subgroupOf A
  let RA : Subgroup A := R.subgroupOf A
  have hAnormD : A ≤ Subgroup.normalizer (D : Set G) :=
    sup_le hKD hLD
  letI : DA.Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hAnormD
  letI : IsSolvable A := isSolvable_subgroup_of_isSolvable A
  letI : IsSolvable RA := isSolvable_subgroup_of_isSolvable RA
  have hDAKA : DA ≤ KA := fun d hd => hDK hd
  have hcentLocal : centralizerWithin KA RA ≤ DA := by
    intro x hx
    apply hCD
    refine ⟨hx.1, ?_⟩
    intro r hr
    let rA : RA := ⟨⟨r, hRA hr⟩, hr⟩
    exact congrArg Subtype.val (hx.2 (rA : A) rA.property)
  let qA : A →* A ⧸ DA := QuotientGroup.mk' DA
  let Kd : Subgroup (A ⧸ DA) := KA.map qA
  let Rd : Subgroup (A ⧸ DA) := RA.map qA
  have hcopLocal : Nat.Coprime (Nat.card DA) (Nat.card RA) := by
    rw [natCard_subgroupOf_eq hDA, natCard_subgroupOf_eq hRA]
    exact hcopDR
  have hcentq : centralizerWithin Kd Rd = ⊥ := by
    have hm :=
      map_centralizerWithin_quotient_eq_of_coprime_of_solvable_right
        (N := DA) (Y := KA) (R := RA) hDAKA hcopLocal
    have hmapbot : (centralizerWithin KA RA).map qA = ⊥ := by
      apply (Subgroup.map_eq_bot_iff _).mpr
      simpa [qA, QuotientGroup.ker_mk'] using hcentLocal
    rw [hmapbot] at hm
    simpa only [Kd, Rd, qA] using hm.symm
  let toKA : K →* KA :=
    { toFun := fun k => ⟨⟨(k : G), hKA k.property⟩, k.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have htoKA : Function.Surjective toKA := by
    intro x
    refine ⟨⟨(((x : KA) : A) : G), x.property⟩, ?_⟩
    rfl
  let fK : K →* Kd := (qA.subgroupMap KA).comp toKA
  have hfK : Function.Surjective fK :=
    (qA.subgroupMap_surjective KA).comp htoKA
  have hfKker : D.subgroupOf K = fK.ker := by
    ext k
    rw [MonoidHom.mem_ker]
    constructor
    · intro hk
      apply Subtype.ext
      change qA (toKA k : A) = 1
      apply (QuotientGroup.eq_one_iff (toKA k : A)).mpr
      change (k : G) ∈ D
      exact hk
    · intro hk
      have hk' := congrArg Subtype.val hk
      change qA (toKA k : A) = 1 at hk'
      have hmem := (QuotientGroup.eq_one_iff (toKA k : A)).mp hk'
      change (k : G) ∈ D at hmem
      exact hmem
  let E := K ⧸ D.subgroupOf K
  let eE : E ≃* Kd :=
    QuotientGroup.liftEquiv (D.subgroupOf K) hfK hfKker
  let a : L →* MulAut E :=
    subgroupConjugationFactorHom D K L hLK hLD
  let iL : L →* A := Subgroup.inclusion hLA
  have heAction (g : L) (x : E) :
      ((eE (a g x) : Kd) : A ⧸ DA) =
        qA (iL g) * (eE x : A ⧸ DA) * (qA (iL g))⁻¹ := by
    obtain ⟨k, rfl⟩ :=
      QuotientGroup.mk'_surjective (D.subgroupOf K) x
    let kg : K :=
      ⟨(g : G) * (k : G) * (g : G)⁻¹,
        (hLK g.property (k : G)).mp k.property⟩
    have hact :
        a g (QuotientGroup.mk' (D.subgroupOf K) k) =
          QuotientGroup.mk' (D.subgroupOf K) kg := by
      simpa only [a, kg] using
        subgroupConjugationFactorHom_apply_mk
          D K L hLK hLD g k
    rw [hact]
    change qA (toKA kg : A) =
      qA (iL g) * qA (toKA k : A) * (qA (iL g))⁻¹
    calc
      qA (toKA kg : A) =
          qA (iL g * toKA k * (iL g)⁻¹) := by
        congr 1
      _ = qA (iL g) * qA (toKA k : A) * (qA (iL g))⁻¹ := by
        rw [map_mul, map_mul, map_inv]
  intro x hxfix
  have hxcent : (eE x : A ⧸ DA) ∈ centralizerWithin Kd Rd := by
    refine ⟨(eE x).property, ?_⟩
    intro r hr
    rcases hr with ⟨rA, hrA, hrEq⟩
    have hrR : (((rA : A) : G)) ∈ R := hrA
    let rL : R.subgroupOf L :=
      ⟨⟨((rA : A) : G), hRL hrR⟩, hrR⟩
    have hfixed : a (rL : L) x = x := hxfix rL
    have hsame : iL (rL : L) = rA := by
      apply Subtype.ext
      rfl
    have hconj : qA rA * (eE x : A ⧸ DA) * (qA rA)⁻¹ =
        (eE x : A ⧸ DA) := by
      rw [← hsame]
      simpa only [hfixed] using (heAction (rL : L) x).symm
    rw [← hrEq]
    calc
      qA rA * (eE x : A ⧸ DA) =
          (qA rA * (eE x : A ⧸ DA) * (qA rA)⁻¹) * qA rA := by
        group
      _ = (eE x : A ⧸ DA) * qA rA := by rw [hconj]
  have hxbot : (eE x : A ⧸ DA) ∈ (⊥ : Subgroup (A ⧸ DA)) := by
    rw [← hcentq]
    exact hxcent
  have hxe : eE x = 1 := by
    apply Subtype.ext
    exact Subgroup.mem_bot.mp hxbot
  apply eE.injective
  simpa using hxe

/-- The abelian endpoint of the normalized-subgroup dichotomy is elementary
abelian. -/
private theorem elementary_of_normalized_subgroup_dichotomy
    {G : Type u} [Group G] [Finite G]
    {q : ℕ} [Fact q.Prime]
    (K P R : Subgroup G)
    (hKq : IsPGroup q K) (hKne : K ≠ ⊥)
    (hKcomm : IsMulCommutative K)
    (hKP : ⁅K, P⁆ = K)
    (hcopKP : (Nat.card K).Coprime (Nat.card P))
    (hnormKPR : P ⊔ R ≤ Subgroup.normalizer (K : Set G))
    (hsub : ∀ X : Subgroup G,
      P ⊔ R ≤ Subgroup.normalizer (X : Set G) → X ≤ K →
      X = K ∨ X ≤ Subgroup.centralizer (P : Set G)) :
    IsElementaryAbelianGroup q K := by
  classical
  letI : IsMulCommutative K := hKcomm
  have hnormPK : P ≤ Subgroup.normalizer (K : Set G) :=
    le_sup_left.trans hnormKPR
  have hperfect : ⁅P, K⁆ = K := by
    rw [Subgroup.commutator_comm]
    exact hKP
  have hKK : ⁅K, K⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact Subgroup.le_centralizer_iff_isMulCommutative.mpr hKcomm
  have hCKP : centralizerWithin K P = ⊥ := by
    apply le_bot_iff.mp
    exact (centralizerWithin_le_commutator_of_perfect_coprime_action
      hnormPK hcopKP hperfect).trans_eq hKK
  let Omega : Subgroup G := (omegaOne q K).map K.subtype
  have hOmegaK : Omega ≤ K := by
    dsimp only [Omega]
    exact Subgroup.map_subtype_le _
  have hOmegaNorm : P ⊔ R ≤ Subgroup.normalizer (Omega : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    exact characteristic_map_subtype_invariant_under_normalizer
      K (P ⊔ R) (omegaOne q K) hnormKPR
  have hOmegaEq : Omega = K := by
    rcases hsub Omega hOmegaNorm hOmegaK with hEq | hCent
    · exact hEq
    · exfalso
      have hOmegaBot : Omega = ⊥ := by
        apply le_bot_iff.mp
        rw [← hCKP]
        exact le_inf hOmegaK hCent
      have hOmegaKBot : omegaOne q K = ⊥ := by
        apply Subgroup.map_injective K.subtype_injective
        simpa only [Omega, Subgroup.map_bot] using hOmegaBot
      have hcardK : Nat.card K ≠ 1 :=
        (K.one_lt_card_iff_ne_bot.mpr hKne).ne'
      exact (omegaOne_ne_bot_of_isPGroup hKq hcardK) hOmegaKBot
  have hOmegaTop : omegaOne q K = ⊤ := by
    apply Subgroup.map_injective K.subtype_injective
    calc
      (omegaOne q K).map K.subtype = K := by
        simpa only [Omega] using hOmegaEq
      _ = (⊤ : Subgroup K).map K.subtype := by
        rw [← MonoidHom.range_eq_map, K.range_subtype]
  have hpow (x : K) : x ^ q = 1 := by
    exact omegaOne_pow_eq_one_of_mul_closed q
      (fun a b ha hb ↦ by
        have hab : Commute a b := Std.Commutative.comm a b
        simpa [ha, hb] using hab.mul_pow q)
      (by rw [hOmegaTop]; exact Subgroup.mem_top x)
  exact ⟨hKq, hKcomm, hpow⟩

/-- In the noncommutative endpoint the critical subgroup argument may be
compressed to the characteristic omega subgroup. -/
private theorem special_and_pow_prime_of_noncomm_dichotomy
    {G : Type u} [Group G] [Finite G]
    {q : ℕ} [Fact q.Prime]
    (K P R : Subgroup G)
    (hKq : IsPGroup q K) (hKne : K ≠ ⊥)
    (hKodd : Odd (Nat.card K))
    (hnormKPR : P ⊔ R ≤ Subgroup.normalizer (K : Set G))
    (hcopKP : (Nat.card K).Coprime (Nat.card P))
    (hKP : ⁅K, P⁆ = K)
    (hsub : ∀ X : Subgroup G,
      P ⊔ R ≤ Subgroup.normalizer (X : Set G) → X ≤ K →
      X = K ∨ X ≤ Subgroup.centralizer (P : Set G))
    (hnoncomm : ¬ IsMulCommutative K) :
    ∃ hS : IsSpecial K,
      centralizerWithin K P = ⁅K, K⁆ ∧ ∀ x : K, x ^ q = 1 := by
  classical
  have hnormPK : P ≤ Subgroup.normalizer (K : Set G) :=
    le_sup_left.trans hnormKPR
  have hperfect : ⁅P, K⁆ = K := by
    rw [Subgroup.commutator_comm]
    exact hKP
  have hchar : ∀ (A : Subgroup K) [A.Characteristic],
      IsMulCommutative A →
      A.map K.subtype ≤ Subgroup.centralizer (P : Set G) := by
    intro A hAchar hAcomm
    let X : Subgroup G := A.map K.subtype
    have hXK : X ≤ K := Subgroup.map_subtype_le _
    have hXnorm : P ⊔ R ≤ Subgroup.normalizer (X : Set G) := by
      rw [Subgroup.le_normalizer_iff]
      exact characteristic_map_subtype_invariant_under_normalizer
        K (P ⊔ R) A hnormKPR
    rcases hsub X hXnorm hXK with hXeq | hXcent
    · exfalso
      apply hnoncomm
      apply isMulCommutative_iff.mpr
      intro x y
      have hsurj : Function.Surjective A.subtype := by
        intro z
        have hz : (z : G) ∈ X := by
          rw [hXeq]
          exact z.property
        rcases hz with ⟨a, ha, heq⟩
        exact ⟨⟨a, ha⟩, Subtype.ext heq⟩
      obtain ⟨a, rfl⟩ := hsurj x
      obtain ⟨b, rfl⟩ := hsurj y
      exact congrArg A.subtype
        ((isMulCommutative_iff.mp hAcomm) a b)
    · exact hXcent
  obtain ⟨hS, hfixed, hcenterPow⟩ :=
    isSpecial_and_centralizerWithin_eq_center_of_characteristic_abelian_coprime
      (Fact.out : q.Prime) hKq hnoncomm hnormPK hcopKP hperfect hchar
  have hCKP : centralizerWithin K P = ⁅K, K⁆ :=
    hfixed.trans <| (congrArg (fun Z : Subgroup K => Z.map K.subtype)
      hS.commutator_eq_center.symm).trans K.map_subtype_commutator
  let Omega : Subgroup G := (omegaOne q K).map K.subtype
  have hOmegaK : Omega ≤ K := Subgroup.map_subtype_le _
  have hOmegaNorm : P ⊔ R ≤ Subgroup.normalizer (Omega : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    exact characteristic_map_subtype_invariant_under_normalizer
      K (P ⊔ R) (omegaOne q K) hnormKPR
  have hqdiv : q ∣ Nat.card K :=
    hKq.card_eq_or_dvd.resolve_left
      (K.one_lt_card_iff_ne_bot.mpr hKne).ne'
  have hqodd : Odd q := hKodd.of_dvd_nat hqdiv
  have hOmegaEq : Omega = K := by
    rcases hsub Omega hOmegaNorm hOmegaK with hEq | hCent
    · exact hEq
    · have homega : P ≤ Subgroup.centralizer (Omega : Set G) :=
        Subgroup.le_centralizer_iff.mp hCent
      have hPcentK : P ≤ Subgroup.centralizer (K : Set G) :=
        special_perfect_action_centralizes_of_centralizes_omegaOne
          (Fact.out : q.Prime) hqodd hKq hS hcenterPow
          hnormPK hperfect homega
      have hbot : ⁅P, K⁆ = ⊥ :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hPcentK
      exact (hKne (hperfect.symm.trans hbot)).elim
  have hOmegaTop : omegaOne q K = ⊤ := by
    apply Subgroup.map_injective K.subtype_injective
    calc
      (omegaOne q K).map K.subtype = K := by
        simpa only [Omega] using hOmegaEq
      _ = (⊤ : Subgroup K).map K.subtype := by
        rw [← MonoidHom.range_eq_map, K.range_subtype]
  letI : Group.IsNilpotent K := hKq.isNilpotent
  have hclass2 : Group.nilpotencyClass K ≤ 2 :=
    nilpotencyClass_le_two_of_commutator_le_center
      hS.commutator_eq_center.le
  have hclass : Group.nilpotencyClass K ≤ if 3 < q then 3 else 2 := by
    split_ifs <;> omega
  have hpow (x : K) : x ^ q = 1 :=
    omegaOne_pow_eq_one_of_small_nilpotencyClass
      q Fact.out hqodd hKq hclass x (by rw [hOmegaTop]; trivial)
  exact ⟨hS, hCKP, hpow⟩

/-- In the abelian endpoint the derived quotient is the group itself. -/
private theorem prime_sq_lt_card_of_derived_quotient
    {K : Type u} [Group K] [Finite K]
    {q : ℕ} [Fact q.Prime]
    (hKcomm : IsMulCommutative K)
    (hquot : q ^ 2 < Nat.card (K ⧸ _root_.commutator K)) :
    q ^ 2 < Nat.card K := by
  letI : IsMulCommutative K := hKcomm
  simpa only [_root_.commutator_eq_bot, ← Subgroup.index_eq_card,
    Subgroup.index_bot] using hquot

/-- The two-coatom calculation which eliminates the special,
noncommutative endpoint. -/
private theorem false_of_special_coprime_coatom_configuration
    {G : Type u} [Group G] [Finite G]
    {q : ℕ} [Fact q.Prime]
    (K P R : Subgroup G)
    (hS : IsSpecial K)
    (hnormPK : P ≤ Subgroup.normalizer (K : Set G))
    (hsub : ∀ X : Subgroup G,
      P ⊔ R ≤ Subgroup.normalizer (X : Set G) → X ≤ K →
      X = K ∨ X ≤ Subgroup.centralizer (P : Set G))
    (hCKP : centralizerWithin K P = ⁅K, K⁆)
    (hDne : ⁅R, K⁆ ≠ ⊥)
    (hCcard : Nat.card (centralizerWithin K R) = q)
    (hCDRbot : centralizerWithin ⁅R, K⁆ R = ⊥)
    (hDcomm : IsMulCommutative (⁅R, K⁆ : Subgroup G))
    (hCDdis : Disjoint (centralizerWithin K R) ⁅R, K⁆)
    (hDCsup : ⁅R, K⁆ ⊔ centralizerWithin K R = K)
    (hlarge : q ^ 2 < Nat.card (K ⧸ _root_.commutator K)) : False := by
  classical
  let D : Subgroup G := ⁅R, K⁆
  let C : Subgroup G := centralizerWithin K R
  let Z : Subgroup G := ⁅K, K⁆
  have hDCsup' : D ⊔ C = K := by
    simpa only [D, C] using hDCsup
  have hDK : D ≤ K := by
    calc
      D ≤ D ⊔ C := le_sup_left
      _ = K := hDCsup'
  have hCK : C ≤ K := centralizerWithin_le_left K R
  have hnormDR : R ≤ Subgroup.normalizer (D : Set G) := by
    dsimp only [D]
    exact Subgroup.normalizer_commutator_ge_left R K
  have hnormDK : K ≤ Subgroup.normalizer (D : Set G) := by
    dsimp only [D]
    exact Subgroup.normalizer_commutator_ge_right R K
  have hCne : C ≠ ⊥ := by
    intro hbot
    have hcardOne : Nat.card C = 1 := by rw [hbot]; exact Nat.card_unique
    rw [hCcard] at hcardOne
    exact (Fact.out : q.Prime).ne_one hcardOne
  have hDneK : D ≠ K := by
    intro hEq
    apply hCne
    simpa only [C, D, hEq] using hCDRbot
  let DK : Subgroup K := D.subgroupOf K
  let CK : Subgroup K := C.subgroupOf K
  letI : DK.Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hnormDK
  have hdisSub : Disjoint DK CK := by
    rw [disjoint_iff]
    apply le_bot_iff.mp
    intro x hx
    apply Subgroup.mem_bot.mpr
    apply Subtype.ext
    apply Subgroup.mem_bot.mp
    have hxAmbient : ((x : K) : G) ∈ D ⊓ C := hx
    rw [disjoint_iff.mp hCDdis.symm] at hxAmbient
    exact hxAmbient
  have hDKCKtop : DK ⊔ CK = ⊤ := by
    apply Subgroup.map_injective K.subtype_injective
    calc
      (DK ⊔ CK).map K.subtype = D ⊔ C := by
        rw [Subgroup.map_sup,
          Subgroup.map_subgroupOf_eq_of_le hDK,
          Subgroup.map_subgroupOf_eq_of_le hCK]
      _ = K := by simpa only [D, C] using hDCsup
      _ = (⊤ : Subgroup K).map K.subtype := by
        rw [← MonoidHom.range_eq_map, K.range_subtype]
  have hcomp : DK.IsComplement' CK := by
    apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisSub
    rw [← Subgroup.normal_mul DK CK, hDKCKtop]
    rfl
  have hDKindex : DK.index = q := by
    calc
      DK.index = Nat.card CK := hcomp.symm.index_eq_card
      _ = Nat.card C := natCard_subgroupOf_eq hCK
      _ = q := hCcard
  have hDKcoat : IsCoatom DK :=
    isCoatom_of_index_eq_prime (Fact.out : q.Prime) hDKindex
  by_cases hPnormD : P ≤ Subgroup.normalizer (D : Set G)
  · have hDnormPR : P ⊔ R ≤ Subgroup.normalizer (D : Set G) :=
      sup_le hPnormD hnormDR
    rcases hsub D hDnormPR hDK with hDeq | hDcent
    · exact hDneK hDeq
    · have hDZ : D ≤ Z := by
        dsimp only [Z]
        rw [← hCKP]
        exact le_inf hDK hDcent
      have hPhiMap : (frattini K).map K.subtype = Z := by
        dsimp only [Z]
        rw [hS.frattini_eq_center, ← hS.commutator_eq_center,
          K.map_subtype_commutator]
      have hDKPhi : DK ≤ frattini K := by
        rw [← Subgroup.map_le_map_iff_of_injective K.subtype_injective,
          Subgroup.map_subgroupOf_eq_of_le hDK, hPhiMap]
        exact hDZ
      have hCKPhiTop : CK ⊔ frattini K = ⊤ := by
        apply top_unique
        rw [← hDKCKtop]
        exact sup_le (hDKPhi.trans le_sup_right) le_sup_left
      have hCKtop : CK = ⊤ := frattini_nongenerating hCKPhiTop
      have hCeqK : C = K := by
        calc
          C = CK.map K.subtype :=
            (Subgroup.map_subgroupOf_eq_of_le hCK).symm
          _ = (⊤ : Subgroup K).map K.subtype := by rw [hCKtop]
          _ = K := by rw [← MonoidHom.range_eq_map, K.range_subtype]
      have hDleC : D ≤ C := by rw [hCeqK]; exact hDK
      have hDbot : D = ⊥ := by
        calc
          D = D ⊓ C := (inf_eq_left.mpr hDleC).symm
          _ = ⊥ := disjoint_iff.mp hCDdis.symm
      exact hDne (by simpa only [D] using hDbot)
  · obtain ⟨x, hxP, hxnot⟩ := SetLike.not_le_iff_exists.mp hPnormD
    have hKmap : K.map (MulAut.conj x).toMonoidHom = K :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hnormPK hxP)
    let eK : K ≃* K :=
      ((MulAut.conj x).subgroupMap K).trans
        (MulEquiv.subgroupCongr hKmap)
    let E : Subgroup K := DK.map eK.toMonoidHom
    have hecomp : K.subtype.comp eK.toMonoidHom =
        (MulAut.conj x).toMonoidHom.comp K.subtype := by
      ext y
      rfl
    have hEambient : E.map K.subtype =
        D.map (MulAut.conj x).toMonoidHom := by
      calc
        E.map K.subtype = DK.map (K.subtype.comp eK.toMonoidHom) := by
          change (DK.map eK.toMonoidHom).map K.subtype = _
          rw [Subgroup.map_map]
        _ = DK.map ((MulAut.conj x).toMonoidHom.comp K.subtype) := by
          rw [hecomp]
        _ = (DK.map K.subtype).map (MulAut.conj x).toMonoidHom := by
          rw [Subgroup.map_map]
        _ = D.map (MulAut.conj x).toMonoidHom := by
          rw [Subgroup.map_subgroupOf_eq_of_le hDK]
    have hEne : DK ≠ E := by
      intro hEq
      apply hxnot
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      calc
        D.map (MulAut.conj x).toMonoidHom = E.map K.subtype :=
          hEambient.symm
        _ = DK.map K.subtype := by rw [← hEq]
        _ = D := Subgroup.map_subgroupOf_eq_of_le hDK
    have hEindex : E.index = q := by
      calc
        E.index = DK.index := Subgroup.index_map_equiv DK eK
        _ = q := hDKindex
    have hEcoat : IsCoatom E :=
      isCoatom_of_index_eq_prime (Fact.out : q.Prime) hEindex
    have hDEtop : DK ⊔ E = ⊤ :=
      hDKcoat.sup_eq_top_of_ne hEcoat hEne
    let eDKD : DK ≃* D := Subgroup.subgroupOfEquivOfLe hDK
    have hDKcomm : IsMulCommutative DK := by
      apply isMulCommutative_iff.mpr
      intro a b
      apply eDKD.injective
      simpa only [map_mul] using
        (isMulCommutative_iff.mp hDcomm) (eDKD a) (eDKD b)
    let eDKE : DK ≃* E :=
      DK.equivMapOfInjective eK.toMonoidHom eK.injective
    have hEcomm : IsMulCommutative E := by
      apply isMulCommutative_iff.mpr
      intro a b
      obtain ⟨a0, rfl⟩ := eDKE.surjective a
      obtain ⟨b0, rfl⟩ := eDKE.surjective b
      simpa only [map_mul] using congrArg eDKE
        ((isMulCommutative_iff.mp hDKcomm) a0 b0)
    let I : Subgroup K := DK ⊓ E
    have hIcenter : I ≤ Subgroup.center K := by
      intro i hi
      rw [Subgroup.mem_center_iff]
      intro k
      have hDKcent : DK ≤ Subgroup.centralizer ({i} : Set K) := by
        intro d hd
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        rw [Set.mem_singleton_iff] at hz
        subst z
        exact (congrArg Subtype.val
          ((isMulCommutative_iff.mp hDKcomm)
            (⟨d, hd⟩ : DK) (⟨i, hi.1⟩ : DK))).symm
      have hEcent : E ≤ Subgroup.centralizer ({i} : Set K) := by
        intro e he
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        rw [Set.mem_singleton_iff] at hz
        subst z
        exact (congrArg Subtype.val
          ((isMulCommutative_iff.mp hEcomm)
            (⟨e, he⟩ : E) (⟨i, hi.2⟩ : E))).symm
      have hkcent : k ∈ Subgroup.centralizer ({i} : Set K) :=
        (sup_le hDKcent hEcent) (by rw [hDEtop]; trivial)
      exact (Subgroup.mem_centralizer_iff.mp hkcent i
        (Set.mem_singleton i)).symm
    have hIle : I ≤ _root_.commutator K :=
      hIcenter.trans_eq hS.commutator_eq_center.symm
    have hle : Nat.card (K ⧸ _root_.commutator K) ≤ q ^ 2 := calc
      _ = (_root_.commutator K).index := rfl
      _ ≤ I.index := Subgroup.index_antitone hIle
      _ ≤ DK.index * E.index := by
        change (DK ⊓ E).index ≤ DK.index * E.index
        exact Subgroup.index_inf_le
      _ = q ^ 2 := by rw [hDKindex, hEindex, pow_two]
    exact (not_lt_of_ge hle) hlarge

end KStructureHelpers

section MainInduction

/-- A quotient of a subgroup by the restriction of an ambient normal
subgroup is canonically its image in the ambient quotient. -/
private def subgroupQuotientEquivImage
    {G : Type u} [Group G] (K H : Subgroup G) [K.Normal]
    (hKH : K ≤ H) :
    (H ⧸ K.subgroupOf H) ≃* H.map (QuotientGroup.mk' K) := by
  letI : (K.subgroupOf H).Normal :=
    Subgroup.Normal.subgroupOf (inferInstance : K.Normal) H
  exact QuotientGroup.liftEquiv (K.subgroupOf H)
    ((QuotientGroup.mk' K).subgroupMap_surjective H) (by
      rw [Subgroup.ker_subgroupMap, QuotientGroup.ker_mk'])

/-- Cardinality-indexed form of Bender--Glauberman Theorem 3.6. -/
def OddSemidirectZGroupPLengthStatement
    (p n : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] [IsSolvable G],
    Nat.card G = n →
    ∀ (H R R0 : Subgroup G) [H.Normal],
      H.IsComplement' R →
      Nat.Coprime (Nat.card H) (Nat.card R) →
      Odd (Nat.card G) →
      R0 ≤ R →
      (Nat.card R0).Prime →
      IsZGroup (centralizerWithin H R0) →
      IsPLengthOne p (⁅R, H⁆ : Subgroup G)

/-- The recursive proper-commutator branch of Theorem 3.6. -/
private theorem oddSemidirectZGroupPLength_properCommutator
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G] [Finite G] [IsSolvable G]
    (H R R0 : Subgroup G) [H.Normal]
    (hHR : H.IsComplement' R)
    (hcop : Nat.Coprime (Nat.card H) (Nat.card R))
    (hodd : Odd (Nat.card G))
    (hR0R : R0 ≤ R)
    (hR0prime : (Nat.card R0).Prime)
    (hZ : IsZGroup (centralizerWithin H R0))
    (hproper : ⁅R, H⁆ < H)
    (ih : ∀ m, m < Nat.card G →
      OddSemidirectZGroupPLengthStatement.{u} p m) :
    IsPLengthOne p (⁅R, H⁆ : Subgroup G) := by
  let D : Subgroup G := ⁅R, H⁆
  have hDH : D ≤ H := Subgroup.commutator_le_right R H
  have hnormD : R ≤ Subgroup.normalizer (D : Set G) :=
    Subgroup.normalizer_commutator_ge_left R H
  let J : Subgroup G := R ⊔ D
  let DJ : Subgroup J := D.subgroupOf J
  let RJ : Subgroup J := R.subgroupOf J
  let R0J : Subgroup J := R0.subgroupOf J
  letI : IsSolvable J := isSolvable_subgroup_of_isSolvable J
  letI : DJ.Normal :=
    Subgroup.normal_subgroupOf_sup_of_le_normalizer hnormD
  have hlt : Nat.card J < Nat.card G := by
    simpa [J, D] using
      natCard_sup_lt_of_properKernel hHR hproper hnormD
  have hcompJ : DJ.IsComplement' RJ := by
    simpa [J, DJ, RJ] using
      properKernel_subgroupOf_isComplement hHR hDH hnormD
  have hcopJ : Nat.Coprime (Nat.card DJ) (Nat.card RJ) := by
    simpa [J, DJ, RJ] using
      natCard_coprime_subgroupOf_properKernel hcop hDH
  have hoddJ : Odd (Nat.card J) := by
    simpa [J] using
      (odd_natCard_sup (G := G) (H := D) (R := R) hodd)
  have hR0Jcard : Nat.card R0J = Nat.card R0 :=
    natCard_subgroupOf_eq
      (hR0R.trans (show R ≤ J from le_sup_left))
  have hR0Jprime : (Nat.card R0J).Prime := by
    rwa [hR0Jcard]
  have hR0JRJ : R0J ≤ RJ := Subgroup.subgroupOf_mono J hR0R
  have hZJ : IsZGroup (centralizerWithin DJ R0J) := by
    exact isZGroup_centralizerWithin_subgroupOf hDH
      (hR0R.trans (show R ≤ J from le_sup_left)) hZ
  have hrecJ : IsPLengthOne p (⁅RJ, DJ⁆ : Subgroup J) := by
    exact ih (Nat.card J) hlt J rfl DJ RJ R0J
      hcompJ hcopJ hoddJ hR0JRJ hR0Jprime hZJ
  have hmap : (⁅RJ, DJ⁆ : Subgroup J).map J.subtype =
      (⁅R, D⁆ : Subgroup G) := by
    rw [Subgroup.map_commutator,
      Subgroup.map_subgroupOf_eq_of_le
        (show R ≤ J from le_sup_left),
      Subgroup.map_subgroupOf_eq_of_le
        (show D ≤ J from le_sup_right)]
  let e : (⁅RJ, DJ⁆ : Subgroup J) ≃* (⁅R, D⁆ : Subgroup G) := by
    rw [← hmap]
    exact Subgroup.equivMapOfInjective (⁅RJ, DJ⁆ : Subgroup J)
      J.subtype J.subtype_injective
  have hrecRD : IsPLengthOne p (⁅R, D⁆ : Subgroup G) :=
    isPLengthOne_of_mulEquiv hrecJ e
  have hnormH : R ≤ Subgroup.normalizer (H : Set G) := by
    rw [H.normalizer_eq_top]
    exact le_top
  have hidem : ⁅R, D⁆ = D := by
    simpa [D] using
      (commutator_commutator_eq_of_coprime
        (K := H) (R := R) hnormH hcop)
  rwa [hidem] at hrecRD

/-- The recursive quotient branch of Theorem 3.6.  The perfect-action
reduction makes the image of the mixed commutator equal to the whole image
of the normal factor. -/
private theorem oddSemidirectZGroupPLength_quotient
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G] [Finite G] [IsSolvable G]
    (H R R0 X : Subgroup G) [H.Normal] [X.Normal]
    (hHR : H.IsComplement' R)
    (hcop : Nat.Coprime (Nat.card H) (Nat.card R))
    (hodd : Odd (Nat.card G))
    (hR0R : R0 ≤ R)
    (hR0prime : (Nat.card R0).Prime)
    (hZ : IsZGroup (centralizerWithin H R0))
    (hperfect : ⁅R, H⁆ = H)
    (hXne : X ≠ ⊥) (hXH : X ≤ H)
    (ih : ∀ m, m < Nat.card G →
      OddSemidirectZGroupPLengthStatement.{u} p m) :
    IsPLengthOne p (H ⧸ X.subgroupOf H) := by
  let q : G →* G ⧸ X := QuotientGroup.mk' X
  let Hq : Subgroup (G ⧸ X) := H.map q
  let Rq : Subgroup (G ⧸ X) := R.map q
  let R0q : Subgroup (G ⧸ X) := R0.map q
  letI : Hq.Normal :=
    Subgroup.Normal.map (inferInstance : H.Normal) q
      (QuotientGroup.mk'_surjective X)
  letI : IsSolvable R0 := isSolvable_subgroup_of_isSolvable R0
  have hlt : Nat.card (G ⧸ X) < Nat.card G :=
    natCard_quotient_lt_of_ne_bot X hXne
  have hcompq : Hq.IsComplement' Rq := by
    simpa [Hq, Rq, q] using hHR.quotient_isComplement hXH
  have hcopq : Nat.Coprime (Nat.card Hq) (Nat.card Rq) := by
    exact hcop.coprime_dvd_left (Subgroup.card_map_dvd H q) |>.coprime_dvd_right
      (Subgroup.card_map_dvd R q)
  have hoddq : Odd (Nat.card (G ⧸ X)) :=
    odd_natCard_quotient X hodd
  have hR0qRq : R0q ≤ Rq := Subgroup.map_mono hR0R
  have hqR0inj : Function.Injective (q.subgroupMap R0) := by
    intro a b hab
    apply Subtype.ext
    have habq : q (a : G) = q (b : G) :=
      congrArg Subtype.val hab
    have habR : (⟨(a : G), hR0R a.property⟩ : R) =
        ⟨(b : G), hR0R b.property⟩ :=
      hHR.quotientMap_injective_on_right hXH habq
    exact congrArg (fun r : R => (r : G)) habR
  have hR0qcard : Nat.card R0q = Nat.card R0 := by
    let eR0 : R0 ≃* R0.map q :=
      MulEquiv.ofBijective (q.subgroupMap R0)
        ⟨hqR0inj, q.subgroupMap_surjective R0⟩
    simpa only [R0q] using (Nat.card_congr eR0.toEquiv).symm
  have hR0qprime : (Nat.card R0q).Prime := by
    rwa [hR0qcard]
  have hcopXR0 : Nat.Coprime (Nat.card X) (Nat.card R0) :=
    hcop.coprime_dvd_left (Subgroup.card_dvd_of_le hXH) |>.coprime_dvd_right
      (Subgroup.card_dvd_of_le hR0R)
  have hmapCent :=
    map_centralizerWithin_quotient_eq_of_coprime_of_solvable_right
      (N := X) (Y := H) (R := R0) hXH hcopXR0
  have hZq : IsZGroup (centralizerWithin Hq R0q) := by
    change IsZGroup (centralizerWithin
      (H.map (QuotientGroup.mk' X))
      (R0.map (QuotientGroup.mk' X)))
    rw [← hmapCent]
    letI : IsZGroup (centralizerWithin H R0) := hZ
    exact IsZGroup.of_surjective
      (f := (QuotientGroup.mk' X).subgroupMap
        (centralizerWithin H R0))
      ((QuotientGroup.mk' X).subgroupMap_surjective
        (centralizerWithin H R0))
  have hrec : IsPLengthOne p (⁅Rq, Hq⁆ : Subgroup (G ⧸ X)) :=
    ih (Nat.card (G ⧸ X)) hlt (G ⧸ X) rfl Hq Rq R0q
      hcompq hcopq hoddq hR0qRq hR0qprime hZq
  have hcommq : ⁅Rq, Hq⁆ = Hq := by
    dsimp only [Rq, Hq, q]
    rw [← Subgroup.map_commutator, hperfect]
  rw [hcommq] at hrec
  let e : (H ⧸ X.subgroupOf H) ≃* Hq :=
    subgroupQuotientEquivImage X H hXH
  exact isPLengthOne_of_mulEquiv hrec e.symm

/-- If the normal factor has a nontrivial `p'`-core, quotient induction and
the standard `p'`-core lifting rule close the perfect-action branch. -/
private theorem oddSemidirectZGroupPLength_of_pPrimeCore_ne_bot
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G] [Finite G] [IsSolvable G]
    (H R R0 : Subgroup G) [H.Normal]
    (hHR : H.IsComplement' R)
    (hcop : Nat.Coprime (Nat.card H) (Nat.card R))
    (hodd : Odd (Nat.card G))
    (hR0R : R0 ≤ R)
    (hR0prime : (Nat.card R0).Prime)
    (hZ : IsZGroup (centralizerWithin H R0))
    (hperfect : ⁅R, H⁆ = H)
    (hcore : pPrimeCore p H ≠ ⊥)
    (ih : ∀ m, m < Nat.card G →
      OddSemidirectZGroupPLengthStatement.{u} p m) :
    IsPLengthOne p H := by
  let O : Subgroup H := pPrimeCore p H
  let X : Subgroup G := O.map H.subtype
  letI : X.Normal := by
    dsimp only [X, O]
    infer_instance
  have hXH : X ≤ H := by
    exact Subgroup.map_subtype_le O
  have hXne : X ≠ ⊥ := by
    intro hX
    apply hcore
    apply (Subgroup.map_injective
      (f := H.subtype) H.subtype_injective)
    simpa [X, O] using hX
  have hXO : X.subgroupOf H = O := by
    dsimp only [X]
    exact Subgroup.comap_map_eq_self_of_injective
      H.subtype_injective O
  have hquot : IsPLengthOne p (H ⧸ X.subgroupOf H) :=
    oddSemidirectZGroupPLength_quotient H R R0 X hHR hcop hodd
      hR0R hR0prime hZ hperfect hXne hXH ih
  have hquotO : IsPLengthOne p (H ⧸ O) :=
    isPLengthOne_of_mulEquiv hquot
      (QuotientGroup.quotientMulEquivOfEq hXO)
  exact isPLengthOne_of_quotient_pPrimeCore hquotO

/-- A nontrivial Frattini subgroup of the `p`-core is another quotient
induction branch. -/
private theorem oddSemidirectZGroupPLength_of_frattini_pCore_ne_bot
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G] [Finite G] [IsSolvable G]
    (H R R0 : Subgroup G) [H.Normal]
    (hHR : H.IsComplement' R)
    (hcop : Nat.Coprime (Nat.card H) (Nat.card R))
    (hodd : Odd (Nat.card G))
    (hR0R : R0 ≤ R)
    (hR0prime : (Nat.card R0).Prime)
    (hZ : IsZGroup (centralizerWithin H R0))
    (hperfect : ⁅R, H⁆ = H)
    (hOA : pPrimeCore p H = ⊥)
    (hPhi : frattini (pCore p H) ≠ ⊥)
    (ih : ∀ m, m < Nat.card G →
      OddSemidirectZGroupPLengthStatement.{u} p m) :
    IsPLengthOne p H := by
  let P : Subgroup H := pCore p H
  let N : Subgroup H := (frattini P).map P.subtype
  let X : Subgroup G := N.map H.subtype
  letI : N.Normal := by
    dsimp only [N, P]
    infer_instance
  letI : X.Normal := by
    dsimp only [X, N, P]
    infer_instance
  have hNne : N ≠ ⊥ := by
    intro hN
    apply hPhi
    apply Subgroup.map_injective P.subtype_injective
    simpa [N, P] using hN
  have hXne : X ≠ ⊥ := by
    intro hX
    apply hNne
    apply Subgroup.map_injective H.subtype_injective
    simpa [X] using hX
  have hXH : X ≤ H := Subgroup.map_subtype_le N
  have hXN : X.subgroupOf H = N := by
    dsimp only [X]
    exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective N
  have hquotX : IsPLengthOne p (H ⧸ X.subgroupOf H) :=
    oddSemidirectZGroupPLength_quotient H R R0 X hHR hcop hodd
      hR0R hR0prime hZ hperfect hXne hXH ih
  have hquotN : IsPLengthOne p (H ⧸ N) :=
    isPLengthOne_of_mulEquiv hquotX
      (QuotientGroup.quotientMulEquivOfEq hXN)
  have hNp : IsPGroup p N := by
    dsimp only [N, P]
    exact (pCore_isPGroup.to_subgroup (frattini (pCore p H))).map
      (pCore p H).subtype
  have hOQ : pPrimeCore p (H ⧸ N) = ⊥ := by
    simpa [P, N] using
      (pPrimeCore_quotient_frattini_pCore_eq_bot
        (A := H) (p := p) hOA)
  exact isPLengthOne_of_isPGroup_quotient N hNp hOQ hquotN

/-- A nontrivial ambient-normal direct decomposition of the `p`-core is
closed by the two-quotient lifting rule. -/
private theorem oddSemidirectZGroupPLength_of_decomposable_pCore
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G] [Finite G] [IsSolvable G]
    (H R R0 : Subgroup G) [H.Normal]
    (hHR : H.IsComplement' R)
    (hcop : Nat.Coprime (Nat.card H) (Nat.card R))
    (hodd : Odd (Nat.card G))
    (hR0R : R0 ≤ R)
    (hR0prime : (Nat.card R0).Prime)
    (hZ : IsZGroup (centralizerWithin H R0))
    (hperfect : ⁅R, H⁆ = H)
    (hdec : ¬ NormalIndecomposableFactor
      ((pCore p H).map H.subtype))
    (ih : ∀ m, m < Nat.card G →
      OddSemidirectZGroupPLengthStatement.{u} p m) :
    IsPLengthOne p H := by
  classical
  simp only [NormalIndecomposableFactor] at hdec
  push_neg at hdec
  obtain ⟨U, W, hUnormal, hWnormal, hsup, hdis, hUne, hUneV⟩ := hdec
  let V : Subgroup G := (pCore p H).map H.subtype
  have hVH : V ≤ H := Subgroup.map_subtype_le (pCore p H)
  have hUV : U ≤ V := by
    change U ≤ (pCore p H).map H.subtype
    rw [← hsup]
    exact le_sup_left
  have hWV : W ≤ V := by
    change W ≤ (pCore p H).map H.subtype
    rw [← hsup]
    exact le_sup_right
  have hUH : U ≤ H := hUV.trans hVH
  have hWH : W ≤ H := hWV.trans hVH
  have hWne : W ≠ ⊥ := by
    intro hWbot
    apply hUneV
    simpa [V, hWbot] using hsup
  letI : U.Normal := hUnormal
  letI : W.Normal := hWnormal
  letI : (U.subgroupOf H).Normal :=
    Subgroup.Normal.subgroupOf hUnormal H
  letI : (W.subgroupOf H).Normal :=
    Subgroup.Normal.subgroupOf hWnormal H
  have hquotU : IsPLengthOne p (H ⧸ U.subgroupOf H) :=
    oddSemidirectZGroupPLength_quotient H R R0 U hHR hcop hodd
      hR0R hR0prime hZ hperfect hUne hUH ih
  have hquotW : IsPLengthOne p (H ⧸ W.subgroupOf H) :=
    oddSemidirectZGroupPLength_quotient H R R0 W hHR hcop hodd
      hR0R hR0prime hZ hperfect hWne hWH ih
  have hdisSub : Disjoint (U.subgroupOf H) (W.subgroupOf H) := by
    rw [disjoint_iff]
    apply le_antisymm _ bot_le
    intro x hx
    apply Subgroup.mem_bot.mpr
    apply Subtype.ext
    apply Subgroup.mem_bot.mp
    have hxAmbient : ((x : H) : G) ∈ U ⊓ W := hx
    rw [disjoint_iff.mp hdis] at hxAmbient
    exact hxAmbient
  exact isPLengthOne_of_two_quotients hdisSub hquotU hquotW

/-- The reduced perfect-action branch of Theorem 3.6. -/
private theorem oddSemidirectZGroupPLength_reducedCore
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G] [Finite G] [IsSolvable G]
    (H R R0 : Subgroup G) [H.Normal]
    (hHR : H.IsComplement' R)
    (hcop : Nat.Coprime (Nat.card H) (Nat.card R))
    (hodd : Odd (Nat.card G))
    (hR0R : R0 ≤ R)
    (hR0prime : (Nat.card R0).Prime)
    (hZ : IsZGroup (centralizerWithin H R0))
    (hperfect : ⁅R, H⁆ = H)
    (hOA : pPrimeCore p H = ⊥)
    (hPhi : frattini (pCore p H) = ⊥)
    (hindecomp : NormalIndecomposableFactor
      ((pCore p H).map H.subtype))
    (ih : ∀ m, m < Nat.card G →
      OddSemidirectZGroupPLengthStatement.{u} p m) :
    IsPLengthOne p H := by
  classical
  letI : IsSolvable H := isSolvable_subgroup_of_isSolvable H
  let Vh : Subgroup H := pCore p H
  let V : Subgroup G := Vh.map H.subtype
  letI : Vh.Characteristic := by
    dsimp only [Vh]
    infer_instance
  letI : V.Normal := by
    dsimp only [V]
    infer_instance
  have hVH : V ≤ H := Subgroup.map_subtype_le Vh
  have hVsubH : V.subgroupOf H = Vh := by
    dsimp only [V]
    exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective Vh
  have hVhElem : IsElementaryAbelianGroup p Vh := by
    dsimp only [Vh]
    exact isElementaryAbelianGroup_of_frattini_eq_bot
      pCore_isPGroup hPhi
  have hVelem : IsElementaryAbelianGroup p V :=
    isElementaryAbelianGroup_map hVhElem H.subtype
  by_cases hVbot : V = ⊥
  · have hVhbot : Vh = ⊥ := by
      apply (Subgroup.map_eq_bot_iff_of_injective
        Vh H.subtype_injective).mp
      simpa only [V] using hVbot
    have hcent :
        Subgroup.centralizer (pCore p H : Set H) ≤ pCore p H :=
      centralizer_pCore_le_pCore_of_pPrimeCore_eq_bot hOA
    have hallOne : ∀ x : H, x = 1 := by
      intro x
      have hxcent : x ∈ Subgroup.centralizer (pCore p H : Set H) := by
        rw [show pCore p H = ⊥ from hVhbot,
          Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Subgroup.mem_bot.mp hy]
        simp
      have hxbot : x ∈ (⊥ : Subgroup H) := by
        rw [← hVhbot]
        exact hcent hxcent
      exact Subgroup.mem_bot.mp hxbot
    letI : Subsingleton H :=
      ⟨fun x y => (hallOne x).trans (hallOne y).symm⟩
    exact isPLengthOne_of_subsingleton
  have hVne : V ≠ ⊥ := hVbot
  let Q := H ⧸ Vh
  let q : H →* Q := QuotientGroup.mk' Vh
  let F : Subgroup Q := fittingCore Q
  let Uh : Subgroup H := F.comap q
  let U : Subgroup G := Uh.map H.subtype
  letI : F.Characteristic := by
    dsimp only [F]
    infer_instance
  letI : Group.IsNilpotent F := by
    dsimp only [F]
    infer_instance
  letI : Uh.Characteristic := by
    dsimp only [Uh, q]
    exact Subgroup.Characteristic.comap_quotient_mk
      (show F.Characteristic by infer_instance)
  letI : U.Normal := by
    dsimp only [U]
    infer_instance
  have hVhUh : Vh ≤ Uh := by
    intro x hx
    change q x ∈ F
    have hxq : q x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    rw [hxq]
    exact F.one_mem
  have hVU : V ≤ U := Subgroup.map_mono hVhUh
  have hUH : U ≤ H := Subgroup.map_subtype_le Uh
  have hUsubH : U.subgroupOf H = Uh := by
    dsimp only [U]
    exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective Uh
  have hcoreQ : pCore p Q = ⊥ := by
    simpa only [Q, Vh] using
      (pCore_quotient_pCore_eq_bot (G := H) (p := p))
  have hmapCoreLe : (pCore p F).map F.subtype ≤ pCore p Q := by
    apply le_pCore
    · exact pCore_isPGroup.map F.subtype
    · infer_instance
  have hmapCoreBot : (pCore p F).map F.subtype = ⊥ := by
    apply le_bot_iff.mp
    simpa only [hcoreQ] using hmapCoreLe
  have hcoreF : pCore p F = ⊥ := by
    exact (Subgroup.map_eq_bot_iff_of_injective
      (pCore p F) F.subtype_injective).mp hmapCoreBot
  have hpF : ¬ p ∣ Nat.card F :=
    not_dvd_natCard_of_pCore_eq_bot_of_isNilpotent hcoreF
  have hUmapF : Uh.map q = F := by
    dsimp only [Uh]
    exact Subgroup.map_comap_eq_self_of_surjective
      (QuotientGroup.mk'_surjective Vh) F
  let f : Uh →* F :=
    (q.comp Uh.subtype).codRestrict F (fun x => x.property)
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective Vh (y : Q)
    have hxUh : x ∈ Uh := by
      change QuotientGroup.mk' Vh x ∈ F
      rw [hx]
      exact y.property
    refine ⟨⟨x, hxUh⟩, ?_⟩
    apply Subtype.ext
    change QuotientGroup.mk' Vh x = (y : Q)
    exact hx
  have hfker : f.ker = Vh.subgroupOf Uh := by
    ext x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      have hx' := congrArg Subtype.val hx
      change QuotientGroup.mk' Vh (x : H) = 1 at hx'
      change (x : H) ∈ Vh
      exact (QuotientGroup.eq_one_iff (x : H)).mp hx'
    · intro hx
      apply Subtype.ext
      change QuotientGroup.mk' Vh (x : H) = 1
      exact (QuotientGroup.eq_one_iff (x : H)).mpr hx
  have hrelVhUh : Vh.relIndex Uh = Nat.card F := by
    calc
      Vh.relIndex Uh = (Vh.subgroupOf Uh).index := rfl
      _ = f.ker.index :=
        congrArg (fun X : Subgroup Uh => X.index) hfker.symm
      _ = Nat.card f.range := Subgroup.index_ker f
      _ = Nat.card F := by
        rw [MonoidHom.range_eq_top.mpr hf, Subgroup.card_top]
  have hrelVU : V.relIndex U = Vh.relIndex Uh := by
    simpa only [V, U] using
      Subgroup.relIndex_map_map_of_injective Vh Uh H.subtype_injective
  have hVUp : IsPGroup p (V.subgroupOf U) :=
    hVelem.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hVU).symm
  have hindexVU : ¬ p ∣ (V.subgroupOf U).index := by
    change ¬ p ∣ V.relIndex U
    rw [hrelVU, hrelVhUh]
    exact hpF
  let SV : Sylow p U := hVUp.toSylow hindexVU
  have hRnormU : R ≤ Subgroup.normalizer (U : Set G) := by
    rw [U.normalizer_eq_top]
    exact le_top
  have hcopUR : Nat.Coprime (Nat.card U) (Nat.card R) :=
    hcop.coprime_dvd_left (Subgroup.card_dvd_of_le hUH)
  have hsolU : IsSolvable U := isSolvable_subgroup_of_isSolvable U
  obtain ⟨K, hKU, hKHall, hRnormK⟩ :=
    exists_primeComplement_normalized_of_coprime_of_isSolvable
      (p := p) (A := R) (K := U) hRnormU hcopUR hsolU
  have hVKcomp : (V.subgroupOf U).IsComplement' (K.subgroupOf U) := by
    have hSVcoe : (SV : Subgroup U) = V.subgroupOf U := rfl
    rw [← hSVcoe]
    exact hKHall.sylow_isComplement (Fact.out : p.Prime) SV
  have hVK : V ⊔ K = U := by
    calc
      V ⊔ K = (V.subgroupOf U ⊔ K.subgroupOf U).map U.subtype := by
        rw [Subgroup.map_sup,
          Subgroup.map_subgroupOf_eq_of_le hVU,
          Subgroup.map_subgroupOf_eq_of_le hKU]
      _ = (⊤ : Subgroup U).map U.subtype := by
        rw [hVKcomp.sup_eq_top]
      _ = U := by
        rw [← MonoidHom.range_eq_map, U.range_subtype]
  have hKcopP : Nat.Coprime (Nat.card K) p := by
    simpa only [natCard_subgroupOf_eq hKU] using hKHall.card_coprime
  have hcopVK : Nat.Coprime (Nat.card V) (Nat.card K) := by
    obtain ⟨a, ha⟩ := hVelem.isPGroup.exists_card_eq
    rw [ha]
    exact hKcopP.symm.pow_left a
  letI : IsSolvable V := isSolvable_subgroup_of_isSolvable V
  have hFrattini : U ⊔ Subgroup.normalizer (K : Set G) = ⊤ :=
    normal_sup_normalizer_eq_top_of_solvable_complement
      U V K hVU hKU hVKcomp hcopVK
  let N : Subgroup G := H ⊓ Subgroup.normalizer (K : Set G)
  have hNH : N ≤ H := inf_le_left
  have hKH : K ≤ H := hKU.trans hUH
  have hKN : K ≤ N := le_inf hKH Subgroup.le_normalizer
  have hUN : U ⊔ N = H := by
    apply le_antisymm
    · exact sup_le hUH hNH
    · intro x hxH
      have hxJoin : x ∈ U ⊔ Subgroup.normalizer (K : Set G) := by
        rw [hFrattini]
        exact Subgroup.mem_top x
      have hxProd : x ∈ (U : Set G) *
          (Subgroup.normalizer (K : Set G) : Set G) := by
        rw [← Subgroup.coe_mul_of_right_le_normalizer_left
          U (Subgroup.normalizer (K : Set G))
          (by rw [U.normalizer_eq_top]; exact le_top)]
        exact hxJoin
      obtain ⟨u, hu, n, hn, hun⟩ := hxProd
      have hnH : n ∈ H := by
        have hneq : n = u⁻¹ * x := by
          rw [← hun]
          simp
        rw [hneq]
        exact H.mul_mem (H.inv_mem (hUH hu)) hxH
      have hmem : u * n ∈ U ⊔ N :=
        Subgroup.mul_mem_sup hu ⟨hnH, hn⟩
      have hun' : u * n = x := hun
      rw [hun'] at hmem
      exact hmem
  have hUleVN : U ≤ V ⊔ N := by
    rw [← hVK]
    exact sup_le le_sup_left (hKN.trans le_sup_right)
  have hVN : V ⊔ N = H := by
    apply le_antisymm
    · exact sup_le hVH hNH
    · rw [← hUN]
      exact sup_le hUleVN le_sup_right
  have hRnormN : R ≤ Subgroup.normalizer (N : Set G) := by
    exact
      (le_inf
        (show R ≤ Subgroup.normalizer (H : Set G) by
          rw [H.normalizer_eq_top]
          exact le_top)
        (hRnormK.trans Subgroup.le_normalizer)).trans
        Subgroup.inf_normalizer_le_normalizer_inf
  have hcopNR : Nat.Coprime (Nat.card N) (Nat.card R) :=
    hcop.coprime_dvd_left (Subgroup.card_dvd_of_le hNH)
  have hsolN : IsSolvable N := isSolvable_subgroup_of_isSolvable N
  obtain ⟨PN, hRnormPN⟩ :=
    exists_sylow_normalized_of_coprime_of_isSolvable
      (p := p) (A := R) (L := N) hRnormN hcopNR hsolN
  let P : Subgroup G := (PN : Subgroup N).map N.subtype
  have hPdef : P = (PN : Subgroup N).map N.subtype := rfl
  have hPN : P ≤ N := Subgroup.map_subtype_le _
  have hPH : P ≤ H := hPN.trans hNH
  have hPnormK : P ≤ Subgroup.normalizer (K : Set G) :=
    hPN.trans inf_le_right
  have hPp : IsPGroup p P := PN.isPGroup'.map N.subtype
  have hRnormP : R ≤ Subgroup.normalizer (P : Set G) := by
    simpa only [P] using hRnormPN
  obtain ⟨SH, hSH⟩ :=
    exists_sylow_map_eq_sup_of_normal_sup_eq
      H V N P hVH hNH hVN hVelem.isPGroup PN hPdef
  by_cases hKPbot : ⁅K, P⁆ = ⊥
  · have hPKbot : ⁅P, K⁆ = ⊥ := by
      rw [Subgroup.commutator_comm]
      exact hKPbot
    have hPUcomm : ⁅P, U⁆ ≤ V := by
      rw [← hVK]
      apply commutator_sup_le_of_normal
      · exact Subgroup.commutator_le_right P V
      · rw [hPKbot]
        exact bot_le
    let PH : Subgroup H := P.subgroupOf H
    have hPHp : IsPGroup p PH :=
      hPp.of_equiv (Subgroup.subgroupOfEquivOfLe hPH).symm
    have hcommPHUh : ⁅PH, Uh⁆ ≤ Vh := by
      apply (Subgroup.map_le_map_iff_of_injective
        H.subtype_injective).mp
      rw [Subgroup.map_commutator,
        Subgroup.map_subgroupOf_eq_of_le hPH]
      change ⁅P, U⁆ ≤ V
      exact hPUcomm
    let Pq : Subgroup Q := PH.map q
    have hPqp : IsPGroup p Pq := by
      dsimp only [Pq]
      exact hPHp.map q
    have hPqcent : Pq ≤ Subgroup.centralizer (F : Set Q) := by
      rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
      change ⁅PH.map q, F⁆ = ⊥
      rw [← hUmapF, ← Subgroup.map_commutator,
        Subgroup.map_eq_bot_iff]
      change ⁅PH, Uh⁆ ≤ (QuotientGroup.mk' Vh).ker
      rw [QuotientGroup.ker_mk']
      exact hcommPHUh
    have hPqF : Pq ≤ F :=
      hPqcent.trans (centralizer_fittingCore_le (G := Q))
    have hPqSubp : IsPGroup p (Pq.subgroupOf F) :=
      hPqp.of_equiv (Subgroup.subgroupOfEquivOfLe hPqF).symm
    have hPqSubBot : Pq.subgroupOf F = ⊥ :=
      subgroup_eq_bot_of_isPGroup_of_not_dvd_natCard
        (Pq.subgroupOf F) hPqSubp hpF
    have hPqBot : Pq = ⊥ := by
      calc
        Pq = Pq ⊓ F := (inf_eq_left.mpr hPqF).symm
        _ = ⊥ := disjoint_iff.mp
          (Subgroup.subgroupOf_eq_bot.mp hPqSubBot)
    have hPHVh : PH ≤ Vh := by
      have hmapBot : PH.map q = ⊥ := by
        simpa only [Pq] using hPqBot
      rw [Subgroup.map_eq_bot_iff] at hmapBot
      change PH ≤ (QuotientGroup.mk' Vh).ker at hmapBot
      rw [QuotientGroup.ker_mk'] at hmapBot
      exact hmapBot
    have hPV : P ≤ V := by
      calc
        P = PH.map H.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hPH).symm
        _ ≤ Vh.map H.subtype := Subgroup.map_mono hPHVh
        _ = V := rfl
    have hSHcore : (SH : Subgroup H) = pCore p H := by
      apply (Subgroup.map_injective
        (f := H.subtype) H.subtype_injective)
      calc
        (SH : Subgroup H).map H.subtype = V ⊔ P := hSH
        _ = V := sup_eq_left.mpr hPV
        _ = Vh.map H.subtype := rfl
        _ = (pCore p H).map H.subtype := rfl
    rw [IsPLengthOne]
    have hOp : IsPGroup p (pPrimeCore p H) := by
      rw [hOA]
      exact IsPGroup.of_bot
    let SQ : Sylow p (H ⧸ pPrimeCore p H) :=
      SH.mapSurjective
        (QuotientGroup.mk'_surjective (pPrimeCore p H))
    refine ⟨SQ, ?_⟩
    dsimp only [SQ]
    rw [Sylow.coe_mapSurjective, hSHcore]
    exact map_pCore_quotient_eq
      (G := H) (p := p) (N := pPrimeCore p H) hOp
  · exfalso
    -- The nontrivial mixed-commutator branch is impossible.
    have hKPne : ⁅K, P⁆ ≠ ⊥ := hKPbot
    have hKnormV : K ≤ Subgroup.normalizer (V : Set G) :=
      Subgroup.le_normalizer_of_normal
    have hPnormV : P ≤ Subgroup.normalizer (V : Set G) :=
      Subgroup.le_normalizer_of_normal
    have hRnormV : R ≤ Subgroup.normalizer (V : Set G) :=
      Subgroup.le_normalizer_of_normal
    have hcopKP : Nat.Coprime (Nat.card K) (Nat.card P) := by
      obtain ⟨a, ha⟩ := hPp.exists_card_eq
      rw [ha]
      exact hKcopP.pow_right a
    have hdisVK : Disjoint V K :=
      Subgroup.disjoint_of_coprime_natCard hcopVK
    have hCVH : centralizerWithin H V = V := by
      apply le_antisymm
      · intro x hx
        let xH : H := ⟨x, hx.1⟩
        have hxcent : xH ∈
            Subgroup.centralizer (pCore p H : Set H) := by
          rw [Subgroup.mem_centralizer_iff]
          intro v hv
          have hvV : (v : G) ∈ V := by
            change (v : G) ∈ Vh.map H.subtype
            exact ⟨v, hv, rfl⟩
          exact Subtype.ext (hx.2 (v : G) hvV)
        have hxcore :=
          centralizer_pCore_le_pCore_of_pPrimeCore_eq_bot hOA hxcent
        change x ∈ Vh.map H.subtype
        exact ⟨xH, hxcore, rfl⟩
      · intro v hv
        refine ⟨hVH hv, ?_⟩
        intro w hw
        exact congrArg Subtype.val
          ((isMulCommutative_iff.mp hVelem.commutative)
            (⟨w, hw⟩ : V) (⟨v, hv⟩ : V))
    let C : Subgroup G := centralizerWithin V K
    let D : Subgroup G := ⁅K, V⁆
    have hCleV : C ≤ V := centralizerWithin_le_left V K
    have hDleV : D ≤ V := Subgroup.commutator_le_right K V
    have hVnormC : V ≤ Subgroup.normalizer (C : Set G) := by
      apply (show V ≤ Subgroup.centralizer (C : Set G) from ?_).trans
        (Subgroup.centralizer_le_normalizer (C : Set G))
      intro v hv
      rw [Subgroup.mem_centralizer_iff]
      intro c hc
      exact congrArg (fun v : V => (v : G))
        ((isMulCommutative_iff.mp hVelem.commutative)
          (⟨c, hCleV hc⟩ : V) (⟨v, hv⟩ : V))
    have hNnormC : N ≤ Subgroup.normalizer (C : Set G) := by
      intro n hn
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      have hmapV : V.map (MulAut.conj n).toMonoidHom = V :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp
          ((Subgroup.le_normalizer_of_normal :
            N ≤ Subgroup.normalizer (V : Set G)) hn)
      have hmapK : K.map (MulAut.conj n).toMonoidHom = K :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (hn.2)
      dsimp only [C]
      change (centralizerWithin V K).map
        (MulAut.conj n).toMonoidHom = centralizerWithin V K
      rw [map_centralizerWithin_equiv (MulAut.conj n) hmapV, hmapK]
    have hRnormC : R ≤ Subgroup.normalizer (C : Set G) := by
      intro r hr
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      have hmapV : V.map (MulAut.conj r).toMonoidHom = V :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (hRnormV hr)
      have hmapK : K.map (MulAut.conj r).toMonoidHom = K :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (hRnormK hr)
      dsimp only [C]
      change (centralizerWithin V K).map
        (MulAut.conj r).toMonoidHom = centralizerWithin V K
      rw [map_centralizerWithin_equiv (MulAut.conj r) hmapV, hmapK]
    have hgenVNR : (V ⊔ N) ⊔ R = ⊤ := by
      rw [hVN, hHR.sup_eq_top]
    letI : C.Normal := by
      rw [← Subgroup.normalizer_eq_top_iff]
      apply top_unique
      rw [← hgenVNR]
      exact sup_le (sup_le hVnormC hNnormC) hRnormC
    have hVnormD : V ≤ Subgroup.normalizer (D : Set G) := by
      dsimp only [D]
      exact Subgroup.normalizer_commutator_ge_right K V
    have hNnormD : N ≤ Subgroup.normalizer (D : Set G) := by
      intro n hn
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      dsimp only [D]
      rw [Subgroup.map_commutator,
        Subgroup.mem_normalizer_iff_map_conj_eq.mp hn.2,
        Subgroup.mem_normalizer_iff_map_conj_eq.mp
          ((Subgroup.le_normalizer_of_normal :
            N ≤ Subgroup.normalizer (V : Set G)) hn)]
    have hRnormD : R ≤ Subgroup.normalizer (D : Set G) := by
      intro r hr
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      dsimp only [D]
      rw [Subgroup.map_commutator,
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (hRnormK hr),
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (hRnormV hr)]
    letI : D.Normal := by
      rw [← Subgroup.normalizer_eq_top_iff]
      apply top_unique
      rw [← hgenVNR]
      exact sup_le (sup_le hVnormD hNnormD) hRnormD
    have hDCsup : D ⊔ C = V := by
      apply le_antisymm
      · exact sup_le hDleV hCleV
      · exact le_commutator_sup_centralizerWithin_of_coprime
          hKnormV hcopVK
    have hKnormD : K ≤ Subgroup.normalizer (D : Set G) := by
      dsimp only [D]
      exact Subgroup.normalizer_commutator_ge_left K V
    have hperfectD : ⁅K, D⁆ = D := by
      dsimp only [D]
      exact commutator_commutator_eq_of_coprime hKnormV hcopVK
    have hDcomm : IsMulCommutative D := by
      apply isMulCommutative_iff.mpr
      intro x y
      apply Subtype.ext
      change (x : G) * (y : G) = (y : G) * (x : G)
      exact congrArg (fun v : V => (v : G))
        ((isMulCommutative_iff.mp hVelem.commutative)
          (⟨x, hDleV x.property⟩ : V)
          (⟨y, hDleV y.property⟩ : V))
    have hCDfix : centralizerWithin D K = ⊥ := by
      apply le_bot_iff.mp
      exact (centralizerWithin_le_commutator_of_perfect_coprime_action
        hKnormD
        (hcopVK.coprime_dvd_left (Subgroup.card_dvd_of_le hDleV))
        hperfectD).trans
          (by
            rw [le_bot_iff,
              Subgroup.commutator_eq_bot_iff_le_centralizer]
            exact Subgroup.le_centralizer_iff_isMulCommutative.mpr hDcomm)
    have hCDdis : Disjoint C D := by
      rw [disjoint_iff]
      apply le_bot_iff.mp
      intro x hx
      have hxfix : x ∈ centralizerWithin D K :=
        ⟨hx.2, hx.1.2⟩
      rw [hCDfix] at hxfix
      exact hxfix
    have hCcase : C = ⊥ ∨ C = V :=
      hindecomp C D inferInstance inferInstance
        (by rw [sup_comm]; exact hDCsup) hCDdis
    have hCVK : centralizerWithin V K = ⊥ := by
      dsimp only [C] at hCcase ⊢
      rcases hCcase with hCbot | hCV
      · exact hCbot
      · exfalso
        have hKcentV : K ≤ Subgroup.centralizer (V : Set G) := by
          apply Subgroup.le_centralizer_iff.mp
          rw [← hCV]
          exact inf_le_right
        have hKCV : K ≤ centralizerWithin H V :=
          le_inf hKH hKcentV
        have hKV : K ≤ V := by rw [← hCVH]; exact hKCV
        have hKbot : K = ⊥ := by
          apply le_antisymm _ bot_le
          intro k hk
          have hkI : k ∈ V ⊓ K := ⟨hKV hk, hk⟩
          rw [disjoint_iff.mp hdisVK] at hkI
          exact hkI
        apply hKPne
        rw [hKbot, Subgroup.commutator_bot_left]
    have hVNdis : Disjoint V N := by
      rw [disjoint_iff]
      apply le_bot_iff.mp
      intro x hx
      have hxcent : x ∈ Subgroup.centralizer (K : Set G) :=
        mem_centralizer_of_mem_of_mem_normalizer_of_coprime
          hKnormV hcopVK hx.1 hx.2.2
      have hxC : x ∈ centralizerWithin V K := ⟨hx.1, hxcent⟩
      rw [hCVK] at hxC
      exact hxC
    have hVPdis : Disjoint V P :=
      hVNdis.mono_right hPN
    have hcardKF : Nat.card K = Nat.card F := by
      calc
        Nat.card K = Nat.card (K.subgroupOf U) :=
          (natCard_subgroupOf_eq hKU).symm
        _ = (V.subgroupOf U).index :=
          hVKcomp.symm.index_eq_card.symm
        _ = V.relIndex U := rfl
        _ = Vh.relIndex Uh := hrelVU
        _ = Nat.card F := hrelVhUh
    let iKH : K →* H := Subgroup.inclusion hKH
    let fK : K →* F :=
      (q.comp iKH).codRestrict F (fun k => by
        have hkUh : iKH k ∈ Uh := by
          rw [← hUsubH]
          exact hKU k.property
        exact hkUh)
    have hfKinj : Function.Injective fK := by
      intro a b hab
      have habq : q (iKH a) = q (iKH b) :=
        congrArg Subtype.val hab
      have hdVh : (iKH a)⁻¹ * iKH b ∈ Vh :=
        QuotientGroup.eq.mp habq
      have hdV : (a : G)⁻¹ * (b : G) ∈ V := by
        change (a : G)⁻¹ * (b : G) ∈ Vh.map H.subtype
        exact ⟨(iKH a)⁻¹ * iKH b, hdVh, rfl⟩
      have hdK : (a : G)⁻¹ * (b : G) ∈ K :=
        K.mul_mem (K.inv_mem a.property) b.property
      have hdOne : (a : G)⁻¹ * (b : G) = 1 := by
        apply Subgroup.mem_bot.mp
        rw [← disjoint_iff.mp hdisVK]
        exact ⟨hdV, hdK⟩
      exact Subtype.ext (inv_mul_eq_one.mp hdOne)
    letI : Fintype K := Fintype.ofFinite K
    letI : Fintype F := Fintype.ofFinite F
    have hfKbij : Function.Bijective fK :=
      (Fintype.bijective_iff_injective_and_card fK).mpr
        ⟨hfKinj, by simpa only [Nat.card_eq_fintype_card] using hcardKF⟩
    let eKF : K ≃* F := MulEquiv.ofBijective fK hfKbij
    have hKnil : Group.IsNilpotent K :=
      Group.nilpotent_of_mulEquiv eKF.symm
    let fN : N →* Q := q.comp (Subgroup.inclusion hNH)
    have hfNsurj : Function.Surjective fN := by
      intro z
      obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective Vh z
      have hh : (h : G) ∈ V ⊔ N := by
        rw [hVN]
        exact h.property
      have hprod : (h : G) ∈ (V : Set G) * (N : Set G) := by
        rw [← Subgroup.coe_mul_of_right_le_normalizer_left V N
          (by rw [V.normalizer_eq_top]; exact le_top)]
        exact hh
      obtain ⟨v, hv, n, hn, hvn⟩ := hprod
      let vH : H := ⟨v, hVH hv⟩
      let nH : H := ⟨n, hNH hn⟩
      refine ⟨⟨n, hn⟩, ?_⟩
      change q nH = q h
      have hvone : q vH = 1 := by
        apply (QuotientGroup.eq_one_iff vH).mpr
        rw [← hVsubH]
        exact hv
      have heq : vH * nH = h := Subtype.ext hvn
      rw [← heq, map_mul, hvone, one_mul]
    have hfNinj : Function.Injective fN := by
      intro a b hab
      have hdVh :
          ((Subgroup.inclusion hNH a)⁻¹ * Subgroup.inclusion hNH b) ∈ Vh :=
        QuotientGroup.eq.mp hab
      have hdV : (a : G)⁻¹ * (b : G) ∈ V := by
        change (a : G)⁻¹ * (b : G) ∈ Vh.map H.subtype
        exact ⟨(Subgroup.inclusion hNH a)⁻¹ *
          Subgroup.inclusion hNH b, hdVh, rfl⟩
      have hdN : (a : G)⁻¹ * (b : G) ∈ N :=
        N.mul_mem (N.inv_mem a.property) b.property
      have hdOne : (a : G)⁻¹ * (b : G) = 1 := by
        apply Subgroup.mem_bot.mp
        rw [← disjoint_iff.mp hVNdis]
        exact ⟨hdV, hdN⟩
      exact Subtype.ext (inv_mul_eq_one.mp hdOne)
    let eNQ : N ≃* Q :=
      MulEquiv.ofBijective fN ⟨hfNinj, hfNsurj⟩
    let KN : Subgroup N := K.subgroupOf N
    have hKNmap : KN.map eNQ.toMonoidHom = F := by
      apply le_antisymm
      · rintro y ⟨k, hk, rfl⟩
        change q (Subgroup.inclusion hNH k) ∈ F
        let kk : K := ⟨(k : G), hk⟩
        exact (fK kk).property
      · intro y hy
        obtain ⟨k, hk⟩ := hfKbij.2 ⟨y, hy⟩
        let kN : KN := ⟨⟨(k : G), hKN k.property⟩, k.property⟩
        refine ⟨kN, kN.property, ?_⟩
        exact congrArg Subtype.val hk
    have hfitN : fittingCore N = KN := by
      apply Subgroup.map_injective (f := eNQ.toMonoidHom) eNQ.injective
      rw [map_fittingCore_mulEquiv eNQ, hKNmap]
    have hCHK : centralizerWithin H K ≤ K := by
      intro x hx
      have hxNorm : x ∈ Subgroup.normalizer (K : Set G) :=
        Subgroup.centralizer_le_normalizer (K : Set G) hx.2
      let xN : N := ⟨x, hx.1, hxNorm⟩
      have hxCentN : xN ∈ Subgroup.centralizer (KN : Set N) := by
        rw [Subgroup.mem_centralizer_iff]
        intro k hk
        apply Subtype.ext
        exact hx.2 (k : G) hk
      have hxFit : xN ∈ fittingCore N := by
        apply centralizer_fittingCore_le
        simpa only [hfitN] using hxCentN
      rw [hfitN] at hxFit
      exact hxFit
    have hCKV : centralizerWithin K V = ⊥ := by
      apply le_bot_iff.mp
      intro x hx
      have hxHV : x ∈ centralizerWithin H V :=
        ⟨hKH hx.1, hx.2⟩
      have hxV : x ∈ V := by rw [hCVH] at hxHV; exact hxHV
      have hxI : x ∈ V ⊓ K := ⟨hxV, hx.1⟩
      rw [disjoint_iff.mp hdisVK] at hxI
      exact hxI
    have hKR0ne : ⁅K, R0⁆ ≠ ⊥ := by
      intro hKR0bot
      have hKcentR0 : K ≤ Subgroup.centralizer (R0 : Set G) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp hKR0bot
      have hKCR0 : K ≤ centralizerWithin H R0 :=
        le_inf hKH hKcentR0
      let fZ : K →* centralizerWithin H R0 :=
        Subgroup.inclusion hKCR0
      letI : IsZGroup (centralizerWithin H R0) := hZ
      letI : IsZGroup K :=
        IsZGroup.of_injective (f := fZ)
          (Subgroup.inclusion_injective hKCR0)
      letI : Group.IsNilpotent K := hKnil
      have hKcyc : IsCyclic K := inferInstance
      have hNRcent : ⁅N, R⁆ ≤ Subgroup.centralizer (K : Set G) :=
        commutator_le_centralizer_of_normalizes_isCyclic
          K N R hKcyc inf_le_right hRnormK
      have hNRleH : ⁅N, R⁆ ≤ H :=
        (Subgroup.commutator_mono hNH le_rfl).trans
          (Subgroup.commutator_le_left H R)
      have hNRleK : ⁅N, R⁆ ≤ K := by
        exact (le_inf hNRleH hNRcent).trans hCHK
      have hHleU : H ≤ U := by
        rw [← hperfect, ← hVN]
        apply commutator_sup_le_of_normal
        · exact (Subgroup.commutator_le_right R V).trans hVU
        · rw [Subgroup.commutator_comm]
          exact hNRleK.trans hKU
      have hPU : P ≤ U := hPH.trans hHleU
      let PU : Subgroup U := P.subgroupOf U
      have hPUp : IsPGroup p PU :=
        hPp.of_equiv (Subgroup.subgroupOfEquivOfLe hPU).symm
      obtain ⟨TP, hPUTP⟩ := hPUp.exists_le_sylow
      letI : (V.subgroupOf U).Normal :=
        Subgroup.Normal.subgroupOf (inferInstance : V.Normal) U
      have hSVnormal : (SV : Subgroup U).Normal := by
        change (V.subgroupOf U).Normal
        infer_instance
      letI : Unique (Sylow p U) :=
        Sylow.unique_of_normal SV hSVnormal
      have hTP : TP = SV := Subsingleton.elim TP SV
      have hPV : P ≤ V := by
        intro x hx
        let xU : U := ⟨x, hPU hx⟩
        have hxTP : xU ∈ (TP : Subgroup U) := hPUTP hx
        rw [hTP] at hxTP
        exact hxTP
      have hPbot : P = ⊥ := by
        apply le_antisymm _ bot_le
        intro x hx
        have hxI : x ∈ V ⊓ P := ⟨hPV hx, hx⟩
        rw [disjoint_iff.mp hVPdis] at hxI
        exact hxI
      apply hKPne
      rw [hPbot, Subgroup.commutator_bot_right]
    have hcopKR0 : Nat.Coprime (Nat.card K) (Nat.card R0) :=
      hcop.coprime_dvd_left (Subgroup.card_dvd_of_le hKH) |>.coprime_dvd_right
        (Subgroup.card_dvd_of_le hR0R)
    have hpR0 : Nat.Coprime p (Nat.card R0) := by
      have hpV : p ∣ Nat.card V :=
        hVelem.isPGroup.card_eq_or_dvd.resolve_left
          (V.one_lt_card_iff_ne_bot.mpr hVne).ne'
      exact (hcop.coprime_dvd_left (Subgroup.card_dvd_of_le hVH)
        |>.coprime_dvd_right (Subgroup.card_dvd_of_le hR0R))
        |>.coprime_dvd_left hpV
    have hCVR0ne : centralizerWithin V R0 ≠ ⊥ := by
      intro hCVR0bot
      let J : Subgroup G := K ⊔ R0
      have hKJ : K ≤ J := le_sup_left
      have hR0J : R0 ≤ J := le_sup_right
      let KJ : Subgroup J := K.subgroupOf J
      let R0J : Subgroup J := R0.subgroupOf J
      have hR0normK : R0 ≤ Subgroup.normalizer (K : Set G) :=
        hR0R.trans hRnormK
      have hJnormK : J ≤ Subgroup.normalizer (K : Set G) :=
        sup_le Subgroup.le_normalizer hR0normK
      letI : KJ.Normal :=
        Subgroup.normal_subgroupOf_of_le_normalizer hJnormK
      have hKJmap : KJ.map J.subtype = K :=
        Subgroup.map_subgroupOf_eq_of_le hKJ
      have hR0Jmap : R0J.map J.subtype = R0 :=
        Subgroup.map_subgroupOf_eq_of_le hR0J
      have hcardKJ : Nat.card KJ = Nat.card K :=
        natCard_subgroupOf_eq hKJ
      have hcardR0J : Nat.card R0J = Nat.card R0 :=
        natCard_subgroupOf_eq hR0J
      have hdisJ : Disjoint KJ R0J := by
        rw [disjoint_iff]
        apply le_bot_iff.mp
        intro x hx
        apply Subgroup.mem_bot.mpr
        apply Subtype.ext
        apply Subgroup.mem_bot.mp
        have hxG : (x : G) ∈ K ⊓ R0 := hx
        rw [disjoint_iff.mp
          (Subgroup.disjoint_of_coprime_natCard hcopKR0)] at hxG
        exact hxG
      have hsupJ : KJ ⊔ R0J = ⊤ := by
        rw [← Subgroup.subgroupOf_sup hKJ hR0J]
        exact Subgroup.subgroupOf_self J
      have hcompJ : KJ.IsComplement' R0J := by
        apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisJ
        rw [← Subgroup.normal_mul KJ R0J, hsupJ]
        rfl
      have hcopJ : Nat.Coprime (Nat.card KJ) (Nat.card R0J) := by
        simpa only [hcardKJ, hcardR0J] using hcopKR0
      letI : IsSolvable J := isSolvable_subgroup_of_isSolvable J
      have hoddJ : Odd (Nat.card J) :=
        hodd.of_dvd_nat J.card_subgroup_dvd_card
      have hR0Jprime : (Nat.card R0J).Prime := by
        rw [hcardR0J]
        exact hR0prime
      have hpK : Nat.Coprime p (Nat.card K) := hKcopP.symm
      have hpJ : Nat.Coprime p (Nat.card J) := by
        rw [← hcompJ.card_mul, hcardKJ, hcardR0J]
        exact hpK.mul_right hpR0
      have hJcard : (Nat.card J : ZMod p) ≠ 0 := by
        letI : NeZero (Nat.card J : ZMod p) :=
          NeZero.of_not_dvd (ZMod p)
            ((Fact.out : p.Prime).coprime_iff_not_dvd.mp hpJ)
        exact NeZero.ne _
      have hJnormV : J ≤ Subgroup.normalizer (V : Set G) :=
        sup_le hKnormV (hR0R.trans hRnormV)
      let aJ : J →* MulAut V :=
        V.normalizerMonoidHom.comp (Subgroup.inclusion hJnormV)
      letI : IsMulCommutative V := hVelem.commutative
      letI : Module (ZMod p) (Additive V) :=
        AddCommGroup.zmodModule fun x => hVelem.pow_eq_one x.toMul
      let endMonoid : Monoid (Module.End (ZMod p) (Additive V)) :=
        Module.End.instMonoid
      letI : Monoid (Module.End (ZMod p) (Additive V)) := endMonoid
      letI : MulOne (Module.End (ZMod p) (Additive V)) :=
        endMonoid.toMulOne
      letI : MulOneClass (Module.End (ZMod p) (Additive V)) :=
        endMonoid.toMulOneClass
      let sigma : Representation (ZMod p) J (Additive V) :=
        elementaryAbelianActionRepresentation V J p aJ
      letI : Fintype J := Fintype.ofFinite J
      have hfixSigma :=
          (Submodule.eq_bot_iff (Representation.invariants
            (sigma.comp R0J.subtype :
              Representation (ZMod p) R0J (Additive V)))).mpr (by
        intro x hx
        change x.toMul = 1
        have hxC : (x.toMul : G) ∈ centralizerWithin V R0 := by
          refine ⟨x.toMul.property, ?_⟩
          intro r hr
          let rJ : R0J := ⟨⟨r, hR0J hr⟩, hr⟩
          have hfixed :=
            (Representation.mem_invariants _ x).mp hx rJ
          change Additive.ofMul (aJ (rJ : J) x.toMul) = x at hfixed
          have hconj : r * (x.toMul : G) * r⁻¹ = x.toMul :=
            congrArg (fun z : Additive V => (z.toMul : G)) hfixed
          calc
            r * (x.toMul : G) =
                (r * (x.toMul : G) * r⁻¹) * r := by group
            _ = (x.toMul : G) * r := by rw [hconj]
        rw [hCVR0bot] at hxC
        exact Subtype.ext (Subgroup.mem_bot.mp hxC))
      have hkill := odd_prime_sdprod_rfix0 sigma KJ R0J hcompJ
        hcopJ hoddJ hR0Jprime hJcard hfixSigma
      have hlocalBot : ⁅R0J, KJ⁆ = ⊥ := by
        apply le_bot_iff.mp
        intro z hz
        have hzker := hkill hz
        have hzKJ : z ∈ KJ :=
          Subgroup.commutator_le_right R0J KJ hz
        have hzCent : (z : G) ∈ Subgroup.centralizer (V : Set G) := by
          rw [Subgroup.mem_centralizer_iff]
          intro v hv
          let vv : V := ⟨v, hv⟩
          have hsigma := MonoidHom.mem_ker.mp hzker
          have hfixed : aJ z vv = vv := by
            have hzfun := LinearMap.congr_fun hsigma (Additive.ofMul vv)
            change Additive.ofMul (aJ z vv) = Additive.ofMul vv at hzfun
            exact congrArg Additive.toMul hzfun
          have hconj : (z : G) * v * (z : G)⁻¹ = v :=
            congrArg Subtype.val hfixed
          calc
            v * (z : G) = ((z : G) * v * (z : G)⁻¹) * (z : G) := by
              rw [hconj]
            _ = (z : G) * v := by group
        have hzWithin : (z : G) ∈ centralizerWithin K V :=
          ⟨hzKJ, hzCent⟩
        rw [hCKV] at hzWithin
        exact Subtype.ext (Subgroup.mem_bot.mp hzWithin)
      apply hKR0ne
      rw [Subgroup.commutator_comm]
      calc
        (⁅R0, K⁆ : Subgroup G) =
            (⁅R0J, KJ⁆ : Subgroup J).map J.subtype := by
          rw [Subgroup.map_commutator, hR0Jmap, hKJmap]
        _ = ⊥ := by rw [hlocalBot, Subgroup.map_bot]
    let C0 : Subgroup G := centralizerWithin V R0
    have hC0leMain : C0 ≤ centralizerWithin H R0 := by
      intro x hx
      exact ⟨hVH hx.1, hx.2⟩
    let fC0 : C0 →* centralizerWithin H R0 :=
      Subgroup.inclusion hC0leMain
    letI : IsZGroup (centralizerWithin H R0) := hZ
    letI : IsZGroup C0 :=
      IsZGroup.of_injective (f := fC0)
        (Subgroup.inclusion_injective hC0leMain)
    have hC0p : IsPGroup p C0 :=
      hVelem.isPGroup.to_le (centralizerWithin_le_left V R0)
    letI : Group.IsNilpotent C0 := hC0p.isNilpotent
    have hC0cyc : IsCyclic C0 := inferInstance
    letI : IsCyclic C0 := hC0cyc
    letI : Nontrivial C0 :=
      (Subgroup.nontrivial_iff_ne_bot C0).mpr (by
        simpa only [C0] using hCVR0ne)
    have hC0pow (c : C0) : c ^ p = 1 := by
      apply Subtype.ext
      exact congrArg V.subtype
        (hVelem.pow_eq_one
          ⟨(c : G), centralizerWithin_le_left V R0 c.property⟩)
    have hC0exp : Monoid.exponent C0 = p :=
      (Monoid.exponent_eq_prime_iff (Fact.out : p.Prime)).mpr
        (fun c hc => orderOf_eq_prime (hC0pow c) hc)
    have hCVR0card : Nat.card (centralizerWithin V R0) = p := by
      change Nat.card C0 = p
      calc
        Nat.card C0 = Monoid.exponent C0 := IsCyclic.exponent_eq_card.symm
        _ = p := hC0exp
    have hVPp : IsPGroup p (V ⊔ P : Subgroup G) := by
      rw [← hSH]
      exact SH.isPGroup'.map H.subtype
    let T0 : Subgroup G := centralizerWithin (V ⊔ P) R0
    have hT0leMain : T0 ≤ centralizerWithin H R0 := by
      intro x hx
      exact ⟨(sup_le hVH hPH) hx.1, hx.2⟩
    let fT0 : T0 →* centralizerWithin H R0 :=
      Subgroup.inclusion hT0leMain
    letI : IsZGroup T0 :=
      IsZGroup.of_injective (f := fT0)
        (Subgroup.inclusion_injective hT0leMain)
    have hT0p : IsPGroup p T0 :=
      hVPp.to_le (centralizerWithin_le_left (V ⊔ P) R0)
    have hC0T0 : centralizerWithin V R0 ≤ T0 := by
      intro x hx
      exact ⟨(show V ≤ V ⊔ P from le_sup_left) hx.1, hx.2⟩
    have hCP0T0 : centralizerWithin P R0 ≤ T0 := by
      intro x hx
      exact ⟨(show P ≤ V ⊔ P from le_sup_right) hx.1, hx.2⟩
    have hCPR0bot : centralizerWithin P R0 = ⊥ := by
      by_cases hT0bot : T0 = ⊥
      · apply le_bot_iff.mp
        rw [← hT0bot]
        exact hCP0T0
      letI : Group.IsNilpotent T0 := hT0p.isNilpotent
      have hT0cyc : IsCyclic T0 := inferInstance
      letI : IsCyclic T0 := hT0cyc
      let CV0 : Subgroup T0 :=
        (centralizerWithin V R0).subgroupOf T0
      have hCV0card : Nat.card CV0 = p := by
        rw [natCard_subgroupOf_eq hC0T0, hCVR0card]
      have hOmegaCard : Nat.card (omegaOne p T0) = p :=
        card_omegaOne_of_isCyclic_isPGroup
          (Fact.out : p.Prime) hT0p
          (T0.one_lt_card_iff_ne_bot.mpr hT0bot).ne'
      have hCV0Omega : CV0 ≤ omegaOne p T0 := by
        intro x hx
        rw [omegaOne_eq_powMonoidHom_ker, MonoidHom.mem_ker]
        apply Subtype.ext
        have hxV : ((x : T0) : G) ∈ V := hx.1
        exact congrArg V.subtype
          (hVelem.pow_eq_one ⟨((x : T0) : G), hxV⟩)
      have hCV0eqOmega : CV0 = omegaOne p T0 :=
        Subgroup.eq_of_le_of_card_ge hCV0Omega (by
          rw [hCV0card, hOmegaCard])
      by_contra hCPne
      have hCPp : IsPGroup p (centralizerWithin P R0) :=
        hPp.to_le (centralizerWithin_le_left P R0)
      have hpCP : p ∣ Nat.card (centralizerWithin P R0) :=
        hCPp.card_eq_or_dvd.resolve_left
          ((centralizerWithin P R0).one_lt_card_iff_ne_bot.mpr hCPne).ne'
      obtain ⟨x, hxOrder⟩ :=
        exists_prime_orderOf_dvd_card'
          (G := centralizerWithin P R0) p hpCP
      let xT : T0 := ⟨(x : G), hCP0T0 x.property⟩
      have hxp : x ^ p = 1 := by
        rw [← hxOrder]
        exact pow_orderOf_eq_one x
      have hxOmega : xT ∈ omegaOne p T0 := by
        rw [omegaOne_eq_powMonoidHom_ker, MonoidHom.mem_ker]
        apply Subtype.ext
        change ((x : G) ^ p) = 1
        exact congrArg (fun z : centralizerWithin P R0 => (z : G)) hxp
      have hxCV0 : xT ∈ CV0 := by
        rw [hCV0eqOmega]
        exact hxOmega
      have hxV : (x : G) ∈ V := hxCV0.1
      have hxP : (x : G) ∈ P := x.property.1
      have hxOne : (x : G) = 1 := by
        apply Subgroup.mem_bot.mp
        rw [← disjoint_iff.mp hVPdis]
        exact ⟨hxV, hxP⟩
      have hxSubOne : x = 1 := Subtype.ext hxOne
      rw [hxSubOne, orderOf_one] at hxOrder
      exact (Fact.out : p.Prime).ne_one hxOrder.symm
    have hR0normP : R0 ≤ Subgroup.normalizer (P : Set G) :=
      hR0R.trans hRnormP
    have hcopPR0 : Nat.Coprime (Nat.card P) (Nat.card R0) :=
      hcop.coprime_dvd_left (Subgroup.card_dvd_of_le hPH) |>.coprime_dvd_right
        (Subgroup.card_dvd_of_le hR0R)
    have hR0P : ⁅R0, P⁆ = P := by
      apply le_antisymm
      · exact Subgroup.le_normalizer_iff_commutator_le_right.mp hR0normP
      · have hdecomp :=
          le_commutator_sup_centralizerWithin_of_coprime
            hR0normP hcopPR0
        rw [hCPR0bot, sup_bot_eq] at hdecomp
        exact hdecomp
    have hPR0 : ⁅P, R0⁆ = P := by
      rw [Subgroup.commutator_comm]
      exact hR0P
    have hLocal : ∀ X : Subgroup G,
        P ⊔ R0 ≤ Subgroup.normalizer (X : Set G) →
        X ≤ K →
        (Nat.card ((V ⊔ X) ⊔ P : Subgroup G) < Nat.card H ∨
          Nat.card R0 < Nat.card R) →
        ⁅X, P⁆ = ⊥ := by
      intro X hPR0normX hXK hsmall
      let H0 : Subgroup G := (V ⊔ X) ⊔ P
      have hH0H : H0 ≤ H :=
        sup_le (sup_le hVH (hXK.trans hKH)) hPH
      have hR0normX : R0 ≤ Subgroup.normalizer (X : Set G) :=
        le_sup_right.trans hPR0normX
      have hR0normH0 : R0 ≤ Subgroup.normalizer (H0 : Set G) := by
        have hR0normVX : R0 ≤
            Subgroup.normalizer ((V ⊔ X : Subgroup G) : Set G) :=
          (le_inf (hR0R.trans hRnormV) hR0normX).trans
            (Subgroup.normalizer_inf_normalizer_le_normalizer_sup V X)
        exact (le_inf hR0normVX (hR0R.trans hRnormP)).trans
          (Subgroup.normalizer_inf_normalizer_le_normalizer_sup (V ⊔ X) P)
      let J : Subgroup G := R0 ⊔ H0
      let HJ : Subgroup J := H0.subgroupOf J
      let RJ : Subgroup J := R0.subgroupOf J
      letI : IsSolvable J := isSolvable_subgroup_of_isSolvable J
      letI : HJ.Normal :=
        Subgroup.normal_subgroupOf_sup_of_le_normalizer hR0normH0
      have hH0J : H0 ≤ J := le_sup_right
      have hR0J : R0 ≤ J := le_sup_left
      have hdisAmbient : Disjoint H0 R0 :=
        hHR.disjoint.mono hH0H hR0R
      have hdisJ : Disjoint HJ RJ := by
        rw [disjoint_iff]
        apply le_bot_iff.mp
        intro x hx
        apply Subgroup.mem_bot.mpr
        apply Subtype.ext
        apply Subgroup.mem_bot.mp
        have hxG : ((x : J) : G) ∈ H0 ⊓ R0 := hx
        rw [disjoint_iff.mp hdisAmbient] at hxG
        exact hxG
      have hsupJ : HJ ⊔ RJ = ⊤ := by
        rw [← Subgroup.subgroupOf_sup hH0J hR0J, sup_comm]
        exact Subgroup.subgroupOf_self J
      have hcompJ : HJ.IsComplement' RJ := by
        apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisJ
        rw [← Subgroup.normal_mul HJ RJ, hsupJ]
        rfl
      have hcardHJ : Nat.card HJ = Nat.card H0 :=
        natCard_subgroupOf_eq hH0J
      have hcardRJ : Nat.card RJ = Nat.card R0 :=
        natCard_subgroupOf_eq hR0J
      have hlt : Nat.card J < Nat.card G := by
        rw [← hcompJ.card_mul, hcardHJ, hcardRJ, ← hHR.card_mul]
        rcases hsmall with hsmallH | hsmallR
        · exact lt_of_le_of_lt
            (Nat.mul_le_mul_left _ (Subgroup.card_le_of_le hR0R))
            (Nat.mul_lt_mul_of_pos_right hsmallH Nat.card_pos)
        · exact lt_of_le_of_lt
            (Nat.mul_le_mul_right _ (Subgroup.card_le_of_le hH0H))
            (Nat.mul_lt_mul_of_pos_left hsmallR Nat.card_pos)
      have hcopJ : Nat.Coprime (Nat.card HJ) (Nat.card RJ) := by
        rw [hcardHJ, hcardRJ]
        exact hcop.coprime_dvd_left (Subgroup.card_dvd_of_le hH0H)
          |>.coprime_dvd_right (Subgroup.card_dvd_of_le hR0R)
      have hoddJ : Odd (Nat.card J) :=
        hodd.of_dvd_nat J.card_subgroup_dvd_card
      have hRJprime : (Nat.card RJ).Prime := by
        rw [hcardRJ]
        exact hR0prime
      have hZJ : IsZGroup (centralizerWithin HJ RJ) :=
        isZGroup_centralizerWithin_subgroupOf hH0H hR0J hZ
      have hrecJ : IsPLengthOne p (⁅RJ, HJ⁆ : Subgroup J) :=
        ih (Nat.card J) hlt J rfl HJ RJ RJ hcompJ hcopJ hoddJ
          le_rfl hRJprime hZJ
      let A : Subgroup G := ⁅R0, H0⁆
      have hmapA : (⁅RJ, HJ⁆ : Subgroup J).map J.subtype = A := by
        rw [Subgroup.map_commutator,
          Subgroup.map_subgroupOf_eq_of_le hR0J,
          Subgroup.map_subgroupOf_eq_of_le hH0J]
      let eA : (⁅RJ, HJ⁆ : Subgroup J) ≃* A := by
        rw [← hmapA]
        exact Subgroup.equivMapOfInjective (⁅RJ, HJ⁆ : Subgroup J)
          J.subtype J.subtype_injective
      have hplA : IsPLengthOne p A :=
        isPLengthOne_of_mulEquiv hrecJ eA
      have hAH0 : A ≤ H0 :=
        Subgroup.le_normalizer_iff_commutator_le_right.mp hR0normH0
      have hH0normA : H0 ≤ Subgroup.normalizer (A : Set G) :=
        Subgroup.normalizer_commutator_ge_right R0 H0
      let O0 : Subgroup H0 := pPrimeCore p H0
      let O0G : Subgroup G := O0.map H0.subtype
      have hH0normO0G : H0 ≤
          Subgroup.normalizer (O0G : Set G) := by
        rw [Subgroup.le_normalizer_iff]
        exact characteristic_map_subtype_invariant_under_normalizer
          H0 H0 O0 Subgroup.le_normalizer
      have hO0GH0 : O0G ≤ H0 := Subgroup.map_subtype_le O0
      have hO0Gprime : IsPPrimeSubgroup p O0G := by
        rw [IsPPrimeSubgroup,
          Subgroup.card_map_of_injective H0.subtype_injective]
        exact pPrimeCore_coprime_card
      have hcopO0GV : Nat.Coprime (Nat.card O0G) (Nat.card V) := by
        obtain ⟨a, ha⟩ := hVelem.isPGroup.exists_card_eq
        rw [ha]
        exact hO0Gprime.symm.pow_right a
      have hO0Gbot : O0G = ⊥ := by
        apply le_antisymm _ bot_le
        intro x hxO
        have hxCent : x ∈ Subgroup.centralizer (V : Set G) :=
          mem_centralizer_of_mem_of_mem_normalizer_of_coprime
            (show V ≤ Subgroup.normalizer (O0G : Set G) from
              (show V ≤ H0 from le_sup_left.trans le_sup_left) |>.trans
                hH0normO0G)
            hcopO0GV hxO
            ((Subgroup.le_normalizer_of_normal :
              O0G ≤ Subgroup.normalizer (V : Set G)) hxO)
        have hxWithin : x ∈ centralizerWithin H V :=
          ⟨hH0H (hO0GH0 hxO), hxCent⟩
        have hxV : x ∈ V := by
          rw [hCVH] at hxWithin
          exact hxWithin
        have hxBot : x ∈ V ⊓ O0G := ⟨hxV, hxO⟩
        rw [disjoint_iff.mp
          (Subgroup.disjoint_of_coprime_natCard hcopO0GV.symm)] at hxBot
        exact hxBot
      have hcoreH0 : pPrimeCore p H0 = ⊥ := by
        exact (Subgroup.map_eq_bot_iff_of_injective
          (pPrimeCore p H0) H0.subtype_injective).mp
            (by simpa only [O0G, O0] using hO0Gbot)
      let OA : Subgroup A := pPrimeCore p A
      let OAG : Subgroup G := OA.map A.subtype
      have hH0normOAG : H0 ≤
          Subgroup.normalizer (OAG : Set G) := by
        rw [Subgroup.le_normalizer_iff]
        exact characteristic_map_subtype_invariant_under_normalizer
          A H0 OA hH0normA
      have hOAGH0 : OAG ≤ H0 :=
        (Subgroup.map_subtype_le OA).trans hAH0
      let OAH0 : Subgroup H0 := OAG.subgroupOf H0
      letI : OAH0.Normal :=
        Subgroup.normal_subgroupOf_of_le_normalizer hH0normOAG
      have hOAGprime : IsPPrimeSubgroup p OAG := by
        rw [IsPPrimeSubgroup,
          Subgroup.card_map_of_injective A.subtype_injective]
        exact pPrimeCore_coprime_card
      have hOAH0prime : IsPPrimeSubgroup p OAH0 := by
        rw [IsPPrimeSubgroup, natCard_subgroupOf_eq hOAGH0]
        exact hOAGprime
      have hOAH0bot : OAH0 = ⊥ := by
        apply le_bot_iff.mp
        have hle : OAH0 ≤ pPrimeCore p H0 :=
          le_pPrimeCore hOAH0prime (by infer_instance)
        simpa only [hcoreH0] using hle
      have hOAGbot : OAG = ⊥ := by
        apply le_antisymm _ bot_le
        intro x hx
        let x0 : H0 := ⟨x, hOAGH0 hx⟩
        have hx0 : x0 ∈ OAH0 := hx
        rw [hOAH0bot] at hx0
        exact Subgroup.mem_bot.mpr
          (congrArg Subtype.val (Subgroup.mem_bot.mp hx0))
      have hcoreA : pPrimeCore p A = ⊥ := by
        exact (Subgroup.map_eq_bot_iff_of_injective
          (pPrimeCore p A) A.subtype_injective).mp
            (by simpa only [OAG, OA] using hOAGbot)
      obtain ⟨S, hS⟩ := hplA
      let e0 : (A ⧸ pPrimeCore p A) ≃* A :=
        (QuotientGroup.quotientMulEquivOfEq hcoreA).trans
          QuotientGroup.quotientBot
      let SA : Sylow p A :=
        S.mapSurjective (f := e0.toMonoidHom) e0.surjective
      have hSA : (SA : Subgroup A) = pCore p A := by
        dsimp only [SA]
        rw [Sylow.coe_mapSurjective, hS]
        exact map_pCore_eq_mulEquiv e0
      have hPA : P ≤ A := by
        calc
          P = ⁅R0, P⁆ := hR0P.symm
          _ ≤ ⁅R0, H0⁆ :=
            Subgroup.commutator_mono le_rfl le_sup_right
          _ = A := rfl
      let PA : Subgroup A := P.subgroupOf A
      have hPAp : IsPGroup p PA :=
        hPp.of_equiv (Subgroup.subgroupOfEquivOfLe hPA).symm
      obtain ⟨TA, hPATA⟩ := hPAp.exists_le_sylow
      have hSAnormal : (SA : Subgroup A).Normal := by
        rw [hSA]
        infer_instance
      letI : Unique (Sylow p A) :=
        Sylow.unique_of_normal SA hSAnormal
      have hTASA : TA = SA := Subsingleton.elim TA SA
      have hPAcore : PA ≤ pCore p A := by
        rw [← hSA, ← hTASA]
        exact hPATA
      let T : Subgroup G := (pCore p A).map A.subtype
      have hPT : P ≤ T := by
        intro x hx
        let xA : A := ⟨x, hPA hx⟩
        exact ⟨xA, hPAcore hx, rfl⟩
      have hXH0 : X ≤ H0 := le_sup_right.trans le_sup_left
      have hXnormA : X ≤ Subgroup.normalizer (A : Set G) :=
        hXH0.trans hH0normA
      have hXnormT : X ≤ Subgroup.normalizer (T : Set G) := by
        rw [Subgroup.le_normalizer_iff]
        exact characteristic_map_subtype_invariant_under_normalizer
          A X (pCore p A) hXnormA
      have hcommT : ⁅X, P⁆ ≤ T :=
        (Subgroup.commutator_mono le_rfl hPT).trans
          (Subgroup.le_normalizer_iff_commutator_le_right.mp hXnormT)
      have hPnormX : P ≤ Subgroup.normalizer (X : Set G) :=
        le_sup_left.trans hPR0normX
      have hcommX : ⁅X, P⁆ ≤ X :=
        Subgroup.le_normalizer_iff_commutator_le_left.mp hPnormX
      have hXprime : IsPPrimeSubgroup p X := by
        rw [IsPPrimeSubgroup]
        exact hKcopP.symm.coprime_dvd_right
          (Subgroup.card_dvd_of_le hXK)
      have hTp : IsPGroup p T := pCore_isPGroup.map A.subtype
      have hcopXT : Nat.Coprime (Nat.card X) (Nat.card T) := by
        obtain ⟨a, ha⟩ := hTp.exists_card_eq
        rw [ha]
        exact hXprime.symm.pow_right a
      apply le_antisymm _ bot_le
      intro z hz
      have hzI : z ∈ X ⊓ T := ⟨hcommX hz, hcommT hz⟩
      rw [disjoint_iff.mp
        (Subgroup.disjoint_of_coprime_natCard hcopXT)] at hzI
      exact hzI
    let H1 : Subgroup G := (V ⊔ K) ⊔ P
    have hH1H : H1 ≤ H :=
      sup_le (sup_le hVH hKH) hPH
    have hnormKPR0 : P ⊔ R0 ≤
        Subgroup.normalizer (K : Set G) :=
      sup_le hPnormK (hR0R.trans hRnormK)
    have hH1eq : H1 = H := by
      by_contra hne
      have hcard : Nat.card H1 < Nat.card H := by
        exact lt_of_le_of_ne (Subgroup.card_le_of_le hH1H)
          (fun he => hne (Subgroup.eq_of_le_of_card_ge hH1H he.ge))
      exact hKPne (hLocal K hnormKPR0 le_rfl (Or.inl hcard))
    have hR0eq : R0 = R := by
      by_contra hne
      have hcard : Nat.card R0 < Nat.card R := by
        exact lt_of_le_of_ne (Subgroup.card_le_of_le hR0R)
          (fun he => hne (Subgroup.eq_of_le_of_card_ge hR0R he.ge))
      exact hKPne (hLocal K hnormKPR0 le_rfl (Or.inr hcard))
    subst R0
    have hsub : ∀ X : Subgroup G,
        P ⊔ R ≤ Subgroup.normalizer (X : Set G) → X ≤ K →
        X = K ∨ X ≤ Subgroup.centralizer (P : Set G) := by
      intro X hPRnormX hXK
      by_cases hXeq : X = K
      · exact Or.inl hXeq
      right
      have hXltK : Nat.card X < Nat.card K := by
        exact lt_of_le_of_ne (Subgroup.card_le_of_le hXK)
          (fun he => hXeq (Subgroup.eq_of_le_of_card_ge hXK he.ge))
      have hXPleN : X ⊔ P ≤ N :=
        sup_le (hXK.trans hKN) hPN
      have hVdisXP : Disjoint V (X ⊔ P) :=
        hVNdis.mono_right hXPleN
      have hXPnormV : X ⊔ P ≤
          Subgroup.normalizer (V : Set G) :=
        sup_le (hXK.trans hKnormV) hPnormV
      have hcopXP : Nat.Coprime (Nat.card X) (Nat.card P) :=
        hcopKP.coprime_dvd_left (Subgroup.card_dvd_of_le hXK)
      have hdisXP : Disjoint X P :=
        Subgroup.disjoint_of_coprime_natCard hcopXP
      have hPnormX : P ≤ Subgroup.normalizer (X : Set G) :=
        le_sup_left.trans hPRnormX
      have hcardXP : Nat.card (X ⊔ P : Subgroup G) =
          Nat.card P * Nat.card X := by
        rw [sup_comm]
        exact natCard_sup_eq_mul_of_disjoint_of_le_normalizer
          hdisXP.symm hPnormX
      have hcardHX : Nat.card ((V ⊔ X) ⊔ P : Subgroup G) =
          Nat.card P * Nat.card X * Nat.card V := by
        rw [show (V ⊔ X) ⊔ P = (X ⊔ P) ⊔ V by ac_rfl,
          natCard_sup_eq_mul_of_disjoint_of_le_normalizer
            hVdisXP.symm hXPnormV,
          hcardXP]
      have hKPleN : K ⊔ P ≤ N := sup_le hKN hPN
      have hVdisKP : Disjoint V (K ⊔ P) :=
        hVNdis.mono_right hKPleN
      have hKPnormV : K ⊔ P ≤
          Subgroup.normalizer (V : Set G) :=
        sup_le hKnormV hPnormV
      have hdisKP : Disjoint K P :=
        Subgroup.disjoint_of_coprime_natCard hcopKP
      have hcardKP : Nat.card (K ⊔ P : Subgroup G) =
          Nat.card P * Nat.card K := by
        rw [sup_comm]
        exact natCard_sup_eq_mul_of_disjoint_of_le_normalizer
          hdisKP.symm hPnormK
      have hcardH1 : Nat.card H1 =
          Nat.card P * Nat.card K * Nat.card V := by
        change Nat.card ((V ⊔ K) ⊔ P : Subgroup G) = _
        rw [show (V ⊔ K) ⊔ P = (K ⊔ P) ⊔ V by ac_rfl,
          natCard_sup_eq_mul_of_disjoint_of_le_normalizer
            hVdisKP.symm hKPnormV,
          hcardKP]
      have hcardHXH :
          Nat.card ((V ⊔ X) ⊔ P : Subgroup G) < Nat.card H := by
        rw [hcardHX, ← hH1eq, hcardH1]
        exact Nat.mul_lt_mul_of_pos_right
          (Nat.mul_lt_mul_of_pos_left hXltK Nat.card_pos)
          Nat.card_pos
      have hXPbot : ⁅X, P⁆ = ⊥ :=
        hLocal X hPRnormX hXK (Or.inl hcardHXH)
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hXPbot
    have hPne : P ≠ ⊥ := by
      intro hPbot
      apply hKPne
      rw [hPbot, Subgroup.commutator_bot_right]
    have hKne : K ≠ ⊥ := by
      intro hKbot
      apply hKPne
      rw [hKbot, Subgroup.commutator_bot_left]
    let DPK : Subgroup G := ⁅P, K⁆
    have hPnormDPK : P ≤ Subgroup.normalizer (DPK : Set G) := by
      dsimp only [DPK]
      exact Subgroup.normalizer_commutator_ge_left P K
    have hRnormDPK : R ≤ Subgroup.normalizer (DPK : Set G) := by
      intro r hr
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      dsimp only [DPK]
      rw [Subgroup.map_commutator,
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (hRnormP hr),
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (hRnormK hr)]
    have hPRnormDPK : P ⊔ R ≤
        Subgroup.normalizer (DPK : Set G) :=
      sup_le hPnormDPK hRnormDPK
    have hDPKleK : DPK ≤ K := by
      dsimp only [DPK]
      exact Subgroup.le_normalizer_iff_commutator_le_right.mp hPnormK
    have hPKne : ⁅P, K⁆ ≠ ⊥ := by
      intro hbot
      apply hKPne
      rw [Subgroup.commutator_comm]
      exact hbot
    have hPK : ⁅P, K⁆ = K := by
      rcases hsub DPK hPRnormDPK hDPKleK with heq | hcent
      · exact heq
      · have hDPKPbot : ⁅DPK, P⁆ = ⊥ :=
          Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hcent
        have hPDPKbot : ⁅P, DPK⁆ = ⊥ := by
          rw [Subgroup.commutator_comm]
          exact hDPKPbot
        have hidem : ⁅P, DPK⁆ = DPK := by
          dsimp only [DPK]
          exact commutator_commutator_eq_of_coprime hPnormK hcopKP
        exfalso
        apply (hPKne : ⁅P, K⁆ ≠ ⊥)
        exact hidem.symm.trans hPDPKbot
    have hKP : ⁅K, P⁆ = K := by
      rw [Subgroup.commutator_comm]
      exact hPK
    obtain ⟨q, hq, hqK⟩ :=
      Nat.exists_prime_and_dvd
        ((K.one_lt_card_iff_ne_bot.mpr hKne).ne')
    letI : Fact q.Prime := ⟨hq⟩
    have hnormKPR : P ⊔ R ≤
        Subgroup.normalizer (K : Set G) :=
      sup_le hPnormK hRnormK
    have hKq : IsPGroup q K :=
      isPGroup_of_nilpotent_prime_core_dichotomy
        K P R hq hKnil hqK hnormKPR hsub hKP
    have hKodd : Odd (Nat.card K) :=
      hodd.of_dvd_nat K.card_subgroup_dvd_card
    have hcopKR : Nat.Coprime (Nat.card K) (Nat.card R) :=
      hcop.coprime_dvd_left (Subgroup.card_dvd_of_le hKH)
    have hpR : p ≠ Nat.card R := by
      intro heq
      rw [heq] at hpR0
      have hone : Nat.card R = 1 := by
        simpa [Nat.Coprime] using hpR0
      exact hR0prime.ne_one hone
    let L : Subgroup G := P ⊔ R
    have hPL : P ≤ L := le_sup_left
    have hRL : R ≤ L := le_sup_right
    let PL : Subgroup L := P.subgroupOf L
    let RL : Subgroup L := R.subgroupOf L
    have hcardPL : Nat.card PL = Nat.card P :=
      natCard_subgroupOf_eq hPL
    have hcardRL : Nat.card RL = Nat.card R :=
      natCard_subgroupOf_eq hRL
    have hdisPR : Disjoint P R :=
      Subgroup.disjoint_of_coprime_natCard hcopPR0
    have hLnormP : L ≤ Subgroup.normalizer (P : Set G) :=
      sup_le Subgroup.le_normalizer hRnormP
    letI : PL.Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer hLnormP
    have hdisPLRL : Disjoint PL RL := by
      rw [disjoint_iff]
      apply le_bot_iff.mp
      intro x hx
      apply Subgroup.mem_bot.mpr
      apply Subtype.ext
      apply Subgroup.mem_bot.mp
      have hxG : ((x : L) : G) ∈ P ⊓ R := hx
      rw [disjoint_iff.mp hdisPR] at hxG
      exact hxG
    have hsupPLRL : PL ⊔ RL = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hPL hRL]
      exact Subgroup.subgroupOf_self L
    have hcompPLRL : PL.IsComplement' RL := by
      apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisPLRL
      rw [← Subgroup.normal_mul PL RL, hsupPLRL]
      rfl
    have hcopPLRL : Nat.Coprime (Nat.card PL) (Nat.card RL) := by
      simpa only [hcardPL, hcardRL] using hcopPR0
    have hcardL : Nat.card L = Nat.card P * Nat.card R := by
      rw [← hcompPLRL.card_mul, hcardPL, hcardRL]
    have hLodd : Odd (Nat.card L) :=
      hodd.of_dvd_nat L.card_subgroup_dvd_card
    have hLsol : IsSolvable L :=
      isSolvable_subgroup_of_isSolvable L
    have hqP : Nat.Coprime q (Nat.card P) :=
      hcopKP.coprime_dvd_left hqK
    have hqR : Nat.Coprime q (Nat.card R) :=
      hcopKR.coprime_dvd_left hqK
    have hLprime : IsPPrimeSubgroup q L := by
      rw [IsPPrimeSubgroup, hcardL, Nat.coprime_mul_iff_right]
      exact ⟨hqP, hqR⟩
    have hqL : ¬ q ∣ Nat.card L :=
      hq.coprime_iff_not_dvd.mp hLprime
    have hRPK : ⁅R, P⁆ = P := by
      rw [Subgroup.commutator_comm]
      exact hPR0
    have hLnoncomm : ¬ IsMulCommutative L := by
      intro hcomm
      have hbot : ⁅RL, PL⁆ = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro r _hr
        rw [Subgroup.mem_centralizer_iff]
        intro a _ha
        exact ((isMulCommutative_iff.mp hcomm) r a).symm
      have hmapBot : (⁅RL, PL⁆ : Subgroup L).map L.subtype = ⊥ := by
        rw [hbot, Subgroup.map_bot]
      rw [Subgroup.map_commutator,
        Subgroup.map_subgroupOf_eq_of_le hRL,
        Subgroup.map_subgroupOf_eq_of_le hPL,
        hRPK] at hmapBot
      exact hPne hmapBot
    have hCPK : centralizerWithin P K = ⊥ := by
      apply le_antisymm _ bot_le
      intro x hx
      have hxHK : x ∈ centralizerWithin H K :=
        ⟨hPH hx.1, hx.2⟩
      have hxK : x ∈ K := hCHK hxHK
      have hxI : x ∈ K ⊓ P := ⟨hxK, hx.1⟩
      rw [disjoint_iff.mp
        (Subgroup.disjoint_of_coprime_natCard hcopKP)] at hxI
      exact hxI
    have hCRK : centralizerWithin R K = ⊥ := by
      let CR : Subgroup R :=
        (centralizerWithin R K).subgroupOf R
      letI : Fact (Nat.card R).Prime := ⟨hR0prime⟩
      rcases CR.eq_bot_or_eq_top_of_prime_card with hbot | htop
      · apply le_antisymm _ bot_le
        intro x hx
        let xR : R := ⟨x, hx.1⟩
        have hxCR : xR ∈ CR := hx
        rw [hbot] at hxCR
        exact Subgroup.mem_bot.mpr
          (congrArg Subtype.val (Subgroup.mem_bot.mp hxCR))
      · have hRcentK : R ≤ Subgroup.centralizer (K : Set G) := by
          intro r hr
          let rR : R := ⟨r, hr⟩
          have hrCR : rR ∈ CR := by
            rw [htop]
            exact Subgroup.mem_top rR
          exact hrCR.2
        have hRKbot : ⁅R, K⁆ = ⊥ :=
          Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hRcentK
        exfalso
        apply hKR0ne
        rw [Subgroup.commutator_comm]
        exact hRKbot
    have hLnormK : L ≤ Subgroup.normalizer (K : Set G) :=
      sup_le hPnormK hRnormK
    let rhoK : L →* MulAut K :=
      K.normalizerMonoidHom.comp (Subgroup.inclusion hLnormK)
    have hrhoK : Function.Injective rhoK := by
      rw [← rhoK.ker_eq_bot_iff]
      rw [Subgroup.eq_bot_iff_forall]
      intro x hxker
      have hxSup : (x : G) ∈ R ⊔ P := by
        simpa only [L, sup_comm] using x.property
      have hxProd : (x : G) ∈ (R : Set G) * (P : Set G) := by
        rw [← Subgroup.coe_mul_of_left_le_normalizer_right R P hRnormP]
        exact hxSup
      obtain ⟨r, hr, a, ha, hra⟩ := hxProd
      let rL : L := ⟨r, hRL hr⟩
      let aL : L := ⟨a, hPL ha⟩
      have hxa : x = rL * aL := Subtype.ext hra.symm
      have hrhoa : rhoK rL * rhoK aL = 1 := by
        rw [← map_mul, ← hxa]
        exact MonoidHom.mem_ker.mp hxker
      have heq : rhoK rL = (rhoK aL)⁻¹ := by
        calc
          rhoK rL = (rhoK rL * rhoK aL) * (rhoK aL)⁻¹ := by group
          _ = (rhoK aL)⁻¹ := by rw [hrhoa, one_mul]
      let IPL : Subgroup (MulAut K) := PL.map rhoK
      let IRL : Subgroup (MulAut K) := RL.map rhoK
      have hIPLdvd : Nat.card IPL ∣ Nat.card P := by
        have h := Subgroup.card_map_dvd PL rhoK
        simpa only [IPL, hcardPL] using h
      have hIRLdvd : Nat.card IRL ∣ Nat.card R := by
        have h := Subgroup.card_map_dvd RL rhoK
        simpa only [IRL, hcardRL] using h
      have hdisImages : Disjoint IRL IPL :=
        Subgroup.disjoint_of_coprime_natCard
          (hcopPR0.symm.coprime_dvd_left hIRLdvd
            |>.coprime_dvd_right hIPLdvd)
      have hrhoRmem : rhoK rL ∈ IRL := ⟨rL, hr, rfl⟩
      have hrhoPmem : rhoK rL ∈ IPL := by
        rw [heq]
        exact IPL.inv_mem ⟨aL, ha, rfl⟩
      have hrhoRone : rhoK rL = 1 := by
        apply Subgroup.mem_bot.mp
        rw [← disjoint_iff.mp hdisImages]
        exact ⟨hrhoRmem, hrhoPmem⟩
      have hrhoPone : rhoK aL = 1 := by
        have : (rhoK aL)⁻¹ = 1 := heq.symm.trans hrhoRone
        simpa using congrArg Inv.inv this
      have hrCent : r ∈ Subgroup.centralizer (K : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro k hk
        let kk : K := ⟨k, hk⟩
        have hfix : rhoK rL kk = kk := by rw [hrhoRone]; rfl
        have hconj : r * k * r⁻¹ = k :=
          congrArg Subtype.val hfix
        calc
          k * r = (r * k * r⁻¹) * r := by rw [hconj]
          _ = r * k := by group
      have hrWithin : r ∈ centralizerWithin R K := ⟨hr, hrCent⟩
      have hrOne : r = 1 := by
        rw [hCRK] at hrWithin
        exact Subgroup.mem_bot.mp hrWithin
      have haCent : a ∈ Subgroup.centralizer (K : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro k hk
        let kk : K := ⟨k, hk⟩
        have hfix : rhoK aL kk = kk := by rw [hrhoPone]; rfl
        have hconj : a * k * a⁻¹ = k :=
          congrArg Subtype.val hfix
        calc
          k * a = (a * k * a⁻¹) * a := by rw [hconj]
          _ = a * k := by group
      have haWithin : a ∈ centralizerWithin P K := ⟨ha, haCent⟩
      have haOne : a = 1 := by
        rw [hCPK] at haWithin
        exact Subgroup.mem_bot.mp haWithin
      apply Subtype.ext
      rw [hxa]
      change r * a = 1
      rw [hrOne, haOne, one_mul]
    have hCLK : centralizerWithin L K = ⊥ := by
      apply le_antisymm _ bot_le
      intro x hx
      let xL : L := ⟨x, hx.1⟩
      have hxker : xL ∈ rhoK.ker := by
        apply MonoidHom.mem_ker.mpr
        apply MulEquiv.ext
        intro k
        apply Subtype.ext
        have hcomm := hx.2 (k : G) k.property
        change x * (k : G) * x⁻¹ = (k : G)
        calc
          x * (k : G) * x⁻¹ = (k : G) * x * x⁻¹ := by
            rw [← hcomm]
          _ = (k : G) := by group
      have hxOne : xL = 1 := by
        apply hrhoK
        rw [MonoidHom.mem_ker.mp hxker, map_one]
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val hxOne)
    let Ephi := K ⧸ frattini K
    let rhoPhi : L →* MulAut Ephi :=
      (frattiniQuotientMulAutHom K).comp rhoK
    have hrhoPhi : Function.Injective rhoPhi :=
      frattiniQuotientAction_injective_of_pPrime_of_trivial_centralizer
        K L hKq hLnormK hLprime hCLK
    have hEphiQ : IsPGroup q Ephi :=
      hKq.to_quotient (frattini K)
    have hEphiOdd : Odd (Nat.card Ephi) :=
      odd_natCard_quotient (frattini K) hKodd
    have hlargePhi : q ^ 2 < Nat.card Ephi :=
      prime_sq_lt_natCard_of_odd_faithful_coprime_action
        hLsol hEphiQ hEphiOdd hLodd hqL rhoPhi hrhoPhi hLnoncomm
    let ZK : Subgroup G := (_root_.commutator K).map K.subtype
    have hZKleK : ZK ≤ K := Subgroup.map_subtype_le _
    have hZKsub : ZK.subgroupOf K = _root_.commutator K := by
      dsimp only [ZK]
      exact Subgroup.comap_map_eq_self_of_injective
        K.subtype_injective (_root_.commutator K)
    have hKnormZK : K ≤ Subgroup.normalizer (ZK : Set G) := by
      rw [Subgroup.le_normalizer_iff]
      exact characteristic_map_subtype_invariant_under_normalizer
        K K (_root_.commutator K) Subgroup.le_normalizer
    have hLnormZK : L ≤ Subgroup.normalizer (ZK : Set G) := by
      rw [Subgroup.le_normalizer_iff]
      exact characteristic_map_subtype_invariant_under_normalizer
        K L (_root_.commutator K) hLnormK
    letI : (ZK.subgroupOf K).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer hKnormZK
    have hperfectPL : ⁅RL, PL⁆ = PL := by
      apply Subgroup.map_injective L.subtype_injective
      rw [Subgroup.map_commutator,
        Subgroup.map_subgroupOf_eq_of_le hRL,
        Subgroup.map_subgroupOf_eq_of_le hPL,
        hRPK]
    have hPLne : PL ≠ ⊥ := by
      intro hbot
      apply hPne
      calc
        P = PL.map L.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hPL).symm
        _ = ⊥ := by rw [hbot, Subgroup.map_bot]
    have hLcardZMod : (Nat.card L : ZMod q) ≠ 0 := by
      letI : NeZero (Nat.card L : ZMod q) :=
        NeZero.of_not_dvd (ZMod q) hqL
      exact NeZero.ne _
    have hCnotZ_of_elementary
        (hE : IsElementaryAbelianGroup q
          (K ⧸ ZK.subgroupOf K)) :
        ¬ centralizerWithin K R ≤ ZK := by
      intro hCZ
      let a : L →* MulAut (K ⧸ ZK.subgroupOf K) :=
        subgroupConjugationFactorHom ZK K L hLnormK hLnormZK
      have ha : Function.Injective a := by
        rw [← a.ker_eq_bot_iff]
        rw [Subgroup.eq_bot_iff_forall]
        intro g hg
        have hcommZ : ∀ k : G, k ∈ K →
            ⁅(g : G), k⁆ ∈ ZK :=
          (mem_ker_subgroupConjugationFactorHom_iff
            ZK K L hLnormK hLnormZK g).mp hg
        have hphiKer : g ∈ rhoPhi.ker := by
          apply MonoidHom.mem_ker.mpr
          apply MulEquiv.ext
          intro y
          obtain ⟨k, rfl⟩ :=
            QuotientGroup.mk'_surjective (frattini K) y
          apply QuotientGroup.eq_iff_div_mem.mpr
          have hcAmbient : ⁅(g : G), (k : G)⁆ ∈ ZK :=
            hcommZ (k : G) k.property
          rcases hcAmbient with ⟨c, hc, hceq⟩
          have hcPhi : c ∈ frattini K :=
            IsPGroup.commutator_le_frattini hKq hc
          have heq : rhoK g k / k = c := by
            apply Subtype.ext
            simpa [rhoK, div_eq_mul_inv, commutatorElement_def]
              using hceq.symm
          change rhoK g k / k ∈ frattini K
          rw [heq]
          exact hcPhi
        have hgOne : g = 1 := by
          apply hrhoPhi
          rw [MonoidHom.mem_ker.mp hphiKer, map_one]
        exact hgOne
      have hcopZKR : Nat.Coprime (Nat.card ZK) (Nat.card R) :=
        hcopKR.coprime_dvd_left
          (Subgroup.card_dvd_of_le hZKleK)
      have hfix : ∀ x : K ⧸ ZK.subgroupOf K,
          (∀ r : RL, a (r : L) x = x) → x = 1 :=
        factor_fixed_eq_one_of_centralizer_le
          K ZK L R hZKleK hRL hLnormK hLnormZK hKnormZK
            hcopZKR hCZ
      letI : IsSolvable L := hLsol
      exact false_of_faithful_elementary_action_zero_fixed
        PL RL hcompPLRL hcopPLRL hLodd
          (by simpa only [hcardRL] using hR0prime) hLcardZMod
          hE a ha hperfectPL hPLne hfix
    have hlargeDerived :
        q ^ 2 < Nat.card (K ⧸ _root_.commutator K) := by
      calc
        q ^ 2 < (frattini K).index := by
          simpa only [Subgroup.index_eq_card] using hlargePhi
        _ ≤ (_root_.commutator K).index :=
          Subgroup.index_antitone
            (IsPGroup.commutator_le_frattini hKq)
        _ = Nat.card (K ⧸ _root_.commutator K) :=
          Subgroup.index_eq_card (_root_.commutator K)
    have hderivedQuotientElementary
        (hpow : ∀ x : K, x ^ q = 1) :
        IsElementaryAbelianGroup q (K ⧸ ZK.subgroupOf K) := by
      have hQq : IsPGroup q (K ⧸ ZK.subgroupOf K) :=
        hKq.to_quotient (ZK.subgroupOf K)
      letI : IsMulCommutative (K ⧸ ZK.subgroupOf K) :=
        Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr
          (by rw [hZKsub])
      refine ⟨hQq, inferInstance, ?_⟩
      intro x
      obtain ⟨k, rfl⟩ :=
        QuotientGroup.mk'_surjective (ZK.subgroupOf K) x
      rw [← map_pow, hpow, map_one]
    have hgenerated : (V ⊔ K) ⊔ (P ⊔ R) = ⊤ := by
      calc
        (V ⊔ K) ⊔ (P ⊔ R) = ((V ⊔ K) ⊔ P) ⊔ R := by
          ac_rfl
        _ = H ⊔ R := by rw [← hH1eq]
        _ = ⊤ := hHR.sup_eq_top
    by_cases hKcomm : IsMulCommutative K
    · have hKelem : IsElementaryAbelianGroup q K :=
        elementary_of_normalized_subgroup_dichotomy
          K P R hKq hKne hKcomm hKP hcopKP hnormKPR hsub
      have hEderived : IsElementaryAbelianGroup q
          (K ⧸ ZK.subgroupOf K) :=
        hderivedQuotientElementary hKelem.pow_eq_one
      have hCnotZ : ¬ centralizerWithin K R ≤ ZK :=
        hCnotZ_of_elementary hEderived
      /-
      The special, noncommutative endpoint is proved in the second branch
      below.  Keeping this source-shaped block beside the common setup makes
      the two endpoint calculations easier to compare while the port is
      stabilized.
      let C : Subgroup G := centralizerWithin K R
      let D : Subgroup G := ⁅R, K⁆
      have hCleK : C ≤ K := centralizerWithin_le_left K R
      have hDleK : D ≤ K :=
        Subgroup.le_normalizer_iff_commutator_le_right.mp hRnormK
      have hCne : C ≠ ⊥ := by
        intro hbot
        apply hCnotZ
        rw [show centralizerWithin K R = ⊥ from hbot]
        exact bot_le
      have hCq : IsPGroup q C := hKq.to_le hCleK
      have hCleMain : C ≤ centralizerWithin H R := by
        intro x hx
        exact ⟨hKH hx.1, hx.2⟩
      let fC : C →* centralizerWithin H R :=
        Subgroup.inclusion hCleMain
      letI : IsZGroup (centralizerWithin H R) := hZ
      letI : IsZGroup C :=
        IsZGroup.of_injective (f := fC)
          (Subgroup.inclusion_injective hCleMain)
      letI : Group.IsNilpotent C := hCq.isNilpotent
      letI : IsCyclic C := inferInstance
      letI : Nontrivial C :=
        (Subgroup.nontrivial_iff_ne_bot C).mpr hCne
      have hCpow (x : C) : x ^ q = 1 := by
        apply Subtype.ext
        exact congrArg K.subtype
          (hKpow ⟨(x : G), hCleK x.property⟩)
      have hCexp : Monoid.exponent C = q :=
        (Monoid.exponent_eq_prime_iff hq).mpr
          (fun x hx => orderOf_eq_prime (hCpow x) hx)
      have hCcard : Nat.card (centralizerWithin K R) = q := by
        change Nat.card C = q
        calc
          Nat.card C = Monoid.exponent C := IsCyclic.exponent_eq_card.symm
          _ = q := hCexp
      have hCdisZ : Disjoint C ZK := by
        let I : Subgroup C := ZK.comap C.subtype
        letI : Fact (Nat.card C).Prime := ⟨by
          change (Nat.card (centralizerWithin K R)).Prime
          rw [hCcard]
          exact hq⟩
        rcases I.eq_bot_or_eq_top_of_prime_card with hIbot | hItop
        · rw [disjoint_iff]
          apply le_bot_iff.mp
          intro x hx
          let xC : C := ⟨x, hx.1⟩
          have hxI : xC ∈ I := hx.2
          rw [hIbot] at hxI
          exact Subgroup.mem_bot.mpr
            (congrArg Subtype.val (Subgroup.mem_bot.mp hxI))
        · exfalso
          apply hCnotZ
          intro x hx
          let xC : C := ⟨x, hx⟩
          have hxI : xC ∈ I := by
            rw [hItop]
            exact Subgroup.mem_top xC
          exact hxI
      have hRnormD : R ≤ Subgroup.normalizer (D : Set G) := by
        dsimp only [D]
        exact Subgroup.normalizer_commutator_ge_left R K
      have hcopDR : Nat.Coprime (Nat.card D) (Nat.card R) :=
        hcopKR.coprime_dvd_left (Subgroup.card_dvd_of_le hDleK)
      have hRperfectD : ⁅R, D⁆ = D := by
        dsimp only [D]
        exact commutator_commutator_eq_of_coprime hRnormK hcopKR
      have hCDRleZ : centralizerWithin D R ≤ ZK := by
        apply (centralizerWithin_le_commutator_of_perfect_coprime_action
          hRnormD hcopDR hRperfectD).trans
        simpa only [ZK, K.map_subtype_commutator] using
          (Subgroup.commutator_mono hDleK hDleK)
      have hCDRbot : centralizerWithin D R = ⊥ := by
        apply le_bot_iff.mp
        intro x hx
        have hxC : x ∈ C := ⟨hDleK hx.1, hx.2⟩
        have hxZ : x ∈ ZK := hCDRleZ hx
        have hxI : x ∈ C ⊓ ZK := ⟨hxC, hxZ⟩
        rw [disjoint_iff.mp hCdisZ] at hxI
        exact hxI
      have hCDdis : Disjoint C D := by
        rw [disjoint_iff]
        apply le_bot_iff.mp
        intro x hx
        have hxFix : x ∈ centralizerWithin D R :=
          ⟨hx.2, hx.1.2⟩
        rw [hCDRbot] at hxFix
        exact hxFix
      have hDCsup : D ⊔ C = K := by
        apply le_antisymm
        · exact sup_le hDleK hCleK
        · exact le_commutator_sup_centralizerWithin_of_coprime
            hRnormK hcopKR
      have hDne : D ≠ ⊥ := by
        intro hDbot
        apply hKR0ne
        rw [Subgroup.commutator_comm]
        exact hDbot
      let JF : Subgroup G := R ⊔ D
      have hRJF : R ≤ JF := le_sup_left
      have hDJF : D ≤ JF := le_sup_right
      let RJF : Subgroup JF := R.subgroupOf JF
      let DJF : Subgroup JF := D.subgroupOf JF
      letI : IsSolvable JF := isSolvable_subgroup_of_isSolvable JF
      letI : DJF.Normal :=
        Subgroup.normal_subgroupOf_sup_of_le_normalizer hRnormD
      have hdisJF : Disjoint DJF RJF := by
        have hdisDR : Disjoint D R :=
          Subgroup.disjoint_of_coprime_natCard hcopDR
        rw [disjoint_iff]
        apply le_bot_iff.mp
        intro x hx
        apply Subgroup.mem_bot.mpr
        apply Subtype.ext
        apply Subgroup.mem_bot.mp
        have hxG : ((x : JF) : G) ∈ D ⊓ R := hx
        rw [disjoint_iff.mp hdisDR] at hxG
        exact hxG
      have hsupJF : DJF ⊔ RJF = ⊤ := by
        rw [← Subgroup.subgroupOf_sup hDJF hRJF, sup_comm]
        exact Subgroup.subgroupOf_self JF
      have hcompJF : DJF.IsComplement' RJF := by
        apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisJF
        rw [← Subgroup.normal_mul DJF RJF, hsupJF]
        rfl
      have hcardDJF : Nat.card DJF = Nat.card D :=
        natCard_subgroupOf_eq hDJF
      have hcardRJF : Nat.card RJF = Nat.card R :=
        natCard_subgroupOf_eq hRJF
      have hJprime : IsPPrimeSubgroup p JF := by
        rw [IsPPrimeSubgroup, ← hcompJF.card_mul,
          hcardDJF, hcardRJF, Nat.coprime_mul_iff_right]
        exact ⟨hKcopP.symm.coprime_dvd_right
          (Subgroup.card_dvd_of_le hDleK), hpR0⟩
      have hJnormV : JF ≤ Subgroup.normalizer (V : Set G) :=
        sup_le hRnormV (hDleK.trans hKnormV)
      have hDDcent :=
        commutator_le_centralizerWithin_of_frobenius_prime_fixed
          JF D R V hDJF hRJF hcompJF hR0prime hCDRbot
            hVelem hJnormV hJprime hCVR0card
      have hDDbot : ⁅D, D⁆ = ⊥ := by
        apply le_bot_iff.mp
        exact hDDcent.trans (by
          intro x hx
          have hxKV : x ∈ centralizerWithin K V :=
            ⟨hDleK hx.1, hx.2⟩
          rw [hCKV] at hxKV
          exact hxKV)
      have hDrootBot : _root_.commutator D = ⊥ := by
        apply Subgroup.map_injective D.subtype_injective
        rw [D.map_subtype_commutator, hDDbot, Subgroup.map_bot]
      have hDcomm : IsMulCommutative D :=
        (_root_.commutator_eq_bot_iff D).mp hDrootBot
      exact false_of_special_coprime_coatom_configuration
        K P R hS hPnormK hsub hCKP hDne hCcard hCDRbot
          hDcomm hCDdis hDCsup hlargeDerived
      -/
      have hKlarge : q ^ 2 < Nat.card K :=
        prime_sq_lt_card_of_derived_quotient hKcomm hlargeDerived
      let CKR : Subgroup G := centralizerWithin K R
      have hCKRne : CKR ≠ ⊥ := by
        intro hbot
        apply hCnotZ
        change CKR ≤ ZK
        rw [hbot]
        exact bot_le
      have hCKRleMain : CKR ≤ centralizerWithin H R := by
        intro x hx
        exact ⟨hKH hx.1, hx.2⟩
      let fCKR : CKR →* centralizerWithin H R :=
        Subgroup.inclusion hCKRleMain
      letI : IsZGroup (centralizerWithin H R) := hZ
      letI : IsZGroup CKR :=
        IsZGroup.of_injective (f := fCKR)
          (Subgroup.inclusion_injective hCKRleMain)
      have hCKRq : IsPGroup q CKR :=
        hKelem.isPGroup.to_le (centralizerWithin_le_left K R)
      letI : Group.IsNilpotent CKR := hCKRq.isNilpotent
      letI : IsCyclic CKR := inferInstance
      letI : Nontrivial CKR :=
        (Subgroup.nontrivial_iff_ne_bot CKR).mpr hCKRne
      have hCKRpow (x : CKR) : x ^ q = 1 := by
        apply Subtype.ext
        exact congrArg K.subtype
          (hKelem.pow_eq_one
            ⟨(x : G), centralizerWithin_le_left K R x.property⟩)
      have hCKRexp : Monoid.exponent CKR = q :=
        (Monoid.exponent_eq_prime_iff hq).mpr
          (fun x hx => orderOf_eq_prime (hCKRpow x) hx)
      have hCKRcard : Nat.card (centralizerWithin K R) = q := by
        change Nat.card CKR = q
        calc
          Nat.card CKR = Monoid.exponent CKR :=
            IsCyclic.exponent_eq_card.symm
          _ = q := hCKRexp
      exact false_of_final_centralizerBlock_configuration
        V K P R hVelem hKelem hVne hCVK hCKV hKnormV hPnormV hRnormV
          hPnormK hRnormK hPp hR0prime hpR hcopVK hcopKR
          hCVR0card hCKRcard hKP hPR0 hKlarge hindecomp
          hgenerated hodd
    · obtain ⟨hS, hCKP, hKpow⟩ :=
        special_and_pow_prime_of_noncomm_dichotomy
          K P R hKq hKne hKodd hnormKPR hcopKP hKP hsub hKcomm
      have hEderived : IsElementaryAbelianGroup q
          (K ⧸ ZK.subgroupOf K) :=
        hderivedQuotientElementary hKpow
      have hCnotZ : ¬ centralizerWithin K R ≤ ZK :=
        hCnotZ_of_elementary hEderived

      let C : Subgroup G := centralizerWithin K R
      let D : Subgroup G := ⁅R, K⁆
      have hCleK : C ≤ K := centralizerWithin_le_left K R
      have hDleK : D ≤ K :=
        Subgroup.le_normalizer_iff_commutator_le_right.mp hRnormK
      have hCne : C ≠ ⊥ := by
        intro hbot
        apply hCnotZ
        rw [show centralizerWithin K R = ⊥ from hbot]
        exact bot_le
      have hCq : IsPGroup q C := hKq.to_le hCleK
      have hCleMain : C ≤ centralizerWithin H R := by
        intro x hx
        exact ⟨hKH hx.1, hx.2⟩
      let fC : C →* centralizerWithin H R :=
        Subgroup.inclusion hCleMain
      letI : IsZGroup (centralizerWithin H R) := hZ
      letI : IsZGroup C :=
        IsZGroup.of_injective (f := fC)
          (Subgroup.inclusion_injective hCleMain)
      letI : Group.IsNilpotent C := hCq.isNilpotent
      letI : IsCyclic C := inferInstance
      letI : Nontrivial C :=
        (Subgroup.nontrivial_iff_ne_bot C).mpr hCne
      have hCpow (x : C) : x ^ q = 1 := by
        apply Subtype.ext
        exact congrArg K.subtype
          (hKpow ⟨(x : G), hCleK x.property⟩)
      have hCexp : Monoid.exponent C = q :=
        (Monoid.exponent_eq_prime_iff hq).mpr
          (fun x hx => orderOf_eq_prime (hCpow x) hx)
      have hCcard : Nat.card (centralizerWithin K R) = q := by
        change Nat.card C = q
        calc
          Nat.card C = Monoid.exponent C := IsCyclic.exponent_eq_card.symm
          _ = q := hCexp
      have hCdisZ : Disjoint C ZK := by
        let I : Subgroup C := ZK.comap C.subtype
        letI : Fact (Nat.card C).Prime := ⟨by
          change (Nat.card (centralizerWithin K R)).Prime
          rw [hCcard]
          exact hq⟩
        rcases I.eq_bot_or_eq_top_of_prime_card with hIbot | hItop
        · rw [disjoint_iff]
          apply le_bot_iff.mp
          intro x hx
          let xC : C := ⟨x, hx.1⟩
          have hxI : xC ∈ I := hx.2
          rw [hIbot] at hxI
          exact Subgroup.mem_bot.mpr
            (congrArg Subtype.val (Subgroup.mem_bot.mp hxI))
        · exfalso
          apply hCnotZ
          intro x hx
          let xC : C := ⟨x, hx⟩
          have hxI : xC ∈ I := by
            rw [hItop]
            exact Subgroup.mem_top xC
          exact hxI
      have hRnormD : R ≤ Subgroup.normalizer (D : Set G) := by
        dsimp only [D]
        exact Subgroup.normalizer_commutator_ge_left R K
      have hcopDR : Nat.Coprime (Nat.card D) (Nat.card R) :=
        hcopKR.coprime_dvd_left (Subgroup.card_dvd_of_le hDleK)
      have hRperfectD : ⁅R, D⁆ = D := by
        dsimp only [D]
        exact commutator_commutator_eq_of_coprime hRnormK hcopKR
      have hCDRleZ : centralizerWithin D R ≤ ZK := by
        apply (centralizerWithin_le_commutator_of_perfect_coprime_action
          hRnormD hcopDR hRperfectD).trans
        simpa only [ZK, K.map_subtype_commutator] using
          (Subgroup.commutator_mono hDleK hDleK)
      have hCDRbot : centralizerWithin D R = ⊥ := by
        apply le_bot_iff.mp
        intro x hx
        have hxC : x ∈ C := ⟨hDleK hx.1, hx.2⟩
        have hxZ : x ∈ ZK := hCDRleZ hx
        have hxI : x ∈ C ⊓ ZK := ⟨hxC, hxZ⟩
        rw [disjoint_iff.mp hCdisZ] at hxI
        exact hxI
      have hCDdis : Disjoint C D := by
        rw [disjoint_iff]
        apply le_bot_iff.mp
        intro x hx
        have hxFix : x ∈ centralizerWithin D R :=
          ⟨hx.2, hx.1.2⟩
        rw [hCDRbot] at hxFix
        exact hxFix
      have hDCsup : D ⊔ C = K := by
        apply le_antisymm
        · exact sup_le hDleK hCleK
        · exact le_commutator_sup_centralizerWithin_of_coprime
            hRnormK hcopKR
      have hDne : D ≠ ⊥ := by
        intro hDbot
        apply hKR0ne
        rw [Subgroup.commutator_comm]
        exact hDbot
      let JF : Subgroup G := R ⊔ D
      have hRJF : R ≤ JF := le_sup_left
      have hDJF : D ≤ JF := le_sup_right
      let RJF : Subgroup JF := R.subgroupOf JF
      let DJF : Subgroup JF := D.subgroupOf JF
      letI : IsSolvable JF := isSolvable_subgroup_of_isSolvable JF
      letI : DJF.Normal :=
        Subgroup.normal_subgroupOf_sup_of_le_normalizer hRnormD
      have hdisJF : Disjoint DJF RJF := by
        have hdisDR : Disjoint D R :=
          Subgroup.disjoint_of_coprime_natCard hcopDR
        rw [disjoint_iff]
        apply le_bot_iff.mp
        intro x hx
        apply Subgroup.mem_bot.mpr
        apply Subtype.ext
        apply Subgroup.mem_bot.mp
        have hxG : ((x : JF) : G) ∈ D ⊓ R := hx
        rw [disjoint_iff.mp hdisDR] at hxG
        exact hxG
      have hsupJF : DJF ⊔ RJF = ⊤ := by
        rw [← Subgroup.subgroupOf_sup hDJF hRJF, sup_comm]
        exact Subgroup.subgroupOf_self JF
      have hcompJF : DJF.IsComplement' RJF := by
        apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisJF
        rw [← Subgroup.normal_mul DJF RJF, hsupJF]
        rfl
      have hcardDJF : Nat.card DJF = Nat.card D :=
        natCard_subgroupOf_eq hDJF
      have hcardRJF : Nat.card RJF = Nat.card R :=
        natCard_subgroupOf_eq hRJF
      have hJprime : IsPPrimeSubgroup p JF := by
        rw [IsPPrimeSubgroup, ← hcompJF.card_mul,
          hcardDJF, hcardRJF, Nat.coprime_mul_iff_right]
        exact ⟨hKcopP.symm.coprime_dvd_right
          (Subgroup.card_dvd_of_le hDleK), hpR0⟩
      have hJnormV : JF ≤ Subgroup.normalizer (V : Set G) :=
        sup_le hRnormV (hDleK.trans hKnormV)
      have hDDcent :=
        commutator_le_centralizerWithin_of_frobenius_prime_fixed
          JF D R V hDJF hRJF hcompJF hR0prime hCDRbot
            hVelem hJnormV hJprime hCVR0card
      have hDDbot : ⁅D, D⁆ = ⊥ := by
        apply le_bot_iff.mp
        exact hDDcent.trans (by
          intro x hx
          have hxKV : x ∈ centralizerWithin K V :=
            ⟨hDleK hx.1, hx.2⟩
          rw [hCKV] at hxKV
          exact hxKV)
      have hDrootBot : _root_.commutator D = ⊥ := by
        apply Subgroup.map_injective D.subtype_injective
        rw [D.map_subtype_commutator, hDDbot, Subgroup.map_bot]
      have hDcomm : IsMulCommutative D :=
        (_root_.commutator_eq_bot_iff D).mp hDrootBot
      exact false_of_special_coprime_coatom_configuration
        K P R hS hPnormK hsub hCKP hDne hCcard hCDRbot
          hDcomm hCDdis hDCsup hlargeDerived

/-- Theorem 3.6 holds at every finite cardinality. -/
theorem oddSemidirectZGroupPLengthStatement_all
    (p n : ℕ) [Fact p.Prime] :
    OddSemidirectZGroupPLengthStatement.{u} p n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro G _ _ _ hcard H R R0 _ hHR hcop hodd hR0R
        hR0prime hZ
      have ihG : ∀ m, m < Nat.card G →
          OddSemidirectZGroupPLengthStatement.{u} p m := by
        intro m hm
        exact ih m (by simpa only [hcard] using hm)
      by_cases hproper : ⁅R, H⁆ < H
      · exact
          oddSemidirectZGroupPLength_properCommutator
            H R R0 hHR hcop hodd hR0R hR0prime hZ hproper ihG
      · have hperfect : ⁅R, H⁆ = H :=
          (lt_or_eq_of_le
            (Subgroup.commutator_le_right R H)).resolve_left hproper
        have hHpl : IsPLengthOne p H := by
          by_cases hOA : pPrimeCore p H = ⊥
          · by_cases hPhi : frattini (pCore p H) = ⊥
            · by_cases hindecomp :
                NormalIndecomposableFactor
                  ((pCore p H).map H.subtype)
              · exact
                  oddSemidirectZGroupPLength_reducedCore
                    H R R0 hHR hcop hodd hR0R hR0prime hZ
                      hperfect hOA hPhi hindecomp ihG
              · exact
                  oddSemidirectZGroupPLength_of_decomposable_pCore
                    H R R0 hHR hcop hodd hR0R hR0prime hZ
                      hperfect hindecomp ihG
            · exact
                oddSemidirectZGroupPLength_of_frattini_pCore_ne_bot
                  H R R0 hHR hcop hodd hR0R hR0prime hZ
                    hperfect hOA hPhi ihG
          · exact
              oddSemidirectZGroupPLength_of_pPrimeCore_ne_bot
                H R R0 hHR hcop hodd hR0R hR0prime hZ
                  hperfect hOA ihG
        exact isPLengthOne_of_mulEquiv hHpl
          (MulEquiv.subgroupCongr hperfect).symm

/-- `BGsection3.v: odd_sdprod_Zgroup_cent_prime_plength1`
(Bender--Glauberman Theorem 3.6). -/
theorem odd_sdprod_Zgroup_cent_prime_plength1
    {G : Type u} [Group G] [Finite G] [IsSolvable G]
    {p : ℕ} [Fact p.Prime]
    (H R R0 : Subgroup G) [H.Normal]
    (hHR : H.IsComplement' R)
    (hcop : Nat.Coprime (Nat.card H) (Nat.card R))
    (hodd : Odd (Nat.card G))
    (hR0R : R0 ≤ R)
    (hR0prime : (Nat.card R0).Prime)
    (hZ : IsZGroup (centralizerWithin H R0)) :
    IsPLengthOne p (⁅R, H⁆ : Subgroup G) :=
  oddSemidirectZGroupPLengthStatement_all p (Nat.card G)
    G rfl H R R0 hHR hcop hodd hR0R hR0prime hZ

/-- Subgroup-ambient form of Theorem 3.6 used in Section 10. -/
theorem odd_sdprod_Zgroup_cent_prime_plength1_of_subgroup
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime]
    (J H R R0 : Subgroup G)
    [IsSolvable J] [Subgroup.Normal (H.subgroupOf J)]
    (hHJ : H ≤ J) (hRJ : R ≤ J)
    (hHR : (H.subgroupOf J).IsComplement' (R.subgroupOf J))
    (hcop : Nat.Coprime (Nat.card H) (Nat.card R))
    (hodd : Odd (Nat.card J))
    (hR0R : R0 ≤ R)
    (hR0prime : (Nat.card R0).Prime)
    (hZ : IsZGroup (centralizerWithin H R0)) :
    IsPLengthOne p (⁅H, R⁆ : Subgroup G) := by
  have hR0J : R0 ≤ J := hR0R.trans hRJ
  have hcopJ : Nat.Coprime
      (Nat.card (H.subgroupOf J))
      (Nat.card (R.subgroupOf J)) := by
    rw [natCard_subgroupOf_eq hHJ, natCard_subgroupOf_eq hRJ]
    exact hcop
  have hR0JRJ : R0.subgroupOf J ≤ R.subgroupOf J :=
    Subgroup.subgroupOf_mono J hR0R
  have hR0Jprime : (Nat.card (R0.subgroupOf J)).Prime := by
    rw [natCard_subgroupOf_eq hR0J]
    exact hR0prime
  have hZJ : IsZGroup
      (centralizerWithin (H.subgroupOf J) (R0.subgroupOf J)) :=
    isZGroup_centralizerWithin_subgroupOf
      (J := J) (H := H) (D := H) (R0 := R0)
      le_rfl hR0J hZ
  have hlocal : IsPLengthOne p
      (⁅R.subgroupOf J, H.subgroupOf J⁆ : Subgroup J) :=
    odd_sdprod_Zgroup_cent_prime_plength1
      (p := p) (H.subgroupOf J) (R.subgroupOf J)
        (R0.subgroupOf J) hHR hcopJ hodd hR0JRJ hR0Jprime hZJ
  have hmap :
      (⁅R.subgroupOf J, H.subgroupOf J⁆ : Subgroup J).map J.subtype =
        (⁅R, H⁆ : Subgroup G) :=
    map_subgroupOf_commutator hHJ hRJ
  let eMap :
      (⁅R.subgroupOf J, H.subgroupOf J⁆ : Subgroup J) ≃*
        (⁅R.subgroupOf J, H.subgroupOf J⁆ : Subgroup J).map J.subtype :=
    Subgroup.equivMapOfInjective _ J.subtype J.subtype_injective
  let e :
      (⁅R.subgroupOf J, H.subgroupOf J⁆ : Subgroup J) ≃*
        (⁅R, H⁆ : Subgroup G) :=
    eMap.trans (MulEquiv.subgroupCongr hmap)
  have hamb : IsPLengthOne p (⁅R, H⁆ : Subgroup G) :=
    isPLengthOne_of_mulEquiv hlocal e
  exact isPLengthOne_of_mulEquiv hamb
    (MulEquiv.subgroupCongr (Subgroup.commutator_comm R H))

end MainInduction

end

end Submission.OddOrder.BG.Section03
