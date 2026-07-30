import Submission.OddOrder.BG.Section15.FittingCore
import Submission.OddOrder.BG.Section14.PTypeEmbedding
import Submission.OddOrder.BG.Section14.PTypeStructure
import Submission.OddOrder.BG.Section14.PartitionAndSignalizers
import Submission.OddOrder.BG.Section13.TauRegularity
import Submission.OddOrder.BG.Section12.SigmaNilpotent
import Submission.OddOrder.BG.Section12.ComplementExistence
import Submission.OddOrder.BG.Section04.OddPGroupRankOne
import Submission.OddOrder.BG.Section04.RankTwoFittingDerived
import Submission.OddOrder.BG.Section05.NarrowAutomorphismAndComplement
import Submission.OddOrder.BG.Section03.PrimeActionCommutatorFitting
import Submission.OddOrder.BG.Section03.PrimeFrobeniusQuotientKernel
import Submission.OddOrder.BG.Section03.FrobeniusSolvableKernel
import Submission.OddOrder.BG.Section03.FrobeniusPrimeFixedPoint
import Submission.OddOrder.BG.Section06.CoprimeDerivedSemidirect
import Submission.OddOrder.MathlibSupport.AmbientFitting
import Submission.OddOrder.MathlibSupport.AmbientSylowTransport
import Submission.OddOrder.MathlibSupport.CoprimeInvariantHall
import Submission.OddOrder.MathlibSupport.CommutatorSup
import Submission.OddOrder.MathlibSupport.ElementaryAbelian
import Submission.OddOrder.MathlibSupport.ElementaryAbelianFunctorial
import Submission.OddOrder.MathlibSupport.MinimalNormal
import Submission.OddOrder.MathlibSupport.MinimalNormalElementaryAbelian
import Submission.OddOrder.MathlibSupport.NilpotentPrimeCoreHall
import Submission.OddOrder.MathlibSupport.NormalPrimeComplementContainment
import Submission.OddOrder.MathlibSupport.PGroupNormalizer
import Submission.OddOrder.MathlibSupport.PSubgroupAbsentPrime
import Submission.OddOrder.MathlibSupport.PCoreSelfQuotient
import Submission.OddOrder.MathlibSupport.PrimeOrderInvariantSylow
import Submission.OddOrder.MathlibSupport.SolvableComplementConjugacy
import Submission.OddOrder.MathlibSupport.StableFactor
import Submission.OddOrder.PF.Section03.InternalDirectProduct

/-!
# Bender--Glauberman Section 15: the Fitting-core structure

This file ports `BGsection15.v`, lines 207--938: Lemma 15.1, Theorem 15.2,
and Corollaries 15.3--15.6.  The two long source conjunctions are represented
by `KappaStructure` and `FCoreStructure`; their field names retain the source
clause labels.  The public theorem aliases retain the Coq declaration names.

The Section 12 theorem `FTtypeF_complement` is applied directly.  Its
elementwise regularity hypothesis and all structural inputs are proved here
from the kappa-complement data, exactly as in the source proof of Lemma 15.1.

MathComp regards every subgroup and every quotient as an ambient group.  Two
small adapters make those coercions explicit here:

* `derivedWithin M` and `secondDerivedWithin M` are the first two derived
  subgroups, mapped back to the ambient group;
* `factorCentralizerWithin A Q N` is the set denoted
  `'C_A(Q / N | 'Q)` in the source.  It consists of the elements of `A` whose
  commutators with `Q` lie in `N`.  It is deliberately exposed as a set: the
  assertions below identify it with a subgroup, while avoiding an unnecessary
  normality argument in the definition.

Following `Section15.FittingCore`, Coq's `M`_F` is written explicitly as
`Fitting_core M`.  It must not be confused with Mathlib's ordinary Fitting
subgroup, whose ambient image is `fittingWithin M`.
-/

namespace Submission.OddOrder.BG.Section15

open Submission.OddOrder.BG.Section03
open Submission.OddOrder.BG.Section04
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section09
open Submission.OddOrder.BG.Section10
open Submission.OddOrder.BG.Section12
open Submission.OddOrder.BG.Section13
open Submission.OddOrder.BG.Section14
open Submission.OddOrder.MathlibSupport
open Submission.OddOrder.PF
open scoped Pointwise IsMulCommutative commutatorElement

noncomputable section

universe u

variable {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]

/-! ## Ambient adapters used by all seven declarations -/

/-- The derived subgroup of an ambient subgroup, mapped back into `G`. -/
def derivedWithin (M : Subgroup G) : Subgroup G :=
  (_root_.commutator M).map M.subtype

/-- The second derived subgroup, again viewed inside the original ambient
group. -/
def secondDerivedWithin (M : Subgroup G) : Subgroup G :=
  derivedWithin (derivedWithin M)

/-- The ambient `p`-core of a subgroup.  This is MathComp's `'O_p(M)`. -/
def pCoreWithin (p : ℕ) (M : Subgroup G) : Subgroup G :=
  (pCore p M).map M.subtype

/-- The subgroup denoted `Kstar = C_(M_sigma)(K)` in Section 15. -/
abbrev kappaCentralizer (M K : Subgroup G) : Subgroup G :=
  centralizerWithin (sigmaCore M) K

/-- The centralizer of the chosen `q'`-Hall complement in the ambient
`q`-core. -/
abbrev hallFixedCore (M K D : Subgroup G) : Subgroup G :=
  centralizerWithin (pCoreWithin (Nat.card (kappaCentralizer M K)) M) D

/-- The source stable-factor centralizer `'C_A(Q / N | 'Q)`. -/
def factorCentralizerWithin
    (A Q N : Subgroup G) : Set G :=
  {a | a ∈ A ∧ ∀ q ∈ Q, ⁅q, a⁆ ∈ N}

/-- Minimal normality of `Q / N` in `M / N`, without quotient-coercion
noise.  The interval formulation is equivalent to the quotient formulation
once `N` and `Q` are normal in `M`. -/
def IsMinimalNormalFactor
    (N Q M : Subgroup G) : Prop :=
  N < Q ∧ Q ≤ M ∧
    (N.subgroupOf M).Normal ∧ (Q.subgroupOf M).Normal ∧
    ∀ L : Subgroup G, N ≤ L → L ≤ Q →
      (L.subgroupOf M).Normal → L = N ∨ L = Q

/-- The subgroup generated by the fixed points in `U` of nonidentity
elements of `M_sigma`. -/
def sigmaFixedPointGenerated (M U : Subgroup G) : Subgroup G :=
  Subgroup.closure
    {u : G | ∃ x : G, x ∈ sigmaCore M ∧ x ≠ 1 ∧
      u ∈ centralizerWithin U (Subgroup.zpowers x)}

/-- The `sigma(M)'`-core of the Fitting subgroup, mapped into `G`; this is
the subgroup called `Y` in Corollary 15.5. -/
def fittingSigmaPrimeCore (M : Subgroup G) : Subgroup G :=
  (piCore (sigmaPrimes M)ᶜ (fittingWithin M)).map
    (fittingWithin M).subtype

/-! ## Local subgroup adapters -/

private theorem derivedWithin_le_15 (M : Subgroup G) :
    derivedWithin M ≤ M :=
  Subgroup.map_subtype_le (_root_.commutator M)

private theorem isPrimeComplement_iff_isHall_compl_singleton_15
    {X : Type*} [Group X] [Finite X]
    {q : ℕ} (hq : q.Prime) {H : Subgroup X} :
    IsPrimeComplement q H ↔ IsHall ({q} : Set ℕ)ᶜ H := by
  constructor
  · intro hH
    constructor
    · intro r hr hrH hrq
      have hrq' : r = q := Set.mem_singleton_iff.mp hrq
      subst r
      exact hH.not_dvd_card hq hrH
    · intro r hr hrIndex
      obtain ⟨n, hn⟩ := hH.exists_index_eq_pow
      have hrq : r ∣ q := hr.dvd_of_dvd_pow (by simpa [hn] using hrIndex)
      have : r = q :=
        (hq.eq_one_or_self_of_dvd r hrq).resolve_left hr.ne_one
      simpa [this]
  · intro hH
    constructor
    · have hnq : ¬q ∣ Nat.card H := by
        intro hqH
        exact hH.isPiNumber_card hq hqH (by simp)
      exact (hq.coprime_iff_not_dvd.mpr hnq).symm
    · refine ⟨H.index.primeFactorsList.length, ?_⟩
      apply Nat.eq_prime_pow_of_unique_prime_dvd
        H.index_ne_zero_of_finite
      intro r hr hrIndex
      have hrq := hH.isPiNumber_index hr hrIndex
      simpa using hrq

private theorem centralizerWithin_map_mulEquiv_15
    {X : Type*} [Group X] (A B : Subgroup X) (e : X ≃* X) :
    (centralizerWithin A B).map e.toMonoidHom =
      centralizerWithin (A.map e.toMonoidHom)
        (B.map e.toMonoidHom) := by
  ext y
  rw [Subgroup.mem_map_equiv]
  constructor
  · intro hy
    refine ⟨Subgroup.mem_map_equiv.mpr hy.1, ?_⟩
    intro b hb
    have hb' : e.symm b ∈ B := Subgroup.mem_map_equiv.mp hb
    simpa using congrArg e (hy.2 (e.symm b) hb')
  · intro hy
    refine ⟨Subgroup.mem_map_equiv.mp hy.1, ?_⟩
    intro b hb
    have heb : e b ∈ B.map e.toMonoidHom :=
      ⟨b, hb, rfl⟩
    simpa using congrArg e.symm (hy.2 (e b) heb)

private theorem elementaryAbelian_of_mulEquiv_15
    {X Y : Type*} [Group X] [Group Y] {p : ℕ}
    (hX : IsElementaryAbelianGroup p X) (e : X ≃* Y) :
    IsElementaryAbelianGroup p Y := by
  refine
    { isPGroup := hX.isPGroup.of_equiv e
      commutative := isMulCommutative_iff.mpr ?_
      pow_eq_one := ?_ }
  · intro x y
    apply e.symm.injective
    simpa using
      (isMulCommutative_iff.mp hX.commutative (e.symm x) (e.symm y))
  · intro x
    apply e.symm.injective
    simpa using hX.pow_eq_one (e.symm x)

private theorem normal_sylow_complement_sdprod_15
    {X : Type*} [Group X] [Finite X]
    {q : ℕ} (hq : q.Prime) {Q D L : Subgroup X}
    (hQ : IsSylowSubgroupOf q Q L)
    (hQnormal : (Q.subgroupOf L).Normal)
    (hDL : D ≤ L)
    (hD : IsHall ({q} : Set ℕ)ᶜ (D.subgroupOf L)) :
    IsInternalSemidirectProductIn Q D L := by
  letI : Fact q.Prime := ⟨hq⟩
  obtain ⟨P, hP⟩ := hQ
  have hQL : Q ≤ L := by
    rw [hP]
    exact Subgroup.map_subtype_le _
  have hQsub : Q.subgroupOf L = (P : Subgroup L) := by
    rw [hP]
    exact Subgroup.comap_map_eq_self_of_injective
      L.subtype_injective (P : Subgroup L)
  refine ⟨hQL, hDL, hQnormal, ?_⟩
  rw [hQsub]
  exact
    ((isPrimeComplement_iff_isHall_compl_singleton_15 hq).mpr hD).sylow_isComplement
      hq P

private theorem centralizerWithin_normalized_by_common_normalizer_15
    {X : Type*} [Group X] {A B C : Subgroup X}
    (hAB : A ≤ Subgroup.normalizer (B : Set X))
    (hAC : A ≤ Subgroup.normalizer (C : Set X)) :
    A ≤ Subgroup.normalizer (centralizerWithin B C : Set X) := by
  rw [Subgroup.le_normalizer_iff]
  intro a ha x hx
  refine ⟨(Subgroup.mem_normalizer_iff.mp (hAB ha) x).mp hx.1, ?_⟩
  intro c hc
  have haInvC : a⁻¹ ∈ Subgroup.normalizer (C : Set X) :=
    (Subgroup.normalizer (C : Set X)).inv_mem (hAC ha)
  have hc' : a⁻¹ * c * a ∈ C := by
    simpa only [inv_inv] using
      (Subgroup.mem_normalizer_iff.mp haInvC c).mp hc
  have hcomm := hx.2 (a⁻¹ * c * a) hc'
  calc
    c * (a * x * a⁻¹) =
        a * ((a⁻¹ * c * a) * x) * a⁻¹ := by group
    _ = a * (x * (a⁻¹ * c * a)) * a⁻¹ := by rw [hcomm]
    _ = (a * x * a⁻¹) * c := by group

private theorem normal_inf_subgroupOf_of_le_15
    {M H C : Subgroup G}
    (hHM : H ≤ M) (hCM : C ≤ M)
    (hHnormal : (H.subgroupOf M).Normal) :
    ((H ⊓ C).subgroupOf C).Normal := by
  have hMnormH : M ≤ Subgroup.normalizer (H : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hHM).mp hHnormal
  apply Subgroup.normal_subgroupOf_of_le_normalizer
  intro c hc
  have hcH := Subgroup.mem_normalizer_iff.mp (hMnormH (hCM hc))
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · intro hz
    exact ⟨(hcH z).mp hz.1,
      C.mul_mem (C.mul_mem hc hz.2) (C.inv_mem hc)⟩
  · intro hz
    have hzC : z ∈ C := by
      have hconj : c⁻¹ * (c * z * c⁻¹) * c ∈ C :=
        C.mul_mem (C.mul_mem (C.inv_mem hc) hz.2) hc
      have heq : c⁻¹ * (c * z * c⁻¹) * c = z := by group
      simpa only [heq] using hconj
    exact ⟨(hcH z).mpr hz.1, hzC⟩

private theorem semidirect_restrict_right_15
    {A B C D : Subgroup G}
    (h : IsInternalSemidirectProductIn A B C) (hDB : D ≤ B) :
    IsInternalSemidirectProductIn A D (A ⊔ D) := by
  have hAC : A ≤ C := h.1
  have hDC : D ≤ C := hDB.trans h.2.1
  have hCnormA : C ≤ Subgroup.normalizer (A : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAC).mp h.2.2.1
  have hAnormal : (A.subgroupOf (A ⊔ D)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      (sup_le Subgroup.le_normalizer (hDC.trans hCnormA))
  have hdis : Disjoint (A.subgroupOf (A ⊔ D))
      (D.subgroupOf (A ⊔ D)) := by
    rw [disjoint_iff]
    apply le_antisymm _ bot_le
    intro x hx
    have hxC : (⟨(x : G), (show A ⊔ D ≤ C from
        sup_le hAC hDC) x.property⟩ : C) ∈
        (A.subgroupOf C) ⊓ (B.subgroupOf C) :=
      ⟨hx.1, hDB hx.2⟩
    have hxBot := h.2.2.2.disjoint.le_bot hxC
    apply Subgroup.mem_bot.mpr
    apply Subtype.ext
    exact congrArg (fun w : C ↦ (w : G))
      (Subgroup.mem_bot.mp hxBot)
  refine ⟨le_sup_left, le_sup_right, hAnormal, ?_⟩
  apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdis
  letI : (A.subgroupOf (A ⊔ D)).Normal := hAnormal
  rw [← Subgroup.normal_mul,
    ← Subgroup.subgroupOf_sup le_sup_left le_sup_right,
    Subgroup.subgroupOf_self]
  rfl

private theorem semidirect_restrict_left_15
    {A B C D : Subgroup G}
    (h : IsInternalSemidirectProductIn A B C)
    (hDA : D ≤ A)
    (hBnormD : B ≤ Subgroup.normalizer (D : Set G)) :
    IsInternalSemidirectProductIn D B (D ⊔ B) := by
  have hDC : D ≤ C := hDA.trans h.1
  have hBC : B ≤ C := h.2.1
  have hDnormal : (D.subgroupOf (D ⊔ B)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      (sup_le Subgroup.le_normalizer hBnormD)
  have hdis : Disjoint (D.subgroupOf (D ⊔ B))
      (B.subgroupOf (D ⊔ B)) := by
    rw [disjoint_iff]
    apply le_antisymm _ bot_le
    intro x hx
    have hxC : (⟨(x : G), (show D ⊔ B ≤ C from
        sup_le hDC hBC) x.property⟩ : C) ∈
        (A.subgroupOf C) ⊓ (B.subgroupOf C) :=
      ⟨hDA hx.1, hx.2⟩
    have hxBot := h.2.2.2.disjoint.le_bot hxC
    apply Subgroup.mem_bot.mpr
    apply Subtype.ext
    exact congrArg (fun w : C ↦ (w : G))
      (Subgroup.mem_bot.mp hxBot)
  refine ⟨le_sup_left, le_sup_right, hDnormal, ?_⟩
  apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdis
  letI : (D.subgroupOf (D ⊔ B)).Normal := hDnormal
  rw [← Subgroup.normal_mul,
    ← Subgroup.subgroupOf_sup le_sup_left le_sup_right,
    Subgroup.subgroupOf_self]
  rfl

private theorem inf_left_sup_right_eq_left_of_semidirect_15
    {Q D L Ms : Subgroup G}
    (hsd : IsInternalSemidirectProductIn Q D Ms)
    (hLQ : L ≤ Q)
    (hDnormL : D ≤ Subgroup.normalizer (L : Set G)) :
    Q ⊓ (L ⊔ D) = L := by
  apply le_antisymm ?_ (le_inf hLQ le_sup_left)
  intro x hx
  have hLDsd : IsInternalSemidirectProductIn L D (L ⊔ D) :=
    semidirect_restrict_left_15 hsd hLQ hDnormL
  let xH : (L ⊔ D : Subgroup G) := ⟨x, hx.2⟩
  obtain ⟨⟨l, d⟩, hld⟩ := hLDsd.2.2.2.2 xH
  have hxld : x = (l : G) * (d : G) :=
    congrArg Subtype.val hld.symm
  have hdQ : (d : G) ∈ Q := by
    have hmem : (l : G)⁻¹ * x ∈ Q :=
      Q.mul_mem (Q.inv_mem (hLQ l.property)) hx.1
    have heq : (l : G)⁻¹ * x = (d : G) := by
      rw [hxld]
      group
    simpa only [heq] using hmem
  let dMs : Ms := ⟨(d : G), hsd.2.1 d.property⟩
  have hdInf : dMs ∈
      (Q.subgroupOf Ms) ⊓ (D.subgroupOf Ms) :=
    ⟨hdQ, d.property⟩
  have hdBot := hsd.2.2.2.disjoint.le_bot hdInf
  have hdOne : (d : G) = 1 := by
    exact congrArg Subtype.val (Subgroup.mem_bot.mp hdBot)
  rw [hxld, hdOne, mul_one]
  exact l.property

private theorem semidirect_sup_eq_15
    {A B H : Subgroup G}
    (h : IsInternalSemidirectProductIn A B H) : A ⊔ B = H := by
  apply le_antisymm (sup_le h.1 h.2.1)
  intro z hz
  let zH : H := ⟨z, hz⟩
  have hzTop : zH ∈ (A.subgroupOf H) ⊔ (B.subgroupOf H) := by
    rw [h.2.2.2.sup_eq_top]
    exact Subgroup.mem_top zH
  have hzSub : zH ∈ (A ⊔ B).subgroupOf H := by
    rw [Subgroup.subgroupOf_sup h.1 h.2.1]
    exact hzTop
  exact hzSub

/-- Coq's `M / Qi` in the `Qi_rec` construction is formed inside the
normalizer of `Qi`.  This wrapper records the corresponding interval chief
factor without prematurely asserting that `Qi` is normal in all of `M`. -/
private def IsMinimalNormalizerFactor_15
    (N Q M : Subgroup G) : Prop :=
  IsMinimalNormalFactor N Q (M ⊓ Subgroup.normalizer (N : Set G))

private theorem normal_in_upper_of_minimalNormalizerFactor_15
    {N Q M : Subgroup G}
    (h : IsMinimalNormalizerFactor_15 N Q M) :
    (N.subgroupOf Q).Normal := by
  apply Subgroup.normal_subgroupOf_of_le_normalizer
  exact h.2.1.trans inf_le_right

private theorem normal_of_normalized_by_iterated_sdprod_15
    {A Q D S K M : Subgroup G}
    (hAM : A ≤ M)
    (hQnormA : Q ≤ Subgroup.normalizer (A : Set G))
    (hDnormA : D ≤ Subgroup.normalizer (A : Set G))
    (hKnormA : K ≤ Subgroup.normalizer (A : Set G))
    (hQD : IsInternalSemidirectProductIn Q D S)
    (hSK : IsInternalSemidirectProductIn S K M) :
    (A.subgroupOf M).Normal := by
  apply (Subgroup.normal_subgroupOf_iff_le_normalizer hAM).mpr
  rw [← semidirect_sup_eq_15 hSK, ← semidirect_sup_eq_15 hQD]
  exact sup_le (sup_le hQnormA hDnormA) hKnormA

private theorem minimalNormalFactor_of_minimalNormalizerFactor_15
    {N Q M : Subgroup G}
    (h : IsMinimalNormalizerFactor_15 N Q M)
    (hNnormalM : (N.subgroupOf M).Normal) :
    IsMinimalNormalFactor N Q M := by
  have hNleM : N ≤ M := (h.1.le.trans h.2.1).trans inf_le_left
  have hMnormN : M ≤ Subgroup.normalizer (N : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNleM).mp hNnormalM
  have hNM : M ⊓ Subgroup.normalizer (N : Set G) = M :=
    inf_eq_left.mpr hMnormN
  simpa only [IsMinimalNormalizerFactor_15, hNM] using h

/-- The interval form of a chief `p`-factor gives the literal quotient
`Q / N` its elementary-abelian structure.  The proof first realizes the
factor as the minimal normal image of `Q` in `M / N`, applies the existing
minimal-normal theorem there, and then transports back along the canonical
quotient/image equivalence. -/
private theorem elementaryAbelian_quotient_of_minimalNormalFactor_15
    {N Q M : Subgroup G} {p : ℕ} [Fact p.Prime]
    [(N.subgroupOf Q).Normal]
    (hminimal : IsMinimalNormalFactor N Q M)
    (hQp : IsPGroup p Q)
    (hsolM : IsSolvable M) :
    IsElementaryAbelianGroup p (Q ⧸ N.subgroupOf Q) := by
  classical
  let NM : Subgroup M := N.subgroupOf M
  let QM : Subgroup M := Q.subgroupOf M
  have hNQ : N ≤ Q := hminimal.1.le
  have hQM : Q ≤ M := hminimal.2.1
  have hNM : N ≤ M := hNQ.trans hQM
  have hNMQM : NM ≤ QM := by
    intro x hx
    exact hNQ hx
  letI : NM.Normal := by
    simpa only [NM] using hminimal.2.2.1
  letI : QM.Normal := by
    simpa only [QM] using hminimal.2.2.2.1
  let qM : M →* M ⧸ NM := QuotientGroup.mk' NM
  have hminImage : IsMinimalNormal (QM.map qM) := by
    refine ⟨?_, inferInstance, ?_⟩
    · intro hbot
      have hleKer : QM ≤ qM.ker :=
        (Subgroup.map_eq_bot_iff QM).mp hbot
      have hleNM : QM ≤ NM := by
        simpa [qM, QuotientGroup.ker_mk'] using hleKer
      have hQN : Q ≤ N := by
        intro x hx
        exact hleNM (show (⟨x, hQM hx⟩ : M) ∈ QM from hx)
      exact (not_le_of_gt hminimal.1) hQN
    · intro L hLnormal hLle hLne
      let R : Subgroup M := L.comap qM
      have hNMR : NM ≤ R := by
        exact QuotientGroup.le_comap_mk' NM L
      have hkerQM : qM.ker ≤ QM := by
        simpa [qM, QuotientGroup.ker_mk'] using hNMQM
      have hRQM : R ≤ QM := by
        calc
          R ≤ (QM.map qM).comap qM := Subgroup.comap_mono hLle
          _ = QM := Subgroup.comap_map_eq_self hkerQM
      have hRnormal : R.Normal := Subgroup.Normal.comap hLnormal qM
      let A : Subgroup G := R.map M.subtype
      have hNA : N ≤ A := by
        intro n hn
        exact ⟨(⟨n, hNM hn⟩ : M), hNMR hn, rfl⟩
      have hAQ : A ≤ Q := by
        rintro _ ⟨r, hr, rfl⟩
        exact hRQM hr
      have hAsub : A.subgroupOf M = R := by
        ext x
        constructor
        · rintro ⟨r, hr, hrx⟩
          have hrx' : r = x := Subtype.ext hrx
          exact hrx' ▸ hr
        · intro hx
          exact ⟨x, hx, rfl⟩
      have hAnormal : (A.subgroupOf M).Normal := by
        rw [hAsub]
        exact hRnormal
      rcases hminimal.2.2.2.2 A hNA hAQ hAnormal with hA | hA
      · exfalso
        apply hLne
        have hRN : R = NM := by
          apply Subgroup.map_injective M.subtype_injective
          calc
            R.map M.subtype = A := rfl
            _ = N := hA
            _ = NM.map M.subtype :=
              (Subgroup.map_subgroupOf_eq_of_le hNM).symm
        calc
          L = R.map qM :=
            (Subgroup.map_comap_eq_self_of_surjective
              (QuotientGroup.mk'_surjective NM) L).symm
          _ = NM.map qM := congrArg (Subgroup.map qM) hRN
          _ = ⊥ := QuotientGroup.map_mk'_self NM
      · have hRQM_eq : R = QM := by
          apply Subgroup.map_injective M.subtype_injective
          calc
            R.map M.subtype = A := rfl
            _ = Q := hA
            _ = QM.map M.subtype :=
              (Subgroup.map_subgroupOf_eq_of_le hQM).symm
        have hImageEq : QM.map qM = L := by
          calc
            QM.map qM = R.map qM :=
              congrArg (Subgroup.map qM) hRQM_eq.symm
            _ = L := Subgroup.map_comap_eq_self_of_surjective
              (QuotientGroup.mk'_surjective NM) L
        exact hImageEq.le
  let eQM : QM ≃* Q := Subgroup.subgroupOfEquivOfLe hQM
  have hQMp : IsPGroup p QM := hQp.of_equiv eQM.symm
  have hImageP : IsPGroup p (QM.map qM) := hQMp.map qM
  letI : IsSolvable M := hsolM
  letI : IsSolvable (M ⧸ NM) :=
    isSolvable_quotient_of_isSolvable NM
  letI : IsSolvable (QM.map qM) :=
    isSolvable_subgroup_of_isSolvable (QM.map qM)
  have hImageAbelian :=
    hminImage.isElementaryAbelian_of_isPGroup hImageP
  have hElemImage : IsElementaryAbelianGroup p (QM.map qM) :=
    ⟨hImageP, hImageAbelian.1, hImageAbelian.2⟩
  let toQM : Q →* QM :=
    { toFun := fun x ↦ ⟨⟨(x : G), hQM x.property⟩, x.property⟩
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl }
  have htoQM : Function.Surjective toQM := by
    intro x
    exact ⟨⟨(((x : QM) : M) : G), x.property⟩, rfl⟩
  let f : Q →* QM.map qM := (qM.subgroupMap QM).comp toQM
  have hf : Function.Surjective f :=
    (qM.subgroupMap_surjective QM).comp htoQM
  have hfker : N.subgroupOf Q = f.ker := by
    ext x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      apply Subtype.ext
      exact QuotientGroup.eq_one_iff (toQM x : M) |>.mpr hx
    · intro hx
      have hx' := congrArg Subtype.val hx
      exact QuotientGroup.eq_one_iff (toQM x : M) |>.mp hx'
  let e : (Q ⧸ N.subgroupOf Q) ≃* QM.map qM :=
    QuotientGroup.liftEquiv (N.subgroupOf Q) hf hfker
  exact elementaryAbelian_of_mulEquiv_15 hElemImage e.symm

private theorem isNilpotent_of_le_15
    {A B : Subgroup G} (hB : Group.IsNilpotent B) (hAB : A ≤ B) :
    Group.IsNilpotent A := by
  letI : Group.IsNilpotent B := hB
  have hsub : Group.IsNilpotent (A.subgroupOf B) := by infer_instance
  letI : Group.IsNilpotent (A.subgroupOf B) := hsub
  exact Group.nilpotent_of_mulEquiv
    (Subgroup.subgroupOfEquivOfLe hAB)

/-- The source stable-factor centralizer is a subgroup whenever its modulus
is normalized by the ambient acting subgroup. -/
private def factorCentralizerSubgroup_15
    {X : Type*} [Group X] {A Q N : Subgroup X}
    (hAN : A ≤ Subgroup.normalizer (N : Set X)) : Subgroup X where
  carrier := factorCentralizerWithin A Q N
  one_mem' := ⟨A.one_mem, by simp [commutatorElement_def]⟩
  mul_mem' := by
    rintro a b ⟨haA, ha⟩ ⟨hbA, hb⟩
    refine ⟨A.mul_mem haA hbA, ?_⟩
    intro z hzQ
    have hconj : a * ⁅z, b⁆ * a⁻¹ ∈ N :=
      (Subgroup.mem_normalizer_iff.mp (hAN haA) ⁅z, b⁆).mp
        (hb z hzQ)
    have heq :
        ⁅z, a * b⁆ = ⁅z, a⁆ * (a * ⁅z, b⁆ * a⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [heq]
    exact N.mul_mem (ha z hzQ) hconj
  inv_mem' := by
    rintro a ⟨haA, ha⟩
    refine ⟨A.inv_mem haA, ?_⟩
    intro z hzQ
    have hinv : ⁅z, a⁆⁻¹ ∈ N := N.inv_mem (ha z hzQ)
    have haInvNorm : a⁻¹ ∈ Subgroup.normalizer (N : Set X) :=
      (Subgroup.normalizer (N : Set X)).inv_mem (hAN haA)
    have hconj : a⁻¹ * ⁅z, a⁆⁻¹ * a ∈ N :=
      by
        simpa only [inv_inv] using
          (Subgroup.mem_normalizer_iff.mp haInvNorm ⁅z, a⁆⁻¹).mp hinv
    have heq : ⁅z, a⁻¹⁆ = a⁻¹ * ⁅z, a⁆⁻¹ * a := by
      simp only [commutatorElement_def]
      group
    rwa [heq]

private theorem factorCentralizerSubgroup_normalized_15
    {X : Type*} [Group X] {A Q N B : Subgroup X}
    (hAN : A ≤ Subgroup.normalizer (N : Set X))
    (hBA : B ≤ Subgroup.normalizer (A : Set X))
    (hBQ : B ≤ Subgroup.normalizer (Q : Set X))
    (hBN : B ≤ Subgroup.normalizer (N : Set X)) :
    B ≤ Subgroup.normalizer
      (factorCentralizerSubgroup_15 (Q := Q) hAN : Set X) := by
  have hconj_mem : ∀ b ∈ B, ∀ x ∈
      factorCentralizerSubgroup_15 (Q := Q) hAN,
      b * x * b⁻¹ ∈ factorCentralizerSubgroup_15 (Q := Q) hAN := by
    intro b hb x hx
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hBA hb) x).mp hx.1, ?_⟩
    intro z hzQ
    have hbInvQ : b⁻¹ ∈ Subgroup.normalizer (Q : Set X) :=
      (Subgroup.normalizer (Q : Set X)).inv_mem (hBQ hb)
    have hz' : b⁻¹ * z * b ∈ Q := by
      simpa only [inv_inv] using
        (Subgroup.mem_normalizer_iff.mp hbInvQ z).mp hzQ
    have hcommN : ⁅b⁻¹ * z * b, x⁆ ∈ N := hx.2 _ hz'
    have hconjN : b * ⁅b⁻¹ * z * b, x⁆ * b⁻¹ ∈ N :=
      (Subgroup.mem_normalizer_iff.mp (hBN hb) _).mp hcommN
    have heq :
        ⁅z, b * x * b⁻¹⁆ = b * ⁅b⁻¹ * z * b, x⁆ * b⁻¹ := by
      simp only [commutatorElement_def]
      group
    rwa [heq]
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact hconj_mem b hb x
  · intro hx
    have hback := hconj_mem b⁻¹ (B.inv_mem hb) (b * x * b⁻¹) hx
    have heq : b⁻¹ * (b * x * b⁻¹) * (b⁻¹)⁻¹ = x := by group
    rwa [heq] at hback

/-- A normal subgroup disjoint from the right factor of a coprime internal
semidirect product lies in the left factor.  This is the cardinal form of
MathComp's `coprime_mulG_setI_norm`. -/
private theorem normal_le_left_of_disjoint_right_of_coprime_sdprod_15
    {A B H N : Subgroup G}
    (hsd : IsInternalSemidirectProductIn A B N)
    (hcop : Nat.Coprime (Nat.card A) (Nat.card B))
    (hHN : H ≤ N) (hHnormal : (H.subgroupOf N).Normal)
    (hdis : Disjoint H B) : H ≤ A := by
  let AN : Subgroup N := A.subgroupOf N
  let BN : Subgroup N := B.subgroupOf N
  let HN : Subgroup N := H.subgroupOf N
  letI : HN.Normal := by simpa only [HN] using hHnormal
  have hdisN : Disjoint HN BN := by
    rw [disjoint_iff]
    apply le_antisymm
    · intro x hx
      apply Subgroup.mem_bot.mpr
      apply Subtype.ext
      have hxbot : ((x : N) : G) ∈ (⊥ : Subgroup G) := by
        rw [← disjoint_iff.mp hdis]
        exact ⟨hx.1, hx.2⟩
      exact Subgroup.mem_bot.mp hxbot
    · exact bot_le
  have hBNnormHN : BN ≤ Subgroup.normalizer (HN : Set N) := by
    rw [HN.normalizer_eq_top]
    exact le_top
  have hcardSup : Nat.card (HN ⊔ BN : Subgroup N) =
      Nat.card HN * Nat.card BN := by
    simpa only [sup_comm, mul_comm] using
      (natCard_sup_eq_mul_of_disjoint_of_le_normalizer
        hdisN.symm hBNnormHN)
  have hcompN : AN.IsComplement' BN := by
    simpa only [AN, BN] using hsd.2.2.2
  have hprodDvd : Nat.card HN * Nat.card BN ∣
      Nat.card AN * Nat.card BN := by
    rw [← hcardSup, hcompN.card_mul]
    simpa only [Subgroup.card_top] using
      (Subgroup.card_dvd_of_le (show HN ⊔ BN ≤ ⊤ from le_top))
  have hcardDvd : Nat.card HN ∣ Nat.card AN :=
    Nat.dvd_of_mul_dvd_mul_right Nat.card_pos hprodDvd
  have hcopAN : Nat.Coprime (Nat.card AN) AN.index := by
    rw [hcompN.symm.index_eq_card]
    simpa only [AN, BN,
      MathlibSupport.natCard_subgroupOf_eq hsd.1,
      MathlibSupport.natCard_subgroupOf_eq hsd.2.1] using hcop
  have hHallAN : IsHall (primeSupport (Nat.card AN)) AN :=
    isHall_primeSupport AN hcopAN
  have hHNpi : IsPiNumber (primeSupport (Nat.card AN)) (Nat.card HN) :=
    IsPiNumber.primeSupport_self.of_dvd hcardDvd
  have hHNAN : HN ≤ AN :=
    normal_isPiNumber_le_isHall (show HN.Normal from inferInstance)
      hHNpi hHallAN
  intro x hx
  exact hHNAN (show (⟨x, hHN hx⟩ : N) ∈ HN from hx)

private theorem isComplement_subgroupOf_of_left_le_15
    {X : Type*} [Group X] {N C T : Subgroup X}
    (hNC : N.IsComplement' C) (hNT : N ≤ T) :
    (N.subgroupOf T).IsComplement'
      ((C ⊓ T).subgroupOf T) := by
  change Function.Bijective
    (fun x : (N.subgroupOf T) × ((C ⊓ T).subgroupOf T) ↦
      (x.1 : T) * (x.2 : T))
  constructor
  · intro x y hxy
    let xX : N × C :=
      (⟨((x.1 : T) : X), x.1.property⟩,
        ⟨((x.2 : T) : X), x.2.property.1⟩)
    let yX : N × C :=
      (⟨((y.1 : T) : X), y.1.property⟩,
        ⟨((y.2 : T) : X), y.2.property.1⟩)
    have hxyX : (xX.1 : X) * (xX.2 : X) =
        (yX.1 : X) * (yX.2 : X) :=
      congrArg Subtype.val hxy
    have hpair : xX = yX := hNC.1 hxyX
    apply Prod.ext
    · apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : N × C ↦ (z.1 : X)) hpair
    · apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : N × C ↦ (z.2 : X)) hpair
  · intro t
    obtain ⟨⟨n, c⟩, hnc⟩ := hNC.2 (t : X)
    have hcT : (c : X) ∈ T := by
      have hcEq : (c : X) = (n : X)⁻¹ * (t : X) := by
        rw [← hnc]
        simp
      rw [hcEq]
      exact T.mul_mem (T.inv_mem (hNT n.property)) t.property
    let nT : N.subgroupOf T :=
      ⟨⟨(n : X), hNT n.property⟩, n.property⟩
    let cT : (C ⊓ T).subgroupOf T :=
      ⟨⟨(c : X), hcT⟩, ⟨c.property, hcT⟩⟩
    refine ⟨(nT, cT), ?_⟩
    apply Subtype.ext
    exact hnc

private def subgroupQuotientEquivImage_15
    {X : Type*} [Group X] (N H : Subgroup X) [N.Normal] :
    (H ⧸ N.subgroupOf H) ≃* H.map (QuotientGroup.mk' N) := by
  letI : (N.subgroupOf H).Normal :=
    Subgroup.Normal.subgroupOf (inferInstance : N.Normal) H
  exact QuotientGroup.liftEquiv (N.subgroupOf H)
    ((QuotientGroup.mk' N).subgroupMap_surjective H) (by
      rw [Subgroup.ker_subgroupMap, QuotientGroup.ker_mk'])

private theorem quotient_semiregular_of_injective_on_sup_15
    {X : Type*} [Group X] [Finite X]
    {N D K : Subgroup X} [N.Normal]
    (hreg : IsSemiregularConjugation D K)
    (hinj : Function.Injective
      ((QuotientGroup.mk' N).subgroupMap (D ⊔ K))) :
    IsSemiregularConjugation
      (D.map (QuotientGroup.mk' N))
      (K.map (QuotientGroup.mk' N)) := by
  intro kb hkb db hfix
  rcases kb.property with ⟨k, hk, hkq⟩
  rcases db.property with ⟨d, hd, hdq⟩
  let J : Subgroup X := D ⊔ K
  let kJ : J :=
    ⟨k, (show K ≤ D ⊔ K from le_sup_right) hk⟩
  let dJ : J :=
    ⟨d, (show D ≤ D ⊔ K from le_sup_left) hd⟩
  have hkJ : kJ ≠ 1 := by
    intro hk1
    apply hkb
    apply Subtype.ext
    change (kb : X ⧸ N) = (1 : X ⧸ N)
    rw [← hkq]
    have hkX : k = (1 : X) := by
      exact congrArg (fun z : J ↦ (z : X)) hk1
    simpa only [map_one] using
      congrArg (QuotientGroup.mk' N) hkX
  have hmap :
      (QuotientGroup.mk' N).subgroupMap J
          (kJ * dJ * kJ⁻¹) =
        (QuotientGroup.mk' N).subgroupMap J dJ := by
    apply Subtype.ext
    change (QuotientGroup.mk' N) (k * d * k⁻¹) =
      (QuotientGroup.mk' N) d
    simpa only [map_mul, map_inv, hkq, hdq] using hfix
  have hraw : k * d * k⁻¹ = d := by
    exact congrArg (fun z : J ↦ (z : X)) (hinj hmap)
  have hkK : (⟨k, hk⟩ : K) ≠ 1 := by
    intro hk1
    apply hkJ
    apply Subtype.ext
    exact congrArg (fun z : K ↦ (z : X)) hk1
  have hd1 : (⟨d, hd⟩ : D) = 1 :=
    hreg ⟨k, hk⟩ hkK ⟨d, hd⟩ hraw
  apply Subtype.ext
  change (db : X ⧸ N) = (1 : X ⧸ N)
  rw [← hdq]
  have hdX : d = (1 : X) := by
    exact congrArg (fun z : D ↦ (z : X)) hd1
  simpa only [map_one] using congrArg (QuotientGroup.mk' N) hdX

private theorem semidirect_reassociate_15
    {S U K F M : Subgroup G}
    (hSF : IsInternalSemidirectProductIn S F M)
    (hUK : IsInternalSemidirectProductIn U K F) :
    IsInternalSemidirectProductIn (S ⊔ U) K M := by
  have hSU := semidirect_restrict_right_15 hSF hUK.1
  have hSM : S ≤ M := hSF.1
  have hUM : U ≤ M := hUK.1.trans hSF.2.1
  have hKM : K ≤ M := hUK.2.1.trans hSF.2.1
  have hMnormS : M ≤ Subgroup.normalizer (S : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hSM).mp hSF.2.2.1
  have hFnormU : F ≤ Subgroup.normalizer (U : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUK.1).mp hUK.2.2.1
  have hKnormSU : K ≤ Subgroup.normalizer ((S ⊔ U : Subgroup G) : Set G) := by
    exact (le_inf (hKM.trans hMnormS)
      (hUK.2.1.trans hFnormU)).trans
        (Subgroup.normalizer_inf_normalizer_le_normalizer_sup S U)
  have hMeq : M = S ⊔ (U ⊔ K) := by
    calc
      M = S ⊔ F := (semidirect_sup_eq_15 hSF).symm
      _ = S ⊔ (U ⊔ K) := by rw [semidirect_sup_eq_15 hUK]
  have hMnormSU : M ≤ Subgroup.normalizer ((S ⊔ U : Subgroup G) : Set G) := by
    rw [hMeq]
    exact sup_le
      (le_sup_left.trans Subgroup.le_normalizer)
      (sup_le (le_sup_right.trans Subgroup.le_normalizer) hKnormSU)
  have hAnormal : ((S ⊔ U).subgroupOf M).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hMnormSU
  have hdis : Disjoint ((S ⊔ U).subgroupOf M) (K.subgroupOf M) := by
    rw [disjoint_iff]
    apply le_antisymm _ bot_le
    intro x hx
    let xA : (S ⊔ U : Subgroup G) := ⟨(x : G), hx.1⟩
    obtain ⟨⟨s, u⟩, hsu⟩ := hSU.2.2.2.2 xA
    have hxsu : (x : G) = (s : G) * (u : G) :=
      congrArg Subtype.val hsu.symm
    have hsF : (s : G) ∈ F := by
      have hxuF : (x : G) * (u : G)⁻¹ ∈ F :=
        F.mul_mem (hUK.2.1 hx.2) (F.inv_mem (hUK.1 u.property))
      simpa [hxsu, mul_assoc] using hxuF
    have hsBot : (s : G) ∈ (⊥ : Subgroup G) := by
      have hsInf : (⟨(s : G), hSM s.property⟩ : M) ∈
          (S.subgroupOf M) ⊓ (F.subgroupOf M) := ⟨s.property, hsF⟩
      have := hSF.2.2.2.disjoint.le_bot hsInf
      simpa using this
    have hsOne : (s : G) = 1 := Subgroup.mem_bot.mp hsBot
    have hxu : (x : G) = u := by simpa [hsOne] using hxsu
    have hxBot : (x : G) ∈ (⊥ : Subgroup G) := by
      have huK : (u : G) ∈ K := hxu ▸ hx.2
      have huInf : (⟨(u : G), hUK.1 u.property⟩ : F) ∈
          (U.subgroupOf F) ⊓ (K.subgroupOf F) := ⟨u.property, huK⟩
      have := hUK.2.2.2.disjoint.le_bot huInf
      simpa [hxu] using this
    simpa using hxBot
  refine ⟨sup_le hSM hUM, hKM, hAnormal, ?_⟩
  apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdis
  letI : ((S ⊔ U).subgroupOf M).Normal := hAnormal
  rw [← Subgroup.normal_mul]
  have hsup : (S ⊔ U).subgroupOf M ⊔ K.subgroupOf M = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (sup_le hSM hUM) hKM,
      sup_assoc, ← hMeq]
    exact Subgroup.subgroupOf_self M
  rw [hsup]
  rfl

private theorem isMulCommutative_of_le_15
    {A B : Subgroup G} (hAB : A ≤ B) (hB : IsMulCommutative B) :
    IsMulCommutative A := by
  rw [isMulCommutative_iff] at hB ⊢
  intro x y
  apply A.subtype_injective
  exact congrArg Subtype.val
    (hB ⟨x, hAB x.property⟩ ⟨y, hAB y.property⟩)

private theorem isCyclic_of_le_15
    {A B : Subgroup G} (hAB : A ≤ B) (hB : IsCyclic B) : IsCyclic A := by
  letI : IsCyclic B := hB
  exact Subgroup.isCyclic_of_le hAB

private theorem isSolvable_of_le_15
    {A B : Subgroup G} (hB : IsSolvable B) (hAB : A ≤ B) :
    IsSolvable A :=
  isSolvable_of_injective (Subgroup.inclusion hAB)
    (Subgroup.inclusion_injective hAB)

private theorem isPiNumber_orderOf_of_mem_15
    {pi : Set ℕ} {H : Subgroup G} {x : G}
    (hH : IsPiNumber pi (Nat.card H)) (hxH : x ∈ H) :
    IsPiNumber pi (orderOf x) :=
  hH.of_dvd (H.orderOf_dvd_natCard hxH)

private theorem pCoreWithin_normal_15 (p : ℕ) (M : Subgroup G) :
    ((pCoreWithin p M).subgroupOf M).Normal := by
  change (((pCore p M).map M.subtype).comap M.subtype).Normal
  rw [Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
  infer_instance

private noncomputable def semidirectQuotientEquiv_15
    {N H K : Subgroup G}
    (hsd : IsInternalSemidirectProductIn N H K) :
    letI : (N.subgroupOf K).Normal := hsd.2.2.1
    K ⧸ N.subgroupOf K ≃* H := by
  letI : (N.subgroupOf K).Normal := hsd.2.2.1
  exact hsd.2.2.2.symm.QuotientMulEquiv.trans
    (Subgroup.subgroupOfEquivOfLe hsd.2.1)

private theorem complement_nilpotent_of_nilpotent_quotient_15
    {N H L : Subgroup G}
    (hsd : IsInternalSemidirectProductIn N H L)
    (hquot : letI : (N.subgroupOf L).Normal := hsd.2.2.1
      Group.IsNilpotent (L ⧸ N.subgroupOf L)) :
    Group.IsNilpotent H := by
  letI : (N.subgroupOf L).Normal := hsd.2.2.1
  letI : Group.IsNilpotent (L ⧸ N.subgroupOf L) := hquot
  exact Group.nilpotent_of_mulEquiv (semidirectQuotientEquiv_15 hsd)

private theorem qi_layer_partner_obstruction_15
    {M Ms Ks K K₁ D Q Qi L : Subgroup G}
    (hqPrime : (Nat.card Ks).Prime)
    (hsolM : IsSolvable M)
    (hQq : IsPGroup (Nat.card Ks) Q)
    (hKsQ : Ks ≤ Q)
    (hcentQDQi : centralizerWithin Q D ≤ Qi)
    (hQiL : Qi < L)
    (hLQ : L ≤ Q)
    (hLnormQi : L ≤ Subgroup.normalizer (Qi : Set G))
    (hQiInv : D ⊔ K ≤ Subgroup.normalizer (Qi : Set G))
    (hLInv : D ⊔ K ≤ Subgroup.normalizer (L : Set G))
    (hQDsd : IsInternalSemidirectProductIn Q D Ms)
    (hSigmaK : IsInternalSemidirectProductIn Ms K M)
    (hKnormD : K ≤ Subgroup.normalizer (D : Set G))
    (hK₁K : K₁ ≤ K)
    (hK₁prime : (Nat.card K₁).Prime)
    (hcentK₁ : centralizerWithin Ms K₁ = Ks)
    (hcopMsK : Nat.Coprime (Nat.card Ms) (Nat.card K))
    (hHallD : IsHall ({Nat.card Ks} : Set ℕ)ᶜ (D.subgroupOf Ms)) :
    ¬ (Ks ≤ L → Ks ≤ Qi) := by
  classical
  let q := Nat.card Ks
  letI : Fact q.Prime := ⟨hqPrime⟩
  intro hreg
  have hKsInfLQi : Ks ⊓ L ≤ Qi := by
    let I : Subgroup Ks := (Ks ⊓ L).subgroupOf Ks
    letI : Fact (Nat.card Ks).Prime := ⟨hqPrime⟩
    rcases I.eq_bot_or_eq_top_of_prime_card with hbot | htop
    · intro x hx
      have hxI : (⟨x, hx.1⟩ : Ks) ∈ I := hx
      rw [hbot] at hxI
      have hxOne : x = 1 :=
        congrArg Subtype.val (Subgroup.mem_bot.mp hxI)
      simpa only [hxOne] using Qi.one_mem
    · have hKsL : Ks ≤ L :=
        (Subgroup.subgroupOf_eq_top.mp htop).trans inf_le_right
      exact inf_le_left.trans (hreg hKsL)

  let H : Subgroup G := L ⊔ D
  let J : Subgroup G := H ⊔ K₁
  have hDnormL : D ≤ Subgroup.normalizer (L : Set G) :=
    le_sup_left.trans hLInv
  have hKnormL : K ≤ Subgroup.normalizer (L : Set G) :=
    le_sup_right.trans hLInv
  have hKnormH : K ≤ Subgroup.normalizer (H : Set G) := by
    exact (le_inf hKnormL hKnormD).trans
      (Subgroup.normalizer_inf_normalizer_le_normalizer_sup L D)
  have hHMs : H ≤ Ms :=
    sup_le (hLQ.trans hQDsd.1) hQDsd.2.1
  have hHKsd : IsInternalSemidirectProductIn H K (H ⊔ K) :=
    semidirect_restrict_left_15 hSigmaK hHMs hKnormH
  have hHK₁sd : IsInternalSemidirectProductIn H K₁ J := by
    simpa only [J] using semidirect_restrict_right_15 hHKsd hK₁K
  have hQinfH : Q ⊓ H = L := by
    simpa only [H] using
      inf_left_sup_right_eq_left_of_semidirect_15 hQDsd hLQ hDnormL
  have hcentHK₁ : centralizerWithin H K₁ ≤ Qi := by
    intro x hx
    have hxMs : x ∈ Ms := hHMs hx.1
    have hxKs : x ∈ Ks := by
      rw [← hcentK₁]
      exact ⟨hxMs, hx.2⟩
    have hxL : x ∈ L := by
      have hxInf : x ∈ Q ⊓ H := ⟨hKsQ hxKs, hx.1⟩
      rw [hQinfH] at hxInf
      exact hxInf
    exact hKsInfLQi ⟨hxKs, hxL⟩

  have hHJ : H ≤ J := le_sup_left
  have hK₁J : K₁ ≤ J := le_sup_right
  have hQiH : Qi ≤ H := hQiL.le.trans le_sup_left
  have hQiJ : Qi ≤ J := hQiH.trans hHJ
  have hLJ : L ≤ J := le_sup_left.trans hHJ
  have hDJ : D ≤ J := le_sup_right.trans hHJ
  have hJM : J ≤ M :=
    sup_le (hHMs.trans hSigmaK.1) (hK₁K.trans hSigmaK.2.1)
  have hsolJ : IsSolvable J :=
    isSolvable_of_injective (Subgroup.inclusion hJM)
      (Subgroup.inclusion_injective hJM)
  letI : IsSolvable J := hsolJ
  have hDnormQi : D ≤ Subgroup.normalizer (Qi : Set G) :=
    le_sup_left.trans hQiInv
  have hK₁normQi : K₁ ≤ Subgroup.normalizer (Qi : Set G) :=
    hK₁K.trans (le_sup_right.trans hQiInv)
  have hJnormQi : J ≤ Subgroup.normalizer (Qi : Set G) := by
    simpa only [J, H] using
      (sup_le (sup_le hLnormQi hDnormQi) hK₁normQi)
  have hQiJnormal : (Qi.subgroupOf J).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hJnormQi

  let HJ : Subgroup J := H.subgroupOf J
  let K₁J : Subgroup J := K₁.subgroupOf J
  let QiJ : Subgroup J := Qi.subgroupOf J
  let LJ : Subgroup J := L.subgroupOf J
  let DJ : Subgroup J := D.subgroupOf J
  letI : HJ.Normal := by simpa only [HJ] using hHK₁sd.2.2.1
  letI : QiJ.Normal := by simpa only [QiJ] using hQiJnormal
  have hQiJHJ : QiJ ≤ HJ := by
    intro x hx
    exact hQiH hx
  have hcopQiK₁ : Nat.Coprime (Nat.card Qi) (Nat.card K₁) :=
    hcopMsK.coprime_dvd_left
        (Subgroup.card_dvd_of_le (hQiH.trans hHMs))
      |>.coprime_dvd_right (Subgroup.card_dvd_of_le hK₁K)
  have hcopQiJK₁J : Nat.Coprime (Nat.card QiJ) (Nat.card K₁J) := by
    simpa only [QiJ, K₁J,
      MathlibSupport.natCard_subgroupOf_eq hQiJ,
      MathlibSupport.natCard_subgroupOf_eq hK₁J] using hcopQiK₁
  have hK₁Jprime : (Nat.card K₁J).Prime := by
    simpa only [K₁J,
      MathlibSupport.natCard_subgroupOf_eq hK₁J] using hK₁prime
  have hcentJ : centralizerWithin HJ K₁J ≤ QiJ := by
    intro x hx
    have hxG : ((x : J) : G) ∈ centralizerWithin H K₁ := by
      refine ⟨hx.1, ?_⟩
      intro k hk
      let kJ : J := ⟨k, hK₁J hk⟩
      have hxk := hx.2 kJ (show kJ ∈ K₁J from hk)
      exact congrArg (fun z : J ↦ (z : G)) hxk
    exact hcentHK₁ hxG
  have hnilHJ : Group.IsNilpotent (HJ ⧸ QiJ.subgroupOf HJ) :=
    primeFrobeniusQuotientKernel_nilpotent
      hHK₁sd.2.2.2 hQiJHJ hcopQiJK₁J hK₁Jprime hcentJ

  have hLJHJ : LJ ≤ HJ := by
    intro x hx
    exact (show L ≤ H from le_sup_left) hx
  have hDJHJ : DJ ≤ HJ := by
    intro x hx
    exact (show D ≤ H from le_sup_right) hx
  let NH : Subgroup HJ := QiJ.subgroupOf HJ
  let LH : Subgroup HJ := LJ.subgroupOf HJ
  let DH : Subgroup HJ := DJ.subgroupOf HJ
  letI : NH.Normal := by
    simpa only [NH] using
      Subgroup.Normal.subgroupOf (show QiJ.Normal from inferInstance) HJ
  let Hbar := HJ ⧸ NH
  let qH : HJ →* Hbar := QuotientGroup.mk' NH
  let Lbar : Subgroup Hbar := LH.map qH
  let Dbar : Subgroup Hbar := DH.map qH
  letI : Group.IsNilpotent Hbar := by
    simpa only [Hbar, NH] using hnilHJ

  have hNHLH : NH ≤ LH := by
    intro x hx
    exact hQiL.le hx
  let eLJ : LJ ≃* L := Subgroup.subgroupOfEquivOfLe hLJ
  let eLH : LH ≃* LJ := Subgroup.subgroupOfEquivOfLe hLJHJ
  have hLq : IsPGroup q L := hQq.to_le hLQ
  have hLHq : IsPGroup q LH :=
    hLq.of_equiv (eLJ.symm.trans eLH.symm)
  have hLbarq : IsPGroup q Lbar := hLHq.map qH

  have hDcomp : IsPrimeComplement q (D.subgroupOf Ms) :=
    (isPrimeComplement_iff_isHall_compl_singleton_15 hqPrime).mpr
      (by simpa only [q] using hHallD)
  have hDprime : IsPPrimeSubgroup q D := by
    unfold IsPPrimeSubgroup
    simpa only [MathlibSupport.natCard_subgroupOf_eq hQDsd.2.1] using
      hDcomp.card_coprime.symm
  let eDJ : DJ ≃* D := Subgroup.subgroupOfEquivOfLe hDJ
  let eDH : DH ≃* DJ := Subgroup.subgroupOfEquivOfLe hDJHJ
  have hDHprime : IsPPrimeSubgroup q DH := by
    unfold IsPPrimeSubgroup at hDprime ⊢
    rw [Nat.card_congr (eDH.trans eDJ).toEquiv]
    exact hDprime
  have hDbarPrime : IsPPrimeSubgroup q Dbar :=
    hDHprime.coprime_dvd_right (Subgroup.card_map_dvd DH qH)
  have hLbarCore : Lbar ≤ pCore q Hbar :=
    hLbarq.le_pCore_of_isNilpotent
  have hDbarCore : Dbar ≤ pPrimeCore q Hbar :=
    isPPrimeSubgroup_le_normal_primeComplement
      (by infer_instance)
      (pPrimeCore_isPrimeComplement_of_isNilpotent (G := Hbar) (p := q))
      hDbarPrime
  have hLbarCent : Lbar ≤ centralizerWithin Lbar Dbar := by
    intro x hx
    refine ⟨hx, ?_⟩
    intro d hd
    exact Subgroup.mem_centralizer_iff.mp
      (pCore_le_centralizer_pPrimeCore q (hLbarCore hx)) d (hDbarCore hd)

  have hNHq : IsPGroup q NH := hLHq.to_le hNHLH
  have hcopNHD : Nat.Coprime (Nat.card NH) (Nat.card DH) := by
    obtain ⟨n, hn⟩ := hNHq.exists_card_eq
    rw [hn]
    exact hDHprime.pow_left n
  letI : IsSolvable HJ := isSolvable_subgroup_of_isSolvable HJ
  letI : IsSolvable DH := isSolvable_subgroup_of_isSolvable DH
  have hcentLHDH : centralizerWithin LH DH ≤ NH := by
    intro x hx
    have hxQD : (((x : HJ) : J) : G) ∈ centralizerWithin Q D := by
      refine ⟨hLQ hx.1, ?_⟩
      intro d hd
      let dJ : J := ⟨d, hDJ hd⟩
      let dH : HJ := ⟨dJ, hDJHJ (show dJ ∈ DJ from hd)⟩
      have hxd := hx.2 dH (show dH ∈ DH from hd)
      have hxdG := congrArg (fun z : HJ ↦ ((z : J) : G)) hxd
      change d * (((x : HJ) : J) : G) =
        (((x : HJ) : J) : G) * d at hxdG
      exact hxdG
    exact hcentQDQi hxQD
  have hmapCent :=
    map_centralizerWithin_quotient_eq_of_coprime_of_solvable_right
      (N := NH) (Y := LH) (R := DH) hNHLH hcopNHD
  have hmapCentBot : (centralizerWithin LH DH).map qH = ⊥ := by
    apply (Subgroup.map_eq_bot_iff (centralizerWithin LH DH)).mpr
    change centralizerWithin LH DH ≤ (QuotientGroup.mk' NH).ker
    rw [QuotientGroup.ker_mk']
    exact hcentLHDH
  have hcentBar : centralizerWithin Lbar Dbar = ⊥ := by
    change centralizerWithin (LH.map qH) (DH.map qH) = ⊥
    rw [← hmapCent, hmapCentBot]
  have hLbarBot : Lbar = ⊥ := by
    apply le_antisymm ?_ bot_le
    rw [← hcentBar]
    exact hLbarCent
  have hLHNH : LH ≤ NH := by
    have hker := (Subgroup.map_eq_bot_iff LH).mp
      (show LH.map qH = ⊥ by simpa only [Lbar] using hLbarBot)
    change LH ≤ (QuotientGroup.mk' NH).ker at hker
    rw [QuotientGroup.ker_mk'] at hker
    exact hker
  have hLQi : L ≤ Qi := by
    intro x hx
    let xJ : J := ⟨x, hLJ hx⟩
    let xH : HJ := ⟨xJ, (show L ≤ H from le_sup_left) hx⟩
    have hxLH : xH ∈ LH := hx
    exact hLHNH hxLH
  exact (not_le_of_gt hQiL) hLQi

private theorem semidirect_quotient_commutative_15
    {N H K : Subgroup G}
    (hsd : IsInternalSemidirectProductIn N H K)
    (hH : IsMulCommutative H) :
    letI : (N.subgroupOf K).Normal := hsd.2.2.1
    IsMulCommutative (K ⧸ N.subgroupOf K) := by
  letI : (N.subgroupOf K).Normal := hsd.2.2.1
  let e := semidirectQuotientEquiv_15 hsd
  apply isMulCommutative_iff.mpr
  intro x y
  apply e.injective
  simpa only [map_mul] using
    (isMulCommutative_iff.mp hH (e x) (e y))

private theorem centralizerWithin_eq_bot_of_semiregular_actor_15
    {X : Type*} [Group X] {A B : Subgroup X}
    (hreg : IsSemiregularConjugation A B) (hB : B ≠ ⊥) :
    centralizerWithin A B = ⊥ := by
  letI : Nontrivial B := (Subgroup.nontrivial_iff_ne_bot B).mpr hB
  obtain ⟨bB, hbB1⟩ := exists_ne (1 : B)
  let b : X := bB
  have hbB : b ∈ B := bB.property
  have hb1 : b ≠ 1 := by
    intro hb
    apply hbB1
    apply Subtype.ext
    exact hb
  apply le_bot_iff.mp
  intro x hx
  let xA : A := ⟨x, hx.1⟩
  have hcomm : (bB : X) * x = x * (bB : X) :=
    Subgroup.mem_centralizer_iff.mp hx.2 b hbB
  have hfix : (bB : X) * x * (bB : X)⁻¹ = x := by
    rw [hcomm]
    simp
  have hxOne : xA = 1 := hreg bB hbB1 xA hfix
  simpa [xA] using congrArg Subtype.val hxOne

private theorem isMulCommutative_of_mulEquiv_15
    {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (hB : IsMulCommutative B) : IsMulCommutative A := by
  apply isMulCommutative_iff.mpr
  intro x y
  apply e.injective
  simpa only [map_mul] using
    (isMulCommutative_iff.mp hB (e x) (e y))

private theorem isMulCommutative_subgroup_of_le_15
    {Q : Type*} [Group Q] {A B : Subgroup Q}
    (hAB : A ≤ B) (hB : IsMulCommutative B) : IsMulCommutative A := by
  apply isMulCommutative_iff.mpr
  intro x y
  apply A.subtype_injective
  exact congrArg Subtype.val
    (isMulCommutative_iff.mp hB
      ⟨(x : Q), hAB x.property⟩ ⟨(y : Q), hAB y.property⟩)

private theorem derived_quotient_commutative_of_semidirect_15
    {N H K : Subgroup G}
    (hsd : IsInternalSemidirectProductIn N H K)
    (hHder : IsMulCommutative (_root_.commutator H)) :
    let D := derivedWithin K
    let S := N ⊓ D
    letI : (S.subgroupOf D).Normal :=
      normal_inf_subgroupOf_of_le_15 hsd.1 (derivedWithin_le_15 K)
        hsd.2.2.1
    IsMulCommutative (D ⧸ S.subgroupOf D) := by
  let D := derivedWithin K
  let S := N ⊓ D
  letI : (S.subgroupOf D).Normal :=
    normal_inf_subgroupOf_of_le_15 hsd.1 (derivedWithin_le_15 K)
      hsd.2.2.1
  let NK : Subgroup K := N.subgroupOf K
  letI : NK.Normal := by simpa only [NK] using hsd.2.2.1
  let Q := K ⧸ NK
  let q : K →* Q := QuotientGroup.mk' NK
  have hDK : D ≤ K := derivedWithin_le_15 K
  let i : D →* K := Subgroup.inclusion hDK
  let f : D →* Q := q.comp i
  have hker : f.ker = S.subgroupOf D := by
    ext x
    change q (i x) = 1 ↔ (x : G) ∈ N ∧ (x : G) ∈ D
    constructor
    · intro hx
      have hxi : i x ∈ NK :=
        (QuotientGroup.eq_one_iff (i x)).mp hx
      exact ⟨hxi, x.property⟩
    · rintro ⟨hxN, _⟩
      exact (QuotientGroup.eq_one_iff (i x)).mpr hxN
  have hqSurj : Function.Surjective q := QuotientGroup.mk'_surjective NK
  have hmapComm :
      (_root_.commutator K).map q = _root_.commutator Q := by
    rw [map_commutator_eq,
      MonoidHom.range_eq_top.mpr hqSurj]
    rfl
  have hrange : f.range ≤ _root_.commutator Q := by
    rintro y ⟨x, rfl⟩
    rcases x.property with ⟨z, hz, hzx⟩
    have hzmap : q z ∈ (_root_.commutator K).map q :=
      Subgroup.mem_map_of_mem q hz
    rw [hmapComm] at hzmap
    change q (i x) ∈ _root_.commutator Q
    rw [show i x = z by
      apply Subtype.ext
      exact hzx.symm]
    exact hzmap
  let e : Q ≃* H := semidirectQuotientEquiv_15 hsd
  have heSurj : Function.Surjective e.toMonoidHom := e.surjective
  have heMapComm :
      (_root_.commutator Q).map e.toMonoidHom =
        _root_.commutator H := by
    rw [map_commutator_eq,
      MonoidHom.range_eq_top.mpr heSurj]
    rfl
  have hMappedComm :
      IsMulCommutative
        ((_root_.commutator Q).map e.toMonoidHom) := by
    rw [heMapComm]
    exact hHder
  have hQder : IsMulCommutative (_root_.commutator Q) :=
    isMulCommutative_of_mulEquiv_15
      (e.subgroupMap (_root_.commutator Q)) hMappedComm
  have hRangeComm : IsMulCommutative f.range :=
    isMulCommutative_subgroup_of_le_15 hrange hQder
  have hQuotKer : IsMulCommutative (D ⧸ f.ker) :=
    isMulCommutative_of_mulEquiv_15
      (QuotientGroup.quotientKerEquivRange f) hRangeComm
  exact isMulCommutative_of_mulEquiv_15
    (QuotientGroup.quotientMulEquivOfEq hker).symm hQuotKer

/-! ## Lemma 15.1 -/

/-- The five conclusions of `BGsection15.v: kappa_structure`.

The quotient in clause (a) is formed by intersecting `M_sigma` with the
derived group.  Under the maximality hypothesis this intersection is just
`M_sigma`, by `Msigma_der1`. -/
structure KappaStructure
    (M U K : Subgroup G) : Prop where
  /- (a) -/
  sigma_U_sdprod :
    IsInternalSemidirectProductIn (sigmaCore M) U
      (sigmaCore M ⊔ U)
  sigmaU_K_sdprod :
    IsInternalSemidirectProductIn (sigmaCore M ⊔ U) K M
  K_cyclic : IsCyclic K
  derived_mod_sigma_abelian :
    let D := derivedWithin M
    let S := sigmaCore M ⊓ D
    letI : (S.subgroupOf D).Normal :=
      normal_inf_subgroupOf_of_le_15 (sigmaCore_le M)
        (derivedWithin_le_15 M) (sigmaCore_normal M)
    IsMulCommutative (D ⧸ S.subgroupOf D)

  /- (b) -/
  derived_decomposition : K ≠ ⊥ →
    IsInternalSemidirectProductIn (sigmaCore M) U (derivedWithin M)
  U_abelian_of_K_ne_bot : K ≠ ⊥ → IsMulCommutative U

  /- (c) -/
  U_subgroup_control : ∀ {X : Subgroup G},
    X ≤ U → X ≠ ⊥ →
      centralizerWithin (sigmaCore M) X ≠ ⊥ →
      minSimple_max_groups_of (G := G)
          ((Subgroup.centralizer (X : Set G) : Subgroup G) : Set G) = {M} ∧
        IsCyclic X ∧
        IsPiNumber (tau2Primes M) (Nat.card X)

  /- (d) -/
  fixedPointGenerated_abelian :
    IsMulCommutative (sigmaFixedPointGenerated M U)

  /- (e) -/
  exponent_frobenius : U ≠ ⊥ →
    ∃ U₀ : Subgroup G, U₀ ≤ U ∧
      Monoid.exponent U₀ = Monoid.exponent U ∧
      IsInternalSemidirectProductIn (sigmaCore M) U₀
        (sigmaCore M ⊔ U₀) ∧
      IsFrobeniusDecomposition
        ((sigmaCore M).subgroupOf (sigmaCore M ⊔ U₀))
        (U₀.subgroupOf (sigmaCore M ⊔ U₀))

/-! ## Theorem 15.2 -/

/-- Clause (g)'s three descriptions of the Fitting subgroup. -/
structure FCoreCentralizerDescriptions
    (M K D : Subgroup G) : Prop where
  pcore_join_centralizer :
    let q := Nat.card (kappaCentralizer M K)
    let Q := pCoreWithin q M
    Q ⊔ centralizerWithin M Q = fittingWithin M
  factor_centralizer :
    let q := Nat.card (kappaCentralizer M K)
    let Q := pCoreWithin q M
    let Q₀ := centralizerWithin Q D
    factorCentralizerWithin M Q Q₀ = (fittingWithin M : Set G)
  partner_factor_centralizer :
    let Ms := sigmaCore M
    let Ks := kappaCentralizer M K
    let q := Nat.card Ks
    let Q := pCoreWithin q M
    let Q₀ := centralizerWithin Q D
    factorCentralizerWithin Ms Ks Q₀ =
      (fittingWithin M : Set G)

/-- The conclusions of Theorem 15.2 for fixed `K` and `D` in the
non-nilpotent branch. -/
structure FCoreNonNilpotentStructure
    (M K D : Subgroup G) : Prop where
  /- (a) -/
  typeP1 : M ∈ typeP1MaximalSubgroups (G := G)
  sigma_K_sdprod :
    IsInternalSemidirectProductIn (sigmaCore M) K M
  sigma_eq_derived : sigmaCore M = derivedWithin M

  /- (b) -/
  card_K_prime : Nat.Prime (Nat.card K)
  card_partner_prime : Nat.Prime (Nat.card (kappaCentralizer M K))
  partner_prime_in_Fcore :
    Nat.card (kappaCentralizer M K) ∈
      primeSupport (Nat.card (Fitting_core M))
  partner_prime_beta :
    Nat.card (kappaCentralizer M K) ∈ betaPrimes M

  /- (c), (d), (e) -/
  pcore_sylow :
    let q := Nat.card (kappaCentralizer M K)
    IsSylowSubgroupOf q (pCoreWithin q M) M
  D_nilpotent : Group.IsNilpotent D
  Q0_normal_M :
    let q := Nat.card (kappaCentralizer M K)
    let Q := pCoreWithin q M
    ((centralizerWithin Q D).subgroupOf M).Normal
  Q0_normal_Q :
    let q := Nat.card (kappaCentralizer M K)
    let Q := pCoreWithin q M
    ((centralizerWithin Q D).subgroupOf Q).Normal

  /- (f) -/
  quotient_minimal_normal :
    let q := Nat.card (kappaCentralizer M K)
    let Q := pCoreWithin q M
    IsMinimalNormalFactor (centralizerWithin Q D) Q M
  quotient_elementary_abelian :
    let q := Nat.card (kappaCentralizer M K)
    let Q := pCoreWithin q M
    let Q₀ := centralizerWithin Q D
    letI : (Q₀.subgroupOf Q).Normal := by
      exact Q0_normal_Q
    IsElementaryAbelianGroup q (Q ⧸ Q₀.subgroupOf Q)
  quotient_card :
    let p := Nat.card K
    let q := Nat.card (kappaCentralizer M K)
    let Q := pCoreWithin q M
    let Q₀ := centralizerWithin Q D
    letI : (Q₀.subgroupOf Q).Normal := by
      exact Q0_normal_Q
    Nat.card (Q ⧸ Q₀.subgroupOf Q) = q ^ p

  /- (g) -/
  sigma_derived_eq_second :
    derivedWithin (sigmaCore M) = secondDerivedWithin M
  secondDerived_le_fitting : secondDerivedWithin M ≤ fittingWithin M
  fitting_descriptions : FCoreCentralizerDescriptions M K D
  fitting_lt_sigma : fittingWithin M < sigmaCore M

private theorem FCoreNonNilpotentStructure.conjugate_complement_back
    {M K D₁ D : Subgroup G}
    (h : FCoreNonNilpotentStructure M K D₁)
    (x : G) (hxM : x ∈ M)
    (hD : D = D₁.map (MulAut.conj x).toMonoidHom) :
    FCoreNonNilpotentStructure M K D := by
  classical
  let q := Nat.card (kappaCentralizer M K)
  let Q := pCoreWithin q M
  let e : G ≃* G := MulAut.conj x
  have hQleM : Q ≤ M := Subgroup.map_subtype_le _
  have hQnormal : (Q.subgroupOf M).Normal := by
    simpa [q, Q] using pCoreWithin_normal_15 q M
  have hQmap : Q.map e.toMonoidHom = Q := by
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (((Subgroup.normal_subgroupOf_iff_le_normalizer hQleM).mp hQnormal)
        hxM)
  have hQ₀leM : centralizerWithin Q D₁ ≤ M :=
    inf_le_left.trans hQleM
  have hQ₀normalM : ((centralizerWithin Q D₁).subgroupOf M).Normal := by
    simpa [q, Q] using h.Q0_normal_M
  have hQ₀map :
      (centralizerWithin Q D₁).map e.toMonoidHom =
        centralizerWithin Q D₁ := by
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (((Subgroup.normal_subgroupOf_iff_le_normalizer hQ₀leM).mp
        hQ₀normalM) hxM)
  have hQ₀eq :
      centralizerWithin Q D = centralizerWithin Q D₁ := by
    have hmap := centralizerWithin_map_mulEquiv_15 Q D₁ e
    rw [hQ₀map, hQmap, ← hD] at hmap
    exact hmap.symm
  have hDnil : Group.IsNilpotent D := by
    letI : Group.IsNilpotent D₁ := h.D_nilpotent
    rw [hD]
    exact Group.nilpotent_of_mulEquiv (e.subgroupMap D₁)
  let Q₀ := centralizerWithin Q D
  let Q₁ := centralizerWithin Q D₁
  have hQ₀normalQ : (Q₀.subgroupOf Q).Normal := by
    change ((centralizerWithin Q D).subgroupOf Q).Normal
    rw [hQ₀eq]
    simpa [q, Q] using h.Q0_normal_Q
  have hQ₁normalQ : (Q₁.subgroupOf Q).Normal := by
    simpa [q, Q, Q₁] using h.Q0_normal_Q
  letI : (Q₀.subgroupOf Q).Normal := hQ₀normalQ
  letI : (Q₁.subgroupOf Q).Normal := hQ₁normalQ
  have hQsubEq : Q₀.subgroupOf Q = Q₁.subgroupOf Q := by
    exact congrArg (fun S : Subgroup G ↦ S.subgroupOf Q) hQ₀eq
  let eQuot : (Q ⧸ Q₀.subgroupOf Q) ≃* (Q ⧸ Q₁.subgroupOf Q) :=
    QuotientGroup.quotientMulEquivOfEq hQsubEq
  have hElem₁ : IsElementaryAbelianGroup q (Q ⧸ Q₁.subgroupOf Q) := by
    simpa [q, Q, Q₁] using h.quotient_elementary_abelian
  have hElem₀ : IsElementaryAbelianGroup q (Q ⧸ Q₀.subgroupOf Q) :=
    elementaryAbelian_of_mulEquiv_15 hElem₁ eQuot.symm
  have hCard₁ : Nat.card (Q ⧸ Q₁.subgroupOf Q) = q ^ Nat.card K := by
    simpa [q, Q, Q₁] using h.quotient_card
  have hCard₀ : Nat.card (Q ⧸ Q₀.subgroupOf Q) = q ^ Nat.card K :=
    (Nat.card_congr eQuot.toEquiv).trans hCard₁
  exact
    { typeP1 := h.typeP1
      sigma_K_sdprod := h.sigma_K_sdprod
      sigma_eq_derived := h.sigma_eq_derived
      card_K_prime := h.card_K_prime
      card_partner_prime := h.card_partner_prime
      partner_prime_in_Fcore := h.partner_prime_in_Fcore
      partner_prime_beta := h.partner_prime_beta
      pcore_sylow := h.pcore_sylow
      D_nilpotent := hDnil
      Q0_normal_M := by
        change ((centralizerWithin Q D).subgroupOf M).Normal
        rw [hQ₀eq]
        exact hQ₀normalM
      Q0_normal_Q := by
        simpa [q, Q, Q₀] using hQ₀normalQ
      quotient_minimal_normal := by
        change IsMinimalNormalFactor (centralizerWithin Q D) Q M
        rw [hQ₀eq]
        simpa [q, Q] using h.quotient_minimal_normal
      quotient_elementary_abelian := by
        simpa [q, Q, Q₀] using hElem₀
      quotient_card := by
        simpa [q, Q, Q₀] using hCard₀
      sigma_derived_eq_second := h.sigma_derived_eq_second
      secondDerived_le_fitting := h.secondDerived_le_fitting
      fitting_descriptions :=
        { pcore_join_centralizer :=
            h.fitting_descriptions.pcore_join_centralizer
          factor_centralizer := by
            change factorCentralizerWithin M Q
                (centralizerWithin Q D) = (fittingWithin M : Set G)
            rw [hQ₀eq]
            simpa [q, Q] using
              h.fitting_descriptions.factor_centralizer
          partner_factor_centralizer := by
            change factorCentralizerWithin (sigmaCore M)
                (kappaCentralizer M K) (centralizerWithin Q D) =
              (fittingWithin M : Set G)
            rw [hQ₀eq]
            simpa [q, Q] using
              h.fitting_descriptions.partner_factor_centralizer }
      fitting_lt_sigma := h.fitting_lt_sigma }

/-- The complete proposition-valued form of Theorem 15.2. -/
structure FCoreStructure (M : Subgroup G) : Prop where
  Fcore_ne_bot : Fitting_core M ≠ ⊥
  Fcore_le_sigma : Fitting_core M ≤ sigmaCore M
  sigma_le_derived : sigmaCore M ≤ derivedWithin M
  derived_lt : derivedWithin M < M
  nonnilpotent : ∀ {K D : Subgroup G},
    K ≤ M →
    IsHall (kappaPrimes M) (K.subgroupOf M) →
    Fitting_core M ≠ sigmaCore M →
    D ≤ sigmaCore M →
    IsHall ({Nat.card (kappaCentralizer M K)} : Set ℕ)ᶜ
      (D.subgroupOf (sigmaCore M)) →
    FCoreNonNilpotentStructure M K D

/-! ## Corollary 15.5 and Corollary 15.6 records -/

/-- The conclusions of `BGsection15.v: Fitting_structure`. -/
structure FittingStructure (M : Subgroup G) : Prop where
  /- (a) -/
  sigmaPrimeCore_cyclic : IsCyclic (fittingSigmaPrimeCore M)
  sigmaPrimeCore_tau2 :
    IsPiNumber (tau2Primes M) (Nat.card (fittingSigmaPrimeCore M))

  /- (b) -/
  secondDerived_le_fitting : secondDerivedWithin M ≤ fittingWithin M
  Fcore_centralizer_commute :
    ∀ x ∈ Fitting_core M, ∀ y ∈ centralizerWithin M (Fitting_core M),
      Commute x y
  Fcore_join_centralizer :
    Fitting_core M ⊔ centralizerWithin M (Fitting_core M) =
      fittingWithin M
  sigmaFitting_times_sigmaPrimeCore :
    IsInternalDirectProductIn
      (fittingWithin (sigmaCore M)) (fittingSigmaPrimeCore M)
      (fittingWithin M)

  /- (c) -/
  Fcore_le_derived : Fitting_core M ≤ derivedWithin M
  Fcore_normal_derived :
    ((Fitting_core M).subgroupOf (derivedWithin M)).Normal
  derived_mod_Fcore_nilpotent :
    letI : ((Fitting_core M).subgroupOf (derivedWithin M)).Normal :=
      Fcore_normal_derived
    Group.IsNilpotent
      (derivedWithin M ⧸
        (Fitting_core M).subgroupOf (derivedWithin M))

  /- (d) -/
  typeP_fitting_le_derived :
    M ∈ typePMaximalSubgroups (G := G) →
      fittingWithin M ≤ derivedWithin M

/-- The five conclusions of `BGsection15.v: Ptype_cyclics`. -/
structure PTypeCyclics (M K : Subgroup G) : Prop where
  partner_ne_bot : kappaCentralizer M K ≠ ⊥
  partner_cyclic : IsCyclic (kappaCentralizer M K)
  partner_le_secondDerived :
    kappaCentralizer M K ≤ secondDerivedWithin M
  partner_le_Fcore : kappaCentralizer M K ≤ Fitting_core M
  Fcore_not_cyclic : ¬ IsCyclic (Fitting_core M)

/-! ## The regularity input for Lemma 15.1 -/

/-- A rank-one subgroup inside the cyclic subgroup generated by a nonidentity
element.  This is the ambient-group form of the rank-one choice made in the
regularity paragraph of `BGsection15.v: kappa_structure`. -/
private theorem exists_rankOneLineIn_zpowers_of_mem_15_1
    {K : Subgroup G} {x : G} (hxK : x ∈ K) (hx1 : x ≠ 1) :
    ∃ p : ℕ, p.Prime ∧ ∃ X : Subgroup G,
      RankOneLineIn p K X ∧ X ≤ Subgroup.zpowers x := by
  let C : Subgroup G := Subgroup.zpowers x
  have hCne : C ≠ ⊥ := by
    intro hbot
    have hxbot : x ∈ (⊥ : Subgroup G) := by
      rw [← hbot]
      exact Subgroup.mem_zpowers x
    exact hx1 (by simpa using hxbot)
  obtain ⟨p, hp, hpC⟩ := Nat.exists_prime_and_dvd
    (C.one_lt_card_iff_ne_bot.mpr hCne).ne'
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨y, hyOrder⟩ :=
    exists_prime_orderOf_dvd_card' (G := C) p hpC
  let X : Subgroup G := Subgroup.zpowers (y : G)
  have hXC : X ≤ C := Subgroup.zpowers_le.mpr y.property
  have hXK : X ≤ K :=
    hXC.trans (Subgroup.zpowers_le.mpr hxK)
  have hcardX : Nat.card X = p := by
    simpa [X, Nat.card_zpowers] using hyOrder
  exact ⟨p, hp, X,
    ⟨hXK, isElementaryAbelianOfRank_one_of_card_eq_prime hcardX⟩,
    hXC⟩

/-! ## Proofs -/

/-- `BGsection15.v: kappa_structure`, Bender--Glauberman Lemma 15.1. -/
theorem kappa_structure
    {M U K : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hcompl : KappaComplement M U K) :
    KappaStructure M U K := by
  classical
  let Ms := sigmaCore M
  have hctx := kappa_compl_context hM hcompl
  have hMsnormal : (Ms.subgroupOf M).Normal := by
    simpa [Ms] using sigmaCore_normal M
  have hMsU :
      IsInternalSemidirectProductIn Ms U (Ms ⊔ U) := by
    simpa only [Ms] using
      semidirect_restrict_right_15 hctx.sigma_UK_sdprod le_sup_left
  have hMsUK :
      IsInternalSemidirectProductIn (Ms ⊔ U) K M := by
    exact semidirect_reassociate_15 hctx.sigma_UK_sdprod hctx.U_K_sdprod
  have hquotAbelian :
      let D := derivedWithin M
      let S := sigmaCore M ⊓ D
      letI : (S.subgroupOf D).Normal :=
        normal_inf_subgroupOf_of_le_15 (sigmaCore_le M)
          (derivedWithin_le_15 M) (sigmaCore_normal M)
      IsMulCommutative (D ⧸ S.subgroupOf D) := by
    exact derived_quotient_commutative_of_semidirect_15
      hctx.sigma_UK_sdprod
      (der_mmax_compl_abelian hM hctx.U_sup_K_le_M
        hctx.hall_sigma_complement)

  have hpartC : ∀ {X : Subgroup G},
      X ≤ U → X ≠ ⊥ → centralizerWithin Ms X ≠ ⊥ →
        minSimple_max_groups_of (G := G)
            ((Subgroup.centralizer (X : Set G) : Subgroup G) : Set G) = {M} ∧
          IsCyclic X ∧ IsPiNumber (tau2Primes M) (Nat.card X) := by
    intro X hXU hXne hCXne
    let C := centralizerWithin Ms X
    haveI : Nontrivial C := C.nontrivial_iff_ne_bot.mpr hCXne
    obtain ⟨xC, hxCne⟩ := exists_ne (1 : C)
    let x : G := xC
    have hxCX : x ∈ centralizerWithin Ms X := xC.property
    have hxne : x ≠ 1 := by
      intro hx
      apply hxCne
      apply Subtype.ext
      exact hx
    have hxMs : x ∈ Ms := hxCX.1
    have hXE : X ≤ U ⊔ K := hXU.trans le_sup_left
    have hpi (y : G) (hyX : y ∈ X) (hyne : y ≠ 1) :
        (IsPiNumber (kappaPrimes M) (orderOf y) ∧
            elementCentralizer x ≤ M) ∨
          (IsPiNumber (tau2Primes M) (orderOf y) ∧
            sigmaLength y = 1 ∧
            minSimple_max_groups_of (G := G)
              ((elementCentralizer y : Subgroup G) : Set G) = {M}) := by
      apply pi_of_cent_sigma hM hxMs hxne
      · refine ⟨hctx.U_sup_K_le_M
            ((le_sup_left : U ≤ U ⊔ K) (hXU hyX)), ?_⟩
        have hyx : Commute y x := hxCX.2 y hyX
        intro z hz
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
        exact (hyx.symm.zpow_left n).eq
      · exact hyne
      · have hUcard :
            IsPiNumber (sigmaKappaPrimes M)ᶜ (Nat.card U) := by
            rw [← MathlibSupport.natCard_subgroupOf_eq hcompl.U_le_M]
            exact hcompl.hall_U.isPiNumber_card
        have hUcardSigma :
            IsPiNumber (sigmaPrimes M)ᶜ (Nat.card U) :=
          hUcard.mono (by
            intro r hr hrSigma
            exact hr (Or.inl hrSigma))
        exact isPiNumber_orderOf_of_mem_15
          (hUcardSigma.of_dvd (Subgroup.card_dvd_of_le hXU)) hyX
    have hXtau2 : IsPiNumber (tau2Primes M) (Nat.card X) := by
      apply Submission.OddOrder.MathlibSupport.isPiNumber_natCard_of_orderOf
      intro y hyX hyne
      rcases hpi y hyX hyne with hkappa | htau
      · have hyU : y ∈ U := hXU hyX
        have hUcard :
            IsPiNumber (sigmaKappaPrimes M)ᶜ (Nat.card U) := by
          rw [← MathlibSupport.natCard_subgroupOf_eq hcompl.U_le_M]
          exact hcompl.hall_U.isPiNumber_card
        have hySigmaKappa' :
            IsPiNumber (sigmaKappaPrimes M)ᶜ (orderOf y) :=
          isPiNumber_orderOf_of_mem_15 hUcard hyU
        have hyUKappa' :
            IsPiNumber (kappaPrimes M)ᶜ (orderOf y) :=
          hySigmaKappa'.mono (by
            intro r hr hrKappa
            exact hr (Or.inr hrKappa))
        have hyOrderOne : orderOf y = 1 :=
          Nat.eq_one_of_dvd_coprimes
            (hkappa.1.coprime_compl hyUKappa') dvd_rfl dvd_rfl
        exact (hyne (orderOf_eq_one_iff.mp hyOrderOne)).elim
      · exact htau.1
    have hXcyclic : IsCyclic X := by
      obtain ⟨E₂, hXE₂, hE₂E, hHallE₂⟩ :=
        Submission.OddOrder.MathlibSupport.exists_ambient_isHall_ge_of_isSolvable
          hXE
          (sigma_compl_sol hctx.U_sup_K_le_M
            hctx.hall_sigma_complement)
          (tau2Primes M) hXtau2
      have hE₂abelian := tau2_compl_abelian hM
        hctx.U_sup_K_le_M hctx.hall_sigma_complement hE₂E hHallE₂
      have hXcomm : IsMulCommutative X :=
        isMulCommutative_of_le_15 hXE₂ hE₂abelian
      have hXz : IsZGroup X := by
        rw [isZGroup_iff]
        intro p hp P
        letI : Fact p.Prime := ⟨hp⟩
        let PG : Subgroup G := (P : Subgroup X).map X.subtype
        have hcardPG : Nat.card PG = Nat.card P := by
          exact Subgroup.card_map_of_injective X.subtype_injective
        have hPodd : Odd (Nat.card P) := by
          rw [← hcardPG]
          exact mFT_odd PG
        apply
          (odd_pgroup_isCyclic_iff_no_elementaryAbelian_rank_two
            P.isPGroup' hPodd).2
        rintro ⟨E, hE⟩
        let j : P →* G :=
          X.subtype.comp (P : Subgroup X).subtype
        let A : Subgroup G := E.map j
        have hj : Function.Injective j :=
          X.subtype_injective.comp
            (P : Subgroup X).subtype_injective
        have hA : IsElementaryAbelianOfRank p 2 A :=
          hE.map_of_injective j hj
        have hAX : A ≤ X := by
          rintro _ ⟨e, _he, rfl⟩
          exact (e : X).property
        have hpA : p ∣ Nat.card A := by
          rw [hA.card_eq]
          exact dvd_pow_self p (by omega)
        have hpTau : p ∈ tau2Primes M :=
          hXtau2 hp (hpA.trans (Subgroup.card_dvd_of_le hAX))
        have hAM : A ≤ M :=
          hAX.trans (hXU.trans hcompl.U_le_M)
        have hCA : centralizerWithin Ms A = ⊥ := by
          simpa only [Ms] using
            (tau2_context hM hpTau hAM hA).centralizerWithin_eq_bot
        apply hCXne
        apply le_antisymm
        · exact (centralizerWithin_antitone_right hAX).trans_eq hCA
        · exact bot_le
      letI : IsMulCommutative X := hXcomm
      letI : IsZGroup X := hXz
      letI : Group.IsNilpotent X := inferInstance
      infer_instance
    obtain ⟨y, hygen⟩ :=
      (Subgroup.isCyclic_iff_exists_zpowers_eq_top X).mp hXcyclic
    have hyX : y ∈ X := by
      rw [← hygen]
      exact Subgroup.mem_zpowers y
    have hyne : y ≠ 1 := by
      intro hy
      apply hXne
      rw [← hygen, hy]
      simp
    rcases hpi y hyX hyne with hkappa | htau
    · have hyTau2Compl :
          IsPiNumber (tau2Primes M)ᶜ (orderOf y) :=
        hkappa.1.mono (by
          intro r hrKappa hrTau2
          rcases kappa_tau13 hrKappa with hrTau1 | hrTau3
          · exact (tau2'1 M hrTau1) hrTau2
          · exact (tau3'2 M hrTau2) hrTau3)
      have hcop : Nat.Coprime (Nat.card X) (orderOf y) :=
        hXtau2.coprime_compl hyTau2Compl
      have hyOrder : orderOf y = Nat.card X := by
        rw [← Nat.card_zpowers, hygen]
      have hXcard : Nat.card X = 1 :=
        Nat.eq_one_of_dvd_coprimes hcop dvd_rfl (by rw [hyOrder])
      exact (hXne (Subgroup.card_eq_one.mp hXcard)).elim
    · exact ⟨by simpa [elementCentralizer, hygen] using htau.2.2,
        hXcyclic, hXtau2⟩

  have hUpi :
      IsPiNumber (sigmaKappaPrimes M)ᶜ (Nat.card U) := by
    rw [← MathlibSupport.natCard_subgroupOf_eq hcompl.U_le_M]
    exact hcompl.hall_U.isPiNumber_card
  have hKpi :
      IsPiNumber (sigmaKappaPrimes M) (Nat.card K) := by
    rw [← MathlibSupport.natCard_subgroupOf_eq hcompl.K_le_M]
    exact hcompl.hall_K.isPiNumber_card.mono
      (by intro r hr; exact Or.inr hr)
  have hUKcoprime : Nat.Coprime (Nat.card U) (Nat.card K) :=
    (hKpi.coprime_compl hUpi).symm
  have hHallUInComplement :
      IsHall (primeSupport (Nat.card U))
        (U.subgroupOf (U ⊔ K)) := by
    rw [← MathlibSupport.natCard_subgroupOf_eq le_sup_left]
    apply isHall_primeSupport
    rw [hctx.U_K_sdprod.2.2.2.symm.index_eq_card,
      MathlibSupport.natCard_subgroupOf_eq le_sup_left,
      MathlibSupport.natCard_subgroupOf_eq le_sup_right]
    exact hUKcoprime
  have hregular : FTTypeFRegularity M U := by
    intro x hxU hx1 hxTau13
    by_contra hcentral
    obtain ⟨p, hp, X, hX, hXcycle⟩ :=
      exists_rankOneLineIn_zpowers_of_mem_15_1 hxU hx1
    have hpX : p ∣ Nat.card X := by
      rw [hX.2.card_eq, pow_one]
    have hpOrder : p ∣ orderOf x := by
      rw [← Nat.card_zpowers]
      exact hpX.trans (Subgroup.card_dvd_of_le hXcycle)
    have hpTau13 : p ∈ tau13Primes M := by
      simpa [tau13Primes] using hxTau13 hp hpOrder
    have hXcentral :
        centralizerWithin (sigmaCore M) X ≠ ⊥ := by
      intro hXbot
      apply hcentral
      apply le_antisymm
      · exact (centralizerWithin_antitone_right hXcycle).trans_eq hXbot
      · exact bot_le
    have hpKappa : p ∈ kappaPrimes M := by
      exact ⟨hpTau13, X,
        ⟨hX.1.trans hcompl.U_le_M, hX.2⟩, hXcentral⟩
    have hpComplement : p ∈ (sigmaKappaPrimes M)ᶜ :=
      isPiNumber_orderOf_of_mem_15 hUpi hxU hp hpOrder
    exact hpComplement (Or.inr hpKappa)
  have htypeF := FTtypeF_complement
    hM hctx.U_sup_K_le_M hctx.hall_sigma_complement
    le_sup_left hHallUInComplement hctx.U_K_sdprod.2.2.1
    hregular
  have hKcyclic : IsCyclic K := by
    by_cases hK : K = ⊥
    · subst K
      infer_instance
    · have hP : M ∈ typePMaximalSubgroups (G := G) := by
        exact ⟨hM, fun hF ↦ hK ((trivg_kappa hM hcompl.K_le_M
          hcompl.hall_K).2 hF)⟩
      obtain ⟨Mstar, hemb⟩ :=
        Ptype_embedding hP hcompl.K_le_M hcompl.hall_K
      exact isCyclic_of_le_15 le_sup_left
        hemb.cyclicStructure.cyclic_join
  have hderived : K ≠ ⊥ →
      IsInternalSemidirectProductIn Ms U (derivedWithin M) := by
    intro hK
    have hKnormU : K ≤ Subgroup.normalizer (U : Set G) :=
      hctx.U_K_sdprod.2.1.trans
        ((Subgroup.normal_subgroupOf_iff_le_normalizer
          hctx.U_K_sdprod.1).mp hctx.U_K_sdprod.2.2.1)
    have hcentUK : centralizerWithin U K = ⊥ :=
      centralizerWithin_eq_bot_of_semiregular_actor_15
        hctx.U_K_semiregular hK
    have hUsol : IsSolvable U :=
      isSolvable_of_le_15 (mmax_sol hM) hcompl.U_le_M
    have hUleComm : U ≤ ⁅K, U⁆ := by
      letI : IsSolvable U := hUsol
      have hdecomp :=
        le_commutator_sup_centralizerWithin_of_coprime
          hKnormU hUKcoprime
      simpa only [hcentUK, sup_bot_eq] using hdecomp
    have hUleD : U ≤ derivedWithin M :=
      hUleComm.trans
        ((Subgroup.commutator_mono hcompl.K_le_M hcompl.U_le_M).trans
          M.map_subtype_commutator.ge)
    have hMsD : Ms ≤ derivedWithin M := by
      change sigmaCore M ≤ (_root_.commutator M).map M.subtype
      exact Msigma_der1 hM
    have hAD : Ms ⊔ U ≤ derivedWithin M :=
      sup_le hMsD hUleD
    letI : ((Ms ⊔ U).subgroupOf M).Normal := hMsUK.2.2.1
    letI : IsCyclic K := hKcyclic
    have hKcomm : IsMulCommutative K := inferInstance
    have hquotK :
        IsMulCommutative (M ⧸ (Ms ⊔ U).subgroupOf M) :=
      semidirect_quotient_commutative_15 hMsUK hKcomm
    have hcommLe :
        _root_.commutator M ≤ (Ms ⊔ U).subgroupOf M :=
      Subgroup.Normal.quotient_commutative_iff_commutator_le.mp hquotK
    have hDA : derivedWithin M ≤ Ms ⊔ U := by
      calc
        derivedWithin M = (_root_.commutator M).map M.subtype := rfl
        _ ≤ ((Ms ⊔ U).subgroupOf M).map M.subtype :=
          Subgroup.map_mono hcommLe
        _ = Ms ⊔ U :=
          Subgroup.map_subgroupOf_eq_of_le hMsUK.1
    have hEq : Ms ⊔ U = derivedWithin M := le_antisymm hAD hDA
    simpa only [hEq] using hMsU
  have hUcomm : K ≠ ⊥ → IsMulCommutative U :=
    hctx.U_abelian_of_K_ne_bot
  have hfixedLe :
      sigmaFixedPointGenerated M U ≤
        htypeF.fixedPoint.fixedPointSubgroup := by
    rw [sigmaFixedPointGenerated]
    rw [Subgroup.closure_le]
    intro y hy
    rcases hy with ⟨x, hxMs, hxne, hyCent⟩
    exact htypeF.fixedPoint.fixedPoint_control hxMs hxne hyCent
  have hfixed : IsMulCommutative (sigmaFixedPointGenerated M U) :=
    isMulCommutative_of_le_15 hfixedLe
      htypeF.fixedPoint.fixedPoint_abelian
  have hfrob : U ≠ ⊥ →
      ∃ U₀ : Subgroup G, U₀ ≤ U ∧
        Monoid.exponent U₀ = Monoid.exponent U ∧
        IsInternalSemidirectProductIn Ms U₀ (Ms ⊔ U₀) ∧
        IsFrobeniusDecomposition
          (Ms.subgroupOf (Ms ⊔ U₀))
          (U₀.subgroupOf (Ms ⊔ U₀)) := by
    intro hU
    let hFrob := htypeF.frobenius hU
    exact ⟨hFrob.complement, hFrob.complement_le_U,
      hFrob.exponent_eq, hFrob.semidirect, hFrob.frobenius⟩
  exact
    { sigma_U_sdprod := hMsU
      sigmaU_K_sdprod := hMsUK
      K_cyclic := hKcyclic
      derived_mod_sigma_abelian := hquotAbelian
      derived_decomposition := hderived
      U_abelian_of_K_ne_bot := hUcomm
      U_subgroup_control := hpartC
      fixedPointGenerated_abelian := hfixed
      exponent_frobenius := hfrob }

/-- The fixed-`K,D` part of Theorem 15.2.  Isolating it mirrors the source's
`KDpart` local assertion and makes the final nontriviality argument short. -/
private theorem fcore_nonnilpotent_structure
    {M K D : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hKM : K ≤ M)
    (hHallK : IsHall (kappaPrimes M) (K.subgroupOf M))
    (hneF : Fitting_core M ≠ sigmaCore M)
    (hDsigma : D ≤ sigmaCore M)
    (hHallD :
      IsHall ({Nat.card (kappaCentralizer M K)} : Set ℕ)ᶜ
        (D.subgroupOf (sigmaCore M))) :
    FCoreNonNilpotentStructure M K D := by
  classical
  let Ms := sigmaCore M
  let Ks := kappaCentralizer M K
  let p := Nat.card K
  let q := Nat.card Ks
  let Q := pCoreWithin q M
  let Q₀ := centralizerWithin Q D

  have hsolM : IsSolvable M := mmax_sol hM
  have hMsM : Ms ≤ M := sigmaCore_le M
  have hsolMs : IsSolvable Ms :=
    isSolvable_of_injective (Subgroup.inclusion hMsM)
      (Subgroup.inclusion_injective hMsM)
  have hnotNilMs : ¬ Group.IsNilpotent Ms := by
    intro hnil
    exact hneF ((Fcore_eq_Msigma hM).2 hnil)

  /- The first paragraph of the source: a nonnilpotent sigma core puts `M`
  in type P1, and Lemma 15.1 collapses the `U` factor. -/
  have hP1 : M ∈ typeP1MaximalSubgroups (G := G) := by
    by_cases hF : M ∈ typeFMaximalSubgroups (G := G)
    · exact (hnotNilMs (notP1type_Msigma_nil (Or.inl hF))).elim
    have hP : M ∈ typePMaximalSubgroups (G := G) := ⟨hM, hF⟩
    by_cases hP1 : M ∈ typeP1MaximalSubgroups (G := G)
    · exact hP1
    exact (hnotNilMs
      (notP1type_Msigma_nil (Or.inr ⟨hP, hP1⟩))).elim
  have hP : M ∈ typePMaximalSubgroups (G := G) := hP1.1
  have hKne : K ≠ ⊥ := by
    intro hK
    exact hP.2 ((trivg_kappa hM hKM hHallK).1 hK)
  obtain ⟨U, hcompl⟩ := ex_kappa_compl hM hKM hHallK
  have hUbot : U = ⊥ := (trivg_kappa_compl hM hcompl).2 hP1
  have hkappa := kappa_structure hM hcompl
  have hSigmaK : IsInternalSemidirectProductIn Ms K M := by
    simpa [Ms, hUbot] using hkappa.sigmaU_K_sdprod
  have hSigmaDerived : Ms = derivedWithin M := by
    change sigmaCore M = derivedWithin M
    have hdecomp := hkappa.derived_decomposition hKne
    have htop := hdecomp.2.2.2.sup_eq_top
    have hMsTop :
        (sigmaCore M).subgroupOf (derivedWithin M) = ⊤ := by
      simpa [hUbot] using htop
    exact le_antisymm hdecomp.1
      (Subgroup.subgroupOf_eq_top.mp hMsTop)

  /- Proposition 14.2 and Theorem 14.7 give the prime partner. -/
  have hPstruct := Ptype_structure hP hKM hHallK
  obtain ⟨Mstar, hemb⟩ := Ptype_embedding hP hKM hHallK
  have hqPrime : Nat.Prime q := by
    rcases hemb.typeP2_prime with hM2 | hMstar2
    · exact (hM2.1.2 hP1).elim
    · simpa [q, Ks, kappaCentralizer, pTypePartner] using hMstar2.2
  letI : Fact q.Prime := ⟨hqPrime⟩
  have hKsne : Ks ≠ ⊥ := by
    simpa [Ks, kappaCentralizer, pTypeCentralizer] using
      hPstruct.Kstar_ne_bot

  have hMsnormal : (Ms.subgroupOf M).Normal := by
    simpa [Ms] using sigmaCore_normal M
  have hQnormalM : (Q.subgroupOf M).Normal := by
    simpa [Q] using pCoreWithin_normal_15 q M
  have hQleM : Q ≤ M := by
    exact Subgroup.map_subtype_le _
  have hQq : IsPGroup q Q := by
    dsimp [Q, pCoreWithin]
    exact pCore_isPGroup.map M.subtype
  have hqSigma : q ∈ sigmaPrimes M := by
    apply hemb.Kstar_hall_sigma.isPiNumber_card hqPrime
    rw [MathlibSupport.natCard_subgroupOf_eq hemb.Kstar_le_Mstar]
    simp [q, Ks, kappaCentralizer, pTypePartner]
  have hQleMs : Q ≤ Ms := by
    dsimp only [Ms]
    rw [sigmaCore]
    unfold primeSetCore
    exact le_sSup
      ⟨hQleM, hQnormalM, hQq.isPiNumber_natCard hqSigma⟩

  /- A prime-order subgroup of `K` centralizes exactly `Kstar`.  The
  Frobenius-kernel argument applied modulo `Q` then makes `Ms/Q`
  nilpotent, so `Q` is a Sylow subgroup first of `Ms` and then of `M`. -/
  letI : Nontrivial K := (Subgroup.nontrivial_iff_ne_bot K).mpr hKne
  obtain ⟨xK, hxKne⟩ := exists_ne (1 : K)
  have hxG : (xK : G) ≠ 1 := by
    intro hx
    apply hxKne
    apply Subtype.ext
    exact hx
  obtain ⟨r, hr, K₁, hK₁, _hK₁zx⟩ :=
    exists_rankOneLineIn_zpowers_of_mem_15_1 xK.property hxG
  have hK₁K : K₁ ≤ K := hK₁.1
  have hK₁card : Nat.card K₁ = r := by
    simpa using hK₁.2.card_eq
  have hK₁prime : Nat.Prime (Nat.card K₁) := by
    simpa [hK₁card] using hr
  have hK₁ne : K₁ ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hK₁card
    exact hr.ne_one hK₁card.symm
  have hcentK₁ : centralizerWithin Ms K₁ = Ks := by
    simpa [Ms, Ks, kappaCentralizer] using
      hPstruct.sigma_K_prime.centralizer_eq hK₁K hK₁ne
  /- The source proves `Kstar ≤ Q` before invoking Sylow theory.  The
  mixed-commutator identity is Lemma 6.3(a), transported through the subtype
  embedding of `M`; the one Section 3 seam is the internal-product wrapper. -/
  have hcopMsMK :
      Nat.Coprime (Nat.card (Ms.subgroupOf M))
        (Nat.card (K.subgroupOf M)) :=
    (Msigma_Hall hM).isPiNumber_card.coprime_compl
      (hHallK.isPiNumber_card.mono (kappa_sigma' M))
  have hcopMsK : Nat.Coprime (Nat.card Ms) (Nat.card K) := by
    simpa only [MathlibSupport.natCard_subgroupOf_eq hMsM,
      MathlibSupport.natCard_subgroupOf_eq hKM] using hcopMsMK
  have hsemiprimeMsK : IsSemiprimeAction Ms K := by
    intro X hXK hXne
    simpa only [Ms] using
      hPstruct.sigma_K_prime.centralizer_eq hXK hXne
  have hcommMsK : ⁅Ms, K⁆ = Ms := by
    let MsM : Subgroup M := Ms.subgroupOf M
    let KM : Subgroup M := K.subgroupOf M
    letI : IsSolvable M := hsolM
    letI : IsSolvable MsM :=
      isSolvable_subgroup_of_isSolvable MsM
    have hKMnormMsM : KM ≤ Subgroup.normalizer (MsM : Set M) := by
      rw [Subgroup.normalizer_eq_top_iff.mpr hSigmaK.2.2.1]
      exact le_top
    have hMsMderived : MsM ≤ _root_.commutator M := by
      change Ms.subgroupOf M ≤ _root_.commutator M
      rw [hSigmaDerived]
      change (((_root_.commutator M).map M.subtype).comap M.subtype) ≤
        _root_.commutator M
      rw [Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
    have hcommInside : ⁅MsM, KM⁆ = MsM :=
      _root_.Submission.OddOrder.BG.Section06.commutator_eq_left_of_isComplement_of_solvable_of_le_commutator
        hSigmaK.2.2.2 hKMnormMsM hMsMderived
    calc
      ⁅Ms, K⁆ = ⁅MsM, KM⁆.map M.subtype := by
        rw [Subgroup.map_commutator,
          Subgroup.map_subgroupOf_eq_of_le hMsM,
          Subgroup.map_subgroupOf_eq_of_le hKM]
      _ = MsM.map M.subtype := by rw [hcommInside]
      _ = Ms := Subgroup.map_subgroupOf_eq_of_le hMsM
  have hFMsFM : fittingWithin Ms ≤ fittingWithin M := by
    have hFMsM : fittingWithin Ms ≤ M :=
      (fittingWithin_le Ms).trans hMsM
    have hMnormMs : M ≤ Subgroup.normalizer (Ms : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hMsM).mp hMsnormal
    have hMnormFMs :
        M ≤ Subgroup.normalizer (fittingWithin Ms : Set G) :=
      le_normalizer_fittingWithin_of_le_normalizer hMnormMs
    have hFMsNormalM : ((fittingWithin Ms).subgroupOf M).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hFMsM).mpr hMnormFMs
    let FMsM : Subgroup M := (fittingWithin Ms).subgroupOf M
    let eFMs : FMsM ≃* fittingWithin Ms :=
      Subgroup.subgroupOfEquivOfLe hFMsM
    letI : FMsM.Normal := hFMsNormalM
    letI : Group.IsNilpotent FMsM :=
      Group.nilpotent_of_mulEquiv eFMs.symm
    have hFMsCore : FMsM ≤ fittingCore M :=
      nilpotent_normal_le_fittingCore (by infer_instance) (by infer_instance)
    change fittingWithin Ms ≤ (fittingCore M).map M.subtype
    rw [← Subgroup.map_subgroupOf_eq_of_le hFMsM]
    exact Subgroup.map_mono hFMsCore
  have hKsQ : Ks ≤ Q := by
    have hKsFitNe : Ks ⊓ fittingWithin M ≠ ⊥ := by
      intro hKsFit
      have hcentFMsK : centralizerWithin (fittingWithin Ms) K = ⊥ := by
        apply le_bot_iff.mp
        intro x hx
        have hxKs : x ∈ Ks := by
          change x ∈ centralizerWithin Ms K
          exact ⟨(fittingWithin_le Ms) hx.1, hx.2⟩
        have hxMeet : x ∈ Ks ⊓ fittingWithin M :=
          ⟨hxKs, hFMsFM hx.1⟩
        rw [hKsFit] at hxMeet
        exact hxMeet
      have hcommFit : ⁅Ms, K⁆ ≤ fittingWithin Ms :=
        odd_sdprod_primact_commg_sub_Fitting_of_internal
          hSigmaK (mFT_odd M) hsolM hcopMsK hsemiprimeMsK hcentFMsK
      have hMsFit : Ms ≤ fittingWithin Ms := by
        simpa only [hcommMsK] using hcommFit
      have hFitEq : fittingWithin Ms = Ms :=
        le_antisymm (fittingWithin_le Ms) hMsFit
      have hnilMs : Group.IsNilpotent Ms := by
        rw [← hFitEq]
        infer_instance
      exact hnotNilMs hnilMs
    let X : Subgroup G := Ks ⊓ fittingWithin M
    have hXne : X ≠ ⊥ := by
      simpa only [X] using hKsFitNe
    have hXKs : X ≤ Ks := inf_le_left
    have hXFit : X ≤ fittingWithin M := inf_le_right
    have hKsq : IsPGroup q Ks := by
      apply IsPGroup.of_card (n := 1)
      simp [q]
    have hXq : IsPGroup q X := hKsq.to_le hXKs
    let XF : Subgroup (fittingWithin M) :=
      X.subgroupOf (fittingWithin M)
    have hXFq : IsPGroup q XF :=
      hXq.of_equiv (Subgroup.subgroupOfEquivOfLe hXFit).symm
    have hXFcore : XF ≤ pCore q (fittingWithin M) :=
      hXFq.le_pCore_of_isNilpotent
    have hXleMappedCore :
        X ≤ (pCore q (fittingWithin M)).map (fittingWithin M).subtype := by
      rw [← Subgroup.map_subgroupOf_eq_of_le hXFit]
      exact Subgroup.map_mono hXFcore
    have hXQ : X ≤ Q := by
      simpa only [Q, pCoreWithin,
        map_pCore_fittingWithin_eq_map_pCore M q] using hXleMappedCore
    have hXcardDvd : Nat.card X ∣ q := by
      simpa only [q] using Subgroup.card_dvd_of_le hXKs
    have hXcard : Nat.card X = q :=
      ((Nat.dvd_prime hqPrime).mp hXcardDvd).resolve_left
        (fun hcard ↦ hXne (Subgroup.card_eq_one.mp hcard))
    have hXeq : X = Ks := by
      apply Subgroup.eq_of_le_of_card_ge hXKs
      simpa only [q] using hXcard.ge
    rw [← hXeq]
    exact hXQ

  /- Restrict to `J = Ms ⊔ K₁`, apply the prime Frobenius quotient-kernel
  theorem, and transport the resulting nilpotence back across the nested
  subgroup quotient. -/
  have hQnormalMs : (Q.subgroupOf Ms).Normal := by
    have hMnormQ : M ≤ Subgroup.normalizer (Q : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hQleM).mp hQnormalM
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hQleMs).mpr
      (hMsM.trans hMnormQ)
  have hcopQK₁ : Nat.Coprime (Nat.card Q) (Nat.card K₁) :=
    hcopMsK.coprime_dvd_left (Subgroup.card_dvd_of_le hQleMs)
      |>.coprime_dvd_right (Subgroup.card_dvd_of_le hK₁K)
  let J : Subgroup G := Ms ⊔ K₁
  have hMsJ : Ms ≤ J := le_sup_left
  have hK₁J : K₁ ≤ J := le_sup_right
  have hQJ : Q ≤ J := hQleMs.trans hMsJ
  have hJM : J ≤ M := sup_le hMsM (hK₁K.trans hKM)
  have hsolJ : IsSolvable J := isSolvable_of_le_15 hsolM hJM
  have hSigmaK₁ : IsInternalSemidirectProductIn Ms K₁ J := by
    simpa only [J] using semidirect_restrict_right_15 hSigmaK hK₁K
  let MsJ : Subgroup J := Ms.subgroupOf J
  let K₁J : Subgroup J := K₁.subgroupOf J
  let QJ : Subgroup J := Q.subgroupOf J
  have hMsJnormal : MsJ.Normal := by
    simpa only [MsJ] using hSigmaK₁.2.2.1
  have hQJnormal : QJ.Normal := by
    have hMnormQ : M ≤ Subgroup.normalizer (Q : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hQleM).mp hQnormalM
    simpa only [QJ] using
      (Subgroup.normal_subgroupOf_iff_le_normalizer hQJ).mpr
        (hJM.trans hMnormQ)
  have hQJMsJ : QJ ≤ MsJ := by
    intro x hx
    exact hQleMs hx
  have hcopQJK₁J : Nat.Coprime (Nat.card QJ) (Nat.card K₁J) := by
    simpa only [QJ, K₁J, MathlibSupport.natCard_subgroupOf_eq hQJ,
      MathlibSupport.natCard_subgroupOf_eq hK₁J] using hcopQK₁
  have hK₁Jprime : Nat.Prime (Nat.card K₁J) := by
    simpa only [K₁J, MathlibSupport.natCard_subgroupOf_eq hK₁J] using
      hK₁prime
  have hcentJ : centralizerWithin MsJ K₁J ≤ QJ := by
    intro x hx
    have hxCent : ((x : J) : G) ∈ centralizerWithin Ms K₁ := by
      refine ⟨hx.1, ?_⟩
      intro a ha
      let aJ : J := ⟨a, hK₁J ha⟩
      have hxaJ := hx.2 aJ (show aJ ∈ K₁J from ha)
      exact congrArg (fun z : J ↦ (z : G)) hxaJ
    exact hKsQ (hcentK₁.le hxCent)
  have hnilJ : Group.IsNilpotent (MsJ ⧸ QJ.subgroupOf MsJ) := by
    letI : IsSolvable J := hsolJ
    letI : MsJ.Normal := hMsJnormal
    letI : QJ.Normal := hQJnormal
    exact primeFrobeniusQuotientKernel_nilpotent
      (by simpa only [MsJ, K₁J] using hSigmaK₁.2.2.2)
      hQJMsJ hcopQJK₁J hK₁Jprime hcentJ
  have hnilMsQ : Group.IsNilpotent (Ms ⧸ Q.subgroupOf Ms) := by
    letI : (QJ.subgroupOf MsJ).Normal :=
      Subgroup.Normal.subgroupOf hQJnormal MsJ
    letI : (Q.subgroupOf Ms).Normal := hQnormalMs
    let eMs : MsJ ≃* Ms := Subgroup.subgroupOfEquivOfLe hMsJ
    have hmapQ :
        (QJ.subgroupOf MsJ).map eMs.toMonoidHom = Q.subgroupOf Ms := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        let xJ : J := ⟨(x : G), hMsJ x.property⟩
        let y : MsJ := ⟨xJ, x.property⟩
        refine ⟨y, ?_, ?_⟩
        · change (x : G) ∈ Q
          exact hx
        apply Subtype.ext
        rfl
    let eQuot :
        (MsJ ⧸ QJ.subgroupOf MsJ) ≃* (Ms ⧸ Q.subgroupOf Ms) :=
      QuotientGroup.congr (QJ.subgroupOf MsJ) (Q.subgroupOf Ms) eMs hmapQ
    letI : Group.IsNilpotent (MsJ ⧸ QJ.subgroupOf MsJ) := hnilJ
    exact Group.nilpotent_of_mulEquiv eQuot

  /- Identify the represented core intrinsically, use the nilpotent self-core
  quotient to obtain a Sylow subgroup of `Ms`, and extend it across the
  sigma-Hall index. -/
  have hQsq : IsPGroup q (Q.subgroupOf Ms) :=
    hQq.of_equiv (Subgroup.subgroupOfEquivOfLe hQleMs).symm
  have hQcore : Q.subgroupOf Ms = pCore q Ms := by
    apply le_antisymm
    · exact le_pCore hQsq hQnormalMs
    · let P : Subgroup G := (pCore q Ms).map Ms.subtype
      have hPMs : P ≤ Ms := Subgroup.map_subtype_le _
      have hPM : P ≤ M := hPMs.trans hMsM
      have hMnormMs : M ≤ Subgroup.normalizer (Ms : Set G) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hMsM).mp hMsnormal
      have hMnormP : M ≤ Subgroup.normalizer (P : Set G) := by
        rw [Subgroup.le_normalizer_iff]
        exact characteristic_map_subtype_invariant_under_normalizer
          Ms M (pCore q Ms) hMnormMs
      have hPnormalM : (P.subgroupOf M).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hPM).mpr hMnormP
      have hPq : IsPGroup q (P.subgroupOf M) :=
        (pCore_isPGroup.map Ms.subtype).of_equiv
          (Subgroup.subgroupOfEquivOfLe hPM).symm
      have hPcoreM : P.subgroupOf M ≤ pCore q M :=
        le_pCore hPq hPnormalM
      have hPQ : P ≤ Q := by
        calc
          P = (P.subgroupOf M).map M.subtype :=
            (Subgroup.map_subgroupOf_eq_of_le hPM).symm
          _ ≤ (pCore q M).map M.subtype := Subgroup.map_mono hPcoreM
          _ = Q := rfl
      intro x hx
      exact hPQ ⟨x, hx, rfl⟩
  have hQsylowMs : IsSylowSubgroupOf q Q Ms := by
    letI : (Q.subgroupOf Ms).Normal := hQnormalMs
    letI : Group.IsNilpotent (Ms ⧸ pCore q Ms) := by
      letI : Group.IsNilpotent (Ms ⧸ Q.subgroupOf Ms) := hnilMsQ
      exact Group.nilpotent_of_mulEquiv
        (QuotientGroup.quotientMulEquivOfEq hQcore)
    have hqNotIndex : ¬ q ∣ (Q.subgroupOf Ms).index := by
      rw [Subgroup.index_eq_card]
      rw [hQcore]
      exact not_dvd_natCard_quotient_pCore_of_isNilpotent
    let P : Sylow q Ms := hQsq.toSylow hqNotIndex
    refine ⟨P, ?_⟩
    change Q = (Q.subgroupOf Ms).map Ms.subtype
    exact (Subgroup.map_subgroupOf_eq_of_le hQleMs).symm
  have hqNotIndexMsM : ¬ q ∣ (Ms.subgroupOf M).index := by
    intro hqIndex
    exact (Msigma_Hall hM).isPiNumber_index
      hqPrime hqIndex hqSigma
  have hQsylowM : IsSylowSubgroupOf q Q M :=
    hQsylowMs.extend_of_not_dvd_index hMsM hqNotIndexMsM
  have hQleF : Q ≤ Fitting_core M :=
    normal_sylow_le_Fcore hQsylowM hQnormalM
  have hqQ : q ∣ Nat.card Q := by
    simpa only [q] using Subgroup.card_dvd_of_le hKsQ
  have hqF : q ∈ primeSupport (Nat.card (Fitting_core M)) :=
    ⟨hqPrime, hqQ.trans (Subgroup.card_dvd_of_le hQleF)⟩

  /- Replace `D` by a `K`-invariant conjugate, as in the source's
  `without loss nDK`.  All assertions below are invariant under that
  conjugation. -/
  have hHallDq : IsHall ({q} : Set ℕ)ᶜ (D.subgroupOf Ms) := by
    simpa [q, Ks, Ms] using hHallD
  obtain ⟨D₁, hD₁sigma, hD₁primeComplement, hKD₁⟩ :=
    exists_primeComplement_normalized_of_coprime_of_isSolvable
      (p := q) (A := K) (K := Ms)
      (hSigmaK.2.1.trans
        ((Subgroup.normal_subgroupOf_iff_le_normalizer hMsM).mp hMsnormal))
      hcopMsK hsolMs
  have hHallD₁ : IsHall ({q} : Set ℕ)ᶜ (D₁.subgroupOf Ms) :=
    (isPrimeComplement_iff_isHall_compl_singleton_15 hqPrime).mp
      hD₁primeComplement
  have hQDsd₀ : IsInternalSemidirectProductIn Q D Ms :=
    normal_sylow_complement_sdprod_15
      hqPrime hQsylowMs hQnormalMs hDsigma hHallDq
  have hQD₁sd : IsInternalSemidirectProductIn Q D₁ Ms :=
    normal_sylow_complement_sdprod_15
      hqPrime hQsylowMs hQnormalMs hD₁sigma hHallD₁
  obtain ⟨P, hQP⟩ := hQsylowMs
  have hQsubMs : Q.subgroupOf Ms = (P : Subgroup Ms) := by
    rw [hQP]
    exact Subgroup.comap_map_eq_self_of_injective
      Ms.subtype_injective (P : Subgroup Ms)
  let N : Subgroup Ms := Q.subgroupOf Ms
  letI : N.Normal := by simpa [N] using hQnormalMs
  letI : IsSolvable Ms := hsolMs
  letI : IsSolvable N := isSolvable_subgroup_of_isSolvable N
  have hcopN : Nat.Coprime (Nat.card N) N.index := by
    simpa [N, hQsubMs] using P.card_coprime_index
  obtain ⟨x, hx⟩ :=
    Subgroup.solvable_complement_conjugacy hcopN
      hQD₁sd.2.2.2 hQDsd₀.2.2.2
  let xG : G := ((x : N) : Ms)
  have hxM : xG ∈ M := hMsM (x : Ms).property
  have heD : D = D₁.map (MulAut.conj xG).toMonoidHom := by
    calc
      D = (D.subgroupOf Ms).map Ms.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hDsigma).symm
      _ = ((D₁.subgroupOf Ms).map
            (MulAut.conj (x : Ms)).toMonoidHom).map Ms.subtype := by
        rw [hx]
      _ = (D₁.subgroupOf Ms).map
            (Ms.subtype.comp (MulAut.conj (x : Ms)).toMonoidHom) := by
        rw [Subgroup.map_map]
      _ = (D₁.subgroupOf Ms).map
            ((MulAut.conj xG).toMonoidHom.comp Ms.subtype) := by rfl
      _ = ((D₁.subgroupOf Ms).map Ms.subtype).map
            (MulAut.conj xG).toMonoidHom := by
        rw [Subgroup.map_map]
      _ = D₁.map (MulAut.conj xG).toMonoidHom := by
        rw [Subgroup.map_subgroupOf_eq_of_le hD₁sigma]
  suffices hD₁result : FCoreNonNilpotentStructure M K D₁ by
    exact hD₁result.conjugate_complement_back xG hxM heD
  clear hDsigma hHallD Q₀ hHallDq hQDsd₀ hx heD D
  let D := D₁
  have hQsylowMs : IsSylowSubgroupOf q Q Ms := ⟨P, hQP⟩
  let Q₀ := centralizerWithin Q D
  have hDsigma : D ≤ Ms := by simpa [D] using hD₁sigma
  have hHallD : IsHall ({q} : Set ℕ)ᶜ (D.subgroupOf Ms) := by
    simpa [q, D] using hHallD₁
  have hKnormD : K ≤ Subgroup.normalizer (D : Set G) := by
    simpa [D] using hKD₁

  have hQDsd : IsInternalSemidirectProductIn Q D Ms := by
    exact normal_sylow_complement_sdprod_15
      hqPrime hQsylowMs hQnormalMs hDsigma hHallD
  have hDnil : Group.IsNilpotent D := by
    exact complement_nilpotent_of_nilpotent_quotient_15 hQDsd hnilMsQ
  have hQ₀leQ : Q₀ ≤ Q := inf_le_left
  have hDnormQ : D ≤ Subgroup.normalizer (Q : Set G) :=
    hQDsd.2.1.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hQDsd.1).mp
        hQDsd.2.2.1)
  have hDnormQ₀ : D ≤ Subgroup.normalizer (Q₀ : Set G) := by
    exact centralizerWithin_normalized_by_common_normalizer_15
      hDnormQ Subgroup.le_normalizer
  have hKnormQ : K ≤ Subgroup.normalizer (Q : Set G) :=
    hKM.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hQleM).mp hQnormalM)
  have hKnormQ₀ : K ≤ Subgroup.normalizer (Q₀ : Set G) := by
    exact centralizerWithin_normalized_by_common_normalizer_15
      hKnormQ hKnormD
  have hDKnormQ₀ : D ⊔ K ≤ Subgroup.normalizer (Q₀ : Set G) :=
    sup_le hDnormQ₀ hKnormQ₀

  /- The `Qi_rec` induction from pp. 118--119.  Starting with `Q0`, choose
  a minimal normal layer and repeat while the layer does not contain
  `Kstar`.  Nilpotence of the relevant Frobenius kernels rules out stopping
  early, so the first layer already reaches `Q`. -/
  have hQ₀ltQ : Q₀ < Q := by
    refine lt_of_le_of_ne hQ₀leQ ?_
    intro heq
    have hQcentD : Q ≤ centralizerWithin Q D := by
      simpa only [Q₀] using heq.symm.le
    have hdirect : IsInternalDirectProductIn Q D Ms := by
      exact
        { left_le := hQDsd.1
          right_le := hQDsd.2.1
          complement := hQDsd.2.2.2
          commute := by
            intro x y
            exact ((hQcentD x.property).2 (y : G) y.property).symm }
    letI : Group.IsNilpotent Q := hQq.isNilpotent
    letI : Group.IsNilpotent D := hDnil
    exact hnotNilMs (Group.nilpotent_of_mulEquiv hdirect.mulEquiv)
  have hDKM : D ⊔ K ≤ M :=
    sup_le (hDsigma.trans hMsM) hKM
  have Qi_rec :
      ∀ (Qi : Subgroup G),
        Qi ≤ Q → Q₀ ≤ Qi →
        D ⊔ K ≤ Subgroup.normalizer (Qi : Set G) →
        Qi < Q →
        ∃ L : Subgroup G,
          IsMinimalNormalizerFactor_15 Qi L M ∧
            L ≤ Q ∧
            D ⊔ K ≤ Subgroup.normalizer (L : Set G) ∧
            Ks ≤ L ∧ ¬ Ks ≤ Qi := by
    intro Qi hQiQ hQ₀Qi hQiInv hQiLtQ
    let Ni : Subgroup G := M ⊓ Subgroup.normalizer (Qi : Set G)
    let R : Subgroup G := Q ⊓ Subgroup.normalizer (Qi : Set G)
    have hQiM : Qi ≤ M := hQiQ.trans hQleM
    have hQiNi : Qi ≤ Ni :=
      le_inf hQiM Subgroup.le_normalizer
    have hQiNormalNi : (Qi.subgroupOf Ni).Normal := by
      apply Subgroup.normal_subgroupOf_of_le_normalizer
      exact inf_le_right
    have hRNi : R ≤ Ni :=
      inf_le_inf hQleM le_rfl
    have hMnormQ : M ≤ Subgroup.normalizer (Q : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hQleM).mp hQnormalM
    have hNiNormQ : Ni ≤ Subgroup.normalizer (Q : Set G) :=
      inf_le_left.trans hMnormQ
    have hNiNormNQi :
        Ni ≤ Subgroup.normalizer
          (Subgroup.normalizer (Qi : Set G) : Set G) :=
      inf_le_right.trans Subgroup.le_normalizer
    have hNiNormR : Ni ≤ Subgroup.normalizer (R : Set G) := by
      simpa only [R] using
        (le_inf hNiNormQ hNiNormNQi).trans
          (Subgroup.inf_normalizer_le_normalizer_inf
            (H := Q) (K := Subgroup.normalizer (Qi : Set G)))
    have hRNormalNi : (R.subgroupOf Ni).Normal := by
      exact Subgroup.normal_subgroupOf_of_le_normalizer hNiNormR
    have hQiLtR : Qi < R := by
      simpa only [R] using
        (lt_inf_normalizer_of_isPGroup hQq hQiLtQ)
    let Good : Subgroup G → Prop := fun T ↦
      Qi < T ∧ T ≤ R ∧ (T.subgroupOf Ni).Normal
    have hRgood : Good R := ⟨hQiLtR, le_rfl, hRNormalNi⟩
    obtain ⟨L, _hLR, hLmin⟩ :=
      Finite.exists_le_minimal (p := Good) hRgood
    have hLgood : Good L := hLmin.1
    have hLNi : L ≤ Ni := hLgood.2.1.trans hRNi
    have hminFactor : IsMinimalNormalizerFactor_15 Qi L M := by
      refine ⟨hLgood.1, hLNi, hQiNormalNi, hLgood.2.2, ?_⟩
      intro T hQiT hTL hTnormal
      by_cases hTQi : T = Qi
      · exact Or.inl hTQi
      · right
        have hQiTLt : Qi < T :=
          lt_of_le_of_ne hQiT (Ne.symm hTQi)
        have hTR : T ≤ R := hTL.trans hLgood.2.1
        have hTgood : Good T := ⟨hQiTLt, hTR, hTnormal⟩
        exact (hLmin.eq_of_ge hTgood hTL).symm
    have hLQ : L ≤ Q := hLgood.2.1.trans inf_le_left
    have hDKNi : D ⊔ K ≤ Ni :=
      le_inf hDKM hQiInv
    have hNiNormL : Ni ≤ Subgroup.normalizer (L : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hLNi).mp
        hLgood.2.2
    have hDKInvL : D ⊔ K ≤ Subgroup.normalizer (L : Set G) :=
      hDKNi.trans hNiNormL
    have hQiNormalL : (Qi.subgroupOf L).Normal :=
      normal_in_upper_of_minimalNormalizerFactor_15 hminFactor
    have hLnormQi : L ≤ Subgroup.normalizer (Qi : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hminFactor.1.le).mp
        hQiNormalL
    have hcentQDQi : centralizerWithin Q D ≤ Qi := by
      simpa only [Q₀] using hQ₀Qi
    have hnreg : ¬ (Ks ≤ L → Ks ≤ Qi) := by
      exact qi_layer_partner_obstruction_15
        (M := M) (Ms := Ms) (Ks := Ks) (K := K) (K₁ := K₁)
        (D := D) (Q := Q) (Qi := Qi) (L := L)
        hqPrime hsolM hQq hKsQ hcentQDQi hminFactor.1 hLQ
        hLnormQi hQiInv hDKInvL hQDsd hSigmaK hKnormD hK₁K
        hK₁prime hcentK₁ hcopMsK (by simpa only [q] using hHallD)
    have hKsL : Ks ≤ L := by
      by_contra hnot
      exact hnreg (fun h ↦ (hnot h).elim)
    have hnotKsQi : ¬ Ks ≤ Qi := by
      intro hKsQi
      exact hnreg (fun _ ↦ hKsQi)
    exact ⟨L, hminFactor, hLQ, hDKInvL, hKsL, hnotKsQi⟩
  obtain ⟨Q₁, hminQ₁, hQ₁Q, hDKnormQ₁,
      hKsQ₁, hnotKsQ₀⟩ :=
    Qi_rec Q₀ hQ₀leQ le_rfl hDKnormQ₀ hQ₀ltQ
  have hQ₁eq : Q₁ = Q := by
    by_contra hne
    have hQ₁ltQ : Q₁ < Q := lt_of_le_of_ne hQ₁Q hne
    obtain ⟨Q₂, _hminQ₂, _hQ₂Q, _hDKnormQ₂,
        _hKsQ₂, hnotKsQ₁⟩ :=
      Qi_rec Q₁ hQ₁Q hminQ₁.1.le hDKnormQ₁ hQ₁ltQ
    exact hnotKsQ₁ hKsQ₁
  have hminQnorm : IsMinimalNormalizerFactor_15 Q₀ Q M := by
    simpa only [hQ₁eq] using hminQ₁
  have hQ₀normalQ : (Q₀.subgroupOf Q).Normal :=
    normal_in_upper_of_minimalNormalizerFactor_15 hminQnorm
  have hQnormQ₀ : Q ≤ Subgroup.normalizer (Q₀ : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQ₀leQ).mp
      hQ₀normalQ
  have hQ₀normalM : (Q₀.subgroupOf M).Normal :=
    normal_of_normalized_by_iterated_sdprod_15
      (hQ₀leQ.trans hQleM) hQnormQ₀ hDnormQ₀ hKnormQ₀
      hQDsd hSigmaK
  have hminimal : IsMinimalNormalFactor Q₀ Q M := by
    exact minimalNormalFactor_of_minimalNormalizerFactor_15
      hminQnorm hQ₀normalM

  let Qbar := Q ⧸ Q₀.subgroupOf Q
  letI : (Q₀.subgroupOf Q).Normal := hQ₀normalQ
  have hQbarElem : IsElementaryAbelianGroup q Qbar := by
    exact elementaryAbelian_quotient_of_minimalNormalFactor_15
      hminimal hQq hsolM
  have hQbarComm : IsMulCommutative Qbar :=
    hQbarElem.commutative

  /- The Fitting subgroup is the stable-factor centralizer. -/
  let F := fittingWithin M
  let Pq : Subgroup F := pCore q F
  let Rq : Subgroup F := pPrimeCore q F
  have hPqmap : Pq.map F.subtype = Q := by
    simpa only [F, Pq, Q, pCoreWithin] using
      map_pCore_fittingWithin_eq_map_pCore M q
  have hRqcent : Rq.map F.subtype ≤ centralizerWithin M Q := by
    rintro y ⟨r, hrR, rfl⟩
    refine ⟨(fittingWithin_le M r.property), ?_⟩
    intro z hzQ
    rw [← hPqmap] at hzQ
    rcases hzQ with ⟨s, hsP, rfl⟩
    have hsCent := pCore_le_centralizer_pPrimeCore (G := F) q hsP
    exact congrArg Subtype.val
      (Subgroup.mem_centralizer_iff.mp hsCent r hrR).symm
  have hfitLe : fittingWithin M ≤
      Q ⊔ centralizerWithin M Q := by
    have htop :=
      sup_pCore_pPrimeCore_eq_top_of_isNilpotent (G := F) q
    have hmapTop : (⊤ : Subgroup F).map F.subtype = F := by
      simpa using
        (Subgroup.map_subgroupOf_eq_of_le (show F ≤ F from le_rfl))
    change F ≤ Q ⊔ centralizerWithin M Q
    rw [← hmapTop, ← htop, Subgroup.map_sup, hPqmap]
    exact sup_le le_sup_left (hRqcent.trans le_sup_right)

  have hQnotKs : ¬ Q ≤ Ks := by
    obtain ⟨S, hQS⟩ := hQsylowM
    have hqKs : q ∈ primeSupport (Nat.card Ks) := by
      refine ⟨hqPrime, ?_⟩
      change Nat.card Ks ∣ Nat.card Ks
      exact dvd_rfl
    have hnle := (hPstruct.Kstar_sylow_unique
      (by simpa only [Ks, kappaCentralizer, pTypeCentralizer] using hqKs)
      S).2
    intro hQKs
    apply hnle
    simpa only [ambientSylow, ← hQS, Ks, kappaCentralizer,
      pTypeCentralizer] using hQKs
  have hCKQ : centralizerWithin K Q = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    by_contra hx1
    let X : Subgroup G := Subgroup.zpowers x
    have hXK : X ≤ K := Subgroup.zpowers_le.mpr hx.1
    have hXne : X ≠ ⊥ := by
      intro hbot
      have hxbot : x ∈ (⊥ : Subgroup G) := by
        rw [← hbot]
        exact Subgroup.mem_zpowers x
      exact hx1 (by simpa using hxbot)
    have hQcentX : Q ≤ centralizerWithin Ms X := by
      intro z hzQ
      refine ⟨hQleMs hzQ, ?_⟩
      intro a haX
      rcases Subgroup.mem_zpowers_iff.mp haX with ⟨n, rfl⟩
      exact (show Commute z x from hx.2 z hzQ).zpow_right n |>.eq.symm
    apply hQnotKs
    simpa only [Ms, Ks, kappaCentralizer] using
      hQcentX.trans_eq (hPstruct.sigma_K_prime X hXK hXne)

  let CMQ := centralizerWithin M Q
  have hCMQM : CMQ ≤ M := centralizerWithin_le_left M Q
  have hCMQnormalM : (CMQ.subgroupOf M).Normal := by
    letI : (Q.subgroupOf M).Normal := hQnormalM
    have heq : CMQ.subgroupOf M =
        Subgroup.centralizer (Q.subgroupOf M : Set M) := by
      ext x
      simp only [CMQ, centralizerWithin, Subgroup.mem_subgroupOf,
        Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
      constructor
      · rintro ⟨_, hx⟩ z hz
        exact Subtype.ext (hx z hz)
      · intro hx
        refine ⟨x.property, ?_⟩
        intro z hz
        exact congrArg Subtype.val (hx ⟨z, hQleM hz⟩ hz)
    rw [heq]
    infer_instance
  have hCMQdisK : Disjoint CMQ K := by
    rw [disjoint_iff]
    apply le_antisymm
    · intro x hx
      have hxbot : x ∈ (⊥ : Subgroup G) := by
        rw [← hCKQ]
        exact ⟨hx.2, hx.1.2⟩
      exact hxbot
    · exact bot_le
  have hCMQMs : CMQ ≤ Ms := by
    exact normal_le_left_of_disjoint_right_of_coprime_sdprod_15
      hSigmaK hcopMsK hCMQM hCMQnormalM hCMQdisK

  have hMnormMs : M ≤ Subgroup.normalizer (Ms : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMsM).mp hMsnormal
  have hMnormQ : M ≤ Subgroup.normalizer (Q : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQleM).mp hQnormalM
  have hMnormQ₀ : M ≤ Subgroup.normalizer (Q₀ : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (hQ₀leQ.trans hQleM)).mp hQ₀normalM
  let Cfac : Subgroup G :=
    factorCentralizerSubgroup_15 (Q := Q)
      (hMsM.trans hMnormQ₀)
  have hCfacCarrier : (Cfac : Set G) =
      factorCentralizerWithin Ms Q Q₀ := rfl
  have hCfacM : Cfac ≤ M := by
    intro x hx
    exact hMsM hx.1
  have hCfacNormalM : (Cfac.subgroupOf M).Normal := by
    apply Subgroup.normal_subgroupOf_of_le_normalizer
    exact factorCentralizerSubgroup_normalized_15
      (A := Ms) (Q := Q) (N := Q₀) (B := M)
      (hMsM.trans hMnormQ₀) hMnormMs hMnormQ hMnormQ₀
  have hQfactor : Q ≤ Cfac := by
    have hcommLe : _root_.commutator Q ≤ Q₀.subgroupOf Q :=
      Subgroup.Normal.quotient_commutative_iff_commutator_le.mp hQbarComm
    intro a haQ
    refine ⟨hQleMs haQ, ?_⟩
    intro z hzQ
    let aQ : Q := ⟨a, haQ⟩
    let zQ : Q := ⟨z, hzQ⟩
    have hzacom : ⁅zQ, aQ⁆ ∈ _root_.commutator Q := by
      rw [commutator_eq_closure]
      exact Subgroup.subset_closure
        (commutator_mem_commutatorSet zQ aQ)
    exact hcommLe hzacom
  have hCMQfactor : CMQ ≤ Cfac := by
    intro x hx
    refine ⟨hCMQMs hx, ?_⟩
    intro z hzQ
    have hcomm : ⁅z, x⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr (hx.2 z hzQ)
    rw [hcomm]
    exact Q₀.one_mem
  have hjoinLeFactor :
      Q ⊔ centralizerWithin M Q ≤ Cfac := by
    exact sup_le hQfactor hCMQfactor

  let A₀ : Subgroup G := D ⊓ Cfac
  have hCfacMs : Cfac ≤ Ms := by
    intro x hx
    exact hx.1
  have hcompC :
      (Q.subgroupOf Cfac).IsComplement'
        (A₀.subgroupOf Cfac) := by
    change Function.Bijective
      (fun x : (Q.subgroupOf Cfac) × (A₀.subgroupOf Cfac) ↦
        (x.1 : Cfac) * (x.2 : Cfac))
    constructor
    · intro x y hxy
      let xMs : (Q.subgroupOf Ms) × (D.subgroupOf Ms) :=
        (⟨⟨(((x.1 : Cfac) : G)), hQleMs x.1.property⟩,
            x.1.property⟩,
          ⟨⟨(((x.2 : Cfac) : G)), hDsigma x.2.property.1⟩,
            x.2.property.1⟩)
      let yMs : (Q.subgroupOf Ms) × (D.subgroupOf Ms) :=
        (⟨⟨(((y.1 : Cfac) : G)), hQleMs y.1.property⟩,
            y.1.property⟩,
          ⟨⟨(((y.2 : Cfac) : G)), hDsigma y.2.property.1⟩,
            y.2.property.1⟩)
      have hxyMs : (xMs.1 : Ms) * (xMs.2 : Ms) =
          (yMs.1 : Ms) * (yMs.2 : Ms) := by
        apply Subtype.ext
        exact congrArg (fun z : Cfac ↦ (z : G)) hxy
      have hpair : xMs = yMs := hQDsd.2.2.2.1 hxyMs
      apply Prod.ext
      · apply Subtype.ext
        apply Subtype.ext
        exact congrArg
          (fun z : (Q.subgroupOf Ms) × (D.subgroupOf Ms) ↦
            ((z.1 : Ms) : G)) hpair
      · apply Subtype.ext
        apply Subtype.ext
        exact congrArg
          (fun z : (Q.subgroupOf Ms) × (D.subgroupOf Ms) ↦
            ((z.2 : Ms) : G)) hpair
    · intro t
      let tMs : Ms := ⟨(t : G), hCfacMs t.property⟩
      obtain ⟨⟨qMs, dMs⟩, hqd⟩ := hQDsd.2.2.2.2 tMs
      have hqdG : ((qMs : Ms) : G) * ((dMs : Ms) : G) =
          (t : G) := congrArg Subtype.val hqd
      have hdCfac : ((dMs : Ms) : G) ∈ Cfac := by
        have hdEq : ((dMs : Ms) : G) =
            ((qMs : Ms) : G)⁻¹ * (t : G) := by
          rw [← hqdG]
          group
        rw [hdEq]
        exact Cfac.mul_mem
          (Cfac.inv_mem (hQfactor qMs.property)) t.property
      let qC : Q.subgroupOf Cfac :=
        ⟨⟨((qMs : Ms) : G), hQfactor qMs.property⟩,
          qMs.property⟩
      let dC : A₀.subgroupOf Cfac :=
        ⟨⟨((dMs : Ms) : G), hdCfac⟩,
          ⟨dMs.property, hdCfac⟩⟩
      refine ⟨(qC, dC), ?_⟩
      apply Subtype.ext
      exact hqdG
  have hA₀centQ₀ : A₀ ≤ Subgroup.centralizer (Q₀ : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    exact (hn.2 a ha.1).symm
  have hcommQA₀ : ⁅Q, A₀⁆ ≤ Q₀ := by
    apply Subgroup.commutator_le.mpr
    intro z hz a ha
    exact ha.2.2 z hz
  have hcommA₀Q : ⁅A₀, Q⁆ ≤ Q₀ := by
    simpa only [Subgroup.commutator_comm A₀ Q] using hcommQA₀
  have hQpi : IsPiNumber ({q} : Set ℕ) (Nat.card Q) :=
    hQq.isPiNumber_natCard (by simp)
  have hDpi : IsPiNumber ({q} : Set ℕ)ᶜ (Nat.card D) := by
    simpa only [MathlibSupport.natCard_subgroupOf_eq hDsigma] using
      hHallD.isPiNumber_card
  have hA₀pi : IsPiNumber ({q} : Set ℕ)ᶜ (Nat.card A₀) :=
    hDpi.of_dvd (Subgroup.card_dvd_of_le inf_le_left)
  have hcopQA₀ : Nat.Coprime (Nat.card Q) (Nat.card A₀) :=
    hQpi.coprime_compl hA₀pi
  have hA₀centQ : A₀ ≤ Subgroup.centralizer (Q : Set G) :=
    stableFactor_centralizes hA₀centQ₀ hQ₀leQ hcommA₀Q hcopQA₀
  have hdirectC : IsInternalDirectProductIn Q A₀ Cfac :=
    { left_le := hQfactor
      right_le := inf_le_right
      complement := hcompC
      commute := by
        intro z a
        exact Subgroup.mem_centralizer_iff.mp
          (hA₀centQ a.property) z z.property }
  have hCfacNil : Group.IsNilpotent Cfac := by
    letI : Group.IsNilpotent Q := hQq.isNilpotent
    letI : Group.IsNilpotent A₀ :=
      isNilpotent_of_le_15 hDnil inf_le_left
    exact Group.nilpotent_of_mulEquiv hdirectC.mulEquiv
  have hCfacFit : Cfac ≤ fittingWithin M := by
    let CM : Subgroup M := Cfac.subgroupOf M
    let eCM : CM ≃* Cfac := Subgroup.subgroupOfEquivOfLe hCfacM
    letI : CM.Normal := hCfacNormalM
    letI : Group.IsNilpotent CM :=
      Group.nilpotent_of_mulEquiv eCM.symm
    have hcore : CM ≤ fittingCore M :=
      nilpotent_normal_le_fittingCore (by infer_instance) (by infer_instance)
    change Cfac ≤ (fittingCore M).map M.subtype
    rw [← Subgroup.map_subgroupOf_eq_of_le hCfacM]
    exact Subgroup.map_mono hcore
  have hfitFactor : fittingWithin M ≤ Cfac :=
    hfitLe.trans hjoinLeFactor
  have hfactorEq :
      factorCentralizerWithin Ms Q Q₀ =
        (fittingWithin M : Set G) := by
    rw [← hCfacCarrier]
    exact congrArg (fun H : Subgroup G ↦ (H : Set G))
      (le_antisymm hCfacFit hfitFactor)
  have hfitJoin : Q ⊔ centralizerWithin M Q = fittingWithin M := by
    apply le_antisymm
    · exact hjoinLeFactor.trans hCfacFit
    · exact hfitLe
  have hfitLt : fittingWithin M < Ms := by
    refine lt_of_le_of_ne (hfitFactor.trans hCfacMs) ?_
    intro heq
    exact hnotNilMs (heq ▸ fittingWithin_isNilpotent M)

  /- Coprime stabilizers on `Q/Q0` and the prime-action theorem give the
  two prime orders and the cardinality `q^p`. -/
  have hDKreg : centralizerWithin D K = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hxKs : x ∈ Ks := by
      change x ∈ centralizerWithin Ms K
      exact ⟨hDsigma hx.1, hx.2⟩
    let xMs : Ms := ⟨x, hDsigma hx.1⟩
    have hxInf :
        xMs ∈ (Q.subgroupOf Ms) ⊓ (D.subgroupOf Ms) :=
      ⟨hKsQ hxKs, hx.1⟩
    have hxBot : xMs ∈ (⊥ : Subgroup Ms) :=
      hQDsd.2.2.2.disjoint.le_bot hxInf
    apply Subgroup.mem_bot.mpr
    simpa [xMs] using
      congrArg Subtype.val (Subgroup.mem_bot.mp hxBot)
  have hprimeDK : IsPrimeAction D K :=
    IsPrimeAction.mono_left hDsigma hPstruct.sigma_K_prime
  have hsemiregDK : IsSemiregularConjugation D K := by
    intro k hk d hfix
    have hkG : (k : G) ≠ 1 := by
      intro hkOne
      apply hk
      exact Subtype.ext hkOne
    let X : Subgroup G := Subgroup.zpowers (k : G)
    have hXK : X ≤ K := Subgroup.zpowers_le.mpr k.property
    have hXne : X ≠ ⊥ := Subgroup.zpowers_ne_bot.mpr hkG
    have hcentEq := hprimeDK.centralizer_eq hXK hXne
    have hcomm : Commute (k : G) (d : G) := by
      rw [Commute]
      calc
        (k : G) * (d : G) =
            ((k : G) * (d : G) * (k : G)⁻¹) * (k : G) := by
          group
        _ = (d : G) * (k : G) := by rw [hfix]
    have hdCent : (d : G) ∈ centralizerWithin D X := by
      refine ⟨d.property, ?_⟩
      intro y hy
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact hcomm.zpow_left n
    rw [hcentEq, hDKreg] at hdCent
    apply Subtype.ext
    exact Subgroup.mem_bot.mp hdCent
  have hQ₀M : Q₀ ≤ M := hQ₀leQ.trans hQleM
  have hDM : D ≤ M := hDsigma.trans hMsM
  let N₀ : Subgroup M := Q₀.subgroupOf M
  let DM : Subgroup M := D.subgroupOf M
  let KM : Subgroup M := K.subgroupOf M
  letI : N₀.Normal := by
    simpa only [N₀] using hQ₀normalM
  let Mbar := M ⧸ N₀
  let qM : M →* Mbar := QuotientGroup.mk' N₀
  have hN₀q : IsPGroup q N₀ :=
    (hQq.to_le hQ₀leQ).of_equiv
      (Subgroup.subgroupOfEquivOfLe hQ₀M).symm
  have hN₀pi : IsPiNumber ({q} : Set ℕ) (Nat.card N₀) :=
    hN₀q.isPiNumber_natCard (by simp)
  have hDMpi : IsPiNumber ({q} : Set ℕ)ᶜ (Nat.card DM) := by
    simpa only [DM, MathlibSupport.natCard_subgroupOf_eq hDM,
      MathlibSupport.natCard_subgroupOf_eq hDsigma] using
      hHallD.isPiNumber_card
  have hcopN₀DM : Nat.Coprime (Nat.card N₀) (Nat.card DM) :=
    hN₀pi.coprime_compl hDMpi
  have hN₀cardDvdMs : Nat.card N₀ ∣ Nat.card Ms := by
    simpa only [N₀, MathlibSupport.natCard_subgroupOf_eq hQ₀M] using
      Subgroup.card_dvd_of_le (hQ₀leQ.trans hQleMs)
  have hcopN₀K : Nat.Coprime (Nat.card N₀) (Nat.card K) :=
    hcopMsK.coprime_dvd_left hN₀cardDvdMs
  have hcopN₀KM : Nat.Coprime (Nat.card N₀) (Nat.card KM) := by
    simpa only [KM, MathlibSupport.natCard_subgroupOf_eq hKM] using
      hcopN₀K
  have hDKsd : IsInternalSemidirectProductIn D K (D ⊔ K) :=
    semidirect_restrict_left_15 hSigmaK hDsigma hKnormD
  have hDKcard : Nat.card (D ⊔ K : Subgroup G) =
      Nat.card D * Nat.card K := by
    calc
      Nat.card (D ⊔ K : Subgroup G) =
          Nat.card (D.subgroupOf (D ⊔ K)) *
            Nat.card (K.subgroupOf (D ⊔ K)) :=
        hDKsd.2.2.2.card_mul.symm
      _ = Nat.card D * Nat.card K := by
        rw [MathlibSupport.natCard_subgroupOf_eq le_sup_left,
          MathlibSupport.natCard_subgroupOf_eq le_sup_right]
  have hDMKMcard : Nat.card (DM ⊔ KM : Subgroup M) =
      Nat.card DM * Nat.card KM := by
    calc
      Nat.card (DM ⊔ KM : Subgroup M) =
          Nat.card ((D ⊔ K).subgroupOf M) := by
        rw [Subgroup.subgroupOf_sup hDM hKM]
      _ = Nat.card (D ⊔ K : Subgroup G) :=
        MathlibSupport.natCard_subgroupOf_eq (sup_le hDM hKM)
      _ = Nat.card D * Nat.card K := hDKcard
      _ = Nat.card DM * Nat.card KM := by
        change Nat.card D * Nat.card K =
          Nat.card (D.subgroupOf M) * Nat.card (K.subgroupOf M)
        rw [MathlibSupport.natCard_subgroupOf_eq hDM,
          MathlibSupport.natCard_subgroupOf_eq hKM]
  have hcopN₀DMKM :
      Nat.Coprime (Nat.card N₀) (Nat.card (DM ⊔ KM : Subgroup M)) := by
    rw [hDMKMcard]
    exact hcopN₀DM.mul_right hcopN₀KM
  have hdisN₀DMKM : Disjoint N₀ (DM ⊔ KM) :=
    Subgroup.disjoint_of_coprime_natCard hcopN₀DMKM
  have hqM_inj : Function.Injective (qM.subgroupMap (DM ⊔ KM)) := by
    rw [← MonoidHom.ker_eq_bot_iff, Subgroup.ker_subgroupMap,
      QuotientGroup.ker_mk', Subgroup.subgroupOf_eq_bot]
    exact hdisN₀DMKM
  have hsemiregDMKM : IsSemiregularConjugation DM KM := by
    intro k hk d hfix
    let kK : K := ⟨((k : M) : G), k.property⟩
    let dD : D := ⟨((d : M) : G), d.property⟩
    have hkK : kK ≠ 1 := by
      intro hkOne
      apply hk
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : K ↦ (z : G)) hkOne
    have hfixG :
        (kK : G) * (dD : G) * (kK : G)⁻¹ = (dD : G) := by
      exact congrArg Subtype.val hfix
    have hdOne : dD = 1 := hsemiregDK kK hkK dD hfixG
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : D ↦ (z : G)) hdOne
  have hsemiregDbKb : IsSemiregularConjugation
      (DM.map qM) (KM.map qM) :=
    quotient_semiregular_of_injective_on_sup_15 hsemiregDMKM hqM_inj
  let QM : Subgroup M := Q.subgroupOf M
  let Qb : Subgroup Mbar := QM.map qM
  let Db : Subgroup Mbar := DM.map qM
  let Kb : Subgroup Mbar := KM.map qM
  have hsemiregDbKb' : IsSemiregularConjugation Db Kb := by
    simpa only [Db, Kb] using hsemiregDbKb
  let toQM : Q →* QM :=
    { toFun := fun x ↦ ⟨⟨(x : G), hQleM x.property⟩, x.property⟩
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl }
  have htoQM : Function.Surjective toQM := by
    intro x
    exact ⟨⟨(((x : QM) : M) : G), x.property⟩, rfl⟩
  let fQ : Q →* Qb := (qM.subgroupMap QM).comp toQM
  have hfQ : Function.Surjective fQ :=
    (qM.subgroupMap_surjective QM).comp htoQM
  have hfQker : Q₀.subgroupOf Q = fQ.ker := by
    ext x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      apply Subtype.ext
      exact QuotientGroup.eq_one_iff (toQM x : M) |>.mpr hx
    · intro hx
      have hx' := congrArg Subtype.val hx
      exact QuotientGroup.eq_one_iff (toQM x : M) |>.mp hx'
  let eQ : Qbar ≃* Qb :=
    QuotientGroup.liftEquiv (Q₀.subgroupOf Q) hfQ hfQker
  have hQbElem : IsElementaryAbelianGroup q Qb :=
    elementaryAbelian_of_mulEquiv_15 hQbarElem eQ
  have hQbComm : IsMulCommutative Qb := hQbElem.commutative
  have hN₀QM : N₀ ≤ QM := by
    intro x hx
    exact hQ₀leQ hx
  letI : QM.Normal := by
    simpa only [QM] using hQnormalM
  have hQbNormal : Qb.Normal := by
    dsimp only [Qb]
    infer_instance
  letI : Qb.Normal := hQbNormal
  have hminQb : IsMinimalNormal Qb := by
    refine ⟨?_, hQbNormal, ?_⟩
    · intro hbot
      have hleKer : QM ≤ qM.ker :=
        (Subgroup.map_eq_bot_iff QM).mp (by simpa only [Qb] using hbot)
      have hleN₀ : QM ≤ N₀ := by
        change QM ≤ (QuotientGroup.mk' N₀).ker at hleKer
        simpa only [QuotientGroup.ker_mk'] using hleKer
      have hQQ₀ : Q ≤ Q₀ := by
        intro x hx
        exact hleN₀ (show (⟨x, hQleM hx⟩ : M) ∈ QM from hx)
      exact (not_le_of_gt hminimal.1) hQQ₀
    · intro L hLnormal hLle hLne
      let R : Subgroup M := L.comap qM
      have hN₀R : N₀ ≤ R := QuotientGroup.le_comap_mk' N₀ L
      have hkerQM : qM.ker ≤ QM := by
        change (QuotientGroup.mk' N₀).ker ≤ QM
        simpa only [QuotientGroup.ker_mk'] using hN₀QM
      have hRQM : R ≤ QM := by
        calc
          R ≤ (QM.map qM).comap qM :=
            Subgroup.comap_mono (by simpa only [Qb] using hLle)
          _ = QM := Subgroup.comap_map_eq_self hkerQM
      have hRnormal : R.Normal := Subgroup.Normal.comap hLnormal qM
      let A : Subgroup G := R.map M.subtype
      have hQ₀A : Q₀ ≤ A := by
        intro n hn
        exact ⟨(⟨n, hQ₀M hn⟩ : M), hN₀R hn, rfl⟩
      have hAQ : A ≤ Q := by
        rintro _ ⟨r, hr, rfl⟩
        exact hRQM hr
      have hAsub : A.subgroupOf M = R := by
        ext x
        constructor
        · rintro ⟨r, hr, hrx⟩
          have hrx' : r = x := Subtype.ext hrx
          exact hrx' ▸ hr
        · intro hx
          exact ⟨x, hx, rfl⟩
      have hAnormal : (A.subgroupOf M).Normal := by
        rw [hAsub]
        exact hRnormal
      rcases hminimal.2.2.2.2 A hQ₀A hAQ hAnormal with hA | hA
      · exfalso
        apply hLne
        have hRQ₀ : R = N₀ := by
          apply Subgroup.map_injective M.subtype_injective
          calc
            R.map M.subtype = A := rfl
            _ = Q₀ := hA
            _ = N₀.map M.subtype :=
              (Subgroup.map_subgroupOf_eq_of_le hQ₀M).symm
        calc
          L = R.map qM :=
            (Subgroup.map_comap_eq_self_of_surjective
              (QuotientGroup.mk'_surjective N₀) L).symm
          _ = N₀.map qM := congrArg (Subgroup.map qM) hRQ₀
          _ = ⊥ := QuotientGroup.map_mk'_self N₀
      · have hRQM_eq : R = QM := by
          apply Subgroup.map_injective M.subtype_injective
          calc
            R.map M.subtype = A := rfl
            _ = Q := hA
            _ = QM.map M.subtype :=
              (Subgroup.map_subgroupOf_eq_of_le hQleM).symm
        have hImageEq : QM.map qM = L := by
          calc
            QM.map qM = R.map qM :=
              congrArg (Subgroup.map qM) hRQM_eq.symm
            _ = L := Subgroup.map_comap_eq_self_of_surjective
              (QuotientGroup.mk'_surjective N₀) L
        simpa only [Qb] using hImageEq.le
  have hKMnormDM : KM ≤ Subgroup.normalizer (DM : Set M) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro d
    change (((d : M) : G) ∈ D) ↔
      (((k : M) : G) * ((d : M) : G) * ((k : M) : G)⁻¹ ∈ D)
    exact Subgroup.mem_normalizer_iff.mp (hKnormD hk) (((d : M) : G))
  have hKbNormDb : Kb ≤ Subgroup.normalizer (Db : Set Mbar) := by
    dsimp only [Kb, Db]
    exact (Subgroup.map_mono hKMnormDM).trans (DM.le_normalizer_map qM)
  have hQMDMKMtop : (QM ⊔ DM) ⊔ KM = ⊤ := by
    change ((Q.subgroupOf M ⊔ D.subgroupOf M) ⊔ K.subgroupOf M) = ⊤
    rw [← Subgroup.subgroupOf_sup hQleM hDM,
      ← Subgroup.subgroupOf_sup (sup_le hQleM hDM) hKM,
      semidirect_sup_eq_15 hQDsd, semidirect_sup_eq_15 hSigmaK,
      Subgroup.subgroupOf_self]
  have hQbDbKbtop : (Qb ⊔ Db) ⊔ Kb = ⊤ := by
    change ((QM.map qM ⊔ DM.map qM) ⊔ KM.map qM) = ⊤
    rw [← Subgroup.map_sup, ← Subgroup.map_sup, hQMDMKMtop,
      Subgroup.map_top_of_surjective qM
        (QuotientGroup.mk'_surjective N₀)]
  let Cb : Subgroup Mbar := centralizerWithin Qb Db
  letI : IsMulCommutative Qb := hQbComm
  have hCbQb : Cb ≤ Qb := inf_le_left
  have hQbNormCb : Qb ≤ Subgroup.normalizer (Cb : Set Mbar) := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hCbQb).mp
    infer_instance
  have hDbNormQb : Db ≤ Subgroup.normalizer (Qb : Set Mbar) :=
    Subgroup.le_normalizer_of_normal
  have hKbNormQb : Kb ≤ Subgroup.normalizer (Qb : Set Mbar) :=
    Subgroup.le_normalizer_of_normal
  have hDbNormCb : Db ≤ Subgroup.normalizer (Cb : Set Mbar) :=
    centralizerWithin_normalized_by_common_normalizer_15
      hDbNormQb Subgroup.le_normalizer
  have hKbNormCb : Kb ≤ Subgroup.normalizer (Cb : Set Mbar) :=
    centralizerWithin_normalized_by_common_normalizer_15
      hKbNormQb hKbNormDb
  have hCbNormal : Cb.Normal := by
    apply Subgroup.normalizer_eq_top_iff.mp
    apply top_unique
    rw [← hQbDbKbtop]
    exact sup_le (sup_le hQbNormCb hDbNormCb) hKbNormCb
  have hQbDreg : centralizerWithin Qb Db = ⊥ := by
    change Cb = ⊥
    by_contra hCbne
    have hCbEq : Cb = Qb :=
      hminQb.eq_of_normal_le hCbNormal hCbQb hCbne
    have hDfac : D ≤ Cfac := by
      intro d hd
      refine ⟨hDsigma hd, ?_⟩
      intro z hz
      let zM : M := ⟨z, hQleM hz⟩
      let dM : M := ⟨d, hDM hd⟩
      have hzQb : qM zM ∈ Qb := by
        change qM zM ∈ QM.map qM
        exact ⟨zM, hz, rfl⟩
      have hdDb : qM dM ∈ Db := by
        change qM dM ∈ DM.map qM
        exact ⟨dM, hd, rfl⟩
      have hzCb : qM zM ∈ Cb := by
        rw [hCbEq]
        exact hzQb
      have hcomm : qM zM * qM dM = qM dM * qM zM :=
        (hzCb.2 (qM dM) hdDb).symm
      have hcommOne : ⁅qM zM, qM dM⁆ = 1 :=
        commutatorElement_eq_one_iff_mul_comm.mpr hcomm
      change ⁅zM, dM⁆ ∈ N₀
      exact (QuotientGroup.eq_one_iff (N := N₀) ⁅zM, dM⁆).mp (by
        change qM ⁅zM, dM⁆ = 1
        rw [map_commutatorElement]
        exact hcommOne)
    have hDfit : D ≤ fittingWithin M := hDfac.trans hCfacFit
    have hQfit : Q ≤ fittingWithin M := by
      rw [← hfitJoin]
      exact le_sup_left
    apply (not_le_of_gt hfitLt)
    rw [← semidirect_sup_eq_15 hQDsd]
    exact sup_le hQfit hDfit
  have hDne : D ≠ ⊥ := by
    intro hDbot
    have hMsQ : Ms = Q := by
      rw [← semidirect_sup_eq_15 hQDsd, hDbot, sup_bot_eq]
    apply hnotNilMs
    rw [hMsQ]
    exact hQq.isNilpotent
  have hDMne : DM ≠ ⊥ := by
    intro hDMbot
    apply hDne
    calc
      D = DM.map M.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hDM).symm
      _ = ⊥ := by rw [hDMbot, Subgroup.map_bot]
  have hKMne : KM ≠ ⊥ := by
    intro hKMbot
    apply hKne
    calc
      K = KM.map M.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hKM).symm
      _ = ⊥ := by rw [hKMbot, Subgroup.map_bot]
  have hmap_ne_bot_of_le_actor :
      ∀ L : Subgroup M, L ≤ DM ⊔ KM → L ≠ ⊥ →
        L.map qM ≠ ⊥ := by
    intro L hL hLne hmapBot
    have hleKer : L ≤ qM.ker :=
      (Subgroup.map_eq_bot_iff L).mp hmapBot
    have hleN₀ : L ≤ N₀ := by
      change L ≤ (QuotientGroup.mk' N₀).ker at hleKer
      simpa only [QuotientGroup.ker_mk'] using hleKer
    apply hLne
    apply le_bot_iff.mp
    intro x hx
    exact hdisN₀DMKM.le_bot ⟨hleN₀ hx, hL hx⟩
  have hDbne : Db ≠ ⊥ := by
    simpa only [Db] using
      hmap_ne_bot_of_le_actor DM le_sup_left hDMne
  have hKbne : Kb ≠ ⊥ := by
    simpa only [Kb] using
      hmap_ne_bot_of_le_actor KM le_sup_right hKMne
  have hFrobDbKb : IsFrobeniusDecomposition
      (Db.subgroupOf (Db ⊔ Kb)) (Kb.subgroupOf (Db ⊔ Kb)) :=
    by
      rw [sup_comm Db Kb]
      exact hsemiregDbKb'.isFrobeniusDecomposition_sup
        hKbNormDb hDbne hKbne

  have hK₁M : K₁ ≤ M := hK₁K.trans hKM
  let K₁M : Subgroup M := K₁.subgroupOf M
  let K₁b : Subgroup Mbar := K₁M.map qM
  have hK₁MKM : K₁M ≤ KM := by
    intro x hx
    exact hK₁K hx
  have hK₁Mne : K₁M ≠ ⊥ := by
    intro hbot
    apply hK₁ne
    calc
      K₁ = K₁M.map M.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hK₁M).symm
      _ = ⊥ := by rw [hbot, Subgroup.map_bot]
  have hK₁bKb : K₁b ≤ Kb := by
    exact Subgroup.map_mono hK₁MKM
  have hK₁bne : K₁b ≠ ⊥ := by
    exact hmap_ne_bot_of_le_actor K₁M
      (hK₁MKM.trans le_sup_right) hK₁Mne
  have hsemiregDbK₁b : IsSemiregularConjugation Db K₁b := by
    intro k hk d hfix
    let kK : Kb := ⟨(k : Mbar), hK₁bKb k.property⟩
    have hkK : kK ≠ 1 := by
      intro hkOne
      apply hk
      apply Subtype.ext
      exact congrArg (fun x : Kb ↦ (x : Mbar)) hkOne
    exact hsemiregDbKb' kK hkK d hfix
  have hK₁bNormDb : K₁b ≤ Subgroup.normalizer (Db : Set Mbar) :=
    hK₁bKb.trans hKbNormDb
  have hFrobDbK₁b : IsFrobeniusDecomposition
      (Db.subgroupOf (Db ⊔ K₁b))
      (K₁b.subgroupOf (Db ⊔ K₁b)) :=
    by
      rw [sup_comm Db K₁b]
      exact hsemiregDbK₁b.isFrobeniusDecomposition_sup
        hK₁bNormDb hDbne hK₁bne
  have hqM_inj_of_le_actor :
      ∀ L : Subgroup M, L ≤ DM ⊔ KM →
        Function.Injective (qM.subgroupMap L) := by
    intro L hL
    rw [← MonoidHom.ker_eq_bot_iff, Subgroup.ker_subgroupMap,
      QuotientGroup.ker_mk', Subgroup.subgroupOf_eq_bot]
    exact hdisN₀DMKM.mono_right hL
  let eKM : KM ≃* KM.map qM :=
    MulEquiv.ofBijective (qM.subgroupMap KM)
      ⟨hqM_inj_of_le_actor KM le_sup_right,
        qM.subgroupMap_surjective KM⟩
  let eK₁M : K₁M ≃* K₁M.map qM :=
    MulEquiv.ofBijective (qM.subgroupMap K₁M)
      ⟨hqM_inj_of_le_actor K₁M
          (hK₁MKM.trans le_sup_right),
        qM.subgroupMap_surjective K₁M⟩
  have hKbCardK : Nat.card Kb = Nat.card K := by
    calc
      Nat.card Kb = Nat.card (KM.map qM) := rfl
      _ = Nat.card KM := (Nat.card_congr eKM.toEquiv).symm
      _ = Nat.card K :=
        MathlibSupport.natCard_subgroupOf_eq hKM
  have hK₁bCardK₁ : Nat.card K₁b = Nat.card K₁ := by
    calc
      Nat.card K₁b = Nat.card (K₁M.map qM) := rfl
      _ = Nat.card K₁M := (Nat.card_congr eK₁M.toEquiv).symm
      _ = Nat.card K₁ :=
        MathlibSupport.natCard_subgroupOf_eq hK₁M

  have hKsM : Ks ≤ M := hKsQ.trans hQleM
  let KsM : Subgroup M := Ks.subgroupOf M
  let Ksb : Subgroup Mbar := KsM.map qM
  have hKsbne : Ksb ≠ ⊥ := by
    intro hbot
    have hleKer : KsM ≤ qM.ker :=
      (Subgroup.map_eq_bot_iff KsM).mp (by
        simpa only [Ksb] using hbot)
    have hleN₀ : KsM ≤ N₀ := by
      change KsM ≤ (QuotientGroup.mk' N₀).ker at hleKer
      simpa only [QuotientGroup.ker_mk'] using hleKer
    apply hnotKsQ₀
    intro x hx
    exact hleN₀
      (show (⟨x, hKsM hx⟩ : M) ∈ KsM from hx)
  have hKsbCardDvd : Nat.card Ksb ∣ q := by
    calc
      Nat.card Ksb ∣ Nat.card KsM := by
        exact Subgroup.card_map_dvd KsM qM
      _ = Nat.card Ks :=
        MathlibSupport.natCard_subgroupOf_eq hKsM
      _ = q := rfl
  have hKsbCard : Nat.card Ksb = q :=
    (hqPrime.eq_one_or_self_of_dvd _ hKsbCardDvd).resolve_left
      (fun hcard ↦ hKsbne (Subgroup.card_eq_one.mp hcard))

  have hcentralizerQ_of_Ms :
      ∀ R : Subgroup G, centralizerWithin Ms R = Ks →
        centralizerWithin Q R = Ks := by
    intro R hcent
    apply le_antisymm
    · intro x hx
      exact hcent.le ⟨hQleMs hx.1, hx.2⟩
    · intro x hx
      have hxMs : x ∈ centralizerWithin Ms R := hcent.symm.le hx
      exact ⟨hKsQ hx, hxMs.2⟩
  have hcentralizerQM_subgroupOf :
      ∀ (R C : Subgroup G) (hRM : R ≤ M) (hCM : C ≤ M),
        centralizerWithin Q R = C →
          centralizerWithin QM (R.subgroupOf M) =
            C.subgroupOf M := by
    intro R C hRM hCM hcent
    ext x
    constructor
    · intro hx
      have hxG : ((x : M) : G) ∈ centralizerWithin Q R := by
        refine ⟨hx.1, ?_⟩
        intro y hy
        let yM : M := ⟨y, hRM hy⟩
        exact congrArg Subtype.val (hx.2 yM hy)
      exact hcent.le hxG
    · intro hx
      have hxG : ((x : M) : G) ∈ centralizerWithin Q R :=
        hcent.symm.le hx
      refine ⟨hxG.1, ?_⟩
      intro y hy
      apply Subtype.ext
      exact hxG.2 ((y : M) : G) hy
  have hcentMsK : centralizerWithin Ms K = Ks := by rfl
  have hcentQK : centralizerWithin Q K = Ks :=
    hcentralizerQ_of_Ms K hcentMsK
  have hcentQK₁ : centralizerWithin Q K₁ = Ks :=
    hcentralizerQ_of_Ms K₁ hcentK₁
  have hcentQMKM : centralizerWithin QM KM = KsM := by
    simpa only [KM, KsM] using
      hcentralizerQM_subgroupOf K Ks hKM hKsM hcentQK
  have hcentQMK₁M : centralizerWithin QM K₁M = KsM := by
    simpa only [K₁M, KsM] using
      hcentralizerQM_subgroupOf K₁ Ks hK₁M hKsM hcentQK₁
  have hcopN₀K₁M : Nat.Coprime (Nat.card N₀) (Nat.card K₁M) :=
    hcopN₀KM.coprime_dvd_right
      (Subgroup.card_dvd_of_le hK₁MKM)
  letI : IsSolvable M := hsolM
  letI : IsSolvable KM := isSolvable_subgroup_of_isSolvable KM
  letI : IsSolvable K₁M := isSolvable_subgroup_of_isSolvable K₁M
  have hmapCentK :
      (centralizerWithin QM KM).map qM =
        centralizerWithin Qb Kb := by
    simpa only [qM, Qb, Kb] using
      (map_centralizerWithin_quotient_eq_of_coprime_of_solvable_right
        (N := N₀) (Y := QM) (R := KM) hN₀QM hcopN₀KM)
  have hmapCentK₁ :
      (centralizerWithin QM K₁M).map qM =
        centralizerWithin Qb K₁b := by
    simpa only [qM, Qb, K₁b] using
      (map_centralizerWithin_quotient_eq_of_coprime_of_solvable_right
        (N := N₀) (Y := QM) (R := K₁M) hN₀QM hcopN₀K₁M)
  have hcentQbKb : centralizerWithin Qb Kb = Ksb := by
    calc
      centralizerWithin Qb Kb =
          (centralizerWithin QM KM).map qM := hmapCentK.symm
      _ = Ksb := by rw [hcentQMKM]
  have hcentQbK₁b : centralizerWithin Qb K₁b = Ksb := by
    calc
      centralizerWithin Qb K₁b =
          (centralizerWithin QM K₁M).map qM := hmapCentK₁.symm
      _ = Ksb := by rw [hcentQMK₁M]
  have hcentQbKbCard : Nat.card (centralizerWithin Qb Kb) = q := by
    rw [hcentQbKb]
    exact hKsbCard
  have hcentQbK₁bCard : Nat.card (centralizerWithin Qb K₁b) = q := by
    rw [hcentQbK₁b]
    exact hKsbCard

  have hcopQK : Nat.Coprime (Nat.card Q) (Nat.card K) :=
    hcopMsK.coprime_dvd_left (Subgroup.card_dvd_of_le hQleMs)
  have hcopQKM : Nat.Coprime (Nat.card Q) (Nat.card KM) := by
    simpa only [KM, MathlibSupport.natCard_subgroupOf_eq hKM] using hcopQK
  have hcopQDM : Nat.Coprime (Nat.card Q) (Nat.card DM) :=
    hQpi.coprime_compl hDMpi
  have hcopQDMKM :
      Nat.Coprime (Nat.card Q) (Nat.card (DM ⊔ KM : Subgroup M)) := by
    rw [hDMKMcard]
    exact hcopQDM.mul_right hcopQKM
  have hQbCardDvdQ : Nat.card Qb ∣ Nat.card Q := by
    calc
      Nat.card Qb ∣ Nat.card QM := by
        exact Subgroup.card_map_dvd QM qM
      _ = Nat.card Q :=
        MathlibSupport.natCard_subgroupOf_eq hQleM
  have hmapActor : (DM ⊔ KM).map qM = Db ⊔ Kb := by
    rw [Subgroup.map_sup]
  have hDbKbCardDvd :
      Nat.card (Db ⊔ Kb : Subgroup Mbar) ∣
        Nat.card (DM ⊔ KM : Subgroup M) := by
    rw [← hmapActor]
    exact Subgroup.card_map_dvd (DM ⊔ KM) qM
  have hcopQbDbKb :
      Nat.Coprime (Nat.card Qb) (Nat.card (Db ⊔ Kb : Subgroup Mbar)) :=
    (hcopQDMKM.coprime_dvd_left hQbCardDvdQ).coprime_dvd_right
      hDbKbCardDvd
  have hDbK₁bLe : Db ⊔ K₁b ≤ Db ⊔ Kb :=
    sup_le le_sup_left (hK₁bKb.trans le_sup_right)
  have hcopQbDbK₁b :
      Nat.Coprime (Nat.card Qb)
        (Nat.card (Db ⊔ K₁b : Subgroup Mbar)) :=
    hcopQbDbKb.coprime_dvd_right
      (Subgroup.card_dvd_of_le hDbK₁bLe)
  have hDbKbNormQb :
      Db ⊔ Kb ≤ Subgroup.normalizer (Qb : Set Mbar) :=
    Subgroup.le_normalizer_of_normal
  have hDbK₁bNormQb :
      Db ⊔ K₁b ≤ Subgroup.normalizer (Qb : Set Mbar) :=
    Subgroup.le_normalizer_of_normal
  have hQbSol : IsSolvable Qb :=
    _root_.isSolvable_of_comm (fun a b ↦ mul_comm' a b)
  have hFixKb : Nat.card Qb =
      Nat.card (centralizerWithin Qb Kb) ^ Nat.card Kb :=
    (Frobenius_Wielandt_fixpoint hFrobDbKb hDbKbNormQb
      hcopQbDbKb hQbSol).2.2 hQbDreg
  have hFixK₁b : Nat.card Qb =
      Nat.card (centralizerWithin Qb K₁b) ^ Nat.card K₁b :=
    (Frobenius_Wielandt_fixpoint hFrobDbK₁b hDbK₁bNormQb
      hcopQbDbK₁b hQbSol).2.2 hQbDreg
  have hKbCardK₁b : Nat.card Kb = Nat.card K₁b := by
    have hbaseTwo : 2 ≤ Nat.card (centralizerWithin Qb Kb) := by
      rw [hcentQbKbCard]
      exact hqPrime.two_le
    exact Nat.pow_right_injective hbaseTwo (by
      calc
        Nat.card (centralizerWithin Qb Kb) ^ Nat.card Kb =
            Nat.card Qb := hFixKb.symm
        _ = Nat.card (centralizerWithin Qb K₁b) ^ Nat.card K₁b :=
          hFixK₁b
        _ = Nat.card (centralizerWithin Qb Kb) ^ Nat.card K₁b := by
          rw [hcentQbKb, hcentQbK₁b])
  have hKcardK₁ : Nat.card K = Nat.card K₁ := by
    calc
      Nat.card K = Nat.card Kb := hKbCardK.symm
      _ = Nat.card K₁b := hKbCardK₁b
      _ = Nat.card K₁ := hK₁bCardK₁
  have hpPrime' : Nat.Prime p := by
    change Nat.Prime (Nat.card K)
    rw [hKcardK₁]
    exact hK₁prime
  have hKbPrime : Nat.Prime (Nat.card Kb) := by
    rw [hKbCardK]
    simpa only [p] using hpPrime'
  have hQbarCard' : Nat.card Qbar = q ^ p := by
    calc
      Nat.card Qbar = Nat.card Qb := Nat.card_congr eQ.toEquiv
      _ = Nat.card (centralizerWithin Qb Kb) ^ Nat.card Kb := hFixKb
      _ = q ^ p := by rw [hcentQbKbCard, hKbCardK]

  have hqQb : q ∣ Nat.card Qb := by
    rw [← hcentQbKbCard]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hDbKbPrime : IsPPrimeSubgroup q (Db ⊔ Kb) :=
    hcopQbDbKb.coprime_dvd_left hqQb
  letI : IsSolvable Mbar :=
    isSolvable_quotient_of_isSolvable N₀
  letI : IsSolvable ↑(Db ⊔ Kb) :=
    isSolvable_subgroup_of_isSolvable (Db ⊔ Kb)
  letI : (Db.subgroupOf (Db ⊔ Kb)).Normal :=
    hFrobDbKb.kernel_normal
  have hDderivedCent :
      ⁅Db, Db⁆ ≤ centralizerWithin Db Qb := by
    exact Frobenius_prime_cent_prime
      (Db ⊔ Kb) Db Kb Qb
      le_sup_left le_sup_right hFrobDbKb.isComplement hKbPrime
      (centralizerWithin_eq_bot_of_semiregular_actor_15
        hsemiregDbKb' hKbne)
      hQbElem hDbKbNormQb hDbKbPrime hcentQbKbCard

  have hmapDcomm : ⁅DM, DM⁆.map M.subtype = ⁅D, D⁆ := by
    rw [Subgroup.map_commutator,
      Subgroup.map_subgroupOf_eq_of_le hDM]
  have hDcommFit : ⁅D, D⁆ ≤ fittingWithin M := by
    intro x hx
    have hxD : x ∈ D := Subgroup.commutator_le_self D hx
    have hxMs : x ∈ Ms := hDsigma hxD
    let xM : M := ⟨x, hMsM hxMs⟩
    have hxDMcomm : xM ∈ ⁅DM, DM⁆ := by
      have hxMap : x ∈ ⁅DM, DM⁆.map M.subtype := by
        rw [hmapDcomm]
        exact hx
      rcases hxMap with ⟨y, hy, hyx⟩
      have hyxM : y = xM := Subtype.ext hyx
      exact hyxM ▸ hy
    have hxDbcomm : qM xM ∈ ⁅Db, Db⁆ := by
      have hxMap : qM xM ∈ ⁅DM, DM⁆.map qM :=
        ⟨xM, hxDMcomm, rfl⟩
      simpa only [Subgroup.map_commutator, Db] using hxMap
    have hxCent : qM xM ∈ centralizerWithin Db Qb :=
      hDderivedCent hxDbcomm
    have hxFactor : x ∈ factorCentralizerWithin Ms Q Q₀ := by
      refine ⟨hxMs, ?_⟩
      intro z hz
      let zM : M := ⟨z, hQleM hz⟩
      have hzQb : qM zM ∈ Qb := by
        change qM zM ∈ QM.map qM
        exact ⟨zM, hz, rfl⟩
      have hcommOne : ⁅qM zM, qM xM⁆ = 1 :=
        commutatorElement_eq_one_iff_mul_comm.mpr
          (hxCent.2 (qM zM) hzQb)
      change ⁅zM, xM⁆ ∈ N₀
      exact (QuotientGroup.eq_one_iff (N := N₀) ⁅zM, xM⁆).mp (by
        change qM ⁅zM, xM⁆ = 1
        rw [map_commutatorElement]
        exact hcommOne)
    change (x : G) ∈ (fittingWithin M : Set G)
    rw [← hfactorEq]
    exact hxFactor

  have hQfit : Q ≤ fittingWithin M := by
    rw [← hfitJoin]
    exact le_sup_left
  let Qs : Subgroup Ms := Q.subgroupOf Ms
  let Ds : Subgroup Ms := D.subgroupOf Ms
  let Fs : Subgroup Ms := (fittingWithin M).subgroupOf Ms
  letI : Qs.Normal := by
    simpa only [Qs] using hQDsd.2.2.1
  letI : Fs.Normal := by
    apply Subgroup.normal_subgroupOf_of_le_normalizer
    exact hMsM.trans (fittingWithin_le_normalizer M)
  have hQsFs : Qs ≤ Fs := by
    intro x hx
    exact hQfit hx
  have hDsCommFs : ⁅Ds, Ds⁆ ≤ Fs := by
    apply (Subgroup.map_le_map_iff_of_injective
      Ms.subtype_injective).mp
    rw [Subgroup.map_commutator,
      Subgroup.map_subgroupOf_eq_of_le hDsigma,
      Subgroup.map_subgroupOf_eq_of_le hfitLt.le]
    exact hDcommFit
  have hQsQs : ⁅Qs, Qs⁆ ≤ Fs :=
    (Subgroup.commutator_le_left Qs Qs).trans hQsFs
  have hQsDs : ⁅Qs, Ds⁆ ≤ Fs :=
    (Subgroup.commutator_le_left Qs Ds).trans hQsFs
  have hDsQs : ⁅Ds, Qs⁆ ≤ Fs :=
    (Subgroup.commutator_le_right Ds Qs).trans hQsFs
  have hQsSup : ⁅Qs, Qs ⊔ Ds⁆ ≤ Fs :=
    commutator_sup_le_of_normal hQsQs hQsDs
  have hDsSup : ⁅Ds, Qs ⊔ Ds⁆ ≤ Fs :=
    commutator_sup_le_of_normal hDsQs hDsCommFs
  have hSupQs : ⁅Qs ⊔ Ds, Qs⁆ ≤ Fs := by
    rw [Subgroup.commutator_comm]
    exact hQsSup
  have hSupDs : ⁅Qs ⊔ Ds, Ds⁆ ≤ Fs := by
    rw [Subgroup.commutator_comm]
    exact hDsSup
  have hSupComm : ⁅Qs ⊔ Ds, Qs ⊔ Ds⁆ ≤ Fs :=
    commutator_sup_le_of_normal hSupQs hSupDs
  have hQsDsTop : Qs ⊔ Ds = ⊤ := by
    simpa only [Qs, Ds] using hQDsd.2.2.2.sup_eq_top
  have hcommMsFs : _root_.commutator Ms ≤ Fs := by
    change ⁅(⊤ : Subgroup Ms), ⊤⁆ ≤ Fs
    rw [← hQsDsTop]
    exact hSupComm
  have hderivedMsFit : derivedWithin Ms ≤ fittingWithin M := by
    change (_root_.commutator Ms).map Ms.subtype ≤ fittingWithin M
    calc
      (_root_.commutator Ms).map Ms.subtype ≤ Fs.map Ms.subtype :=
        Subgroup.map_mono hcommMsFs
      _ = fittingWithin M := by
        simpa only [Fs] using
          Subgroup.map_subgroupOf_eq_of_le hfitLt.le
  have hsecondFit : secondDerivedWithin M ≤ fittingWithin M := by
    change derivedWithin (derivedWithin M) ≤ fittingWithin M
    rw [← hSigmaDerived]
    exact hderivedMsFit
  have hSigmaSecond :
      derivedWithin Ms = secondDerivedWithin M := by
    rw [secondDerivedWithin, ← hSigmaDerived]

  have hpartnerFactor :
      factorCentralizerWithin Ms Ks Q₀ =
        (fittingWithin M : Set G) := by
    let Cp : Subgroup G :=
      factorCentralizerSubgroup_15
        (A := Ms) (Q := Ks) (N := Q₀)
        (hMsM.trans hMnormQ₀)
    have hCpMs : Cp ≤ Ms := by
      intro x hx
      exact hx.1
    have hfitCp : fittingWithin M ≤ Cp := by
      intro x hx
      have hxFactor : x ∈ factorCentralizerWithin Ms Q Q₀ := by
        change (x : G) ∈ (fittingWithin M : Set G) at hx
        rw [← hfactorEq] at hx
        exact hx
      exact ⟨hxFactor.1, fun z hz ↦ hxFactor.2 z (hKsQ hz)⟩
    have hMsNormCp : Ms ≤ Subgroup.normalizer (Cp : Set G) := by
      rw [Subgroup.le_normalizer_iff_commutator_le_right]
      calc
        ⁅Ms, Cp⁆ ≤ ⁅Ms, Ms⁆ :=
          Subgroup.commutator_mono le_rfl hCpMs
        _ ≤ derivedWithin Ms := Ms.map_subtype_commutator.ge
        _ = secondDerivedWithin M := hSigmaSecond
        _ ≤ fittingWithin M := hsecondFit
        _ ≤ Cp := hfitCp
    have hKnormMs : K ≤ Subgroup.normalizer (Ms : Set G) :=
      hKM.trans hMnormMs
    have hKnormKs : K ≤ Subgroup.normalizer (Ks : Set G) := by
      simpa only [Ks] using
        centralizerWithin_normalized_by_common_normalizer_15
          hKnormMs (Subgroup.le_normalizer :
            K ≤ Subgroup.normalizer (K : Set G))
    have hKnormCp : K ≤ Subgroup.normalizer (Cp : Set G) := by
      exact factorCentralizerSubgroup_normalized_15
        (A := Ms) (Q := Ks) (N := Q₀) (B := K)
        (hMsM.trans hMnormQ₀) hKnormMs hKnormKs hKnormQ₀
    have hCpM : Cp ≤ M := hCpMs.trans hMsM
    have hMnormCp : M ≤ Subgroup.normalizer (Cp : Set G) := by
      rw [← semidirect_sup_eq_15 hSigmaK]
      exact sup_le hMsNormCp hKnormCp
    have hCpNormal : (Cp.subgroupOf M).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hCpM).mpr
        hMnormCp

    let Cq : Subgroup G :=
      factorCentralizerSubgroup_15
        (A := Q) (Q := Cp) (N := Q₀) hQnormQ₀
    have hCpNormQ₀ : Cp ≤ Subgroup.normalizer (Q₀ : Set G) :=
      hCpM.trans hMnormQ₀
    have hCpQ₀comm : ⁅Cp, Q₀⁆ ≤ Q₀ :=
      Subgroup.le_normalizer_iff_commutator_le_right.mp hCpNormQ₀
    have hQ₀Cq : Q₀ ≤ Cq := by
      intro x hx
      refine ⟨hQ₀leQ hx, ?_⟩
      intro c hc
      exact hCpQ₀comm
        (Subgroup.commutator_mem_commutator hc hx)
    have hKsCpComm : ⁅Ks, Cp⁆ ≤ Q₀ := by
      rw [Subgroup.commutator_le]
      intro k hk c hc
      exact hc.2 k hk
    have hCpKsComm : ⁅Cp, Ks⁆ ≤ Q₀ := by
      rw [Subgroup.commutator_comm]
      exact hKsCpComm
    have hKsCq : Ks ≤ Cq := by
      intro k hk
      refine ⟨hKsQ hk, ?_⟩
      intro c hc
      exact hCpKsComm
        (Subgroup.commutator_mem_commutator hc hk)
    have hCqQ : Cq ≤ Q := by
      intro x hx
      exact hx.1
    have hCqM : Cq ≤ M := hCqQ.trans hQleM
    have hMnormCq : M ≤ Subgroup.normalizer (Cq : Set G) := by
      exact factorCentralizerSubgroup_normalized_15
        (A := Q) (Q := Cp) (N := Q₀) (B := M)
        hQnormQ₀ hMnormQ hMnormCp hMnormQ₀
    have hCqNormal : (Cq.subgroupOf M).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hCqM).mpr
        hMnormCq
    have hCqEq : Cq = Q := by
      rcases hminimal.2.2.2.2 Cq hQ₀Cq hCqQ hCqNormal with hCq | hCq
      · exfalso
        apply hnotKsQ₀
        rw [← hCq]
        exact hKsCq
      · exact hCq
    have hCpQcomm : ⁅Cp, Q⁆ ≤ Q₀ := by
      rw [Subgroup.commutator_le]
      intro c hc x hx
      have hxCq : x ∈ Cq := by
        rw [hCqEq]
        exact hx
      exact hxCq.2 c hc
    have hQCpComm : ⁅Q, Cp⁆ ≤ Q₀ := by
      rw [Subgroup.commutator_comm]
      exact hCpQcomm
    have hCpFit : Cp ≤ fittingWithin M := by
      intro x hx
      change (x : G) ∈ (fittingWithin M : Set G)
      rw [← hfactorEq]
      refine ⟨hCpMs hx, ?_⟩
      intro z hz
      exact hQCpComm
        (Subgroup.commutator_mem_commutator hz hx)
    change (Cp : Set G) = (fittingWithin M : Set G)
    exact congrArg (fun H : Subgroup G ↦ (H : Set G))
      (le_antisymm hCpFit hfitCp)
  have hambientFactor :
      factorCentralizerWithin M Q Q₀ =
        (fittingWithin M : Set G) := by
    let Ca : Subgroup G :=
      factorCentralizerSubgroup_15
        (A := M) (Q := Q) (N := Q₀) hMnormQ₀
    have hCaM : Ca ≤ M := by
      intro x hx
      exact hx.1
    have hFCa : fittingWithin M ≤ Ca := by
      intro x hx
      have hxFactor : x ∈ factorCentralizerWithin Ms Q Q₀ := by
        change (x : G) ∈ (fittingWithin M : Set G) at hx
        rw [← hfactorEq] at hx
        exact hx
      exact ⟨hMsM hxFactor.1, hxFactor.2⟩
    have hMnormCa : M ≤ Subgroup.normalizer (Ca : Set G) := by
      exact factorCentralizerSubgroup_normalized_15
        (A := M) (Q := Q) (N := Q₀) (B := M)
        hMnormQ₀ (Subgroup.le_normalizer :
          M ≤ Subgroup.normalizer (M : Set G))
        hMnormQ hMnormQ₀
    have hCaNormal : (Ca.subgroupOf M).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hCaM).mpr
        hMnormCa
    have hdis : Disjoint Ca K := by
      let CK : Subgroup K := Ca.subgroupOf K
      letI : Fact (Nat.card K).Prime :=
        ⟨by simpa only [p] using hpPrime'⟩
      rcases CK.eq_bot_or_eq_top_of_prime_card with hbot | htop
      · exact Subgroup.subgroupOf_eq_bot.mp (by
          simpa only [CK] using hbot)
      · have hKCa : K ≤ Ca := by
          exact Subgroup.subgroupOf_eq_top.mp (by
            simpa only [CK] using htop)
        have hQbCent : Qb ≤ centralizerWithin Qb Kb := by
          intro qb hqb
          refine ⟨hqb, ?_⟩
          intro kb hkb
          change qb ∈ QM.map qM at hqb
          change kb ∈ KM.map qM at hkb
          rcases hqb with ⟨x, hx, rfl⟩
          rcases hkb with ⟨y, hy, rfl⟩
          have hyCa : ((y : M) : G) ∈ Ca := hKCa hy
          have hcommN : ⁅x, y⁆ ∈ N₀ := by
            change ⁅((x : M) : G), ((y : M) : G)⁆ ∈ Q₀
            exact hyCa.2 ((x : M) : G) hx
          have hmul : qM x * qM y = qM y * qM x := by
            rw [← commutatorElement_eq_one_iff_mul_comm,
              ← map_commutatorElement]
            exact (QuotientGroup.eq_one_iff
              (N := N₀) ⁅x, y⁆).mpr hcommN
          exact hmul.symm
        have hQbKsb : Qb = Ksb := by
          calc
            Qb = centralizerWithin Qb Kb :=
              le_antisymm hQbCent inf_le_left
            _ = Ksb := hcentQbKb
        have hQbCard : Nat.card Qb = q := by
          rw [hQbKsb]
          exact hKsbCard
        have hQbPow : Nat.card Qb = q ^ p := by
          calc
            Nat.card Qb =
                Nat.card (centralizerWithin Qb Kb) ^ Nat.card Kb :=
              hFixKb
            _ = q ^ p := by
              rw [hcentQbKbCard, hKbCardK]
        have hpowEq : q ^ p = q := hQbPow.symm.trans hQbCard
        have hpowLt : q < q ^ p := by
          simpa using
            Nat.pow_lt_pow_right hqPrime.one_lt hpPrime'.one_lt
        exact ((ne_of_gt hpowLt) hpowEq).elim
    have hCaMs : Ca ≤ Ms :=
      normal_le_left_of_disjoint_right_of_coprime_sdprod_15
        hSigmaK hcopMsK hCaM hCaNormal hdis
    have hCaF : Ca ≤ fittingWithin M := by
      intro x hx
      change (x : G) ∈ (fittingWithin M : Set G)
      rw [← hfactorEq]
      exact ⟨hCaMs hx, hx.2⟩
    change (Ca : Set G) = (fittingWithin M : Set G)
    exact congrArg (fun H : Subgroup G ↦ (H : Set G))
      (le_antisymm hCaF hFCa)

  /- The final narrow-automorphism argument is exactly the last paragraph
  of the source proof. -/
  have hqBeta : q ∈ betaPrimes M := by
    by_contra hq
    have hcopDK : Nat.Coprime (Nat.card D) (Nat.card K) :=
      hcopMsK.coprime_dvd_left
        (Subgroup.card_dvd_of_le hDsigma)
    letI : Group.IsNilpotent D := hDnil
    have hDcomm : D ≤ ⁅K, D⁆ := by
      have hle :=
        le_commutator_sup_centralizerWithin_of_coprime
          hKnormD hcopDK
      rw [hDKreg, sup_bot_eq] at hle
      exact hle
    have hDderived : D ≤ derivedWithin (D ⊔ K) := by
      calc
        D ≤ ⁅K, D⁆ := hDcomm
        _ ≤ ⁅D ⊔ K, D ⊔ K⁆ :=
          Subgroup.commutator_mono le_sup_right le_sup_left
        _ ≤ derivedWithin (D ⊔ K) :=
          (D ⊔ K).map_subtype_commutator.ge
    have hQsylowM' := hQsylowM
    rcases hQsylowM' with ⟨P, hQP⟩
    have hQsubM : Q.subgroupOf M = (P : Subgroup M) := by
      rw [hQP]
      exact Subgroup.comap_map_eq_self_of_injective
        M.subtype_injective (P : Subgroup M)
    have hPnormal : (P : Subgroup M).Normal := by
      rw [← hQsubM]
      exact hQnormalM
    letI : Unique (Sylow q M) :=
      Sylow.unique_of_normal P hPnormal
    have hPnarrow :
        Section05.IsNarrow q (⊤ : Subgroup P) := by
      by_contra hPnot
      apply hq
      refine ⟨hqPrime, ?_⟩
      intro S
      have hSP : S = P := Subsingleton.elim S P
      subst S
      exact hPnot
    let eQP : Q ≃* P :=
      (Subgroup.subgroupOfEquivOfLe hQleM).symm.trans
        (MulEquiv.subgroupCongr hQsubM)
    have hQnarrow :
        Section05.IsNarrow q (⊤ : Subgroup Q) := by
      have hiff :=
        Section05.isNarrow_map_mulEquiv_iff
          (p := q) eQP (⊤ : Subgroup Q)
      apply hiff.mp
      simpa only [Subgroup.map_top_of_surjective
        eQP.toMonoidHom eQP.surjective] using hPnarrow
    let H : Subgroup G := D ⊔ K
    have hHM : H ≤ M :=
      sup_le (hDsigma.trans hMsM) hKM
    have hHnormQ : H ≤ Subgroup.normalizer (Q : Set G) :=
      hHM.trans hMnormQ
    let i : H →* Subgroup.normalizer (Q : Set G) :=
      Subgroup.inclusion hHnormQ
    let rho : H →* MulAut Q :=
      Q.normalizerMonoidHom.comp i
    let A : Subgroup (MulAut Q) := rho.range
    have hHsol : IsSolvable H :=
      isSolvable_of_le_15 hsolM hHM
    have hAsol : IsSolvable A := by
      letI : IsSolvable H := hHsol
      exact solvable_of_surjective
        rho.rangeRestrict_surjective
    have hAodd : Odd (Nat.card A) :=
      (mFT_odd H).of_dvd_nat
        (by simpa only [A] using Subgroup.card_range_dvd rho)
    obtain ⟨_, hAquotComm, _⟩ :=
      Section05.Aut_narrow hQq (mFT_odd Q) A
        hQnarrow hAsol hAodd
    have hAder : IsPGroup q (_root_.commutator A) := by
      apply pCore_isPGroup.to_le
      exact Subgroup.Normal.quotient_commutative_iff_commutator_le.mp
        hAquotComm
    have hcopqD : Nat.Coprime q (Nat.card D) := by
      simpa only [DM, MathlibSupport.natCard_subgroupOf_eq hDM] using
        hcopQDM.coprime_dvd_left hqQ
    have hcopqK : Nat.Coprime q (Nat.card K) :=
      hcopQK.coprime_dvd_left hqQ
    have hHcard : Nat.card H = Nat.card D * Nat.card K := by
      simpa only [H] using hDKcard
    have hcopqH : Nat.Coprime q (Nat.card H) := by
      rw [hHcard]
      exact hcopqD.mul_right hcopqK
    have hqH : ¬q ∣ Nat.card H :=
      hqPrime.coprime_iff_not_dvd.mp hcopqH
    have hAdvdH : Nat.card A ∣ Nat.card H := by
      simpa only [A] using Subgroup.card_range_dvd rho
    have hqA : ¬q ∣ Nat.card A :=
      fun hqAdvd ↦ hqH (hqAdvd.trans hAdvdH)
    have hAderBot : _root_.commutator A = ⊥ :=
      subgroup_eq_bot_of_isPGroup_of_not_dvd_natCard
        (_root_.commutator A) hAder hqA
    have hmapDer :
        (_root_.commutator H).map rho =
          (_root_.commutator A).map A.subtype := by
      calc
        (_root_.commutator H).map rho =
            ⁅rho.range, rho.range⁆ :=
          map_commutator_eq H rho
        _ = (_root_.commutator A).map A.subtype := by
          simpa only [A] using
            (Subgroup.map_subtype_commutator A).symm
    have hHderMapBot :
        (_root_.commutator H).map rho = ⊥ := by
      calc
        (_root_.commutator H).map rho =
            (_root_.commutator A).map A.subtype := hmapDer
        _ = ⊥ := by rw [hAderBot, Subgroup.map_bot]
    have hHderKer : _root_.commutator H ≤ rho.ker := by
      rw [← Subgroup.map_eq_bot_iff]
      exact hHderMapBot
    have hcentQ :
        derivedWithin H ≤ centralizerWithin M Q := by
      intro x hx
      rcases hx with ⟨y, hy, rfl⟩
      have hyKer : y ∈ rho.ker := hHderKer hy
      change i y ∈ Q.normalizerMonoidHom.ker at hyKer
      rw [Subgroup.normalizerMonoidHom_ker] at hyKer
      change ((y : H) : G) ∈
        Subgroup.centralizer (Q : Set G) at hyKer
      refine ⟨hHM y.property, ?_⟩
      intro z hz
      exact Subgroup.mem_centralizer_iff.mp hyKer z hz
    have hDcentQ : D ≤ centralizerWithin M Q := by
      simpa only [H] using hDderived.trans hcentQ
    have hQQ₀ : Q ≤ Q₀ := by
      intro x hx
      refine ⟨hx, ?_⟩
      intro d hd
      exact ((hDcentQ hd).2 x hx).symm
    exact (not_le_of_gt hQ₀ltQ) hQQ₀

  exact
    { typeP1 := hP1
      sigma_K_sdprod := hSigmaK
      sigma_eq_derived := hSigmaDerived
      card_K_prime := hpPrime'
      card_partner_prime := hqPrime
      partner_prime_in_Fcore := hqF
      partner_prime_beta := hqBeta
      pcore_sylow := by
        simpa only [Ks, q, Q] using hQsylowM
      D_nilpotent := hDnil
      Q0_normal_M := by
        simpa only [Ks, D, q, Q, Q₀] using hQ₀normalM
      Q0_normal_Q := by
        simpa only [Ks, D, q, Q, Q₀] using hQ₀normalQ
      quotient_minimal_normal := by
        simpa only [Ks, D, q, Q, Q₀] using hminimal
      quotient_elementary_abelian := by
        simpa only [Ks, D, q, Q, Q₀, Qbar] using hQbarElem
      quotient_card := by
        simpa only [p, Ks, D, q, Q, Q₀, Qbar] using hQbarCard'
      sigma_derived_eq_second := hSigmaSecond
      secondDerived_le_fitting := hsecondFit
      fitting_descriptions :=
        { pcore_join_centralizer := by
            simpa only [Ks, q, Q] using hfitJoin
          factor_centralizer := by
            simpa only [Ks, D, q, Q, Q₀] using hambientFactor
          partner_factor_centralizer := by
            simpa only [Ms, Ks, D, q, Q, Q₀] using hpartnerFactor }
      fitting_lt_sigma := hfitLt }

/-- `BGsection15.v: Fcore_structure`, Bender--Glauberman Theorem 15.2. -/
theorem Fcore_structure
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G)) :
    FCoreStructure M := by
  classical
  have hMsol : IsSolvable M := mmax_sol hM
  letI : IsSolvable M := hMsol
  have hFle : Fitting_core M ≤ sigmaCore M :=
    Fcore_sub_Msigma hM
  have hSigmaDer : sigmaCore M ≤ derivedWithin M :=
    Msigma_der1 hM
  have hDerLt : derivedWithin M < M := by
    letI : Nontrivial M :=
      M.nontrivial_iff_ne_bot.mpr (mmax_neq1 hM)
    let D : Subgroup M := _root_.commutator M
    have hDtop : D < (⊤ : Subgroup M) := by
      simpa only [D] using
        (IsSolvable.commutator_lt_top_of_nontrivial M)
    have hmap :=
      (Subgroup.map_lt_map_iff_of_injective M.subtype_injective).2 hDtop
    simpa only [derivedWithin, D, ← MonoidHom.range_eq_map,
      M.range_subtype] using hmap
  have hFne : Fitting_core M ≠ ⊥ := by
    by_cases heq : Fitting_core M = sigmaCore M
    · rw [heq]
      exact Msigma_neq1 hM
    · obtain ⟨K, hKM, hHallK⟩ :=
        Submission.OddOrder.MathlibSupport.exists_ambient_isHall_of_isSolvable
          (K := M) hMsol (kappaPrimes M)
      let q := Nat.card (kappaCentralizer M K)
      have hSigmaSol : IsSolvable (sigmaCore M) :=
        isSolvable_of_le_15 hMsol (sigmaCore_le M)
      obtain ⟨D, hDsigma, hHallD⟩ :=
        Submission.OddOrder.MathlibSupport.exists_ambient_isHall_of_isSolvable
          (K := sigmaCore M) hSigmaSol ({q} : Set ℕ)ᶜ
      have hs := fcore_nonnilpotent_structure hM
        hKM hHallK heq
        hDsigma (by simpa [q] using hHallD)
      intro hFbot
      have hmem := hs.partner_prime_in_Fcore
      have hcard : Nat.card (Fitting_core M) = 1 :=
        Subgroup.card_eq_one.mpr hFbot
      rw [hcard] at hmem
      exact hmem.1.not_dvd_one hmem.2
  exact
    { Fcore_ne_bot := hFne
      Fcore_le_sigma := hFle
      sigma_le_derived := hSigmaDer
      derived_lt := hDerLt
      nonnilpotent := by
        intro K D hKM hHallK hne hDsigma hHallD
        exact fcore_nonnilpotent_structure
          hM hKM hHallK hne hDsigma hHallD }

/-! ## Corollary 15.3 -/

/-- A sigma-subgroup of the normalizer in Proposition 14.2 lies in its
sigma-factor.  This is the elementwise projection argument implicit in the
MathComp direct-product decomposition. -/
private theorem sigma_subgroup_le_pTypeCentralizer_of_le_normalizer_15_3
    {M K S : Subgroup G}
    (hKM : K ≤ M)
    (hHallK : IsHall (kappaPrimes M) (K.subgroupOf M))
    (hs : PTypeStructure M K)
    (hSN : S ≤ normalizerWithin M K)
    (hSsigma : IsPiNumber (sigmaPrimes M) (Nat.card S)) :
    S ≤ pTypeCentralizer M K := by
  have hKkappa : IsPiNumber (kappaPrimes M) (Nat.card K) := by
    simpa only [MathlibSupport.natCard_subgroupOf_eq hKM] using
      hHallK.isPiNumber_card
  have hKsigmaCompl :
      IsPiNumber (sigmaPrimes M)ᶜ (Nat.card K) :=
    hKkappa.mono (kappa_sigma' M)
  intro x hxS
  let w : normalizerWithin M K := ⟨x, hSN hxS⟩
  let hdir := hs.normalizer_direct
  have hwOrder : orderOf w ∣ Nat.card S := by
    simpa only [w, Subgroup.orderOf_mk] using
      S.orderOf_dvd_natCard hxS
  have hleftSigma :
      IsPiNumber (sigmaPrimes M)
        (orderOf (hdir.leftProjection w)) := by
    exact hSsigma.of_dvd
      ((orderOf_map_dvd hdir.leftProjection w).trans hwOrder)
  have hleftSigmaCompl :
      IsPiNumber (sigmaPrimes M)ᶜ
        (orderOf (hdir.leftProjection w)) := by
    exact hKsigmaCompl.of_dvd
      (orderOf_dvd_natCard (hdir.leftProjection w))
  have hleftOrder : orderOf (hdir.leftProjection w) = 1 :=
    Nat.eq_one_of_dvd_coprimes
      (hleftSigma.coprime_compl hleftSigmaCompl) dvd_rfl dvd_rfl
  have hproj : hdir.leftProjection w = 1 :=
    orderOf_eq_one_iff.mp hleftOrder
  have hwb : w = hdir.rightEmbedding (hdir.rightProjection w) := by
    calc
      w = hdir.mulEquiv
          (hdir.leftProjection w, hdir.rightProjection w) :=
        (hdir.mulEquiv_projections w).symm
      _ = hdir.mulEquiv (1, hdir.rightProjection w) := by rw [hproj]
      _ = hdir.rightEmbedding (hdir.rightProjection w) :=
        hdir.mulEquiv_apply_right (hdir.rightProjection w)
  change (w : G) ∈ pTypeCentralizer M K
  rw [hwb]
  exact (hdir.rightProjection w).property

/-- Complementary Hall factors, with the first normal, give the internal
semidirect product used in Corollary 15.3. -/
private theorem normal_complementary_hall_sdprod_15_3
    {A B C : Subgroup G} {pi : Set ℕ}
    (hAC : A ≤ C) (hBC : B ≤ C)
    (hAnormal : (A.subgroupOf C).Normal)
    (hAHall : IsHall pi (A.subgroupOf C))
    (hBHall : IsHall piᶜ (B.subgroupOf C)) :
    IsInternalSemidirectProductIn A B C := by
  let AC : Subgroup C := A.subgroupOf C
  let BC : Subgroup C := B.subgroupOf C
  have hcopAB : Nat.Coprime (Nat.card AC) (Nat.card BC) :=
    hAHall.isPiNumber_card.coprime_compl hBHall.isPiNumber_card
  have hBCindexPi : IsPiNumber pi BC.index := by
    simpa only [compl_compl] using hBHall.isPiNumber_index
  have hcopIndex : Nat.Coprime BC.index AC.index :=
    hBCindexPi.coprime_compl hAHall.isPiNumber_index
  have hAcard_dvd_Bindex : Nat.card AC ∣ BC.index := by
    apply hcopAB.dvd_of_dvd_mul_left
    rw [BC.card_mul_index]
    exact AC.card_subgroup_dvd_card
  have hBindex_dvd_Acard : BC.index ∣ Nat.card AC := by
    apply hcopIndex.dvd_of_dvd_mul_right
    rw [AC.card_mul_index]
    exact BC.index_dvd_card
  have hAcard : Nat.card AC = BC.index :=
    Nat.dvd_antisymm hAcard_dvd_Bindex hBindex_dvd_Acard
  have hcard : Nat.card AC * Nat.card BC = Nat.card C := by
    rw [hAcard, BC.index_mul_card]
  have hdis : Disjoint AC BC :=
    Subgroup.disjoint_of_coprime_natCard hcopAB
  exact ⟨hAC, hBC, hAnormal,
    Subgroup.isComplement'_of_card_mul_and_disjoint hcard hdis⟩

/-- In a finite nilpotent group, every Hall subgroup lies in the corresponding
prime core.  This is the Hall-uniqueness calculation used in Corollary 15.3. -/
private theorem hall_le_piCore_of_isNilpotent_15_3
    {K : Type u} [Group K] [Finite K] [Group.IsNilpotent K]
    {pi : Set ℕ} {H : Subgroup K} (hH : IsHall pi H) :
    H ≤ piCore pi K := by
  calc
    H = (sylowSup H).map H.subtype := by
      rw [sylowSup_eq_top]
      exact H.range_subtype.symm.trans
        (MonoidHom.range_eq_map H.subtype)
    _ = ⨆ r : {r : ℕ // r.Prime},
        ((Classical.choice
          (Sylow.nonempty (p := (r : ℕ)) (G := H)) : Sylow r H) :
          Subgroup H).map H.subtype := by
      rw [sylowSup, Subgroup.map_iSup]
    _ ≤ piCore pi K := by
      apply iSup_le
      intro r
      letI : Fact (r : ℕ).Prime := ⟨r.property⟩
      let R : Sylow (r : ℕ) H := Classical.choice Sylow.nonempty
      by_cases hRbot : (R : Subgroup H) = ⊥
      · simp [R, hRbot]
      have hrR : (r : ℕ) ∣ Nat.card R :=
        R.isPGroup'.card_eq_or_dvd.resolve_left
          (fun hcard ↦ hRbot (Subgroup.card_eq_one.mp hcard))
      have hrPi : (r : ℕ) ∈ pi :=
        hH.isPiNumber_card r.property
          (hrR.trans (R : Subgroup H).card_subgroup_dvd_card)
      have hmapR : IsPGroup (r : ℕ)
          ((R : Subgroup H).map H.subtype) := R.isPGroup'.map H.subtype
      exact (hmapR.le_pCore_of_isNilpotent).trans
        (le_piCore (by infer_instance)
          (pCore_isPGroup.isPiNumber_natCard hrPi))

/-- A Hall subgroup of a finite nilpotent group is its corresponding prime
core, hence characteristic. -/
private theorem hall_eq_piCore_of_isNilpotent_15_3
    {K : Type u} [Group K] [Finite K] [Group.IsNilpotent K]
    {pi : Set ℕ} {H : Subgroup K} (hH : IsHall pi H) :
    H = piCore pi K := by
  have hle : H ≤ piCore pi K :=
    hall_le_piCore_of_isNilpotent_15_3 hH
  have hrelPi : IsPiNumber pi (H.relIndex (piCore pi K)) :=
    (piCore_isPiNumber pi).of_dvd
      (Subgroup.relIndex_dvd_card H (piCore pi K))
  have hrelCompl : IsPiNumber piᶜ (H.relIndex (piCore pi K)) :=
    hH.isPiNumber_index.of_dvd
      (Subgroup.relIndex_dvd_index_of_le hle)
  have hcop : (H.relIndex (piCore pi K)).Coprime
      (H.relIndex (piCore pi K)) := hrelPi.coprime_compl hrelCompl
  have hone : H.relIndex (piCore pi K) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop dvd_rfl dvd_rfl
  exact le_antisymm hle (Subgroup.relIndex_eq_one.mp hone)

/-- A characteristic subgroup, mapped back to the ambient group, is
normalized by every element normalizing its parent subgroup. -/
private theorem characteristic_map_subtype_le_normalizer_15_3
    {K : Type u} [Group K] (H : Subgroup K)
    (R : Subgroup H) [R.Characteristic] :
    Subgroup.normalizer (H : Set K) ≤
      Subgroup.normalizer (R.map H.subtype : Set K) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro r
  constructor
  · intro hr
    exact characteristic_map_subtype_invariant_under_normalizer
      H (Subgroup.normalizer (H : Set K)) R le_rfl g hg r hr
  · intro hr
    have hginv : g⁻¹ ∈ Subgroup.normalizer (H : Set K) :=
      (Subgroup.normalizer (H : Set K)).inv_mem hg
    have hback := characteristic_map_subtype_invariant_under_normalizer
      H (Subgroup.normalizer (H : Set K)) R le_rfl
      g⁻¹ hginv (g * r * g⁻¹) hr
    have hcancel : g⁻¹ * (g * r * g⁻¹) * (g⁻¹)⁻¹ = r := by
      group
    simpa only [hcancel] using hback

/-- Surjective images preserve Hall subgroups. -/
private theorem isHall_map_of_surjective_15_3
    {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    {pi : Set ℕ} {H : Subgroup A}
    (f : A →* B) (hf : Function.Surjective f) (hH : IsHall pi H) :
    IsHall pi (H.map f) := by
  constructor
  · exact hH.isPiNumber_card.of_dvd (Subgroup.card_map_dvd H f)
  · apply hH.isPiNumber_index.of_dvd
    rw [← (H.map f).index_comap_of_surjective hf]
    exact Subgroup.index_dvd_of_le (Subgroup.le_comap_map f H)

/-- Restrict a Hall subgroup to an intermediate subgroup containing it. -/
private theorem hall_restrict_15_3
    {A B C : Subgroup G} {pi : Set ℕ}
    (hAB : A ≤ B) (hBC : B ≤ C)
    (hA : IsHall pi (A.subgroupOf C)) :
    IsHall pi (A.subgroupOf B) := by
  constructor
  · rw [MathlibSupport.natCard_subgroupOf_eq hAB]
    simpa only [MathlibSupport.natCard_subgroupOf_eq (hAB.trans hBC)] using
      hA.isPiNumber_card
  · change IsPiNumber piᶜ (A.relIndex B)
    apply hA.isPiNumber_index.of_dvd
    exact ⟨B.relIndex C,
      (A.relIndex_mul_relIndex B C hAB hBC).symm⟩

/-- Conjugating both an ambient subgroup and one of its Hall subgroups
preserves the relative Hall property. -/
private theorem isHall_subgroupOf_map_mulEquiv_15_3
    {A L : Subgroup G} (hLA : L ≤ A)
    {pi : Set ℕ} (hL : IsHall pi (L.subgroupOf A))
    (e : G ≃* G) :
    IsHall pi
      ((L.map e.toMonoidHom).subgroupOf
        (A.map e.toMonoidHom)) := by
  let eA : A ≃* A.map e.toMonoidHom :=
    A.equivMapOfInjective e.toMonoidHom e.injective
  have hmap :
      (L.subgroupOf A).map eA.toMonoidHom =
        (L.map e.toMonoidHom).subgroupOf
          (A.map e.toMonoidHom) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change e (y : G) ∈ L.map e.toMonoidHom
      exact (Subgroup.mem_map_iff_mem e.injective).mpr hy
    · intro hx
      change (x : G) ∈ L.map e.toMonoidHom at hx
      have hx' := Subgroup.mem_map_equiv.mp hx
      let y : A := ⟨e.symm x, hLA hx'⟩
      refine ⟨y, hx', ?_⟩
      apply Subtype.ext
      exact e.apply_symm_apply (x : G)
  rw [← hmap]
  constructor
  · rw [Subgroup.card_map_of_injective eA.injective]
    exact hL.isPiNumber_card
  · have hindex :
        ((L.subgroupOf A).map eA.toMonoidHom).index =
          (L.subgroupOf A).index :=
      Subgroup.index_map_equiv (L.subgroupOf A) eA
    exact hindex.symm ▸ hL.isPiNumber_index

/-- Mapping the normalizer of a represented subgroup back to the ambient
group gives its relative normalizer. -/
private theorem map_normalizer_subgroupOf_15_3
    {A B : Subgroup G} (hBA : B ≤ A) :
    (Subgroup.normalizer (B.subgroupOf A : Set A)).map A.subtype =
      normalizerWithin A B := by
  calc
    (Subgroup.normalizer (B.subgroupOf A : Set A)).map A.subtype =
        ((Subgroup.normalizer (B : Set G)).subgroupOf A).map
          A.subtype := by
      rw [Subgroup.subgroupOf_normalizer_eq hBA]
    _ = Subgroup.normalizer (B : Set G) ⊓ A :=
      Subgroup.subgroupOf_map_subtype
        (Subgroup.normalizer (B : Set G)) A
    _ = normalizerWithin A B := inf_comm _ _

/-- Frattini's argument for a solvable normal Hall factor, in the exact
complement form needed below. -/
private theorem normal_sup_normalizer_eq_top_of_solvable_complement_15_3
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
    MathlibSupport.natCard_subgroupOf_eq hVU
  have hcardKU : Nat.card KU = Nat.card K :=
    MathlibSupport.natCard_subgroupOf_eq hKU
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
        MathlibSupport.natCard_subgroupOf_eq hKaU
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
      congrArg (fun S : Subgroup U ↦ S.map U.subtype) hv
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

/-- `BGsection15.v: cent_Hall_sigma_sdprod`, Corollary 15.3(a). -/
theorem cent_Hall_sigma_sdprod
    {M H : Subgroup G} {pi : Set ℕ}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hHMs : H ≤ sigmaCore M)
    (hHallH : IsHall pi (H.subgroupOf (sigmaCore M)))
    (hHne : H ≠ ⊥) :
    ∃ X : Subgroup G,
      X ≤ M ∧ IsCyclic X ∧
        IsPiNumber (tau2Primes M) (Nat.card X) ∧
        IsInternalSemidirectProductIn
          (centralizerWithin (sigmaCore M) H) X
          (centralizerWithin M H) := by
  classical
  let Ms := sigmaCore M
  let C := centralizerWithin M H
  let Cs := centralizerWithin Ms H
  letI : IsSolvable M := mmax_sol hM
  have hMsM : Ms ≤ M := sigmaCore_le M
  have hMsnormal : (Ms.subgroupOf M).Normal := by
    simpa [Ms] using sigmaCore_normal M
  have hCsol : IsSolvable C :=
    isSolvable_of_injective (Subgroup.inclusion inf_le_left)
      (Subgroup.inclusion_injective inf_le_left)

  /- No kappa-prime divides the centralizer.  Otherwise a kappa Hall
  subgroup containing a rank-one line in `C` invokes Proposition 14.2(e),
  while a Sylow subgroup of `H` lies in `Kstar`. -/
  have hCkappaPrime :
      IsPiNumber (kappaPrimes M)ᶜ (Nat.card C) := by
    intro p hp hpC hpKappa
    letI : Fact p.Prime := ⟨hp⟩
    obtain ⟨x, hxOrder⟩ :=
      exists_prime_orderOf_dvd_card' (G := C) p hpC
    let X : Subgroup G := (Subgroup.zpowers x).map C.subtype
    have hXC : X ≤ C := Subgroup.map_subtype_le _
    have hcardX : Nat.card X = p := by
      dsimp only [X]
      rw [Subgroup.card_map_of_injective C.subtype_injective,
        Nat.card_zpowers, hxOrder]
    have hXline : IsElementaryAbelianOfRank p 1 X :=
      isElementaryAbelianOfRank_one_of_card_eq_prime hcardX
    have hXM : X ≤ M := hXC.trans inf_le_left
    obtain ⟨K, hXK, hKM, hHallK⟩ :=
      Submission.OddOrder.MathlibSupport.exists_ambient_isHall_ge_of_isSolvable
        hXM (mmax_sol hM)
        (kappaPrimes M)
        (hXline.isPGroup.isPiNumber_natCard hpKappa)
    have hP : M ∈ typePMaximalSubgroups (G := G) :=
      (PtypeP hM).2 ⟨p, hpKappa⟩
    have hs := Ptype_structure hP hKM hHallK
    have hXKline : RankOneLineIn p K X :=
      ⟨hXK, hXline⟩
    have hcardHne : Nat.card H ≠ 1 := fun hc ↦
      hHne (Subgroup.card_eq_one.mp hc)
    obtain ⟨q, hq, hqH⟩ := Nat.exists_prime_and_dvd hcardHne
    letI : Fact q.Prime := ⟨hq⟩
    let SH : Sylow q H := Classical.choice Sylow.nonempty
    let S : Subgroup G := ambientSylow H SH
    have hSH : S ≤ H := by
      dsimp only [S, ambientSylow]
      exact Subgroup.map_subtype_le _
    have hSsylowH : IsSylowSubgroupOf q S H := ⟨SH, rfl⟩
    have hqPi : q ∈ pi := by
      apply hHallH.isPiNumber_card hq
      simpa only [MathlibSupport.natCard_subgroupOf_eq hHMs] using hqH
    have hqNotIndexHMs : ¬ q ∣ (H.subgroupOf Ms).index := by
      intro hdiv
      exact hHallH.isPiNumber_index hq hdiv hqPi
    have hSsylowMs : IsSylowSubgroupOf q S Ms :=
      hSsylowH.extend_of_not_dvd_index hHMs hqNotIndexHMs
    have hqSigma : q ∈ sigmaPrimes M := by
      apply sigmaCore_isPiNumber M hq
      exact hqH.trans (Subgroup.card_dvd_of_le hHMs)
    have hqNotIndexMsM : ¬ q ∣ (Ms.subgroupOf M).index := by
      intro hdiv
      exact (Msigma_Hall hM).isPiNumber_index hq hdiv hqSigma
    have hSsylowM : IsSylowSubgroupOf q S M :=
      hSsylowMs.extend_of_not_dvd_index hMsM hqNotIndexMsM
    have hSCX : S ≤ Subgroup.centralizer (X : Set G) := by
      intro s hsS
      rw [Subgroup.mem_centralizer_iff]
      intro x hxX
      exact (Subgroup.mem_centralizer_iff.mp
        (hXC hxX).2 s (hSH hsS)).symm
    have hSNX : S ≤ normalizerWithin M X := by
      intro s hsS
      exact ⟨hMsM (hHMs (hSH hsS)),
        (Subgroup.centralizer_le_normalizer (X : Set G)) (hSCX hsS)⟩
    have hSNK : S ≤ normalizerWithin M K := by
      rw [← (hs.rankOne_normalizer hXKline).1]
      exact hSNX
    have hSsigma : IsPiNumber (sigmaPrimes M) (Nat.card S) :=
      (sigmaCore_isPiNumber M).of_dvd
        (Subgroup.card_dvd_of_le (hSH.trans hHMs))
    have hSKs : S ≤ kappaCentralizer M K := by
      simpa only [kappaCentralizer, pTypeCentralizer] using
        sigma_subgroup_le_pTypeCentralizer_of_le_normalizer_15_3
          hKM hHallK hs hSNK hSsigma
    have hqS : q ∣ Nat.card S := by
      dsimp only [S, ambientSylow]
      rw [Subgroup.card_map_of_injective H.subtype_injective]
      exact SH.dvd_card_of_dvd_card hqH
    have hqKs :
        q ∈ primeSupport (Nat.card (pTypeCentralizer M K)) :=
      ⟨hq, hqS.trans (Subgroup.card_dvd_of_le hSKs)⟩
    obtain ⟨SM, hSM⟩ := hSsylowM
    apply (hs.Kstar_sylow_unique hqKs SM).2
    change (SM : Subgroup M).map M.subtype ≤ pTypeCentralizer M K
    rw [← hSM]
    exact hSKs

  obtain ⟨X, hXC, hHallX⟩ :=
    Submission.OddOrder.MathlibSupport.exists_ambient_isHall_of_isSolvable
      (K := C) hCsol (sigmaPrimes M)ᶜ
  have hCsEq : Cs = Ms ⊓ C := by
    ext z
    change
      (z ∈ Ms ∧ z ∈ Subgroup.centralizer (H : Set G)) ↔
        (z ∈ Ms ∧ z ∈ M ∧
          z ∈ Subgroup.centralizer (H : Set G))
    constructor
    · rintro ⟨hzMs, hzCent⟩
      exact ⟨hzMs, hMsM hzMs, hzCent⟩
    · rintro ⟨hzMs, -, hzCent⟩
      exact ⟨hzMs, hzCent⟩
  have hCsnormalC : (Cs.subgroupOf C).Normal := by
    rw [hCsEq]
    exact normal_inf_subgroupOf_of_le_15 hMsM inf_le_left hMsnormal
  have hHallCs : IsHall (sigmaPrimes M) (Cs.subgroupOf C) := by
    rw [hCsEq]
    constructor
    · rw [MathlibSupport.natCard_subgroupOf_eq inf_le_right]
      have hMspi : IsPiNumber (sigmaPrimes M) (Nat.card Ms) := by
        simpa only [Ms, MathlibSupport.natCard_subgroupOf_eq hMsM] using
          (Msigma_Hall hM).isPiNumber_card
      exact hMspi.of_dvd (Subgroup.card_dvd_of_le inf_le_left)
    · change IsPiNumber (sigmaPrimes M)ᶜ ((Ms ⊓ C).relIndex C)
      rw [Subgroup.inf_relIndex_right]
      change IsPiNumber (sigmaPrimes M)ᶜ
        (Ms.relIndex (M ⊓ Subgroup.centralizer (H : Set G)))
      let MsM : Subgroup M := Ms.subgroupOf M
      let CM : Subgroup M :=
        (M ⊓ Subgroup.centralizer (H : Set G)).subgroupOf M
      letI : MsM.Normal := by simpa [MsM] using hMsnormal
      have hdvd : MsM.relIndex CM ∣ MsM.index :=
        Subgroup.relIndex_dvd_index_of_normal MsM CM
      have hrel : MsM.relIndex CM =
          Ms.relIndex (M ⊓ Subgroup.centralizer (H : Set G)) := by
        simpa only [MsM, CM] using
          Subgroup.relIndex_subgroupOf (H := Ms) inf_le_left
      rw [hrel] at hdvd
      exact (Msigma_Hall hM).isPiNumber_index.of_dvd hdvd
  have hsd : IsInternalSemidirectProductIn Cs X C :=
    normal_complementary_hall_sdprod_15_3
      (by rw [hCsEq]; exact inf_le_right)
      hXC hCsnormalC hHallCs hHallX
  by_cases hXbot : X = ⊥
  · refine ⟨X, hXC.trans inf_le_left, ?_, ?_, hsd⟩
    · subst X
      infer_instance
    · subst X
      have hone : IsPiNumber (tau2Primes M) 1 := IsPiNumber.one
      simpa only [Subgroup.card_bot] using hone
  have hXsigmaKappaPrime :
      IsPiNumber (sigmaKappaPrimes M)ᶜ (Nat.card X) := by
    intro p hp hpX hpUnion
    have hpSigmaCompl : p ∈ (sigmaPrimes M)ᶜ :=
      hHallX.isPiNumber_card hp (by
        simpa only [MathlibSupport.natCard_subgroupOf_eq hXC] using hpX)
    have hpKappaCompl : p ∈ (kappaPrimes M)ᶜ :=
      hCkappaPrime hp
        (hpX.trans (Subgroup.card_dvd_of_le hXC))
    rcases hpUnion with hpSigma | hpKappa
    · exact hpSigmaCompl hpSigma
    · exact hpKappaCompl hpKappa
  obtain ⟨K, hKM, hHallK⟩ :=
    Submission.OddOrder.MathlibSupport.exists_ambient_isHall_of_isSolvable
      (mmax_sol hM) (kappaPrimes M)
  obtain ⟨U, hcompl⟩ := ex_kappa_compl hM hKM hHallK
  obtain ⟨aM, hXUa, _, _, _, _, _⟩ :=
    Submission.OddOrder.MathlibSupport.exists_ambient_isHall_map_conj_ge_of_isSolvable
      (A := X) (K := M) (H := U)
      (hXC.trans inf_le_left) hcompl.U_le_M (mmax_sol hM)
      hXsigmaKappaPrime hcompl.hall_U
  let a : G := (aM : G)⁻¹
  have haM : a ∈ M := M.inv_mem aM.property
  have hXaU : X.map (MulAut.conj a).toMonoidHom ≤ U := by
    rintro y ⟨x, hxX, rfl⟩
    obtain ⟨u, huU, hux⟩ := hXUa hxX
    rw [← hux]
    simpa [a, MulAut.conj_apply, mul_assoc] using huU
  have hkappa := kappa_structure hM hcompl
  have hcentralNe :
      centralizerWithin (sigmaCore M)
        (X.map (MulAut.conj a).toMonoidHom) ≠ ⊥ := by
    obtain ⟨h, hhne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hHne
    have hMnormMs : M ≤ Subgroup.normalizer (Ms : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hMsM).mp hMsnormal
    have hconjMs : (MulAut.conj a) (h : G) ∈ sigmaCore M := by
      change a * (h : G) * a⁻¹ ∈ Ms
      exact (Subgroup.mem_normalizer_iff.mp
        (hMnormMs haM) (h : G)).mp (hHMs h.property)
    apply Subgroup.ne_bot_iff_exists_ne_one.mpr
    refine ⟨⟨(MulAut.conj a) (h : G), ?_⟩, ?_⟩
    · refine ⟨hconjMs, ?_⟩
      rintro y ⟨x, hxX, rfl⟩
      have hxC : x ∈ centralizerWithin M H := by
        simpa only [C] using hXC hxX
      have hcomm : x * (h : G) = (h : G) * x :=
        (hxC.2 (h : G) h.property).symm
      change
        (MulAut.conj a).toMonoidHom x *
            (MulAut.conj a).toMonoidHom (h : G) =
          (MulAut.conj a).toMonoidHom (h : G) *
            (MulAut.conj a).toMonoidHom x
      simpa only [map_mul] using
        congrArg
          (fun z : G ↦ (MulAut.conj a).toMonoidHom z) hcomm
    · intro hzOne
      apply hhne
      apply Subtype.ext
      apply (MulAut.conj a).injective
      simpa using congrArg Subtype.val hzOne
  have hmapNe : X.map (MulAut.conj a).toMonoidHom ≠ ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective X
      (MulAut.conj a).injective).not.mpr hXbot
  have hcontrol :=
    hkappa.U_subgroup_control hXaU hmapNe hcentralNe
  have hXacyclic : IsCyclic (X.map (MulAut.conj a).toMonoidHom) :=
    hcontrol.2.1
  have hXatau :
      IsPiNumber (tau2Primes M)
        (Nat.card (X.map (MulAut.conj a).toMonoidHom)) :=
    hcontrol.2.2
  refine ⟨X, hXC.trans inf_le_left, ?_, ?_, hsd⟩
  · exact
      (X.equivMapOfInjective (MulAut.conj a).toMonoidHom
        (MulAut.conj a).injective).isCyclic.mpr hXacyclic
  · rw [Subgroup.card_map_of_injective
      (K := X) (f := (MulAut.conj a).toMonoidHom)
      (MulAut.conj a).injective] at hXatau
    exact hXatau

/-- `BGsection15.v: sigma_Hall_tame`, Corollary 15.3(b). -/
theorem sigma_Hall_tame
    {M H : Subgroup G} {pi : Set ℕ} {x a : G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hHMs : H ≤ sigmaCore M)
    (hHallH : IsHall pi (H.subgroupOf (sigmaCore M)))
    (hxH : x ∈ H)
    (hxaH : (MulAut.conj a) x ∈ H) :
    ∃ b : G, b ∈ normalizerWithin M H ∧
      (MulAut.conj a) x = (MulAut.conj b) x := by
  classical
  by_cases hx : x = 1
  · refine ⟨(1 : G), ⟨M.one_mem, Subgroup.one_mem _⟩, ?_⟩
    simp [hx]
  have hMsM : sigmaCore M ≤ M := sigmaCore_le M
  have hsigmax : sigmaLength x = 1 :=
    Msigma_ell1 hM (hHMs hxH) hx
  have hsignal := FT_signalizer_context hsigmax
  have hMbase : M ∈
      sigmaMaximalOvergroups (Subgroup.zpowers x : Set G) :=
    ⟨hM, Subgroup.zpowers_le.mpr (hHMs hxH)⟩
  have hMMa :
      M.map (MulAut.conj a⁻¹).toMonoidHom ∈
        sigmaMaximalOvergroups (Subgroup.zpowers x : Set G) := by
    refine ⟨(mmaxJ M (MulAut.conj a⁻¹)).2 hM,
      Subgroup.zpowers_le.mpr ?_⟩
    rw [sigmaCore_map_mulEquiv]
    apply Subgroup.mem_map_equiv.mpr
    simpa [MulAut.conj_apply, mul_assoc] using hHMs hxaH
  obtain ⟨c, hcR, hconjM⟩ :=
    hsignal.basic.transitive hMbase hMMa
  let b := a * c
  have hcx : Commute c x :=
    (Subgroup.mem_centralizer_iff.mp
      (hsignal.basic.R_le_centralizer hcR)
      x (Subgroup.mem_zpowers x)).symm
  have hxab : (MulAut.conj a) x = (MulAut.conj b) x := by
    dsimp only [b]
    simp only [MulAut.conj_apply, mul_inv_rev]
    calc
      a * x * a⁻¹ = a * (c * x * c⁻¹) * a⁻¹ := by
        rw [hcx.eq]
        simp [mul_assoc]
      _ = (a * c) * x * (c⁻¹ * a⁻¹) := by
        simp only [mul_assoc]
  have hbNormM : b ∈ Subgroup.normalizer (M : Set G) := by
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    have hmapped := congrArg
      (fun L : Subgroup G ↦ L.map (MulAut.conj a).toMonoidHom)
      hconjM
    have hcancel :
        (MulAut.conj a).toMonoidHom.comp
            (MulAut.conj a⁻¹).toMonoidHom = MonoidHom.id G := by
      ext z
      change a * (a⁻¹ * z * (a⁻¹)⁻¹) * a⁻¹ = z
      group
    have hcompose :
        (MulAut.conj a).toMonoidHom.comp
            (MulAut.conj c).toMonoidHom =
          (MulAut.conj b).toMonoidHom := by
      ext z
      dsimp only [b]
      change a * (c * z * c⁻¹) * a⁻¹ =
        (a * c) * z * (a * c)⁻¹
      group
    rw [Subgroup.map_map, Subgroup.map_map, hcancel, hcompose,
      Subgroup.map_id] at hmapped
    exact hmapped.symm
  have hbM : b ∈ M := by
    rw [← norm_mmax hM]
    exact hbNormM
  by_cases hHnormal : (H.subgroupOf M).Normal
  · have hMnormH : M ≤ Subgroup.normalizer (H : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer
        (hHMs.trans hMsM)).mp hHnormal
    exact ⟨b, ⟨hbM, hMnormH hbM⟩, hxab⟩

  have hFne : Fitting_core M ≠ sigmaCore M := by
    intro heq
    have hnil : Group.IsNilpotent (sigmaCore M) :=
      (Fcore_eq_Msigma hM).1 heq
    letI : Group.IsNilpotent (sigmaCore M) := hnil
    have hHchar : (H.subgroupOf (sigmaCore M)).Characteristic := by
      rw [hall_eq_piCore_of_isNilpotent_15_3 hHallH]
      infer_instance
    letI : (H.subgroupOf (sigmaCore M)).Characteristic := hHchar
    have hHM : H ≤ M := hHMs.trans hMsM
    have hMnormMs : M ≤
        Subgroup.normalizer (sigmaCore M : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hMsM).mp
        (sigmaCore_normal M)
    have hnormMap :=
      characteristic_map_subtype_le_normalizer_15_3
        (sigmaCore M) (H.subgroupOf (sigmaCore M))
    have hmapH :
        (H.subgroupOf (sigmaCore M)).map (sigmaCore M).subtype = H :=
      Subgroup.map_subgroupOf_eq_of_le hHMs
    rw [hmapH] at hnormMap
    have hMnormH : M ≤ Subgroup.normalizer (H : Set G) :=
      hMnormMs.trans hnormMap
    have hHnormalDerived : (H.subgroupOf M).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hHM).mpr hMnormH
    exact hHnormal hHnormalDerived
  obtain ⟨K, hKM, hHallK⟩ :=
    Submission.OddOrder.MathlibSupport.exists_ambient_isHall_of_isSolvable
      (mmax_sol hM) (kappaPrimes M)
  let q := Nat.card (kappaCentralizer M K)
  have hMsSol : IsSolvable (sigmaCore M) :=
    isSolvable_of_le_15 (mmax_sol hM) hMsM
  obtain ⟨D, hDsigma, hHallD⟩ :=
    Submission.OddOrder.MathlibSupport.exists_ambient_isHall_of_isSolvable
      hMsSol ({q} : Set ℕ)ᶜ
  have hs := (Fcore_structure hM).nonnilpotent
    hKM hHallK hFne hDsigma (by simpa [q] using hHallD)
  letI : Fact q.Prime := ⟨by
    simpa [q] using hs.card_partner_prime⟩
  let Q := pCoreWithin q M
  have hQnormalM : (Q.subgroupOf M).Normal := by
    simpa only [Q] using pCoreWithin_normal_15 q M
  have hQMs : Q ≤ sigmaCore M :=
    (Fcore_sub_Msigma hM).trans'
      (by simpa [Q, q] using
        normal_sylow_le_Fcore hs.pcore_sylow hQnormalM)
  have hQnormalMs : (Q.subgroupOf (sigmaCore M)).Normal := by
    have hMnormQ : M ≤ Subgroup.normalizer (Q : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer
        (hQMs.trans hMsM)).mp hQnormalM
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hQMs).mpr
      (hMsM.trans hMnormQ)
  have hQsylowMs : IsSylowSubgroupOf q Q (sigmaCore M) :=
    hs.pcore_sylow.restrict_of_le hQMs hMsM
  have hQDsigma : IsInternalSemidirectProductIn Q D (sigmaCore M) :=
    normal_sylow_complement_sdprod_15
      (by simpa [q] using hs.card_partner_prime)
      hQsylowMs hQnormalMs hDsigma (by simpa [q] using hHallD)
  have hQsq : IsPGroup q (Q.subgroupOf (sigmaCore M)) :=
    hQsylowMs.isPGroup.of_equiv
      (Subgroup.subgroupOfEquivOfLe hQMs).symm
  have hQcore :
      Q.subgroupOf (sigmaCore M) = pCore q (sigmaCore M) := by
    apply le_antisymm
    · exact le_pCore hQsq hQnormalMs
    · obtain ⟨P, hQP⟩ := hQsylowMs
      have hQsub : Q.subgroupOf (sigmaCore M) =
          (P : Subgroup (sigmaCore M)) := by
        rw [hQP]
        exact Subgroup.comap_map_eq_self_of_injective
          (sigmaCore M).subtype_injective (P : Subgroup (sigmaCore M))
      exact (pCore_le_sylow P).trans hQsub.symm.le
  letI : (Q.subgroupOf (sigmaCore M)).Normal := hQnormalMs
  letI : (Q.subgroupOf (sigmaCore M)).Characteristic := by
    rw [hQcore]
    infer_instance
  have hquotNil : Group.IsNilpotent
      ((sigmaCore M) ⧸ Q.subgroupOf (sigmaCore M)) := by
    letI : Group.IsNilpotent D := hs.D_nilpotent
    exact Group.nilpotent_of_mulEquiv
      (semidirectQuotientEquiv_15 hQDsigma).symm
  let qMs : sigmaCore M →*
      (sigmaCore M ⧸ Q.subgroupOf (sigmaCore M)) :=
    QuotientGroup.mk' (Q.subgroupOf (sigmaCore M))
  let HMs : Subgroup (sigmaCore M) :=
    H.subgroupOf (sigmaCore M)
  let Hbar : Subgroup
      (sigmaCore M ⧸ Q.subgroupOf (sigmaCore M)) := HMs.map qMs
  have hHallHbar : IsHall pi Hbar := by
    exact isHall_map_of_surjective_15_3 qMs
      (QuotientGroup.mk'_surjective (Q.subgroupOf (sigmaCore M)))
      (by simpa only [HMs] using hHallH)
  letI : Group.IsNilpotent
      (sigmaCore M ⧸ Q.subgroupOf (sigmaCore M)) := hquotNil
  have hHbarChar : Hbar.Characteristic := by
    rw [hall_eq_piCore_of_isNilpotent_15_3 hHallHbar]
    infer_instance
  let R : Subgroup (sigmaCore M) := Hbar.comap qMs
  have hRchar : R.Characteristic := by
    dsimp only [R]
    exact Subgroup.Characteristic.comap_quotient_mk hHbarChar
  letI : R.Characteristic := hRchar
  have hRmap : R.map (sigmaCore M).subtype = Q ⊔ H := by
    dsimp only [R, Hbar, HMs, qMs]
    rw [QuotientGroup.comap_map_mk', Subgroup.map_sup,
      Subgroup.map_subgroupOf_eq_of_le hQMs,
      Subgroup.map_subgroupOf_eq_of_le hHMs]
  have hMnormMs : M ≤
      Subgroup.normalizer (sigmaCore M : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMsM).mp
      (sigmaCore_normal M)
  have hMnormQH : M ≤
      Subgroup.normalizer ((Q ⊔ H : Subgroup G) : Set G) := by
    have hnormR := characteristic_map_subtype_le_normalizer_15_3
      (sigmaCore M) R
    rw [hRmap] at hnormR
    exact hMnormMs.trans hnormR
  have hQHnormalM : ((Q ⊔ H).subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (sup_le (hQMs.trans hMsM) (hHMs.trans hMsM))).mpr hMnormQH
  have hqNotPi : q ∉ pi := by
    intro hqPi
    have hQpi : IsPiNumber pi (Nat.card Q) :=
      hQsylowMs.isPGroup.isPiNumber_natCard hqPi
    have hQpiMs :
        IsPiNumber pi (Nat.card (Q.subgroupOf (sigmaCore M))) := by
      simpa only [MathlibSupport.natCard_subgroupOf_eq hQMs] using hQpi
    have hQHsub : Q.subgroupOf (sigmaCore M) ≤
        H.subgroupOf (sigmaCore M) :=
      normal_isPiNumber_le_isHall hQnormalMs hQpiMs hHallH
    have hQH : Q ≤ H := by
      intro y hy
      exact hQHsub
        (show (⟨y, hQMs hy⟩ : sigmaCore M) ∈
          Q.subgroupOf (sigmaCore M) from hy)
    have hHnormalDerived : (H.subgroupOf M).Normal := by
      simpa only [sup_eq_right.mpr hQH] using hQHnormalM
    exact hHnormal hHnormalDerived
  have hQinfH : Q ⊓ H = ⊥ := by
    rw [← disjoint_iff]
    have hQq : IsPiNumber ({q} : Set ℕ) (Nat.card Q) :=
      hQsylowMs.isPGroup.isPiNumber_natCard (Set.mem_singleton q)
    have hHpi : IsPiNumber pi (Nat.card H) := by
      simpa only [MathlibSupport.natCard_subgroupOf_eq hHMs] using
        hHallH.isPiNumber_card
    have hHqCompl : IsPiNumber ({q} : Set ℕ)ᶜ (Nat.card H) :=
      hHpi.mono (by
        intro r hrPi
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        intro hrq
        exact hqNotPi (hrq ▸ hrPi))
    exact Subgroup.disjoint_of_coprime_natCard
      (hQq.coprime_compl hHqCompl)
  have hQM : Q ≤ M := hQMs.trans hMsM
  have hHM : H ≤ M := hHMs.trans hMsM
  have hHallHQH : IsHall pi (H.subgroupOf (Q ⊔ H)) :=
    hall_restrict_15_3 le_sup_right (sup_le hQMs hHMs) hHallH
  have hQnormalQH : (Q.subgroupOf (Q ⊔ H)).Normal := by
    have hMnormQ : M ≤ Subgroup.normalizer (Q : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hQM).mp hQnormalM
    apply Subgroup.normal_subgroupOf_of_le_normalizer
    exact sup_le Subgroup.le_normalizer (hHM.trans hMnormQ)
  have hdisQH :
      Disjoint (Q.subgroupOf (Q ⊔ H)) (H.subgroupOf (Q ⊔ H)) := by
    rw [disjoint_iff]
    apply le_antisymm _ bot_le
    intro y hy
    apply Subgroup.mem_bot.mpr
    apply Subtype.ext
    apply Subgroup.mem_bot.mp
    have hyAmbient : ((y : ↥(Q ⊔ H)) : G) ∈ Q ⊓ H :=
      ⟨hy.1, hy.2⟩
    rw [hQinfH] at hyAmbient
    exact hyAmbient
  have hcompQH :
      (Q.subgroupOf (Q ⊔ H)).IsComplement' (H.subgroupOf (Q ⊔ H)) := by
    letI : (Q.subgroupOf (Q ⊔ H)).Normal := hQnormalQH
    apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisQH
    rw [← Subgroup.normal_mul,
      ← Subgroup.subgroupOf_sup le_sup_left le_sup_right,
      Subgroup.subgroupOf_self]
    rfl
  have hcopQH : Nat.Coprime (Nat.card Q) (Nat.card H) := by
    have hcopHindex : Nat.Coprime (Nat.card (H.subgroupOf (Q ⊔ H)))
        (H.subgroupOf (Q ⊔ H)).index :=
      hHallHQH.isPiNumber_card.coprime_compl hHallHQH.isPiNumber_index
    rw [hcompQH.index_eq_card,
      MathlibSupport.natCard_subgroupOf_eq le_sup_right,
      MathlibSupport.natCard_subgroupOf_eq le_sup_left] at hcopHindex
    exact hcopHindex.symm

  let QM : Subgroup M := Q.subgroupOf M
  let HM : Subgroup M := H.subgroupOf M
  let UM : Subgroup M := QM ⊔ HM
  have hUMeq : UM = (Q ⊔ H).subgroupOf M := by
    dsimp only [UM, QM, HM]
    exact (Subgroup.subgroupOf_sup hQM hHM).symm
  letI : QM.Normal := by simpa only [QM] using hQnormalM
  letI : UM.Normal := by rw [hUMeq]; exact hQHnormalM
  letI : IsSolvable M := mmax_sol hM
  letI : IsSolvable QM := isSolvable_subgroup_of_isSolvable QM
  have hdisUM : Disjoint (QM.subgroupOf UM) (HM.subgroupOf UM) := by
    rw [disjoint_iff]
    apply le_antisymm _ bot_le
    intro y hy
    apply Subgroup.mem_bot.mpr
    apply Subtype.ext
    apply Subtype.ext
    have hyAmbient : (((y : UM) : M) : G) ∈ Q ⊓ H :=
      ⟨hy.1, hy.2⟩
    rw [hQinfH] at hyAmbient
    exact Subgroup.mem_bot.mp hyAmbient
  have hcompUM :
      (QM.subgroupOf UM).IsComplement' (HM.subgroupOf UM) := by
    letI : (QM.subgroupOf UM).Normal :=
      Subgroup.Normal.subgroupOf (inferInstance : QM.Normal) UM
    apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisUM
    rw [← Subgroup.normal_mul,
      ← Subgroup.subgroupOf_sup le_sup_left le_sup_right,
      Subgroup.subgroupOf_self]
    rfl
  have hcopQMHM : Nat.Coprime (Nat.card QM) (Nat.card HM) := by
    dsimp only [QM, HM]
    rw [MathlibSupport.natCard_subgroupOf_eq hQM,
      MathlibSupport.natCard_subgroupOf_eq hHM]
    exact hcopQH
  have hFrattiniM : UM ⊔ Subgroup.normalizer (HM : Set M) = ⊤ :=
    normal_sup_normalizer_eq_top_of_solvable_complement_15_3
      UM QM HM le_sup_left le_sup_right hcompUM hcopQMHM
  have hUMmap : UM.map M.subtype = Q ⊔ H := by
    dsimp only [UM]
    rw [Subgroup.map_sup]
    dsimp only [QM, HM]
    rw [Subgroup.map_subgroupOf_eq_of_le hQM,
      Subgroup.map_subgroupOf_eq_of_le hHM]
  have hNormMap :
      (Subgroup.normalizer (HM : Set M)).map M.subtype =
        normalizerWithin M H := by
    simpa only [HM, normalizerWithin] using
      (map_normalizer_subgroupOf_15_3 hHM)
  have htopMap : (⊤ : Subgroup M).map M.subtype = M := by
    rw [← MonoidHom.range_eq_map, M.range_subtype]
  have hFrattiniAmbient :
      (Q ⊔ H) ⊔ normalizerWithin M H = M := by
    have hmap := congrArg
      (fun L : Subgroup M ↦ L.map M.subtype) hFrattiniM
    rw [Subgroup.map_sup, hUMmap, hNormMap, htopMap] at hmap
    exact hmap
  have hHleNorm : H ≤ normalizerWithin M H :=
    le_inf hHM Subgroup.le_normalizer
  have hfrattini : Q ⊔ normalizerWithin M H = M := by
    calc
      Q ⊔ normalizerWithin M H =
          (Q ⊔ H) ⊔ normalizerWithin M H := by
        apply le_antisymm
        · exact sup_le (le_sup_left.trans le_sup_left) le_sup_right
        · exact sup_le
            (sup_le le_sup_left (hHleNorm.trans le_sup_right)) le_sup_right
      _ = M := hFrattiniAmbient
  have hNormQ : normalizerWithin M H ≤
      Subgroup.normalizer (Q : Set G) := by
    have hMnormQ : M ≤ Subgroup.normalizer (Q : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hQM).mp hQnormalM
    exact inf_le_left.trans hMnormQ
  have hbSup : b ∈ Q ⊔ normalizerWithin M H := by
    rw [hfrattini]
    exact hbM
  have hbProd : b ∈
      (Q : Set G) * (normalizerWithin M H : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left
      Q (normalizerWithin M H) hNormQ]
    exact hbSup
  obtain ⟨z, hzQ, n, hnN, hbn⟩ := hbProd
  refine ⟨n, hnN, ?_⟩
  rw [hxab, ← hbn]
  let y : G := (MulAut.conj n) x
  have hyH : y ∈ H := by
    dsimp only [y]
    exact (Subgroup.mem_normalizer_iff.mp hnN.2 x).mp hxH
  have hyM : y ∈ M := hHM hyH
  have hzyH : (MulAut.conj (z * n)) x ∈ H := by
    have hzb : z * n = b := hbn
    rw [hzb, ← hxab]
    exact hxaH
  have hconjProd :
      (MulAut.conj (z * n)) x = z * y * z⁻¹ := by
    dsimp only [y]
    simp only [MulAut.conj_apply, mul_inv_rev]
    group
  have hMnormQ : M ≤ Subgroup.normalizer (Q : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQM).mp hQnormalM
  have hyzinvQ : y * z⁻¹ * y⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp (hMnormQ hyM) z⁻¹).mp
      (Q.inv_mem hzQ)
  have hdQ : (MulAut.conj (z * n)) x * y⁻¹ ∈ Q := by
    rw [hconjProd]
    simpa only [mul_assoc] using Q.mul_mem hzQ hyzinvQ
  have hdH : (MulAut.conj (z * n)) x * y⁻¹ ∈ H :=
    H.mul_mem hzyH (H.inv_mem hyH)
  have hdInf : (MulAut.conj (z * n)) x * y⁻¹ ∈ Q ⊓ H :=
    ⟨hdQ, hdH⟩
  rw [hQinfH] at hdInf
  have hdOne : (MulAut.conj (z * n)) x * y⁻¹ = 1 :=
    Subgroup.mem_bot.mp hdInf
  exact eq_of_mul_inv_eq_one hdOne

/-! ## Corollary 15.4 -/

/-- A subgroup supported on `pi` lies in a normal `pi`-Hall subgroup. -/
private theorem subgroup_le_normal_isHall15_4
    {K : Type u} [Group K] [Finite K] {pi : Set ℕ}
    {N L : Subgroup K} (hNnormal : N.Normal)
    (hNHall : IsHall pi N) (hLpi : IsPiNumber pi (Nat.card L)) :
    L ≤ N := by
  letI : N.Normal := hNnormal
  have hcop : (Nat.card L).Coprime N.index := by
    apply Nat.coprime_of_dvd
    intro p hp hpL hpIndex
    exact hNHall.isPiNumber_index hp hpIndex (hLpi hp hpL)
  intro x hxL
  let q : K →* K ⧸ N := QuotientGroup.mk' N
  have horderL : orderOf (q x) ∣ Nat.card L :=
    (orderOf_map_dvd q x).trans (L.orderOf_dvd_natCard hxL)
  have horderIndex : orderOf (q x) ∣ N.index := by
    simpa only [N.index_eq_card] using orderOf_dvd_natCard (q x)
  have horderOne : orderOf (q x) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop horderL horderIndex
  exact (QuotientGroup.eq_one_iff x).mp
    (by simpa [q] using orderOf_eq_one_iff.mp horderOne)

/-- A cyclic Sylow subgroup rules out elementary-abelian rank two. -/
private theorem not_rankTwo_of_cyclic_sylow15_4
    {H P : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hPH : IsSylowSubgroupOf p P H) (hcyc : IsCyclic P) :
    ¬ HasElementaryAbelianRankAtLeast p 2 H := by
  rintro ⟨A, hAH, hA⟩
  obtain ⟨Q, hQP⟩ := hPH
  let AH : Subgroup H := A.subgroupOf H
  have hAHrank : IsElementaryAbelianOfRank p 2 AH := hA.subgroupOf hAH
  obtain ⟨S, hAHS⟩ := hAHrank.isPGroup.exists_le_sylow
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq H S Q
  let B : Subgroup H := AH.map (MulAut.conj x).toMonoidHom
  have hBQ : B ≤ (Q : Subgroup H) := by
    have hSQ :
        (S : Subgroup H).map (MulAut.conj x).toMonoidHom =
          (Q : Subgroup H) := by
      change MulAut.conj x • (S : Subgroup H) = (Q : Subgroup H)
      rw [← Sylow.coe_subgroup_smul, hx]
    exact (Subgroup.map_mono hAHS).trans_eq hSQ
  let BG : Subgroup G := B.map H.subtype
  have hBGP : BG ≤ P := by
    rw [hQP]
    exact Subgroup.map_mono hBQ
  have hBG : IsElementaryAbelianOfRank p 2 BG :=
    (hAHrank.map_of_injective (MulAut.conj x).toMonoidHom
      (MulAut.conj x).injective).map_of_injective
        H.subtype H.subtype_injective
  letI : IsCyclic P := hcyc
  let eBG : BG.subgroupOf P ≃* BG :=
    Subgroup.subgroupOfEquivOfLe hBGP
  have hcycBGsub : IsCyclic (BG.subgroupOf P) := by infer_instance
  have hcycBG : IsCyclic BG := eBG.isCyclic.mp hcycBGsub
  exact hBG.not_isCyclic Fact.out hcycBG

/-- `BGsection15.v: nilpotent_Hall_sigma`, Corollary 15.4. -/
theorem nilpotent_Hall_sigma
    {H : Subgroup G}
    (hHnil : Group.IsNilpotent H)
    (hHallH : IsHall (primeSupport (Nat.card H)) H) :
    ∃ M : Subgroup G,
      M ∈ minSimple_max_groups (G := G) ∧ H ≤ sigmaCore M := by
  classical
  by_cases hHbot : H = ⊥
  · obtain ⟨M, hM⟩ := any_mmax (G := G)
    exact ⟨M, hM, by simpa [hHbot]⟩
  have hHcard : Nat.card H ≠ 1 :=
    fun hcard ↦ hHbot (Subgroup.card_eq_one.mp hcard)
  obtain ⟨p, hp, hpH⟩ := Nat.exists_prime_and_dvd hHcard
  letI : Fact p.Prime := ⟨hp⟩
  let S : Subgroup G := (pCore p H).map H.subtype
  have hSsylowH : IsSylowSubgroupOf p S H := by
    let P : Sylow p H := Classical.choice Sylow.nonempty
    refine ⟨P, ?_⟩
    dsimp only [S]
    rw [pCore_eq_sylow_of_isNilpotent P]
  have hSne : S ≠ ⊥ := by
    intro hSbot
    have hcoreBot : pCore p H = ⊥ := by
      exact (Subgroup.map_eq_bot_iff_of_injective
        (pCore p H) H.subtype_injective).mp hSbot
    exact (pCore_ne_bot_iff_dvd_card_of_isNilpotent p).mpr hpH hcoreBot
  have hSproper : Subgroup.normalizer (S : Set G) < ⊤ :=
    mFT_norm_proper S hSne
      (mFT_pgroup_proper S hSsylowH.isPGroup)
  obtain ⟨M, hM, hNormSM⟩ :=
    mmax_exists (Subgroup.normalizer (S : Set G)) hSproper
  have hHNormS : H ≤ Subgroup.normalizer (S : Set G) := by
    rw [← H.range_subtype, MonoidHom.range_eq_map]
    change (⊤ : Subgroup H).map H.subtype ≤
      Subgroup.normalizer ((pCore p H).map H.subtype : Set G)
    rw [← Subgroup.normalizer_eq_top_iff.mpr
      (inferInstance : (pCore p H).Normal)]
    exact (pCore p H).le_normalizer_map H.subtype
  have hHM : H ≤ M := hHNormS.trans hNormSM
  have hSM : S ≤ M := (Subgroup.map_subtype_le _).trans hHM
  have hpHindex : ¬ p ∣ H.index := by
    intro hpIndex
    exact hHallH.isPiNumber_index hp hpIndex ⟨hp, hpH⟩
  have hpHtopIndex : ¬ p ∣ (H.subgroupOf (⊤ : Subgroup G)).index := by
    change ¬ p ∣ H.relIndex (⊤ : Subgroup G)
    simpa only [H.relIndex_top_right] using hpHindex
  have hSsylowG : IsSylowSubgroupOf p S ⊤ :=
    hSsylowH.extend_of_not_dvd_index le_top hpHtopIndex
  have hSsylowM : IsSylowSubgroupOf p S M :=
    hSsylowG.restrict_of_le hSM le_top
  have hpSigma : p ∈ sigmaPrimes M := by
    obtain ⟨P, hSP⟩ := hSsylowM
    refine ⟨hp, P, ?_⟩
    simpa only [ambientSylow, ← hSP] using hNormSM
  have hSMs : S ≤ sigmaCore M := by
    let SM : Subgroup M := S.subgroupOf M
    have hSMp : IsPGroup p SM :=
      hSsylowM.isPGroup.of_equiv
        (Subgroup.subgroupOfEquivOfLe hSM).symm
    have hSMpi : IsPiNumber (sigmaPrimes M) (Nat.card SM) :=
      hSMp.isPiNumber_natCard hpSigma
    have hle : SM ≤ (sigmaCore M).subgroupOf M :=
      subgroup_le_normal_isHall15_4
        (by simpa using sigmaCore_normal M) (Msigma_Hall hM) hSMpi
    intro x hx
    exact hle (show (⟨x, hSM hx⟩ : M) ∈ SM from hx)
  refine ⟨M, hM, ?_⟩
  calc
    H = (sylowSup H).map H.subtype := by
      rw [sylowSup_eq_top]
      exact H.range_subtype.symm.trans
        (MonoidHom.range_eq_map H.subtype)
    _ = ⨆ q : {q : ℕ // q.Prime},
        ((Classical.choice
          (Sylow.nonempty (p := (q : ℕ)) (G := H)) : Sylow q H) :
          Subgroup H).map H.subtype := by
      rw [sylowSup, Subgroup.map_iSup]
    _ ≤ sigmaCore M := by
      apply iSup_le
      intro q
      letI : Fact (q : ℕ).Prime := ⟨q.property⟩
      let Pq : Sylow (q : ℕ) H := Classical.choice Sylow.nonempty
      let Sq : Subgroup G := (Pq : Subgroup H).map H.subtype
      change Sq ≤ sigmaCore M
      have hSqsylowH : IsSylowSubgroupOf (q : ℕ) Sq H := ⟨Pq, rfl⟩
      have hSqH : Sq ≤ H := Subgroup.map_subtype_le _
      have hSqM : Sq ≤ M := hSqH.trans hHM
      by_cases hqp : (q : ℕ) = p
      · have hSqS : Sq = S := by
          dsimp only [Sq, S]
          rw [← pCore_eq_sylow_of_isNilpotent Pq, hqp]
        exact hSqS.le.trans hSMs
      by_cases hSqbot : Sq = ⊥
      · simpa only [hSqbot] using
          (bot_le : (⊥ : Subgroup G) ≤ sigmaCore M)
      have hSqCentS : Sq ≤ centralizerWithin M S := by
        rintro x ⟨xH, hxPq, rfl⟩
        refine ⟨hHM xH.property, ?_⟩
        intro s hsS
        rcases hsS with ⟨sH, hsCore, rfl⟩
        have hxCore : xH ∈ pCore (q : ℕ) H := by
          rw [pCore_eq_sylow_of_isNilpotent Pq]
          exact hxPq
        have hxPrime : xH ∈ pPrimeCore p H :=
          (pCore_le_pPrimeCore_of_ne (G := H) (p := p) (q := (q : ℕ))
            (fun hpq ↦ hqp hpq.symm)) hxCore
        have hsCent :=
          (pCore_le_centralizer_pPrimeCore (G := H) p) hsCore
        exact congrArg Subtype.val
          (Subgroup.mem_centralizer_iff.mp hsCent xH hxPrime).symm
      have hqSq : (q : ℕ) ∣ Nat.card Sq :=
        hSqsylowH.isPGroup.card_eq_or_dvd.resolve_left
          (fun hcard ↦ hSqbot (Subgroup.card_eq_one.mp hcard))
      have hqH : (q : ℕ) ∣ Nat.card H :=
        hqSq.trans (Subgroup.card_dvd_of_le hSqH)
      have hqSupport : (q : ℕ) ∈ primeSupport (Nat.card H) :=
        ⟨q.property, hqH⟩
      have hqNotIndexH : ¬ (q : ℕ) ∣ H.index := by
        intro hdiv
        exact hHallH.isPiNumber_index q.property hdiv hqSupport
      have hqNotIndexHtop :
          ¬ (q : ℕ) ∣ (H.subgroupOf (⊤ : Subgroup G)).index := by
        change ¬ (q : ℕ) ∣ H.relIndex (⊤ : Subgroup G)
        simpa only [H.relIndex_top_right] using hqNotIndexH
      have hSqsylowG : IsSylowSubgroupOf (q : ℕ) Sq (⊤ : Subgroup G) :=
        hSqsylowH.extend_of_not_dvd_index le_top hqNotIndexHtop
      have hSqsylowM : IsSylowSubgroupOf (q : ℕ) Sq M :=
        hSqsylowG.restrict_of_le hSqM le_top
      have hSsylowMs : IsSylowSubgroupOf p S (sigmaCore M) :=
        hSsylowM.restrict_of_le hSMs (sigmaCore_le M)
      obtain ⟨PS, hSPS⟩ := hSsylowMs
      have hSsubEq :
          S.subgroupOf (sigmaCore M) = (PS : Subgroup (sigmaCore M)) := by
        rw [hSPS]
        exact Subgroup.comap_map_eq_self_of_injective
          (sigmaCore M).subtype_injective _
      have hHallS : IsHall (primeSupport (Nat.card PS))
          (S.subgroupOf (sigmaCore M)) := by
        rw [hSsubEq]
        exact sylow_isHall_primeSupport PS
      obtain ⟨X, _hXM, hXcyclic, hXtau2, hcentSd⟩ :=
        cent_Hall_sigma_sdprod hM hSMs hHallS hSne
      let C : Subgroup G := centralizerWithin M S
      let Cs : Subgroup G := centralizerWithin (sigmaCore M) S
      have hSqC : Sq ≤ C := by simpa only [C] using hSqCentS
      have hCsMs : Cs ≤ sigmaCore M := by
        simpa only [Cs] using
          (centralizerWithin_le_left (sigmaCore M) S)
      have hsd : IsInternalSemidirectProductIn Cs X C := by
        simpa only [Cs, C] using hcentSd
      have hCsTauCompl : IsPiNumber (tau2Primes M)ᶜ (Nat.card Cs) := by
        intro r hr hrCs hrTau
        have hrSigma : r ∈ sigmaPrimes M :=
          sigmaCore_isPiNumber M hr
            (hrCs.trans (Subgroup.card_dvd_of_le hCsMs))
        exact hrTau.2.1 hrSigma
      have hHallCs : IsHall (tau2Primes M)ᶜ (Cs.subgroupOf C) := by
        constructor
        · rw [MathlibSupport.natCard_subgroupOf_eq hsd.1]
          exact hCsTauCompl
        · rw [hsd.2.2.2.symm.index_eq_card,
              MathlibSupport.natCard_subgroupOf_eq hsd.2.1]
          simpa only [compl_compl] using hXtau2
      have hHallX : IsHall (tau2Primes M) (X.subgroupOf C) := by
        constructor
        · rw [MathlibSupport.natCard_subgroupOf_eq hsd.2.1]
          exact hXtau2
        · rw [hsd.2.2.2.index_eq_card,
              MathlibSupport.natCard_subgroupOf_eq hsd.1]
          exact hCsTauCompl
      by_cases hqTau : (q : ℕ) ∈ tau2Primes M
      · have hSqsylowC : IsSylowSubgroupOf (q : ℕ) Sq C :=
          hSqsylowM.restrict_of_le hSqC
            (by simpa only [C] using centralizerWithin_le_left M S)
        let PX : Sylow (q : ℕ) X := Classical.choice Sylow.nonempty
        let TX : Subgroup G := (PX : Subgroup X).map X.subtype
        have hTXleX : TX ≤ X := Subgroup.map_subtype_le _
        have hTXcyclic : IsCyclic TX := by
          let eTX : TX.subgroupOf X ≃* TX :=
            Subgroup.subgroupOfEquivOfLe hTXleX
          letI : IsCyclic X := hXcyclic
          have hsubCyclic : IsCyclic (TX.subgroupOf X) := by infer_instance
          exact eTX.isCyclic.mp hsubCyclic
        have hTXsylowX : IsSylowSubgroupOf (q : ℕ) TX X := ⟨PX, rfl⟩
        have hqNotIndexXC : ¬ (q : ℕ) ∣ (X.subgroupOf C).index := by
          intro hdiv
          exact hHallX.isPiNumber_index q.property hdiv hqTau
        have hTXsylowC : IsSylowSubgroupOf (q : ℕ) TX C :=
          hTXsylowX.extend_of_not_dvd_index hsd.2.1 hqNotIndexXC
        obtain ⟨PC, hSqPC⟩ := hSqsylowC
        obtain ⟨QC, hTXQC⟩ := hTXsylowC
        have hQCcyclic : IsCyclic QC := by
          let eQC : QC ≃* ((QC : Subgroup C).map C.subtype) :=
            (QC : Subgroup C).equivMapOfInjective
              C.subtype C.subtype_injective
          apply eQC.isCyclic.mpr
          rw [← hTXQC]
          exact hTXcyclic
        have hPCcyclic : IsCyclic PC :=
          (Sylow.equiv PC QC).isCyclic.mpr hQCcyclic
        have hSqcyclic : IsCyclic Sq := by
          let ePC : PC ≃* ((PC : Subgroup C).map C.subtype) :=
            (PC : Subgroup C).equivMapOfInjective
              C.subtype C.subtype_injective
          rw [hSqPC]
          exact ePC.isCyclic.mp hPCcyclic
        exfalso
        exact (not_rankTwo_of_cyclic_sylow15_4 hSqsylowM hSqcyclic)
          hqTau.2.2.1
      · have hSqPi : IsPiNumber (tau2Primes M)ᶜ
            (Nat.card (Sq.subgroupOf C)) := by
          rw [MathlibSupport.natCard_subgroupOf_eq hSqC]
          exact hSqsylowH.isPGroup.isPiNumber_natCard hqTau
        have hsub : Sq.subgroupOf C ≤ Cs.subgroupOf C :=
          subgroup_le_normal_isHall15_4 hsd.2.2.1 hHallCs hSqPi
        intro x hxSq
        let xC : C := ⟨x, hSqC hxSq⟩
        have hxSqC : xC ∈ Sq.subgroupOf C := hxSq
        have hxCsC : xC ∈ Cs.subgroupOf C := hsub hxSqC
        change (xC : G) ∈ sigmaCore M
        exact hCsMs hxCsC

/-! ## Corollary 15.5 -/

private theorem nilpotent_normal_le_fittingWithin_15_5
    {A B : Subgroup G} (hAB : A ≤ B)
    (hAnormal : (A.subgroupOf B).Normal)
    (hAnil : Group.IsNilpotent A) :
    A ≤ fittingWithin B := by
  let AB : Subgroup B := A.subgroupOf B
  let eAB : AB ≃* A := Subgroup.subgroupOfEquivOfLe hAB
  letI : AB.Normal := by simpa only [AB] using hAnormal
  letI : Group.IsNilpotent AB := by
    exact Group.nilpotent_of_mulEquiv eAB.symm
  have hcore : AB ≤ fittingCore B :=
    nilpotent_normal_le_fittingCore (by infer_instance) (by infer_instance)
  change A ≤ (fittingCore B).map B.subtype
  rw [← Subgroup.map_subgroupOf_eq_of_le hAB]
  exact Subgroup.map_mono hcore

private theorem isNilpotent_of_isMulCommutative_15_5
    {K : Type u} [Group K] (hK : IsMulCommutative K) :
    Group.IsNilpotent K :=
  ⟨1, Subgroup.upperCentralSeries_one_eq_top_iff.mpr hK⟩

private theorem direct_sup_eq_15_5
    {A B C : Subgroup G} (h : IsInternalDirectProductIn A B C) :
    A ⊔ B = C := by
  apply le_antisymm (sup_le h.left_le h.right_le)
  intro z hz
  let zC : C := ⟨z, hz⟩
  have hzTop : zC ∈ (A.subgroupOf C) ⊔ (B.subgroupOf C) := by
    rw [h.complement.sup_eq_top]
    exact Subgroup.mem_top zC
  have hzSub : zC ∈ (A ⊔ B).subgroupOf C := by
    rw [Subgroup.subgroupOf_sup h.left_le h.right_le]
    exact hzTop
  exact hzSub

private theorem piCore_isHall_of_isNilpotent_15_5
    {K : Type u} [Group K] [Finite K] [Group.IsNilpotent K]
    (pi : Set ℕ) : IsHall pi (piCore pi K) := by
  exact ⟨piCore_isPiNumber pi, by
    intro p hp hpIndex hpPi
    letI : Fact p.Prime := ⟨hp⟩
    let P : Sylow p K := Classical.choice Sylow.nonempty
    have hPnormal : (P : Subgroup K).Normal := by infer_instance
    have hPle : (P : Subgroup K) ≤ piCore pi K :=
      le_piCore hPnormal (P.isPGroup'.isPiNumber_natCard hpPi)
    exact P.not_dvd_index
      (hpIndex.trans (Subgroup.index_dvd_of_le hPle))⟩

private theorem mapped_complementary_piCores_direct_15_5
    {K : Subgroup G} {pi : Set ℕ}
    (hKnil : Group.IsNilpotent K) :
    IsInternalDirectProductIn
      ((piCore pi K).map K.subtype)
      ((piCore piᶜ K).map K.subtype) K := by
  letI : Group.IsNilpotent K := hKnil
  let A : Subgroup G := (piCore pi K).map K.subtype
  let B : Subgroup G := (piCore piᶜ K).map K.subtype
  have hAK : A ≤ K := Subgroup.map_subtype_le _
  have hBK : B ≤ K := Subgroup.map_subtype_le _
  have hAsub : A.subgroupOf K = piCore pi K := by
    change ((piCore pi K).map K.subtype).comap K.subtype = piCore pi K
    exact Subgroup.comap_map_eq_self_of_injective K.subtype_injective _
  have hBsub : B.subgroupOf K = piCore piᶜ K := by
    change ((piCore piᶜ K).map K.subtype).comap K.subtype = piCore piᶜ K
    exact Subgroup.comap_map_eq_self_of_injective K.subtype_injective _
  have hAnormal : (A.subgroupOf K).Normal := by rw [hAsub]; infer_instance
  have hBnormal : (B.subgroupOf K).Normal := by rw [hBsub]; infer_instance
  have hAHall : IsHall pi (A.subgroupOf K) := by
    rw [hAsub]
    exact piCore_isHall_of_isNilpotent_15_5 pi
  have hBHall : IsHall piᶜ (B.subgroupOf K) := by
    rw [hBsub]
    exact piCore_isHall_of_isNilpotent_15_5 piᶜ
  have hsd := normal_complementary_hall_sdprod_15_3
    hAK hBK hAnormal hAHall hBHall
  have hcomm := Subgroup.commute_of_normal_of_disjoint
    (A.subgroupOf K) (B.subgroupOf K)
    hAnormal hBnormal hsd.2.2.2.disjoint
  exact
    { left_le := hAK
      right_le := hBK
      complement := hsd.2.2.2
      commute := by
        intro a b
        let aK : K := ⟨a, hAK a.property⟩
        let bK : K := ⟨b, hBK b.property⟩
        exact congrArg Subtype.val
          (hcomm aK bK a.property b.property).eq }

private theorem right_isHall_compl_of_sdprod_15_5
    {A B C : Subgroup G} {pi : Set ℕ}
    (h : IsInternalSemidirectProductIn A B C)
    (hApi : IsPiNumber pi (Nat.card A))
    (hBpi : IsPiNumber piᶜ (Nat.card B)) :
    IsHall piᶜ (B.subgroupOf C) := by
  constructor
  · simpa only [MathlibSupport.natCard_subgroupOf_eq h.2.1] using hBpi
  · rw [h.2.2.2.index_eq_card,
      MathlibSupport.natCard_subgroupOf_eq h.1]
    simpa only [compl_compl] using hApi

private theorem left_isHall_compl_of_right_isHall_15_5
    {A B C : Subgroup G} {pi : Set ℕ}
    (h : IsInternalSemidirectProductIn A B C)
    (hB : IsHall pi (B.subgroupOf C)) :
    IsHall piᶜ (A.subgroupOf C) := by
  constructor
  · rw [← h.2.2.2.index_eq_card]
    exact hB.isPiNumber_index
  · rw [h.2.2.2.symm.index_eq_card]
    simpa only [compl_compl,
      MathlibSupport.natCard_subgroupOf_eq h.2.1] using
        hB.isPiNumber_card

private theorem isHall_singleton_of_isSylowSubgroupOf15_5
    {p : ℕ} [Fact p.Prime] {S H : Subgroup G}
    (hS : IsSylowSubgroupOf p S H) :
    IsHall ({p} : Set ℕ) (S.subgroupOf H) := by
  have hSH : S ≤ H := by
    rcases hS with ⟨P, rfl⟩
    exact Subgroup.map_subtype_le _
  constructor
  · rw [MathlibSupport.natCard_subgroupOf_eq hSH]
    exact hS.isPGroup.isPiNumber_natCard (Set.mem_singleton p)
  · intro q hq hqIndex hqp
    have hqp' : q = p := Set.mem_singleton_iff.mp hqp
    subst q
    obtain ⟨P, hSP⟩ := hS
    have hsubEq : S.subgroupOf H = (P : Subgroup H) := by
      rw [hSP]
      exact Subgroup.comap_map_eq_self_of_injective
        H.subtype_injective (P : Subgroup H)
    rw [hsubEq] at hqIndex
    exact P.not_dvd_index hqIndex

private theorem right_direct_factor_le_centralizer_normal_15_5
    {M H A Y : Subgroup G}
    (h : IsInternalDirectProductIn A Y (fittingWithin M))
    (hHA : H ≤ A)
    (hMnormY : M ≤ Subgroup.normalizer (Y : Set G)) :
    Y ≤ centralizerWithin M H ∧
      (Y.subgroupOf (centralizerWithin M H)).Normal := by
  have hYM : Y ≤ M := le_trans h.right_le (fittingWithin_le M)
  have hYC : Y ≤ centralizerWithin M H := by
    intro y hy
    refine ⟨hYM hy, ?_⟩
    intro x hx
    exact (h.commute ⟨x, hHA hx⟩ ⟨y, hy⟩).eq
  exact ⟨hYC,
    (Subgroup.normal_subgroupOf_iff_le_normalizer hYC).mpr
      ((centralizerWithin_le_left M H).trans hMnormY)⟩

private theorem fittingWithin_sigmaCore_eq_map_piCore_15_5
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G)) :
    fittingWithin (sigmaCore M) =
      (piCore (sigmaPrimes M) (fittingWithin M)).map
        (fittingWithin M).subtype := by
  let Ms := sigmaCore M
  let F := fittingWithin M
  let O : Subgroup F := piCore (sigmaPrimes M) F
  let L : Subgroup G := O.map F.subtype
  change fittingWithin Ms = L
  have hMsM : Ms ≤ M := sigmaCore_le M
  have hMsnormal : (Ms.subgroupOf M).Normal := by
    simpa only [Ms] using sigmaCore_normal M
  have hMnormMs : M ≤ Subgroup.normalizer (Ms : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMsM).mp hMsnormal
  have hFM : F ≤ M := fittingWithin_le M
  have hMnormF : M ≤ Subgroup.normalizer (F : Set G) :=
    fittingWithin_le_normalizer M
  have hFMsM : fittingWithin Ms ≤ M := (fittingWithin_le Ms).trans hMsM
  have hMnormFMs : M ≤ Subgroup.normalizer (fittingWithin Ms : Set G) :=
    le_normalizer_fittingWithin_of_le_normalizer hMnormMs
  have hFMsNormalM : ((fittingWithin Ms).subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hFMsM).mpr hMnormFMs
  have hFMsF : fittingWithin Ms ≤ F :=
    nilpotent_normal_le_fittingWithin_15_5 hFMsM hFMsNormalM
      (fittingWithin_isNilpotent Ms)
  have hFMsPi : IsPiNumber (sigmaPrimes M)
      (Nat.card (fittingWithin Ms)) :=
    (sigmaCore_isPiNumber M).of_dvd
      (Subgroup.card_dvd_of_le (fittingWithin_le Ms))
  have hFMsNormalF : ((fittingWithin Ms).subgroupOf F).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hFMsF).mpr
      (hFM.trans hMnormFMs)
  have hFMsCore : (fittingWithin Ms).subgroupOf F ≤ O := by
    apply le_piCore hFMsNormalF
    simpa only [MathlibSupport.natCard_subgroupOf_eq hFMsF] using hFMsPi
  have hFMsL : fittingWithin Ms ≤ L := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hFMsF]
    exact Subgroup.map_mono hFMsCore
  have hLF : L ≤ F := Subgroup.map_subtype_le _
  have hLM : L ≤ M := hLF.trans hFM
  have hnormFL : Subgroup.normalizer (F : Set G) ≤
      Subgroup.normalizer (L : Set G) := by
    simpa only [L] using
      (characteristic_map_subtype_le_normalizer_15_3 F O)
  have hMnormL : M ≤ Subgroup.normalizer (L : Set G) := hMnormF.trans hnormFL
  have hLnormalM : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).mpr hMnormL
  have hLpi : IsPiNumber (sigmaPrimes M) (Nat.card L) := by
    dsimp only [L, O]
    rw [Subgroup.card_map_of_injective F.subtype_injective]
    exact piCore_isPiNumber (sigmaPrimes M)
  have hLleMsSub : (L.subgroupOf M) ≤ (Ms.subgroupOf M) := by
    apply normal_isPiNumber_le_isHall hLnormalM
    · simpa only [MathlibSupport.natCard_subgroupOf_eq hLM] using hLpi
    · simpa only [Ms] using Msigma_Hall hM
  have hLMs : L ≤ Ms := by
    intro x hx
    let xM : M := ⟨x, hLM hx⟩
    exact hLleMsSub (show xM ∈ L.subgroupOf M from hx)
  have hLnormalMs : (L.subgroupOf Ms).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLMs).mpr
      (hMsM.trans hMnormL)
  have hLnil : Group.IsNilpotent L :=
    isNilpotent_of_le_15 (fittingWithin_isNilpotent M) hLF
  have hLFMs : L ≤ fittingWithin Ms :=
    nilpotent_normal_le_fittingWithin_15_5 hLMs hLnormalMs hLnil
  exact le_antisymm hFMsL hLFMs

private theorem fittingWithin_le_H_join_centralizer_15_5
    {M H : Subgroup G} {pi : Set ℕ}
    (hHF : H ≤ fittingWithin M)
    (hHall : IsHall pi (H.subgroupOf M)) :
    fittingWithin M ≤ H ⊔ centralizerWithin M H := by
  let F := fittingWithin M
  letI : Group.IsNilpotent F := fittingWithin_isNilpotent M
  have hHallF : IsHall pi (H.subgroupOf F) :=
    hall_restrict_15_3 hHF (fittingWithin_le M) hHall
  have hHcore : H.subgroupOf F = piCore pi F :=
    hall_eq_piCore_of_isNilpotent_15_3 hHallF
  let C : Subgroup G := (piCore piᶜ F).map F.subtype
  have hd := mapped_complementary_piCores_direct_15_5
    (K := F) (pi := pi) (fittingWithin_isNilpotent M)
  have hHmap : (H.subgroupOf F).map F.subtype = H :=
    Subgroup.map_subgroupOf_eq_of_le hHF
  rw [← hHcore, hHmap] at hd
  have hCcent : C ≤ centralizerWithin M H := by
    intro c hc
    refine ⟨(le_trans hd.right_le (fittingWithin_le M)) hc, ?_⟩
    intro h hh
    exact (hd.commute ⟨h, hh⟩ ⟨c, hc⟩).eq
  calc
    F = H ⊔ C := (direct_sup_eq_15_5 hd).symm
    _ ≤ H ⊔ centralizerWithin M H :=
      sup_le le_sup_left (hCcent.trans le_sup_right)

private theorem sigmaCore_centralizer_le_fitting_15_5
    {M H X : Subgroup G}
    (heq : H = sigmaCore M)
    (hMsNil : Group.IsNilpotent (sigmaCore M))
    (hXcyclic : IsCyclic X)
    (hsd : IsInternalSemidirectProductIn
      (centralizerWithin (sigmaCore M) H) X
      (centralizerWithin M H)) :
    centralizerWithin M H ≤ fittingWithin M := by
  let Cs := centralizerWithin (sigmaCore M) H
  let C := centralizerWithin M H
  have hdir : IsInternalDirectProductIn Cs X C :=
    { left_le := hsd.1
      right_le := hsd.2.1
      complement := hsd.2.2.2
      commute := by
        intro c x
        have hxC : (x : G) ∈ C := hsd.2.1 x.property
        have hcH : (c : G) ∈ H := by rw [heq]; exact c.property.1
        exact hxC.2 (c : G) hcH }
  have hCsNil : Group.IsNilpotent Cs :=
    isNilpotent_of_le_15 hMsNil (centralizerWithin_le_left _ _)
  have hXNil : Group.IsNilpotent X :=
    isNilpotent_of_isMulCommutative_15_5 hXcyclic.isMulCommutative
  have hCnil : Group.IsNilpotent C := by
    letI : Group.IsNilpotent Cs := hCsNil
    letI : Group.IsNilpotent X := hXNil
    exact Group.nilpotent_of_mulEquiv hdir.mulEquiv
  have hCM : C ≤ M := centralizerWithin_le_left M H
  have hMnormH : M ≤ Subgroup.normalizer (H : Set G) := by
    rw [heq]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (sigmaCore_le M)).mp
      (sigmaCore_normal M)
  have hMnormC : M ≤ Subgroup.normalizer (C : Set G) :=
    centralizerWithin_normalized_by_common_normalizer_15
      (Subgroup.le_normalizer : M ≤ Subgroup.normalizer (M : Set G))
      hMnormH
  have hCnormal : (C.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCM).mpr hMnormC
  exact nilpotent_normal_le_fittingWithin_15_5 hCM hCnormal hCnil

/-- `BGsection15.v: Fitting_structure`, Corollary 15.5. -/
theorem Fitting_structure
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G)) :
    FittingStructure M := by
  classical
  let H := Fitting_core M
  let Y := fittingSigmaPrimeCore M
  let Ms := sigmaCore M
  have hFnil : Group.IsNilpotent (fittingWithin M) :=
    fittingWithin_isNilpotent M
  have hHfit : H ≤ fittingWithin M := Fcore_sub_Fitting M
  have hMsM : Ms ≤ M := sigmaCore_le M
  have hMsnormal : (Ms.subgroupOf M).Normal := by
    simpa [Ms] using sigmaCore_normal M
  have hYfit : Y ≤ fittingWithin M := by
    exact Subgroup.map_subtype_le _

  have hfitSigma := fittingWithin_sigmaCore_eq_map_piCore_15_5 hM
  have hfitDprod : IsInternalDirectProductIn (fittingWithin Ms) Y
      (fittingWithin M) := by
    have hd := mapped_complementary_piCores_direct_15_5
      (K := fittingWithin M) (pi := sigmaPrimes M) hFnil
    rw [← hfitSigma] at hd
    simpa only [Ms, Y, fittingSigmaPrimeCore] using hd
  have hs := Fcore_structure hM
  have hHallH : IsHall (primeSupport (Nat.card H)) (H.subgroupOf Ms) :=
    hall_restrict_15_3 hs.Fcore_le_sigma hMsM (Fcore_Hall M)
  obtain ⟨X, hXM, hXcyclic, hXtau2, hcentSd⟩ :=
    cent_Hall_sigma_sdprod hM
      hs.Fcore_le_sigma hHallH hs.Fcore_ne_bot
  have hCsPi : IsPiNumber (sigmaPrimes M)
      (Nat.card (centralizerWithin Ms H)) :=
    (sigmaCore_isPiNumber M).of_dvd
      (Subgroup.card_dvd_of_le (centralizerWithin_le_left Ms H))
  have hXsigmaCompl : IsPiNumber (sigmaPrimes M)ᶜ (Nat.card X) :=
    hXtau2.mono fun _ hp => hp.2.1
  have hXHall : IsHall (sigmaPrimes M)ᶜ
      (X.subgroupOf (centralizerWithin M H)) :=
    right_isHall_compl_of_sdprod_15_5 hcentSd hCsPi hXsigmaCompl
  have hMnormH : M ≤ Subgroup.normalizer (H : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (Fcore_sub M)).mp
      (Fcore_normal M)
  have hHnormalMs : (H.subgroupOf Ms).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hs.Fcore_le_sigma).mpr
      (hMsM.trans hMnormH)
  have hHleft : H ≤ fittingWithin Ms :=
    nilpotent_normal_le_fittingWithin_15_5 hs.Fcore_le_sigma
      hHnormalMs (Fcore_nil M)
  have hMnormY : M ≤ Subgroup.normalizer (Y : Set G) := by
    dsimp only [Y, fittingSigmaPrimeCore]
    exact (fittingWithin_le_normalizer M).trans
      (characteristic_map_subtype_le_normalizer_15_3
        (fittingWithin M)
        (piCore (sigmaPrimes M)ᶜ (fittingWithin M)))
  obtain ⟨hYC, hYnormalC⟩ :=
    right_direct_factor_le_centralizer_normal_15_5
      hfitDprod hHleft hMnormY
  have hYpi : IsPiNumber (sigmaPrimes M)ᶜ (Nat.card Y) := by
    dsimp only [Y, fittingSigmaPrimeCore]
    rw [Subgroup.card_map_of_injective (fittingWithin M).subtype_injective]
    exact piCore_isPiNumber (sigmaPrimes M)ᶜ
  have hYX : Y ≤ X := by
    let C := centralizerWithin M H
    have hsub : (Y.subgroupOf C) ≤ (X.subgroupOf C) := by
      apply normal_isPiNumber_le_isHall hYnormalC
      · simpa only [MathlibSupport.natCard_subgroupOf_eq hYC] using hYpi
      · exact hXHall
    intro y hy
    let yC : C := ⟨y, hYC hy⟩
    exact hsub (show yC ∈ Y.subgroupOf C from hy)
  have hYcyclic : IsCyclic Y :=
    isCyclic_of_le_15 hYX hXcyclic
  have hYtau2 : IsPiNumber (tau2Primes M) (Nat.card Y) :=
    hXtau2.of_dvd (Subgroup.card_dvd_of_le hYX)

  obtain ⟨K, hKM, hHallK⟩ :=
    MathlibSupport.exists_ambient_isHall_of_isSolvable
      (mmax_sol hM) (kappaPrimes M)
  obtain ⟨U, hcompl⟩ := ex_kappa_compl hM hKM hHallK
  have hkappa := kappa_structure hM hcompl
  have htypePfit : M ∈ typePMaximalSubgroups (G := G) →
      fittingWithin M ≤ derivedWithin M := by
    intro hP
    have hKne : K ≠ ⊥ := by
      intro hK
      exact hP.2 ((trivg_kappa hM hKM hHallK).1 hK)
    have hderived := hkappa.derived_decomposition hKne
    have hDerEq : sigmaCore M ⊔ U = derivedWithin M :=
      semidirect_sup_eq_15 hderived
    have hDerHall : IsHall (kappaPrimes M)ᶜ
        ((derivedWithin M).subgroupOf M) := by
      rw [← hDerEq]
      exact left_isHall_compl_of_right_isHall_15_5
        hkappa.sigmaU_K_sdprod hHallK
    have htauKappa : tau2Primes M ⊆ (kappaPrimes M)ᶜ := by
      intro r hrTau hrKappa
      rcases kappa_tau13 hrKappa with hrTau1 | hrTau3
      · exact tau2'1 M hrTau1 hrTau
      · exact tau3'2 M hrTau hrTau3
    have hYkappaCompl : IsPiNumber (kappaPrimes M)ᶜ (Nat.card Y) :=
      hYtau2.mono htauKappa
    have hYM : Y ≤ M := hYfit.trans (fittingWithin_le M)
    have hYnormalM : (Y.subgroupOf M).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hYM).mpr hMnormY
    have hYsub : Y.subgroupOf M ≤ (derivedWithin M).subgroupOf M := by
      apply normal_isPiNumber_le_isHall hYnormalM
      · simpa only [MathlibSupport.natCard_subgroupOf_eq hYM] using
          hYkappaCompl
      · exact hDerHall
    have hYder : Y ≤ derivedWithin M := by
      intro y hy
      let yM : M := ⟨y, hYM hy⟩
      exact hYsub (show yM ∈ Y.subgroupOf M from hy)
    rw [← direct_sup_eq_15_5 hfitDprod]
    exact sup_le
      ((fittingWithin_le Ms).trans hs.sigma_le_derived) hYder

  have hjoin_of_cent_le
      (hcent : centralizerWithin M H ≤ fittingWithin M) :
      H ⊔ centralizerWithin M H = fittingWithin M := by
    apply le_antisymm
    · exact sup_le hHfit hcent
    · exact fittingWithin_le_H_join_centralizer_15_5
        hHfit (Fcore_Hall M)
  have hcommHC :
      ∀ x ∈ H, ∀ y ∈ centralizerWithin M H, Commute x y := by
    intro x hx y hy
    change x * y = y * x
    exact Subgroup.mem_centralizer_iff.mp hy.2 x hx

  have hHder : H ≤ derivedWithin M :=
    hs.Fcore_le_sigma.trans hs.sigma_le_derived
  letI : (H.subgroupOf (derivedWithin M)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hHder).mpr
      ((derivedWithin_le_15 M).trans hMnormH)

  by_cases heq : H = Ms
  · have hcentFit : centralizerWithin M H ≤ fittingWithin M := by
      have hHnil : Group.IsNilpotent H := by
        simpa only [H] using Fcore_nil M
      have hMsNil : Group.IsNilpotent Ms := heq ▸ hHnil
      exact sigmaCore_centralizer_le_fitting_15_5 heq
        (by simpa only [Ms] using hMsNil) hXcyclic hcentSd
    have hInfEq : sigmaCore M ⊓ derivedWithin M = H := by
      calc
        sigmaCore M ⊓ derivedWithin M = sigmaCore M :=
          inf_eq_left.mpr hs.sigma_le_derived
        _ = H := by simpa only [Ms] using heq.symm
    have hquotComm :
        letI : (H.subgroupOf (derivedWithin M)).Normal := by infer_instance
        IsMulCommutative
          (derivedWithin M ⧸ H.subgroupOf (derivedWithin M)) := by
      let S := sigmaCore M ⊓ derivedWithin M
      letI : (S.subgroupOf (derivedWithin M)).Normal := by
        dsimp only [S]
        exact normal_inf_subgroupOf_of_le_15 (sigmaCore_le M)
          (derivedWithin_le_15 M) (sigmaCore_normal M)
      have hsubEq :
          S.subgroupOf (derivedWithin M) =
            H.subgroupOf (derivedWithin M) := by
        exact congrArg
          (fun T : Subgroup G => T.subgroupOf (derivedWithin M))
          (by simpa only [S] using hInfEq)
      let eQuot :
          (derivedWithin M ⧸ S.subgroupOf (derivedWithin M)) ≃*
            (derivedWithin M ⧸ H.subgroupOf (derivedWithin M)) :=
        QuotientGroup.quotientMulEquivOfEq hsubEq
      have hcommS : IsMulCommutative
          (derivedWithin M ⧸ S.subgroupOf (derivedWithin M)) := by
        simpa only [S] using hkappa.derived_mod_sigma_abelian
      exact isMulCommutative_of_mulEquiv_15 eQuot.symm hcommS
    have hquotNil :
        letI : (H.subgroupOf (derivedWithin M)).Normal := by infer_instance
        Group.IsNilpotent (derivedWithin M ⧸ H.subgroupOf (derivedWithin M)) := by
      exact isNilpotent_of_isMulCommutative_15_5 hquotComm
    have hcommDerLeH :
        _root_.commutator (derivedWithin M) ≤
          H.subgroupOf (derivedWithin M) := by
      letI : (H.subgroupOf (derivedWithin M)).Normal := by infer_instance
      exact Subgroup.Normal.quotient_commutative_iff_commutator_le.mp
        hquotComm
    have hsecondFit : secondDerivedWithin M ≤ fittingWithin M := by
      intro x hx
      rcases hx with ⟨z, hz, rfl⟩
      exact hHfit (hcommDerLeH hz)
    exact
      { sigmaPrimeCore_cyclic := hYcyclic
        sigmaPrimeCore_tau2 := hYtau2
        secondDerived_le_fitting := hsecondFit
        Fcore_centralizer_commute := hcommHC
        Fcore_join_centralizer := hjoin_of_cent_le hcentFit
        sigmaFitting_times_sigmaPrimeCore := hfitDprod
        Fcore_le_derived := hs.Fcore_le_sigma.trans hs.sigma_le_derived
        Fcore_normal_derived := by infer_instance
        derived_mod_Fcore_nilpotent := hquotNil
        typeP_fitting_le_derived := htypePfit }

  let q := Nat.card (kappaCentralizer M K)
  obtain ⟨D, hDsigma, hHallD⟩ :=
    MathlibSupport.exists_ambient_isHall_of_isSolvable
      (isSolvable_of_le_15 (mmax_sol hM) hMsM) ({q} : Set ℕ)ᶜ
  have hn := hs.nonnilpotent hKM hHallK heq hDsigma
    (by simpa [q] using hHallD)
  letI : Fact q.Prime := ⟨by
    simpa [q] using hn.card_partner_prime⟩
  let Q := pCoreWithin q M
  have hQH : Q ≤ H := by
    dsimp only [Q, pCoreWithin, H]
    rw [← p_core_Fcore M hn.partner_prime_in_Fcore]
    exact Subgroup.map_subtype_le _
  have hcentFit : centralizerWithin M H ≤ fittingWithin M := by
    rw [← hn.fitting_descriptions.pcore_join_centralizer]
    have hcentHQ : centralizerWithin M H ≤ centralizerWithin M Q := by
      intro x hx
      refine ⟨hx.1, ?_⟩
      intro y hy
      exact hx.2 y (hQH hy)
    exact hcentHQ.trans le_sup_right
  have hQMs : Q ≤ Ms := hQH.trans hs.Fcore_le_sigma
  have hQnormalMs : (Q.subgroupOf Ms).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hQMs).mpr
    exact hMsM.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer
        (show Q ≤ M from by
          dsimp only [Q, pCoreWithin]
          exact Subgroup.map_subtype_le _)).mp
        (pCoreWithin_normal_15 q M))
  have hQDsigma : IsInternalSemidirectProductIn Q D Ms := by
    have hQsylowMs : IsSylowSubgroupOf q Q Ms :=
      hn.pcore_sylow.restrict_of_le hQMs hMsM
    exact normal_complementary_hall_sdprod_15_3
      hQMs hDsigma hQnormalMs
        (isHall_singleton_of_isSylowSubgroupOf15_5 hQsylowMs) hHallD
  have hquotNilMs :
      letI : (H.subgroupOf Ms).Normal := hHnormalMs
      Group.IsNilpotent (Ms ⧸ H.subgroupOf Ms) := by
    let Hs : Subgroup Ms := H.subgroupOf Ms
    letI : Hs.Normal := by simpa only [Hs] using hHnormalMs
    let quo : Ms →* Ms ⧸ Hs := QuotientGroup.mk' Hs
    have hDMs : D ≤ Ms := hQDsigma.2.1
    let f : D →* Ms ⧸ Hs := quo.comp (Subgroup.inclusion hDMs)
    have hf : Function.Surjective f := by
      intro z
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Hs z
      obtain ⟨⟨qx, dx⟩, hqdx⟩ := hQDsigma.2.2.2.2 x
      let dD : D := ⟨(dx : Ms), dx.property⟩
      refine ⟨dD, ?_⟩
      have hqHs : (qx : Ms) ∈ Hs := hQH qx.property
      have hqOne : quo (qx : Ms) = 1 :=
        (QuotientGroup.eq_one_iff (qx : Ms)).mpr hqHs
      change quo (dx : Ms) = quo x
      rw [← hqdx, map_mul, hqOne, one_mul]
    letI : Group.IsNilpotent D := hn.D_nilpotent
    exact Group.nilpotent_of_surjective f hf
  have hquotNil :
      letI : (H.subgroupOf (derivedWithin M)).Normal := by infer_instance
      Group.IsNilpotent
        (derivedWithin M ⧸ H.subgroupOf (derivedWithin M)) := by
    have hMsDer : Ms ≤ derivedWithin M := by
      simpa only [Ms] using le_of_eq hn.sigma_eq_derived
    have hDerMs : derivedWithin M ≤ Ms := by
      simpa only [Ms] using le_of_eq hn.sigma_eq_derived.symm
    let eMs : Ms ≃* derivedWithin M :=
      { toFun := fun x => ⟨x, hMsDer x.property⟩
        invFun := fun x => ⟨x, hDerMs x.property⟩
        left_inv := fun x => Subtype.ext rfl
        right_inv := fun x => Subtype.ext rfl
        map_mul' := fun _ _ => Subtype.ext rfl }
    have hmapH :
        (H.subgroupOf Ms).map eMs.toMonoidHom =
          H.subgroupOf (derivedWithin M) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        let y : Ms := ⟨(x : G), hDerMs x.property⟩
        refine ⟨y, ?_, ?_⟩
        · exact hx
        · apply Subtype.ext
          rfl
    let eQuot :
        (Ms ⧸ H.subgroupOf Ms) ≃*
          (derivedWithin M ⧸ H.subgroupOf (derivedWithin M)) :=
      QuotientGroup.congr (H.subgroupOf Ms)
        (H.subgroupOf (derivedWithin M)) eMs hmapH
    letI : Group.IsNilpotent (Ms ⧸ H.subgroupOf Ms) := hquotNilMs
    exact Group.nilpotent_of_mulEquiv eQuot
  exact
    { sigmaPrimeCore_cyclic := hYcyclic
      sigmaPrimeCore_tau2 := hYtau2
      secondDerived_le_fitting := hn.secondDerived_le_fitting
      Fcore_centralizer_commute := hcommHC
      Fcore_join_centralizer := hjoin_of_cent_le hcentFit
      sigmaFitting_times_sigmaPrimeCore := hfitDprod
      Fcore_le_derived := hs.Fcore_le_sigma.trans hs.sigma_le_derived
      Fcore_normal_derived := by infer_instance
      derived_mod_Fcore_nilpotent := hquotNil
      typeP_fitting_le_derived := htypePfit }

/-! ## Corollary 15.6 -/

/-- `BGsection15.v: Ptype_cyclics`, Corollary 15.6. -/
theorem Ptype_cyclics
    {M K : Subgroup G}
    (hP : M ∈ typePMaximalSubgroups (G := G))
    (hKM : K ≤ M)
    (hHallK : IsHall (kappaPrimes M) (K.subgroupOf M)) :
    PTypeCyclics M K := by
  classical
  have hM : M ∈ minSimple_max_groups (G := G) := hP.1
  letI : IsSolvable M := mmax_sol hM
  have hKne : K ≠ ⊥ := by
    intro hK
    exact hP.2 ((trivg_kappa hM hKM hHallK).1 hK)
  have hs := Ptype_structure hP hKM hHallK
  obtain ⟨Mstar, hemb⟩ := Ptype_embedding hP hKM hHallK
  let Ks := kappaCentralizer M K
  have hKsne : Ks ≠ ⊥ := by
    simpa [Ks, kappaCentralizer, pTypeCentralizer] using hs.Kstar_ne_bot
  have hKscyclic : IsCyclic Ks := by
    exact isCyclic_of_le_15 le_sup_right
      hemb.cyclicStructure.cyclic_join

  /- Source: apply 6.3(a) in `M = M' : K`, then restrict
     `C_(M_sigma)(K)` along `M_sigma <= M'`. -/
  have hKsSecond : Ks ≤ secondDerivedWithin M := by
    let D : Subgroup G := derivedWithin M
    let DM : Subgroup M := D.subgroupOf M
    let KM : Subgroup M := K.subgroupOf M
    have hDleM : D ≤ M := derivedWithin_le_15 M
    have hcopDK : Nat.Coprime (Nat.card D) (Nat.card K) := by
      have hc := hHallK.coprime_card_index
      rw [hemb.derived_sdprod.2.2.2.index_eq_card,
        MathlibSupport.natCard_subgroupOf_eq hKM,
        MathlibSupport.natCard_subgroupOf_eq hemb.derived_sdprod.1] at hc
      simpa only [D, derivedWithin] using hc.symm
    have hDMeq : DM = _root_.commutator M := by
      change
        ((Subgroup.map M.subtype (_root_.commutator M)).comap
          M.subtype) = _root_.commutator M
      exact Subgroup.comap_map_eq_self_of_injective
        M.subtype_injective _
    letI : IsSolvable DM := isSolvable_subgroup_of_isSolvable DM
    letI : DM.Normal := by
      simpa only [DM, D, derivedWithin] using
        hemb.derived_sdprod.2.2.1
    have hcomp : DM.IsComplement' KM := by
      simpa only [DM, KM, D, derivedWithin] using
        hemb.derived_sdprod.2.2.2
    have hnorm : KM ≤ Subgroup.normalizer (DM : Set M) := by
      rw [DM.normalizer_eq_top]
      exact le_top
    have hcop : Nat.Coprime (Nat.card DM) (Nat.card KM) := by
      simpa only [DM, KM,
        MathlibSupport.natCard_subgroupOf_eq hDleM,
        MathlibSupport.natCard_subgroupOf_eq hKM] using hcopDK
    have hder : DM ≤ _root_.commutator M := hDMeq.le
    have h63 :=
      Submission.OddOrder.BG.Section06.coprime_der1_sdprod
        hcomp hnorm hcop hder
    have hmapComm :
        (⁅DM, DM⁆ : Subgroup M).map M.subtype =
          secondDerivedWithin M := by
      rw [Subgroup.map_commutator,
        Subgroup.map_subgroupOf_eq_of_le hDleM,
        secondDerivedWithin, derivedWithin,
        D.map_subtype_commutator]
    intro x hx
    change x ∈ centralizerWithin (sigmaCore M) K at hx
    have hxD : x ∈ D := Msigma_der1 hM hx.1
    let xM : M := ⟨x, hDleM hxD⟩
    have hxCent : xM ∈ centralizerWithin DM KM := by
      refine ⟨hxD, ?_⟩
      intro y hy
      apply Subtype.ext
      exact hx.2 (y : G) hy
    rw [← hmapComm]
    exact ⟨xM, h63.2 hxCent, rfl⟩

  by_cases heq : Fitting_core M = sigmaCore M
  · have hKsF : Ks ≤ Fitting_core M := by
      rw [heq]
      exact centralizerWithin_le_left _ _
    have hnotcyclic : ¬ IsCyclic (Fitting_core M) := by
      intro hFcyclic
      have hfit := Fitting_structure hM
      have hMsCyclic : IsCyclic (sigmaCore M) := by
        exact heq ▸ hFcyclic
      have hleftCyclic : IsCyclic (fittingWithin (sigmaCore M)) :=
        isCyclic_of_le_15 (fittingWithin_le _) hMsCyclic
      have hleftPi :
          IsPiNumber (sigmaPrimes M)
            (Nat.card (fittingWithin (sigmaCore M))) :=
        (sigmaCore_isPiNumber M).of_dvd
          (Subgroup.card_dvd_of_le (fittingWithin_le (sigmaCore M)))
      have hrightPi :
          IsPiNumber (sigmaPrimes M)ᶜ
            (Nat.card (fittingSigmaPrimeCore M)) := by
        rw [fittingSigmaPrimeCore,
          Subgroup.card_map_of_injective
            (fittingWithin M).subtype_injective]
        exact piCore_isPiNumber (sigmaPrimes M)ᶜ
      have hfactorCop :
          Nat.Coprime (Nat.card (fittingWithin (sigmaCore M)))
            (Nat.card (fittingSigmaPrimeCore M)) :=
        hleftPi.coprime_compl hrightPi
      have hfitCyclic : IsCyclic (fittingWithin M) := by
        apply hfit.sigmaFitting_times_sigmaPrimeCore.mulEquiv.isCyclic.mp
        exact Group.isCyclic_prod_iff.mpr
          ⟨hleftCyclic, hfit.sigmaPrimeCore_cyclic, hfactorCop⟩

      /- Source's `Aut_cyclic_abelian`: the derived subgroup of `M`
         centralizes its cyclic Fitting subgroup; self-centralization then
         puts it inside the Fitting subgroup. -/
      let F : Subgroup M := fittingCore M
      let eF : F ≃* fittingWithin M :=
        (fittingCore M).equivMapOfInjective
          M.subtype M.subtype_injective
      have hFCyclic : IsCyclic F := eF.isCyclic.mpr hfitCyclic
      letI : IsCyclic F := hFCyclic
      letI : IsMulCommutative (MulAut F) := by
        apply isMulCommutative_iff.mpr
        intro a b
        obtain ⟨m, hm⟩ := a.toMonoidHom.map_cyclic
        obtain ⟨n, hn⟩ := b.toMonoidHom.map_cyclic
        apply MulEquiv.ext
        intro x
        change a (b x) = b (a x)
        calc
          a (b x) = (b x) ^ m := hm (b x)
          _ = (x ^ n) ^ m := by
            exact congrArg (fun z : F => z ^ m) (by simpa using hn x)
          _ = x ^ (n * m) := (zpow_mul x n m).symm
          _ = x ^ (m * n) := by rw [mul_comm]
          _ = (x ^ m) ^ n := zpow_mul x m n
          _ = b (a x) := by
            simpa [show a x = x ^ m by simpa using hm x] using
              (hn (a x)).symm
      have hDerCent :
          _root_.commutator M ≤ Subgroup.centralizer (F : Set M) := by
        have h :=
          Abelianization.commutator_subset_ker F.normalizerMonoidHom
        rwa [Subgroup.normalizerMonoidHom_ker,
          Subgroup.normalizer_eq_top,
          ← Subgroup.map_subtype_le_map_subtype,
          Subgroup.map_subtype_commutator,
          Subgroup.map_subgroupOf_eq_of_le le_top] at h
      have hDerF : _root_.commutator M ≤ F :=
        hDerCent.trans (centralizer_fittingCore_le (G := M))
      have hDerivedFit : derivedWithin M ≤ fittingWithin M := by
        simpa only [derivedWithin, fittingWithin, F] using
          Subgroup.map_mono hDerF
      have hDerivedCyclic : IsCyclic (derivedWithin M) :=
        isCyclic_of_le_15 hDerivedFit hfitCyclic
      letI : IsCyclic (derivedWithin M) := hDerivedCyclic
      letI : IsMulCommutative (derivedWithin M) := by infer_instance
      have hSecondBot : secondDerivedWithin M = ⊥ := by
        rw [secondDerivedWithin, derivedWithin,
          _root_.commutator_eq_bot, Subgroup.map_bot]
      have hKsbot : Ks = ⊥ := by
        apply le_bot_iff.mp
        exact hKsSecond.trans_eq hSecondBot
      exact hKsne hKsbot
    exact
      { partner_ne_bot := hKsne
        partner_cyclic := hKscyclic
        partner_le_secondDerived := hKsSecond
        partner_le_Fcore := hKsF
        Fcore_not_cyclic := hnotcyclic }

  let q := Nat.card Ks
  obtain ⟨D, hDsigma, hHallD⟩ :=
    MathlibSupport.exists_ambient_isHall_of_isSolvable
      (isSolvable_of_le_15 (mmax_sol hM) (sigmaCore_le M))
      ({q} : Set ℕ)ᶜ
  have hf := (Fcore_structure hM).nonnilpotent
    hKM hHallK heq hDsigma (by simpa [q, Ks] using hHallD)
  letI : Fact q.Prime := ⟨by
    simpa [q, Ks] using hf.card_partner_prime⟩
  let Q := pCoreWithin q M
  have hQF : Q ≤ Fitting_core M := by
    dsimp only [Q, pCoreWithin]
    rw [← p_core_Fcore M hf.partner_prime_in_Fcore]
    exact Subgroup.map_subtype_le _
  have hQsyl : IsSylowSubgroupOf q Q M := by
    simpa [q, Ks, Q] using hf.pcore_sylow
  obtain ⟨P, hQP⟩ := hQsyl
  have hPcoreEq : pCore q M = (P : Subgroup M) := by
    have h := congrArg
      (fun L : Subgroup G => L.comap M.subtype) hQP
    simpa [Q, pCoreWithin,
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective] using h
  letI : (P : Subgroup M).Normal := by
    rw [← hPcoreEq]
    infer_instance
  have hKsM : Ks ≤ M :=
    (centralizerWithin_le_left (sigmaCore M) K).trans (sigmaCore_le M)
  let KsM : Subgroup M := Ks.subgroupOf M
  have hKsq : IsPGroup q Ks := by
    apply IsPGroup.of_card (n := 1)
    simp [q]
  have hKsMq : IsPGroup q KsM :=
    hKsq.of_equiv (Subgroup.subgroupOfEquivOfLe hKsM).symm
  obtain ⟨S, hKsMS⟩ := hKsMq.exists_le_sylow
  have hPS : (P : Subgroup M) ≤ S :=
    P.isPGroup'.le_sylow_of_normal S
  have hSP : (S : Subgroup M) = P :=
    P.is_maximal' S.isPGroup' hPS
  have hKsMP : KsM ≤ P := hKsMS.trans_eq hSP
  have hKsQ : Ks ≤ Q := by
    rw [hQP]
    calc
      Ks = KsM.map M.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hKsM).symm
      _ ≤ (P : Subgroup M).map M.subtype :=
        Subgroup.map_mono hKsMP
  have hKsF : Ks ≤ Fitting_core M := hKsQ.trans hQF
  have hnotcyclic : ¬ IsCyclic (Fitting_core M) := by
    intro hFcyclic
    have hQcyclic : IsCyclic Q := isCyclic_of_le_15 hQF hFcyclic
    have hPmapCyclic :
        IsCyclic ((P : Subgroup M).map M.subtype) := by
      rw [← hQP]
      exact hQcyclic
    let eP : P ≃* ((P : Subgroup M).map M.subtype) :=
      (P : Subgroup M).equivMapOfInjective
        M.subtype M.subtype_injective
    have hPcyclic : IsCyclic P := eP.isCyclic.mpr hPmapCyclic
    have hPnarrow :
        Submission.OddOrder.BG.Section05.IsNarrow q
          (⊤ : Subgroup P) := by
      intro hRank3
      obtain ⟨E, hEtop, hErank⟩ := hRank3
      have hTopCyclic : IsCyclic (⊤ : Subgroup P) :=
        Subgroup.topEquiv.isCyclic.mpr hPcyclic
      letI : IsCyclic (⊤ : Subgroup P) := hTopCyclic
      have hEcyclic : IsCyclic E := Subgroup.isCyclic_of_le hEtop
      letI : IsCyclic E := hEcyclic
      letI := Fintype.ofFinite E
      have hle : Nat.card E ≤ q := by
        rw [Nat.card_eq_fintype_card]
        simpa only [hErank.pow_eq_one, Finset.filter_true,
          Finset.card_univ] using
          (IsCyclic.card_pow_eq_one_le
            (α := E) (Fact.out : q.Prime).pos)
      have hlt : q < q ^ 3 := by
        simpa using Nat.pow_lt_pow_right
          (Fact.out : q.Prime).one_lt (by omega : 1 < 3)
      exact ((not_lt_of_ge (hErank.card_eq ▸ hle)) hlt).elim
    exact hf.partner_prime_beta.2 P hPnarrow
  exact
    { partner_ne_bot := hKsne
      partner_cyclic := hKscyclic
      partner_le_secondDerived := hKsSecond
      partner_le_Fcore := hKsF
      Fcore_not_cyclic := hnotcyclic }

end

end Submission.OddOrder.BG.Section15
