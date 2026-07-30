import Submission.OddOrder.BG.Section12.ComplementDecomposition
import Submission.OddOrder.BG.Section10.SigmaComplementRank
import Submission.OddOrder.MathlibSupport.SylowConjugateEmbedding

/-!
# Bender--Glauberman Section 12: elements of rank two in a sigma complement

This file ports the rank-two elementary-abelian and derived-subgroup facts
from `BGsection12.v`, lines 199--242.  As elsewhere in the Lean port,
membership in MathComp's sets of elementary-abelian subgroups is expressed
by an inclusion together with `IsElementaryAbelianOfRank`.
-/

namespace Submission.OddOrder.BG.Section12

open Submission.OddOrder.BG.Section04
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section10
open Submission.OddOrder.MathlibSupport

noncomputable section

universe u

/-- `BGsection12.v: ex_tau2Elem`.

Every prime in `tau2(M)` has a rank-two elementary-abelian subgroup in a
fixed sigma complement.  The proof transports a Sylow subgroup of the
complement to a Sylow subgroup of `M`, then uses Sylow conjugacy to move a
rank-two witness into it. -/
theorem ex_tau2Elem
    {G : Type u} [Group G] [Finite G]
    {M E : Subgroup G}
    (hEM : E ≤ M)
    (hHall : IsHall (sigmaPrimes M)ᶜ (E.subgroupOf M))
    {p : ℕ} (hpTau : p ∈ tau2Primes M) :
    ∃ A : Subgroup G, A ≤ E ∧ A ≤ M ∧
      IsElementaryAbelianOfRank p 2 A := by
  classical
  rcases hpTau with
    ⟨hpPrime, hpNotSigma, hRankTwo, _hNoRankThree⟩
  letI : Fact p.Prime := ⟨hpPrime⟩
  let EM : Subgroup M := E.subgroupOf M
  let P : Sylow p EM := Sylow.nonempty.some
  let S : Subgroup M := (P : Subgroup EM).map EM.subtype
  have hSp : IsPGroup p S := by
    dsimp [S]
    exact P.isPGroup'.map EM.subtype
  have hpEMindex : ¬ p ∣ EM.index := by
    intro hpIndex
    have hpSigma : p ∈ sigmaPrimes M := by
      simpa only [compl_compl] using
        hHall.isPiNumber_index hpPrime hpIndex
    exact hpNotSigma hpSigma
  have hpSindex : ¬ p ∣ S.index := by
    dsimp [S]
    rw [Subgroup.index_map_subtype]
    exact hpPrime.not_dvd_mul P.not_dvd_index hpEMindex
  let Q : Sylow p M := hSp.toSylow hpSindex
  have hQEM : (Q : Subgroup M) ≤ EM := by
    change S ≤ EM
    dsimp [S]
    exact Subgroup.map_subtype_le (P : Subgroup EM)
  have hQambientE : (Q : Subgroup M).map M.subtype ≤ E := by
    calc
      (Q : Subgroup M).map M.subtype ≤ EM.map M.subtype :=
        Subgroup.map_mono hQEM
      _ = E := Subgroup.map_subgroupOf_eq_of_le hEM
  obtain ⟨B, hBM, hB⟩ := hRankTwo
  obtain ⟨m, hm⟩ :=
    exists_conjugate_le_sylow_map Q hBM hB.isPGroup
  let A : Subgroup G :=
    B.map (MulAut.conj (m : G)).toMonoidHom
  have hAQ : A ≤ (Q : Subgroup M).map M.subtype := by
    rintro a ⟨b, hb, rfl⟩
    exact hm b hb
  have hAE : A ≤ E := hAQ.trans hQambientE
  have hA : IsElementaryAbelianOfRank p 2 A := by
    dsimp [A]
    exact hB.map_of_injective
      (MulAut.conj (m : G)).toMonoidHom
      (MulAut.conj (m : G)).injective
  exact ⟨A, hAE, hAE.trans hEM, hA⟩

/-- `BGsection12.v: sigma'2Elem_tau2`.

A rank-two elementary-abelian subgroup of a sigma complement has its prime
in `tau2(M)`. -/
theorem sigmaPrime2Elem_tau2
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M E : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hEM : E ≤ M)
    (hHall : IsHall (sigmaPrimes M)ᶜ (E.subgroupOf M))
    {p : ℕ} [Fact p.Prime] {A : Subgroup G}
    (hAE : A ≤ E)
    (hA : IsElementaryAbelianOfRank p 2 A) :
    p ∈ tau2Primes M := by
  have hpA : p ∣ Nat.card A := by
    rw [hA.card_eq]
    exact dvd_pow_self p (by omega)
  have hpE : p ∣ Nat.card E :=
    hpA.trans (Subgroup.card_dvd_of_le hAE)
  have hpEM : p ∣ Nat.card (E.subgroupOf M) := by
    rwa [natCard_subgroupOf_eq hEM]
  have hpNotSigma : p ∉ sigmaPrimes M :=
    hHall.isPiNumber_card Fact.out hpEM
  have hRankTwo : HasElementaryAbelianRankAtLeast p 2 M :=
    ⟨A, hAE.trans hEM, hA⟩
  have hNoRankThree :
      ¬ HasElementaryAbelianRankAtLeast p 3 M := by
    intro hRankThree
    exact hpNotSigma
      (alpha_sub_sigma hM ⟨Fact.out, hRankThree⟩)
  exact ⟨Fact.out, hpNotSigma, hRankTwo, hNoRankThree⟩

/-- Source-name alias for `sigmaPrime2Elem_tau2`. -/
theorem sigma'2Elem_tau2
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M E : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hEM : E ≤ M)
    (hHall : IsHall (sigmaPrimes M)ᶜ (E.subgroupOf M))
    {p : ℕ} [Fact p.Prime] {A : Subgroup G}
    (hAE : A ≤ E)
    (hA : IsElementaryAbelianOfRank p 2 A) :
    p ∈ tau2Primes M :=
  sigmaPrime2Elem_tau2 hM hEM hHall hAE hA

/-- `BGsection12.v: der1_sigma_compl_nil`.

The derived subgroup of a sigma complement is nilpotent.  Its image in the
derived subgroup of `M / M_alpha` is injective because the complement is
disjoint from `M_sigma`, hence from `M_alpha`. -/
theorem der1_sigma_compl_nil
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M E : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hEM : E ≤ M)
    (hHall : IsHall (sigmaPrimes M)ᶜ (E.subgroupOf M)) :
    Group.IsNilpotent (_root_.commutator E) := by
  classical
  let A : Subgroup M := (alphaCore M).subgroupOf M
  have hAnormal : A.Normal := by
    simpa [A] using alphaCore_normal M
  letI : A.Normal := hAnormal
  let Q := M ⧸ A
  let q : M →* Q := QuotientGroup.mk' A
  let j : E →* M := Subgroup.inclusion hEM
  let f : E →* Q := q.comp j
  have hdis : Disjoint (sigmaCore M) E :=
    Subgroup.disjoint_of_coprime_natCard
      (coprime_sigma_compl hEM hHall)
  have hfinj : Function.Injective f := by
    rw [← f.ker_eq_bot_iff]
    apply le_antisymm ?_ bot_le
    intro x hx
    have hfx : f x = 1 := f.mem_ker.mp hx
    change q (j x) = 1 at hfx
    have hxA : j x ∈ A :=
      (QuotientGroup.eq_one_iff (j x)).mp hfx
    have hxAlphaJ : ((j x : M) : G) ∈ alphaCore M := hxA
    have hxAlpha : (x : G) ∈ alphaCore M := by
      simpa only [j, Subgroup.coe_inclusion] using hxAlphaJ
    have hxSigma : (x : G) ∈ sigmaCore M :=
      alphaCore_le_sigmaCore hM hxAlpha
    have hxBot : (x : G) ∈ (⊥ : Subgroup G) := by
      rw [← disjoint_iff.mp hdis]
      exact ⟨hxSigma, x.property⟩
    apply Subgroup.mem_bot.mpr
    apply Subtype.ext
    exact Subgroup.mem_bot.mp hxBot
  let D : Subgroup E := _root_.commutator E
  let R : Subgroup Q := D.map f
  have hRcomm : R ≤ _root_.commutator Q := by
    dsimp only [R, D]
    rw [map_commutator_eq]
    exact Subgroup.commutator_mono le_top le_top
  letI : Group.IsNilpotent (_root_.commutator Q) := by
    simpa [Q, A] using Malpha_quo_nil hM
  letI : Group.IsNilpotent
      (R.subgroupOf (_root_.commutator Q)) := inferInstance
  let eR : R.subgroupOf (_root_.commutator Q) ≃* R :=
    Subgroup.subgroupOfEquivOfLe hRcomm
  letI : Group.IsNilpotent R :=
    Group.nilpotent_of_mulEquiv eR
  let eD : D ≃* R := D.equivMapOfInjective f hfinj
  have hDnil : Group.IsNilpotent D :=
    Group.nilpotent_of_mulEquiv eD.symm
  simpa [D] using hDnil

/-- `BGsection12.v: tau2_not_beta`.

A `tau2(M)` prime is outside `beta(G)`, and every rank-two
elementary-abelian `p`-subgroup of `M` is maximal among the elementary
abelian `p`-subgroups of `G`. -/
theorem tau2_not_beta
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    {p : ℕ} (hpTau : p ∈ tau2Primes M) :
    p ∉ betaPrimes (⊤ : Subgroup G) ∧
      ∀ {A : Subgroup G}, A ≤ M →
        IsElementaryAbelianOfRank p 2 A →
        IsPMaxElem p (⊤ : Subgroup G) A := by
  rcases hpTau with
    ⟨hpPrime, hpNotSigma, hRankTwo, hNoRankThree⟩
  letI : Fact p.Prime := ⟨hpPrime⟩
  have hRank : HasElementaryAbelianPRankTwo p M :=
    ⟨hRankTwo, hNoRankThree⟩
  refine ⟨sigma'_rank2_beta' hM hpNotSigma hRank, ?_⟩
  intro A hAM hA
  exact sigma'_rank2_max hM hpNotSigma hRank hAM hA

end

end Submission.OddOrder.BG.Section12
