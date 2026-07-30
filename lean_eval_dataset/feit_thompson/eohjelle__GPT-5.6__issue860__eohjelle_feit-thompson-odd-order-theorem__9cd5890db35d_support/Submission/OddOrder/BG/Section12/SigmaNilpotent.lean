import Submission.OddOrder.BG.Section12.AbelianTau2

/-!
# Bender--Glauberman Section 12: abelian sigma-complement consequences

This file ports `BGsection12.v`, lines 1316--1462.  The first result is the
nilpotent `sigma(M)'`-subgroup criterion.  It is followed by the derived- and
`tau2`-complement consequences, the `tau1` quotient attached to a rank-two
subgroup, the normalizer theorem for noncyclic sigma subgroups, and the
unique-maximal-overgroup result for a nonregular `tau2` element.

The order of `E / C_E(A)` in Corollary 12.10(c) is represented by the index
of `C_E(A)` in `E`.  This keeps the conclusion independent of a local
typeclass installation for the normal subgroup used to form the quotient.
-/

namespace Submission.OddOrder.BG.Section12

open Submission.OddOrder.BG.Section04
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section10
open Submission.OddOrder.MathlibSupport
open scoped IsMulCommutative Pointwise

noncomputable section

universe u v

/-! ### Small transport and Hall-subgroup adapters -/

/-- Commutativity descends to a subgroup. -/
private theorem isMulCommutative_of_le_12_10
    {K : Type u} [Group K] {A B : Subgroup K}
    (hAB : A ≤ B) (hB : IsMulCommutative B) :
    IsMulCommutative A := by
  apply isMulCommutative_iff.mpr
  intro x y
  apply Subtype.ext
  exact congrArg (fun z : B ↦ (z : K))
    (isMulCommutative_iff.mp hB
      ⟨(x : K), hAB x.property⟩ ⟨(y : K), hAB y.property⟩)

/-- Commutativity transports across a multiplicative equivalence. -/
private theorem isMulCommutative_of_mulEquiv_12_10
    {A : Type u} {B : Type v} [Group A] [Group B]
    (e : A ≃* B) (hA : IsMulCommutative A) :
    IsMulCommutative B := by
  apply isMulCommutative_iff.mpr
  intro x y
  apply e.symm.injective
  simpa only [map_mul] using
    (isMulCommutative_iff.mp hA (e.symm x) (e.symm y))

/-- A `pi`-subgroup of a finite group lies in a normal `pi`-Hall subgroup. -/
private theorem le_normal_isHall_of_isPiNumber_12_10
    {K : Type u} [Group K] [Finite K]
    {pi : Set ℕ} {H L : Subgroup K}
    (hHnormal : H.Normal) (hHHall : IsHall pi H)
    (hLpi : IsPiNumber pi (Nat.card L)) :
    L ≤ H := by
  letI : H.Normal := hHnormal
  have hcop : (Nat.card L).Coprime H.index := by
    apply Nat.coprime_of_dvd
    intro p hp hpL hpIndex
    exact hHHall.isPiNumber_index hp hpIndex (hLpi hp hpL)
  intro x hxL
  let q : K →* K ⧸ H := QuotientGroup.mk' H
  have horderL : orderOf (q x) ∣ Nat.card L :=
    (orderOf_map_dvd q x).trans (L.orderOf_dvd_natCard hxL)
  have horderIndex : orderOf (q x) ∣ H.index := by
    simpa only [H.index_eq_card] using orderOf_dvd_natCard (q x)
  have horderOne : orderOf (q x) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop horderL horderIndex
  exact (QuotientGroup.eq_one_iff x).mp
    (by simpa [q] using orderOf_eq_one_iff.mp horderOne)

/-- A Sylow subgroup of a Hall subgroup is Sylow in the ambient group. -/
private theorem exists_sylow_eq_map_of_sylow_hall_12_10
    {K : Type u} [Group K] [Finite K]
    {pi : Set ℕ} {p : ℕ} (hp : p.Prime)
    {A : Subgroup K} (hA : IsHall pi A) (hpPi : p ∈ pi)
    (P : Sylow p A) :
    ∃ Q : Sylow p K,
      (Q : Subgroup K) = (P : Subgroup A).map A.subtype := by
  letI : Fact p.Prime := ⟨hp⟩
  let S : Subgroup K := (P : Subgroup A).map A.subtype
  have hSp : IsPGroup p S := P.isPGroup'.map A.subtype
  have hpAindex : ¬ p ∣ A.index := by
    intro hpIndex
    exact hA.isPiNumber_index hp hpIndex hpPi
  have hpSindex : ¬ p ∣ S.index := by
    dsimp only [S]
    rw [Subgroup.index_map_subtype]
    exact hp.not_dvd_mul P.not_dvd_index hpAindex
  exact ⟨hSp.toSylow hpSindex, rfl⟩

/-- Transport a Sylow subgroup through a Hall inclusion while retaining its
ambient carrier. -/
private theorem exists_ambient_sylow_eq_of_sylow_hall_12_10
    {G : Type u} [Group G] [Finite G]
    {K H : Subgroup G} {pi : Set ℕ} {p : ℕ}
    (hp : p.Prime) (hKH : K ≤ H)
    (hKHall : IsHall pi (K.subgroupOf H))
    (hpPi : p ∈ pi) (P : Sylow p K) :
    ∃ Q : Sylow p H,
      (Q : Subgroup H).map H.subtype =
        (P : Subgroup K).map K.subtype := by
  letI : Fact p.Prime := ⟨hp⟩
  let e : K.subgroupOf H ≃* K :=
    Subgroup.subgroupOfEquivOfLe hKH
  let P' : Sylow p (K.subgroupOf H) :=
    P.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  obtain ⟨Q, hQ⟩ :=
    exists_sylow_eq_map_of_sylow_hall_12_10 hp hKHall hpPi P'
  refine ⟨Q, ?_⟩
  rw [hQ, Subgroup.map_map]
  simp only [P', Sylow.coe_mapSurjective, Subgroup.map_map]
  apply congrArg (fun f : K →* G ↦ (P : Subgroup K).map f)
  ext x
  rfl

/-- The intrinsic centralizer in `E` is the subgroup-of copy of the ambient
centralizer-within subgroup. -/
private theorem subgroupOf_centralizerWithin_eq
    {G : Type u} [Group G] {E A : Subgroup G} (hAE : A ≤ E) :
    (centralizerWithin E A).subgroupOf E =
      Subgroup.centralizer (A.subgroupOf E : Set E) := by
  ext x
  constructor
  · intro hx
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    apply Subtype.ext
    exact (mem_centralizerWithin.mp hx).2 (a : G) ha
  · intro hx
    refine ⟨x.property, ?_⟩
    intro a ha
    let aE : E := ⟨a, hAE ha⟩
    exact congrArg Subtype.val
      (Subgroup.mem_centralizer_iff.mp hx aE ha)

/-! ### Corollary 12.10(a) -/

/-- `BGsection12.v: sigma'_nil_abelian`, Corollary 12.10(a).

A nilpotent subgroup of a maximal subgroup whose prime divisors all lie
outside `sigma(M)` is commutative. -/
theorem sigma'_nil_abelian
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M N : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hNM : N ≤ M)
    (hNcompl : IsPiNumber (sigmaPrimes M)ᶜ (Nat.card N))
    (hNnil : Group.IsNilpotent N) :
    IsMulCommutative N := by
  classical
  letI : Group.IsNilpotent N := hNnil
  obtain ⟨e⟩ :=
    (Group.isNilpotent_of_finite_tfae.out 0 4 rfl rfl).mp hNnil
  let ps := (Nat.card N).primeFactors
  have hSylowComm :
      ∀ (p : ps) (P : Sylow (p : ℕ) N),
        IsMulCommutative (P : Subgroup N) := by
    intro p P
    have hp : (p : ℕ).Prime := Nat.prime_of_mem_primeFactors p.property
    letI : Fact (p : ℕ).Prime := ⟨hp⟩
    have hpN : (p : ℕ) ∣ Nat.card N :=
      Nat.dvd_of_mem_primeFactors p.property
    have hpCompl : (p : ℕ) ∈ (sigmaPrimes M)ᶜ :=
      hNcompl hp hpN
    have hNoRankThree :
        ¬ HasElementaryAbelianRankAtLeast (p : ℕ) 3 M := by
      intro hRankThree
      exact hpCompl (alpha_sub_sigma hM ⟨hp, hRankThree⟩)
    let PN : Subgroup G := (P : Subgroup N).map N.subtype
    have hPNN : PN ≤ N := Subgroup.map_subtype_le (P : Subgroup N)
    have hPNM : PN ≤ M := hPNN.trans hNM
    have hPNp : IsPGroup (p : ℕ) PN := P.isPGroup'.map N.subtype
    by_cases hRankTwo :
        HasElementaryAbelianRankAtLeast (p : ℕ) 2 M
    · obtain ⟨A, hAM, hA⟩ := hRankTwo
      have hpTau : (p : ℕ) ∈ tau2Primes M :=
        ⟨hp, hpCompl, ⟨A, hAM, hA⟩, hNoRankThree⟩
      let PNM : Subgroup M := PN.subgroupOf M
      let ePNM : PNM ≃* PN := Subgroup.subgroupOfEquivOfLe hPNM
      have hPNMp : IsPGroup (p : ℕ) PNM :=
        hPNp.of_equiv ePNM.symm
      obtain ⟨Q, hPNMQ⟩ := hPNMp.exists_le_sylow
      have hPNQ : PN ≤ ambientSylow M Q := by
        rw [← Subgroup.map_subgroupOf_eq_of_le hPNM]
        exact Subgroup.map_mono hPNMQ
      have hQcomm : IsMulCommutative (ambientSylow M Q) :=
        (tau2_context hM hpTau hAM hA).sylow_abelian Q
      have hPNcomm : IsMulCommutative PN :=
        isMulCommutative_of_le_12_10 hPNQ hQcomm
      let eP : (P : Subgroup N) ≃* PN :=
        (P : Subgroup N).equivMapOfInjective N.subtype
          N.subtype_injective
      exact isMulCommutative_of_mulEquiv_12_10 eP.symm hPNcomm
    · have hNoRankTwoP :
          ¬ ∃ A : Subgroup (P : Subgroup N),
            IsElementaryAbelianOfRank (p : ℕ) 2 A := by
        rintro ⟨A, hA⟩
        let f : (P : Subgroup N) →* G :=
          N.subtype.comp (P : Subgroup N).subtype
        let AG : Subgroup G := A.map f
        have hAGM : AG ≤ M := by
          rintro _ ⟨a, ha, rfl⟩
          exact hNM (((a : (P : Subgroup N)) : N).property)
        have hf : Function.Injective f :=
          N.subtype_injective.comp
            (P : Subgroup N).subtype_injective
        exact hRankTwo ⟨AG, hAGM,
          hA.map_of_injective f hf⟩
      have hcardPN : Nat.card PN = Nat.card (P : Subgroup N) := by
        dsimp only [PN]
        rw [Subgroup.card_map_of_injective N.subtype_injective]
      have hoddP : Odd (Nat.card (P : Subgroup N)) := by
        rw [← hcardPN]
        exact mFT_odd PN
      have hPcyclic : IsCyclic (P : Subgroup N) :=
        (odd_pgroup_isCyclic_iff_no_elementaryAbelian_rank_two
          P.isPGroup' hoddP).mpr hNoRankTwoP
      exact hPcyclic.isMulCommutative
  letI : ∀ (p : ps) (P : Sylow (p : ℕ) N),
      IsMulCommutative (P : Subgroup N) := hSylowComm
  have hprodComm :
      IsMulCommutative
        (∀ p : ps, ∀ P : Sylow (p : ℕ) N,
          (P : Subgroup N)) := inferInstance
  exact isMulCommutative_of_mulEquiv_12_10 e hprodComm

/-- Descriptive alias for the source-named Corollary 12.10(a). -/
theorem sigmaPrime_complement_nil_abelian
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M N : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hNM : N ≤ M)
    (hNcompl : IsPiNumber (sigmaPrimes M)ᶜ (Nat.card N))
    (hNnil : Group.IsNilpotent N) :
    IsMulCommutative N :=
  sigma'_nil_abelian hM hNM hNcompl hNnil

/-! ### Corollary 12.10(b) -/

/-- `BGsection12.v: der_mmax_compl_abelian`, the first assertion of
Corollary 12.10(b). -/
theorem der_mmax_compl_abelian
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M E : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hEM : E ≤ M)
    (hHallE : IsHall (sigmaPrimes M)ᶜ (E.subgroupOf M)) :
    IsMulCommutative (_root_.commutator E) := by
  let D : Subgroup G := (_root_.commutator E).map E.subtype
  have hDE : D ≤ E := Subgroup.map_subtype_le (_root_.commutator E)
  have hDM : D ≤ M := hDE.trans hEM
  have hDcompl : IsPiNumber (sigmaPrimes M)ᶜ (Nat.card D) := by
    have hderDvd : Nat.card (_root_.commutator E) ∣ Nat.card E :=
      (_root_.commutator E).card_subgroup_dvd_card
    have hEcompl : IsPiNumber (sigmaPrimes M)ᶜ (Nat.card E) := by
      rw [← natCard_subgroupOf_eq hEM]
      exact hHallE.isPiNumber_card
    dsimp only [D]
    rw [Subgroup.card_map_of_injective E.subtype_injective]
    exact hEcompl.of_dvd hderDvd
  let eD : (_root_.commutator E) ≃* D :=
    (_root_.commutator E).equivMapOfInjective E.subtype
      E.subtype_injective
  have hDnil : Group.IsNilpotent D := by
    letI : Group.IsNilpotent (_root_.commutator E) :=
      der1_sigma_compl_nil hM hEM hHallE
    exact Group.nilpotent_of_mulEquiv eD
  have hDcomm : IsMulCommutative D :=
    sigma'_nil_abelian hM hDM hDcompl hDnil
  exact isMulCommutative_of_mulEquiv_12_10 eD.symm hDcomm

/-- `BGsection12.v: tau2_compl_abelian`, the second assertion of
Corollary 12.10(b).  No compatibility with a fixed complement decomposition
is assumed for `E₂`. -/
theorem tau2_compl_abelian
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M E E₂ : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hEM : E ≤ M)
    (hHallE : IsHall (sigmaPrimes M)ᶜ (E.subgroupOf M))
    (hE₂E : E₂ ≤ E)
    (hHallE₂ : IsHall (tau2Primes M) (E₂.subgroupOf E)) :
    IsMulCommutative E₂ := by
  classical
  obtain ⟨⟨E₁, hE₁E, hHallE₁⟩,
      ⟨E₃, hE₃E, hHallE₃⟩⟩ := ex_tau13_compl hEM hHallE
  obtain ⟨F₂, hF₂E, hHallF₂, hCompl⟩ :=
    ex_tau2_compl hEM hHallE hE₁E hHallE₁ hE₃E hHallE₃
  by_cases hF₂bot : F₂ = ⊥
  · have hF₂normal : (F₂.subgroupOf E).Normal := by
      simpa [hF₂bot] using
        (inferInstance : (⊥ : Subgroup E).Normal)
    have hE₂F₂sub : E₂.subgroupOf E ≤ F₂.subgroupOf E :=
      le_normal_isHall_of_isPiNumber_12_10
        hF₂normal hCompl.hall_E₂ hHallE₂.isPiNumber_card
    have hE₂F₂ : E₂ ≤ F₂ := by
      intro x hx
      have hxF₂ : (⟨x, hE₂E hx⟩ : E) ∈ F₂.subgroupOf E :=
        hE₂F₂sub hx
      exact hxF₂
    have hE₂bot : E₂ = ⊥ := by
      apply le_antisymm
      · simpa [hF₂bot] using hE₂F₂
      · exact bot_le
    rw [hE₂bot]
    infer_instance
  · have hcardF₂ : 1 < Nat.card F₂ :=
      F₂.one_lt_card_iff_ne_bot.mpr hF₂bot
    obtain ⟨p, hp, hpF₂⟩ := Nat.exists_prime_and_dvd
      (by omega : Nat.card F₂ ≠ 1)
    letI : Fact p.Prime := ⟨hp⟩
    have hpF₂sub : p ∣ Nat.card (F₂.subgroupOf E) := by
      rwa [natCard_subgroupOf_eq hF₂E]
    have hpTau : p ∈ tau2Primes M :=
      hHallF₂.isPiNumber_card hp hpF₂sub
    obtain ⟨A, hAE, -, hA⟩ := ex_tau2Elem hEM hHallE hpTau
    obtain ⟨S, hAS⟩ := hA.isPGroup.exists_le_sylow
    by_cases hScomm : IsMulCommutative (S : Subgroup G)
    · have hConclusion :=
        abelian_tau2 S hM hCompl hpTau hAE hA hAS hScomm
      have hF₂normal : (F₂.subgroupOf E).Normal :=
        hConclusion.E₂_normal
      have hE₂F₂sub : E₂.subgroupOf E ≤ F₂.subgroupOf E :=
        le_normal_isHall_of_isPiNumber_12_10
          hF₂normal hCompl.hall_E₂ hHallE₂.isPiNumber_card
      have hE₂F₂ : E₂ ≤ F₂ := by
        intro x hx
        have hxF₂ : (⟨x, hE₂E hx⟩ : E) ∈ F₂.subgroupOf E :=
          hE₂F₂sub hx
        exact hxF₂
      exact isMulCommutative_of_le_12_10 hE₂F₂
        hConclusion.E₂_abelian
    · have hNonabelian :=
        nonabelian_tau2 hM hEM hHallE hpTau hAE hA
          S.isPGroup' hScomm
      have hE₂pi : IsPiNumber (tau2Primes M) (Nat.card E₂) := by
        rw [← natCard_subgroupOf_eq hE₂E]
        exact hHallE₂.isPiNumber_card
      have hE₂p : IsPGroup p E₂ := by
        apply isPGroup_of_isPiNumber_singleton
        rw [← hNonabelian.tau2_eq]
        exact hE₂pi
      have hE₂compl :
          IsPiNumber (sigmaPrimes M)ᶜ (Nat.card E₂) := by
        have hEcompl :
            IsPiNumber (sigmaPrimes M)ᶜ (Nat.card E) := by
          rw [← natCard_subgroupOf_eq hEM]
          exact hHallE.isPiNumber_card
        exact hEcompl.of_dvd (Subgroup.card_dvd_of_le hE₂E)
      exact sigma'_nil_abelian hM (hE₂E.trans hEM)
        hE₂compl hE₂p.isNilpotent

/-! ### Corollary 12.10(c) -/

/-- The three conclusions of `BGsection12.v: tau1_cent_tau2Elem_factor`.

The last field says that the order of `E / C_E(A)` is a `tau1(M)`-number,
using the index of `C_E(A)` in `E` as the quotient order. -/
structure Tau1CentralizerFactor
    {G : Type u} [Group G] [Finite G] (M E A : Subgroup G) : Prop where
  factors_centralize :
    ∀ {E₁ E₂ E₃ : Subgroup G},
      sigma_complement M E E₁ E₂ E₃ →
        E₃ ⊔ E₂ ≤ centralizerWithin E A
  centralizer_normal :
    ((centralizerWithin E A).subgroupOf E).Normal
  quotient_isPiNumber :
    IsPiNumber (tau1Primes M)
      ((centralizerWithin E A).subgroupOf E).index

/-- `BGsection12.v: tau1_cent_tau2Elem_factor`, Corollary 12.10(c). -/
theorem tau1_cent_tau2Elem_factor
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M E A : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hM : M ∈ minSimple_max_groups (G := G))
    (hEM : E ≤ M)
    (hHallE : IsHall (sigmaPrimes M)ᶜ (E.subgroupOf M))
    (hpTau : p ∈ tau2Primes M)
    (hAE : A ≤ E)
    (hA : IsElementaryAbelianOfRank p 2 A) :
    Tau1CentralizerFactor M E A := by
  classical
  let C : Subgroup G := centralizerWithin E A
  let CE : Subgroup E := C.subgroupOf E
  have hAContext := tau2_compl_context hM hEM hHallE hpTau hAE hA
  have hCnormal : CE.Normal := by
    letI : (A.subgroupOf E).Normal := hAContext.A_normal
    rw [show CE = Subgroup.centralizer (A.subgroupOf E : Set E) by
      simpa [C, CE] using subgroupOf_centralizerWithin_eq hAE]
    infer_instance
  have hFactors :
      ∀ {E₁ E₂ E₃ : Subgroup G},
        sigma_complement M E E₁ E₂ E₃ →
          E₃ ⊔ E₂ ≤ C := by
    intro E₁ E₂ E₃ hCompl
    have hRegular := tau2_regular hM hCompl hpTau hAE hA
    have hE₂comm := tau2_compl_abelian hM hEM hHallE
      hCompl.E₂_le_E hCompl.hall_E₂
    have hE₂C : E₂ ≤ C := by
      intro x hx
      refine ⟨hCompl.E₂_le_E hx, ?_⟩
      intro a ha
      exact congrArg Subtype.val
        (isMulCommutative_iff.mp hE₂comm
          ⟨a, hRegular.A_le_E₂ ha⟩ ⟨x, hx⟩)
    have hE₃C : E₃ ≤ C := by
      let E₃E : Subgroup E := E₃.subgroupOf E
      let AE : Subgroup E := A.subgroupOf E
      have hE₃pi : IsPiNumber (tau3Primes M) (Nat.card E₃E) :=
        hCompl.hall_E₃.isPiNumber_card
      have hApi : IsPiNumber (tau3Primes M)ᶜ (Nat.card AE) := by
        rw [natCard_subgroupOf_eq hAE]
        exact hA.isPGroup.isPiNumber_natCard (tau3'2 M hpTau)
      have hcop : Nat.Coprime (Nat.card E₃E) (Nat.card AE) :=
        hE₃pi.coprime_compl hApi
      have hdis : Disjoint E₃E AE :=
        Subgroup.disjoint_of_coprime_natCard hcop
      have hcomm := Subgroup.commute_of_normal_of_disjoint
        E₃E AE
        (by simpa [E₃E] using
          (sigma_compl_context hM hCompl).E₃_normal)
        (by simpa [AE] using hAContext.A_normal) hdis
      intro x hx
      refine ⟨hCompl.E₃_le_E hx, ?_⟩
      intro a ha
      let xE : E := ⟨x, hCompl.E₃_le_E hx⟩
      let aE : E := ⟨a, hAE ha⟩
      exact congrArg Subtype.val
        (hcomm xE aE hx ha).eq.symm
    exact sup_le hE₃C hE₂C
  obtain ⟨⟨E₁, hE₁E, hHallE₁⟩,
      ⟨E₃, hE₃E, hHallE₃⟩⟩ := ex_tau13_compl hEM hHallE
  obtain ⟨E₂, hE₂E, hHallE₂, hCompl⟩ :=
    ex_tau2_compl hEM hHallE hE₁E hHallE₁ hE₃E hHallE₃
  let K : Subgroup G := E₃ ⊔ E₂
  have hKC : K ≤ C := hFactors hCompl
  have hKECE : K.subgroupOf E ≤ CE := by
    intro x hx
    exact hKC hx
  have hcomp :
      (K.subgroupOf E).IsComplement' (E₁.subgroupOf E) := by
    simpa [K] using
      (sigma_compl_context hM hCompl).E₃₂_E₁_sdprod.2.2.2
  have hindexDvd : CE.index ∣ (K.subgroupOf E).index :=
    Subgroup.index_dvd_of_le hKECE
  have hquotPi : IsPiNumber (tau1Primes M) CE.index := by
    apply hHallE₁.isPiNumber_card.of_dvd
    calc
      CE.index ∣ (K.subgroupOf E).index := hindexDvd
      _ = Nat.card (E₁.subgroupOf E) := hcomp.symm.index_eq_card
  exact
    { factors_centralize := by
        intro E₁ E₂ E₃ hComplement
        simpa [C] using hFactors hComplement
      centralizer_normal := by simpa [CE, C] using hCnormal
      quotient_isPiNumber := by simpa [CE, C] using hquotPi }

/-! ### Corollary 12.10(d) -/

/-- `BGsection12.v: norm_noncyclic_sigma`, Corollary 12.10(d). -/
theorem norm_noncyclic_sigma
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M P : Subgroup G} {p : ℕ}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hpSigma : p ∈ sigmaPrimes M)
    (hPp : IsPGroup p P)
    (hPM : P ≤ M)
    (hPnoncyclic : ¬ IsCyclic P) :
    Subgroup.normalizer (P : Set G) ≤ M := by
  classical
  letI : Fact p.Prime := ⟨hpSigma.1⟩
  have hRankTwoP :
      ∃ A₀ : Subgroup P,
        IsElementaryAbelianOfRank p 2 A₀ := by
    by_contra hno
    exact hPnoncyclic
      ((odd_pgroup_isCyclic_iff_no_elementaryAbelian_rank_two
        hPp (mFT_odd P)).mpr hno)
  obtain ⟨A₀, hA₀⟩ := hRankTwoP
  let A : Subgroup G := A₀.map P.subtype
  have hAP : A ≤ P := Subgroup.map_subtype_le A₀
  have hA : IsElementaryAbelianOfRank p 2 A :=
    hA₀.map_of_injective P.subtype P.subtype_injective
  have hCAM : Subgroup.centralizer (A : Set G) ≤ M :=
    (p2Elem_mmax hM (hAP.trans hPM) hA).1
  have hCPM : Subgroup.centralizer (P : Set G) ≤ M :=
    (Subgroup.centralizer_le hAP).trans hCAM
  have hproduct := (sigma_group_trans hM hpSigma hPp).2.2 hPM
  intro x hx
  have hxprod : x ∈
      (Subgroup.centralizer (P : Set G) : Set G) *
        ((M ⊓ Subgroup.normalizer (P : Set G) : Subgroup G) : Set G) := by
    rw [hproduct]
    exact hx
  rcases hxprod with ⟨c, hc, n, hn, rfl⟩
  exact M.mul_mem (hCPM hc) hn.1

/-! ### Corollary 12.10(e) -/

/-- `BGsection12.v: cent1_nreg_sigma_uniq`, Corollary 12.10(e).

The source predicate saying that `x` is a `tau2(M)`-element is rendered as
the prime-support condition on `orderOf x`. -/
theorem cent1_nreg_sigma_uniq
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M : Subgroup G} {x : G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hxM : x ∈ M)
    (hxne : x ≠ 1)
    (hxTau : IsPiNumber (tau2Primes M) (orderOf x))
    (hcent :
      centralizerWithin (sigmaCore M) (Subgroup.zpowers x) ≠ ⊥) :
    minSimple_max_groups_of (G := G)
        (Subgroup.centralizer ({x} : Set G) : Set G) = {M} := by
  classical
  let X : Subgroup G := Subgroup.zpowers x
  let Cx : Subgroup G := Subgroup.centralizer ({x} : Set G)
  have hXM : X ≤ M := Subgroup.zpowers_le.mpr hxM
  have hcardX : Nat.card X = orderOf x := by
    simp [X, Nat.card_zpowers]
  have hXtau : IsPiNumber (tau2Primes M) (Nat.card X) := by
    simpa [hcardX] using hxTau
  have hXcompl : IsPiNumber (sigmaPrimes M)ᶜ (Nat.card X) :=
    hXtau.mono (fun _ hq ↦ hq.2.1)
  obtain ⟨E, hXE, hEM, hHallE⟩ :=
    exists_ambient_isHall_ge_of_isSolvable
      hXM (mmax_sol hM) (sigmaPrimes M)ᶜ hXcompl
  have hEsol : IsSolvable E := sigma_compl_sol hEM hHallE
  obtain ⟨E₂, hXE₂, hE₂E, hHallE₂⟩ :=
    exists_ambient_isHall_ge_of_isSolvable
      hXE hEsol (tau2Primes M) hXtau
  have horderNe : orderOf x ≠ 1 :=
    fun horder ↦ hxne (orderOf_eq_one_iff.mp horder)
  obtain ⟨p, hp, hpOrder⟩ := Nat.exists_prime_and_dvd horderNe
  letI : Fact p.Prime := ⟨hp⟩
  have hpTau : p ∈ tau2Primes M := hxTau hp hpOrder
  obtain ⟨B, hBE, -, hB⟩ := ex_tau2Elem hEM hHallE hpTau
  let P : Sylow p E₂ := Classical.choice Sylow.nonempty
  obtain ⟨Q, hQ⟩ :=
    exists_ambient_sylow_eq_of_sylow_hall_12_10
      hp hE₂E hHallE₂ hpTau P
  have hQE₂ : (Q : Subgroup E).map E.subtype ≤ E₂ := by
    rw [hQ]
    exact Subgroup.map_subtype_le (P : Subgroup E₂)
  obtain ⟨e, he⟩ :=
    exists_conjugate_le_sylow_map Q hBE hB.isPGroup
  let A : Subgroup G :=
    B.map (MulAut.conj (e : G)).toMonoidHom
  have hAQ : A ≤ (Q : Subgroup E).map E.subtype := by
    rintro a ⟨b, hb, rfl⟩
    exact he b hb
  have hAE₂ : A ≤ E₂ := by
    exact hAQ.trans hQE₂
  have hAE : A ≤ E := hAE₂.trans hE₂E
  have hAM : A ≤ M := hAE.trans hEM
  have hA : IsElementaryAbelianOfRank p 2 A :=
    hB.map_of_injective (MulAut.conj (e : G)).toMonoidHom
      (MulAut.conj (e : G)).injective
  have hE₂comm : IsMulCommutative E₂ :=
    tau2_compl_abelian hM hEM hHallE hE₂E hHallE₂
  have hACx : A ≤ Cx := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyx : y = x := Set.mem_singleton_iff.mp hy
    subst y
    exact congrArg Subtype.val
      (isMulCommutative_iff.mp hE₂comm
        ⟨x, hXE₂ (Subgroup.mem_zpowers x)⟩
        ⟨a, hAE₂ ha⟩)
  have hTauContext := tau2_context hM hpTau hAM hA
  have hsubset :
      minSimple_max_groups_of (G := G) (Cx : Set G) ⊆ {M} := by
    intro H hH
    rw [Set.mem_singleton_iff]
    by_contra hHM
    have hAH : A ≤ H := hACx.trans hH.2
    have hHofA :
        H ∈ minSimple_max_groups_of (G := G) (A : Set G) :=
      ⟨hH.1, hAH⟩
    have hinter : sigmaCore M ⊓ H = ⊥ :=
      hTauContext.maximal_intersection_eq_bot hHofA hHM
    have hcentLe : centralizerWithin (sigmaCore M) X ≤
        sigmaCore M ⊓ H := by
      intro z hz
      refine ⟨hz.1, hH.2 ?_⟩
      change ∀ y ∈ ({x} : Set G), y * z = z * y
      intro y hy
      have hyx : y = x := Set.mem_singleton_iff.mp hy
      subst y
      exact hz.2 x (Subgroup.mem_zpowers x)
    apply hcent
    apply le_antisymm
    · simpa [X, hinter] using hcentLe
    · exact bot_le
  apply Set.Subset.antisymm hsubset
  rw [Set.singleton_subset_iff]
  obtain ⟨H, hHmax, hCxH⟩ :=
    mmax_exists Cx (by simpa [Cx] using mFT_cent1_proper hxne)
  have hHM : H = M := Set.mem_singleton_iff.mp
    (hsubset ⟨hHmax, hCxH⟩)
  subst H
  exact ⟨hHmax, hCxH⟩

end

end Submission.OddOrder.BG.Section12
