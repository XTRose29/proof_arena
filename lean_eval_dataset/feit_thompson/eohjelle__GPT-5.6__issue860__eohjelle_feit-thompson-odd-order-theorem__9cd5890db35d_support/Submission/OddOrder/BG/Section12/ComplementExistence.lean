import Submission.OddOrder.BG.Section12.TauDefinitions
import Submission.OddOrder.BG.Section07.MaximalSubgroups
import Submission.OddOrder.MathlibSupport.MinimalNormal
import Submission.OddOrder.MathlibSupport.MinimalNormalExistence
import Submission.OddOrder.MathlibSupport.PiCore
import Submission.OddOrder.MathlibSupport.SolvableComplementConjugacy
import Submission.OddOrder.MathlibSupport.Solvability

/-!
# Bender--Glauberman Section 12: existence of sigma complements

This file ports the first three existence remarks after the `tau`-set
definitions in `BGsection12.v`.  Hall existence is proved locally for finite
solvable groups; no choice of Hall subgroup is added as an assumption.
-/

namespace Submission.OddOrder.BG.Section12

open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section10
open Submission.OddOrder.MathlibSupport

noncomputable section

universe u

/-- Hall's existence theorem for a finite solvable group. -/
theorem exists_isHall_of_isSolvable
    {K : Type u} [Group K] [Finite K]
    (hsol : IsSolvable K) (pi : Set ℕ) :
    ∃ H : Subgroup K, IsHall pi H := by
  classical
  letI : IsSolvable K := hsol
  let motive : ℕ → Prop := fun n ↦
    ∀ {L : Type u} [Group L] [Finite L] [IsSolvable L],
      Nat.card L = n → ∃ H : Subgroup L, IsHall pi H
  suffices hmain : motive (Nat.card K) from hmain rfl
  exact Nat.strong_induction_on (p := motive) (Nat.card K) fun n ih ↦ by
    intro L _ _ _ hcard
    by_cases hcardOne : Nat.card L = 1
    · refine ⟨⊤, ?_⟩
      constructor
      · simpa [hcardOne] using (IsPiNumber.one (pi := pi))
      · simp only [Subgroup.index_top]
        exact IsPiNumber.one
    have hcardGt : 1 < Nat.card L :=
      (Nat.one_le_iff_ne_zero.mpr Nat.card_pos.ne').lt_of_ne
        (Ne.symm hcardOne)
    letI : Nontrivial L := Finite.one_lt_card_iff_nontrivial.mp hcardGt
    obtain ⟨N, hNmin, -⟩ :=
      exists_minimalNormal_le (K := (⊤ : Subgroup L))
        (by infer_instance) top_ne_bot
    letI : N.Normal := hNmin.normal
    obtain ⟨r, hr, hNr⟩ := hNmin.exists_prime_isPGroup
    letI : Fact r.Prime := ⟨hr⟩
    have hquotlt : Nat.card (L ⧸ N) < Nat.card L :=
      natCard_quotient_lt_of_ne_bot N hNmin.ne_bot
    obtain ⟨Hbar, hHbar⟩ :=
      ih (Nat.card (L ⧸ N)) (by simpa [hcard] using hquotlt)
        (L := L ⧸ N) rfl
    let q : L →* L ⧸ N := QuotientGroup.mk' N
    let B : Subgroup L := Hbar.comap q
    have hNB : N ≤ B := QuotientGroup.le_comap_mk' N Hbar
    let NB : Subgroup B := N.subgroupOf B
    let f : B →* L ⧸ N := q.comp B.subtype
    have hkerf : f.ker = NB := by
      ext x
      change q (x : L) = 1 ↔ (x : L) ∈ N
      exact QuotientGroup.eq_one_iff (x : L)
    have hrangef : f.range = Hbar := by
      dsimp [f, B]
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
      exact Subgroup.map_comap_eq_self_of_surjective
        (QuotientGroup.mk'_surjective N) Hbar
    have hNBindex : NB.index = Nat.card Hbar := by
      calc
        NB.index = f.ker.index := congrArg Subgroup.index hkerf.symm
        _ = Nat.card f.range := Subgroup.index_ker f
        _ = Nat.card Hbar :=
          Nat.card_congr (MulEquiv.subgroupCongr hrangef).toEquiv
    have hNBcard : Nat.card NB = Nat.card N :=
      natCard_subgroupOf_eq hNB
    have hBindex : B.index = Hbar.index := by
      simpa [B, q] using
        Hbar.index_comap_of_surjective (QuotientGroup.mk'_surjective N)
    have hBcard : Nat.card B = Nat.card N * Nat.card Hbar := by
      rw [← NB.index_mul_card, hNBindex, hNBcard, mul_comm]
    by_cases hrPi : r ∈ pi
    · refine ⟨B, ?_⟩
      constructor
      · rw [hBcard]
        exact (hNr.isPiNumber_natCard hrPi).mul hHbar.isPiNumber_card
      · rw [hBindex]
        exact hHbar.isPiNumber_index
    · have hrCompl : r ∈ piᶜ := hrPi
      have hNcompl : IsPiNumber piᶜ (Nat.card N) :=
        hNr.isPiNumber_natCard hrCompl
      letI : NB.Normal := hNmin.normal.subgroupOf B
      have hcop : (Nat.card NB).Coprime NB.index := by
        rw [hNBcard, hNBindex]
        exact hNcompl.coprime_compl
          (by simpa only [compl_compl] using hHbar.isPiNumber_card)
      obtain ⟨C, hcomp⟩ := NB.exists_right_complement'_of_coprime hcop
      let H : Subgroup L := C.map B.subtype
      have hHcard : Nat.card H = Nat.card Hbar := by
        rw [Subgroup.card_map_of_injective B.subtype_injective,
          ← hNBindex]
        exact hcomp.symm.index_eq_card.symm
      refine ⟨H, ?_⟩
      constructor
      · rw [hHcard]
        exact hHbar.isPiNumber_card
      · change IsPiNumber piᶜ (C.map B.subtype).index
        rw [Subgroup.index_map_subtype, hcomp.index_eq_card,
          hNBcard, hBindex]
        exact hNcompl.mul hHbar.isPiNumber_index

/-- A subgroup whose order is coprime to a normal Hall factor can be
included in a suitable complement.  This is the relative form of
Schur--Zassenhaus used in Hall's subgroup-containment theorem. -/
private theorem exists_right_complement_ge_of_coprime
    {K : Type u} [Group K] [Finite K] [IsSolvable K]
    {N A : Subgroup K} [N.Normal]
    (hNcop : (Nat.card N).Coprime N.index)
    (hNAcop : (Nat.card N).Coprime (Nat.card A)) :
    ∃ C : Subgroup K, N.IsComplement' C ∧ A ≤ C := by
  classical
  obtain ⟨C, hC⟩ := N.exists_right_complement'_of_coprime hNcop
  let D : Subgroup K := N ⊔ A
  let ND : Subgroup D := N.subgroupOf D
  let AD : Subgroup D := A.subgroupOf D
  let CD : Subgroup D := (C ⊓ D).subgroupOf D
  letI : ND.Normal :=
    Subgroup.Normal.subgroupOf (inferInstance : N.Normal) D

  have hNDA : ND.IsComplement' AD := by
    have hdis : Disjoint ND AD := by
      rw [disjoint_iff]
      apply le_antisymm _ bot_le
      intro z hz
      apply Subgroup.mem_bot.mpr
      apply Subtype.ext
      have hzbot : ((z : D) : K) ∈ (⊥ : Subgroup K) := by
        rw [← disjoint_iff.mp
          (Subgroup.disjoint_of_coprime_natCard hNAcop)]
        exact hz
      exact Subgroup.mem_bot.mp hzbot
    apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdis
    rw [← Subgroup.normal_mul ND AD]
    have hsup : ND ⊔ AD = ⊤ := by
      change N.subgroupOf D ⊔ A.subgroupOf D = ⊤
      rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right]
      exact Subgroup.subgroupOf_self D
    rw [hsup]
    rfl

  have hNDC : ND.IsComplement' CD := by
    have hdis : Disjoint ND CD := by
      rw [disjoint_iff]
      apply le_antisymm _ bot_le
      intro z hz
      apply Subgroup.mem_bot.mpr
      apply Subtype.ext
      have hzbot : ((z : D) : K) ∈ (⊥ : Subgroup K) := by
        rw [← disjoint_iff.mp hC.disjoint]
        exact ⟨hz.1, hz.2.1⟩
      exact Subgroup.mem_bot.mp hzbot
    apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdis
    rw [← Subgroup.normal_mul ND CD]
    have hsup : ND ⊔ CD = ⊤ := by
      apply top_unique
      intro z _
      obtain ⟨nc, hnc, -⟩ := hC.existsUnique (z : K)
      have hcD : (nc.2 : K) ∈ D := by
        have hcEq : (nc.2 : K) = (nc.1 : K)⁻¹ * (z : K) := by
          rw [← hnc]
          simp
        rw [hcEq]
        exact D.mul_mem
          (D.inv_mem ((show N ≤ D from le_sup_left) nc.1.property))
          z.property
      let nD : ND :=
        ⟨⟨(nc.1 : K), (show N ≤ D from le_sup_left) nc.1.property⟩,
          nc.1.property⟩
      let cD : CD :=
        ⟨⟨(nc.2 : K), hcD⟩, ⟨nc.2.property, hcD⟩⟩
      have hmul : (nD : D) * (cD : D) ∈ ND ⊔ CD :=
        Subgroup.mul_mem_sup nD.property cD.property
      have hmulEq : (nD : D) * (cD : D) = z :=
        Subtype.ext hnc
      rwa [← hmulEq]
    rw [hsup]
    rfl

  have hNDcop : (Nat.card ND).Coprime ND.index := by
    rw [hNDA.symm.index_eq_card,
      natCard_subgroupOf_eq (show N ≤ D from le_sup_left),
      natCard_subgroupOf_eq (show A ≤ D from le_sup_right)]
    exact hNAcop
  obtain ⟨n, hn⟩ :=
    Subgroup.solvable_complement_conjugacy hNDcop hNDC hNDA
  let nK : K := ((n : ND) : D)
  let C' : Subgroup K :=
    C.map (MulAut.conj nK).toMonoidHom
  have hC'comp : N.IsComplement' C' := by
    have hcardC' : Nat.card C' = Nat.card C :=
      Subgroup.card_map_of_injective (MulAut.conj nK).injective
    have hcard : Nat.card N * Nat.card C' = Nat.card K := by
      rw [hcardC']
      exact hC.card_mul
    have hNmap :
        N.map (MulAut.conj nK).toMonoidHom = N :=
      Subgroup.Normal.map_conj_eq N nK
    have hdisMap : Disjoint
        (N.map (MulAut.conj nK).toMonoidHom) C' :=
      Subgroup.disjoint_map (MulAut.conj nK).injective hC.disjoint
    rw [hNmap] at hdisMap
    exact Subgroup.isComplement'_of_card_mul_and_disjoint
      hcard hdisMap
  refine ⟨C', hC'comp, ?_⟩
  intro a ha
  let aD : D := ⟨a, (show A ≤ D from le_sup_right) ha⟩
  have haAD : aD ∈ AD := ha
  rw [hn] at haAD
  obtain ⟨c, hc, hca⟩ := haAD
  refine ⟨((c : D) : K), hc.1, ?_⟩
  exact congrArg (fun x : D ↦ (x : K)) hca

/-- Hall's subgroup-containment theorem for finite solvable groups: every
`pi`-subgroup is contained in a `pi`-Hall subgroup. -/
theorem exists_isHall_ge_of_isSolvable
    {K : Type u} [Group K] [Finite K]
    (hsol : IsSolvable K) (pi : Set ℕ) {A : Subgroup K}
    (hApi : IsPiNumber pi (Nat.card A)) :
    ∃ H : Subgroup K, A ≤ H ∧ IsHall pi H := by
  classical
  letI : IsSolvable K := hsol
  let motive : ℕ → Prop := fun n ↦
    ∀ {L : Type u} [Group L] [Finite L] [IsSolvable L],
      Nat.card L = n → ∀ {A : Subgroup L},
        IsPiNumber pi (Nat.card A) →
          ∃ H : Subgroup L, A ≤ H ∧ IsHall pi H
  suffices hmain : motive (Nat.card K) from hmain rfl hApi
  exact Nat.strong_induction_on (p := motive) (Nat.card K) fun n ih ↦ by
    intro L _ _ _ hcard A hApi
    by_cases hcardOne : Nat.card L = 1
    · refine ⟨⊤, le_top, ?_⟩
      constructor
      · simpa [hcardOne] using (IsPiNumber.one (pi := pi))
      · simp only [Subgroup.index_top]
        exact IsPiNumber.one
    have hcardGt : 1 < Nat.card L :=
      (Nat.one_le_iff_ne_zero.mpr Nat.card_pos.ne').lt_of_ne
        (Ne.symm hcardOne)
    letI : Nontrivial L :=
      Finite.one_lt_card_iff_nontrivial.mp hcardGt
    obtain ⟨N, hNmin, -⟩ :=
      exists_minimalNormal_le (K := (⊤ : Subgroup L))
        (by infer_instance) top_ne_bot
    letI : N.Normal := hNmin.normal
    obtain ⟨r, hr, hNr⟩ := hNmin.exists_prime_isPGroup
    letI : Fact r.Prime := ⟨hr⟩
    have hquotlt : Nat.card (L ⧸ N) < Nat.card L :=
      natCard_quotient_lt_of_ne_bot N hNmin.ne_bot
    let q : L →* L ⧸ N := QuotientGroup.mk' N
    have hAbarPi : IsPiNumber pi (Nat.card (A.map q)) :=
      hApi.of_dvd (Subgroup.card_map_dvd A q)
    obtain ⟨Hbar, hAbarHbar, hHbar⟩ :=
      ih (Nat.card (L ⧸ N)) (by simpa [hcard] using hquotlt)
        (L := L ⧸ N) rfl hAbarPi
    let B : Subgroup L := Hbar.comap q
    have hAB : A ≤ B := by
      intro a ha
      change q a ∈ Hbar
      exact hAbarHbar (Subgroup.mem_map_of_mem q ha)
    have hNB : N ≤ B := QuotientGroup.le_comap_mk' N Hbar
    let NB : Subgroup B := N.subgroupOf B
    let f : B →* L ⧸ N := q.comp B.subtype
    have hkerf : f.ker = NB := by
      ext x
      change q (x : L) = 1 ↔ (x : L) ∈ N
      exact QuotientGroup.eq_one_iff (x : L)
    have hrangef : f.range = Hbar := by
      dsimp [f, B]
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
      exact Subgroup.map_comap_eq_self_of_surjective
        (QuotientGroup.mk'_surjective N) Hbar
    have hNBindex : NB.index = Nat.card Hbar := by
      calc
        NB.index = f.ker.index := congrArg Subgroup.index hkerf.symm
        _ = Nat.card f.range := Subgroup.index_ker f
        _ = Nat.card Hbar :=
          Nat.card_congr (MulEquiv.subgroupCongr hrangef).toEquiv
    have hNBcard : Nat.card NB = Nat.card N :=
      natCard_subgroupOf_eq hNB
    have hBindex : B.index = Hbar.index := by
      simpa [B, q] using
        Hbar.index_comap_of_surjective
          (QuotientGroup.mk'_surjective N)
    have hBcard : Nat.card B = Nat.card N * Nat.card Hbar := by
      rw [← NB.index_mul_card, hNBindex, hNBcard, mul_comm]
    by_cases hrPi : r ∈ pi
    · refine ⟨B, hAB, ?_⟩
      constructor
      · rw [hBcard]
        exact (hNr.isPiNumber_natCard hrPi).mul
          hHbar.isPiNumber_card
      · rw [hBindex]
        exact hHbar.isPiNumber_index
    · have hrCompl : r ∈ piᶜ := hrPi
      have hNcompl : IsPiNumber piᶜ (Nat.card N) :=
        hNr.isPiNumber_natCard hrCompl
      let AB : Subgroup B := A.subgroupOf B
      have hABpi : IsPiNumber pi (Nat.card AB) := by
        rw [natCard_subgroupOf_eq hAB]
        exact hApi
      have hNBcompl : IsPiNumber piᶜ (Nat.card NB) := by
        rw [hNBcard]
        exact hNcompl
      letI : NB.Normal := hNmin.normal.subgroupOf B
      have hNBcop : (Nat.card NB).Coprime NB.index := by
        rw [hNBcard, hNBindex]
        exact hNcompl.coprime_compl
          (by simpa only [compl_compl] using hHbar.isPiNumber_card)
      have hNBABcop : (Nat.card NB).Coprime (Nat.card AB) :=
        (hABpi.coprime_compl hNBcompl).symm
      obtain ⟨C, hcomp, hABC⟩ :=
        exists_right_complement_ge_of_coprime
          (N := NB) (A := AB) hNBcop hNBABcop
      let H : Subgroup L := C.map B.subtype
      have hAH : A ≤ H := by
        intro a ha
        let aB : B := ⟨a, hAB ha⟩
        have haAB : aB ∈ AB := ha
        exact Subgroup.mem_map_of_mem B.subtype (hABC haAB)
      have hHcard : Nat.card H = Nat.card Hbar := by
        rw [Subgroup.card_map_of_injective B.subtype_injective,
          ← hNBindex]
        exact hcomp.symm.index_eq_card.symm
      refine ⟨H, hAH, ?_⟩
      constructor
      · rw [hHcard]
        exact hHbar.isPiNumber_card
      · change IsPiNumber piᶜ (C.map B.subtype).index
        rw [Subgroup.index_map_subtype, hcomp.index_eq_card,
          hNBcard, hBindex]
        exact hNcompl.mul hHbar.isPiNumber_index

/-- Embed an intrinsic Hall subgroup as an ambient subgroup. -/
theorem exists_ambient_isHall_of_isSolvable
    {G : Type u} [Group G] [Finite G] {K : Subgroup G}
    (hsol : IsSolvable K) (pi : Set ℕ) :
    ∃ H : Subgroup G, H ≤ K ∧ IsHall pi (H.subgroupOf K) := by
  obtain ⟨H, hH⟩ := exists_isHall_of_isSolvable hsol pi
  let HG : Subgroup G := H.map K.subtype
  have hHGK : HG ≤ K := Subgroup.map_subtype_le H
  have hsubgroupOf : HG.subgroupOf K = H := by
    change (H.map K.subtype).comap K.subtype = H
    exact Subgroup.comap_map_eq_self_of_injective
      K.subtype_injective H
  refine ⟨HG, hHGK, ?_⟩
  rw [hsubgroupOf]
  exact hH

/-- Ambient form of Hall's subgroup-containment theorem.  If `A ≤ K` is
a `pi`-subgroup and `K` is solvable, an ambiently represented `pi`-Hall
subgroup of `K` can be chosen to contain `A`. -/
theorem exists_ambient_isHall_ge_of_isSolvable
    {G : Type u} [Group G] [Finite G]
    {K A : Subgroup G} (hAK : A ≤ K)
    (hsol : IsSolvable K) (pi : Set ℕ)
    (hApi : IsPiNumber pi (Nat.card A)) :
    ∃ H : Subgroup G, A ≤ H ∧ H ≤ K ∧
      IsHall pi (H.subgroupOf K) := by
  have hAsubPi : IsPiNumber pi (Nat.card (A.subgroupOf K)) := by
    rw [natCard_subgroupOf_eq hAK]
    exact hApi
  obtain ⟨H, hAH, hH⟩ :=
    exists_isHall_ge_of_isSolvable hsol pi hAsubPi
  let HG : Subgroup G := H.map K.subtype
  have hAHG : A ≤ HG := by
    intro a ha
    let aK : K := ⟨a, hAK ha⟩
    have haSub : aK ∈ A.subgroupOf K := ha
    exact Subgroup.mem_map_of_mem K.subtype (hAH haSub)
  have hHGK : HG ≤ K := Subgroup.map_subtype_le H
  have hsubgroupOf : HG.subgroupOf K = H := by
    change (H.map K.subtype).comap K.subtype = H
    exact Subgroup.comap_map_eq_self_of_injective
      K.subtype_injective H
  refine ⟨HG, hAHG, hHGK, ?_⟩
  rw [hsubgroupOf]
  exact hH

/-- `BGsection12.v: ex_sigma_compl`.

Every maximal subgroup has an ambiently represented
`sigma(M)`-complement Hall subgroup. -/
theorem ex_sigma_compl
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G)) :
    ∃ F : Subgroup G, F ≤ M ∧
      IsHall (sigmaPrimes M)ᶜ (F.subgroupOf M) :=
  exists_ambient_isHall_of_isSolvable
    (mmax_sol hM) (sigmaPrimes M)ᶜ

/-- `BGsection12.v: sigma_compl_sol`.

This deliberately does not assume that `M` is maximal.  A Hall subgroup
supported outside `sigma(M)` is a proper subgroup of the minimal
counterexample, and hence is solvable. -/
theorem sigma_compl_sol
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M E : Subgroup G} (hEM : E ≤ M)
    (hHall : IsHall (sigmaPrimes M)ᶜ (E.subgroupOf M)) :
    IsSolvable E := by
  classical
  apply mFT_sol
  rw [lt_top_iff_ne_top]
  intro hEtop
  have hMtop : M = ⊤ := by
    apply top_unique
    rw [← hEtop]
    exact hEM
  have hcardNe : Nat.card G ≠ 1 :=
    ne_of_gt (Finite.one_lt_card (α := G))
  obtain ⟨p, hp, hpG⟩ := Nat.exists_prime_and_dvd hcardNe
  have hpE : p ∣ Nat.card E := by
    simpa [hEtop] using hpG
  have hHallCard : IsPiNumber (sigmaPrimes M)ᶜ (Nat.card E) := by
    rw [← natCard_subgroupOf_eq hEM]
    exact hHall.isPiNumber_card
  have hpNotSigma : p ∉ sigmaPrimes M :=
    hHallCard hp hpE
  letI : Fact p.Prime := ⟨hp⟩
  let P : Sylow p M := Classical.choice Sylow.nonempty
  apply hpNotSigma
  refine ⟨hp, P, ?_⟩
  intro x _
  rw [hMtop]
  exact Subgroup.mem_top x

/-- `BGsection12.v: ex_tau13_compl`.

The two rank-one prime classes have Hall subgroups in any fixed sigma
complement. -/
theorem ex_tau13_compl
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M E : Subgroup G} (hEM : E ≤ M)
    (hHall : IsHall (sigmaPrimes M)ᶜ (E.subgroupOf M)) :
    (∃ E₁ : Subgroup G, E₁ ≤ E ∧
      IsHall (tau1Primes M) (E₁.subgroupOf E)) ∧
    (∃ E₃ : Subgroup G, E₃ ≤ E ∧
      IsHall (tau3Primes M) (E₃.subgroupOf E)) := by
  have hsol : IsSolvable E := sigma_compl_sol hEM hHall
  exact ⟨exists_ambient_isHall_of_isSolvable hsol (tau1Primes M),
    exists_ambient_isHall_of_isSolvable hsol (tau3Primes M)⟩

end

end Submission.OddOrder.BG.Section12
