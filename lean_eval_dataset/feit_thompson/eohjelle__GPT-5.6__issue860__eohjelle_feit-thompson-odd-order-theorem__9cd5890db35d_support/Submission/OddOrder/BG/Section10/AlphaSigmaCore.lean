import Submission.OddOrder.BG.Section04.RankTwoFittingDerived
import Submission.OddOrder.BG.Section04.RankTwoMaximalPrimeCoreSylow
import Submission.OddOrder.BG.Section10.SigmaTransitivity
import Submission.OddOrder.MathlibSupport.FittingNilpotent
import Submission.OddOrder.MathlibSupport.MaximalPrimeDivisor
import Submission.OddOrder.MathlibSupport.MinimalNormal
import Submission.OddOrder.MathlibSupport.MinimalNormalExistence
import Submission.OddOrder.MathlibSupport.NilpotentPrimeCores
import Submission.OddOrder.MathlibSupport.PElementCyclic
import Submission.OddOrder.MathlibSupport.PiCore
import Submission.OddOrder.MathlibSupport.Solvability
import Mathlib.GroupTheory.Focal

/-!
# Bender--Glauberman Section 10: the alpha and sigma cores

This file ports the block of `BGsection10.v` from `Malpha_Hall` through
`Msigma_neq1`.  The main structural input is Theorem 10.1, exposed in
`SigmaTransitivity`: its focal-subgroup application puts every
`sigma(M)`-Hall subgroup in `M'`.  The Fitting subgroup of
`M / alphaCore(M)` then controls both core Hall properties and the rank-two
quotient.
-/

namespace Submission.OddOrder.BG.Section10

open Submission.OddOrder.BG.Section04
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.MathlibSupport
open scoped commutatorElement IsMulCommutative

noncomputable section

universe u

private instance alphaCore_subgroupOf_normal
    {G : Type u} [Group G] [Finite G] (M : Subgroup G) :
    ((alphaCore M).subgroupOf M).Normal :=
  alphaCore_normal M

/-! ### Prime-set Hall lemmas -/

private theorem isPiNumber_card_sup_of_normal_left
    {K : Type u} [Group K] [Finite K] {pi : Set ℕ}
    {A B : Subgroup K} (hA : A.Normal)
    (hApi : IsPiNumber pi (Nat.card A))
    (hBpi : IsPiNumber pi (Nat.card B)) :
    IsPiNumber pi (Nat.card (A ⊔ B : Subgroup K)) := by
  letI : A.Normal := hA
  have hrel : A.relIndex (A ⊔ B) = A.relIndex B :=
    Subgroup.relIndex_sup_left B A
  have hsubcard : Nat.card (A.subgroupOf (A ⊔ B)) = Nat.card A :=
    natCard_subgroupOf_eq le_sup_left
  rw [← (A.subgroupOf (A ⊔ B)).card_mul_index, hsubcard]
  change IsPiNumber pi (Nat.card A * A.relIndex (A ⊔ B))
  rw [hrel]
  exact hApi.mul (hBpi.of_dvd (Subgroup.relIndex_dvd_card A B))

/-- A normal `pi`-subgroup is contained in every `pi`-Hall subgroup. -/
private theorem normal_isPiNumber_le_isHall
    {K : Type u} [Group K] [Finite K] {pi : Set ℕ}
    {A H : Subgroup K} (hA : A.Normal)
    (hApi : IsPiNumber pi (Nat.card A)) (hH : IsHall pi H) :
    A ≤ H := by
  have hHsup : H ≤ A ⊔ H := le_sup_right
  have hrelPi : IsPiNumber pi (H.relIndex (A ⊔ H)) :=
    (isPiNumber_card_sup_of_normal_left hA hApi hH.isPiNumber_card).of_dvd
      (Subgroup.relIndex_dvd_card H (A ⊔ H))
  have hrelCompl : IsPiNumber piᶜ (H.relIndex (A ⊔ H)) :=
    hH.isPiNumber_index.of_dvd
      (Subgroup.relIndex_dvd_index_of_le hHsup)
  have hcop : (H.relIndex (A ⊔ H)).Coprime
      (H.relIndex (A ⊔ H)) := hrelPi.coprime_compl hrelCompl
  have hone : H.relIndex (A ⊔ H) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop dvd_rfl dvd_rfl
  exact le_sup_left.trans (Subgroup.relIndex_eq_one.mp hone)

/-- A normal Hall subgroup is the corresponding group-level prime core. -/
private theorem normalHall_eq_piCore
    {K : Type u} [Group K] [Finite K] {pi : Set ℕ}
    {H : Subgroup K} (hHnormal : H.Normal) (hH : IsHall pi H) :
    H = piCore pi K := by
  apply le_antisymm
  · exact le_piCore hHnormal hH.isPiNumber_card
  · exact normal_isPiNumber_le_isHall
      (inferInstance : (piCore pi K).Normal)
      (piCore_isPiNumber pi) hH

/-- The ambient prime-set core, restricted to its defining subgroup, is
the ordinary group-level `piCore` of that subgroup. -/
private theorem primeSetCore_subgroupOf_eq_piCore
    {K : Type u} [Group K] [Finite K]
    (pi : Set ℕ) (X : Subgroup K) :
    (primeSetCore pi X).subgroupOf X = piCore pi X := by
  let A : Subgroup K := primeSetCore pi X
  have hAX : A ≤ X := primeSetCore_le pi X
  apply le_antisymm
  · apply le_piCore
    · simpa [A] using primeSetCore_normal pi X
    · rw [natCard_subgroupOf_eq hAX]
      simpa [A] using primeSetCore_isPiNumber pi X
  · intro x hx
    change (x : K) ∈ A
    have hmapNormal :
        (((piCore pi X).map X.subtype).subgroupOf X).Normal := by
      change (((piCore pi X).map X.subtype).comap X.subtype).Normal
      rw [Subgroup.comap_map_eq_self_of_injective X.subtype_injective]
      infer_instance
    have hmapPi : IsPiNumber pi
        (Nat.card ((piCore pi X).map X.subtype)) := by
      rw [Subgroup.card_map_of_injective X.subtype_injective]
      exact piCore_isPiNumber pi
    have hmapCore : (piCore pi X).map X.subtype ≤ A := by
      dsimp only [A]
      rw [primeSetCore]
      exact le_sSup ⟨Subgroup.map_subtype_le _, hmapNormal, hmapPi⟩
    exact hmapCore (Subgroup.mem_map_of_mem X.subtype hx)

/-- Hall's existence theorem in the only form needed here.  The proof is
the usual induction through a minimal normal elementary-abelian factor. -/
private theorem exists_isHall_of_isSolvable
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
      Nat.one_lt_iff_ne_zero_and_ne_one.mpr
        ⟨(Nat.card_pos (α := L)).ne', hcardOne⟩
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
        exact (hHbar.isPiNumber_card.coprime_compl hNcompl).symm
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
      · dsimp only [H]
        rw [Subgroup.index_map_subtype, hcomp.index_eq_card,
          hNBcard, hBindex]
        exact hNcompl.mul hHbar.isPiNumber_index

/-! ### Nilpotent Hall subgroups and elementary-abelian lifting -/

private theorem hall_le_piCore_of_isNilpotent
    {K : Type u} [Group K] [Finite K] [Group.IsNilpotent K]
    {pi : Set ℕ} {H : Subgroup K} (hH : IsHall pi H) :
    H ≤ piCore pi K := by
  calc
    H = (sylowSup H).map H.subtype := by
      rw [sylowSup_eq_top]
      exact H.range_subtype.symm.trans
        (MonoidHom.range_eq_map H.subtype)
    _ = ⨆ p : {p : ℕ // p.Prime},
        ((Classical.choice
          (Sylow.nonempty (p := (p : ℕ)) (G := H)) : Sylow p H) :
          Subgroup H).map H.subtype := by
      rw [sylowSup, Subgroup.map_iSup]
    _ ≤ piCore pi K := by
      apply iSup_le
      intro p
      letI : Fact (p : ℕ).Prime := ⟨p.property⟩
      let P : Sylow (p : ℕ) H := Classical.choice Sylow.nonempty
      by_cases hPbot : (P : Subgroup H) = ⊥
      · simp [P, hPbot]
      have hpP : (p : ℕ) ∣ Nat.card P :=
        P.isPGroup'.card_eq_or_dvd.resolve_left
          (fun hcard ↦ hPbot (Subgroup.card_eq_one.mp hcard))
      have hpPi : (p : ℕ) ∈ pi :=
        hH.isPiNumber_card p.property
          (hpP.trans (P : Subgroup H).card_subgroup_dvd_card)
      have hmapP : IsPGroup (p : ℕ)
          ((P : Subgroup H).map H.subtype) := P.isPGroup'.map H.subtype
      exact (hmapP.le_pCore_of_isNilpotent).trans
        (le_piCore (by infer_instance)
          (pCore_isPGroup.isPiNumber_natCard hpPi))

private theorem hall_eq_piCore_of_isNilpotent
    {K : Type u} [Group K] [Finite K] [Group.IsNilpotent K]
    {pi : Set ℕ} {H : Subgroup K} (hH : IsHall pi H) :
    H = piCore pi K := by
  have hle : H ≤ piCore pi K := hall_le_piCore_of_isNilpotent hH
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

/-- Elementary-abelian subgroups lift across a normal kernel whose order is
supported away from their prime. -/
private theorem exists_elementaryAbelian_lift
    {K : Type u} [Group K] [Finite K]
    {pi : Set ℕ} {N : Subgroup K} (hNnormal : N.Normal)
    (hNpi : IsPiNumber pi (Nat.card N))
    {p : ℕ} (hp : p.Prime) (hpNot : p ∉ pi)
    {E : Subgroup (K ⧸ N)} (hE : IsElementaryAbelianOfRank p 3 E) :
    ∃ C : Subgroup K, IsElementaryAbelianOfRank p 3 C := by
  classical
  letI : N.Normal := hNnormal
  letI : Fact p.Prime := ⟨hp⟩
  let q : K →* K ⧸ N := QuotientGroup.mk' N
  let L : Subgroup K := E.comap q
  have hNL : N ≤ L := QuotientGroup.le_comap_mk' N E
  let NL : Subgroup L := N.subgroupOf L
  letI : NL.Normal := hNnormal.subgroupOf L
  let f : L →* E :=
    (q.comp L.subtype).codRestrict E (fun x ↦ x.property)
  have hfker : f.ker = NL := by
    ext x
    constructor
    · intro hx
      have hfx : f x = 1 := hx
      have hxq : q (x : K) = 1 := congrArg Subtype.val hfx
      change (x : L) ∈ NL
      change (x : K) ∈ N
      exact (QuotientGroup.eq_one_iff (x : K)).mp hxq
    · intro hx
      change (x : K) ∈ N at hx
      change f x = 1
      apply Subtype.ext
      change q (x : K) = 1
      exact (QuotientGroup.eq_one_iff (x : K)).mpr hx
  have hfsurj : Function.Surjective f := by
    intro e
    obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective N (e : K ⧸ N)
    let gL : L := ⟨g, by
      change q g ∈ E
      rw [hg]
      exact e.property⟩
    refine ⟨gL, ?_⟩
    apply Subtype.ext
    exact hg
  have hNLcard : Nat.card NL = Nat.card N :=
    natCard_subgroupOf_eq hNL
  have hNLindex : NL.index = Nat.card E := by
    calc
      NL.index = f.ker.index := congrArg Subgroup.index hfker.symm
      _ = Nat.card f.range := Subgroup.index_ker f
      _ = Nat.card E := by
        rw [MonoidHom.range_eq_top.mpr hfsurj]
        simp
  have hpCompl : IsPiNumber piᶜ (p ^ 3) := by
    have hpComplMem : p ∈ piᶜ := hpNot
    simpa only [hE.card_eq] using
      (IsPGroup.of_card (G := E) (n := 3) hE.card_eq).isPiNumber_natCard
        hpComplMem
  have hcop : (Nat.card NL).Coprime NL.index := by
    rw [hNLcard, hNLindex, hE.card_eq]
    exact hNpi.coprime_compl hpCompl
  obtain ⟨C, hcomp⟩ := NL.exists_right_complement'_of_coprime hcop
  have hCcard : Nat.card C = p ^ 3 := by
    calc
      Nat.card C = NL.index := hcomp.symm.index_eq_card.symm
      _ = Nat.card E := hNLindex
      _ = p ^ 3 := hE.card_eq
  let fC : C →* E := f.comp C.subtype
  have hfCinj : Function.Injective fC := by
    rw [← MonoidHom.ker_eq_bot_iff]
    apply le_antisymm
    · intro x hx
      have hxNL : (x : L) ∈ NL := by
        rw [← hfker]
        exact hx
      have hxbot : (x : L) ∈ (⊥ : Subgroup L) :=
        hcomp.disjoint.symm.le_bot ⟨x.property, hxNL⟩
      rw [Subgroup.mem_bot] at hxbot ⊢
      exact Subtype.ext hxbot
    · exact bot_le
  letI : IsMulCommutative E := hE.commutative
  have hCelem : IsElementaryAbelianOfRank p 3 C :=
    { isPGroup := IsPGroup.of_card (n := 3) hCcard
      commutative := isMulCommutative_iff.mpr (fun x y ↦ by
        apply hfCinj
        simp only [map_mul]
        exact mul_comm _ _)
      pow_eq_one := fun x ↦ by
        apply hfCinj
        rw [map_pow, map_one]
        exact hE.pow_eq_one (fC x)
      card_eq := hCcard }
  exact ⟨C.map L.subtype,
    hCelem.map_of_injective L.subtype L.subtype_injective⟩

private theorem relIndex_eq_card_map_quotient
    {K : Type u} [Group K] [Finite K]
    {N H : Subgroup K} (hNnormal : N.Normal) (hNH : N ≤ H) :
    N.relIndex H = Nat.card (H.map (QuotientGroup.mk' N)) := by
  letI : N.Normal := hNnormal
  let q : K →* K ⧸ N := QuotientGroup.mk' N
  let f : H →* K ⧸ N := q.comp H.subtype
  have hker : f.ker = N.subgroupOf H := by
    ext x
    change q (x : K) = 1 ↔ (x : K) ∈ N
    exact QuotientGroup.eq_one_iff (x : K)
  have hrange : f.range = H.map q := by
    dsimp [f]
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  calc
    N.relIndex H = (N.subgroupOf H).index := rfl
    _ = f.ker.index := congrArg Subgroup.index hker.symm
    _ = Nat.card f.range := Subgroup.index_ker f
    _ = Nat.card (H.map q) :=
      Nat.card_congr (MulEquiv.subgroupCongr hrange).toEquiv

/-! ### The Fitting subgroup of the alpha quotient -/

private theorem alphaFitting_isPiNumber_compl
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G)) :
    IsPiNumber (alphaPrimes M)ᶜ
      (Nat.card
        (fittingCore (M ⧸ (alphaCore M).subgroupOf M))) := by
  classical
  let A : Subgroup M := (alphaCore M).subgroupOf M
  have hAnormal : A.Normal := by
    simpa [A] using alphaCore_normal M
  letI : A.Normal := hAnormal
  let Q := M ⧸ A
  let F : Subgroup Q := fittingCore Q
  letI : Group.IsNilpotent F := by
    dsimp [F]
    infer_instance
  intro p hp hpF hpAlpha
  letI : Fact p.Prime := ⟨hp⟩
  let P : Subgroup Q := (pCore p F).map F.subtype
  have hpCoreNe : pCore p F ≠ ⊥ :=
    (pCore_ne_bot_iff_dvd_card_of_isNilpotent (G := F) p).2 hpF
  have hPne : P ≠ ⊥ := by
    intro hPbot
    apply hpCoreNe
    exact (Subgroup.map_eq_bot_iff_of_injective
      (pCore p F) F.subtype_injective).mp hPbot
  have hPnormal : P.Normal := by
    dsimp [P, F]
    infer_instance
  have hPp : IsPGroup p P := by
    dsimp [P]
    exact pCore_isPGroup.map F.subtype
  let q := QuotientGroup.mk' A
  let K : Subgroup M := P.comap q
  have hAK : A ≤ K := by
    dsimp [K, q]
    exact QuotientGroup.le_comap_mk' A P
  let AK : Subgroup K := A.subgroupOf K
  let f : K →* Q := q.comp K.subtype
  have hker : f.ker = AK := by
    ext x
    change q (x : M) = 1 ↔ (x : M) ∈ A
    exact QuotientGroup.eq_one_iff (x : M)
  have hrange : f.range = P := by
    dsimp [f, K]
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    exact Subgroup.map_comap_eq_self_of_surjective
      (QuotientGroup.mk'_surjective A) P
  have hAKindex : AK.index = Nat.card P := by
    calc
      AK.index = f.ker.index := congrArg Subgroup.index hker.symm
      _ = Nat.card f.range := Subgroup.index_ker f
      _ = Nat.card P :=
        Nat.card_congr (MulEquiv.subgroupCongr hrange).toEquiv
  have hAKcard : Nat.card AK = Nat.card A :=
    natCard_subgroupOf_eq hAK
  have hAcard : IsPiNumber (alphaPrimes M) (Nat.card A) := by
    rw [natCard_subgroupOf_eq (alphaCore_le M)]
    exact alphaCore_isPiNumber M
  have hPcard : IsPiNumber (alphaPrimes M) (Nat.card P) :=
    hPp.isPiNumber_natCard hpAlpha
  have hKcard : IsPiNumber (alphaPrimes M) (Nat.card K) := by
    rw [← AK.card_mul_index, hAKcard, hAKindex]
    exact hAcard.mul hPcard
  have hKnormal : K.Normal := by
    dsimp [K]
    letI : P.Normal := hPnormal
    infer_instance
  have hKcore : K ≤ piCore (alphaPrimes M) M :=
    le_piCore hKnormal hKcard
  have hKA : K ≤ A := by
    simpa [A, alphaCore] using (show
      K ≤ (primeSetCore (alphaPrimes M) M).subgroupOf M from by
        rw [primeSetCore_subgroupOf_eq_piCore]
        exact hKcore)
  have hKeq : K = A := le_antisymm hKA hAK
  have hPbot : P = ⊥ := by
    calc
      P = K.map q :=
        (Subgroup.map_comap_eq_self_of_surjective
          (QuotientGroup.mk'_surjective A) P).symm
      _ = A.map q := congrArg (fun L : Subgroup M ↦ L.map q) hKeq
      _ = ⊥ := by
        rw [Subgroup.map_eq_bot_iff]
        dsimp only [q]
        rw [QuotientGroup.ker_mk']
  exact hPne hPbot

/-- The derived subgroup of the alpha quotient lies in its Fitting
subgroup.  This is the private `Malpha_quo_sub_Fitting` step in the Coq
proof. -/
private theorem Malpha_quo_sub_Fitting
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G)) :
    _root_.commutator (M ⧸ (alphaCore M).subgroupOf M) ≤
      fittingCore (M ⧸ (alphaCore M).subgroupOf M) := by
  classical
  let A : Subgroup M := (alphaCore M).subgroupOf M
  have hAnormal : A.Normal := by
    simpa [A] using alphaCore_normal M
  letI : A.Normal := hAnormal
  let Q := M ⧸ A
  let F : Subgroup Q := fittingCore Q
  have hAcard : IsPiNumber (alphaPrimes M) (Nat.card A) := by
    rw [natCard_subgroupOf_eq (alphaCore_le M)]
    exact alphaCore_isPiNumber M
  have hFcompl : IsPiNumber (alphaPrimes M)ᶜ (Nat.card F) := by
    simpa [A, Q, F] using alphaFitting_isPiNumber_compl hM
  have hRank : ∀ p : ℕ, p.Prime →
      ¬ ∃ E : Subgroup F, IsElementaryAbelianOfRank p 3 E := by
    intro p hp
    rintro ⟨E, hE⟩
    have hpE : p ∣ Nat.card E := by
      rw [hE.card_eq]
      exact dvd_pow_self p (by omega)
    have hpF : p ∣ Nat.card F :=
      hpE.trans (E : Subgroup F).card_subgroup_dvd_card
    have hpNot : p ∉ alphaPrimes M := hFcompl hp hpF
    let Ebar : Subgroup Q := E.map F.subtype
    have hEbar : IsElementaryAbelianOfRank p 3 Ebar := by
      dsimp [Ebar]
      exact hE.map_of_injective F.subtype F.subtype_injective
    obtain ⟨C, hC⟩ := exists_elementaryAbelian_lift
      (K := M) (N := A) hAnormal hAcard hp hpNot hEbar
    apply hpNot
    exact ⟨hp, C.map M.subtype, Subgroup.map_subtype_le C,
      hC.map_of_injective M.subtype M.subtype_injective⟩
  have hQodd : Odd (Nat.card Q) := by
    simpa [Q, A] using mFT_quo_odd_subgroup M A
  have hQsol : IsSolvable Q := by
    letI : IsSolvable M := mmax_sol hM
    dsimp [Q]
    infer_instance
  simpa [A, Q, F] using
    (rank2_der1_sub_Fitting (G := Q) hQodd hQsol hRank)

/-! ### The focal-subgroup step -/

private theorem sigmaSylow_le_commutator
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    {p : ℕ} (hp : p ∈ sigmaPrimes M) (P : Sylow p M) :
    (P : Subgroup M) ≤ _root_.commutator M := by
  classical
  letI : Fact p.Prime := ⟨hp.1⟩
  obtain ⟨R, hR⟩ := sigma_Sylow_G hM hp P
  have hGder : _root_.commutator G = ⊤ := by
    rcases (inferInstance : (_root_.commutator G).Normal).eq_bot_or_eq_top
      with hbot | htop
    · exact (mFT_nonAbelian (G := G)
        (isMulCommutative_iff.mp
          ((_root_.commutator_eq_bot_iff G).mp hbot))).elim
    · exact htop
  have hRfocal : (R : Subgroup G) = (R : Subgroup G).focalSubgroup := by
    rw [← Subgroup.commutator_inf_eq_focalSubgroup R, hGder, top_inf_eq]
  have hRleM : (R : Subgroup G) ≤ M := by
    rw [hR]
    exact Subgroup.map_subtype_le _
  have hfocal : (R : Subgroup G).focalSubgroup ≤
      (_root_.commutator M).map M.subtype := by
    rw [Subgroup.focalSubgroup_def, Subgroup.closure_le]
    rintro _ ⟨hyR, x, hxR, v, rfl⟩
    have hxM : x ∈ M := hRleM hxR
    have hyM : ⁅x, v⁆ ∈ M := hRleM hyR
    have hconjR : v * x * v⁻¹ ∈ (R : Subgroup G) := by
      have h := (R : Subgroup G).mul_mem
        ((R : Subgroup G).inv_mem hyR) hxR
      simpa only [commutatorElement_def, mul_inv_rev, inv_inv,
        mul_assoc, inv_mul_cancel, mul_one] using h
    have hconjM : v * x * v⁻¹ ∈ M := hRleM hconjR
    let X : Subgroup G := Subgroup.zpowers x
    have hXp : IsPGroup p X :=
      R.isPGroup'.to_le (by
        simpa only [X] using Subgroup.zpowers_le.mpr hxR)
    have hXM : X ≤ M := by
      simpa only [X] using Subgroup.zpowers_le.mpr hxM
    have hXconjM :
        X.map (MulAut.conj (v⁻¹)⁻¹).toMonoidHom ≤ M := by
      dsimp only [X]
      rw [MonoidHom.map_zpowers, Subgroup.zpowers_le]
      simpa only [inv_inv, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        using hconjM
    obtain ⟨c, hcX, m, hmM, hv⟩ :=
      (sigma_group_trans hM hp hXp).1 (v⁻¹) hXM hXconjM
    have hxc : x * c = c * x :=
      Subgroup.mem_centralizer_iff.mp hcX x (by
        change x ∈ Subgroup.zpowers x
        exact Subgroup.mem_zpowers x)
    have hv' : v = m⁻¹ * c⁻¹ := by
      simpa only [inv_inv, mul_inv_rev] using
        congrArg (fun z : G ↦ z⁻¹) hv
    have hcxi : c⁻¹ * x⁻¹ * c = x⁻¹ := by
      have hinv : c⁻¹ * x⁻¹ = x⁻¹ * c⁻¹ := by
        simpa only [mul_inv_rev] using
          congrArg (fun z : G ↦ z⁻¹) hxc
      rw [hinv]
      simp
    have hcommEq : ⁅x, v⁆ = ⁅x, m⁻¹⁆ := by
      calc
        ⁅x, v⁆ = x * (m⁻¹ * c⁻¹) * x⁻¹ * (c * m) := by
          rw [commutatorElement_def, hv, hv']
        _ = x * m⁻¹ * (c⁻¹ * x⁻¹ * c) * m := by group
        _ = x * m⁻¹ * x⁻¹ * m := by rw [hcxi]
        _ = ⁅x, m⁻¹⁆ := by
          simp only [commutatorElement_def, inv_inv]
    let xM : M := ⟨x, hxM⟩
    let yM : M := ⟨⁅x, v⁆, hyM⟩
    let mM : M := ⟨m⁻¹, M.inv_mem hmM⟩
    have hxP : xM ∈ (P : Subgroup M) := by
      rw [← Subgroup.mem_map_iff_mem M.subtype_injective]
      change x ∈ ambientSylow M P
      rwa [← hR]
    have hyP : yM ∈ (P : Subgroup M) := by
      rw [← Subgroup.mem_map_iff_mem M.subtype_injective]
      change ⁅x, v⁆ ∈ ambientSylow M P
      rwa [← hR]
    have hyFocal : yM ∈ (P : Subgroup M).focalSubgroup := by
      rw [Subgroup.focalSubgroup_def]
      apply Subgroup.subset_closure
      refine ⟨hyP, xM, hxP, mM, ?_⟩
      apply Subtype.ext
      change ⁅x, v⁆ = ⁅x, m⁻¹⁆
      exact hcommEq
    have hyDer : yM ∈ _root_.commutator M :=
      (P : Subgroup M).focalSubgroup_le_commutator hyFocal
    exact ⟨yM, hyDer, rfl⟩
  have hPmap : (P : Subgroup M).map M.subtype ≤
      (_root_.commutator M).map M.subtype := by
    change ambientSylow M P ≤ _
    rw [← hR, hRfocal]
    exact hfocal
  exact (Subgroup.map_le_map_iff_of_injective
    M.subtype_injective).mp hPmap

/-- Every `sigma(M)`-Hall subgroup is contained in `M'`. -/
private theorem sigma_Hall_sub_der1
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    {H : Subgroup M} (hH : IsHall (sigmaPrimes M) H) :
    H ≤ _root_.commutator M := by
  classical
  calc
    H = (sylowSup H).map H.subtype := by
      rw [sylowSup_eq_top]
      exact H.range_subtype.symm.trans
        (MonoidHom.range_eq_map H.subtype)
    _ = ⨆ p : {p : ℕ // p.Prime},
        ((Classical.choice
          (Sylow.nonempty (p := (p : ℕ)) (G := H)) : Sylow p H) :
          Subgroup H).map H.subtype := by
      rw [sylowSup, Subgroup.map_iSup]
    _ ≤ _root_.commutator M := by
      apply iSup_le
      intro p
      letI : Fact (p : ℕ).Prime := ⟨p.property⟩
      let P : Sylow (p : ℕ) H := Classical.choice Sylow.nonempty
      by_cases hPbot : (P : Subgroup H) = ⊥
      · simp [P, hPbot]
      have hpP : (p : ℕ) ∣ Nat.card P :=
        P.isPGroup'.card_eq_or_dvd.resolve_left
          (fun hcard ↦ hPbot (Subgroup.card_eq_one.mp hcard))
      have hpSigma : (p : ℕ) ∈ sigmaPrimes M :=
        hH.isPiNumber_card p.property
          (hpP.trans (P : Subgroup H).card_subgroup_dvd_card)
      have hpHindex : ¬ (p : ℕ) ∣ H.index := by
        intro hpIndex
        exact hH.isPiNumber_index p.property hpIndex hpSigma
      let S : Subgroup M := (P : Subgroup H).map H.subtype
      have hSp : IsPGroup (p : ℕ) S := by
        dsimp [S]
        exact P.isPGroup'.map H.subtype
      have hpSindex : ¬ (p : ℕ) ∣ S.index := by
        dsimp [S]
        rw [Subgroup.index_map_subtype]
        exact p.property.not_dvd_mul P.not_dvd_index hpHindex
      let Q : Sylow (p : ℕ) M := hSp.toSylow hpSindex
      simpa [Q, S] using sigmaSylow_le_commutator hM hpSigma Q

/-! ### Hall properties of the two cores -/

/-- `BGsection10.v: Malpha_Hall`. -/
theorem Malpha_Hall
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G)) :
    IsHall (alphaPrimes M) ((alphaCore M).subgroupOf M) := by
  classical
  let A : Subgroup M := (alphaCore M).subgroupOf M
  have hAnormal : A.Normal := by
    simpa [A] using alphaCore_normal M
  letI : A.Normal := hAnormal
  let Q := M ⧸ A
  let F : Subgroup Q := fittingCore Q
  have hAalpha : IsPiNumber (alphaPrimes M) (Nat.card A) := by
    rw [natCard_subgroupOf_eq (alphaCore_le M)]
    exact alphaCore_isPiNumber M
  have hAsigma : IsPiNumber (sigmaPrimes M) (Nat.card A) :=
    hAalpha.mono (alpha_sub_sigma hM)
  obtain ⟨H, hHHall⟩ :=
    exists_isHall_of_isSolvable (mmax_sol hM) (sigmaPrimes M)
  have hAH : A ≤ H :=
    normal_isPiNumber_le_isHall hAnormal hAsigma hHHall
  have hHder : H ≤ _root_.commutator M :=
    sigma_Hall_sub_der1 hM hHHall
  let q := QuotientGroup.mk' A
  have hmapDer : (_root_.commutator M).map q =
      _root_.commutator Q := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr
      (QuotientGroup.mk'_surjective A)]
    rfl
  have hHbarF : H.map q ≤ F := by
    calc
      H.map q ≤ (_root_.commutator M).map q := Subgroup.map_mono hHder
      _ = _root_.commutator Q := hmapDer
      _ ≤ F := by
        simpa [Q, F, A] using Malpha_quo_sub_Fitting hM
  have hFcompl : IsPiNumber (alphaPrimes M)ᶜ (Nat.card F) := by
    simpa [A, Q, F] using alphaFitting_isPiNumber_compl hM
  have hrelCompl : IsPiNumber (alphaPrimes M)ᶜ (A.relIndex H) := by
    rw [relIndex_eq_card_map_quotient hAnormal hAH]
    exact hFcompl.of_dvd (Subgroup.card_dvd_of_le hHbarF)
  have hHindexCompl : IsPiNumber (alphaPrimes M)ᶜ H.index := by
    apply hHHall.isPiNumber_index.mono
    intro p hpNotSigma hpAlpha
    exact hpNotSigma (alpha_sub_sigma hM hpAlpha)
  constructor
  · simpa [A] using hAalpha
  · rw [← A.relIndex_mul_index hAH]
    exact hrelCompl.mul hHindexCompl

/-- `BGsection10.v: Msigma_Hall`. -/
theorem Msigma_Hall
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G)) :
    IsHall (sigmaPrimes M) ((sigmaCore M).subgroupOf M) := by
  classical
  let A : Subgroup M := (alphaCore M).subgroupOf M
  have hAnormal : A.Normal := by
    simpa [A] using alphaCore_normal M
  letI : A.Normal := hAnormal
  let Q := M ⧸ A
  let F : Subgroup Q := fittingCore Q
  have hAalpha : IsPiNumber (alphaPrimes M) (Nat.card A) := by
    rw [natCard_subgroupOf_eq (alphaCore_le M)]
    exact alphaCore_isPiNumber M
  have hAsigma : IsPiNumber (sigmaPrimes M) (Nat.card A) :=
    hAalpha.mono (alpha_sub_sigma hM)
  obtain ⟨H, hHHall⟩ :=
    exists_isHall_of_isSolvable (mmax_sol hM) (sigmaPrimes M)
  have hAH : A ≤ H :=
    normal_isPiNumber_le_isHall hAnormal hAsigma hHHall
  have hHder : H ≤ _root_.commutator M :=
    sigma_Hall_sub_der1 hM hHHall
  let q := QuotientGroup.mk' A
  let Hbar : Subgroup Q := H.map q
  have hmapDer : (_root_.commutator M).map q =
      _root_.commutator Q := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr
      (QuotientGroup.mk'_surjective A)]
    rfl
  have hHbarF : Hbar ≤ F := by
    calc
      Hbar = H.map q := rfl
      _ ≤ (_root_.commutator M).map q := Subgroup.map_mono hHder
      _ = _root_.commutator Q := hmapDer
      _ ≤ F := by
        simpa [Q, F, A] using Malpha_quo_sub_Fitting hM
  have hkerH : q.ker ≤ H := by
    dsimp only [q]
    simpa only [QuotientGroup.ker_mk'] using hAH
  have hHbarHallQ : IsHall (sigmaPrimes M) Hbar := by
    constructor
    · exact hHHall.isPiNumber_card.of_dvd
        (Subgroup.card_map_dvd H q)
    · dsimp only [Hbar]
      rw [H.index_map_eq
        (QuotientGroup.mk'_surjective A) hkerH]
      exact hHHall.isPiNumber_index
  let HF : Subgroup F := Hbar.subgroupOf F
  have hHFHall : IsHall (sigmaPrimes M) HF := by
    constructor
    · rw [natCard_subgroupOf_eq hHbarF]
      exact hHbarHallQ.isPiNumber_card
    · exact hHbarHallQ.isPiNumber_index.of_dvd
        (Subgroup.relIndex_dvd_index_of_le hHbarF)
  letI : Group.IsNilpotent F := by
    dsimp [F]
    infer_instance
  have hHFeq : HF = piCore (sigmaPrimes M) F :=
    hall_eq_piCore_of_isNilpotent hHFHall
  have hHFchar : HF.Characteristic := by
    rw [hHFeq]
    infer_instance
  have hHbarNormal : Hbar.Normal := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hHbarF]
    letI : HF.Characteristic := hHFchar
    dsimp [F]
    infer_instance
  have hHnormal : H.Normal := by
    have hcomap : Hbar.comap q = H := by
      dsimp [Hbar]
      exact Subgroup.comap_map_eq_self hkerH
    rw [← hcomap]
    letI : Hbar.Normal := hHbarNormal
    infer_instance
  have hHeq : H = piCore (sigmaPrimes M) M :=
    normalHall_eq_piCore hHnormal hHHall
  have hcoreEq : (sigmaCore M).subgroupOf M =
      piCore (sigmaPrimes M) M := by
    simpa [sigmaCore] using
      primeSetCore_subgroupOf_eq_piCore (sigmaPrimes M) M
  rw [hcoreEq, ← hHeq]
  exact hHHall

/-- The primes dividing the sigma core are exactly `sigma(M)`. -/
theorem pi_Msigma
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G)) :
    primeSupport (Nat.card (sigmaCore M)) = sigmaPrimes M := by
  let S : Subgroup M := (sigmaCore M).subgroupOf M
  have hHall : IsHall (sigmaPrimes M) S := Msigma_Hall hM
  ext p
  constructor
  · rintro hpS
    have hpS' : p ∈ primeSupport (Nat.card S) := by
      simpa [S, natCard_subgroupOf_eq (sigmaCore_le M)] using hpS
    exact hHall.isPiNumber_card hpS'.1 hpS'.2
  · intro hpSigma
    have hpM : p ∈ primeSupport (Nat.card M) :=
      sigma_sub_primeSupport hM hpSigma
    have hpMul : p ∣ Nat.card S * S.index := by
      rw [S.card_mul_index]
      exact hpM.2
    rcases hpM.1.dvd_mul.mp hpMul with hpCard | hpIndex
    · refine ⟨hpM.1, ?_⟩
      simpa [S, natCard_subgroupOf_eq (sigmaCore_le M)] using hpCard
    · exact (hHall.isPiNumber_index hpM.1 hpIndex hpSigma).elim

private theorem mmax_index_isPiNumber_sigma_compl
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G)) :
    IsPiNumber (sigmaPrimes M)ᶜ M.index := by
  intro p hp hpIndex hpSigma
  letI : Fact p.Prime := ⟨hp⟩
  let P : Sylow p M := Classical.choice Sylow.nonempty
  obtain ⟨R, hR⟩ := sigma_Sylow_G hM hpSigma P
  apply R.not_dvd_index
  rw [hR, ambientSylow, Subgroup.index_map_subtype]
  exact dvd_mul_of_dvd_right hpIndex P.index

/-- `BGsection10.v: Msigma_Hall_G`. -/
theorem Msigma_Hall_G
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G)) :
    IsHall (sigmaPrimes M) (sigmaCore M) := by
  let S : Subgroup M := (sigmaCore M).subgroupOf M
  have hHall : IsHall (sigmaPrimes M) S := Msigma_Hall hM
  constructor
  · exact sigmaCore_isPiNumber M
  · rw [← Subgroup.map_subgroupOf_eq_of_le (sigmaCore_le M),
      Subgroup.index_map_subtype]
    exact hHall.isPiNumber_index.mul
      (mmax_index_isPiNumber_sigma_compl hM)

/-- `BGsection10.v: Malpha_Hall_G`. -/
theorem Malpha_Hall_G
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G)) :
    IsHall (alphaPrimes M) (alphaCore M) := by
  let A : Subgroup M := (alphaCore M).subgroupOf M
  have hHall : IsHall (alphaPrimes M) A := Malpha_Hall hM
  have hMindex : IsPiNumber (alphaPrimes M)ᶜ M.index := by
    apply (mmax_index_isPiNumber_sigma_compl hM).mono
    intro p hpNotSigma hpAlpha
    exact hpNotSigma (alpha_sub_sigma hM hpAlpha)
  constructor
  · exact alphaCore_isPiNumber M
  · rw [← Subgroup.map_subgroupOf_eq_of_le (alphaCore_le M),
      Subgroup.index_map_subtype]
    exact hHall.isPiNumber_index.mul hMindex

/-- `BGsection10.v: Msigma_der1`. -/
theorem Msigma_der1
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G)) :
    sigmaCore M ≤ (_root_.commutator M).map M.subtype := by
  let S : Subgroup M := (sigmaCore M).subgroupOf M
  have hSder : S ≤ _root_.commutator M :=
    sigma_Hall_sub_der1 hM (Msigma_Hall hM)
  calc
    sigmaCore M = S.map M.subtype :=
      (Subgroup.map_subgroupOf_eq_of_le (sigmaCore_le M)).symm
    _ ≤ (_root_.commutator M).map M.subtype :=
      Subgroup.map_mono hSder

/-- `BGsection10.v: Malpha_quo_rank2`.

The statement deliberately quantifies over every elementary-abelian
rank-three subgroup of the full quotient, not only over its Fitting
subgroup. -/
theorem Malpha_quo_rank2
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G)) :
    ∀ p : ℕ, p.Prime →
      ¬ ∃ E : Subgroup (M ⧸ (alphaCore M).subgroupOf M),
        IsElementaryAbelianOfRank p 3 E := by
  classical
  let A : Subgroup M := (alphaCore M).subgroupOf M
  have hAnormal : A.Normal := by
    simpa [A] using alphaCore_normal M
  letI : A.Normal := hAnormal
  have hHall : IsHall (alphaPrimes M) A := by
    simpa [A] using Malpha_Hall hM
  intro p hp
  rintro ⟨E, hE⟩
  have hpE : p ∣ Nat.card E := by
    rw [hE.card_eq]
    exact dvd_pow_self p (by omega)
  have hpQ : p ∣ Nat.card (M ⧸ A) :=
    hpE.trans (E : Subgroup (M ⧸ A)).card_subgroup_dvd_card
  have hpIndex : p ∣ A.index := by
    simpa only [A.index_eq_card] using hpQ
  have hpNot : p ∉ alphaPrimes M := by
    intro hpAlpha
    exact hHall.isPiNumber_index hp hpIndex hpAlpha
  obtain ⟨C, hC⟩ := exists_elementaryAbelian_lift
    (K := M) (N := A) hAnormal hHall.isPiNumber_card hp hpNot hE
  apply hpNot
  exact ⟨hp, C.map M.subtype, Subgroup.map_subtype_le C,
    hC.map_of_injective M.subtype M.subtype_injective⟩

/-- `BGsection10.v: Malpha_quo_nil`. -/
theorem Malpha_quo_nil
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G)) :
    Group.IsNilpotent
      (_root_.commutator (M ⧸ (alphaCore M).subgroupOf M)) := by
  let A : Subgroup M := (alphaCore M).subgroupOf M
  have hAnormal : A.Normal := by
    simpa [A] using alphaCore_normal M
  letI : A.Normal := hAnormal
  let Q := M ⧸ A
  let F : Subgroup Q := fittingCore Q
  have hderF : _root_.commutator Q ≤ F := by
    simpa [A, Q, F] using Malpha_quo_sub_Fitting hM
  letI : Group.IsNilpotent F := by
    dsimp [F]
    infer_instance
  simpa [A, Q] using
    Group.nilpotent_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hderF)

/-- `BGsection10.v: Msigma_neq1`. -/
theorem Msigma_neq1
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G)) :
    sigmaCore M ≠ ⊥ := by
  classical
  intro hSigmaBot
  have hAlphaBot : alphaCore M = ⊥ := by
    apply le_bot_iff.mp
    rw [← hSigmaBot]
    exact alphaCore_le_sigmaCore hM
  have hAlphaSubBot : (alphaCore M).subgroupOf M = ⊥ := by
    simp [hAlphaBot]
  have hRankCore : ∀ p : ℕ, p.Prime →
      ¬ ∃ E : Subgroup (fittingCore M),
        IsElementaryAbelianOfRank p 3 E := by
    intro p hp
    rintro ⟨E, hE⟩
    have hNoQuot := Malpha_quo_rank2 hM p hp
    let A : Subgroup M := (alphaCore M).subgroupOf M
    let q := QuotientGroup.mk' A
    have hqinj : Function.Injective q := by
      rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk']
      exact hAlphaSubBot
    let EM : Subgroup M := E.map (fittingCore M).subtype
    let Ebar : Subgroup (M ⧸ A) := EM.map q
    have hEM : IsElementaryAbelianOfRank p 3 EM := by
      dsimp [EM]
      exact hE.map_of_injective (fittingCore M).subtype
        (fittingCore M).subtype_injective
    have hEbar : IsElementaryAbelianOfRank p 3 Ebar := by
      dsimp [Ebar]
      exact hEM.map_of_injective q hqinj
    exact hNoQuot ⟨Ebar, hEbar⟩
  have hMcard : 1 < Nat.card M :=
    M.one_lt_card_iff_ne_bot.mpr (mmax_neq1 hM)
  obtain ⟨q, hq, hqM, hqmax⟩ :=
    exists_maximal_prime_divisor hMcard
  letI : Fact q.Prime := ⟨hq⟩
  have hIndex : ¬ q ∣ (pCore q M).index :=
    rank2_max_pcore_Sylow hqmax (mFT_odd M) (mmax_sol hM)
      hRankCore
  let P : Sylow q M := pCore_isPGroup.toSylow hIndex
  have hPne : (P : Subgroup M) ≠ ⊥ :=
    P.ne_bot_of_dvd_card hqM
  have hPnormal : (P : Subgroup M).Normal := by
    change (pCore q M).Normal
    infer_instance
  let PG : Subgroup G := ambientSylow M P
  have hPGM : PG ≤ M := by
    dsimp [PG, ambientSylow]
    exact Subgroup.map_subtype_le _
  have hPGnormal : (PG.subgroupOf M).Normal := by
    change ((((P : Subgroup M).map M.subtype).comap M.subtype)).Normal
    rw [Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
    exact hPnormal
  have hPGne : PG ≠ ⊥ := by
    intro hPGbot
    apply hPne
    exact (Subgroup.map_eq_bot_iff_of_injective
      (P : Subgroup M) M.subtype_injective).mp hPGbot
  have hNormPG : Subgroup.normalizer (PG : Set G) = M :=
    mmax_normal hM hPGM hPGnormal hPGne
  have hqSigma : q ∈ sigmaPrimes M := by
    refine ⟨hq, P, ?_⟩
    simpa [PG] using (show Subgroup.normalizer (PG : Set G) ≤ M by
      rw [hNormPG])
  have hPpi : IsPiNumber (sigmaPrimes M) (Nat.card P) :=
    P.isPGroup'.isPiNumber_natCard hqSigma
  have hPcore : (P : Subgroup M) ≤ piCore (sigmaPrimes M) M :=
    le_piCore hPnormal hPpi
  have hPsub : (P : Subgroup M) ≤ (sigmaCore M).subgroupOf M := by
    simpa [sigmaCore] using (show
      (P : Subgroup M) ≤
        (primeSetCore (sigmaPrimes M) M).subgroupOf M from by
          rw [primeSetCore_subgroupOf_eq_piCore]
          exact hPcore)
  apply hPne
  apply le_bot_iff.mp
  simpa [hSigmaBot] using hPsub

end

end Submission.OddOrder.BG.Section10
