import Submission.OddOrder.BG.Section14.PartitionAndSignalizers
import Submission.OddOrder.MathlibSupport.AmbientFitting
import Submission.OddOrder.MathlibSupport.NilpotentPrimeCores
import Submission.OddOrder.MathlibSupport.PCoreFunctorial
import Submission.OddOrder.MathlibSupport.PrimeOrderInvariantSylow
import Submission.OddOrder.MathlibSupport.SolvableHallContainment

/-!
# Bender--Glauberman Section 15: the Fitting core

This file ports `BGsection15.v`, lines 37--206, from `Fitting_core` through
`Fcore_eq_Msigma`.  The source Fitting core is not the ordinary Fitting
subgroup: it is the join of those Sylow subgroups which are normal in the
ambient subgroup.  We therefore keep it separate from
`MathlibSupport.fittingWithin`.

MathComp represents the Fitting core of an ambient subgroup `M` directly in
the ambient group.  In Lean, `normalSylowCore M` is first constructed inside
the group type `M`, and `Fitting_core M` is its image in the original group.
The source's group-functor structures are represented by explicit mapping
laws (`morphim_Fcore`, `Fcore_igFun`, `Fcore_gFun`, and `Fcore_pgFun`).
-/

namespace Submission.OddOrder.BG.Section15

open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section10
open Submission.OddOrder.MathlibSupport

noncomputable section

universe u v

/-! ## Definition and intrinsic elementary facts -/

/-- A subgroup is one of the normal Sylow factors used in the Fitting core. -/
def IsNormalSylowSubgroup
    {Q : Type u} [Group Q] (P : Subgroup Q) : Prop :=
  P.Normal ∧
    ∃ p : ℕ, p.Prime ∧
      ∃ S : Sylow p Q, (S : Subgroup Q) = P

/-- The intrinsic Fitting core: the join of all normal Sylow subgroups. -/
def normalSylowCore (Q : Type u) [Group Q] : Subgroup Q :=
  sSup {P : Subgroup Q | IsNormalSylowSubgroup P}

/-- `BGsection15.v: Fitting_core`.  The intrinsic normal-Sylow join of `M`,
mapped back into the ambient group. -/
def Fitting_core
    {G : Type u} [Group G] (M : Subgroup G) : Subgroup G :=
  (normalSylowCore M).map M.subtype

/-- Idiomatic alias for the source-facing name `Fitting_core`. -/
abbrev fittingHallCore
    {G : Type u} [Group G] (M : Subgroup G) : Subgroup G :=
  Fitting_core M

instance normalSylowCore_normal
    {Q : Type u} [Group Q] : (normalSylowCore Q).Normal := by
  rw [normalSylowCore]
  apply Subgroup.sSup_normal
  intro P hP
  exact hP.1

/-- Passing to the ambient copy and then restricting back recovers the
intrinsic Fitting core. -/
@[simp]
theorem Fitting_core_subgroupOf_eq
    {G : Type u} [Group G] (M : Subgroup G) :
    (Fitting_core M).subgroupOf M = normalSylowCore M := by
  change ((normalSylowCore M).map M.subtype).comap M.subtype =
    normalSylowCore M
  exact Subgroup.comap_map_eq_self_of_injective M.subtype_injective _

/-- `BGsection15.v: Fcore_normal`. -/
instance Fcore_normal
    {G : Type u} [Group G] (M : Subgroup G) :
    ((Fitting_core M).subgroupOf M).Normal := by
  rw [Fitting_core_subgroupOf_eq]
  infer_instance

/-- `BGsection15.v: Fcore_sub`. -/
theorem Fcore_sub
    {G : Type u} [Group G] (M : Subgroup G) :
    Fitting_core M ≤ M := by
  exact Subgroup.map_subtype_le _

private theorem pCore_eq_sylow_of_normal
    {Q : Type u} [Group Q] {p : ℕ} [Fact p.Prime]
    (P : Sylow p Q) (hP : (P : Subgroup Q).Normal) :
    pCore p Q = (P : Subgroup Q) := by
  exact le_antisymm (pCore_le_sylow P)
    (le_pCore P.isPGroup' hP)

/-- Every normal Sylow factor lies in the ordinary Fitting subgroup. -/
theorem normalSylowCore_le_fittingCore
    {Q : Type u} [Group Q] :
    normalSylowCore Q ≤ fittingCore Q := by
  rw [normalSylowCore]
  apply sSup_le
  intro P hP
  rcases hP.2 with ⟨p, hp, S, hSP⟩
  letI : Fact p.Prime := ⟨hp⟩
  have hSnormal : (S : Subgroup Q).Normal := by
    simpa only [hSP] using hP.1
  calc
    P = (S : Subgroup Q) := hSP.symm
    _ = pCore p Q := (pCore_eq_sylow_of_normal S hSnormal).symm
    _ ≤ fittingCore Q := pCore_le_fittingCore p

/-- `BGsection15.v: Fcore_sub_Fitting`. -/
theorem Fcore_sub_Fitting
    {G : Type u} [Group G] (M : Subgroup G) :
    Fitting_core M ≤ fittingWithin M := by
  exact Subgroup.map_mono normalSylowCore_le_fittingCore

/-- `BGsection15.v: Fcore_nil`. -/
instance Fcore_nil
    {G : Type u} [Group G] [Finite G] (M : Subgroup G) :
    Group.IsNilpotent (Fitting_core M) := by
  let C : Subgroup (fittingWithin M) :=
    (Fitting_core M).subgroupOf (fittingWithin M)
  letI : Group.IsNilpotent (fittingWithin M) :=
    fittingWithin_isNilpotent M
  letI : Group.IsNilpotent C := by infer_instance
  exact Group.nilpotent_of_mulEquiv
    (Subgroup.subgroupOfEquivOfLe (Fcore_sub_Fitting M))

/-! ## Maximality among normal nilpotent Hall subgroups -/

/-- A Sylow subgroup of a Hall subgroup maps to a Sylow subgroup of the
ambient finite group. -/
private theorem exists_sylow_eq_map_of_sylow_hall
    {Q : Type u} [Group Q] [Finite Q]
    {pi : Set ℕ} {p : ℕ} (hp : p.Prime)
    {H : Subgroup Q} (hH : IsHall pi H) (hpPi : p ∈ pi)
    (P : Sylow p H) :
    ∃ S : Sylow p Q,
      (S : Subgroup Q) = (P : Subgroup H).map H.subtype := by
  letI : Fact p.Prime := ⟨hp⟩
  let R : Subgroup Q := (P : Subgroup H).map H.subtype
  have hRp : IsPGroup p R := P.isPGroup'.map H.subtype
  have hpHindex : ¬ p ∣ H.index := by
    intro hpIndex
    exact hH.isPiNumber_index hp hpIndex hpPi
  have hpRindex : ¬ p ∣ R.index := by
    dsimp only [R]
    rw [Subgroup.index_map_subtype]
    exact hp.not_dvd_mul P.not_dvd_index hpHindex
  exact ⟨hRp.toSylow hpRindex, rfl⟩

/-- `BGsection15.v: Fcore_max`.  A normal nilpotent Hall subgroup is
contained in the normal-Sylow join. -/
theorem Fcore_max
    {G : Type u} [Group G] [Finite G]
    {M H : Subgroup G} {pi : Set ℕ}
    (hHall : IsHall pi (H.subgroupOf M))
    (hHM : H ≤ M)
    (hHnormal : (H.subgroupOf M).Normal)
    (hHnil : Group.IsNilpotent H) :
    H ≤ Fitting_core M := by
  let A : Subgroup M := H.subgroupOf M
  let eA : A ≃* H := Subgroup.subgroupOfEquivOfLe hHM
  letI : A.Normal := hHnormal
  letI : Group.IsNilpotent H := hHnil
  letI : Group.IsNilpotent A :=
    Group.nilpotent_of_mulEquiv eA.symm
  have hAcore : A ≤ normalSylowCore M := by
    calc
      A = (sylowSup A).map A.subtype := by
        rw [sylowSup_eq_top]
        exact A.range_subtype.symm.trans
          (MonoidHom.range_eq_map A.subtype)
      _ = ⨆ p : {p : ℕ // p.Prime},
          ((Classical.choice
            (Sylow.nonempty (p := (p : ℕ)) (G := A)) : Sylow p A) :
            Subgroup A).map A.subtype := by
        rw [sylowSup, Subgroup.map_iSup]
      _ ≤ normalSylowCore M := by
        apply iSup_le
        intro p
        letI : Fact (p : ℕ).Prime := ⟨p.property⟩
        let P : Sylow (p : ℕ) A := Classical.choice Sylow.nonempty
        by_cases hPbot : (P : Subgroup A) = ⊥
        · simp [P, hPbot]
        have hpP : (p : ℕ) ∣ Nat.card P :=
          P.isPGroup'.card_eq_or_dvd.resolve_left
            (fun hcard ↦ hPbot (Subgroup.card_eq_one.mp hcard))
        have hpPi : (p : ℕ) ∈ pi :=
          hHall.isPiNumber_card p.property
            (hpP.trans (P : Subgroup A).card_subgroup_dvd_card)
        obtain ⟨S, hS⟩ :=
          exists_sylow_eq_map_of_sylow_hall
            p.property hHall hpPi P
        have hPnormal : (P : Subgroup A).Normal := by infer_instance
        letI : (P : Subgroup A).Characteristic :=
          P.characteristic_of_normal hPnormal
        have hPimageNormal :
            ((P : Subgroup A).map A.subtype).Normal := by
          infer_instance
        rw [normalSylowCore]
        exact le_sSup
          ⟨hPimageNormal, (p : ℕ), p.property, S, hS⟩
  calc
    H = A.map M.subtype :=
      (Subgroup.map_subgroupOf_eq_of_le hHM).symm
    _ ≤ (normalSylowCore M).map M.subtype :=
      Subgroup.map_mono hAcore
    _ = Fitting_core M := rfl

/-! ## Direct-product support and Hall consequences -/

/-- The primes which genuinely occur in a nontrivial normal Sylow factor. -/
def normalSylowPrimes (Q : Type u) [Group Q] [Finite Q] : Set ℕ :=
  {p | p.Prime ∧ p ∣ Nat.card Q ∧
    ∃ P : Sylow p Q, (P : Subgroup Q).Normal}

/-- The normal-Sylow join only has prime divisors from
`normalSylowPrimes`. -/
theorem normalSylowCore_le_piCore
    {Q : Type u} [Group Q] [Finite Q] :
    normalSylowCore Q ≤ piCore (normalSylowPrimes Q) Q := by
  rw [normalSylowCore]
  apply sSup_le
  intro P hP
  rcases hP.2 with ⟨p, hp, S, hSP⟩
  letI : Fact p.Prime := ⟨hp⟩
  by_cases hPbot : P = ⊥
  · rw [hPbot]
    exact (bot_le : (⊥ : Subgroup Q) ≤
      piCore (normalSylowPrimes Q) Q)
  have hSnormal : (S : Subgroup Q).Normal := by
    simpa only [hSP] using hP.1
  have hSne : (S : Subgroup Q) ≠ ⊥ := by
    intro hSbot
    exact hPbot (hSP.symm.trans hSbot)
  have hpS : p ∣ Nat.card S :=
    S.isPGroup'.card_eq_or_dvd.resolve_left
      (fun hcard ↦ hSne (Subgroup.card_eq_one.mp hcard))
  have hpQ : p ∣ Nat.card Q :=
    hpS.trans (S : Subgroup Q).card_subgroup_dvd_card
  have hpNormal : p ∈ normalSylowPrimes Q :=
    ⟨hp, hpQ, S, hSnormal⟩
  apply le_piCore hP.1
  simpa only [← hSP] using
    S.isPGroup'.isPiNumber_natCard hpNormal

theorem normalSylowCore_isPiNumber
    {Q : Type u} [Group Q] [Finite Q] :
    IsPiNumber (normalSylowPrimes Q)
      (Nat.card (normalSylowCore Q)) := by
  exact (piCore_isPiNumber (G := Q) (normalSylowPrimes Q)).of_dvd
    (Subgroup.card_dvd_of_le normalSylowCore_le_piCore)

/-- The prime support of the core is exactly the set of nontrivial normal
Sylow primes. -/
theorem primeSupport_normalSylowCore
    {Q : Type u} [Group Q] [Finite Q] :
    primeSupport (Nat.card (normalSylowCore Q)) =
      normalSylowPrimes Q := by
  apply Set.Subset.antisymm
  · intro p hp
    exact normalSylowCore_isPiNumber hp.1 hp.2
  · rintro p ⟨hp, hpQ, P, hPnormal⟩
    letI : Fact p.Prime := ⟨hp⟩
    have hPne : (P : Subgroup Q) ≠ ⊥ :=
      P.ne_bot_of_dvd_card hpQ
    have hpP : p ∣ Nat.card P :=
      P.isPGroup'.card_eq_or_dvd.resolve_left
        (fun hcard ↦ hPne (Subgroup.card_eq_one.mp hcard))
    have hPcore : (P : Subgroup Q) ≤ normalSylowCore Q := by
      rw [normalSylowCore]
      exact le_sSup ⟨hPnormal, p, hp, P, rfl⟩
    exact ⟨hp, hpP.trans (Subgroup.card_dvd_of_le hPcore)⟩

/-- `BGsection15.v: Fcore_dprod`.  The source iterated direct product has
the same carrier as the supremum of the normal Sylow factors; in Lean the
carrier equality is expressed as an indexed supremum. -/
theorem Fcore_dprod
    {G : Type u} [Group G] (M : Subgroup G) :
    Fitting_core M =
      ⨆ P : {P : Subgroup M // IsNormalSylowSubgroup P},
        (P : Subgroup M).map M.subtype := by
  rw [Fitting_core, normalSylowCore, sSup_eq_iSup', Subgroup.map_iSup]
  apply le_antisymm
  · apply iSup_le
    intro P
    exact le_iSup
      (fun P : {P : Subgroup M // IsNormalSylowSubgroup P} ↦
        (P : Subgroup M).map M.subtype)
      ⟨P, P.property⟩
  · apply iSup_le
    intro P
    exact le_iSup
      (fun P : {P : Subgroup M // P ∈
          {P : Subgroup M | IsNormalSylowSubgroup P}} ↦
        (P : Subgroup M).map M.subtype)
      ⟨P, P.property⟩

/-- The intrinsic Fitting core is a Hall subgroup for its own prime
support. -/
theorem normalSylowCore_isHall
    {Q : Type u} [Group Q] [Finite Q] :
    IsHall (primeSupport (Nat.card (normalSylowCore Q)))
      (normalSylowCore Q) := by
  constructor
  · exact IsPiNumber.primeSupport_self
  · intro p hp hpIndex hpCore
    have hpNormal : p ∈ normalSylowPrimes Q := by
      rw [← primeSupport_normalSylowCore]
      exact hpCore
    rcases hpNormal with ⟨-, -, P, hPnormal⟩
    letI : Fact p.Prime := ⟨hp⟩
    have hPcore : (P : Subgroup Q) ≤ normalSylowCore Q := by
      rw [normalSylowCore]
      exact le_sSup ⟨hPnormal, p, hp, P, rfl⟩
    exact P.not_dvd_index
      (hpIndex.trans (Subgroup.index_dvd_of_le hPcore))

/-- `BGsection15.v: Fcore_pcore_Sylow`. -/
theorem Fcore_pcore_eq_sylow
    {G : Type u} [Group G] [Finite G]
    (M : Subgroup G) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ primeSupport (Nat.card (Fitting_core M))) :
    ∃ P : Sylow p M, pCore p M = (P : Subgroup M) := by
  have hpCore := hp
  rw [Fitting_core,
    Subgroup.card_map_of_injective M.subtype_injective,
    primeSupport_normalSylowCore] at hpCore
  rcases hpCore with ⟨-, -, P, hPnormal⟩
  exact ⟨P, pCore_eq_sylow_of_normal P hPnormal⟩

/-- `BGsection15.v: Fcore_pcore_Sylow`, in the ambient-subgroup convention
used throughout the Lean port. -/
theorem Fcore_pcore_Sylow
    {G : Type u} [Group G] [Finite G]
    (M : Subgroup G) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ primeSupport (Nat.card (Fitting_core M))) :
    IsSylowSubgroupOf p ((pCore p M).map M.subtype) M := by
  obtain ⟨P, hP⟩ := Fcore_pcore_eq_sylow M hp
  exact ⟨P, by rw [hP]⟩

/-- A convenient adapter used by the later Section 15 structure theorem:
an ambiently represented normal Sylow subgroup belongs to the Fitting core.
The normality argument can be supplied explicitly or inferred. -/
theorem normal_sylow_le_Fcore
    {G : Type u} [Group G] [Finite G]
    {M Q : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hQ : IsSylowSubgroupOf p Q M)
    (hQnormal : (Q.subgroupOf M).Normal := by infer_instance) :
    Q ≤ Fitting_core M := by
  obtain ⟨P, hQP⟩ := hQ
  have hPnormal : (P : Subgroup M).Normal := by
    have h := hQnormal
    rw [hQP] at h
    change
      (((P : Subgroup M).map M.subtype).comap M.subtype).Normal at h
    rwa [Subgroup.comap_map_eq_self_of_injective
      M.subtype_injective] at h
  rw [hQP, Fitting_core]
  apply Subgroup.map_mono
  rw [normalSylowCore]
  exact le_sSup ⟨hPnormal, p, Fact.out, P, rfl⟩

/-- Internal prime-core identity underlying `p_core_Fcore`. -/
theorem map_pCore_normalSylowCore_eq_pCore
    {Q : Type u} [Group Q] [Finite Q]
    {p : ℕ} [Fact p.Prime]
    (hp : p ∈ primeSupport (Nat.card (normalSylowCore Q))) :
    (pCore p (normalSylowCore Q)).map
        (normalSylowCore Q).subtype = pCore p Q := by
  have hpNormal : p ∈ normalSylowPrimes Q := by
    rw [← primeSupport_normalSylowCore]
    exact hp
  rcases hpNormal with ⟨-, -, P, hPnormal⟩
  have hpcore : pCore p Q = (P : Subgroup Q) :=
    pCore_eq_sylow_of_normal P hPnormal
  have hOle : pCore p Q ≤ normalSylowCore Q := by
    rw [hpcore, normalSylowCore]
    exact le_sSup ⟨hPnormal, p, Fact.out, P, rfl⟩
  apply le_antisymm
  · apply le_pCore (pCore_isPGroup.map
      (normalSylowCore Q).subtype)
    infer_instance
  · rw [← Subgroup.map_subgroupOf_eq_of_le hOle]
    apply Subgroup.map_mono
    apply le_pCore
    · exact pCore_isPGroup.of_equiv
        (Subgroup.subgroupOfEquivOfLe hOle).symm
    · infer_instance

private theorem map_pCore_mulEquiv
    {Q : Type u} {R : Type v} [Group Q] [Group R]
    (p : ℕ) [Fact p.Prime] (e : Q ≃* R) :
    (pCore p Q).map e.toMonoidHom = pCore p R := by
  have hker : IsPGroup p e.toMonoidHom.ker := by
    rw [e.toMonoidHom.ker_eq_bot_iff.mpr e.injective]
    exact IsPGroup.of_bot
  exact map_pCore_eq_of_surjective_of_ker_isPGroup
    e.toMonoidHom e.surjective hker

/-- `BGsection15.v: p_core_Fcore`, in ambient-subgroup form. -/
theorem p_core_Fcore
    {G : Type u} [Group G] [Finite G]
    (M : Subgroup G) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ primeSupport (Nat.card (Fitting_core M))) :
    (pCore p (Fitting_core M)).map (Fitting_core M).subtype =
      (pCore p M).map M.subtype := by
  let C : Subgroup M := normalSylowCore M
  let eC : C ≃* Fitting_core M :=
    C.equivMapOfInjective M.subtype M.subtype_injective
  have hpC : p ∈ primeSupport (Nat.card C) := by
    rw [Nat.card_congr eC.toEquiv]
    exact hp
  have hpcore :
      (pCore p C).map C.subtype = pCore p M := by
    simpa only [C] using
      map_pCore_normalSylowCore_eq_pCore hpC
  have heq : (pCore p C).map eC.toMonoidHom =
      pCore p (Fitting_core M) :=
    map_pCore_mulEquiv p eC
  rw [← heq, Subgroup.map_map]
  have hcomp :
      (Fitting_core M).subtype.comp eC.toMonoidHom =
        M.subtype.comp C.subtype := by
    ext x
    rfl
  rw [hcomp, ← Subgroup.map_map, hpcore]

/-- `BGsection15.v: Fcore_Hall`. -/
theorem Fcore_Hall
    {G : Type u} [Group G] [Finite G] (M : Subgroup G) :
    IsHall (primeSupport (Nat.card (Fitting_core M)))
      ((Fitting_core M).subgroupOf M) := by
  have hcard : Nat.card (Fitting_core M) =
      Nat.card (normalSylowCore M) := by
    rw [Fitting_core,
      Subgroup.card_map_of_injective M.subtype_injective]
  simpa only [Fitting_core_subgroupOf_eq, hcard] using
    (normalSylowCore_isHall (Q := M))

private theorem map_piCore_mulEquiv
    {Q : Type u} {R : Type v} [Group Q] [Group R]
    [Finite Q] [Finite R] (pi : Set ℕ) (e : Q ≃* R) :
    (piCore pi Q).map e.toMonoidHom = piCore pi R := by
  apply le_antisymm
  · apply le_piCore
    · exact Subgroup.Normal.map (by infer_instance)
        e.toMonoidHom e.surjective
    · rw [Subgroup.card_map_of_injective e.injective]
      exact piCore_isPiNumber pi
  · rw [← Subgroup.map_le_map_iff_of_injective
      (f := e.symm.toMonoidHom) e.symm.injective]
    have hback :
        (piCore pi R).map e.symm.toMonoidHom ≤ piCore pi Q := by
      apply le_piCore
      · exact Subgroup.Normal.map (by infer_instance)
          e.symm.toMonoidHom e.symm.surjective
      · rw [Subgroup.card_map_of_injective e.symm.injective]
        exact piCore_isPiNumber pi
    simpa [Subgroup.map_map] using hback

/-- Internal prime-set-core identity underlying `pcore_Fcore`. -/
theorem map_piCore_normalSylowCore_eq_piCore
    {Q : Type u} [Group Q] [Finite Q] {pi : Set ℕ}
    (hpi : pi ⊆ primeSupport (Nat.card (normalSylowCore Q))) :
    (piCore pi (normalSylowCore Q)).map
        (normalSylowCore Q).subtype = piCore pi Q := by
  let C : Subgroup Q := normalSylowCore Q
  have hOCpi : IsPiNumber
      (primeSupport (Nat.card C)) (Nat.card (piCore pi Q)) :=
    (piCore_isPiNumber pi).mono hpi
  have hOC : piCore pi Q ≤ C := by
    exact normal_isPiNumber_le_isHall
      (inferInstance : (piCore pi Q).Normal) hOCpi
      (by simpa only [C] using
        (normalSylowCore_isHall (Q := Q)))
  apply le_antisymm
  · apply le_piCore
    · infer_instance
    · rw [Subgroup.card_map_of_injective C.subtype_injective]
      exact piCore_isPiNumber pi
  · rw [← Subgroup.map_subgroupOf_eq_of_le hOC]
    apply Subgroup.map_mono
    apply le_piCore
    · infer_instance
    · rw [Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe hOC).toEquiv]
      exact piCore_isPiNumber pi

/-- `BGsection15.v: pcore_Fcore`, in ambient-subgroup form. -/
theorem pcore_Fcore
    {G : Type u} [Group G] [Finite G]
    (M : Subgroup G) {pi : Set ℕ}
    (hpi : pi ⊆ primeSupport (Nat.card (Fitting_core M))) :
    (piCore pi (Fitting_core M)).map (Fitting_core M).subtype =
      (piCore pi M).map M.subtype := by
  let C : Subgroup M := normalSylowCore M
  let eC : C ≃* Fitting_core M :=
    C.equivMapOfInjective M.subtype M.subtype_injective
  have hcard : Nat.card (Fitting_core M) = Nat.card C := by
    rw [Fitting_core,
      Subgroup.card_map_of_injective M.subtype_injective]
  have hpiC : pi ⊆ primeSupport (Nat.card C) := by
    simpa only [hcard] using hpi
  have hcore :
      (piCore pi C).map C.subtype = piCore pi M := by
    simpa only [C] using
      map_piCore_normalSylowCore_eq_piCore hpiC
  have heq : (piCore pi C).map eC.toMonoidHom =
      piCore pi (Fitting_core M) :=
    map_piCore_mulEquiv pi eC
  rw [← heq, Subgroup.map_map]
  have hcomp :
      (Fitting_core M).subtype.comp eC.toMonoidHom =
        M.subtype.comp C.subtype := by
    ext x
    rfl
  rw [hcomp, ← Subgroup.map_map, hcore]

/-- `BGsection15.v: Fcore_pcore_Hall`. -/
theorem Fcore_pcore_Hall
    {G : Type u} [Group G] [Finite G]
    (M : Subgroup G) {pi : Set ℕ}
    (hpi : pi ⊆ primeSupport (Nat.card (Fitting_core M))) :
    IsHall pi (piCore pi M) := by
  constructor
  · exact piCore_isPiNumber pi
  · intro p hp hpIndex hpPi
    letI : Fact p.Prime := ⟨hp⟩
    have hpF : p ∈ primeSupport (Nat.card (Fitting_core M)) :=
      hpi hpPi
    obtain ⟨P, hP⟩ := Fcore_pcore_eq_sylow M hpF
    have hpCorePi : pCore p M ≤ piCore pi M := by
      apply le_piCore (by infer_instance)
      exact pCore_isPGroup.isPiNumber_natCard hpPi
    have hPpi : (P : Subgroup M) ≤ piCore pi M := by
      rw [← hP]
      exact hpCorePi
    exact P.not_dvd_index
      (hpIndex.trans (Subgroup.index_dvd_of_le hPpi))

/-! ## Functoriality, characteristicity, and isomorphism transport -/

/-- `BGsection15.v: morphim_Fcore`.  A surjective homomorphism maps every
normal Sylow factor to a normal Sylow factor. -/
theorem morphim_Fcore
    {Q : Type u} {R : Type v} [Group Q] [Group R]
    [Finite Q] [Finite R] (f : Q →* R)
    (hf : Function.Surjective f) :
    (normalSylowCore Q).map f ≤ normalSylowCore R := by
  rw [normalSylowCore, Subgroup.map_le_iff_le_comap]
  apply sSup_le
  intro P hP
  rw [← Subgroup.map_le_iff_le_comap]
  rcases hP.2 with ⟨p, hp, S, hSP⟩
  letI : Fact p.Prime := ⟨hp⟩
  let T : Sylow p R := S.mapSurjective hf
  have hT : (T : Subgroup R) = P.map f := by
    dsimp only [T]
    rw [Sylow.coe_mapSurjective, ← hSP]
  have hPmapNormal : (P.map f).Normal :=
    Subgroup.Normal.map hP.1 f hf
  exact le_sSup ⟨hPmapNormal, p, hp, T, hT⟩

/-- Transport of the intrinsic core across a group isomorphism. -/
theorem normalSylowCore_map_mulEquiv
    {Q : Type u} {R : Type v} [Group Q] [Group R]
    [Finite Q] [Finite R] (e : Q ≃* R) :
    (normalSylowCore Q).map e.toMonoidHom = normalSylowCore R := by
  apply le_antisymm
  · exact morphim_Fcore e.toMonoidHom e.surjective
  · have hback := morphim_Fcore e.symm.toMonoidHom e.symm.surjective
    have hmapped := Subgroup.map_mono hback (f := e.toMonoidHom)
    simpa [Subgroup.map_map] using hmapped

/-- The intrinsic normal-Sylow join is characteristic. -/
instance normalSylowCore_characteristic
    {Q : Type u} [Group Q] [Finite Q] :
    (normalSylowCore Q).Characteristic := by
  rw [Subgroup.characteristic_iff_map_eq]
  intro e
  exact normalSylowCore_map_mulEquiv e

/-- The MathComp `igFun` adapter: the functorial mapping law together with
the intrinsic containment in the ambient group. -/
theorem Fcore_igFun
    {Q : Type u} {R : Type v} [Group Q] [Group R]
    [Finite Q] [Finite R] (f : Q →* R)
    (hf : Function.Surjective f) :
    (normalSylowCore Q).map f ≤ normalSylowCore R :=
  morphim_Fcore f hf

/-- The MathComp `gFun` adapter. -/
theorem Fcore_gFun
    {Q : Type u} {R : Type v} [Group Q] [Group R]
    [Finite Q] [Finite R] (f : Q →* R)
    (hf : Function.Surjective f) :
    (normalSylowCore Q).map f ≤ normalSylowCore R :=
  morphim_Fcore f hf

/-- The MathComp `pgFun` adapter. -/
theorem Fcore_pgFun
    {Q : Type u} {R : Type v} [Group Q] [Group R]
    [Finite Q] [Finite R] (f : Q →* R)
    (hf : Function.Surjective f) :
    (normalSylowCore Q).map f ≤ normalSylowCore R :=
  morphim_Fcore f hf

/-- `BGsection15.v: Fcore_char`. -/
instance Fcore_char
    {G : Type u} [Group G] [Finite G] (M : Subgroup G) :
    ((Fitting_core M).subgroupOf M).Characteristic := by
  rw [Fitting_core_subgroupOf_eq]
  infer_instance

/-- Ambient automorphisms transport the Fitting core. -/
theorem Fitting_core_map_mulEquiv
    {G : Type u} [Group G] [Finite G]
    (M : Subgroup G) (e : G ≃* G) :
    Fitting_core (M.map e.toMonoidHom) =
      (Fitting_core M).map e.toMonoidHom := by
  let eM : M ≃* M.map e.toMonoidHom := e.subgroupMap M
  rw [Fitting_core, Fitting_core,
    ← normalSylowCore_map_mulEquiv eM,
    Subgroup.map_map, Subgroup.map_map]
  apply congrArg
    (fun f : M →* G ↦ (normalSylowCore M).map f)
  ext x
  rfl

/-- `BGsection15.v: FcoreJ`, with conjugation represented by `MulAut`. -/
theorem FcoreJ
    {G : Type u} [Group G] [Finite G]
    (M : Subgroup G) (x : G) :
    Fitting_core (M.map (MulAut.conj x).toMonoidHom) =
      (Fitting_core M).map (MulAut.conj x).toMonoidHom :=
  Fitting_core_map_mulEquiv M (MulAut.conj x)

/-- `BGsection15.v: injm_Fcore`, represented by the injective special case
of the isomorphism mapping law. -/
theorem injm_Fcore
    {Q : Type u} {R : Type v} [Group Q] [Group R]
    [Finite Q] [Finite R] (e : Q ≃* R) :
    (normalSylowCore Q).map e.toMonoidHom = normalSylowCore R :=
  normalSylowCore_map_mulEquiv e

/-- The equivalence induced on Fitting cores by a group equivalence. -/
noncomputable def normalSylowCoreEquiv
    {Q : Type u} {R : Type v} [Group Q] [Group R]
    [Finite Q] [Finite R] (e : Q ≃* R) :
    normalSylowCore Q ≃* normalSylowCore R :=
  (e.subgroupMap (normalSylowCore Q)).trans
    (MulEquiv.subgroupCongr (normalSylowCore_map_mulEquiv e))

/-- `BGsection15.v: isom_Fcore`. -/
noncomputable abbrev isom_Fcore
    {Q : Type u} {R : Type v} [Group Q] [Group R]
    [Finite Q] [Finite R] (e : Q ≃* R) :
    normalSylowCore Q ≃* normalSylowCore R :=
  normalSylowCoreEquiv e

/-- `BGsection15.v: isog_Fcore`. -/
theorem isog_Fcore
    {Q : Type u} {R : Type v} [Group Q] [Group R]
    [Finite Q] [Finite R] (h : Nonempty (Q ≃* R)) :
    Nonempty (normalSylowCore Q ≃* normalSylowCore R) :=
  h.map normalSylowCoreEquiv

/-! ## The sigma-core comparison in a minimal simple odd group -/

variable {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]

/-- The ambient prime-set core, restricted to its defining subgroup, is
the ordinary group-level `piCore` of that subgroup.  Section 10 uses the
same adapter privately; it is repeated here because private declarations do
not cross module boundaries. -/
private theorem primeSetCore_subgroupOf_eq_piCore_15
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

/-- `BGsection15.v: Fcore_sub_Msigma`. -/
theorem Fcore_sub_Msigma
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G)) :
    Fitting_core M ≤ sigmaCore M := by
  rw [Fitting_core, Subgroup.map_le_iff_le_comap, normalSylowCore]
  apply sSup_le
  intro P hP
  rcases hP.2 with ⟨p, hp, S, hSP⟩
  letI : Fact p.Prime := ⟨hp⟩
  by_cases hPbot : P = ⊥
  · rw [hPbot]
    exact (bot_le : (⊥ : Subgroup M) ≤
      (sigmaCore M).subgroupOf M)
  have hSnormal : (S : Subgroup M).Normal := by
    simpa only [hSP] using hP.1
  have hSne : (S : Subgroup M) ≠ ⊥ := by
    intro hSbot
    exact hPbot (hSP.symm.trans hSbot)
  let PG : Subgroup G := (S : Subgroup M).map M.subtype
  have hPGM : PG ≤ M := by
    dsimp only [PG]
    exact Subgroup.map_subtype_le _
  have hPGnormal : (PG.subgroupOf M).Normal := by
    dsimp only [PG]
    change
      (((S : Subgroup M).map M.subtype).comap M.subtype).Normal
    rw [Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
    exact hSnormal
  have hPGne : PG ≠ ⊥ := by
    intro hPGbot
    apply hSne
    exact (Subgroup.map_eq_bot_iff_of_injective
      (S : Subgroup M) M.subtype_injective).mp hPGbot
  have hNormPG : Subgroup.normalizer (PG : Set G) = M :=
    mmax_normal hM hPGM hPGnormal hPGne
  have hpSigma : p ∈ sigmaPrimes M := by
    refine ⟨hp, S, ?_⟩
    simpa [PG, ambientSylow] using
      (show Subgroup.normalizer (PG : Set G) ≤ M by
        rw [hNormPG])
  have hSpi : IsPiNumber (sigmaPrimes M) (Nat.card S) :=
    S.isPGroup'.isPiNumber_natCard hpSigma
  have hScore : (S : Subgroup M) ≤ piCore (sigmaPrimes M) M :=
    le_piCore hSnormal hSpi
  have hSigmaCore : (sigmaCore M).subgroupOf M =
      piCore (sigmaPrimes M) M := by
    simpa [sigmaCore] using
      primeSetCore_subgroupOf_eq_piCore_15 (sigmaPrimes M) M
  change P ≤ (sigmaCore M).subgroupOf M
  rw [← hSP, hSigmaCore]
  exact hScore

/-- `BGsection15.v: Fcore_eq_Msigma`. -/
theorem Fcore_eq_Msigma
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G)) :
    Fitting_core M = sigmaCore M ↔
      Group.IsNilpotent (sigmaCore M) := by
  constructor
  · intro hEq
    rw [← hEq]
    infer_instance
  · intro hnil
    apply le_antisymm (Fcore_sub_Msigma hM)
    exact Fcore_max (Msigma_Hall hM) (sigmaCore_le M)
      (sigmaCore_normal M) hnil

end

end Submission.OddOrder.BG.Section15
