import Submission.OddOrder.PF.Section02.DadeSetSignalizer

/-!
# Peterfalvi 2.10.2: adjoining one point to a set signalizer

The signalizer of `insert a B` is the centralizer of `a` inside the
signalizer of `B`.  The reverse inclusion is the normal-Hall argument in the
Coq proof: a nonempty `B` places its set signalizer inside one pointwise
signalizer, hence gives it complementary prime support, while the Dade
semidirect product at `a` makes the signalizer of `a` a normal Hall subgroup
of the corresponding centralizer in `G`.
-/

namespace Submission.OddOrder.PF

open Submission.OddOrder.MathlibSupport

universe u

variable {Γ : Type u} [Group Γ]

private theorem le_normal_isHall_of_isPiNumber
    [Finite Γ]
    {rho : Set ℕ} {C K X : Subgroup Γ}
    (hKnormal : (K.subgroupOf C).Normal)
    (hKHall : IsHall rho (K.subgroupOf C))
    (hXC : X ≤ C) (hXpi : IsPiNumber rho (Nat.card X)) :
    X ≤ K := by
  let KC : Subgroup C := K.subgroupOf C
  letI : KC.Normal := by simpa [KC] using hKnormal
  have hcop : (Nat.card X).Coprime KC.index := by
    apply Nat.coprime_of_dvd
    intro p hp hpX hpIndex
    have hpRho : p ∈ rho := hXpi hp hpX
    have hpNotRho : p ∈ rhoᶜ := hKHall.isPiNumber_index hp hpIndex
    exact hpNotRho hpRho
  intro x hxX
  let xC : C := ⟨x, hXC hxX⟩
  let qC : C →* C ⧸ KC := QuotientGroup.mk' KC
  have horderX : orderOf (qC xC) ∣ Nat.card X := by
    exact (orderOf_map_dvd qC xC).trans (by
      simpa [xC] using X.orderOf_dvd_natCard hxX)
  have horderIndex : orderOf (qC xC) ∣ KC.index := by
    simpa only [KC.index_eq_card] using orderOf_dvd_natCard (qC xC)
  have horderOne : orderOf (qC xC) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop horderX horderIndex
  have hqOne : qC xC = 1 := orderOf_eq_one_iff.mp horderOne
  have hxKC : xC ∈ KC :=
    (QuotientGroup.eq_one_iff xC).mp (by simpa [qC] using hqOne)
  exact hxKC

/-- Peterfalvi 2.10.2: adjoining `a` to a nonempty Dade subset cuts its
set signalizer down to the elements centralizing `a`. -/
theorem Dade_setU1
    [Finite Γ]
    {G L : Subgroup Γ} {A B : Set Γ}
    (ddA : DadeHypothesis G L A)
    (hBA : B ⊆ A) (hB : B.Nonempty)
    {a : Γ} (ha : a ∈ A) :
    Dade_set_signalizer ddA (insert a B) =
      centralizerWithin (Dade_set_signalizer ddA B)
        (Subgroup.zpowers a) := by
  classical
  let pi : Set ℕ := dadePrimeSet L A
  let Ha : Subgroup Γ := DadeSignalizer ddA a
  let HB : Subgroup Γ := Dade_set_signalizer ddA B
  let CG : Subgroup Γ := centralizerWithin G (Subgroup.zpowers a)
  let CL : Subgroup Γ := centralizerWithin L (Subgroup.zpowers a)
  let C : Subgroup Γ := centralizerWithin HB (Subgroup.zpowers a)

  obtain ⟨b, hbB⟩ := hB
  have hbA : b ∈ A := hBA hbB
  have hHBb : HB ≤ DadeSignalizer ddA b := by
    exact iInf_le_of_le ⟨b, hbB⟩ le_rfl
  have hHbG : DadeSignalizer ddA b ≤ G :=
    (Dade_sdprod ddA hbA).1.trans
      (centralizerWithin_le_left G (Subgroup.zpowers b))
  have hHBG : HB ≤ G := hHBb.trans hHbG
  have hCCG : C ≤ CG := by
    intro x hx
    exact ⟨hHBG hx.1, hx.2⟩
  have hCpi : IsPiNumber piᶜ (Nat.card C) := by
    apply (show IsPiNumber piᶜ (Nat.card (DadeSignalizer ddA b)) by
      simpa [pi, DadeSignalizer] using
        piPrimeCore_isPiNumber (dadePrimeSet L A)
          (centralizerWithin G (Subgroup.zpowers b))).of_dvd
    exact Subgroup.card_dvd_of_le
      ((centralizerWithin_le_left HB (Subgroup.zpowers a)).trans hHBb)

  have hsd := Dade_sdprod ddA ha
  have hHaCG : Ha ≤ CG := by simpa [Ha, CG] using hsd.1
  have hCLCG : CL ≤ CG := by simpa [CL, CG] using hsd.2.1
  have hHaNormal : (Ha.subgroupOf CG).Normal := by
    simpa [Ha, CG] using hsd.2.2.1
  have hcomp :
      (Ha.subgroupOf CG).IsComplement' (CL.subgroupOf CG) := by
    simpa [Ha, CL, CG] using hsd.2.2.2
  have hHaSubCard : Nat.card (Ha.subgroupOf CG) = Nat.card Ha :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHaCG).toEquiv
  have hCLSubCard : Nat.card (CL.subgroupOf CG) = Nat.card CL :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCLCG).toEquiv
  have hCLpi : IsPiNumber pi (Nat.card CL) := by
    intro p hp hpCL
    exact ⟨a, ha, hp, hpCL⟩
  have hHaHall : IsHall piᶜ (Ha.subgroupOf CG) := by
    constructor
    · rw [hHaSubCard]
      simpa [pi, Ha, DadeSignalizer] using
        piPrimeCore_isPiNumber (dadePrimeSet L A)
          (centralizerWithin G (Subgroup.zpowers a))
    · rw [hcomp.symm.index_eq_card, hCLSubCard]
      simpa only [compl_compl] using hCLpi
  have hCHa : C ≤ Ha :=
    le_normal_isHall_of_isPiNumber hHaNormal hHaHall hCCG hCpi

  apply le_antisymm
  · intro x hx
    change x ∈ ⨅ c : (insert a B : Set Γ), DadeSignalizer ddA c at hx
    have hxHa : x ∈ Ha := by
      exact (Subgroup.mem_iInf.mp hx) ⟨a, Set.mem_insert a B⟩
    have hxHB : x ∈ HB := by
      change x ∈ ⨅ c : B, DadeSignalizer ddA c
      rw [Subgroup.mem_iInf]
      intro c
      exact (Subgroup.mem_iInf.mp hx)
        ⟨c, Set.mem_insert_of_mem a c.property⟩
    exact ⟨hxHB, Dade_signalizer_cent ddA a hxHa⟩
  · intro x hx
    change x ∈ C at hx
    have hxHB : x ∈ HB := hx.1
    change x ∈ ⨅ c : B, DadeSignalizer ddA c at hxHB
    change x ∈ ⨅ c : (insert a B : Set Γ), DadeSignalizer ddA c
    rw [Subgroup.mem_iInf]
    rintro ⟨c, hc⟩
    rcases hc with rfl | hcB
    · exact hCHa hx
    · exact (Subgroup.mem_iInf.mp hxHB) ⟨c, hcB⟩

end Submission.OddOrder.PF
