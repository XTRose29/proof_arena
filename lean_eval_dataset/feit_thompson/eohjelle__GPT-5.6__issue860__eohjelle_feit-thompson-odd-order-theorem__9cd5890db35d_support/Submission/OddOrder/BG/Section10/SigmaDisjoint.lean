import Submission.OddOrder.BG.Section10.AlphaSigmaCore

/-!
# Bender--Glauberman Section 10: disjoint sigma cores

This file ports the nilpotent branch of `BGsection10.v: sigma_disjoint`
(Lemma 10.12(b)).  If the sigma core of one maximal subgroup is nilpotent,
then a nontrivial intersection with the sigma core of another maximal
subgroup forces the two maximal subgroups to be conjugate.
-/

namespace Submission.OddOrder.BG.Section10

open Submission.OddOrder.BG.Section07
open Submission.OddOrder.MathlibSupport
open scoped Pointwise

universe u

noncomputable section

/-- A `pi`-subgroup lies in a normal `pi`-Hall subgroup. -/
private theorem isPiNumber_le_normal_isHall
    {K : Type u} [Group K] [Finite K] {pi : Set ℕ}
    {N L : Subgroup K} (hNnormal : N.Normal)
    (hNHall : IsHall pi N) (hLpi : IsPiNumber pi (Nat.card L)) :
    L ≤ N := by
  letI : N.Normal := hNnormal
  have hcop : (Nat.card L).Coprime N.index := by
    apply Nat.coprime_of_dvd
    intro p hp hpL hpIndex
    have hpPi : p ∈ pi := hLpi hp hpL
    have hpNotPi : p ∈ piᶜ := hNHall.isPiNumber_index hp hpIndex
    exact hpNotPi hpPi
  intro x hxL
  let q : K →* K ⧸ N := QuotientGroup.mk' N
  have horderL : orderOf (q x) ∣ Nat.card L :=
    (orderOf_map_dvd q x).trans (L.orderOf_dvd_natCard hxL)
  have horderIndex : orderOf (q x) ∣ N.index := by
    simpa only [N.index_eq_card] using orderOf_dvd_natCard (q x)
  have horderOne : orderOf (q x) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop horderL horderIndex
  have hqOne : q x = 1 := orderOf_eq_one_iff.mp horderOne
  exact (QuotientGroup.eq_one_iff x).mp (by simpa [q] using hqOne)

/-- `BGsection10.v: sigma_disjoint`, part (b), in subgroup form.

Two nonconjugate maximal subgroups have disjoint sigma cores whenever the
first sigma core is nilpotent.  This is the form used in Section 11.
-/
theorem sigmaCore_inf_sigmaCore_eq_bot_of_nilpotent
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M H : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hH : H ∈ minSimple_max_groups (G := G))
    (hnotconj : ∀ g : G,
      H ≠ M.map (MulAut.conj g).toMonoidHom)
    (hnil : Group.IsNilpotent (sigmaCore M)) :
    sigmaCore M ⊓ sigmaCore H = ⊥ := by
  classical
  by_contra hInt
  have hcard :
      Nat.card (sigmaCore M ⊓ sigmaCore H : Subgroup G) ≠ 1 :=
    fun hcard ↦ hInt (Subgroup.card_eq_one.mp hcard)
  obtain ⟨p, hp, hpInt⟩ := Nat.exists_prime_and_dvd hcard
  letI : Fact p.Prime := ⟨hp⟩
  have hpMcard : p ∣ Nat.card (sigmaCore M) :=
    hpInt.trans (Subgroup.card_dvd_of_le inf_le_left)
  have hpHcard : p ∣ Nat.card (sigmaCore H) :=
    hpInt.trans (Subgroup.card_dvd_of_le inf_le_right)
  have hpM : p ∈ sigmaPrimes M := by
    rw [← pi_Msigma hM]
    exact ⟨hp, hpMcard⟩
  have hpH : p ∈ sigmaPrimes H := by
    rw [← pi_Msigma hH]
    exact ⟨hp, hpHcard⟩

  let P : Sylow p M := Classical.choice Sylow.nonempty
  let C : Subgroup M := (sigmaCore M).subgroupOf M
  have hPpi : IsPiNumber (sigmaPrimes M) (Nat.card P) :=
    P.isPGroup'.isPiNumber_natCard hpM
  have hPC : (P : Subgroup M) ≤ C := by
    apply isPiNumber_le_normal_isHall
      (hNnormal := by simpa [C] using sigmaCore_normal M)
      (hNHall := by simpa [C] using Msigma_Hall hM)
      hPpi
  letI : C.Normal := by
    simpa [C] using sigmaCore_normal M
  letI : Group.IsNilpotent (sigmaCore M) := hnil
  letI : Group.IsNilpotent C := by
    exact Group.nilpotent_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe (sigmaCore_le M)).symm
  let PC : Sylow p C := P.subtype hPC
  have hPCnormal : (PC : Subgroup C).Normal := by infer_instance
  letI : (PC : Subgroup C).Characteristic :=
    PC.characteristic_of_normal hPCnormal
  have hPnormal : (P : Subgroup M).Normal := by
    have hmapNormal :
        ((PC : Subgroup C).map C.subtype).Normal := by infer_instance
    simpa [PC, Sylow.coe_subtype,
      Subgroup.map_subgroupOf_eq_of_le hPC] using hmapNormal

  let PG : Subgroup G := ambientSylow M P
  have hPGM : PG ≤ M := by
    dsimp [PG, ambientSylow]
    exact Subgroup.map_subtype_le _
  have hPGnormal : (PG.subgroupOf M).Normal := by
    change ((((P : Subgroup M).map M.subtype).comap M.subtype)).Normal
    rw [Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
    exact hPnormal
  have hPGne : PG ≠ ⊥ := by
    simpa [PG] using sigma_Sylow_neq_bot hM hpM P
  have hNormPG : Subgroup.normalizer (PG : Set G) = M :=
    mmax_normal hM hPGM hPGnormal hPGne

  obtain ⟨S, hS⟩ := sigma_Sylow_G hM hpM P
  let Q : Sylow p H := Classical.choice Sylow.nonempty
  obtain ⟨T, hT⟩ := sigma_Sylow_G hH hpH Q
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S T
  let e : G ≃* G := MulAut.conj g
  have hST :
      (S : Subgroup G).map e.toMonoidHom = (T : Subgroup G) := by
    change MulAut.conj g • (S : Subgroup G) = (T : Subgroup G)
    rw [← Sylow.coe_subgroup_smul, hg]
  have hPGmap :
      PG.map e.toMonoidHom = ambientSylow H Q := by
    dsimp only [PG]
    rw [← hS, ← hT]
    exact hST
  have hMmapH : M.map e.toMonoidHom ≤ H := by
    calc
      M.map e.toMonoidHom =
          (Subgroup.normalizer (PG : Set G)).map e.toMonoidHom := by
            rw [hNormPG]
      _ = Subgroup.normalizer
          (PG.map e.toMonoidHom : Set G) :=
            Subgroup.map_equiv_normalizer_eq PG e
      _ = Subgroup.normalizer (ambientSylow H Q : Set G) := by
            rw [hPGmap]
      _ ≤ H := norm_sigma_Sylow hpH Q
  have hMmapMax :
      M.map e.toMonoidHom ∈ minSimple_max_groups (G := G) :=
    (mmaxJ M e).mpr hM
  have hEq : M.map e.toMonoidHom = H :=
    eq_mmax hMmapMax hH hMmapH
  exact hnotconj g hEq.symm

end

end Submission.OddOrder.BG.Section10
