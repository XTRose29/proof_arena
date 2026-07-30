import Submission.OddOrder.BG.Section04.OddNormalRankTwoExists
import Submission.OddOrder.BG.Section09.CentralizerUniqueMaximal
import Submission.OddOrder.MathlibSupport.ElementaryAbelianCentralizerRank

/-!
# Bender--Glauberman Corollary 9.3

An abelian `p`-subgroup of rank at least three with a unique maximal
overgroup transfers uniqueness to every noncyclic `p`-subgroup whose
centralizer has `p`-rank at least three.
-/

namespace Submission.OddOrder.BG.Section09

open Submission.OddOrder.BG.Section04
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.MathlibSupport
open scoped Pointwise

universe u

private theorem not_isCyclic_of_elementaryAbelian_rank_three
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {E : Subgroup G}
    (hE : IsElementaryAbelianOfRank p 3 E) :
    ¬ IsCyclic E := by
  intro hcyclic
  letI : IsCyclic E := hcyclic
  letI := Fintype.ofFinite E
  classical
  have hle : Nat.card E ≤ p := by
    rw [Nat.card_eq_fintype_card]
    simpa only [hE.pow_eq_one, Finset.filter_true, Finset.card_univ] using
      (IsCyclic.card_pow_eq_one_le (α := E) (Fact.out : p.Prime).pos)
  have hlt : p < p ^ 3 := by
    simpa using
      (Nat.pow_lt_pow_right (Fact.out : p.Prime).one_lt
        (by omega : 1 < 3))
  exact (not_lt_of_ge (hE.card_eq ▸ hle)) hlt

/-- `BGsection9.v: any_cent_rank3_Uniquness`
(Bender--Glauberman Corollary 9.3). -/
theorem any_cent_rank3_Uniqueness
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {p : ℕ} [Fact p.Prime] {A B : Subgroup G}
    (hAcomm : IsMulCommutative A)
    (hAp : IsPGroup p A)
    (hRankA : HasElementaryAbelianRankAtLeast p 3 A)
    (hAuniq : A ∈ minSimple_uniq_max_groups (G := G))
    (hBp : IsPGroup p B)
    (hncycB : ¬ IsCyclic B)
    (hRankCB : HasElementaryAbelianRankAtLeast p 3
      (Subgroup.centralizer (B : Set G))) :
    B ∈ minSimple_uniq_max_groups (G := G) := by
  classical
  rcases hRankCB with ⟨C, hCB, hC⟩
  obtain ⟨P, hCP⟩ := hC.isPGroup.exists_le_sylow
  let PG : Subgroup G := P
  have hCPG : C ≤ PG := hCP
  have hPGp : IsPGroup p PG := P.isPGroup'

  rcases hRankA with ⟨EA, hEAA, hEA⟩
  obtain ⟨Q, hAQ⟩ := hAp.exists_le_sylow
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq G Q P
  let A' : Subgroup G := A.map (MulAut.conj x).toMonoidHom
  let EA' : Subgroup G := EA.map (MulAut.conj x).toMonoidHom
  have hQmap :
      (Q : Subgroup G).map (MulAut.conj x).toMonoidHom = PG := by
    change MulAut.conj x • (Q : Subgroup G) = (P : Subgroup G)
    rw [← Sylow.coe_subgroup_smul, hx]
  have hA'PG : A' ≤ PG := by
    dsimp only [A']
    exact (Subgroup.map_mono hAQ).trans_eq hQmap
  have hEA'A' : EA' ≤ A' := by
    dsimp only [EA', A']
    exact Subgroup.map_mono hEAA
  have hEA' : IsElementaryAbelianOfRank p 3 EA' := by
    dsimp only [EA']
    exact hEA.map_of_injective (MulAut.conj x).toMonoidHom
      (MulAut.conj x).injective
  have hA'comm : IsMulCommutative A' := by
    letI : IsMulCommutative A := hAcomm
    dsimp only [A']
    infer_instance
  have hA'uniq : A' ∈ minSimple_uniq_max_groups (G := G) := by
    dsimp only [A']
    exact (uniq_mmaxJ A (MulAut.conj x)).mpr hAuniq

  have hCnoncyc : ¬ IsCyclic C :=
    not_isCyclic_of_elementaryAbelian_rank_three hC
  have hPGnoncyc : ¬ IsCyclic PG := by
    intro hPGcyc
    letI : IsCyclic PG := hPGcyc
    exact hCnoncyc (Subgroup.isCyclic_of_le hCPG)
  have htopPGnoncyc : ¬ IsCyclic (⊤ : Subgroup PG) := by
    intro htopcyc
    exact hPGnoncyc (Subgroup.topEquiv.isCyclic.mp htopcyc)
  obtain ⟨D₀, _hD₀top, hD₀normal, hD₀⟩ :=
    odd_normal_p2Elem_exists hPGp (mFT_odd PG)
      (⊤ : Subgroup PG) htopPGnoncyc
  let D : Subgroup G := D₀.map PG.subtype
  have hDPG : D ≤ PG := by
    dsimp only [D]
    exact Subgroup.map_subtype_le D₀
  have hDnormal : (D.subgroupOf PG).Normal := by
    change (D.comap PG.subtype).Normal
    dsimp only [D]
    rw [Subgroup.comap_map_eq_self_of_injective PG.subtype_injective]
    exact hD₀normal
  have hD : IsElementaryAbelianOfRank p 2 D := by
    dsimp only [D]
    exact hD₀.map_of_injective PG.subtype PG.subtype_injective

  let CA : Subgroup G := centralizerWithin A' D
  have hRankCA : HasElementaryAbelianRankAtLeast p 2 CA := by
    obtain ⟨F, hF, hFrank⟩ :=
      hasElementaryAbelianRankAtLeast_two_centralizerWithin
        hPGp (hEA'A'.trans hA'PG) hDPG hDnormal hD hEA'
    exact ⟨F, hF.trans (centralizerWithin_mono_left hEA'A'), hFrank⟩
  have hCAcentralA : CA ≤ Subgroup.centralizer (A' : Set G) := by
    dsimp only [CA]
    exact (centralizerWithin_le_left A' D).trans
      (Subgroup.le_centralizer_iff_isMulCommutative.mpr hA'comm)
  have hCAuniq : CA ∈ minSimple_uniq_max_groups (G := G) :=
    cent_uniq_Uniqueness hA'uniq hCAcentralA ⟨p, Fact.out, hRankCA⟩

  have hDcentralCA : D ≤ Subgroup.centralizer (CA : Set G) := by
    apply Subgroup.le_centralizer_iff.mp
    dsimp only [CA, centralizerWithin]
    exact inf_le_right
  have hDuniq : D ∈ minSimple_uniq_max_groups (G := G) :=
    cent_uniq_Uniqueness hCAuniq hDcentralCA
      ⟨p, Fact.out, D, le_rfl, hD⟩

  let CC : Subgroup G := centralizerWithin C D
  obtain ⟨FC, hFCCC, hFC⟩ :=
    hasElementaryAbelianRankAtLeast_two_centralizerWithin
      hPGp hCPG hDPG hDnormal hD hC
  have hRankCC : HasElementaryAbelianRankAtLeast p 2 CC :=
    ⟨FC, hFCCC, hFC⟩
  have hCCcentralD : CC ≤ Subgroup.centralizer (D : Set G) := by
    dsimp only [CC, centralizerWithin]
    exact inf_le_right
  have hCCuniq : CC ∈ minSimple_uniq_max_groups (G := G) :=
    cent_uniq_Uniqueness hDuniq hCCcentralD ⟨p, Fact.out, hRankCC⟩

  have hCCleC : CC ≤ C := by
    dsimp only [CC]
    exact centralizerWithin_le_left C D
  have hCcentralCC : C ≤ Subgroup.centralizer (CC : Set G) :=
    (Subgroup.le_centralizer_iff_isMulCommutative.mpr hC.commutative).trans
      (Subgroup.centralizer_le hCCleC)
  have hRankC2 : HasElementaryAbelianRankAtLeast p 2 C :=
    ⟨FC, hFCCC.trans hCCleC, hFC⟩
  have hCuniq : C ∈ minSimple_uniq_max_groups (G := G) :=
    cent_uniq_Uniqueness hCCuniq hCcentralCC ⟨p, Fact.out, hRankC2⟩

  have htopBnoncyc : ¬ IsCyclic (⊤ : Subgroup B) := by
    intro htopcyc
    exact hncycB (Subgroup.topEquiv.isCyclic.mp htopcyc)
  obtain ⟨EB₀, _hEB₀top, _hEB₀normal, hEB₀⟩ :=
    odd_normal_p2Elem_exists hBp (mFT_odd B)
      (⊤ : Subgroup B) htopBnoncyc
  let EB : Subgroup G := EB₀.map B.subtype
  have hEBB : EB ≤ B := by
    dsimp only [EB]
    exact Subgroup.map_subtype_le EB₀
  have hEB : IsElementaryAbelianOfRank p 2 EB := by
    dsimp only [EB]
    exact hEB₀.map_of_injective B.subtype B.subtype_injective
  have hBcentralC : B ≤ Subgroup.centralizer (C : Set G) :=
    Subgroup.le_centralizer_iff.mp hCB
  exact cent_uniq_Uniqueness hCuniq hBcentralC
    ⟨p, Fact.out, EB, hEBB, hEB⟩

end Submission.OddOrder.BG.Section09
