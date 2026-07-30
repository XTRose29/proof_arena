import Submission.OddOrder.BG.Section05.OmegaUpperCentralMaximal
import Submission.OddOrder.MathlibSupport.ElementaryAbelianSup
import Mathlib.GroupTheory.Sylow

/-!
The maximal elementary-abelian subgroup `S ⊔ Ω₁(Z(G))` used in the
proof of Bender--Glauberman Theorem 5.3(d).
-/

namespace Submission.OddOrder.BG.Section05

open Submission.OddOrder.MathlibSupport
open scoped IsMulCommutative

universe u

variable {G : Type u} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]

/-- If `S` has order `p` and its ambient centralizer has no
elementary-abelian rank-three subgroup, then `S ⊔ Ω₁(Z(G))` is a maximal
elementary-abelian rank-two subgroup.  This is the `SZ` paragraph in
`BGsection5.v:narrow_cent_dprod`. -/
theorem narrow_prime_sup_omegaOneCenter_pmax
    (hG : IsPGroup p G)
    (hRank3 : ∃ A : Subgroup G, IsElementaryAbelianOfRank p 3 A)
    (hNarrow : IsNarrow p (⊤ : Subgroup G))
    {S : Subgroup G} (hScard : Nat.card S = p)
    (hCentRank : ¬ ∃ F : Subgroup G,
      F ≤ centralizerWithin (⊤ : Subgroup G) S ∧
        IsElementaryAbelianOfRank p 3 F) :
    let Z := omegaOneCenter p G
    let SZ := S ⊔ Z
    Disjoint S Z ∧ IsElementaryAbelianOfRank p 2 SZ ∧
      IsPMaxElem p (⊤ : Subgroup G) SZ := by
  let Z : Subgroup G := omegaOneCenter p G
  let SZ : Subgroup G := S ⊔ Z
  have hRankTop : ∃ A : Subgroup G,
      A ≤ (⊤ : Subgroup G) ∧ IsElementaryAbelianOfRank p 3 A := by
    obtain ⟨A, hA⟩ := hRank3
    exact ⟨A, le_top, hA⟩
  obtain ⟨E, hE, hmaxE⟩ := narrow_pmaxElem hNarrow hRankTop
  have hZcard : Nat.card Z = p :=
    omegaOneCenter_card_eq_prime_of_rank_three_pmaxElem
      hG hRank3 hE hmaxE
  have hSZdis : Disjoint S Z := by
    rw [disjoint_iff]
    by_contra hInfNe
    have hdiv : Nat.card (S ⊓ Z : Subgroup G) ∣ p := by
      rw [← hScard]
      exact Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp hdiv with hcardOne | hcardP
    · apply hInfNe
      exact Subgroup.eq_bot_of_card_eq (S ⊓ Z : Subgroup G) hcardOne
    · have hInfS : S ⊓ Z = S := by
        apply Subgroup.eq_of_le_of_card_ge inf_le_left
        rw [hcardP, hScard]
      have hSZ : S ≤ Z := by
        intro s hs
        have hsInf : s ∈ S ⊓ Z := by rw [hInfS]; exact hs
        exact hsInf.2
      have hCentTop : centralizerWithin (⊤ : Subgroup G) S = ⊤ := by
        apply top_unique
        intro g _
        refine mem_centralizerWithin.mpr ⟨trivial, ?_⟩
        intro s hs
        exact (Subgroup.mem_center_iff.mp
          (omegaOneCenter_le_center p (hSZ hs)) g).symm
      apply hCentRank
      obtain ⟨A, hA⟩ := hRank3
      refine ⟨A, ?_, hA⟩
      rw [hCentTop]
      exact le_top
  have hS : IsElementaryAbelianOfRank p 1 S :=
    isElementaryAbelianOfRank_one_of_card_eq_prime hScard
  have hZ : IsElementaryAbelianOfRank p 1 Z :=
    isElementaryAbelianOfRank_one_of_card_eq_prime hZcard
  have hSZcomm : ∀ s ∈ S, ∀ z ∈ Z, Commute s z := by
    intro s _ z hz
    exact Subgroup.mem_center_iff.mp (omegaOneCenter_le_center p hz) s
  have hSZelem : IsElementaryAbelianOfRank p 2 SZ := by
    simpa [SZ] using
      (isElementaryAbelianOfRank_sup_of_disjoint_of_commute
        hG hS hZ hSZdis hSZcomm)
  have hSZmax : IsPMaxElem p (⊤ : Subgroup G) SZ := by
    refine ⟨⟨le_top, hSZelem.toIsElementaryAbelianGroup⟩, ?_⟩
    intro H hH hSZH
    letI : IsMulCommutative H := hH.2.commutative
    have hSH : S ≤ H := (show S ≤ SZ from le_sup_left).trans hSZH
    have hHCent : H ≤ centralizerWithin (⊤ : Subgroup G) S := by
      intro x hx
      refine mem_centralizerWithin.mpr ⟨trivial, ?_⟩
      intro s hs
      exact congrArg Subtype.val
        (mul_comm (⟨s, hSH hs⟩ : H) ⟨x, hx⟩)
    obtain ⟨n, hHcard⟩ := hH.2.isPGroup.exists_card_eq
    have hnle : n ≤ 2 := by
      by_contra hnnot
      have hnthree : 3 ≤ n := by omega
      have hpThreeLe : p ^ 3 ≤ Nat.card H := by
        rw [hHcard]
        exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos hnthree
      obtain ⟨F, hFH, hFcard⟩ :=
        Sylow.exists_subgroup_le_card_pow_prime_of_le_card
          (Fact.out : p.Prime) hG hpThreeLe
      have hFcomm : IsMulCommutative F := by
        apply isMulCommutative_iff.mpr
        intro x y
        apply Subtype.ext
        change (x : G) * (y : G) = (y : G) * (x : G)
        exact congrArg (fun z : H ↦ (z : G))
          (mul_comm (⟨x, hFH x.2⟩ : H) ⟨y, hFH y.2⟩)
      have hFpow : ∀ x : F, x ^ p = 1 := by
        intro x
        apply Subtype.ext
        change (x : G) ^ p = 1
        exact congrArg (fun z : H ↦ (z : G))
          (hH.2.pow_eq_one ⟨x, hFH x.2⟩)
      apply hCentRank
      exact ⟨F, hFH.trans hHCent,
        { isPGroup := hG.to_subgroup F
          commutative := hFcomm
          pow_eq_one := hFpow
          card_eq := hFcard }⟩
    have hHcardLe : Nat.card H ≤ p ^ 2 := by
      rw [hHcard]
      exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos hnle
    have hSZHcard : Nat.card H ≤ Nat.card SZ := by
      rw [hSZelem.card_eq]
      exact hHcardLe
    exact (Subgroup.eq_of_le_of_card_ge hSZH hSZHcard).symm
  exact ⟨hSZdis, hSZelem, hSZmax⟩

end Submission.OddOrder.BG.Section05
