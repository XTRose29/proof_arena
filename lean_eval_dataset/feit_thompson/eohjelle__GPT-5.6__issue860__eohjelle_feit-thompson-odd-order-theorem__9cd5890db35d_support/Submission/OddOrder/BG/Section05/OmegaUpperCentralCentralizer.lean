import Submission.OddOrder.BG.Section05.NormalRankTwoSCNRankThree
import Submission.OddOrder.BG.Section05.OmegaCenterMaximal

/-!
The `C_W(E) = Z` kernel calculation in Bender--Glauberman Lemma 5.2.
-/

namespace Submission.OddOrder.BG.Section05

open Submission.OddOrder.MathlibSupport
open scoped IsMulCommutative

universe u

variable {G : Type u} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]

/-- The omega-one subgroup of the second upper center normalizes a maximal
elementary-abelian subgroup in the rank-three situation. -/
theorem omegaOneUpperCentralTwo_le_normalizer_of_rank_three_pmaxElem
    (hG : IsPGroup p G) (hodd : Odd (Nat.card G))
    (hRank3 : ∃ A : Subgroup G, IsElementaryAbelianOfRank p 3 A)
    {E : Subgroup G} (hmax : IsPMaxElem p (⊤ : Subgroup G) E) :
    omegaOneUpperCentralTwo p G ≤ Subgroup.normalizer (E : Set G) := by
  rw [Subgroup.le_normalizer_iff_commutator_le_right]
  exact
    (Subgroup.commutator_mono le_rfl le_top).trans
      ((commutator_omegaOneUpperCentralTwo_le_omegaOneCenter_of_rank_three
        hG hodd hRank3).trans (omegaOneCenter_le_of_pmaxElem hmax))

/-- Under the hypotheses of Lemma 5.2, the elements of `W` centralizing `E`
are exactly `Z`. -/
theorem centralizerWithin_omegaOneUpperCentralTwo_eq_omegaOneCenter
    (hG : IsPGroup p G) (hodd : Odd (Nat.card G))
    (hRank3 : ∃ A : Subgroup G, IsElementaryAbelianOfRank p 3 A)
    {E : Subgroup G} (hE : IsElementaryAbelianOfRank p 2 E)
    (hmax : IsPMaxElem p (⊤ : Subgroup G) E) :
    centralizerWithin (omegaOneUpperCentralTwo p G) E =
      omegaOneCenter p G := by
  let Z : Subgroup G := omegaOneCenter p G
  let W : Subgroup G := omegaOneUpperCentralTwo p G
  let C : Subgroup G := centralizerWithin W E
  have hTorsion :
      pTorsionCentralizerWithin p (⊤ : Subgroup G) E = (E : Set G) :=
    isPMaxElem_iff_pTorsionCentralizerWithin.mp hmax
  have hWpow : ∀ w : W, w ^ p = 1 :=
    (omegaOneUpperCentralTwo_structure hG hodd hRank3).2
  have hZE : Z ≤ E := omegaOneCenter_le_of_pmaxElem hmax
  have hZW : Z ≤ W := omegaOneCenter_le_omegaOneUpperCentralTwo p
  have hCE : C ≤ E := by
    intro c hc
    have hcData := mem_centralizerWithin.mp hc
    have hcPow : c ^ p = 1 :=
      congrArg Subtype.val (hWpow ⟨c, hcData.1⟩)
    have hcTorsion :
        c ∈ pTorsionCentralizerWithin p (⊤ : Subgroup G) E :=
      ⟨trivial, hcData.2, hcPow⟩
    rw [hTorsion] at hcTorsion
    exact hcTorsion
  have hZC : Z ≤ C := by
    intro z hz
    refine mem_centralizerWithin.mpr ⟨hZW hz, ?_⟩
    intro e he
    exact Subgroup.mem_center_iff.mp (omegaOneCenter_le_center p hz) e
  have hCneE : C ≠ E := by
    intro hCEeq
    have hEW : E ≤ W := by
      rw [← hCEeq]
      exact centralizerWithin_le_left W E
    have hWG : ⁅W, (⊤ : Subgroup G)⁆ ≤ Z :=
      commutator_omegaOneUpperCentralTwo_le_omegaOneCenter_of_rank_three
        hG hodd hRank3
    have hEnormal : E.Normal := by
      apply Subgroup.normalizer_eq_top_iff.mp
      apply top_unique
      rw [Subgroup.le_normalizer_iff_commutator_le_right,
        Subgroup.commutator_comm]
      exact (Subgroup.commutator_mono hEW le_rfl).trans (hWG.trans hZE)
    obtain ⟨D, ⟨hDscn, F, hFD, hF⟩, hED⟩ :=
      normal_p2Elem_SCN3 hG hodd hRank3 hE hEnormal
    letI : IsMulCommutative D := hDscn.commutative
    have hFE : F ≤ E := by
      intro f hf
      have hfCentralizer : f ∈ Subgroup.centralizer (E : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro e he
        exact congrArg Subtype.val
          (mul_comm (⟨e, hED he⟩ : D) ⟨f, hFD hf⟩)
      have hfPow : f ^ p = 1 :=
        congrArg Subtype.val (hF.pow_eq_one ⟨f, hf⟩)
      have hfTorsion :
          f ∈ pTorsionCentralizerWithin p (⊤ : Subgroup G) E :=
        ⟨trivial, hfCentralizer, hfPow⟩
      rw [hTorsion] at hfTorsion
      exact hfTorsion
    have hpows : p ^ 3 ≤ p ^ 2 := by
      rw [← hF.card_eq, ← hE.card_eq]
      exact Subgroup.card_le_of_le hFE
    have : (3 : ℕ) ≤ 2 :=
      (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp hpows
    omega
  have hZcard : Nat.card Z = p :=
    omegaOneCenter_card_eq_prime_of_rank_three_pmaxElem hG hRank3 hE hmax
  obtain ⟨n, hCcard⟩ := (hG.to_subgroup C).exists_card_eq
  have hnpos : 1 ≤ n := by
    apply (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp
    rw [← hCcard, pow_one, ← hZcard]
    exact Subgroup.card_le_of_le hZC
  have hnle : n ≤ 2 := by
    apply (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp
    rw [← hCcard, ← hE.card_eq]
    exact Subgroup.card_le_of_le hCE
  have hnne : n ≠ 2 := by
    intro hn2
    apply hCneE
    apply Subgroup.eq_of_le_of_card_ge hCE
    rw [hCcard, hn2, hE.card_eq]
  have hn1 : n = 1 := by omega
  change C = Z
  symm
  apply Subgroup.eq_of_le_of_card_ge hZC
  rw [hCcard, hn1, pow_one, hZcard]

end Submission.OddOrder.BG.Section05
