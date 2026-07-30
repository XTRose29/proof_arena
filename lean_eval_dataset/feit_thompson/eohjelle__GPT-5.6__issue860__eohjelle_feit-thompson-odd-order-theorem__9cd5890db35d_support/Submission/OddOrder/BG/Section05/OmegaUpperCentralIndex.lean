import Submission.OddOrder.BG.Section05.OmegaUpperCentralRankTwo

/-!
The strict-centralizer and prime-index conclusions of
Bender--Glauberman Lemma 5.2.
-/

namespace Submission.OddOrder.BG.Section05

open Submission.OddOrder.MathlibSupport

universe u

variable {G : Type u} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]

/-- The omega-one subgroup of the center is proper in the omega-one
subgroup of the second upper center. -/
theorem omegaOneCenter_lt_omegaOneUpperCentralTwo
    (hG : IsPGroup p G) (hodd : Odd (Nat.card G))
    (hRank3 : ∃ A : Subgroup G, IsElementaryAbelianOfRank p 3 A)
    {E : Subgroup G} (hE : IsElementaryAbelianOfRank p 2 E)
    (hmax : IsPMaxElem p (⊤ : Subgroup G) E) :
    omegaOneCenter p G < omegaOneUpperCentralTwo p G := by
  apply lt_of_le_of_ne (omegaOneCenter_le_omegaOneUpperCentralTwo p)
  intro hEq
  have hZcard : Nat.card (omegaOneCenter p G) = p :=
    omegaOneCenter_card_eq_prime_of_rank_three_pmaxElem hG hRank3 hE hmax
  have hWcard : Nat.card (omegaOneUpperCentralTwo p G) = p ^ 2 :=
    (omegaOneUpperCentralTwo_isElementaryAbelianOfRank_two
      hG hodd hRank3 hE hmax).card_eq
  have hpows : p = p ^ 2 := by
    calc
      p = Nat.card (omegaOneCenter p G) := hZcard.symm
      _ = Nat.card (omegaOneUpperCentralTwo p G) := by rw [hEq]
      _ = p ^ 2 := hWcard
  have : (1 : ℕ) = 2 :=
    Nat.pow_right_injective (Fact.out : p.Prime).two_le
      (by simpa using hpows)
  omega

/-- The rank-two maximal elementary-abelian subgroup is not contained in
`T = C_G(W)`.  This is the first clause of the Coq conclusion
`~~ (E \subset T)`, using the already known `E ≤ G`. -/
theorem not_le_omegaUpperCentralTwoCentralizer
    (hG : IsPGroup p G) (hodd : Odd (Nat.card G))
    (hRank3 : ∃ A : Subgroup G, IsElementaryAbelianOfRank p 3 A)
    {E : Subgroup G} (hE : IsElementaryAbelianOfRank p 2 E)
    (hmax : IsPMaxElem p (⊤ : Subgroup G) E) :
    ¬ E ≤ omegaUpperCentralTwoCentralizer p G := by
  let Z : Subgroup G := omegaOneCenter p G
  let W : Subgroup G := omegaOneUpperCentralTwo p G
  let T : Subgroup G := omegaUpperCentralTwoCentralizer p G
  have hCeq : centralizerWithin W E = Z :=
    centralizerWithin_omegaOneUpperCentralTwo_eq_omegaOneCenter
      hG hodd hRank3 hE hmax
  have hZWlt : Z < W :=
    omegaOneCenter_lt_omegaOneUpperCentralTwo hG hodd hRank3 hE hmax
  intro hET
  have hWC : W ≤ centralizerWithin W E := by
    intro w hw
    refine mem_centralizerWithin.mpr ⟨hw, ?_⟩
    intro e he
    have heT : e ∈ T := hET he
    exact (Subgroup.mem_centralizer_iff.mp heT w hw).symm
  have hWZ : W ≤ Z := by rw [← hCeq]; exact hWC
  exact (not_le_of_gt hZWlt) hWZ

/-- The centralizer `T = C_G(W)` has index `p`. -/
theorem omegaUpperCentralTwoCentralizer_index_eq_prime
    (hG : IsPGroup p G) (hodd : Odd (Nat.card G))
    (hRank3 : ∃ A : Subgroup G, IsElementaryAbelianOfRank p 3 A)
    {E : Subgroup G} (hE : IsElementaryAbelianOfRank p 2 E)
    (hmax : IsPMaxElem p (⊤ : Subgroup G) E) :
    (omegaUpperCentralTwoCentralizer p G).index = p := by
  let W : Subgroup G := omegaOneUpperCentralTwo p G
  let T : Subgroup G := omegaUpperCentralTwoCentralizer p G
  have hW : IsElementaryAbelianOfRank p 2 W :=
    omegaOneUpperCentralTwo_isElementaryAbelianOfRank_two
      hG hodd hRank3 hE hmax
  have hTnormal : T.Normal := by
    dsimp [T]
    infer_instance
  letI : T.Normal := hTnormal
  have hWnormal : W.Normal := by
    dsimp [W]
    infer_instance
  letI : W.Normal := hWnormal
  let normalizerHom : G →* Subgroup.normalizer (W : Set G) :=
    (MonoidHom.id G).codRestrict (Subgroup.normalizer (W : Set G)) fun g ↦ by
      rw [Subgroup.normalizer_eq_top_iff.mpr hWnormal]
      trivial
  let rho : G →* MulAut W := W.normalizerMonoidHom.comp normalizerHom
  have hker : rho.ker = T := by
    ext g
    change normalizerHom g ∈ W.normalizerMonoidHom.ker ↔ g ∈ T
    rw [Subgroup.normalizerMonoidHom_ker]
    rfl
  have hQcard : Nat.card (G ⧸ rho.ker) ≤ p :=
    section05_natCard_quotient_ker_mulAut_le_prime hG hW rho
  have hindexLe : T.index ≤ p := by
    rw [T.index_eq_card, ← hker]
    exact hQcard
  have hTne : T ≠ ⊤ := by
    intro hTtop
    apply not_le_omegaUpperCentralTwoCentralizer
      hG hodd hRank3 hE hmax
    change E ≤ T
    rw [hTtop]
    exact le_top
  have hindexOneLt : 1 < T.index :=
    Subgroup.one_lt_index_of_ne_top hTne
  obtain ⟨n, hindexPow⟩ := hG.index T
  have hnne : n ≠ 0 := by
    intro hn
    rw [hindexPow, hn, pow_zero] at hindexOneLt
    omega
  have hnpos : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hnne
  have hnle : n ≤ 1 := by
    apply (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp
    rw [← hindexPow, pow_one]
    exact hindexLe
  have hn : n = 1 := by omega
  rw [hindexPow, hn, pow_one]

end Submission.OddOrder.BG.Section05
