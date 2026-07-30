import Submission.OddOrder.BG.Section05.OmegaUpperCentralCentralizer
import Submission.OddOrder.MathlibSupport.Section05RankTwoAction

/-!
The rank-two conclusion for `W = Ω₁(Z₂(G))` in
Bender--Glauberman Lemma 5.2.
-/

namespace Submission.OddOrder.BG.Section05

open Submission.OddOrder.MathlibSupport
open scoped IsMulCommutative

universe u

variable {G : Type u} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]

/-- Under the hypotheses of Lemma 5.2, `W = Ω₁(Z₂(G))` is elementary
abelian of rank two.  The proof is the faithful-action-on-`E` paragraph of
the Coq proof, with kernel `C_W(E) = Z`. -/
theorem omegaOneUpperCentralTwo_isElementaryAbelianOfRank_two
    (hG : IsPGroup p G) (hodd : Odd (Nat.card G))
    (hRank3 : ∃ A : Subgroup G, IsElementaryAbelianOfRank p 3 A)
    {E : Subgroup G} (hE : IsElementaryAbelianOfRank p 2 E)
    (hmax : IsPMaxElem p (⊤ : Subgroup G) E) :
    IsElementaryAbelianOfRank p 2 (omegaOneUpperCentralTwo p G) := by
  let Z : Subgroup G := omegaOneCenter p G
  let W : Subgroup G := omegaOneUpperCentralTwo p G
  let C : Subgroup G := centralizerWithin W E
  have hnorm : W ≤ Subgroup.normalizer (E : Set G) :=
    omegaOneUpperCentralTwo_le_normalizer_of_rank_three_pmaxElem
      hG hodd hRank3 hmax
  let normalizerHom : W →* Subgroup.normalizer (E : Set G) :=
    W.subtype.codRestrict (Subgroup.normalizer (E : Set G)) fun w ↦
      hnorm w.2
  let rho : W →* MulAut E := E.normalizerMonoidHom.comp normalizerHom
  let H : Subgroup W := C.subgroupOf W
  have hker : rho.ker = H := by
    ext w
    change rho w = 1 ↔ (w : G) ∈ C
    change normalizerHom w ∈ E.normalizerMonoidHom.ker ↔
      (w : G) ∈ W ∧ (w : G) ∈ Subgroup.centralizer (E : Set G)
    simp only [w.property, true_and]
    rw [Subgroup.normalizerMonoidHom_ker]
    rfl
  have hCeq : C = Z :=
    centralizerWithin_omegaOneUpperCentralTwo_eq_omegaOneCenter
      hG hodd hRank3 hE hmax
  have hZcard : Nat.card Z = p :=
    omegaOneCenter_card_eq_prime_of_rank_three_pmaxElem hG hRank3 hE hmax
  have hkerCard : Nat.card rho.ker = p := by
    rw [hker]
    calc
      Nat.card H = Nat.card C :=
        natCard_subgroupOf_eq (centralizerWithin_le_left W E)
      _ = Nat.card Z := by rw [hCeq]
      _ = p := hZcard
  have hQcard : Nat.card (W ⧸ rho.ker) ≤ p :=
    section05_natCard_quotient_ker_mulAut_le_prime
      (hG.to_subgroup W) hE rho
  have hWcardLe : Nat.card W ≤ p ^ 2 := by
    calc
      Nat.card W = Nat.card (W ⧸ rho.ker) * Nat.card rho.ker :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup rho.ker
      _ = Nat.card (W ⧸ rho.ker) * p := by rw [hkerCard]
      _ ≤ p * p := Nat.mul_le_mul_right p hQcard
      _ = p ^ 2 := by ring
  have hWnoncyclic : ¬ IsCyclic W :=
    (omegaOneUpperCentralTwo_structure hG hodd hRank3).1
  obtain ⟨n, hWcard⟩ := (hG.to_subgroup W).exists_card_eq
  have hnle : n ≤ 2 := by
    apply (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp
    rw [← hWcard]
    exact hWcardLe
  have hnnotle : ¬ n ≤ 1 := by
    intro hn
    have hWcardDvd : Nat.card W ∣ p := by
      rw [hWcard]
      interval_cases n <;> simp
    letI : IsCyclic W := isCyclic_of_card_dvd_prime hWcardDvd
    exact hWnoncyclic inferInstance
  have hn : n = 2 := by omega
  have hWcardEq : Nat.card W = p ^ 2 := by rw [hWcard, hn]
  have hWcomm : IsMulCommutative W :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq hWcardEq
  have hWpow : ∀ w : W, w ^ p = 1 :=
    (omegaOneUpperCentralTwo_structure hG hodd hRank3).2
  exact
    { isPGroup := hG.to_subgroup W
      commutative := hWcomm
      pow_eq_one := hWpow
      card_eq := hWcardEq }

end Submission.OddOrder.BG.Section05
