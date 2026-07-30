import Submission.OddOrder.BG.Section05.OmegaUpperCentralStructure
import Submission.OddOrder.MathlibSupport.PGroupCenter
import Submission.OddOrder.MathlibSupport.PMaxElem
import Submission.OddOrder.MathlibSupport.SubgroupCardinality

/-!
The center-cardinality part of Bender--Glauberman Lemma 5.2.
-/

namespace Submission.OddOrder.BG.Section05

open Submission.OddOrder.MathlibSupport

universe u

variable {G : Type u} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]

omit [Finite G] [Fact p.Prime] in
/-- The omega-one subgroup of the center lies in every maximal
elementary-abelian subgroup. -/
theorem omegaOneCenter_le_of_pmaxElem
    {E : Subgroup G} (hmax : IsPMaxElem p (⊤ : Subgroup G) E) :
    omegaOneCenter p G ≤ E := by
  have hTorsion :
      pTorsionCentralizerWithin p (⊤ : Subgroup G) E = (E : Set G) :=
    isPMaxElem_iff_pTorsionCentralizerWithin.mp hmax
  intro z hz
  have hzCenter : z ∈ Subgroup.center G := omegaOneCenter_le_center p hz
  have hzCentralizer : z ∈ Subgroup.centralizer (E : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact Subgroup.mem_center_iff.mp hzCenter e
  have hzPow : z ^ p = 1 :=
    congrArg Subtype.val (omegaOneCenter_pow_eq_one p ⟨z, hz⟩)
  have hzTorsion :
      z ∈ pTorsionCentralizerWithin p (⊤ : Subgroup G) E :=
    ⟨trivial, hzCentralizer, hzPow⟩
  rw [hTorsion] at hzTorsion
  exact hzTorsion

/-- In the rank-three situation, maximality forces
`| Ω₁(Z(G)) | = p`.  This is the `cardZ` paragraph in
`BGsection5.v:Ohm1_ucn_p2maxElem`. -/
theorem omegaOneCenter_card_eq_prime_of_rank_three_pmaxElem
    (hG : IsPGroup p G)
    (hRank3 : ∃ A : Subgroup G, IsElementaryAbelianOfRank p 3 A)
    {E : Subgroup G} (hE : IsElementaryAbelianOfRank p 2 E)
    (hmax : IsPMaxElem p (⊤ : Subgroup G) E) :
    Nat.card (omegaOneCenter p G) = p := by
  let Z : Subgroup G := omegaOneCenter p G
  have hZE : Z ≤ E := omegaOneCenter_le_of_pmaxElem hmax
  obtain ⟨A, hA⟩ := hRank3
  have hAone : 1 < Nat.card A := by
    rw [hA.card_eq]
    exact one_lt_pow₀ (Fact.out : p.Prime).one_lt (by omega)
  have hGone : 1 < Nat.card G :=
    hAone.trans_le A.card_le_card_group
  letI : Nontrivial G := Finite.one_lt_card_iff_nontrivial.mp hGone
  letI : Nontrivial (Subgroup.center G) := hG.center_nontrivial
  have hCenterP : IsPGroup p (Subgroup.center G) :=
    hG.to_subgroup (Subgroup.center G)
  obtain ⟨m, hm, hCenterCard⟩ :=
    hCenterP.nontrivial_iff_card.mp inferInstance
  have hpCenter : p ∣ Nat.card (Subgroup.center G) := by
    rw [hCenterCard]
    exact dvd_pow_self p hm.ne'
  obtain ⟨z, hzOrder⟩ :=
    exists_prime_orderOf_dvd_card' (G := Subgroup.center G) p hpCenter
  let zG : G := z
  have hzOrderG : orderOf zG = p :=
    (Subgroup.orderOf_coe z).trans hzOrder
  have hzPowG : zG ^ p = 1 :=
    (congrArg (fun n : ℕ ↦ zG ^ n) hzOrderG).symm.trans
      (pow_orderOf_eq_one zG)
  have hzOmega : z ∈ omegaOne p (Subgroup.center G) := by
    apply mem_omegaOne_of_pow_eq_one
    apply Subtype.ext
    exact hzPowG
  have hzZ : zG ∈ Z := ⟨z, hzOmega, rfl⟩
  let zZ : Z := ⟨zG, hzZ⟩
  have hzGne : zG ≠ 1 := by
    intro hz
    apply (Fact.out : p.Prime).ne_one
    rw [← hzOrderG, hz, orderOf_one]
  have hzZne : zZ ≠ 1 := by
    intro hz
    exact hzGne (congrArg Subtype.val hz)
  letI : Nontrivial Z := ⟨⟨zZ, 1, hzZne⟩⟩
  obtain ⟨n, hn, hZcard⟩ :=
    (hG.to_subgroup Z).nontrivial_iff_card.mp inferInstance
  have hnle : n ≤ 2 := by
    apply (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp
    rw [← hZcard, ← hE.card_eq]
    exact Subgroup.card_le_of_le hZE
  have hnne : n ≠ 2 := by
    intro hn2
    have hZEeq : Z = E := by
      apply Subgroup.eq_of_le_of_card_ge hZE
      rw [hZcard, hn2, hE.card_eq]
    have hEcenter : E ≤ Subgroup.center G := by
      rw [← hZEeq]
      exact omegaOneCenter_le_center p
    have hTorsion :
        pTorsionCentralizerWithin p (⊤ : Subgroup G) E = (E : Set G) :=
      isPMaxElem_iff_pTorsionCentralizerWithin.mp hmax
    have hAE : A ≤ E := by
      intro a ha
      have haCentralizer : a ∈ Subgroup.centralizer (E : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro e he
        exact (Subgroup.mem_center_iff.mp (hEcenter he) a).symm
      have haPow : a ^ p = 1 :=
        congrArg Subtype.val (hA.pow_eq_one ⟨a, ha⟩)
      have haTorsion :
          a ∈ pTorsionCentralizerWithin p (⊤ : Subgroup G) E :=
        ⟨trivial, haCentralizer, haPow⟩
      rw [hTorsion] at haTorsion
      exact haTorsion
    have hpows : p ^ 3 ≤ p ^ 2 := by
      rw [← hA.card_eq, ← hE.card_eq]
      exact Subgroup.card_le_of_le hAE
    have : (3 : ℕ) ≤ 2 :=
      (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp hpows
    omega
  have hn1 : n = 1 := by omega
  change Nat.card Z = p
  rw [hZcard, hn1, pow_one]

end Submission.OddOrder.BG.Section05
