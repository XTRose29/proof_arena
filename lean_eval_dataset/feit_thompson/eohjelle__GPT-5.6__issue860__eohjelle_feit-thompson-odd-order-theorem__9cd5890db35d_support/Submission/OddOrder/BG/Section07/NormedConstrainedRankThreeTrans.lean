import Submission.OddOrder.BG.Section07.NormedConstrainedMeetTrans
import Submission.OddOrder.MathlibSupport.CoprimeAbelianCentralizerGeneration
import Submission.OddOrder.MathlibSupport.ElementaryAbelian

/-!
# Bender--Glauberman, Section 7: rank-three transitivity

This file ports Bender--Glauberman Theorem 7.2,
`normed_constrained_rank3_trans`.  A rank-three elementary-abelian subgroup
of the center of `A` forces the prime-complement core of `C_G(A)` to act
transitively on the maximal `q`-subgroups normalized by `A`.
-/

namespace Submission.OddOrder.BG.Section07

open Submission.OddOrder.MathlibSupport
open scoped IsMulCommutative

universe u

variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
private theorem isMulCommutative_of_le
    {B C : Subgroup G} (hB : IsMulCommutative B) (hCB : C ≤ B) :
    IsMulCommutative C := by
  letI : IsMulCommutative B := hB
  apply isMulCommutative_iff.mpr
  intro x y
  apply Subtype.ext
  change (x : G) * (y : G) = (y : G) * (x : G)
  exact congrArg Subtype.val
    (mul_comm (⟨x, hCB x.2⟩ : B) (⟨y, hCB y.2⟩ : B))

/-- A cocyclic subgroup of an elementary-abelian group of rank three
cannot itself be cyclic. -/
private theorem not_isCyclic_of_rank_three_of_isCyclic_quotient
    {p : ℕ} (hp : p.Prime) {B C : Subgroup G}
    (hB : IsElementaryAbelianOfRank p 3 B) (hCB : C ≤ B)
    (hCnormal : (C.subgroupOf B).Normal)
    (hquotCyclic : IsCyclic (B ⧸ C.subgroupOf B)) :
    ¬ IsCyclic C := by
  classical
  intro hCcyclic
  letI : Fact p.Prime := ⟨hp⟩
  letI : IsCyclic C := hCcyclic
  letI : (C.subgroupOf B).Normal := hCnormal
  letI : IsCyclic (B ⧸ C.subgroupOf B) := hquotCyclic
  have hCpow : ∀ x : C, x ^ p = 1 := by
    intro x
    apply Subtype.ext
    change (x : G) ^ p = 1
    exact congrArg Subtype.val (hB.pow_eq_one (⟨x, hCB x.2⟩ : B))
  have hquotPow : ∀ x : B ⧸ C.subgroupOf B, x ^ p = 1 := by
    intro x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (C.subgroupOf B) x
    rw [← map_pow, hB.pow_eq_one, map_one]
  letI := Fintype.ofFinite C
  letI := Fintype.ofFinite (B ⧸ C.subgroupOf B)
  have hCcard : Nat.card C ≤ p := by
    rw [Nat.card_eq_fintype_card]
    simpa only [hCpow, Finset.filter_true, Finset.card_univ] using
      (IsCyclic.card_pow_eq_one_le (α := C) hp.pos)
  have hquotCard : Nat.card (B ⧸ C.subgroupOf B) ≤ p := by
    rw [Nat.card_eq_fintype_card]
    simpa only [hquotPow, Finset.filter_true, Finset.card_univ] using
      (IsCyclic.card_pow_eq_one_le
        (α := B ⧸ C.subgroupOf B) hp.pos)
  have hfactor : Nat.card B =
      Nat.card (B ⧸ C.subgroupOf B) * Nat.card C := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup,
      natCard_subgroupOf_eq hCB]
  have hle : p ^ 3 ≤ p ^ 2 := by
    rw [← hB.card_eq, hfactor, pow_two]
    exact Nat.mul_le_mul hquotCard hCcard
  have hlt : p ^ 2 < p ^ 3 :=
    Nat.pow_lt_pow_right hp.one_lt (by omega)
  exact (not_lt_of_ge hle) hlt

omit [Finite G] in
private theorem ne_bot_of_not_isCyclic_of_isCyclic_quotient
    {C D : Subgroup G} (hDC : D ≤ C) (hCnoncyclic : ¬ IsCyclic C)
    (hDnormal : (D.subgroupOf C).Normal)
    (hquotCyclic : IsCyclic (C ⧸ D.subgroupOf C)) : D ≠ ⊥ := by
  letI : (D.subgroupOf C).Normal := hDnormal
  intro hDbot
  subst D
  have hsubBot : (⊥ : Subgroup G).subgroupOf C = (⊥ : Subgroup C) := by
    ext x
    simp
  have hquotBot : IsCyclic (C ⧸ (⊥ : Subgroup C)) :=
    (QuotientGroup.quotientMulEquivOfEq hsubBot).isCyclic.mp hquotCyclic
  apply hCnoncyclic
  exact QuotientGroup.quotientBot.isCyclic.mp hquotBot

/-- Bender--Glauberman Theorem 7.2.  The conclusion is the pairwise form
of transitivity, and the inverse in the conjugating map follows MathComp's
convention `Q :^ k = k⁻¹ Q k`. -/
theorem normed_constrained_rank3_trans [IsMinSimpleOddGroup G]
    {q : ℕ} (A : Subgroup G)
    (cstrA : NormedConstrained A)
    (hqA : q ∉ primeSupport (Nat.card A))
    (hRank3 : ∃ (p : ℕ) (B : Subgroup G),
      p.Prime ∧ B ≤ A ∧ A ≤ Subgroup.centralizer (B : Set G) ∧
        IsElementaryAbelianOfRank p 3 B) :
    ∀ Q₁ Q₂ : Subgroup G,
      Q₁ ∈ max_normed_pgroups (A : Set G) ({q} : Set ℕ) →
      Q₂ ∈ max_normed_pgroups (A : Set G) ({q} : Set ℕ) →
      ∃ k : G, k ∈ centralPrimeComplementCore A ∧
        Q₂ = Q₁.map (MulAut.conj k⁻¹).toMonoidHom := by
  classical
  rintro Q₁ Q₂ hQ₁max hQ₂max
  by_cases hQ₁bot : Q₁ = ⊥
  · have hbotMax : (⊥ : Subgroup G) ∈
        max_normed_pgroups (A : Set G) ({q} : Set ℕ) := by
      simpa [hQ₁bot] using hQ₁max
    have hQ₂bot : Q₂ = ⊥ := by
      have hQ₂mem : Q₂ ∈ ({⊥} : Set (Subgroup G)) := by
        rw [← trivg_max_norm A ({q} : Set ℕ) hbotMax]
        exact hQ₂max
      exact Set.mem_singleton_iff.mp hQ₂mem
    subst Q₁
    subst Q₂
    exact ⟨1, (centralPrimeComplementCore A).one_mem, by simp⟩
  have hQ₂ne : Q₂ ≠ ⊥ := by
    intro hQ₂bot
    have hbotMax : (⊥ : Subgroup G) ∈
        max_normed_pgroups (A : Set G) ({q} : Set ℕ) := by
      simpa [hQ₂bot] using hQ₂max
    have hQ₁mem : Q₁ ∈ ({⊥} : Set (Subgroup G)) := by
      rw [← trivg_max_norm A ({q} : Set ℕ) hbotMax]
      exact hQ₁max
    exact hQ₁bot (Set.mem_singleton_iff.mp hQ₁mem)
  have hQ₁data := mem_max_normed hQ₁max
  have hQ₂data := mem_max_normed hQ₂max
  letI : Fact q.Prime :=
    ⟨prime_of_isPiNumber_singleton_of_ne_bot hQ₁data.1 hQ₁bot⟩
  have hQ₁p : IsPGroup q Q₁ :=
    isPGroup_of_isPiNumber_singleton hQ₁data.1
  have hQ₂p : IsPGroup q Q₂ :=
    isPGroup_of_isPiNumber_singleton hQ₂data.1
  obtain ⟨p, B, hp, hBA, hABcentral, hB⟩ := hRank3
  letI : Fact p.Prime := ⟨hp⟩
  have hBQ₁ : B ≤ Subgroup.normalizer (Q₁ : Set G) :=
    hBA.trans hQ₁data.2
  obtain ⟨C, hCB, hCnormal, hBCcyclic, hQ₁Cne⟩ :=
    exists_normal_cocyclic_centralizerWithin_ne_bot_of_isPGroup
      B Q₁ hB.commutative hBQ₁ hQ₁p hQ₁bot
  have hCnoncyclic : ¬ IsCyclic C :=
    not_isCyclic_of_rank_three_of_isCyclic_quotient hp hB hCB
      hCnormal hBCcyclic
  have hCQ₂ : C ≤ Subgroup.normalizer (Q₂ : Set G) :=
    hCB.trans (hBA.trans hQ₂data.2)
  obtain ⟨D, hDC, hDnormal, hCDcyclic, hQ₂Dne⟩ :=
    exists_normal_cocyclic_centralizerWithin_ne_bot_of_isPGroup
      C Q₂ (isMulCommutative_of_le hB.commutative hCB)
        hCQ₂ hQ₂p hQ₂ne
  have hDne : D ≠ ⊥ :=
    ne_bot_of_not_isCyclic_of_isCyclic_quotient hDC hCnoncyclic
      hDnormal hCDcyclic
  letI : Nontrivial D := D.nontrivial_iff_ne_bot.mpr hDne
  obtain ⟨z : D, hz⟩ := exists_ne (1 : D)
  have hzG : (z : G) ≠ 1 := by
    intro hzOne
    apply hz
    exact Subtype.ext hzOne
  let H : Subgroup G := Subgroup.centralizer ({(z : G)} : Set G)
  have hzC : (z : G) ∈ C := hDC z.2
  have hzB : (z : G) ∈ B := hCB hzC
  have hAH : A ≤ H := by
    intro a ha
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp (hABcentral ha) z hzB).symm
  have hHproper : H < ⊤ := by
    exact mFT_cent1_proper hzG
  have hQ₁Hne : Q₁ ⊓ H ≠ ⊥ := by
    have hle : centralizerWithin Q₁ C ≤ Q₁ ⊓ H := by
      intro x hx
      refine ⟨hx.1, ?_⟩
      change x ∈ Subgroup.centralizer ({(z : G)} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hx.2 z hzC).symm
    intro hbot
    apply hQ₁Cne
    exact eq_bot_iff.mpr (hle.trans (le_of_eq hbot))
  have hQ₂Hne : Q₂ ⊓ H ≠ ⊥ := by
    have hle : centralizerWithin Q₂ D ≤ Q₂ ⊓ H := by
      intro x hx
      refine ⟨hx.1, ?_⟩
      change x ∈ Subgroup.centralizer ({(z : G)} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hx.2 z z.2).symm
    intro hbot
    apply hQ₂Dne
    exact eq_bot_iff.mpr (hle.trans (le_of_eq hbot))
  exact normed_constrained_meet_trans A Q₁ Q₂ H cstrA hqA
    hAH hHproper hQ₁max hQ₂max hQ₁Hne hQ₂Hne

end Submission.OddOrder.BG.Section07
