import Submission.OddOrder.MathlibSupport.CentralCommutatorPowers
import Submission.OddOrder.MathlibSupport.NormalSubgroupPowerSeries
import Submission.OddOrder.MathlibSupport.OmegaOneCyclicMaximal

/-!
Selection of the central order-`p` kernel in Huppert's induction.
-/

namespace Submission.OddOrder.MathlibSupport

universe u

variable {G : Type u} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]

/-- In a noncommutative finite `p`-group one can choose a central normal
subgroup `T` of order `p` inside the derived subgroup.  If the first
`p`-power subgroup of the derived group is nontrivial, `T` can be chosen
inside it.  The final disjunction records exactly the two branches of
`BGsection4.v: p2_Ohm1_metacyclic`. -/
theorem exists_huppert_central_kernel
    (hG : IsPGroup p G) (hnoncommutative : ¬ IsMulCommutative G) :
    ∃ (T : Subgroup G) (_hTnormal : T.Normal),
      Nat.card T = p ∧ T ≤ Subgroup.center G ∧
        T ≤ _root_.commutator G ∧
        (T ≤ (iteratedPowerSubgroup p 1 (_root_.commutator G)).map
            (_root_.commutator G).subtype ∨
          (iteratedPowerSubgroup p 1 (_root_.commutator G)).map
              (_root_.commutator G).subtype = ⊥) := by
  classical
  let D : Subgroup G := _root_.commutator G
  let P : Subgroup G :=
    (iteratedPowerSubgroup p 1 D).map D.subtype
  have hDne : D ≠ ⊥ := by
    intro hDbot
    apply hnoncommutative
    exact (_root_.commutator_eq_bot_iff G).mp (by simpa [D] using hDbot)
  have hPD : P ≤ D := by
    rintro _ ⟨x, _, rfl⟩
    exact x.property
  have hDnormal : D.Normal := by dsimp [D]; infer_instance
  letI : D.Normal := hDnormal
  have hPnormal : P.Normal := by
    dsimp [P]
    infer_instance
  letI : P.Normal := hPnormal
  by_cases hPne : P ≠ ⊥
  · obtain ⟨n, hncard⟩ := (hG.to_subgroup P).exists_card_eq
    have hnpos : 1 ≤ n := by
      by_contra hn
      have hnzero : n = 0 := by omega
      have hPcardOne : Nat.card P = 1 := by simpa [hnzero] using hncard
      exact (P.one_lt_card_iff_ne_bot.mpr hPne).ne' hPcardOne
    obtain ⟨T, hTP, hTnormal, hTcard⟩ :=
      exists_normal_subgroup_card_pow_le hG P hncard hnpos
    have hTcardPrime : Nat.card T = p := by simpa using hTcard
    letI : T.Normal := hTnormal
    have hTcenter : T ≤ Subgroup.center G :=
      normal_le_center_of_card_eq_prime Fact.out hG T hTcardPrime
    exact ⟨T, hTnormal, hTcardPrime, hTcenter, hTP.trans hPD,
      Or.inl hTP⟩
  · have hPbot : P = ⊥ := not_ne_iff.mp hPne
    obtain ⟨n, hncard⟩ := (hG.to_subgroup D).exists_card_eq
    have hnpos : 1 ≤ n := by
      by_contra hn
      have hnzero : n = 0 := by omega
      have hDcardOne : Nat.card D = 1 := by simpa [hnzero] using hncard
      exact (D.one_lt_card_iff_ne_bot.mpr hDne).ne' hDcardOne
    obtain ⟨T, hTD, hTnormal, hTcard⟩ :=
      exists_normal_subgroup_card_pow_le hG D hncard hnpos
    have hTcardPrime : Nat.card T = p := by simpa using hTcard
    letI : T.Normal := hTnormal
    have hTcenter : T ≤ Subgroup.center G :=
      normal_le_center_of_card_eq_prime Fact.out hG T hTcardPrime
    exact ⟨T, hTnormal, hTcardPrime, hTcenter, hTD,
      Or.inr (by simpa [P] using hPbot)⟩

end Submission.OddOrder.MathlibSupport
