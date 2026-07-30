import Submission.OddOrder.BG.Section02.OddGL2NormalizerComplement

/-!
The contradiction furnished by the proper-normalizer branch of
`BGsection2.der1_odd_GL2_charf`.

The transfer kernel contains the ambient commutator because its complementary
Sylow subgroup is commutative.  The Sylow prime therefore cannot divide the
cardinality of the ambient commutator.
-/

namespace Submission.OddOrder.BG.Section02

variable {G : Type*} [Group G]

/-- A normal complement to a Sylow subgroup contains the ambient commutator
when the Sylow subgroup is central in its normalizer. -/
theorem commutator_le_normal_complement_of_normalizer_le_centralizer
    {q : ℕ} [Fact q.Prime] (Q : Sylow q G) (K : Subgroup G) [K.Normal]
    (hK : K.IsComplement' (Q : Subgroup G))
    (hcent : Subgroup.normalizer (Q : Set G) ≤
      Subgroup.centralizer (Q : Set G)) :
    _root_.commutator G ≤ K := by
  letI : IsMulCommutative Q := ⟨⟨fun a b => by
    apply Subtype.ext
    exact (hcent (Q.le_normalizer a.2) b b.2).symm⟩⟩
  exact Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top
    hK.sup_eq_top inferInstance

/-- The Sylow prime is absent from the ambient commutator once Burnside
transfer has supplied a normal complement. -/
theorem not_dvd_card_commutator_of_normal_complement
    [Finite G] {q : ℕ} [Fact q.Prime]
    (Q : Sylow q G) (K : Subgroup G) [K.Normal]
    (hK : K.IsComplement' (Q : Subgroup G))
    (hcent : Subgroup.normalizer (Q : Set G) ≤
      Subgroup.centralizer (Q : Set G)) :
    ¬q ∣ Nat.card (_root_.commutator G) := by
  intro hq
  apply Q.not_dvd_index
  rw [hK.index_eq_card]
  exact hq.trans (Subgroup.card_dvd_of_le
    (commutator_le_normal_complement_of_normalizer_le_centralizer
      Q K hK hcent))

/-- The proper-normalizer induction output contradicts divisibility of the
ambient commutator by the selected Sylow prime. -/
theorem not_dvd_card_commutator_of_normalizer_commutator_isPGroup
    [Finite G] {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (Q : Sylow q G)
    (hcomm : IsPGroup p (_root_.commutator (Subgroup.normalizer (Q : Set G))))
    (hpq : p ≠ q) :
    ¬q ∣ Nat.card (_root_.commutator G) := by
  let hcent := normalizer_le_centralizer_of_commutator_isPGroup Q hcomm hpq
  let K : Subgroup G := (MonoidHom.transferSylow Q hcent).ker
  have hK : K.IsComplement' (Q : Subgroup G) :=
    MonoidHom.ker_transferSylow_isComplement' Q hcent
  exact not_dvd_card_commutator_of_normal_complement Q K hK hcent

end Submission.OddOrder.BG.Section02
