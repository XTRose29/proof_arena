import Submission.OddOrder.BG.Section03.OddPrimeSemidirectConstituent
import Submission.OddOrder.MathlibSupport.Cardinality
import Submission.OddOrder.MathlibSupport.ComplementQuotient
import Submission.OddOrder.MathlibSupport.FaithfulQuotientRepresentation
import Submission.OddOrder.MathlibSupport.SubgroupCardinality

/-!
Reduction of Bender-Glauberman Theorem 3.4 to a faithful irreducible
representation.
-/

namespace Submission.OddOrder.BG.Section03

open Submission.OddOrder.MathlibSupport

universe u v w

variable {G : Type u} [Group G] [Fintype G]
variable {K R : Subgroup G}
variable {k : Type v} [Field k]
variable {V : Type w} [AddCommGroup V] [Module k V] [Finite V]

noncomputable section

/-- Under global cardinality induction, the perfect prime-complement action
case reduces to faithful irreducible representations of the current group.
The callback states the remaining faithful irreducible contradiction. -/
theorem kernel_le_representation_ker_of_faithful_irreducible_cases
    [IsSolvable G]
    (rho : Representation k G V)
    (hKR : K.IsComplement' R)
    (hnormK : R ≤ Subgroup.normalizer (K : Set G))
    (hcop : Nat.Coprime (Nat.card K) (Nat.card R))
    (hodd : Odd (Nat.card G))
    (hRprime : (Nat.card R).Prime)
    (hGcard : (Nat.card G : k) ≠ 0)
    (hfix : Representation.invariants
      (rho.comp R.subtype : Representation k R V) = ⊥)
    (hperfect : ⁅R, K⁆ = K)
    (ih : OddPrimeSemidirectGlobalInductionHypothesis.{u, v, w}
      k (Nat.card G))
    (faithfulIrreducibleCase :
      ∀ (W : Type w) [AddCommGroup W] [Module k W] [Finite W]
        (sigma : Representation k G W) [Representation.IsIrreducible sigma],
        Function.Injective sigma →
        K ≠ ⊥ →
        Representation.invariants
          (sigma.comp R.subtype : Representation k R W) = ⊥ →
        False) :
    K ≤ rho.ker := by
  classical
  by_contra hK
  obtain ⟨U, hU, hUK, hfixU, hkerK, _hdis⟩ :=
    exists_irreducible_constituent_with_kernel_le_left rho hKR hnormK
      hcop hRprime hGcard hfix hK
  let sigma : Representation k G U.toSubmodule := U.toRepresentation
  let N : Subgroup G := sigma.ker
  letI : Representation.IsIrreducible sigma := hU
  letI : K.Normal :=
    normal_left_of_isComplement'_of_right_le_normalizer hKR hnormK
  letI : N.Normal := inferInstance
  by_cases hNbot : N = ⊥
  · have hsigma : Function.Injective sigma :=
      sigma.ker_eq_bot_iff.mp hNbot
    have hKne : K ≠ ⊥ := by
      intro hKbot
      apply hUK
      rw [hKbot]
      exact bot_le
    exact faithfulIrreducibleCase U.toSubmodule sigma hsigma hKne hfixU
  · let q : G →* G ⧸ N := QuotientGroup.mk' N
    let Kq : Subgroup (G ⧸ N) := K.map q
    let Rq : Subgroup (G ⧸ N) := R.map q
    let sigmaq : Representation k (G ⧸ N) U.toSubmodule :=
      quotientKerRepresentation sigma
    letI : Fintype (G ⧸ N) := Fintype.ofFinite (G ⧸ N)
    letI : IsSolvable (G ⧸ N) :=
      isSolvable_quotient_of_isSolvable N
    letI : Kq.Normal :=
      Subgroup.Normal.map (inferInstance : K.Normal) q
        (QuotientGroup.mk'_surjective N)
    have hlt : Nat.card (G ⧸ N) < Nat.card G :=
      natCard_quotient_lt_of_ne_bot N hNbot
    have hcompq : Kq.IsComplement' Rq := by
      exact Subgroup.IsComplement'.quotient_isComplement hKR hkerK
    have hcopq : Nat.Coprime (Nat.card Kq) (Nat.card Rq) := by
      exact (hcop.coprime_dvd_left (K.card_map_dvd q)).coprime_dvd_right
        (R.card_map_dvd q)
    have hoddq : Odd (Nat.card (G ⧸ N)) :=
      odd_natCard_quotient N hodd
    have hcardRq : Nat.card Rq = Nat.card R := by
      let f : R → Rq := q.subgroupMap R
      have hf : Function.Bijective f :=
        ⟨Subgroup.IsComplement'.quotientRight_subgroupMap_injective
            hKR hkerK,
          q.subgroupMap_surjective R⟩
      exact (Nat.card_congr (Equiv.ofBijective f hf)).symm
    have hprimeRq : (Nat.card Rq).Prime := by
      rw [hcardRq]
      exact hRprime
    have hcardq : (Nat.card (G ⧸ N) : k) ≠ 0 :=
      natCard_quotient_cast_ne_zero N hGcard
    have hfixq : Representation.invariants
        (sigmaq.comp Rq.subtype : Representation k Rq U.toSubmodule) = ⊥ := by
      exact quotientKerRepresentation_map_invariants_eq_bot sigma R hfixU
    have hrec : ⁅Rq, Kq⁆ ≤ sigmaq.ker :=
      ih (G ⧸ N) U.toSubmodule sigmaq Kq Rq hlt hcompq hcopq
        hoddq hprimeRq hcardq hfixq
    have hperfectq : ⁅Rq, Kq⁆ = Kq := by
      dsimp [Rq, Kq, q]
      rw [← Subgroup.map_commutator, hperfect]
    have hKqbot : Kq = ⊥ := by
      rw [quotientKerRepresentation_ker_eq_bot] at hrec
      rw [hperfectq] at hrec
      exact le_bot_iff.mp hrec
    have hKN : K ≤ N := by
      have hle := (Subgroup.map_eq_bot_iff K).mp hKqbot
      simpa [q, QuotientGroup.ker_mk'] using hle
    exact hUK hKN

end

end Submission.OddOrder.BG.Section03
