import Submission.OddOrder.BG.AppendixAB.QuadraticPairFunctorial
import Submission.OddOrder.MathlibSupport.SubgroupCardinality

/-!
Transport of a quadratic pair through a normal quotient, with strict descent.
-/

namespace Submission.OddOrder.BG.AppendixAB

open Submission.OddOrder.MathlibSupport

variable {G : Type*} [Group G] [Finite G]

/-- Factoring a nontrivial normal subgroup contained in `E` strictly lowers
the cardinality of the image of `E`. -/
theorem natCard_map_quotient_lt
    {D E : Subgroup G} [D.Normal] (hDE : D ≤ E) (hD : D ≠ ⊥) :
    Nat.card (E.map (QuotientGroup.mk' D)) < Nat.card E := by
  let q : G →* G ⧸ D := QuotientGroup.mk' D
  let f : E →* E.map q := q.subgroupMap E
  letI : Fintype E := Fintype.ofFinite E
  letI : Fintype (E.map q) := Fintype.ofFinite (E.map q)
  have hfSurjective : Function.Surjective f := q.subgroupMap_surjective E
  have hfNotInjective : ¬Function.Injective f := by
    intro hf
    obtain ⟨d, hd⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hD
    have hfd : f ⟨d, hDE d.property⟩ = f 1 := by
      apply Subtype.ext
      change q (d : G) = q 1
      rw [map_one]
      exact (QuotientGroup.eq_one_iff (N := D) (d : G)).mpr d.property
    have hdOne : (⟨d, hDE d.property⟩ : E) = 1 := hf hfd
    apply hd
    apply Subtype.ext
    exact congrArg (fun z : E ↦ (z : G)) hdOne
  simpa only [Nat.card_eq_fintype_card] using
    Fintype.card_lt_of_surjective_not_injective f hfSurjective hfNotInjective

/-- The quotient image of a p-subgroup is again a p-subgroup and is strictly
smaller when the quotient kernel is nontrivial inside it. -/
theorem isPGroup_map_quotient_and_card_lt
    {p : ℕ} {D E : Subgroup G} [D.Normal]
    (hDE : D ≤ E) (hD : D ≠ ⊥) (hE : IsPGroup p E) :
    IsPGroup p (E.map (QuotientGroup.mk' D)) ∧
      Nat.card (E.map (QuotientGroup.mk' D)) < Nat.card E :=
  ⟨hE.map (QuotientGroup.mk' D), natCard_map_quotient_lt hDE hD⟩

/-- All hypotheses of the local quadratic-pair induction descend through a
normal quotient, and the acted-on subgroup has strictly smaller cardinality. -/
theorem quadraticPair_normalQuotient
    {p : ℕ} {D E : Subgroup G} [D.Normal]
    (hDE : D ≤ E) (hD : D ≠ ⊥) {x y : G}
    (hxN : x ∈ Subgroup.normalizer (E : Set G))
    (hyN : y ∈ Subgroup.normalizer (E : Set G))
    (hodd : Odd (Nat.card (pairGenerated x y)))
    (hE : IsPGroup p E)
    (hx : IsQuadraticPElement p E x)
    (hy : IsQuadraticPElement p E y) :
    let q : G →* G ⧸ D := QuotientGroup.mk' D
    let Eq : Subgroup (G ⧸ D) := E.map q
    q x ∈ Subgroup.normalizer (Eq : Set (G ⧸ D)) ∧
      q y ∈ Subgroup.normalizer (Eq : Set (G ⧸ D)) ∧
      Odd (Nat.card (pairGenerated (q x) (q y))) ∧
      IsPGroup p Eq ∧
      IsQuadraticPElement p Eq (q x) ∧
      IsQuadraticPElement p Eq (q y) ∧
      Nat.card Eq < Nat.card E := by
  dsimp only
  obtain ⟨hxNq, hyNq, hoddq, hEq, hxq, hyq⟩ :=
    quadraticPair_map (QuotientGroup.mk' D)
      hxN hyN hodd hE hx hy
  exact ⟨hxNq, hyNq, hoddq, hEq, hxq, hyq,
    natCard_map_quotient_lt hDE hD⟩

end Submission.OddOrder.BG.AppendixAB
