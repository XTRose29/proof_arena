import Submission.Helpers

open LeanEval.GroupTheory
open LeanEval.GroupTheory.Defs

namespace Submission.Helpers

universe u

theorem pairwise_quotient
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (x : G)
    (h : ∀ g : G, IsPGroup p
      (Subgroup.closure ({x, g * x * g⁻¹} : Set G)))
    (N : Subgroup G) [N.Normal] :
    ∀ g : G ⧸ N, IsPGroup p
      (Subgroup.closure
        ({QuotientGroup.mk' N x,
          g * QuotientGroup.mk' N x * g⁻¹} : Set (G ⧸ N))) := by
  intro g
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N g
  have hp := (h g).map (QuotientGroup.mk' N)
  rw [MonoidHom.map_closure] at hp
  have hs :
      QuotientGroup.mk' N ''
          ({x, g * x * g⁻¹} : Set G) =
        ({QuotientGroup.mk' N x,
          QuotientGroup.mk' N g * QuotientGroup.mk' N x *
            (QuotientGroup.mk' N g)⁻¹} : Set (G ⧸ N)) := by
    ext y
    simp [eq_comm]
  rwa [hs] at hp

theorem card_quotient_lt_of_ne_bot
    {G : Type*} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal] (hN : N ≠ ⊥) :
    Nat.card (G ⧸ N) < Nat.card G := by
  rw [N.card_eq_card_quotient_mul_card_subgroup]
  exact
    (Nat.lt_mul_iff_one_lt_right
      (Nat.card_pos : 0 < Nat.card (G ⧸ N))).2
      ((Subgroup.one_lt_card_iff_ne_bot N).2 hN)

/-- Quotient induction eliminates every nontrivial normal `p`-subgroup from
a minimal counterexample. -/
theorem mem_pCore_of_nontrivial_normal_pSubgroup_of_induction
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hind : ∀ {K : Type u} [Group K] [Finite K],
      Nat.card K < Nat.card G → ∀ y : K,
        y ∈ pCore p K ↔
          ∀ k : K, IsPGroup p
            (Subgroup.closure ({y, k * y * k⁻¹} : Set K)))
    (x : G)
    (h : ∀ g : G, IsPGroup p
      (Subgroup.closure ({x, g * x * g⁻¹} : Set G)))
    (N : Subgroup G) (hNnormal : N.Normal)
    (hNp : IsPGroup p N) (hNne : N ≠ ⊥) :
    x ∈ pCore p G := by
  letI : N.Normal := hNnormal
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  have hxq : q x ∈ pCore p (G ⧸ N) := by
    apply
      (hind (card_quotient_lt_of_ne_bot N hNne) (q x)).2
    exact pairwise_quotient x h N
  have hker : IsPGroup p q.ker := by
    rw [show q = QuotientGroup.mk' N from rfl, QuotientGroup.ker_mk']
    exact hNp
  have hp :
      IsPGroup p ((pCore p (G ⧸ N)).comap q) :=
    pCore_isPGroup.comap_of_ker_isPGroup q hker
  have hn :
      ((pCore p (G ⧸ N)).comap q).Normal :=
    (pCore_normal p).comap q
  apply le_pCore hn hp
  exact hxq

theorem pCore_eq_bot_of_not_mem_of_induction
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hind : ∀ {K : Type u} [Group K] [Finite K],
      Nat.card K < Nat.card G → ∀ y : K,
        y ∈ pCore p K ↔
          ∀ k : K, IsPGroup p
            (Subgroup.closure ({y, k * y * k⁻¹} : Set K)))
    (x : G)
    (h : ∀ g : G, IsPGroup p
      (Subgroup.closure ({x, g * x * g⁻¹} : Set G)))
    (hx : x ∉ pCore p G) :
    pCore p G = ⊥ := by
  by_contra hne
  exact hx
    (mem_pCore_of_nontrivial_normal_pSubgroup_of_induction
      hind x h (pCore p G) (pCore_normal p) pCore_isPGroup hne)

end Submission.Helpers
