import Submission.OddOrder.BG.Section03.PrimeProductFrobenius

/-!
Representation-theoretic centralization for prime-product groups.
-/

namespace Submission.OddOrder.BG.Section03

universe u v w

variable {G : Type u} [Group G] [Fintype G]
variable {p q : ℕ}
variable {k : Type v} [Field k]
variable {V : Type w} [AddCommGroup V] [Module k V]

/-- If a Sylow `p`-subgroup has no fixed vectors, Lemma 3.3 turns the
Frobenius alternative into either centralization of the normal Sylow
`q`-subgroup or trivial action on that subgroup. -/
theorem sylow_le_centralizer_or_le_representation_ker
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (hcard : Nat.card G = p * q) (P : Sylow p G) (Q : Sylow q G)
    (rho : _root_.Representation k G V)
    (hchar : (Nat.card Q : k) ≠ 0)
    (hfix : _root_.Representation.invariants
      (rho.comp (P : Subgroup G).subtype : _root_.Representation k P V) = ⊥) :
    (P : Subgroup G) ≤ Subgroup.centralizer (Q : Set G) ∨
      (Q : Subgroup G) ≤ rho.ker := by
  classical
  by_cases hcentral : (P : Subgroup G) ≤
      Subgroup.centralizer (Q : Set G)
  · exact Or.inl hcentral
  · right
    by_contra hkernel
    have hfrob := sylow_isFrobeniusDecomposition_of_not_le_centralizer
      hp hq hpq hcard P Q hcentral
    have hchar' : (Fintype.card Q : k) ≠ 0 := by
      simpa [Nat.card_eq_fintype_card] using hchar
    exact hfrob.complement_invariants_ne_bot rho hchar' hkernel hfix

end Submission.OddOrder.BG.Section03
