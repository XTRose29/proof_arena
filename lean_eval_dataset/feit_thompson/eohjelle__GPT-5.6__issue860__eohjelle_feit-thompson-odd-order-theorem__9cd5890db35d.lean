import Submission.OddOrder.PF.Section14.OddOrderTheorem

namespace Submission

/-- Every finite group of odd order is solvable, in an arbitrary universe. -/
theorem feit_thompson {G : Type*} [Group G] [Finite G]
    (hodd : Odd (Nat.card G)) : IsSolvable G := by
  let hsmall :
      ∃ (G₀ : Type) (_ : Group G₀) (_ : Fintype G₀), Nonempty (G ≃* G₀) :=
    Finite.exists_type_univ_nonempty_mulEquiv G
  obtain ⟨G₀, hG₀, hfinG₀, ⟨e⟩⟩ := hsmall
  letI : Group G₀ := hG₀
  letI : Fintype G₀ := hfinG₀
  have hodd₀ : Odd (Nat.card G₀) := by
    rwa [← Nat.card_congr e.toEquiv]
  letI : IsSolvable G₀ := OddOrder.PF.Feit_Thompson hodd₀
  exact solvable_of_solvable_injective (f := e.toMonoidHom) e.injective

end Submission
