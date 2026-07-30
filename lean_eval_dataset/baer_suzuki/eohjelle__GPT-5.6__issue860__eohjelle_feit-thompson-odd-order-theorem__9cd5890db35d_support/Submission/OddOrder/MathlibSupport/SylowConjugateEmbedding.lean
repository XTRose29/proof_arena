import Submission.OddOrder.MathlibSupport.BaerSuzukiSylow

/-!
Conjugating a p-subgroup into a selected Sylow subgroup of a subgroup type.
-/

namespace Submission.OddOrder.MathlibSupport

variable {G : Type*} [Group G] [Finite G]

/-- A p-subgroup of `E` can be conjugated into a chosen Sylow p-subgroup of
`E`, expressed back in the ambient group. -/
theorem exists_conjugate_le_sylow_map {p : ℕ} [Fact p.Prime]
    {E B : Subgroup G} (P₀ : Sylow p E) (hBE : B ≤ E)
    (hB : IsPGroup p B) :
    ∃ e : E, ∀ b : G, b ∈ B →
      (e : G) * b * (e : G)⁻¹ ∈
        (P₀ : Subgroup E).map E.subtype := by
  let Bₑ : Subgroup E := B.subgroupOf E
  have hBₑ : IsPGroup p Bₑ := hB.comap_subtype
  obtain ⟨Q, hBQ⟩ := hBₑ.exists_le_sylow
  obtain ⟨e, he⟩ := MulAction.exists_smul_eq E Q P₀
  refine ⟨e, ?_⟩
  intro b hb
  let bₑ : E := ⟨b, hBE hb⟩
  have hbQ : bₑ ∈ Q := hBQ hb
  have hconjQ : (MulAut.conj e) bₑ ∈ (e • Q : Sylow p E) := by
    exact Subgroup.mem_map_of_mem (MulAut.conj e).toMonoidHom hbQ
  rw [he] at hconjQ
  exact ⟨(MulAut.conj e) bₑ, hconjQ, rfl⟩

end Submission.OddOrder.MathlibSupport
