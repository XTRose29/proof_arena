import Mathlib

/-!
The largest normal `p`-subgroup of a group.

MathComp writes `'O_p(G)` for this subgroup.  Mathlib provides the Sylow and
normal-supremum theorems needed to construct it, but does not bundle the
construction itself.
-/

namespace Submission.OddOrder.MathlibSupport

variable {G : Type*} [Group G] {p : ℕ}

/-- The `p`-core: the supremum of all normal `p`-subgroups. -/
def pCore (p : ℕ) (G : Type*) [Group G] : Subgroup G :=
  sSup {P : Subgroup G | IsPGroup p P ∧ P.Normal}

theorem le_pCore {P : Subgroup G} (hP : IsPGroup p P) (hPnormal : P.Normal) :
    P ≤ pCore p G :=
  le_sSup ⟨hP, hPnormal⟩

instance pCore_normal : (pCore p G).Normal := by
  rw [pCore]
  apply Subgroup.sSup_normal
  exact fun P hP => hP.2

theorem pCore_isPGroup : IsPGroup p (pCore p G) := by
  rw [pCore]
  apply Sylow.sSup_of_normal
  · exact fun P hP => hP.1
  · exact fun P hP => hP.2

theorem map_pCore_le_equiv (e : G ≃* G) :
    (pCore p G).map e.toMonoidHom ≤ pCore p G :=
  le_pCore (pCore_isPGroup.map e.toMonoidHom)
    (Subgroup.Normal.map (by infer_instance) e.toMonoidHom e.surjective)

instance pCore_characteristic : (pCore p G).Characteristic := by
  rw [Subgroup.characteristic_iff_map_eq]
  intro e
  apply le_antisymm (map_pCore_le_equiv e)
  rw [← Subgroup.map_le_map_iff_of_injective
    (f := e.symm.toMonoidHom) e.symm.injective]
  have h := map_pCore_le_equiv (p := p) e.symm
  simpa [Subgroup.map_map] using h

theorem pCore_le_sylow (S : Sylow p G) : pCore p G ≤ S :=
  pCore_isPGroup.le_sylow_of_normal S

theorem pCore_eq_top_of_isPGroup (hG : IsPGroup p G) : pCore p G = ⊤ := by
  exact top_unique (le_pCore (hG.to_subgroup ⊤) (by infer_instance))

end Submission.OddOrder.MathlibSupport
