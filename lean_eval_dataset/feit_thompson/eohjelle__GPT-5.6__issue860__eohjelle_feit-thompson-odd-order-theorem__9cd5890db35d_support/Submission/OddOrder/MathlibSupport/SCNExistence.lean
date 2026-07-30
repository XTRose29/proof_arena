import Submission.OddOrder.MathlibSupport.SCNCentralizer
import Submission.OddOrder.MathlibSupport.SelfCentralizing

/-!
Selection of self-centralizing normal abelian subgroups in finite `p`-groups.

MathComp's `max_SCN` interface is used in Bender--Glauberman Section 4 both
absolutely and relative to a prescribed normal abelian subgroup.  The latter
form is the one needed in the proof of Lemma 4.7.
-/

namespace Submission.OddOrder.MathlibSupport

universe u

variable {G : Type u} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]

/-- Select an inclusion-maximal normal abelian subgroup containing `Z`.

The final maximality statement is unconditional above `M`: any normal
abelian overgroup of `M` automatically still contains `Z`. -/
theorem exists_maximal_isNormalAbelian_containing
    (Z : Subgroup G) (hZ : IsNormalAbelian Z) :
    ∃ M : Subgroup G,
      Z ≤ M ∧ IsNormalAbelian M ∧
        ∀ {A : Subgroup G}, IsNormalAbelian A → M ≤ A → A ≤ M := by
  classical
  let s : Set (Subgroup G) := {A | IsNormalAbelian A ∧ Z ≤ A}
  have hs : s.Nonempty := ⟨Z, hZ, le_rfl⟩
  obtain ⟨M, hM, hMmax⟩ := s.toFinite.exists_maximal hs
  refine ⟨M, hM.2, hM.1, ?_⟩
  intro A hA hMA
  exact hMmax ⟨hA, hM.2.trans hMA⟩ hMA

/-- Relative form of the self-centralizing maximal-normal-abelian theorem. -/
theorem exists_selfCentralizing_isNormalAbelian_containing
    (hG : IsPGroup p G) (Z : Subgroup G) (hZ : IsNormalAbelian Z) :
    ∃ M : Subgroup G,
      Z ≤ M ∧ IsNormalAbelian M ∧
        Subgroup.centralizer (M : Set G) = M := by
  obtain ⟨M, hZM, hM, hMmax⟩ :=
    exists_maximal_isNormalAbelian_containing Z hZ
  exact ⟨M, hZM, hM,
    centralizer_eq_of_maximal_isNormalAbelian hG hM hMmax⟩

/-- A prescribed normal abelian subgroup of a finite `p`-group lies in an
SCN subgroup.  This is the mathlib-facing form of the `max_SCN` selection
used in Bender--Glauberman Lemma 4.7. -/
theorem exists_isSCN_top_containing
    (hG : IsPGroup p G) (Z : Subgroup G) (hZ : IsNormalAbelian Z) :
    ∃ M : Subgroup G, Z ≤ M ∧ IsSCN (⊤ : Subgroup G) M := by
  obtain ⟨M, hZM, hM, hcentralizer⟩ :=
    exists_selfCentralizing_isNormalAbelian_containing hG Z hZ
  refine ⟨M, hZM, ?_⟩
  refine
    { le_sylow := le_top
      le_normalizer := ?_
      commutative := hM.isMulCommutative
      centralizerWithin_eq := ?_ }
  · rw [Subgroup.normalizer_eq_top_iff.mpr hM.normal]
  · simpa [centralizerWithin] using hcentralizer

end Submission.OddOrder.MathlibSupport
