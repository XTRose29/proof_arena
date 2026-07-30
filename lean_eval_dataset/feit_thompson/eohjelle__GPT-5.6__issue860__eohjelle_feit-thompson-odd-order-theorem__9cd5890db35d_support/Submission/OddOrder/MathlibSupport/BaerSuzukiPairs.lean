import Submission.OddOrder.MathlibSupport.BaerSuzukiSylow

/-!
Equivalent pairwise forms of the Baer-Suzuki hypothesis.
-/

namespace Submission.OddOrder.MathlibSupport

open Submission.OddOrder.BG.AppendixAB

variable {G : Type*} [Group G]

/-- The usual one-sided Baer-Suzuki hypothesis. -/
def ConjugatePairsArePGroup (p : ℕ) (x : G) : Prop :=
  ∀ g : G, IsPGroup p (pairGenerated x (g * x * g⁻¹))

theorem conjugacyPairsArePGroup_of_conjugatePairsArePGroup {p : ℕ} {x : G}
    (hx : ConjugatePairsArePGroup p x) : ConjugacyPairsArePGroup p x := by
  intro a ha b hb
  obtain ⟨g, rfl⟩ := isConj_iff.mp ha
  obtain ⟨h, rfl⟩ := isConj_iff.mp hb
  let e : G ≃* G := MulAut.conj g
  let k : G := g⁻¹ * h
  have hk : IsPGroup p (pairGenerated x (k * x * k⁻¹)) := hx k
  have hmap := hk.map e.toMonoidHom
  rw [pairGenerated_map_equiv] at hmap
  change IsPGroup p
    (pairGenerated (g * x * g⁻¹)
      (g * (g⁻¹ * h * x * (g⁻¹ * h)⁻¹) * g⁻¹)) at hmap
  have heq : g * (g⁻¹ * h * x * (g⁻¹ * h)⁻¹) * g⁻¹ =
      h * x * h⁻¹ := by
    group
  rw [heq] at hmap
  exact hmap

theorem conjugatePairsArePGroup_of_conjugacyPairsArePGroup {p : ℕ} {x : G}
    (hx : ConjugacyPairsArePGroup p x) : ConjugatePairsArePGroup p x := by
  intro g
  apply hx x mem_conjugatesOf_self (g * x * g⁻¹)
  exact isConj_iff.mpr ⟨g, rfl⟩

theorem conjugatePairsArePGroup_iff_conjugacyPairsArePGroup {p : ℕ} {x : G} :
    ConjugatePairsArePGroup p x ↔ ConjugacyPairsArePGroup p x :=
  ⟨conjugacyPairsArePGroup_of_conjugatePairsArePGroup,
    conjugatePairsArePGroup_of_conjugacyPairsArePGroup⟩

end Submission.OddOrder.MathlibSupport
