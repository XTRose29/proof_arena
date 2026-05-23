/-
Downloaded from the public lean-eval leaderboard provenance.
problem_id: brauer_character_in_cyclotomic
user: Morgan-Griffiths
model: GPT-5.5
submission_repo: Morgan-Griffiths/997b9a415edd5b3300f67b0b86e2d6d3
submission_ref: aa6af3605a939af31c219c540940de95a99afdc4
issue_number: 46
-/
import Mathlib

namespace Submission

/-ResultDefinitionsBegin-/
/-ResultProofDefinitionsBegin-/

/-- A root of the characteristic polynomial of an endomorphism of finite order is a root of
unity of the same order.  We use the eigenvector interpretation of roots of the characteristic
polynomial over `ℂ`. -/
lemma root_pow_eq_one_of_mem_roots_charpoly_of_pow_eq_one
    {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {n : ℕ} {T : Module.End ℂ V} {μ : ℂ}
    (hT : T ^ n = 1) (hμ : μ ∈ T.charpoly.roots) : μ ^ n = 1 := by
  have hroot : T.charpoly.IsRoot μ := by
    exact (Polynomial.mem_roots (LinearMap.charpoly_monic T).ne_zero).mp hμ
  have heig : T.HasEigenvalue μ := by
    exact (Module.End.hasEigenvalue_iff_isRoot_charpoly T μ).mpr hroot
  obtain ⟨v, hv⟩ := heig.exists_hasUnifEigenvector
  have hpowv := hv.pow_apply n
  have hscalar : μ ^ n • v = (1 : ℂ) • v := by
    calc
      μ ^ n • v = (T ^ n) v := hpowv.symm
      _ = (1 : Module.End ℂ V) v := by rw [hT]
      _ = (1 : ℂ) • v := by simp
  exact smul_left_injective ℂ hv.2 hscalar

/-- If a complex endomorphism satisfies `T ^ n = 1`, then its trace belongs to the
intermediate field generated over `ℚ` by the `n`-th roots of unity. -/
lemma trace_mem_adjoin_nth_roots_of_pow_eq_one
    {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {n : ℕ} (hn : n ≠ 0) {T : Module.End ℂ V} (hT : T ^ n = 1) :
    LinearMap.trace ℂ V T ∈
      IntermediateField.adjoin ℚ {x : ℂ | ∃ m ∈ ({n} : Set ℕ), m ≠ 0 ∧ x ^ m = 1} := by
  classical
  let L : IntermediateField ℚ ℂ :=
    IntermediateField.adjoin ℚ {x : ℂ | ∃ m ∈ ({n} : Set ℕ), m ≠ 0 ∧ x ^ m = 1}
  have htrace : LinearMap.trace ℂ V T = T.charpoly.roots.sum := by
    simpa using Module.End.trace_eq_sum_roots_charpoly_of_splits (f := T)
      (IsAlgClosed.splits T.charpoly)
  rw [htrace]
  change T.charpoly.roots.sum ∈ L
  exact L.multiset_sum_mem T.charpoly.roots (by
    intro μ hμ
    apply IntermediateField.subset_adjoin
    exact ⟨n, by simp, hn, root_pow_eq_one_of_mem_roots_charpoly_of_pow_eq_one hT hμ⟩)

/-ResultProofDefinitionsEnd-/
/-ResultDefinitionsEnd-/

/-ResultBegin-/
theorem brauer_character_in_cyclotomic (G : Type) [Group G] [Fintype G] :
    ∃ φ : CyclotomicField (Monoid.exponent G) ℚ →+* ℂ,
      ∀ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : FiniteDimensional ℂ V)
        (ρ : Representation ℂ G V) (g : G),
        LinearMap.trace ℂ V (ρ g) ∈ φ.range :=
/-ResultProofBegin-/by
  classical
  let n := Monoid.exponent G
  let L : IntermediateField ℚ ℂ :=
    IntermediateField.adjoin ℚ {x : ℂ | ∃ m ∈ ({n} : Set ℕ), m ≠ 0 ∧ x ^ m = 1}
  haveI : NeZero n := by
    dsimp [n]
    infer_instance
  have hn : n ≠ 0 := NeZero.ne n
  haveI : NeZero (n : ℚ) := ⟨Nat.cast_ne_zero.mpr hn⟩
  haveI : IsCyclotomicExtension ({n} : Set ℕ) ℚ (CyclotomicField n ℚ) :=
    CyclotomicField.isCyclotomicExtension n ℚ
  let e : CyclotomicField n ℚ ≃ₐ[ℚ] L := Classical.choice <|
    IsCyclotomicExtension.nonempty_algEquiv_adjoin_of_isSepClosed
      ({n} : Set ℕ) ℚ (CyclotomicField n ℚ) ℂ
  let φ : CyclotomicField (Monoid.exponent G) ℚ →+* ℂ :=
    (L.val.comp e.toAlgHom).toRingHom
  refine ⟨φ, ?_⟩
  intro V _ _ _ ρ g
  let T : Module.End ℂ V := ρ g
  have hT : T ^ n = 1 := by
    calc
      T ^ n = ρ (g ^ n) := by
        simp [T]
      _ = 1 := by
        simp [n, Monoid.pow_exponent_eq_one]
  have hmemL : LinearMap.trace ℂ V T ∈ L := by
    exact trace_mem_adjoin_nth_roots_of_pow_eq_one hn hT
  change LinearMap.trace ℂ V T ∈ φ.range
  rw [RingHom.mem_range]
  refine ⟨e.symm ⟨LinearMap.trace ℂ V T, hmemL⟩, ?_⟩
  change ((e (e.symm ⟨LinearMap.trace ℂ V T, hmemL⟩) : L) : ℂ) = LinearMap.trace ℂ V T
  rw [e.apply_symm_apply]
/-ResultProofEnd-/
/-ResultEnd-/
end Submission