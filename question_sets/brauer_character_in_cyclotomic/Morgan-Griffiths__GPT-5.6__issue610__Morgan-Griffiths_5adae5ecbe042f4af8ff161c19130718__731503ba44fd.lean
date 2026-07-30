import Mathlib
import Submission.Helpers

namespace Submission

/-ResultProofDefinitionsBegin-/
/-ResultProofDefinitionsEnd-/


theorem brauer_character_in_cyclotomic (G : Type) [Group G] [Fintype G] :
    ∃ φ : CyclotomicField (Monoid.exponent G) ℚ →+* ℂ,
      ∀ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : FiniteDimensional ℂ V)
        (ρ : Representation ℂ G V) (g : G),
        LinearMap.trace ℂ V (ρ g) ∈ φ.range := by
  classical
  let n : ℕ := Monoid.exponent G
  haveI hn : NeZero n := by
    dsimp [n]
    infer_instance
  haveI hnQ : NeZero (n : ℚ) := NeZero.charZero
  have hprim : ∀ k ∈ ({n} : Set ℕ), k ≠ 0 → ∃ r : ℂ, IsPrimitiveRoot r k := by
    intro k hk hk0
    have hk' : k = n := Set.mem_singleton_iff.mp hk
    subst k
    haveI : NeZero (n : ℂ) := NeZero.charZero
    exact HasEnoughRootsOfUnity.exists_primitiveRoot ℂ n
  let S : Set ℂ := {x : ℂ | ∃ k ∈ ({n} : Set ℕ), k ≠ 0 ∧ x ^ k = 1}
  let K' : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ S
  letI hcycl : IsCyclotomicExtension ({n} : Set ℕ) ℚ K' := by
    dsimp [K', S]
    exact IntermediateField.isCyclotomicExtension_adjoin_of_exists_isPrimitiveRoot
      ({n} : Set ℕ) ℚ ℂ hprim
  letI hbase : IsCyclotomicExtension ({n} : Set ℕ) ℚ (CyclotomicField n ℚ) :=
    CyclotomicField.isCyclotomicExtension n ℚ
  let e : CyclotomicField n ℚ ≃ₐ[ℚ] K' :=
    IsCyclotomicExtension.algEquiv ({n} : Set ℕ) ℚ (CyclotomicField n ℚ) K'
  let φ : CyclotomicField n ℚ →+* ℂ :=
    (IntermediateField.val K').toRingHom.comp e.toAlgHom.toRingHom
  change ∃ φ : CyclotomicField n ℚ →+* ℂ,
      ∀ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : FiniteDimensional ℂ V)
        (ρ : Representation ℂ G V) (g : G),
        LinearMap.trace ℂ V (ρ g) ∈ φ.range
  refine ⟨φ, ?_⟩
  intro V hA hM hFD ρ g
  letI : AddCommGroup V := hA
  letI : Module ℂ V := hM
  letI : FiniteDimensional ℂ V := hFD
  let f : Module.End ℂ V := ρ g
  have hfn : f ^ n = 1 := by
    dsimp [f]
    calc
      (ρ g : Module.End ℂ V) ^ n = ρ (g ^ n) := (map_pow ρ g n).symm
      _ = ρ 1 := by rw [Monoid.pow_exponent_eq_one g]
      _ = 1 := map_one ρ
  have hroot : ∀ μ ∈ (LinearMap.charpoly f).roots, μ ∈ K' := by
    intro μ hμ
    have hp0 : (LinearMap.charpoly f) ≠ 0 :=
      (LinearMap.charpoly_monic f).ne_zero
    have hIs : (LinearMap.charpoly f).IsRoot μ :=
      (Polynomial.mem_roots hp0).1 hμ
    have hev : f.HasEigenvalue μ :=
      (Module.End.hasEigenvalue_iff_isRoot_charpoly f μ).2 hIs
    obtain ⟨v, hv⟩ := hev.exists_hasEigenvector
    have hvne : v ≠ 0 := (Module.End.hasEigenvector_iff.1 hv).2
    have hvpow := hv.pow_apply n
    rw [hfn] at hvpow
    have heq : μ ^ n • v = (1 : ℂ) • v := by
      simpa using hvpow.symm
    have hmun : μ ^ n = (1 : ℂ) :=
      (smul_left_injective ℂ hvne) heq
    change μ ∈ IntermediateField.adjoin ℚ S
    apply IntermediateField.subset_adjoin ℚ S
    change ∃ k ∈ ({n} : Set ℕ), k ≠ 0 ∧ μ ^ k = 1
    exact ⟨n, Set.mem_singleton n, NeZero.ne n, hmun⟩
  have hsum : (LinearMap.charpoly f).roots.sum ∈ K' := by
    -- closure of an intermediate field under finite sums
    have aux : ∀ t : Multiset ℂ, (∀ z ∈ t, z ∈ K') → t.sum ∈ K' := by
      intro t
      induction t using Multiset.induction_on with
      | empty =>
          intro ht
          simpa using (K'.zero_mem)
      | @cons a t ih =>
          intro ht
          have ha : a ∈ K' := ht a (by simp)
          have ht' : ∀ z ∈ t, z ∈ K' := by
            intro z hz
            exact ht z (by simp [hz])
          simpa using K'.add_mem ha (ih ht')
    exact aux _ hroot
  have htr : LinearMap.trace ℂ V f = (LinearMap.charpoly f).roots.sum :=
    Module.End.trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits _)
  have hx : LinearMap.trace ℂ V (ρ g) ∈ K' := by
    change LinearMap.trace ℂ V f ∈ K'
    rw [htr]
    exact hsum
  -- use the inverse equivalence to witness membership in the range
  refine (RingHom.mem_range).2 ?_
  refine ⟨e.symm ⟨LinearMap.trace ℂ V (ρ g), hx⟩, ?_⟩
  change ((IntermediateField.val K').toRingHom)
      (e (e.symm ⟨LinearMap.trace ℂ V (ρ g), hx⟩)) =
        LinearMap.trace ℂ V (ρ g)
  rw [e.apply_symm_apply]
  rfl


end Submission
