import Mathlib

namespace Submission

noncomputable section

theorem brauer_character_in_cyclotomic (G : Type) [Group G] [Fintype G] :
    ∃ φ : CyclotomicField (Monoid.exponent G) ℚ →+* ℂ,
      ∀ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : FiniteDimensional ℂ V)
        (ρ : Representation ℂ G V) (g : G),
        LinearMap.trace ℂ V (ρ g) ∈ φ.range := by
  classical
  let n := Monoid.exponent G
  haveI : NeZero n := Monoid.neZero_exponent_of_finite (G := G)
  haveI : NeZero (n : ℚ) := by infer_instance
  haveI : IsCyclotomicExtension ({n} : Set ℕ) ℚ (CyclotomicField n ℚ) :=
    CyclotomicField.isCyclotomicExtension n ℚ
  let F : IntermediateField ℚ ℂ :=
    IntermediateField.adjoin ℚ {z : ℂ | ∃ m ∈ ({n} : Set ℕ), m ≠ 0 ∧ z ^ m = 1}
  let e : CyclotomicField n ℚ ≃ₐ[ℚ] F :=
    Classical.choice
      (IsCyclotomicExtension.nonempty_algEquiv_adjoin_of_isSepClosed
        ({n} : Set ℕ) ℚ (CyclotomicField n ℚ) ℂ)
  let φAlg : CyclotomicField n ℚ →ₐ[ℚ] ℂ :=
    (IsScalarTower.toAlgHom ℚ F ℂ).comp e.toAlgHom
  refine ⟨φAlg.toRingHom, ?_⟩
  intro V _ _ _ ρ g
  let f : Module.End ℂ V := ρ g
  have hφ_range : ∀ z : ℂ, z ∈ φAlg.toRingHom.range ↔ z ∈ F := by
    intro z
    constructor
    · rintro ⟨x, rfl⟩
      exact (e x).2
    · intro hz
      obtain ⟨x, hx⟩ := e.surjective ⟨z, hz⟩
      refine ⟨x, ?_⟩
      exact congr_arg Subtype.val hx
  have hroot_mem_range :
      ∀ z ∈ (LinearMap.charpoly f).roots, z ∈ φAlg.toRingHom.range := by
    intro z hz
    have hchar_ne : LinearMap.charpoly f ≠ 0 :=
      (LinearMap.charpoly_monic f).ne_zero
    have hroot : (LinearMap.charpoly f).IsRoot z :=
      (Polynomial.mem_roots hchar_ne).mp hz
    have heig : f.HasEigenvalue z :=
      (Module.End.hasEigenvalue_iff_isRoot_charpoly f z).mpr hroot
    have hfpow : f ^ n = 1 := by
      change (ρ g) ^ n = 1
      rw [← map_pow, Monoid.pow_exponent_eq_one, map_one]
    have heig_pow : (1 : Module.End ℂ V).HasEigenvalue (z ^ n) := by
      simpa [hfpow] using heig.pow n
    have hzpow : z ^ n = 1 := by
      obtain ⟨v, hv⟩ := heig_pow.exists_hasEigenvector
      have hvapp := hv.apply_eq_smul
      simp only [Module.End.one_apply] at hvapp
      by_contra hz_ne
      have hscalar : (z ^ n - 1) • v = 0 := by
        calc
          (z ^ n - 1) • v = z ^ n • v - (1 : ℂ) • v := by rw [sub_smul]
          _ = z ^ n • v - v := by simp
          _ = 0 := by rw [← hvapp, sub_self]
      have hvzero : v = 0 := by
        have hnon : z ^ n - 1 ≠ 0 := sub_ne_zero.mpr hz_ne
        exact (smul_eq_zero.mp hscalar).elim (fun h0 => False.elim (hnon h0)) id
      exact hv.2 hvzero
    rw [hφ_range]
    exact IntermediateField.subset_adjoin ℚ
      {z : ℂ | ∃ m ∈ ({n} : Set ℕ), m ≠ 0 ∧ z ^ m = 1}
      ⟨n, by simp, NeZero.ne n, hzpow⟩
  have htrace :
      LinearMap.trace ℂ V (ρ g) = (LinearMap.charpoly f).roots.sum := by
    change LinearMap.trace ℂ V f = (LinearMap.charpoly f).roots.sum
    exact Module.End.trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits _)
  rw [htrace]
  exact Subring.multiset_sum_mem φAlg.toRingHom.range
    (LinearMap.charpoly f).roots hroot_mem_range

end

end Submission
