import Mathlib
import Submission.Helpers

namespace Submission

theorem brauer_character_in_cyclotomic (G : Type) [Group G] [Fintype G] :
    ∃ φ : CyclotomicField (Monoid.exponent G) ℚ →+* ℂ,
      ∀ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : FiniteDimensional ℂ V)
        (ρ : Representation ℂ G V) (g : G),
        LinearMap.trace ℂ V (ρ g) ∈ φ.range := by
  have hn_ne_zero : Monoid.exponent G ≠ 0 := Monoid.exponent_ne_zero_of_finite
  have hn_pos : 0 < Monoid.exponent G := Nat.pos_of_ne_zero hn_ne_zero
  haveI hn_ne : NeZero (Monoid.exponent G) := ⟨hn_ne_zero⟩
  haveI : NeZero ((Monoid.exponent G : ℚ)) := NeZero.charZero
  haveI hCE : IsCyclotomicExtension {Monoid.exponent G} ℚ
      (CyclotomicField (Monoid.exponent G) ℚ) :=
    CyclotomicField.isCyclotomicExtension _ _
  haveI : Algebra.IsAlgebraic ℚ (CyclotomicField (Monoid.exponent G) ℚ) :=
    NumberField.isAlgebraic (CyclotomicField (Monoid.exponent G) ℚ)
  let φ_alg : CyclotomicField (Monoid.exponent G) ℚ →ₐ[ℚ] ℂ := IsAlgClosed.lift
  obtain ⟨ζ_K, hζ_K⟩ : ∃ ζ : CyclotomicField (Monoid.exponent G) ℚ,
      IsPrimitiveRoot ζ (Monoid.exponent G) :=
    IsCyclotomicExtension.exists_isPrimitiveRoot ℚ
      (CyclotomicField (Monoid.exponent G) ℚ) (Set.mem_singleton _) hn_ne_zero
  have hφζ : IsPrimitiveRoot (φ_alg ζ_K) (Monoid.exponent G) :=
    hζ_K.map_of_injective φ_alg.toRingHom.injective
  have h_root_in_range : ∀ z : ℂ, z ^ Monoid.exponent G = 1 → z ∈ φ_alg.toRingHom.range := by
    intro z hz
    obtain ⟨k, _, hzk⟩ := hφζ.eq_pow_of_pow_eq_one hz
    exact ⟨ζ_K ^ k, by rw [map_pow]; exact hzk⟩
  refine ⟨φ_alg.toRingHom, ?_⟩
  intro V _ _ _ ρ g
  have hg_pow : g ^ Monoid.exponent G = 1 := Monoid.pow_exponent_eq_one g
  have hρg_pow : (ρ g) ^ Monoid.exponent G = 1 := by
    rw [← map_pow, hg_pow, map_one]
  let d := Module.finrank ℂ V
  let b : Module.Basis (Fin d) ℂ V := Module.finBasis ℂ V
  let M : Matrix (Fin d) (Fin d) ℂ := LinearMap.toMatrix b b (ρ g)
  have hM_pow : M ^ Monoid.exponent G = 1 := by
    show (LinearMap.toMatrix b b (ρ g)) ^ Monoid.exponent G = 1
    rw [LinearMap.toMatrix_pow, hρg_pow, LinearMap.toMatrix_one]
  have h_trace_eq : LinearMap.trace ℂ V (ρ g) = M.trace :=
    LinearMap.trace_eq_matrix_trace ℂ b (ρ g)
  have h_sum_roots : M.trace = M.charpoly.roots.sum :=
    Matrix.trace_eq_sum_roots_charpoly M
  have h_root_pow_eq_one : ∀ μ ∈ M.charpoly.roots, μ ^ Monoid.exponent G = 1 := by
    intro μ hμ
    have hμ_root : M.charpoly.IsRoot μ := (Polynomial.mem_roots'.mp hμ).2
    have h_eig : Module.End.HasEigenvalue M.toLin' μ := by
      rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin']
      exact hμ_root
    have h_eig_pow : Module.End.HasEigenvalue (M.toLin' ^ Monoid.exponent G)
        (μ ^ Monoid.exponent G) := h_eig.pow _
    have h_pow_one : (M.toLin' ^ Monoid.exponent G : Module.End ℂ (Fin d → ℂ)) = 1 := by
      rw [← Matrix.toLin'_pow, hM_pow, Matrix.toLin'_one]
      rfl
    rw [h_pow_one] at h_eig_pow
    obtain ⟨v, hv⟩ := h_eig_pow.exists_hasEigenvector
    have hv_eq : (1 : Module.End ℂ (Fin d → ℂ)) v = μ ^ Monoid.exponent G • v :=
      hv.apply_eq_smul
    have hv_ne : v ≠ 0 := hv.2
    have hv1 : v = μ ^ Monoid.exponent G • v := by
      have h1v : (1 : Module.End ℂ (Fin d → ℂ)) v = v := rfl
      rw [← h1v]; exact hv_eq
    have h_smul_zero : (1 - μ ^ Monoid.exponent G) • v = 0 := by
      rw [sub_smul, one_smul, sub_eq_zero]; exact hv1
    rcases smul_eq_zero.mp h_smul_zero with h | h
    · exact (sub_eq_zero.mp h).symm
    · exact absurd h hv_ne
  have h_roots_in_range : ∀ μ ∈ M.charpoly.roots, μ ∈ φ_alg.toRingHom.range :=
    fun μ hμ => h_root_in_range μ (h_root_pow_eq_one μ hμ)
  rw [h_trace_eq, h_sum_roots]
  apply Subring.multiset_sum_mem
  exact h_roots_in_range

end Submission
