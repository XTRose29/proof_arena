import Mathlib

namespace Submission

theorem brauer_character_in_cyclotomic (G : Type) [Group G] [Fintype G] :
    ∃ φ : CyclotomicField (Monoid.exponent G) ℚ →+* ℂ,
      ∀ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : FiniteDimensional ℂ V)
        (ρ : Representation ℂ G V) (g : G),
        LinearMap.trace ℂ V (ρ g) ∈ φ.range := by
  have hn : 0 < Monoid.exponent G :=
    Monoid.exponent_pos_of_exists _ Fintype.card_pos (fun _ => pow_card_eq_one)
  haveI : NeZero (Monoid.exponent G) := ⟨hn.ne'⟩
  haveI : NeZero ((Monoid.exponent G : ℚ)) := ⟨Nat.cast_ne_zero.mpr hn.ne'⟩
  obtain ⟨φ⟩ : Nonempty (CyclotomicField (Monoid.exponent G) ℚ →+* ℂ) := inferInstance
  use φ
  intro V _ _ _ ρ g
  rw [Module.End.trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits _)]
  apply Subsemiring.multiset_sum_mem (RingHom.rangeS φ)
  intro x hx
  have h_x_pow : x ^ (Monoid.exponent G) = 1 := by
    have h2 := spectrum.pow_mem_pow (ρ g) (Monoid.exponent G) (by
      rw [Module.End.mem_spectrum_iff_isRoot_charpoly]
      exact Polynomial.mem_roots (LinearMap.charpoly_monic _).ne_zero |>.mp hx)
    rw [← map_pow, Monoid.pow_exponent_eq_one, map_one] at h2
    by_contra h
    exact h2 <| by
      change IsUnit (algebraMap ℂ (Module.End ℂ V) (x ^ Monoid.exponent G) - 1)
      have h5 : algebraMap ℂ (Module.End ℂ V) (x ^ Monoid.exponent G) - 1 =
          algebraMap ℂ (Module.End ℂ V) (x ^ Monoid.exponent G - 1) := by
        simp only [map_sub, map_one]
      rw [h5]
      exact (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr h)).map _
  
  haveI ext : IsCyclotomicExtension {Monoid.exponent G} ℚ
      (CyclotomicField (Monoid.exponent G) ℚ) :=
    CyclotomicField.isCyclotomicExtension (Monoid.exponent G) ℚ
  let ζ := IsCyclotomicExtension.zeta (Monoid.exponent G) ℚ
    (CyclotomicField (Monoid.exponent G) ℚ)
  have h_prim_K : IsPrimitiveRoot ζ (Monoid.exponent G) :=
    IsCyclotomicExtension.zeta_spec (Monoid.exponent G) ℚ
      (CyclotomicField (Monoid.exponent G) ℚ)
  obtain ⟨k, hk⟩ := (IsPrimitiveRoot.map_of_injective h_prim_K φ.injective).eq_pow_of_pow_eq_one h_x_pow
  exact ⟨ζ ^ k, by rw [map_pow, hk.2]⟩

end Submission