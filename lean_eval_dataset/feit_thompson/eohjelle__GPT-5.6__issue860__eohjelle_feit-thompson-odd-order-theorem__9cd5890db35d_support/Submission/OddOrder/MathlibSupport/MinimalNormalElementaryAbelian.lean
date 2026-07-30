import Submission.OddOrder.MathlibSupport.MinimalNormal

/-!
Elementary-abelian structure of a solvable minimal normal subgroup.

Unlike the ambient-solvable variant in `MinimalNormal`, these results only
assume that the minimal normal subgroup itself is solvable.  This is the form
used in the local induction inside `BGappendixAB.odd_p_stable`.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped IsMulCommutative

variable {G : Type*} [Group G]
variable {M : Subgroup G}

namespace IsMinimalNormal

theorem commutator_eq_bot_of_isSolvable [IsSolvable M]
    (hM : IsMinimalNormal M) : ⁅M, M⁆ = ⊥ := by
  letI : M.Normal := hM.normal
  have hproper : ⁅M, M⁆ < M := by
    letI : Nontrivial M := M.nontrivial_iff_ne_bot.mpr hM.ne_bot
    rw [← M.range_subtype, MonoidHom.range_eq_map, ← Subgroup.map_commutator,
      Subgroup.map_subtype_lt_map_subtype]
    exact IsSolvable.commutator_lt_top_of_nontrivial M
  by_contra hcomm
  have heq : ⁅M, M⁆ = M := hM.eq_of_normal_le
    (by infer_instance) (Subgroup.commutator_le_left M M) hcomm
  exact (ne_of_lt hproper) heq

theorem isMulCommutative_of_isSolvable [IsSolvable M]
    (hM : IsMinimalNormal M) : IsMulCommutative M := by
  have hcent : M ≤ Subgroup.centralizer (M : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      hM.commutator_eq_bot_of_isSolvable
  refine ⟨⟨fun x y ↦ ?_⟩⟩
  apply Subtype.ext
  exact hcent y.2 x x.2

/-- A finite solvable minimal normal `p`-subgroup has exponent `p`. -/
theorem pow_eq_one_of_isPGroup [Finite G] [IsSolvable M]
    (hM : IsMinimalNormal M) {p : ℕ} [Fact p.Prime]
    (hP : IsPGroup p M) : ∀ x : M, x ^ p = 1 := by
  classical
  letI : M.Normal := hM.normal
  letI : IsMulCommutative M := hM.isMulCommutative_of_isSolvable
  let R : Subgroup M := (powMonoidHom p : M →* M).range
  letI : R.Characteristic := by
    rw [Subgroup.characteristic_iff_map_eq]
    intro e
    dsimp [R]
    exact MulEquiv.map_range_powMonoidHom e p
  let K : Subgroup G := R.map M.subtype
  have hKnormal : K.Normal := by
    dsimp [K]
    infer_instance
  have hKle : K ≤ M := by
    dsimp [K]
    exact Subgroup.map_subtype_le _
  by_cases hR : R = ⊥
  · intro x
    have hx : x ^ p ∈ R := by
      change x ^ p ∈ (powMonoidHom p : M →* M).range
      exact ⟨x, by simp⟩
    rw [hR] at hx
    exact Subgroup.mem_bot.mp hx
  · have hKnon : K ≠ ⊥ := by
      dsimp [K]
      intro hK
      apply hR
      exact (Subgroup.map_eq_bot_iff_of_injective
        R M.subtype_injective).mp hK
    have hKM : K = M := hM.eq_of_normal_le hKnormal hKle hKnon
    change R.map M.subtype = M at hKM
    have hRtop : R = ⊤ := by
      apply top_unique
      rw [← Subgroup.map_subtype_le_map_subtype]
      rw [hKM]
      exact Subgroup.map_subtype_le _
    have hsurj : Function.Surjective (powMonoidHom p : M →* M) :=
      MonoidHom.range_eq_top.mp (by simpa [R] using hRtop)
    have hinj : Function.Injective (powMonoidHom p : M →* M) :=
      Finite.injective_iff_surjective.mpr hsurj
    obtain ⟨n, hcard⟩ := hP.exists_card_eq
    have hn : n ≠ 0 := by
      intro hn
      subst n
      have hcardOne : Nat.card M = 1 := by simpa using hcard
      have hcardGt : 1 < Nat.card M := M.one_lt_card_iff_ne_bot.mpr hM.ne_bot
      omega
    have hpCard : p ∣ Nat.card M := by
      rw [hcard]
      exact dvd_pow_self p hn
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hpCard
    have hxne : x ≠ 1 := by
      intro hxeq
      subst x
      simp at hx
      exact (Fact.out : p.Prime).ne_one hx.symm
    exfalso
    apply hxne
    apply hinj
    simp [powMonoidHom_apply, ← hx]

theorem isElementaryAbelian_of_isPGroup [Finite G] [IsSolvable M]
    (hM : IsMinimalNormal M) {p : ℕ} [Fact p.Prime]
    (hP : IsPGroup p M) :
    IsMulCommutative M ∧ ∀ x : M, x ^ p = 1 :=
  ⟨hM.isMulCommutative_of_isSolvable, hM.pow_eq_one_of_isPGroup hP⟩

end IsMinimalNormal

end Submission.OddOrder.MathlibSupport
