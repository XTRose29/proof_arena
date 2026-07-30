import Submission.OddOrder.MathlibSupport.CharacteristicUnderNormalizer
import Submission.OddOrder.MathlibSupport.MinimalNormalUnder

/-!
Elementary-abelian structure of finite p-subgroups that are minimal normal
under an acting subgroup.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped IsMulCommutative

variable {G : Type*} [Group G]
variable {E H : Subgroup G}

namespace IsMinimalNormalUnder

theorem commutator_eq_bot_of_isSolvable [IsSolvable E]
    (h : IsMinimalNormalUnder E H) : ⁅E, E⁆ = ⊥ := by
  let R : Subgroup E := _root_.commutator (G := E)
  letI : R.Characteristic := by
    dsimp [R, _root_.commutator]
    infer_instance
  have hmap : R.map E.subtype = ⁅E, E⁆ := by
    dsimp [R, _root_.commutator]
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, E.range_subtype]
  have hcommle : ⁅E, E⁆ ≤ E := by
    simpa using Subgroup.commutator_le_sup E E
  have hproper : ⁅E, E⁆ < E := by
    letI : Nontrivial E := E.nontrivial_iff_ne_bot.mpr h.ne_bot
    rw [← E.range_subtype, MonoidHom.range_eq_map,
      ← Subgroup.map_commutator, Subgroup.map_subtype_lt_map_subtype]
    exact IsSolvable.commutator_lt_top_of_nontrivial E
  by_contra hcomm
  have hinvariant : ∀ g : G, g ∈ H → ∀ d : G, d ∈ ⁅E, E⁆ →
      g * d * g⁻¹ ∈ ⁅E, E⁆ := by
    rw [← hmap]
    exact characteristic_map_subtype_invariant_under_normalizer
      E H R h.le_normalizer
  have hle : E ≤ ⁅E, E⁆ := h.2.2 _ hcommle hcomm hinvariant
  exact (ne_of_lt hproper) (le_antisymm hcommle hle)

theorem isMulCommutative_of_isSolvable [IsSolvable E]
    (h : IsMinimalNormalUnder E H) : IsMulCommutative E := by
  have hcent : E ≤ Subgroup.centralizer (E : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      h.commutator_eq_bot_of_isSolvable
  refine ⟨⟨fun x y ↦ ?_⟩⟩
  apply Subtype.ext
  exact hcent y.2 x x.2

/-- A finite solvable p-subgroup minimal normal under `H` has exponent p. -/
theorem pow_eq_one_of_isPGroup [Finite G] [IsSolvable E]
    (h : IsMinimalNormalUnder E H) {p : ℕ} [Fact p.Prime]
    (hP : IsPGroup p E) : ∀ x : E, x ^ p = 1 := by
  classical
  letI : IsMulCommutative E := h.isMulCommutative_of_isSolvable
  let R : Subgroup E := (powMonoidHom p : E →* E).range
  letI : R.Characteristic := by
    rw [Subgroup.characteristic_iff_map_eq]
    intro e
    dsimp [R]
    exact MulEquiv.map_range_powMonoidHom e p
  let K : Subgroup G := R.map E.subtype
  have hKle : K ≤ E := by
    dsimp [K]
    exact Subgroup.map_subtype_le _
  by_cases hR : R = ⊥
  · intro x
    have hx : x ^ p ∈ R := by
      change x ^ p ∈ (powMonoidHom p : E →* E).range
      exact ⟨x, by simp⟩
    rw [hR] at hx
    exact Subgroup.mem_bot.mp hx
  · have hKnon : K ≠ ⊥ := by
      dsimp [K]
      intro hK
      apply hR
      exact (Subgroup.map_eq_bot_iff_of_injective
        R E.subtype_injective).mp hK
    have hKinv : ∀ g : G, g ∈ H → ∀ d : G, d ∈ K →
        g * d * g⁻¹ ∈ K := by
      dsimp [K]
      exact characteristic_map_subtype_invariant_under_normalizer
        E H R h.le_normalizer
    have hKE : K = E := le_antisymm hKle
      (h.2.2 K hKle hKnon hKinv)
    change R.map E.subtype = E at hKE
    have hRtop : R = ⊤ := by
      apply top_unique
      rw [← Subgroup.map_subtype_le_map_subtype]
      rw [hKE]
      exact Subgroup.map_subtype_le _
    have hsurj : Function.Surjective (powMonoidHom p : E →* E) :=
      MonoidHom.range_eq_top.mp (by simpa [R] using hRtop)
    have hinj : Function.Injective (powMonoidHom p : E →* E) :=
      Finite.injective_iff_surjective.mpr hsurj
    obtain ⟨n, hcard⟩ := hP.exists_card_eq
    have hn : n ≠ 0 := by
      intro hn
      subst n
      have hcardOne : Nat.card E = 1 := by simpa using hcard
      have hcardGt : 1 < Nat.card E := E.one_lt_card_iff_ne_bot.mpr h.ne_bot
      omega
    have hpCard : p ∣ Nat.card E := by
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

theorem isElementaryAbelian_of_isPGroup [Finite G]
    (h : IsMinimalNormalUnder E H) {p : ℕ} [Fact p.Prime]
    (hP : IsPGroup p E) :
    IsMulCommutative E ∧ ∀ x : E, x ^ p = 1 := by
  letI : Group.IsNilpotent E := hP.isNilpotent
  exact ⟨h.isMulCommutative_of_isSolvable,
    h.pow_eq_one_of_isPGroup hP⟩

end IsMinimalNormalUnder

end Submission.OddOrder.MathlibSupport
