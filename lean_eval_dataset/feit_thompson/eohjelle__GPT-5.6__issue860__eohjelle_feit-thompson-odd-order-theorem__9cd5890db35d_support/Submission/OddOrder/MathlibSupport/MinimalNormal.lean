import Submission.OddOrder.MathlibSupport.PCore

/-!
Minimal normal subgroups of finite solvable groups.

This supplies the first structural part of `BGsection1.minimal_solvable_abelem`:
a global minimal normal subgroup is abelian, and in the finite nontrivial case
it is a `p`-group for some prime `p`.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped IsMulCommutative

variable {G : Type*} [Group G]

/-- A nontrivial subgroup minimal among the normal subgroups of `G`. -/
def IsMinimalNormal (M : Subgroup G) : Prop :=
  M ≠ ⊥ ∧ M.Normal ∧
    ∀ N : Subgroup G, N.Normal → N ≤ M → N ≠ ⊥ → M ≤ N

namespace IsMinimalNormal

variable {M : Subgroup G}

theorem ne_bot (hM : IsMinimalNormal M) : M ≠ ⊥ :=
  hM.1

theorem normal (hM : IsMinimalNormal M) : M.Normal :=
  hM.2.1

theorem eq_of_normal_le (hM : IsMinimalNormal M) {N : Subgroup G}
    (hNnormal : N.Normal) (hNM : N ≤ M) (hN : N ≠ ⊥) : N = M :=
  le_antisymm hNM (hM.2.2 N hNnormal hNM hN)

theorem commutator_eq_bot [IsSolvable G] (hM : IsMinimalNormal M) :
    ⁅M, M⁆ = ⊥ := by
  letI : M.Normal := hM.normal
  have hproper : ⁅M, M⁆ < M :=
    IsSolvable.commutator_lt_of_ne_bot hM.ne_bot
  by_contra hcomm
  have heq : ⁅M, M⁆ = M := hM.eq_of_normal_le
    (by infer_instance) (Subgroup.commutator_le_left M M) hcomm
  exact (ne_of_lt hproper) heq

theorem isMulCommutative [IsSolvable G] (hM : IsMinimalNormal M) :
    IsMulCommutative M := by
  have hcent : M ≤ Subgroup.centralizer (M : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hM.commutator_eq_bot
  refine ⟨⟨fun x y ↦ ?_⟩⟩
  apply Subtype.ext
  exact hcent y.2 x x.2

/-- A finite minimal normal subgroup of a solvable group has prime-power
order.  The stronger elementary-abelian conclusion is ported separately. -/
theorem exists_prime_isPGroup [Finite G] [IsSolvable G]
    (hM : IsMinimalNormal M) :
    ∃ p : ℕ, p.Prime ∧ IsPGroup p M := by
  classical
  letI : M.Normal := hM.normal
  letI : IsMulCommutative M := hM.isMulCommutative
  have hcard : 1 < Nat.card M := M.one_lt_card_iff_ne_bot.mpr hM.ne_bot
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (ne_of_gt hcard)
  letI : Fact p.Prime := ⟨hp⟩
  let S : Sylow p M := Classical.choice inferInstance
  have hSnon : (S : Subgroup M) ≠ ⊥ := S.ne_bot_of_dvd_card hpdvd
  have hScore : (S : Subgroup M) ≤ pCore p M :=
    le_pCore S.isPGroup' (by infer_instance)
  have hcoreNon : pCore p M ≠ ⊥ := by
    intro hcore
    apply hSnon
    rw [hcore] at hScore
    exact le_bot_iff.mp hScore
  let K : Subgroup G := (pCore p M).map M.subtype
  have hKnormal : K.Normal := by
    dsimp [K]
    infer_instance
  have hKle : K ≤ M := by
    dsimp [K]
    exact Subgroup.map_subtype_le _
  have hKnon : K ≠ ⊥ := by
    dsimp [K]
    intro hK
    apply hcoreNon
    exact (Subgroup.map_eq_bot_iff_of_injective
      (pCore p M) M.subtype_injective).mp hK
  have hKM : K = M := hM.eq_of_normal_le hKnormal hKle hKnon
  refine ⟨p, hp, ?_⟩
  rw [← hKM]
  exact pCore_isPGroup.map M.subtype

/-- Full elementary-abelian form of `BGsection1.minnormal_solvable_abelem`:
for some prime `p`, `M` is an abelian `p`-group of exponent `p`. -/
theorem exists_prime_isPGroup_pow_eq_one [Finite G] [IsSolvable G]
    (hM : IsMinimalNormal M) :
    ∃ p : ℕ, p.Prime ∧ IsPGroup p M ∧ ∀ x : M, x ^ p = 1 := by
  classical
  obtain ⟨p, hp, hP⟩ := hM.exists_prime_isPGroup
  letI : Fact p.Prime := ⟨hp⟩
  letI : M.Normal := hM.normal
  letI : IsMulCommutative M := hM.isMulCommutative
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
  · refine ⟨p, hp, hP, ?_⟩
    intro x
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
      exact hp.ne_one hx.symm
    exfalso
    apply hxne
    apply hinj
    simp [powMonoidHom_apply, ← hx]

end IsMinimalNormal

end Submission.OddOrder.MathlibSupport
