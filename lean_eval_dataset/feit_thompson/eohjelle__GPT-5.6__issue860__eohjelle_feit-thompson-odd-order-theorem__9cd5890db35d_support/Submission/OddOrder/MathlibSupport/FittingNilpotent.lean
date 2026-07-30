import Submission.OddOrder.MathlibSupport.Fitting

/-!
Nilpotence of the finite Fitting p-core supremum.

Only primes dividing the ambient group order contribute a nontrivial p-core.
Those p-cores commute pairwise, have pairwise coprime cardinalities, and form
an internal direct product.  This proves the missing nilpotence half of the
finite Fitting construction without assuming the general normal-nilpotent
product theorem.
-/

namespace Submission.OddOrder.MathlibSupport

variable {G : Type*} [Group G]

theorem pCore_eq_bot_of_not_dvd_card [Finite G] {p : ℕ} [Fact p.Prime]
    (hp : ¬p ∣ Nat.card G) : pCore p G = ⊥ := by
  obtain ⟨n, hcard⟩ := (pCore_isPGroup (p := p) (G := G)).exists_card_eq
  have hn : n = 0 := by
    by_contra hn
    have hpcore : p ∣ Nat.card (pCore p G) := by
      rw [hcard]
      exact dvd_pow_self p hn
    exact hp (hpcore.trans (pCore p G).card_subgroup_dvd_card)
  rw [Subgroup.eq_bot_iff_card, hcard, hn, pow_zero]

instance fittingCore_isNilpotent [Finite G] :
    Group.IsNilpotent (fittingCore G) := by
  classical
  let ps := (Nat.card G).primeFactors
  let H : ps → Subgroup G := fun p ↦ pCore (p : ℕ) G
  letI : ∀ p, Fintype (H p) := fun _ ↦ Fintype.ofFinite _
  have hspan : (⨆ p, H p) = fittingCore G := by
    apply le_antisymm
    · apply iSup_le
      intro p
      letI : Fact (p : ℕ).Prime :=
        ⟨Nat.prime_of_mem_primeFactors p.property⟩
      exact pCore_le_fittingCore (G := G) (p : ℕ)
    · rw [fittingCore]
      apply iSup_le
      intro q
      letI : Fact (q : ℕ).Prime := ⟨q.property⟩
      by_cases hq : (q : ℕ) ∣ Nat.card G
      · let p : ps := ⟨q, Nat.mem_primeFactors.mpr
          ⟨q.property, hq, Nat.card_pos.ne'⟩⟩
        exact le_iSup H p
      · rw [pCore_eq_bot_of_not_dvd_card hq]
        exact bot_le
  have hcomm : Pairwise fun p₁ p₂ : ps ↦
      ∀ x y : G, x ∈ H p₁ → y ∈ H p₂ → Commute x y := by
    rintro ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩ hne
    have hp₁prime := Nat.prime_of_mem_primeFactors hp₁
    have hp₂prime := Nat.prime_of_mem_primeFactors hp₂
    letI : Fact p₁.Prime := ⟨hp₁prime⟩
    letI : Fact p₂.Prime := ⟨hp₂prime⟩
    have hne' : p₁ ≠ p₂ := by simpa using hne
    apply Subgroup.commute_of_normal_of_disjoint _ _
      (by infer_instance) (by infer_instance)
    exact IsPGroup.disjoint_of_ne p₁ p₂ hne' _ _
      (pCore_isPGroup (p := p₁) (G := G))
      (pCore_isPGroup (p := p₂) (G := G))
  have hcoprime : Pairwise fun p₁ p₂ : ps ↦
      Nat.Coprime (Fintype.card (H p₁)) (Fintype.card (H p₂)) := by
    rintro ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩ hne
    have hp₁prime := Nat.prime_of_mem_primeFactors hp₁
    have hp₂prime := Nat.prime_of_mem_primeFactors hp₂
    letI : Fact p₁.Prime := ⟨hp₁prime⟩
    letI : Fact p₂.Prime := ⟨hp₂prime⟩
    have hne' : p₁ ≠ p₂ := by simpa using hne
    simp only [← Nat.card_eq_fintype_card]
    exact IsPGroup.coprime_card_of_ne p₁ p₂ hne' _ _
      (pCore_isPGroup (p := p₁) (G := G))
      (pCore_isPGroup (p := p₂) (G := G))
  let φ := Subgroup.noncommPiCoprod hcomm
  have hφrange : φ.range = fittingCore G := by
    dsimp [φ]
    rw [Subgroup.noncommPiCoprod_range, hspan]
  have hφinj : Function.Injective φ := by
    apply Subgroup.injective_noncommPiCoprod_of_iSupIndep
    exact Subgroup.independent_of_coprime_order hcomm hcoprime
  let eRange : (∀ p, H p) ≃* φ.range :=
    MulEquiv.ofBijective φ.rangeRestrict
      ⟨MonoidHom.rangeRestrict_injective_iff.mpr hφinj,
        φ.rangeRestrict_surjective⟩
  let e : (∀ p, H p) ≃* fittingCore G :=
    eRange.trans (MulEquiv.subgroupCongr hφrange)
  letI : ∀ p, Group.IsNilpotent (H p) := fun p ↦ by
    letI : Fact (p : ℕ).Prime :=
      ⟨Nat.prime_of_mem_primeFactors p.property⟩
    exact (pCore_isPGroup (p := (p : ℕ)) (G := G)).isNilpotent
  exact Group.nilpotent_of_mulEquiv e

end Submission.OddOrder.MathlibSupport
