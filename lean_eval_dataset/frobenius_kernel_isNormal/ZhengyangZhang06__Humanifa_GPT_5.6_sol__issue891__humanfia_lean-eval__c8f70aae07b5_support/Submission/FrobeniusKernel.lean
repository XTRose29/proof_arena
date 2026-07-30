import Mathlib
import Submission.CharacterExtension

namespace Submission.Helpers

noncomputable section

section RegularCharacter

variable {H : Type} [Group H] [Fintype H] [DecidableEq H]

lemma leftRegular_character (h : H) :
    (Representation.leftRegular ℂ H).character h =
      if h = 1 then (Nat.card H : ℂ) else 0 := by
  classical
  let b := Finsupp.basisSingleOne (R := ℂ) (ι := H)
  rw [Representation.character, LinearMap.trace_eq_matrix_trace ℂ b, Matrix.trace]
  simp only [Matrix.diag_apply, LinearMap.toMatrix_apply, b,
    Finsupp.coe_basisSingleOne, Representation.ofMulAction_single]
  by_cases hh : h = 1
  · subst h
    simp [← Nat.card_eq_fintype_card]
  · rw [if_neg hh]
    apply Finset.sum_eq_zero
    intro x _
    simp [hh]

end RegularCharacter

section ExtendedRegularCharacter

variable {G X : Type} [Group G] [Fintype G] [Fintype X] [MulAction G X]

lemma extendedCharacter_leftRegular_of_frobeniusKernelPred
    (D : TransitiveActionData G X)
    (hfrob : ∀ g : G, g ≠ 1 → ∀ x y : X, g • x = x → g • y = y → x = y)
    {g : G} (hk : FrobeniusKernelPred (X := X) g) :
    extendedCharacter D hfrob (Representation.leftRegular ℂ D.Stabilizer) g =
      (Nat.card D.Stabilizer : ℂ) := by
  classical
  rcases hk with rfl | hfree
  · rw [extendedCharacter_one]
    simp [← Nat.card_eq_fintype_card]
  · rw [extendedCharacter_of_isFixedPointFree D hfrob _ hfree]
    simp [← Nat.card_eq_fintype_card]

lemma extendedCharacter_leftRegular_of_not_frobeniusKernelPred
    (D : TransitiveActionData G X)
    (hfrob : ∀ g : G, g ≠ 1 → ∀ x y : X, g • x = x → g • y = y → x = y)
    {g : G} (hk : ¬FrobeniusKernelPred (X := X) g) :
    extendedCharacter D hfrob (Representation.leftRegular ℂ D.Stabilizer) g = 0 := by
  classical
  rw [extendedCharacter]
  have hg : g ≠ 1 := by
    intro h
    apply hk
    exact Or.inl h
  have hfix : ∃ x : X, g • x = x := by
    by_contra h
    apply hk
    exact Or.inr fun x hx => h ⟨x, hx⟩
  let z := (D.fixedEquiv hfrob).symm
    (⟨g, hg, hfix⟩ : FixedNontrivial G X)
  rw [dif_pos ⟨hg, hfix⟩]
  change (Representation.leftRegular ℂ D.Stabilizer).character z.2.1 = 0
  rw [leftRegular_character, if_neg]
  intro he
  apply z.2.2
  exact congrArg Subtype.val he

end ExtendedRegularCharacter

section CyclicKernel

variable {G V : Type} [Group G] [Fintype G]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

lemma representation_apply_eq_one_of_character_eq_finrank_on_zpowers
    (rho : Representation ℂ G V) (g : G)
    (hchar : ∀ z : Subgroup.zpowers g,
      rho.character z.1 = Module.finrank ℂ V) :
    rho g = 1 := by
  classical
  let H := Subgroup.zpowers g
  let sigma : Representation ℂ H V := rho.comp H.subtype
  letI : Fintype H := Fintype.ofFinite H
  letI : Invertible (Nat.card H : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have havg := Representation.card_inv_mul_sum_char_eq_finrank sigma
  have hsum :
      ∑ z : H, sigma.character z =
        (Nat.card H : ℂ) * Module.finrank ℂ V := by
    simp_rw [show ∀ z : H, sigma.character z = rho.character z.1 from fun _ => rfl,
      hchar]
    simp [← Nat.card_eq_fintype_card]
  have hfinrankC :
      (Module.finrank ℂ sigma.invariants : ℂ) = Module.finrank ℂ V := by
    rw [← havg, hsum]
    field_simp
  have hfinrank :
      Module.finrank ℂ sigma.invariants = Module.finrank ℂ V := by
    exact_mod_cast hfinrankC
  have hinv : sigma.invariants = ⊤ := Submodule.eq_top_of_finrank_eq hfinrank
  apply LinearMap.ext
  intro v
  change rho g v = v
  have hv : v ∈ sigma.invariants := by rw [hinv]; trivial
  have hall := (Representation.mem_invariants sigma v).mp hv
  exact hall ⟨g, Subgroup.mem_zpowers g⟩

end CyclicKernel

section FrobeniusKernel

variable {G X : Type} [Group G] [Fintype G] [Fintype X] [MulAction G X]

theorem exists_normal_frobeniusKernel
    (D : TransitiveActionData G X)
    (hfrob : ∀ g : G, g ≠ 1 → ∀ x y : X, g • x = x → g • y = y → x = y) :
    ∃ N : Subgroup G, N.Normal ∧
      (N : Set G) = {1} ∪ {g : G | ∀ x : X, g • x ≠ x} := by
  classical
  let regular := Representation.leftRegular ℂ D.Stabilizer
  obtain ⟨C, hC⟩ := exists_fdRep_character_eq_extended D hfrob regular
  have hdimC : Module.finrank ℂ C = Nat.card D.Stabilizer := by
    have h := congrFun hC 1
    rw [FDRep.char_one, extendedCharacter_one] at h
    have hc :
        (Module.finrank ℂ C : ℂ) = (Nat.card D.Stabilizer : ℂ) := by
      simpa [regular, ← Nat.card_eq_fintype_card] using h
    exact_mod_cast hc
  refine ⟨C.ρ.ker, C.ρ.normal_ker, ?_⟩
  ext g
  change C.ρ g = 1 ↔ g ∈ ({1} ∪ {g : G | ∀ x : X, g • x ≠ x} : Set G)
  simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq]
  change C.ρ g = 1 ↔ FrobeniusKernelPred (X := X) g
  constructor
  · intro hg
    have hcharC : C.character g = Module.finrank ℂ C := by
      rw [FDRep.character, hg]
      simp
    have hext :
        extendedCharacter D hfrob regular g = (Nat.card D.Stabilizer : ℂ) := by
      calc
        extendedCharacter D hfrob regular g = C.character g := (congrFun hC g).symm
        _ = (Module.finrank ℂ C : ℂ) := hcharC
        _ = (Nat.card D.Stabilizer : ℂ) := by exact_mod_cast hdimC
    by_contra hk
    rw [extendedCharacter_leftRegular_of_not_frobeniusKernelPred D hfrob hk] at hext
    exact (Nat.cast_ne_zero.mpr Nat.card_pos.ne') hext.symm
  · rintro (rfl | hfree)
    · simp
    · apply representation_apply_eq_one_of_character_eq_finrank_on_zpowers C.ρ
      intro z
      have hzpow : z.1 ∈ Submonoid.powers g :=
        (mem_powers_iff_mem_zpowers (x := g) (y := z.1)).mpr z.2
      obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff z.1 g).mp hzpow
      have hkz : FrobeniusKernelPred (X := X) z.1 := by
        rcases pow_eq_one_or_isFixedPointFree hfrob hfree n with hpow | hpow
        · exact Or.inl (hn.symm.trans hpow)
        · exact Or.inr (by simpa [hn] using hpow)
      calc
        C.character z.1 = extendedCharacter D hfrob regular z.1 := congrFun hC z.1
        _ = (Nat.card D.Stabilizer : ℂ) :=
          extendedCharacter_leftRegular_of_frobeniusKernelPred D hfrob hkz
        _ = (Module.finrank ℂ C : ℂ) := by exact_mod_cast hdimC.symm

end FrobeniusKernel

end

end Submission.Helpers
