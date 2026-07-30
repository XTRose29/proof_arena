import Submission.OddOrder.PF.Section05.SubcoherentConstruction

/-!
# Elementary consequences of subcoherence

This file ports the part of `PFsection5.v` from `nil_coherent` through
`extend_coherent_with` (Peterfalvi (5.4), (5.5), and (5.6.3)).  Source
sequences are represented by sets, source integral spans by
`AddSubgroup.closure`, and target subsequences by finsets contained in the
corresponding finset `R chi`.
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped BigOperators Classical

universe u

local instance subcoherentPropertiesInvertibleCard
    {H : Type u} [Group H] [Fintype H] :
    Invertible (Nat.card H : ℂ) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

variable {L G : Type u} [Group L] [Fintype L] [Group G] [Fintype G]

namespace VirtualCharacter

/-- The integral degree of a virtual character. -/
noncomputable def integralDegree
    {H : Type u} [Group H] [Fintype H] :
    VirtualCharacter H ℂ →+ ℤ where
  toFun z := z.sum fun chi a ↦
    a * (Module.finrank ℂ chi.representation : ℤ)
  map_zero' := by simp
  map_add' z w := by
    apply Finsupp.sum_add_index'
    · intro chi
      simp
    · intro chi a b
      simp [add_mul]

@[simp]
theorem realize_one_eq_integralDegree
    {H : Type u} [Group H] [Fintype H]
    (z : VirtualCharacter H ℂ) :
    VirtualCharacter.realize z 1 = (integralDegree z : ℂ) := by
  classical
  induction z using Finsupp.induction with
  | zero => simp [integralDegree]
  | single_add chi a z hchi ha ih =>
      rw [VirtualCharacter.realize_add, map_add, ClassFunction.add_apply,
        VirtualCharacter.realize_single, ClassFunction.smul_apply,
        smul_eq_mul, ih]
      simp [integralDegree, hchi,
        IrreducibleCharacter.apply_one_eq_finrank]

theorem integralDegree_nonneg_of_isOrdinary
    {H : Type u} [Group H] [Fintype H]
    {z : VirtualCharacter H ℂ} (hz : z.IsOrdinary) :
    0 ≤ integralDegree z := by
  change 0 ≤ z.sum fun chi a ↦
    a * (Module.finrank ℂ chi.representation : ℤ)
  exact Finsupp.sum_nonneg fun chi _ ↦
    mul_nonneg (hz chi) (Int.natCast_nonneg _)

end VirtualCharacter

namespace ClassFunction

namespace IsOrdinaryCharacter

/-- Every ordinary character is a virtual character. -/
theorem isVirtual {H : Type u} [Group H]
    {phi : ClassFunction H ℂ} (hphi : IsOrdinaryCharacter phi) :
    IsVirtual phi := by
  obtain ⟨z, _, rfl⟩ := hphi
  exact ⟨z, rfl⟩

/-- The degree of an ordinary character is a natural number. -/
theorem exists_nat_degree {H : Type u} [Group H] [Fintype H]
    {phi : ClassFunction H ℂ} (hphi : IsOrdinaryCharacter phi) :
    ∃ d : ℕ, phi 1 = (d : ℂ) := by
  obtain ⟨z, hz, rfl⟩ := hphi
  let d := (VirtualCharacter.integralDegree z).toNat
  refine ⟨d, ?_⟩
  rw [VirtualCharacter.realize_one_eq_integralDegree]
  congr 1
  exact (Int.toNat_of_nonneg
    (VirtualCharacter.integralDegree_nonneg_of_isOrdinary hz)).symm

end IsOrdinaryCharacter

namespace IsVirtual

/-- The squared norm of a virtual character is a natural number. -/
theorem exists_nat_norm {H : Type u} [Group H] [Fintype H]
    {phi : ClassFunction H ℂ} (hphi : IsVirtual phi) :
    ∃ n : ℕ, characterPairing phi phi = (n : ℂ) := by
  obtain ⟨z, rfl⟩ := hphi
  refine ⟨(normSq z).toNat, ?_⟩
  rw [VirtualCharacter.characterPairing_realize]
  congr 1
  exact (Int.toNat_of_nonneg (normSq_nonneg z)).symm

end IsVirtual

end ClassFunction

/-- Order on squared norms, expressed without ordering the coefficient field.
`normLE phi psi` means that the norm of `psi` exceeds that of `phi` by a
natural number. -/
def normLE {H K : Type u} [Group H] [Fintype H] [Group K] [Fintype K]
    (phi : ClassFunction H ℂ) (psi : ClassFunction K ℂ) : Prop :=
  ∃ n : ℕ, characterPairing psi psi =
    characterPairing phi phi + (n : ℂ)

@[refl]
theorem normLE_refl {H : Type u} [Group H] [Fintype H]
    (phi : ClassFunction H ℂ) : normLE phi phi := by
  exact ⟨0, by simp⟩

theorem normLE_of_eq {H K : Type u}
    [Group H] [Fintype H] [Group K] [Fintype K]
    {phi : ClassFunction H ℂ} {psi : ClassFunction K ℂ}
    (h : characterPairing phi phi = characterPairing psi psi) :
    normLE phi psi := by
  exact ⟨0, by simpa using h.symm⟩

theorem normLE_zero_of_virtual {H K : Type u}
    [Group H] [Fintype H] [Group K] [Fintype K]
    {phi : ClassFunction K ℂ} (hphi : ClassFunction.IsVirtual phi) :
    normLE (0 : ClassFunction H ℂ) phi := by
  obtain ⟨n, hn⟩ := hphi.exists_nat_norm
  exact ⟨n, by simpa using hn⟩

/-- Pointwise orthogonality between two families. -/
def orthogonalFamilies {H : Type u} [Group H] [Fintype H]
    (A B : Set (ClassFunction H ℂ)) : Prop :=
  ∀ phi ∈ A, ∀ psi ∈ B, characterPairing phi psi = 0

private theorem pairing_neg_left
    {H : Type u} [Group H] [Fintype H]
    (phi psi : ClassFunction H ℂ) :
    characterPairing (-phi) psi = -characterPairing phi psi := by
  rw [← neg_one_smul ℂ phi, characterPairing_smul_left]
  ring

private theorem pairing_neg_right
    {H : Type u} [Group H] [Fintype H]
    (phi psi : ClassFunction H ℂ) :
    characterPairing phi (-psi) = -characterPairing phi psi := by
  rw [← neg_one_smul ℂ psi, characterPairing_smul_right]
  ring

private theorem pairing_sub_left
    {H : Type u} [Group H] [Fintype H]
    (phi psi theta : ClassFunction H ℂ) :
    characterPairing (phi - psi) theta =
      characterPairing phi theta - characterPairing psi theta := by
  rw [sub_eq_add_neg, characterPairing_add_left,
    pairing_neg_left, sub_eq_add_neg]

private theorem pairing_sub_right
    {H : Type u} [Group H] [Fintype H]
    (phi psi theta : ClassFunction H ℂ) :
    characterPairing phi (psi - theta) =
      characterPairing phi psi - characterPairing phi theta := by
  rw [sub_eq_add_neg, characterPairing_add_right,
    pairing_neg_right, sub_eq_add_neg]

private theorem pairing_zsmul_left
    {H : Type u} [Group H] [Fintype H]
    (a : ℤ) (phi psi : ClassFunction H ℂ) :
    characterPairing (a • phi) psi =
      (a : ℂ) * characterPairing phi psi := by
  rw [← Int.cast_smul_eq_zsmul ℂ]
  exact characterPairing_smul_left (a : ℂ) phi psi

private theorem pairing_zsmul_right
    {H : Type u} [Group H] [Fintype H]
    (a : ℤ) (phi psi : ClassFunction H ℂ) :
    characterPairing phi (a • psi) =
      (a : ℂ) * characterPairing phi psi := by
  rw [← Int.cast_smul_eq_zsmul ℂ]
  exact characterPairing_smul_right (a : ℂ) phi psi

private theorem pairing_finset_sum_left
    {H : Type u} [Group H] [Fintype H]
    {I : Type*} (s : Finset I) (f : I → ClassFunction H ℂ)
    (psi : ClassFunction H ℂ) :
    characterPairing (∑ i ∈ s, f i) psi =
      ∑ i ∈ s, characterPairing (f i) psi := by
  exact map_sum (characterPairingRight psi) (fun i ↦ f i) s

private theorem pairing_finset_sum_right
    {H : Type u} [Group H] [Fintype H]
    (phi : ClassFunction H ℂ) {I : Type*}
    (s : Finset I) (f : I → ClassFunction H ℂ) :
    characterPairing phi (∑ i ∈ s, f i) =
      ∑ i ∈ s, characterPairing phi (f i) := by
  exact map_sum (characterPairingLeft phi) (fun i ↦ f i) s

private theorem closure_mono_of_subset
    {S T : Set (ClassFunction L ℂ)} (hST : S ⊆ T) :
    AddSubgroup.closure S ≤ AddSubgroup.closure T :=
  AddSubgroup.closure_mono hST

/-- The empty family is coherent. -/
theorem nil_coherent
    (tau : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ) (A : Set L) :
    coherent (∅ : Set (ClassFunction L ℂ)) A tau := by
  refine ⟨0, ?_⟩
  have zero_of_mem {phi : ClassFunction L ℂ}
      (hphi : phi ∈ AddSubgroup.closure
        (∅ : Set (ClassFunction L ℂ))) : phi = 0 := by
    simpa using hphi
  exact
    { isometry := by
        intro phi hphi psi hpsi
        rw [zero_of_mem hphi, zero_of_mem hpsi]
        simp
      mapsToVirtual := by
        intro phi hphi
        rw [zero_of_mem hphi]
        exact ClassFunction.IsVirtual.zero
      agrees := by
        intro phi hphi _
        rw [zero_of_mem hphi]
        simp }

/-- A contragredient-closed subfamily of a subcoherent family is
subcoherent. -/
theorem subset_subcoherent
    {S S1 : Set (ClassFunction L ℂ)}
    {tau : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ}
    {R : ClassFunction L ℂ → Finset (ClassFunction G ℂ)}
    (hsub : subcoherent S tau R) (hS1 : cfConjC_subset S1 S) :
    subcoherent S1 tau R := by
  have hspan : AddSubgroup.closure S1 ≤ AddSubgroup.closure S :=
    closure_mono_of_subset hS1.1
  exact
    { finite := hsub.finite.subset hS1.1
      source_character := fun phi hphi ↦ hsub.source_character phi (hS1.1 hphi)
      source_virtual := fun phi hphi ↦ hsub.source_virtual phi (hS1.1 hphi)
      zero_not_mem := fun hzero ↦ hsub.zero_not_mem (hS1.1 hzero)
      degree_ne_zero := fun phi hphi ↦ hsub.degree_ne_zero phi (hS1.1 hphi)
      inverse_ne := fun phi hphi ↦ hsub.inverse_ne phi (hS1.1 hphi)
      inverse_mem := hS1.2
      tau_isometry := fun phi hphi hoff psi hpsi hpsiOff ↦
        hsub.tau_isometry phi (hspan hphi) hoff psi (hspan hpsi) hpsiOff
      tau_virtual := fun phi hphi hoff ↦
        hsub.tau_virtual phi (hspan hphi) hoff
      tau_supported := fun phi hphi hoff ↦
        hsub.tau_supported phi (hspan hphi) hoff
      pairwise_orthogonal := fun phi hphi psi hpsi hne ↦
        hsub.pairwise_orthogonal (hS1.1 hphi) (hS1.1 hpsi) hne
      image_virtual := fun xi hxi alpha halpha ↦
        hsub.image_virtual xi (hS1.1 hxi) alpha halpha
      image_orthonormal := fun xi hxi alpha halpha beta hbeta ↦
        hsub.image_orthonormal xi (hS1.1 hxi) alpha halpha beta hbeta
      tau_inverse_sub := fun xi hxi ↦
        hsub.tau_inverse_sub xi (hS1.1 hxi)
      image_orthogonal := fun xi hxi phi hphi hpair hpairInv alpha halpha beta hbeta ↦
        hsub.image_orthogonal xi (hS1.1 hxi) phi (hS1.1 hphi)
          hpair hpairInv alpha halpha beta hbeta }

/-- A member outside a subfamily is orthogonal to that subfamily. -/
theorem subset_ortho_subcoherent
    {S S1 : Set (ClassFunction L ℂ)}
    {tau : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ}
    {R : ClassFunction L ℂ → Finset (ClassFunction G ℂ)}
    (hsub : subcoherent S tau R) (hS1 : S1 ⊆ S)
    {chi : ClassFunction L ℂ} (hchi : chi ∈ S) (hchi1 : chi ∉ S1) :
    ∀ phi ∈ S1, characterPairing phi chi = 0 := by
  intro phi hphi
  exact hsub.pairwise_orthogonal (hS1 hphi) hchi
    (fun h ↦ hchi1 (h ▸ hphi))

/-- Orthogonal projection of a virtual character onto the integral span of
the orthonormal family `R chi`.  This is the set/finset form of source
`subcoherent_split`. -/
theorem subcoherent_split
    {S : Set (ClassFunction L ℂ)}
    {tau : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ}
    {R : ClassFunction L ℂ → Finset (ClassFunction G ℂ)}
    (hsub : subcoherent S tau R)
    {chi : ClassFunction L ℂ} (hchi : chi ∈ S)
    {beta : ClassFunction G ℂ} (hbeta : ClassFunction.IsVirtual beta) :
    ∃ X : ClassFunction G ℂ,
      X ∈ AddSubgroup.closure (↑(R chi) : Set (ClassFunction G ℂ)) ∧
      ClassFunction.IsVirtual X ∧
      ∃ Y : ClassFunction G ℂ,
        ClassFunction.IsVirtual Y ∧
        beta = X - Y ∧
        characterPairing X Y = 0 ∧
        ∀ alpha ∈ R chi, characterPairing Y alpha = 0 := by
  classical
  obtain ⟨b, hb⟩ := hbeta
  let z : ClassFunction G ℂ → VirtualCharacter G ℂ := fun alpha ↦
    if halpha : alpha ∈ R chi then
      Classical.choose (hsub.image_virtual chi hchi alpha halpha)
    else 0
  have hz (alpha : ClassFunction G ℂ) (halpha : alpha ∈ R chi) :
      VirtualCharacter.realize (z alpha) = alpha := by
    simp only [z, dif_pos halpha]
    exact Classical.choose_spec
      (hsub.image_virtual chi hchi alpha halpha)
  let a : ClassFunction G ℂ → ℤ := fun alpha ↦ coeffDot b (z alpha)
  let X : ClassFunction G ℂ := ∑ alpha ∈ R chi, a alpha • alpha
  let Y : ClassFunction G ℂ := X - beta
  have hXspan :
      X ∈ AddSubgroup.closure
        (↑(R chi) : Set (ClassFunction G ℂ)) := by
    apply AddSubgroup.sum_mem
    intro alpha halpha
    exact (AddSubgroup.closure
      (↑(R chi) : Set (ClassFunction G ℂ))).zsmul_mem
        (AddSubgroup.subset_closure halpha) (a alpha)
  have hXvirtual : ClassFunction.IsVirtual X := by
    refine ⟨∑ alpha ∈ R chi, a alpha • z alpha, ?_⟩
    simp only [X, map_sum]
    apply Finset.sum_congr rfl
    intro alpha halpha
    rw [map_zsmul, hz alpha halpha]
  have hYvirtual : ClassFunction.IsVirtual Y := by
    exact hXvirtual.sub ⟨b, hb⟩
  have hbetaPair (alpha : ClassFunction G ℂ) (halpha : alpha ∈ R chi) :
      characterPairing beta alpha = (a alpha : ℂ) := by
    change characterPairing beta alpha =
      ((coeffDot b (z alpha) : ℤ) : ℂ)
    calc
      characterPairing beta alpha =
          characterPairing (VirtualCharacter.realize b)
            (VirtualCharacter.realize (z alpha)) := by
        rw [hb, hz alpha halpha]
      _ = ((coeffDot b (z alpha) : ℤ) : ℂ) :=
        VirtualCharacter.characterPairing_realize b (z alpha)
  have hXPair (alpha : ClassFunction G ℂ) (halpha : alpha ∈ R chi) :
      characterPairing X alpha = (a alpha : ℂ) := by
    simp only [X]
    rw [pairing_finset_sum_left]
    rw [Finset.sum_eq_single alpha]
    · rw [pairing_zsmul_left,
        hsub.image_orthonormal chi hchi alpha halpha alpha halpha,
        if_pos rfl, mul_one]
    · intro gamma hgamma hne
      rw [pairing_zsmul_left,
        hsub.image_orthonormal chi hchi gamma hgamma alpha halpha,
        if_neg hne, mul_zero]
    · exact fun h ↦ (h halpha).elim
  have hYorth (alpha : ClassFunction G ℂ) (halpha : alpha ∈ R chi) :
      characterPairing Y alpha = 0 := by
    simp only [Y]
    rw [pairing_sub_left, hXPair alpha halpha,
      hbetaPair alpha halpha, sub_self]
  have hXY : characterPairing X Y = 0 := by
    simp only [X]
    rw [pairing_finset_sum_left]
    apply Finset.sum_eq_zero
    intro alpha halpha
    rw [pairing_zsmul_left, characterPairing_comm,
      hYorth alpha halpha, mul_zero]
  refine ⟨X, hXspan, hXvirtual, Y, hYvirtual, ?_, hXY, hYorth⟩
  simp only [Y]
  abel

private theorem virtual_eq_zero_of_pairing_self_eq_zero
    {H : Type u} [Group H] [Fintype H]
    {phi : ClassFunction H ℂ} (hphi : ClassFunction.IsVirtual phi)
    (hzero : characterPairing phi phi = 0) : phi = 0 := by
  obtain ⟨z, hz⟩ := hphi
  have hcast : ((normSq z : ℤ) : ℂ) = 0 := by
    rw [← VirtualCharacter.characterPairing_realize_self, hz]
    exact hzero
  have hnorm0 : normSq z = 0 := by
    apply Int.cast_injective (α := ℂ)
    simpa only [Int.cast_zero] using hcast
  have hz0 : z = 0 := (normSq_eq_zero_iff z).mp hnorm0
  rw [← hz, hz0]
  simp

private theorem pairing_self_sub_of_orthogonal
    {H : Type u} [Group H] [Fintype H]
    (phi psi : ClassFunction H ℂ)
    (horth : characterPairing phi psi = 0) :
    characterPairing (phi - psi) (phi - psi) =
      characterPairing phi phi + characterPairing psi psi := by
  rw [pairing_sub_left, pairing_sub_right, pairing_sub_right,
    horth, characterPairing_comm psi phi, horth]
  ring

private theorem pairing_self_add_of_orthogonal
    {H : Type u} [Group H] [Fintype H]
    (phi psi : ClassFunction H ℂ)
    (horth : characterPairing phi psi = 0) :
    characterPairing (phi + psi) (phi + psi) =
      characterPairing phi phi + characterPairing psi psi := by
  rw [characterPairing_add_left, characterPairing_add_right,
    characterPairing_add_right, horth,
    characterPairing_comm psi phi, horth]
  ring

private theorem int_sub_self_nonneg (a : ℤ) : 0 ≤ a ^ 2 - a := by
  nlinarith [mul_self_nonneg a]

private theorem int_sq_sub_self_eq_zero_iff (a : ℤ) :
    a ^ 2 - a = 0 ↔ a = 0 ∨ a = 1 := by
  constructor
  · intro h
    have : a * (a - 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with ha | ha
    · exact Or.inl ha
    · exact Or.inr (sub_eq_zero.mp ha)
  · rintro (rfl | rfl) <;> norm_num

private theorem cast_toNat_of_nonneg (a : ℤ) (ha : 0 ≤ a) :
    ((a.toNat : ℕ) : ℂ) = (a : ℂ) := by
  exact_mod_cast Int.toNat_of_nonneg ha

/-- Peterfalvi (5.4).  The conclusion is phrased using `normLE`, so no order
on `ℂ` is required.  As in the corrected source proof, it is enough to assume
that `X` and `Y` are orthogonal; membership of `X` in the span of `R chi` is
not an input. -/
theorem subcoherent_norm
    {S : Set (ClassFunction L ℂ)}
    {tau : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ}
    {R : ClassFunction L ℂ → Finset (ClassFunction G ℂ)}
    (hsub : subcoherent S tau R)
    {chi psi : ClassFunction L ℂ}
    (hchi : chi ∈ S) (hpsiVirtual : ClassFunction.IsVirtual psi)
    (hchiPsi : characterPairing chi psi = 0)
    (hchiInvPsi :
      characterPairing (ClassFunction.inverseLinear chi) psi = 0)
    (tau1 : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ)
    (hiso : ∀ u ∈ AddSubgroup.closure
        ({chi - psi,
          chi - ClassFunction.inverseLinear chi} : Set (ClassFunction L ℂ)),
      ∀ v ∈ AddSubgroup.closure
        ({chi - psi,
          chi - ClassFunction.inverseLinear chi} : Set (ClassFunction L ℂ)),
        characterPairing (tau1 u) (tau1 v) = characterPairing u v)
    (htauVirtual : ∀ u ∈ AddSubgroup.closure
        ({chi - psi,
          chi - ClassFunction.inverseLinear chi} : Set (ClassFunction L ℂ)),
        ClassFunction.IsVirtual (tau1 u))
    (htauDiff :
      tau1 (chi - ClassFunction.inverseLinear chi) =
        tau (chi - ClassFunction.inverseLinear chi))
    {X Y : ClassFunction G ℂ}
    (hXVirtual : ClassFunction.IsVirtual X)
    (hYVirtual : ClassFunction.IsVirtual Y)
    (hdecomp : tau1 (chi - psi) = X - Y)
    (hXY : characterPairing X Y = 0)
    (hYR : ∀ alpha ∈ R chi, characterPairing Y alpha = 0) :
    normLE chi X ∧
      (normLE psi Y →
        characterPairing X X = characterPairing chi chi ∧
        characterPairing Y Y = characterPairing psi psi ∧
        ∃ E : Finset (ClassFunction G ℂ),
          E ⊆ R chi ∧ X = ∑ alpha ∈ E, alpha) := by
  classical
  let S0 : Set (ClassFunction L ℂ) :=
    {chi - psi, chi - ClassFunction.inverseLinear chi}
  have hfirst : chi - psi ∈ AddSubgroup.closure S0 :=
    AddSubgroup.subset_closure (by simp [S0])
  have hsecond : chi - ClassFunction.inverseLinear chi ∈
      AddSubgroup.closure S0 :=
    AddSubgroup.subset_closure (by simp [S0])
  let beta : ClassFunction G ℂ := tau1 (chi - psi)
  have hbetaVirtual : ClassFunction.IsVirtual beta :=
    htauVirtual _ hfirst
  obtain ⟨b, hb⟩ := hbetaVirtual
  let z : ClassFunction G ℂ → VirtualCharacter G ℂ := fun alpha ↦
    if halpha : alpha ∈ R chi then
      Classical.choose (hsub.image_virtual chi hchi alpha halpha)
    else 0
  have hz (alpha : ClassFunction G ℂ) (halpha : alpha ∈ R chi) :
      VirtualCharacter.realize (z alpha) = alpha := by
    simp only [z, dif_pos halpha]
    exact Classical.choose_spec
      (hsub.image_virtual chi hchi alpha halpha)
  let a : ClassFunction G ℂ → ℤ := fun alpha ↦ coeffDot b (z alpha)
  let X1 : ClassFunction G ℂ := ∑ alpha ∈ R chi, a alpha • alpha
  let Y1 : ClassFunction G ℂ := X1 - beta
  have hX1Virtual : ClassFunction.IsVirtual X1 := by
    refine ⟨∑ alpha ∈ R chi, a alpha • z alpha, ?_⟩
    simp only [X1, map_sum]
    apply Finset.sum_congr rfl
    intro alpha halpha
    rw [map_zsmul, hz alpha halpha]
  have hY1Virtual : ClassFunction.IsVirtual Y1 :=
    hX1Virtual.sub ⟨b, hb⟩
  have hbetaPair (alpha : ClassFunction G ℂ) (halpha : alpha ∈ R chi) :
      characterPairing beta alpha = (a alpha : ℂ) := by
    change characterPairing beta alpha =
      ((coeffDot b (z alpha) : ℤ) : ℂ)
    calc
      characterPairing beta alpha =
          characterPairing (VirtualCharacter.realize b)
            (VirtualCharacter.realize (z alpha)) := by
        rw [hb, hz alpha halpha]
      _ = ((coeffDot b (z alpha) : ℤ) : ℂ) :=
        VirtualCharacter.characterPairing_realize b (z alpha)
  have hX1Pair (alpha : ClassFunction G ℂ) (halpha : alpha ∈ R chi) :
      characterPairing X1 alpha = (a alpha : ℂ) := by
    simp only [X1]
    rw [pairing_finset_sum_left, Finset.sum_eq_single alpha]
    · rw [pairing_zsmul_left,
        hsub.image_orthonormal chi hchi alpha halpha alpha halpha,
        if_pos rfl, mul_one]
    · intro gamma hgamma hne
      rw [pairing_zsmul_left,
        hsub.image_orthonormal chi hchi gamma hgamma alpha halpha,
        if_neg hne, mul_zero]
    · exact fun h ↦ (h halpha).elim
  have hY1R (alpha : ClassFunction G ℂ) (halpha : alpha ∈ R chi) :
      characterPairing Y1 alpha = 0 := by
    simp only [Y1]
    rw [pairing_sub_left, hX1Pair alpha halpha,
      hbetaPair alpha halpha, sub_self]
  have hX1Y1 : characterPairing X1 Y1 = 0 := by
    simp only [X1]
    rw [pairing_finset_sum_left]
    apply Finset.sum_eq_zero
    intro alpha halpha
    rw [pairing_zsmul_left, characterPairing_comm,
      hY1R alpha halpha, mul_zero]
  have hX1Norm : characterPairing X1 X1 =
      ((∑ alpha ∈ R chi, a alpha ^ 2 : ℤ) : ℂ) := by
    simp only [X1]
    rw [pairing_finset_sum_left]
    simp only [pairing_zsmul_left]
    rw [Int.cast_sum]
    apply Finset.sum_congr rfl
    intro alpha halpha
    rw [characterPairing_comm, hX1Pair alpha halpha]
    push_cast
    ring
  have hchiInv :
      characterPairing chi (ClassFunction.inverseLinear chi) = 0 :=
    hsub.pairwise_orthogonal hchi (hsub.inverse_mem chi hchi)
      (hsub.inverse_ne chi hchi).symm
  have hsourcePair :
      characterPairing (chi - psi)
          (chi - ClassFunction.inverseLinear chi) =
        characterPairing chi chi := by
    rw [pairing_sub_left, pairing_sub_right, pairing_sub_right,
      hchiInv, characterPairing_comm psi chi, hchiPsi,
      characterPairing_comm psi (ClassFunction.inverseLinear chi),
      hchiInvPsi]
    ring
  have hchiNorm : characterPairing chi chi =
      ((∑ alpha ∈ R chi, a alpha : ℤ) : ℂ) := by
    calc
      characterPairing chi chi =
          characterPairing (chi - psi)
            (chi - ClassFunction.inverseLinear chi) := hsourcePair.symm
      _ = characterPairing beta
          (tau1 (chi - ClassFunction.inverseLinear chi)) :=
        (hiso _ hfirst _ hsecond).symm
      _ = characterPairing beta
          (tau (chi - ClassFunction.inverseLinear chi)) := by rw [htauDiff]
      _ = characterPairing beta (∑ alpha ∈ R chi, alpha) := by
        rw [hsub.tau_inverse_sub chi hchi]
      _ = ∑ alpha ∈ R chi, characterPairing beta alpha := by
        rw [pairing_finset_sum_right]
      _ = ∑ alpha ∈ R chi, (a alpha : ℂ) := by
        apply Finset.sum_congr rfl
        exact fun alpha halpha ↦ hbetaPair alpha halpha
      _ = ((∑ alpha ∈ R chi, a alpha : ℤ) : ℂ) := by
        push_cast
        rfl
  let D : ClassFunction G ℂ := X - X1
  have hbetaDecomp : beta = X - Y := by
    simpa only [beta] using hdecomp
  have hDorthR (alpha : ClassFunction G ℂ) (halpha : alpha ∈ R chi) :
      characterPairing D alpha = 0 := by
    have hXPair : characterPairing X alpha = characterPairing beta alpha := by
      rw [hbetaDecomp, pairing_sub_left, hYR alpha halpha, sub_zero]
    simp only [D]
    rw [pairing_sub_left, hXPair, hbetaPair alpha halpha,
      hX1Pair alpha halpha, sub_self]
  have hX1D : characterPairing X1 D = 0 := by
    simp only [X1]
    rw [pairing_finset_sum_left]
    apply Finset.sum_eq_zero
    intro alpha halpha
    rw [pairing_zsmul_left, characterPairing_comm,
      hDorthR alpha halpha, mul_zero]
  have hDVirtual : ClassFunction.IsVirtual D :=
    hXVirtual.sub hX1Virtual
  obtain ⟨nD, hnD⟩ := hDVirtual.exists_nat_norm
  have hXeq : X = X1 + D := by
    simp only [D]
    abel
  have hXNorm : characterPairing X X =
      ((∑ alpha ∈ R chi, a alpha ^ 2 : ℤ) : ℂ) + (nD : ℂ) := by
    rw [hXeq, pairing_self_add_of_orthogonal X1 D hX1D,
      hX1Norm, hnD]
  let defect : ℤ := ∑ alpha ∈ R chi, (a alpha ^ 2 - a alpha)
  have hdefectNonneg : 0 ≤ defect := by
    apply Finset.sum_nonneg
    intro alpha halpha
    exact int_sub_self_nonneg (a alpha)
  let gap : ℕ := defect.toNat + nD
  have hXGap : characterPairing X X =
      characterPairing chi chi + (gap : ℂ) := by
    rw [hXNorm, hchiNorm]
    simp only [gap, Nat.cast_add]
    rw [cast_toNat_of_nonneg defect hdefectNonneg]
    simp only [defect, Finset.sum_sub_distrib, Int.cast_sum, Int.cast_sub,
      Int.cast_pow]
    push_cast
    ring
  refine ⟨⟨gap, hXGap⟩, ?_⟩
  rintro ⟨nY, hYGap⟩
  have hbetaNorm : characterPairing beta beta =
      characterPairing (chi - psi) (chi - psi) :=
    hiso _ hfirst _ hfirst
  have hsourceNorm :
      characterPairing (chi - psi) (chi - psi) =
        characterPairing chi chi + characterPairing psi psi :=
    pairing_self_sub_of_orthogonal chi psi hchiPsi
  have htargetNorm : characterPairing beta beta =
      characterPairing X X + characterPairing Y Y := by
    rw [hbetaDecomp,
      pairing_self_sub_of_orthogonal X Y hXY]
  have htotal : characterPairing X X + characterPairing Y Y =
      characterPairing chi chi + characterPairing psi psi := by
    rw [← htargetNorm, hbetaNorm, hsourceNorm]
  have hgapCast : ((gap + nY : ℕ) : ℂ) = 0 := by
    rw [Nat.cast_add]
    rw [hXGap, hYGap] at htotal
    linear_combination htotal
  have hgapNat : gap + nY = 0 := by
    exact_mod_cast hgapCast
  have hgap0 : gap = 0 := by omega
  have hnY0 : nY = 0 := by omega
  have hXNormEq : characterPairing X X = characterPairing chi chi := by
    rw [hXGap, hgap0]
    simp
  have hYNormEq : characterPairing Y Y = characterPairing psi psi := by
    rw [hYGap, hnY0]
    simp
  refine ⟨hXNormEq, hYNormEq, ?_⟩
  have hgapParts : defect.toNat + nD = 0 := by
    simpa only [gap] using hgap0
  have hdefectNat0 : defect.toNat = 0 := by omega
  have hnD0 : nD = 0 := by omega
  have hD0 : D = 0 := by
    apply virtual_eq_zero_of_pairing_self_eq_zero hDVirtual
    rw [hnD, hnD0]
    simp
  have hdefect0 : defect = 0 := by
    apply le_antisymm
    · exact Int.toNat_eq_zero.mp hdefectNat0
    · exact hdefectNonneg
  have ha01 (alpha : ClassFunction G ℂ) (halpha : alpha ∈ R chi) :
      a alpha = 0 ∨ a alpha = 1 := by
    apply (int_sq_sub_self_eq_zero_iff (a alpha)).mp
    have hterms := (Finset.sum_eq_zero_iff_of_nonneg
      (fun gamma _ ↦ int_sub_self_nonneg (a gamma))).mp hdefect0
    exact hterms alpha halpha
  let E : Finset (ClassFunction G ℂ) :=
    (R chi).filter fun alpha ↦ a alpha = 1
  refine ⟨E, ?_, ?_⟩
  · intro alpha halpha
    exact (Finset.mem_filter.mp halpha).1
  · rw [hXeq, hD0, add_zero]
    simp only [X1]
    simp only [E, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro alpha halpha
    rcases ha01 alpha halpha with ha | ha
    · simp [ha]
    · simp [ha]

private theorem inverseLinear_involutive
    {H : Type u} [Group H] (phi : ClassFunction H ℂ) :
    ClassFunction.inverseLinear (ClassFunction.inverseLinear phi) = phi := by
  ext x
  simp

private theorem inverse_sub_supported
    (phi : ClassFunction L ℂ) :
    phi - ClassFunction.inverseLinear phi ∈
      ClassFunction.supportedOn (nonidentitySet L) := by
  rw [ClassFunction.mem_supportedOn_iff]
  intro x hx
  have hxone : x = 1 := by
    simpa [nonidentitySet] using not_not.mp hx
  subst x
  simp

/-- Peterfalvi (5.5): an isometry which has the prescribed value on the
contragredient difference sends `chi` to a sum of a subfamily of `R chi`. -/
theorem coherent_sum_subseq
    {S : Set (ClassFunction L ℂ)}
    {tau : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ}
    {R : ClassFunction L ℂ → Finset (ClassFunction G ℂ)}
    (hsub : subcoherent S tau R)
    {chi : ClassFunction L ℂ} (hchi : chi ∈ S)
    (tau1 : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ)
    (hiso : ∀ u ∈ AddSubgroup.closure
        ({chi, ClassFunction.inverseLinear chi} : Set (ClassFunction L ℂ)),
      ∀ v ∈ AddSubgroup.closure
        ({chi, ClassFunction.inverseLinear chi} : Set (ClassFunction L ℂ)),
        characterPairing (tau1 u) (tau1 v) = characterPairing u v)
    (htauVirtual : ∀ u ∈ AddSubgroup.closure
        ({chi, ClassFunction.inverseLinear chi} : Set (ClassFunction L ℂ)),
        ClassFunction.IsVirtual (tau1 u))
    (htauDiff :
      tau1 (chi - ClassFunction.inverseLinear chi) =
        tau (chi - ClassFunction.inverseLinear chi)) :
    ∃ E : Finset (ClassFunction G ℂ),
      E ⊆ R chi ∧ tau1 chi = ∑ alpha ∈ E, alpha := by
  let T : Set (ClassFunction L ℂ) :=
    {chi, ClassFunction.inverseLinear chi}
  have hchiT : chi ∈ AddSubgroup.closure T :=
    AddSubgroup.subset_closure (by simp [T])
  have hinvT : ClassFunction.inverseLinear chi ∈ AddSubgroup.closure T :=
    AddSubgroup.subset_closure (by simp [T])
  have hdiffT : chi - ClassFunction.inverseLinear chi ∈
      AddSubgroup.closure T :=
    (AddSubgroup.closure T).sub_mem hchiT hinvT
  have hbetaVirtual : ClassFunction.IsVirtual (tau1 chi) :=
    htauVirtual _ hchiT
  obtain ⟨X, _, hXVirtual, Y, hYVirtual, hsplit, hXY, hYR⟩ :=
    subcoherent_split hsub hchi hbetaVirtual
  have hsmall : AddSubgroup.closure
      ({chi - (0 : ClassFunction L ℂ),
        chi - ClassFunction.inverseLinear chi} : Set (ClassFunction L ℂ)) ≤
      AddSubgroup.closure T := by
    refine (AddSubgroup.closure_le (AddSubgroup.closure T)).2 ?_
    intro u hu
    rcases hu with (rfl | rfl)
    · simpa using hchiT
    · exact hdiffT
  have hnorm := subcoherent_norm hsub hchi
    (ClassFunction.IsVirtual.zero :
      ClassFunction.IsVirtual (0 : ClassFunction L ℂ))
    (by simp) (by simp) tau1
    (fun u hu v hv ↦ hiso u (hsmall hu) v (hsmall hv))
    (fun u hu ↦ htauVirtual u (hsmall hu)) htauDiff
    hXVirtual hYVirtual
    (by simpa using hsplit) hXY hYR
  have hzeroLE : normLE (0 : ClassFunction L ℂ) Y :=
    normLE_zero_of_virtual hYVirtual
  obtain ⟨_, hYnorm, E, hER, hXsum⟩ := hnorm.2 hzeroLE
  have hY0 : Y = 0 := by
    apply virtual_eq_zero_of_pairing_self_eq_zero hYVirtual
    simpa using hYnorm
  refine ⟨E, hER, ?_⟩
  calc
    tau1 chi = X - Y := hsplit
    _ = X := by rw [hY0, sub_zero]
    _ = ∑ alpha ∈ E, alpha := hXsum

/-- Coherence version of (5.5), convenient for later applications. -/
theorem mem_coherent_sum_subseq
    {S S1 : Set (ClassFunction L ℂ)}
    {tau tau1 : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ}
    {R : ClassFunction L ℂ → Finset (ClassFunction G ℂ)}
    (hsub : subcoherent S tau R) (hS1 : cfConjC_subset S1 S)
    (hcoh : coherent_with S1 (nonidentitySet L) tau tau1)
    {chi : ClassFunction L ℂ} (hchi : chi ∈ S1) :
    ∃ E : Finset (ClassFunction G ℂ),
      E ⊆ R chi ∧ tau1 chi = ∑ alpha ∈ E, alpha := by
  have hinv : ClassFunction.inverseLinear chi ∈ S1 :=
    hS1.2 chi hchi
  have hpairSubset :
      ({chi, ClassFunction.inverseLinear chi} : Set (ClassFunction L ℂ)) ⊆ S1 :=
    Set.pair_subset hchi hinv
  have hspan : AddSubgroup.closure
      ({chi, ClassFunction.inverseLinear chi} : Set (ClassFunction L ℂ)) ≤
      AddSubgroup.closure S1 :=
    AddSubgroup.closure_mono hpairSubset
  have hdiff : chi - ClassFunction.inverseLinear chi ∈
      AddSubgroup.closure S1 :=
    (AddSubgroup.closure S1).sub_mem
      (AddSubgroup.subset_closure hchi)
      (AddSubgroup.subset_closure hinv)
  exact coherent_sum_subseq hsub (hS1.1 hchi) tau1
    (fun u hu v hv ↦ hcoh.isometry u (hspan hu) v (hspan hv))
    (fun u hu ↦ hcoh.mapsToVirtual u (hspan hu))
    (hcoh.agrees _ hdiff (inverse_sub_supported chi))

/-- Images of a coherent subfamily are orthogonal to the target family of a
source character outside that subfamily.  The source only states this for
generators; closure under integral combinations is included here because it
is what the bridge construction uses. -/
theorem coherent_ortho_supp
    {S S1 : Set (ClassFunction L ℂ)}
    {tau tau1 : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ}
    {R : ClassFunction L ℂ → Finset (ClassFunction G ℂ)}
    (hsub : subcoherent S tau R) (hS1 : cfConjC_subset S1 S)
    (hcoh : coherent_with S1 (nonidentitySet L) tau tau1)
    {chi : ClassFunction L ℂ} (hchi : chi ∈ S) (hchi1 : chi ∉ S1) :
    orthogonalFamilies (tau1 '' AddSubgroup.closure S1)
      (↑(R chi) : Set (ClassFunction G ℂ)) := by
  have hinvChi : ClassFunction.inverseLinear chi ∈ S :=
    hsub.inverse_mem chi hchi
  have hinvChiNot : ClassFunction.inverseLinear chi ∉ S1 := by
    intro hinvMem
    have := hS1.2 _ hinvMem
    rw [inverseLinear_involutive] at this
    exact hchi1 this
  have hgenerator : ∀ phi ∈ S1, ∀ alpha ∈ R chi,
      characterPairing (tau1 phi) alpha = 0 := by
    intro phi hphi alpha halpha
    obtain ⟨E, hER, hsum⟩ :=
      mem_coherent_sum_subseq hsub hS1 hcoh hphi
    rw [hsum, pairing_finset_sum_left]
    apply Finset.sum_eq_zero
    intro beta hbeta
    have hbetaR : beta ∈ R phi := hER hbeta
    have hphiChi : characterPairing phi chi = 0 :=
      subset_ortho_subcoherent hsub hS1.1 hchi hchi1 phi hphi
    have hphiInv :
        characterPairing phi (ClassFunction.inverseLinear chi) = 0 :=
      hsub.pairwise_orthogonal (hS1.1 hphi) hinvChi
        (fun heq ↦ hinvChiNot (heq ▸ hphi))
    exact hsub.image_orthogonal chi hchi phi (hS1.1 hphi)
      hphiChi hphiInv beta hbetaR alpha halpha
  rintro _ ⟨u, hu, rfl⟩ alpha halpha
  induction hu using AddSubgroup.closure_induction with
  | mem phi hphi => exact hgenerator phi hphi alpha halpha
  | zero => simp
  | add phi psi hphi hpsi ihphi ihpsi =>
      simp only [map_add, characterPairing_add_left, ihphi, ihpsi, add_zero]
  | neg phi hphi ihphi =>
      simp only [map_neg, pairing_neg_left, ihphi, neg_zero]

/-- Coherent images of two disjoint contragredient-closed subfamilies are
orthogonal, including on their integral spans. -/
theorem coherent_ortho
    {S S1 S2 : Set (ClassFunction L ℂ)}
    {tau tau1 tau2 : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ}
    {R : ClassFunction L ℂ → Finset (ClassFunction G ℂ)}
    (hsub : subcoherent S tau R)
    (hS1 : cfConjC_subset S1 S)
    (hcoh1 : coherent_with S1 (nonidentitySet L) tau tau1)
    (hS2 : cfConjC_subset S2 S)
    (hcoh2 : coherent_with S2 (nonidentitySet L) tau tau2)
    (hdisjoint : S2 ⊆ S1ᶜ) :
    orthogonalFamilies (tau1 '' AddSubgroup.closure S1)
      (tau2 '' AddSubgroup.closure S2) := by
  have hgenerator : ∀ u ∈ AddSubgroup.closure S1,
      ∀ phi ∈ S2, characterPairing (tau1 u) (tau2 phi) = 0 := by
    intro u hu phi hphi
    obtain ⟨E, hER, hsum⟩ :=
      mem_coherent_sum_subseq hsub hS2 hcoh2 hphi
    rw [hsum, pairing_finset_sum_right]
    apply Finset.sum_eq_zero
    intro alpha halpha
    exact coherent_ortho_supp hsub hS1 hcoh1 (hS2.1 hphi)
      (hdisjoint hphi) (tau1 u) ⟨u, hu, rfl⟩ alpha (hER halpha)
  rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
  induction hv using AddSubgroup.closure_induction with
  | mem phi hphi => exact hgenerator u hu phi hphi
  | zero => simp
  | add phi psi hphi hpsi ihphi ihpsi =>
      simp only [map_add, characterPairing_add_right, ihphi, ihpsi, add_zero]
  | neg phi hphi ihphi =>
      simp only [map_neg, pairing_neg_right, ihphi, neg_zero]

private theorem virtual_of_mem_closure
    {H : Type u} [Group H] [Fintype H]
    {S : Set (ClassFunction H ℂ)}
    (hS : ∀ phi ∈ S, ClassFunction.IsVirtual phi)
    {u : ClassFunction H ℂ} (hu : u ∈ AddSubgroup.closure S) :
    ClassFunction.IsVirtual u := by
  induction hu using AddSubgroup.closure_induction with
  | mem phi hphi => exact hS phi hphi
  | zero => exact ClassFunction.IsVirtual.zero
  | add phi psi hphi hpsi ihphi ihpsi => exact ihphi.add ihpsi
  | neg phi hphi ihphi => exact ihphi.neg

private theorem pairing_self_ne_zero_of_virtual_ne_zero
    {H : Type u} [Group H] [Fintype H]
    {phi : ClassFunction H ℂ} (hphi : ClassFunction.IsVirtual phi)
    (hphi0 : phi ≠ 0) : characterPairing phi phi ≠ 0 := by
  intro hzero
  exact hphi0 (virtual_eq_zero_of_pairing_self_eq_zero hphi hzero)

/-- Glue two coherent isometries on disjoint subfamilies.  The equality on a
single degree-balancing difference `chi - phi` is enough to make the glued
map agree with `tau` on all degree-zero integral combinations. -/
theorem bridge_coherent
    {S S1 S2 : Set (ClassFunction L ℂ)}
    {tau tau1 tau2 : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ}
    {R : ClassFunction L ℂ → Finset (ClassFunction G ℂ)}
    (hsub : subcoherent S tau R)
    (hS1 : cfConjC_subset S1 S)
    (hcoh1 : coherent_with S1 (nonidentitySet L) tau tau1)
    (hS2 : cfConjC_subset S2 S)
    (hcoh2 : coherent_with S2 (nonidentitySet L) tau tau2)
    (hdisjoint : S2 ⊆ S1ᶜ)
    {chi phi : ClassFunction L ℂ}
    (hchi : chi ∈ S1) (hphi : phi ∈ AddSubgroup.closure S2)
    (hdiffOff : chi - phi ∈
      ClassFunction.supportedOn (nonidentitySet L))
    (hbridge : tau (chi - phi) = tau1 chi - tau2 phi) :
    coherent (S1 ∪ S2) (nonidentitySet L) tau := by
  classical
  letI : Fintype S1 := (hsub.finite.subset hS1.1).fintype
  letI : Fintype S2 := (hsub.finite.subset hS2.1).fintype
  have hnorm1 (x : S1) : characterPairing x.1 x.1 ≠ 0 :=
    pairing_self_ne_zero_of_virtual_ne_zero
      (hsub.source_virtual x.1 (hS1.1 x.property))
      (fun hx ↦ hsub.zero_not_mem (by simpa [hx] using hS1.1 x.property))
  have hnorm2 (x : S2) : characterPairing x.1 x.1 ≠ 0 :=
    pairing_self_ne_zero_of_virtual_ne_zero
      (hsub.source_virtual x.1 (hS2.1 x.property))
      (fun hx ↦ hsub.zero_not_mem (by simpa [hx] using hS2.1 x.property))
  let tau3 : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ :=
    { toFun := fun eta ↦
        (∑ x : S1,
          (characterPairing x.1 eta / characterPairing x.1 x.1) • tau1 x.1) +
        ∑ y : S2,
          (characterPairing y.1 eta / characterPairing y.1 y.1) • tau2 y.1
      map_add' := by
        intro eta theta
        simp only [characterPairing_add_right, add_div, add_smul,
          Finset.sum_add_distrib, map_add]
        abel
      map_smul' := by
        intro c eta
        simp only [characterPairing_smul_right, RingHom.id_apply]
        rw [smul_add, Finset.smul_sum, Finset.smul_sum]
        congr 1 <;> apply Finset.sum_congr rfl <;> intro x hx <;>
          rw [smul_smul] <;> congr 1 <;> ring }
  have htau3S1 (x : S1) : tau3 x.1 = tau1 x.1 := by
    change (∑ y : S1,
        (characterPairing y.1 x.1 / characterPairing y.1 y.1) • tau1 y.1) +
      (∑ y : S2,
        (characterPairing y.1 x.1 / characterPairing y.1 y.1) • tau2 y.1) =
      tau1 x.1
    have hfirst : (∑ y : S1,
        (characterPairing y.1 x.1 / characterPairing y.1 y.1) • tau1 y.1) =
        tau1 x.1 := by
      rw [Finset.sum_eq_single x]
      · rw [div_self (hnorm1 x), one_smul]
      · intro y _ hyx
        have hne : y.1 ≠ x.1 := fun h ↦ hyx (Subtype.ext h)
        rw [hsub.pairwise_orthogonal (hS1.1 y.property)
          (hS1.1 x.property) hne, zero_div, zero_smul]
      · simp
    have hsecond : (∑ y : S2,
        (characterPairing y.1 x.1 / characterPairing y.1 y.1) • tau2 y.1) = 0 := by
      apply Finset.sum_eq_zero
      intro y hy
      have hne : y.1 ≠ x.1 := by
        intro heq
        exact hdisjoint y.property (heq.symm ▸ x.property)
      rw [hsub.pairwise_orthogonal (hS2.1 y.property)
        (hS1.1 x.property) hne, zero_div, zero_smul]
    rw [hfirst, hsecond, add_zero]
  have htau3S2 (x : S2) : tau3 x.1 = tau2 x.1 := by
    change (∑ y : S1,
        (characterPairing y.1 x.1 / characterPairing y.1 y.1) • tau1 y.1) +
      (∑ y : S2,
        (characterPairing y.1 x.1 / characterPairing y.1 y.1) • tau2 y.1) =
      tau2 x.1
    have hfirst : (∑ y : S1,
        (characterPairing y.1 x.1 / characterPairing y.1 y.1) • tau1 y.1) = 0 := by
      apply Finset.sum_eq_zero
      intro y hy
      have hne : y.1 ≠ x.1 := by
        intro heq
        exact hdisjoint x.property (heq ▸ y.property)
      rw [hsub.pairwise_orthogonal (hS1.1 y.property)
        (hS2.1 x.property) hne, zero_div, zero_smul]
    have hsecond : (∑ y : S2,
        (characterPairing y.1 x.1 / characterPairing y.1 y.1) • tau2 y.1) =
        tau2 x.1 := by
      rw [Finset.sum_eq_single x]
      · rw [div_self (hnorm2 x), one_smul]
      · intro y _ hyx
        have hne : y.1 ≠ x.1 := fun h ↦ hyx (Subtype.ext h)
        rw [hsub.pairwise_orthogonal (hS2.1 y.property)
          (hS2.1 x.property) hne, zero_div, zero_smul]
      · simp
    rw [hfirst, hsecond, zero_add]
  have htau3Span1 : ∀ u ∈ AddSubgroup.closure S1, tau3 u = tau1 u := by
    intro u hu
    induction hu using AddSubgroup.closure_induction with
    | mem x hx => exact htau3S1 ⟨x, hx⟩
    | zero => simp
    | add x y hx hy ihx ihy => simpa only [map_add, ihx, ihy]
    | neg x hx ihx => simpa only [map_neg, ihx]
  have htau3Span2 : ∀ u ∈ AddSubgroup.closure S2, tau3 u = tau2 u := by
    intro u hu
    induction hu using AddSubgroup.closure_induction with
    | mem x hx => exact htau3S2 ⟨x, hx⟩
    | zero => simp
    | add x y hx hy ihx ihy => simpa only [map_add, ihx, ihy]
    | neg x hx ihx => simpa only [map_neg, ihx]
  have hpairGenerator : ∀ x ∈ S1 ∪ S2, ∀ y ∈ S1 ∪ S2,
      characterPairing (tau3 x) (tau3 y) = characterPairing x y := by
    intro x hx y hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · rw [htau3S1 ⟨x, hx⟩, htau3S1 ⟨y, hy⟩]
      exact hcoh1.isometry _ (AddSubgroup.subset_closure hx)
        _ (AddSubgroup.subset_closure hy)
    · rw [htau3S1 ⟨x, hx⟩, htau3S2 ⟨y, hy⟩]
      have htarget := coherent_ortho hsub hS1 hcoh1 hS2 hcoh2 hdisjoint
        (tau1 x) ⟨x, AddSubgroup.subset_closure hx, rfl⟩
        (tau2 y) ⟨y, AddSubgroup.subset_closure hy, rfl⟩
      have hsource : characterPairing x y = 0 :=
        hsub.pairwise_orthogonal (hS1.1 hx) (hS2.1 hy)
          (fun heq ↦ hdisjoint hy (heq ▸ hx))
      exact htarget.trans hsource.symm
    · rw [htau3S2 ⟨x, hx⟩, htau3S1 ⟨y, hy⟩]
      have htarget := coherent_ortho hsub hS1 hcoh1 hS2 hcoh2 hdisjoint
        (tau1 y) ⟨y, AddSubgroup.subset_closure hy, rfl⟩
        (tau2 x) ⟨x, AddSubgroup.subset_closure hx, rfl⟩
      have hsource : characterPairing x y = 0 :=
        hsub.pairwise_orthogonal (hS2.1 hx) (hS1.1 hy)
          (fun heq ↦ hdisjoint hx (heq.symm ▸ hy))
      calc
        characterPairing (tau2 x) (tau1 y) =
            characterPairing (tau1 y) (tau2 x) :=
          characterPairing_comm _ _
        _ = 0 := htarget
        _ = characterPairing x y := hsource.symm
    · rw [htau3S2 ⟨x, hx⟩, htau3S2 ⟨y, hy⟩]
      exact hcoh2.isometry _ (AddSubgroup.subset_closure hx)
        _ (AddSubgroup.subset_closure hy)
  have htau3Isometry : ∀ x ∈ AddSubgroup.closure (S1 ∪ S2),
      ∀ y ∈ AddSubgroup.closure (S1 ∪ S2),
        characterPairing (tau3 x) (tau3 y) = characterPairing x y := by
    intro x hx y hy
    induction hx, hy using AddSubgroup.closure_induction₂ with
    | mem x y hx hy => exact hpairGenerator x hx y hy
    | zero_left => simp
    | zero_right => simp
    | add_left x y z hx hy hz ihx ihy =>
        simp only [map_add, characterPairing_add_left, ihx, ihy]
    | add_right x y z hx hy hz ihx ihy =>
        simp only [map_add, characterPairing_add_right, ihx, ihy]
    | neg_left x y hx hy ih =>
        simp only [map_neg, pairing_neg_left, ih]
    | neg_right x y hx hy ih =>
        simp only [map_neg, pairing_neg_right, ih]
  have htau3Virtual : ∀ x ∈ AddSubgroup.closure (S1 ∪ S2),
      ClassFunction.IsVirtual (tau3 x) := by
    intro x hx
    induction hx using AddSubgroup.closure_induction with
    | mem x hx =>
        rcases hx with hx | hx
        · rw [htau3S1 ⟨x, hx⟩]
          exact hcoh1.mapsToVirtual x (AddSubgroup.subset_closure hx)
        · rw [htau3S2 ⟨x, hx⟩]
          exact hcoh2.mapsToVirtual x (AddSubgroup.subset_closure hx)
    | zero => simpa only [map_zero] using
        (ClassFunction.IsVirtual.zero :
          ClassFunction.IsVirtual (0 : ClassFunction G ℂ))
    | add x y hx hy ihx ihy => simpa only [map_add] using ihx.add ihy
    | neg x hx ihx => simpa only [map_neg] using ihx.neg
  refine ⟨tau3, {
    isometry := htau3Isometry
    mapsToVirtual := htau3Virtual
    agrees := ?_ }⟩
  intro eta heta hetaOff
  have hetaSup : eta ∈ AddSubgroup.closure S1 ⊔ AddSubgroup.closure S2 := by
    rw [← AddSubgroup.closure_union]
    exact heta
  obtain ⟨u, hu, v, hv, huv⟩ := AddSubgroup.mem_sup.mp hetaSup
  have htau3Eta : tau3 eta = tau1 u + tau2 v := by
    rw [← huv, map_add, htau3Span1 u hu, htau3Span2 v hv]
  obtain ⟨d, hd⟩ :=
    (hsub.source_character chi (hS1.1 hchi)).exists_nat_degree
  have hd0 : (d : ℂ) ≠ 0 := by
    rw [← hd]
    exact hsub.degree_ne_zero chi (hS1.1 hchi)
  have huVirtual : ClassFunction.IsVirtual u :=
    virtual_of_mem_closure
      (fun x hx ↦ hsub.source_virtual x (hS1.1 hx)) hu
  obtain ⟨zu, hzu⟩ := huVirtual
  let c : ℤ := VirtualCharacter.integralDegree zu
  have huOne : u 1 = (c : ℂ) := by
    rw [← hzu, VirtualCharacter.realize_one_eq_integralDegree]
  have hetaOne : eta 1 = 0 :=
    ClassFunction.eq_zero_of_mem_supportedOn hetaOff (by simp [nonidentitySet])
  have hvOne : v 1 = -(c : ℂ) := by
    have hvalue := congrArg (fun f : ClassFunction L ℂ ↦ f 1) huv
    simp only [ClassFunction.add_apply, huOne] at hvalue
    rw [hetaOne] at hvalue
    linear_combination hvalue
  have hphiOne : phi 1 = (d : ℂ) := by
    have hzero := ClassFunction.eq_zero_of_mem_supportedOn hdiffOff
      (show (1 : L) ∉ nonidentitySet L by simp [nonidentitySet])
    simp only [ClassFunction.sub_apply, hd] at hzero
    exact (sub_eq_zero.mp hzero).symm
  let u0 : ClassFunction L ℂ :=
    (d : ℂ) • u - (c : ℂ) • chi
  let v0 : ClassFunction L ℂ :=
    (d : ℂ) • v + (c : ℂ) • phi
  have hu0 : u0 ∈ AddSubgroup.closure S1 := by
    apply (AddSubgroup.closure S1).sub_mem
    · simpa only [Nat.cast_smul_eq_nsmul] using
        (AddSubgroup.closure S1).nsmul_mem hu d
    · simpa only [← Int.cast_smul_eq_zsmul ℂ] using
        (AddSubgroup.closure S1).zsmul_mem
          (AddSubgroup.subset_closure hchi) c
  have hv0 : v0 ∈ AddSubgroup.closure S2 := by
    apply (AddSubgroup.closure S2).add_mem
    · simpa only [Nat.cast_smul_eq_nsmul] using
        (AddSubgroup.closure S2).nsmul_mem hv d
    · simpa only [← Int.cast_smul_eq_zsmul ℂ] using
        (AddSubgroup.closure S2).zsmul_mem hphi c
  have hu0Off : u0 ∈ ClassFunction.supportedOn (nonidentitySet L) := by
    rw [ClassFunction.mem_supportedOn_iff]
    intro x hx
    have hxone : x = 1 := by
      simpa [nonidentitySet] using not_not.mp hx
    subst x
    simp only [u0, ClassFunction.sub_apply, ClassFunction.smul_apply,
      smul_eq_mul, huOne, hd]
    ring
  have hv0Off : v0 ∈ ClassFunction.supportedOn (nonidentitySet L) := by
    rw [ClassFunction.mem_supportedOn_iff]
    intro x hx
    have hxone : x = 1 := by
      simpa [nonidentitySet] using not_not.mp hx
    subst x
    simp only [v0, ClassFunction.add_apply, ClassFunction.smul_apply,
      smul_eq_mul, hvOne, hphiOne]
    ring
  have hagree1 : tau1 u0 = tau u0 := hcoh1.agrees u0 hu0 hu0Off
  have hagree2 : tau2 v0 = tau v0 := hcoh2.agrees v0 hv0 hv0Off
  have hscaled :
      (d : ℂ) • (tau1 u + tau2 v) -
          (c : ℂ) • (tau1 chi - tau2 phi) =
        (d : ℂ) • tau (u + v) -
          (c : ℂ) • tau (chi - phi) := by
    calc
      (d : ℂ) • (tau1 u + tau2 v) -
          (c : ℂ) • (tau1 chi - tau2 phi) =
          tau1 u0 + tau2 v0 := by
            simp only [u0, v0, map_sub, map_add, map_smul]
            module
      _ = tau u0 + tau v0 := by rw [hagree1, hagree2]
      _ = (d : ℂ) • tau (u + v) -
          (c : ℂ) • tau (chi - phi) := by
            simp only [u0, v0, map_sub, map_add, map_smul]
            module
  rw [← hbridge] at hscaled
  have hscaled' :
      (d : ℂ) • (tau1 u + tau2 v) =
        (d : ℂ) • tau (u + v) :=
    sub_left_injective hscaled
  rw [htau3Eta, ← huv]
  exact smul_right_injective (ClassFunction G ℂ) hd0 hscaled'

private theorem coherent_inverse_pair_with_value
    {S : Set (ClassFunction L ℂ)}
    {tau : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ}
    {R : ClassFunction L ℂ → Finset (ClassFunction G ℂ)}
    (hsub : subcoherent S tau R)
    {chi : ClassFunction L ℂ} (hchi : chi ∈ S)
    {X Xc : ClassFunction G ℂ}
    (hXVirtual : ClassFunction.IsVirtual X)
    (hXcVirtual : ClassFunction.IsVirtual Xc)
    (hXXc : characterPairing X Xc = 0)
    (hXNorm : characterPairing X X = characterPairing chi chi)
    (hXcNorm : characterPairing Xc Xc =
      characterPairing (ClassFunction.inverseLinear chi)
        (ClassFunction.inverseLinear chi))
    (hdiff : tau (chi - ClassFunction.inverseLinear chi) = X - Xc) :
    ∃ tau2 : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ,
      coherent_with
        ({chi, ClassFunction.inverseLinear chi} : Set (ClassFunction L ℂ))
        (nonidentitySet L) tau tau2 ∧ tau2 chi = X := by
  classical
  let chic := ClassFunction.inverseLinear chi
  have hchic : chic ∈ S := hsub.inverse_mem chi hchi
  have hne : chi ≠ chic := (hsub.inverse_ne chi hchi).symm
  have horth : characterPairing chi chic = 0 :=
    hsub.pairwise_orthogonal hchi hchic hne
  have hchiNorm0 : characterPairing chi chi ≠ 0 :=
    pairing_self_ne_zero_of_virtual_ne_zero
      (hsub.source_virtual chi hchi)
      (fun hz ↦ hsub.zero_not_mem (hz ▸ hchi))
  have hchicNorm0 : characterPairing chic chic ≠ 0 :=
    pairing_self_ne_zero_of_virtual_ne_zero
      (hsub.source_virtual chic hchic)
      (fun hz ↦ hsub.zero_not_mem (hz ▸ hchic))
  let tau2 : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ :=
    { toFun := fun eta ↦
        (characterPairing chi eta / characterPairing chi chi) • X +
        (characterPairing chic eta / characterPairing chic chic) • Xc
      map_add' := by
        intro eta theta
        simp only [characterPairing_add_right, add_div, add_smul]
        abel
      map_smul' := by
        intro c eta
        simp only [characterPairing_smul_right, RingHom.id_apply]
        rw [smul_add]
        congr 1 <;> rw [smul_smul] <;> congr 1 <;> ring }
  have htau2Chi : tau2 chi = X := by
    change (characterPairing chi chi / characterPairing chi chi) • X +
      (characterPairing chic chi / characterPairing chic chic) • Xc = X
    rw [div_self hchiNorm0, one_smul, characterPairing_comm chic chi,
      horth, zero_div, zero_smul, add_zero]
  have htau2Chic : tau2 chic = Xc := by
    change (characterPairing chi chic / characterPairing chi chi) • X +
      (characterPairing chic chic / characterPairing chic chic) • Xc = Xc
    rw [horth, zero_div, zero_smul, div_self hchicNorm0,
      one_smul, zero_add]
  let P : Set (ClassFunction L ℂ) := {chi, chic}
  have hpair : ∀ x ∈ P, ∀ y ∈ P,
      characterPairing (tau2 x) (tau2 y) = characterPairing x y := by
    intro x hx y hy
    simp only [P, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · rw [hx, hy, htau2Chi, hXNorm]
    · rw [hx, hy, htau2Chi, htau2Chic, hXXc, horth]
    · rw [hx, hy, htau2Chic, htau2Chi, characterPairing_comm Xc X,
        hXXc, characterPairing_comm chic chi, horth]
    · rw [hx, hy, htau2Chic, hXcNorm]
  have hisometry : ∀ x ∈ AddSubgroup.closure P,
      ∀ y ∈ AddSubgroup.closure P,
        characterPairing (tau2 x) (tau2 y) = characterPairing x y := by
    intro x hx y hy
    induction hx, hy using AddSubgroup.closure_induction₂ with
    | mem x y hx hy => exact hpair x hx y hy
    | zero_left => simp
    | zero_right => simp
    | add_left x y z hx hy hz ihx ihy =>
        simp only [map_add, characterPairing_add_left, ihx, ihy]
    | add_right x y z hx hy hz ihx ihy =>
        simp only [map_add, characterPairing_add_right, ihx, ihy]
    | neg_left x y hx hy ih => simp only [map_neg, pairing_neg_left, ih]
    | neg_right x y hx hy ih => simp only [map_neg, pairing_neg_right, ih]
  have hvirtual : ∀ x ∈ AddSubgroup.closure P,
      ClassFunction.IsVirtual (tau2 x) := by
    intro x hx
    induction hx using AddSubgroup.closure_induction with
    | mem x hx =>
        rcases hx with (rfl | rfl)
        · rw [htau2Chi]
          exact hXVirtual
        · rw [htau2Chic]
          exact hXcVirtual
    | zero => simpa only [map_zero] using
        (ClassFunction.IsVirtual.zero :
          ClassFunction.IsVirtual (0 : ClassFunction G ℂ))
    | add x y hx hy ihx ihy => simpa only [map_add] using ihx.add ihy
    | neg x hx ihx => simpa only [map_neg] using ihx.neg
  have hagrees : ∀ eta ∈ AddSubgroup.closure P,
      eta ∈ ClassFunction.supportedOn (nonidentitySet L) →
        tau2 eta = tau eta := by
    intro eta heta hetaOff
    obtain ⟨m, n, hmn⟩ := AddSubgroup.mem_closure_pair.mp heta
    have hetaOne : eta 1 = 0 :=
      ClassFunction.eq_zero_of_mem_supportedOn hetaOff
        (by simp [nonidentitySet])
    have hcoeff : m + n = 0 := by
      have hvalue := congrArg (fun f : ClassFunction L ℂ ↦ f 1) hmn.symm
      rw [← Int.cast_smul_eq_zsmul ℂ,
        ← Int.cast_smul_eq_zsmul ℂ] at hvalue
      simp only [ClassFunction.add_apply, ClassFunction.smul_apply,
        chic, ClassFunction.inverseLinear_apply, inv_one,
        smul_eq_mul] at hvalue
      have hmul : (((m + n : ℤ) : ℂ) * chi 1) = 0 := by
        rw [Int.cast_add]
        calc
          ((m : ℂ) + (n : ℂ)) * chi 1 = eta 1 := by
            linear_combination hvalue.symm
          _ = 0 := hetaOne
      have hcast : ((m + n : ℤ) : ℂ) = 0 :=
        (mul_eq_zero.mp hmul).resolve_right (hsub.degree_ne_zero chi hchi)
      apply Int.cast_injective (α := ℂ)
      simpa only [Int.cast_zero] using hcast
    have hn : n = -m := by omega
    have hetaDiff : eta = m • (chi - chic) := by
      calc
        eta = m • chi + n • chic := hmn.symm
        _ = m • (chi - chic) := by rw [hn]; module
    rw [hetaDiff, map_zsmul, map_zsmul, hdiff]
    rw [map_sub, htau2Chi, htau2Chic]
  exact ⟨tau2, ⟨⟨hisometry, hvirtual, hagrees⟩, htau2Chi⟩⟩

/-- Peterfalvi (5.6.3), the extension lemma reused in Section 9.  A character
`chi` can be adjoined once its degree-balanced difference with a coherent
member has an orthogonal target decomposition. -/
theorem extend_coherent_with
    {S S1 : Set (ClassFunction L ℂ)}
    {tau tau1 : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ}
    {R : ClassFunction L ℂ → Finset (ClassFunction G ℂ)}
    (hsub : subcoherent S tau R)
    (hS1 : cfConjC_subset S1 S)
    (hcoh : coherent_with S1 (nonidentitySet L) tau tau1)
    {chi phi : ClassFunction L ℂ}
    (hphi : phi ∈ S1) (hchi : chi ∈ S) (hchi1 : chi ∉ S1)
    (a : ℕ) (X : ClassFunction G ℂ)
    (hdegree : chi 1 = (a : ℂ) * phi 1)
    (horth : characterPairing X ((a : ℂ) • tau1 phi) = 0)
    (hmap : tau (chi - (a : ℂ) • phi) =
      X - (a : ℂ) • tau1 phi) :
    coherent
      ({chi, ClassFunction.inverseLinear chi} ∪ S1)
      (nonidentitySet L) tau := by
  classical
  let chic := ClassFunction.inverseLinear chi
  let psi : ClassFunction L ℂ := (a : ℂ) • phi
  let Y : ClassFunction G ℂ := (a : ℂ) • tau1 phi
  let beta : ClassFunction L ℂ := chi - psi
  have hphiS : phi ∈ S := hS1.1 hphi
  have hphiVirtual : ClassFunction.IsVirtual phi :=
    hsub.source_virtual phi hphiS
  have hpsiVirtual : ClassFunction.IsVirtual psi := by
    simpa only [psi] using hphiVirtual.natCast_smul a
  have hYVirtual : ClassFunction.IsVirtual Y := by
    exact (hcoh.mapsToVirtual phi (AddSubgroup.subset_closure hphi)).natCast_smul a
  have hbetaSpan : beta ∈ AddSubgroup.closure S := by
    apply (AddSubgroup.closure S).sub_mem (AddSubgroup.subset_closure hchi)
    simpa only [psi, Nat.cast_smul_eq_nsmul] using
      (AddSubgroup.closure S).nsmul_mem
        (AddSubgroup.subset_closure hphiS) a
  have hbetaOff : beta ∈ ClassFunction.supportedOn (nonidentitySet L) := by
    rw [ClassFunction.mem_supportedOn_iff]
    intro x hx
    have hxone : x = 1 := by
      simpa [nonidentitySet] using not_not.mp hx
    subst x
    simp only [beta, psi, ClassFunction.sub_apply,
      ClassFunction.smul_apply, smul_eq_mul, hdegree, sub_self]
  have htauBetaVirtual : ClassFunction.IsVirtual (tau beta) :=
    hsub.tau_virtual beta hbetaSpan hbetaOff
  have hmap' : tau beta = X - Y := by
    simpa only [beta, psi, Y] using hmap
  have hXVirtual : ClassFunction.IsVirtual X := by
    have hXeq : X = tau beta + Y := by
      rw [hmap']
      abel
    rw [hXeq]
    exact htauBetaVirtual.add hYVirtual
  have hinvS : chic ∈ S := hsub.inverse_mem chi hchi
  have hinvNot : chic ∉ S1 := by
    intro hinvMem
    have := hS1.2 _ hinvMem
    simp only [chic, inverseLinear_involutive] at this
    exact hchi1 this
  have hchiPhi : characterPairing chi phi = 0 := by
    rw [characterPairing_comm]
    exact subset_ortho_subcoherent hsub hS1.1 hchi hchi1 phi hphi
  have hinvPhi : characterPairing chic phi = 0 :=
    hsub.pairwise_orthogonal hinvS hphiS
      (fun heq ↦ hinvNot (heq.symm ▸ hphi))
  have hchiPsi : characterPairing chi psi = 0 := by
    simp only [psi]
    rw [characterPairing_smul_right, hchiPhi, mul_zero]
  have hinvPsi : characterPairing chic psi = 0 := by
    simp only [psi]
    rw [characterPairing_smul_right, hinvPhi, mul_zero]
  have hYR : ∀ alpha ∈ R chi, characterPairing Y alpha = 0 := by
    intro alpha halpha
    have hbase := coherent_ortho_supp hsub hS1 hcoh hchi hchi1
      (tau1 phi) ⟨phi, AddSubgroup.subset_closure hphi, rfl⟩
      alpha halpha
    simp only [Y]
    rw [characterPairing_smul_left, hbase, mul_zero]
  let S0 : Set (ClassFunction L ℂ) :=
    {beta, chi - chic}
  have hS0Span : AddSubgroup.closure S0 ≤ AddSubgroup.closure S := by
    refine (AddSubgroup.closure_le (AddSubgroup.closure S)).2 ?_
    intro u hu
    rcases hu with (rfl | rfl)
    · exact hbetaSpan
    · exact (AddSubgroup.closure S).sub_mem
        (AddSubgroup.subset_closure hchi)
        (AddSubgroup.subset_closure hinvS)
  have hdiffOff : chi - chic ∈
      ClassFunction.supportedOn (nonidentitySet L) := by
    simpa only [chic] using inverse_sub_supported chi
  have hS0Off : ∀ u ∈ AddSubgroup.closure S0,
      u ∈ ClassFunction.supportedOn (nonidentitySet L) := by
    intro u hu
    induction hu using AddSubgroup.closure_induction with
    | mem u hu =>
        rcases hu with (rfl | rfl)
        · exact hbetaOff
        · exact hdiffOff
    | zero => exact (ClassFunction.supportedOn (nonidentitySet L)).zero_mem
    | add x y hx hy ihx ihy =>
        exact (ClassFunction.supportedOn (nonidentitySet L)).add_mem ihx ihy
    | neg x hx ihx =>
        exact (ClassFunction.supportedOn (R := ℂ)
          (nonidentitySet L)).neg_mem ihx
  have hnormPsiY : normLE psi Y := by
    apply normLE_of_eq
    simp only [psi, Y, characterPairing_smul_left,
      characterPairing_smul_right]
    rw [hcoh.isometry phi (AddSubgroup.subset_closure hphi)
      phi (AddSubgroup.subset_closure hphi)]
  have hnorm := subcoherent_norm hsub hchi hpsiVirtual
    hchiPsi hinvPsi tau
    (fun u hu v hv ↦ hsub.tau_isometry u (hS0Span hu) (hS0Off u hu)
      v (hS0Span hv) (hS0Off v hv))
    (fun u hu ↦ hsub.tau_virtual u (hS0Span hu) (hS0Off u hu))
    rfl hXVirtual hYVirtual hmap' horth hYR
  obtain ⟨hXNorm, _, E, hER, hXsum⟩ := hnorm.2 hnormPsiY
  let Ec : Finset (ClassFunction G ℂ) := R chi \ E
  let Xc : ClassFunction G ℂ := -∑ alpha ∈ Ec, alpha
  have hEcR : Ec ⊆ R chi := by
    intro alpha halpha
    exact (Finset.mem_sdiff.mp halpha).1
  have hXcVirtual : ClassFunction.IsVirtual Xc := by
    have hsumSpan : (∑ alpha ∈ Ec, alpha) ∈
        AddSubgroup.closure
          (↑(R chi) : Set (ClassFunction G ℂ)) := by
      apply AddSubgroup.sum_mem
      intro alpha halpha
      exact AddSubgroup.subset_closure (hEcR halpha)
    have hsumVirtual : ClassFunction.IsVirtual
        (∑ alpha ∈ Ec, alpha) :=
      virtual_of_mem_closure
        (fun alpha halpha ↦ hsub.image_virtual chi hchi alpha halpha)
        hsumSpan
    simpa only [Xc] using hsumVirtual.neg
  have hXXc : characterPairing X Xc = 0 := by
    simp only [Xc]
    rw [hXsum, pairing_neg_right, pairing_finset_sum_left]
    apply neg_eq_zero.mpr
    apply Finset.sum_eq_zero
    intro alpha halpha
    rw [pairing_finset_sum_right]
    apply Finset.sum_eq_zero
    intro gamma hgamma
    have halphaR := hER halpha
    have hgammaR := hEcR hgamma
    have hne : alpha ≠ gamma := by
      intro heq
      subst gamma
      exact (Finset.mem_sdiff.mp hgamma).2 halpha
    rw [hsub.image_orthonormal chi hchi alpha halphaR gamma hgammaR,
      if_neg hne]
  have hpartition :
      (∑ alpha ∈ R chi, alpha) =
        (∑ alpha ∈ E, alpha) + ∑ alpha ∈ Ec, alpha := by
    dsimp only [Ec]
    rw [← Finset.sum_sdiff hER, add_comm]
  have htauPair : tau (chi - chic) = X - Xc := by
    simp only [Xc]
    rw [hsub.tau_inverse_sub chi hchi, hpartition, hXsum]
    abel
  have hchiChic : characterPairing chi chic = 0 :=
    hsub.pairwise_orthogonal hchi hinvS (hsub.inverse_ne chi hchi).symm
  have hpairSpan : chi - chic ∈ AddSubgroup.closure S :=
    (AddSubgroup.closure S).sub_mem
      (AddSubgroup.subset_closure hchi)
      (AddSubgroup.subset_closure hinvS)
  have htauPairNorm :
      characterPairing (tau (chi - chic)) (tau (chi - chic)) =
        characterPairing (chi - chic) (chi - chic) :=
    hsub.tau_isometry _ hpairSpan hdiffOff _ hpairSpan hdiffOff
  have hXcNorm : characterPairing Xc Xc =
      characterPairing chic chic := by
    have htarget := pairing_self_sub_of_orthogonal X Xc hXXc
    have hsource := pairing_self_sub_of_orthogonal chi chic hchiChic
    rw [← htauPair] at htarget
    linear_combination -htarget + htauPairNorm + hsource - hXNorm
  obtain ⟨tau2, hcoh2, htau2Chi⟩ :=
    coherent_inverse_pair_with_value hsub hchi hXVirtual hXcVirtual
      hXXc hXNorm hXcNorm htauPair
  let P : Set (ClassFunction L ℂ) := {chi, chic}
  have hP : cfConjC_subset P S := by
    constructor
    · exact Set.pair_subset hchi hinvS
    · intro x hx
      simp only [P, Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
      rcases hx with hx | hx
      · rw [hx]
        exact Or.inr rfl
      · rw [hx]
        exact Or.inl (inverseLinear_involutive chi)
  have hS1P : S1 ⊆ Pᶜ := by
    intro x hx hxP
    rcases hxP with (rfl | rfl)
    · exact hchi1 hx
    · exact hinvNot hx
  have hpsiSpan : psi ∈ AddSubgroup.closure S1 := by
    simpa only [psi, Nat.cast_smul_eq_nsmul] using
      (AddSubgroup.closure S1).nsmul_mem
        (AddSubgroup.subset_closure hphi) a
  apply bridge_coherent hsub hP hcoh2 hS1 hcoh hS1P
    (chi := chi) (phi := psi)
  · exact Or.inl rfl
  · exact hpsiSpan
  · exact hbetaOff
  · rw [htau2Chi, map_smul]
    exact hmap'

end

end Submission.OddOrder.PF
