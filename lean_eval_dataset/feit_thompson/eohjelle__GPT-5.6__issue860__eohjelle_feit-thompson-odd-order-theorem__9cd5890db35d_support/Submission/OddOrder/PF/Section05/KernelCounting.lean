import Submission.OddOrder.PF.Section05.InducedIrreducibles

/-!
# Kernel counting for irreducible characters

This file ports the three counting lemmas at the beginning of Peterfalvi
Section 5 (`PFsection5.v`, lines 70--110).  The key construction is the
inflated regular character of a quotient by a normal subgroup: on the
ambient group it has value the subgroup index on the subgroup and vanishes
off it.  Its scalar product with an irreducible character is the dimension
of the normal-subgroup fixed space.  Irreducibility makes that space either
zero or the whole representation, so character completeness gives the
required degree-square sum without introducing quotient irreducibles as a
separate indexing type.
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped BigOperators Classical MonoidAlgebra
open CategoryTheory

universe u v

local instance kernelCountingInvertibleCard
    {G : Type u} {k : Type v} [Group G] [Fintype G] [Field k] [CharZero k] :
    Invertible (Nat.card G : k) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

namespace ClassFunction

variable {G : Type u} {k : Type v} [Group G] [Fintype G]
  [Field k] [IsAlgClosed k] [CharZero k]

/-- The regular character of `G / H`, inflated to `G`: it is `H.index` on
`H` and zero away from `H`. -/
private def normalQuotientRegular (H : Subgroup G) [H.Normal] :
    ClassFunction G k where
  val g := if g ∈ H then (H.index : k) else 0
  property x g := by
    exact if_congr (IsConjStable.normal H x g) rfl rfl

@[simp]
private theorem normalQuotientRegular_apply
    (H : Subgroup G) [H.Normal] (g : G) :
    normalQuotientRegular (k := k) H g =
      if g ∈ H then (H.index : k) else 0 :=
  rfl

/-- Universe-polymorphic form of
`ClassFunction.translationKernel_irreducibleCharacter`. -/
private theorem translationKernel_irreducibleCharacter_general
    (chi : IrreducibleCharacter G k) :
    translationKernel (chi : ClassFunction G k) =
      chi.representation.ρ.ker := by
  apply le_antisymm
  · intro a ha
    rw [MonoidHom.mem_ker]
    let rho : Representation k G chi.representation :=
      chi.representation.ρ
    letI : Simple chi.representation := chi.representation_simple
    letI : Representation.IsIrreducible rho :=
      Submission.OddOrder.MathlibSupport.representation_isIrreducible_of_simple_fdRep
        chi.representation
    have htraceGroup (g : G) :
        LinearMap.trace k chi.representation
            ((rho a - 1) * rho g) = 0 := by
      rw [sub_mul, one_mul, map_sub, ← rho.map_mul]
      change rho.character (a * g) - rho.character g = 0
      dsimp only [rho]
      change chi.representation.character (a * g) -
        chi.representation.character g = 0
      rw [chi.representation_character, chi.representation_character]
      exact sub_eq_zero.mpr (ha g)
    have htraceAlgebra (z : k[G]) :
        LinearMap.trace k chi.representation
            ((rho a - 1) * rho.asAlgebraHom z) = 0 := by
      induction z using MonoidAlgebra.induction_on with
      | hM g =>
          simpa only [Representation.asAlgebraHom_of] using htraceGroup g
      | hadd x y hx hy =>
          simp only [map_add, mul_add, hx, hy, add_zero]
      | hsmul c x hx =>
          simp only [map_smul, mul_smul_comm, hx, smul_zero]
    have htraceEnd (X : Module.End k chi.representation) :
        LinearMap.trace k chi.representation ((rho a - 1) * X) = 0 := by
      obtain ⟨z, rfl⟩ :=
        Submission.OddOrder.MathlibSupport.Representation.IsIrreducible.asAlgebraHom_surjective
          rho X
      exact htraceAlgebra z
    have hzero : rho a - 1 = 0 := by
      let b := Module.finBasis k chi.representation
      apply (LinearMap.toMatrixAlgEquiv b).injective
      rw [map_zero]
      apply (Matrix.ext_iff_trace_mul_right).2
      intro X
      have hX := htraceEnd ((LinearMap.toMatrixAlgEquiv b).symm X)
      rw [LinearMap.trace_eq_matrix_trace k b] at hX
      change
        ((LinearMap.toMatrixAlgEquiv b)
            ((rho a - 1) * (LinearMap.toMatrixAlgEquiv b).symm X)).trace = 0
        at hX
      simpa only [map_mul, AlgEquiv.apply_symm_apply, Matrix.zero_mul,
        Matrix.trace_zero] using hX
    exact sub_eq_zero.mp hzero
  · intro a ha g
    rw [← chi.representation_character,
      ← chi.representation_character]
    change LinearMap.trace k chi.representation
        (chi.representation.ρ (a * g)) =
      LinearMap.trace k chi.representation (chi.representation.ρ g)
    rw [chi.representation.ρ.map_mul, MonoidHom.mem_ker.mp ha, one_mul]

/-- The pairing with the inflated quotient-regular character is the
dimension of the `H`-fixed space. -/
private theorem characterPairing_normalQuotientRegular_eq_finrank
    (H : Subgroup G) [H.Normal]
    (chi : IrreducibleCharacter G k) :
    characterPairing (chi : ClassFunction G k)
        (normalQuotientRegular (k := k) H) =
      (Module.finrank k
        (Representation.invariants
          (chi.representation.ρ.comp H.subtype)) : k) := by
  let rhoH : Representation k H chi.representation :=
    chi.representation.ρ.comp H.subtype
  have hchar (h : H) : rhoH.character h = chi h := by
    change chi.representation.character (h : G) = chi h
    exact chi.representation_character (h : G)
  have hsum :
      (∑ x : G, chi x * normalQuotientRegular (k := k) H x⁻¹) =
        (∑ h : H, chi h * (H.index : k)) := by
    calc
      (∑ x : G, chi x * normalQuotientRegular (k := k) H x⁻¹) =
          ∑ x : G, if x ∈ H then chi x * (H.index : k) else 0 := by
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : x ∈ H
        · rw [normalQuotientRegular_apply, if_pos (H.inv_mem hx), if_pos hx]
        · have hxinv : x⁻¹ ∉ H := by simpa using hx
          rw [normalQuotientRegular_apply, if_neg hxinv, mul_zero, if_neg hx]
      _ = ∑ h : H, chi h * (H.index : k) := by
        rw [← Finset.sum_filter]
        apply Finset.sum_subtype
        intro x
        simp
  have hpair_average :
      characterPairing (chi : ClassFunction G k)
          (normalQuotientRegular (k := k) H) =
        (Nat.card H : k)⁻¹ * ∑ h : H, chi h := by
    rw [characterPairing, hsum, ← Finset.sum_mul]
    rw [← H.card_mul_index, Nat.cast_mul]
    have hHcard : (Nat.card H : k) ≠ 0 :=
      Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    have hindex : (H.index : k) ≠ 0 :=
      Nat.cast_ne_zero.mpr H.index_ne_zero_of_finite
    field_simp [hHcard, hindex]
  have havg := rhoH.card_inv_mul_sum_char_eq_finrank
  rw [hpair_average]
  simpa only [hchar] using havg

/-- For an irreducible representation, the fixed space of a normal subgroup
is all or nothing.  In character language, the full case is precisely the
translation-kernel condition. -/
private theorem characterPairing_normalQuotientRegular
    (H : Subgroup G) [H.Normal]
    (chi : IrreducibleCharacter G k) :
    characterPairing (chi : ClassFunction G k)
        (normalQuotientRegular (k := k) H) =
      if H ≤ translationKernel (chi : ClassFunction G k) then chi 1 else 0 := by
  let rho : Representation k G chi.representation := chi.representation.ρ
  letI : Simple chi.representation := chi.representation_simple
  letI : Representation.IsIrreducible rho :=
    Submission.OddOrder.MathlibSupport.representation_isIrreducible_of_simple_fdRep
      chi.representation
  rw [characterPairing_normalQuotientRegular_eq_finrank]
  by_cases hker : H ≤ translationKernel (chi : ClassFunction G k)
  · rw [if_pos hker]
    have hinvariants :
        Representation.invariants (rho.comp H.subtype) = ⊤ := by
      apply top_unique
      intro v _
      rw [Representation.mem_invariants]
      intro h
      have hh : (h : G) ∈ chi.representation.ρ.ker := by
        rw [← translationKernel_irreducibleCharacter_general chi]
        exact hker h.property
      exact DFunLike.congr_fun (MonoidHom.mem_ker.mp hh) v
    rw [show chi.representation.ρ = rho from rfl, hinvariants,
      finrank_top, ← IrreducibleCharacter.apply_one_eq_finrank]
  · rw [if_neg hker]
    have hinvariants :
        Representation.invariants (rho.comp H.subtype) = ⊥ := by
      let U : Subrepresentation rho :=
        { toSubmodule := Representation.invariants (rho.comp H.subtype)
          apply_mem_toSubmodule g := Representation.le_comap_invariants rho H g }
      rcases IsSimpleOrder.eq_bot_or_eq_top U with hU | hU
      · apply SetLike.ext
        intro v
        have hv := congrArg (fun W : Subrepresentation rho ↦ v ∈ W) hU
        change
          (v ∈ Representation.invariants (rho.comp H.subtype)) =
            (v ∈ (⊥ : Submodule k chi.representation)) at hv
        exact iff_of_eq hv
      · exfalso
        apply hker
        rw [translationKernel_irreducibleCharacter_general chi]
        intro h hh
        rw [MonoidHom.mem_ker]
        ext v
        have hv : v ∈ U := by
          rw [hU]
          trivial
        exact (Representation.mem_invariants _ _).mp hv ⟨h, hh⟩
    rw [show chi.representation.ρ = rho from rfl, hinvariants,
      finrank_bot, Nat.cast_zero]

end ClassFunction

variable {G : Type u} {k : Type v} [Group G] [Fintype G]
  [Field k] [IsAlgClosed k] [CharZero k]

/-- Source `sum_Iirr_ker_square`: the sum of the squares of the degrees of
the irreducible characters whose kernel contains `H` is `[G : H]`. -/
theorem sum_Iirr_ker_square (H : Subgroup G) [H.Normal] :
    (∑ chi ∈ Iirr_ker (k := k) H, chi 1 ^ 2) = (H.index : k) := by
  let qreg : ClassFunction G k :=
    ClassFunction.normalQuotientRegular (k := k) H
  have hexpansion :
      (∑ chi : IrreducibleCharacter G k,
          characterPairing (chi : ClassFunction G k) qreg * chi 1) =
        qreg 1 := by
    let evalOne : ClassFunction G k →ₗ[k] k :=
      { toFun := fun f ↦ f 1
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
    calc
      (∑ chi : IrreducibleCharacter G k,
          characterPairing (chi : ClassFunction G k) qreg * chi 1) =
          evalOne (irreducibleCharacterExpansion qreg) := by
        simp [evalOne, irreducibleCharacterExpansion]
      _ = evalOne qreg :=
        congrArg evalOne (irreducibleCharacterExpansion_eq qreg)
      _ = qreg 1 := rfl
  calc
    (∑ chi ∈ Iirr_ker (k := k) H, chi 1 ^ 2) =
        ∑ chi : IrreducibleCharacter G k,
          (if H ≤ ClassFunction.translationKernel
              (chi : ClassFunction G k) then chi 1 else 0) * chi 1 := by
      rw [Iirr_ker, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro chi _
      split_ifs <;> simp [pow_two]
    _ = ∑ chi : IrreducibleCharacter G k,
          characterPairing (chi : ClassFunction G k) qreg * chi 1 := by
      apply Finset.sum_congr rfl
      intro chi _
      rw [ClassFunction.characterPairing_normalQuotientRegular]
    _ = qreg 1 := hexpansion
    _ = (H.index : k) := by simp [qreg]

/-- Source `sum_Iirr_kerD_square`: subtracting the two nested kernel sums
counts the characters whose kernel contains `M` but not `H`. -/
theorem sum_Iirr_kerD_square
    (H M : Subgroup G) [H.Normal] [M.Normal] (hMH : M ≤ H) :
    (∑ chi ∈ Iirr_kerD (k := k) H M, chi 1 ^ 2) =
      (H.index : k) * (((M.relIndex H : ℕ) : k) - 1) := by
  have hsub : Iirr_ker (k := k) H ⊆ Iirr_ker (k := k) M :=
    Iirr_kerS hMH
  calc
    (∑ chi ∈ Iirr_kerD (k := k) H M, chi 1 ^ 2) =
        (∑ chi ∈ Iirr_ker (k := k) M, chi 1 ^ 2) -
          ∑ chi ∈ Iirr_ker (k := k) H, chi 1 ^ 2 := by
      exact Finset.sum_sdiff_eq_sub hsub
    _ = (M.index : k) - (H.index : k) := by
      rw [sum_Iirr_ker_square, sum_Iirr_ker_square]
    _ = (H.index : k) * (((M.relIndex H : ℕ) : k) - 1) := by
      rw [← M.relIndex_mul_index hMH, Nat.cast_mul]
      ring

/-- An irreducible character with the whole group in its translation kernel
is the trivial character. -/
private theorem top_le_translationKernel_irreducible_iff
    (chi : IrreducibleCharacter G k) :
    ⊤ ≤ ClassFunction.translationKernel (chi : ClassFunction G k) ↔
      chi = IrreducibleCharacter.trivial := by
  constructor
  · intro htop
    have hconstant (g : G) : chi g = chi 1 := by
      have hg := htop (show g ∈ (⊤ : Subgroup G) by trivial) 1
      simpa using hg
    have hchi_ne_zero : chi 1 ≠ 0 := by
      intro hone
      have hzero : (chi : ClassFunction G k) = 0 := by
        apply ClassFunction.ext
        intro g
        rw [hconstant g, hone]
        rfl
      have hself := IrreducibleCharacter.characterPairing_self chi
      rw [hzero, characterPairing_zero_left] at hself
      exact zero_ne_one hself
    have hpair :
        characterPairing (chi : ClassFunction G k)
            ((IrreducibleCharacter.trivial : IrreducibleCharacter G k) :
              ClassFunction G k) = chi 1 := by
      rw [characterPairing]
      simp_rw [IrreducibleCharacter.trivial_apply, mul_one, hconstant]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_eq_nat_card,
        nsmul_eq_mul]
      have hcard : (Nat.card G : k) ≠ 0 :=
        Nat.cast_ne_zero.mpr Nat.card_pos.ne'
      field_simp [hcard]
    by_contra hne
    have horth := IrreducibleCharacter.characterPairing_eq_zero hne
    rw [hpair] at horth
    exact hchi_ne_zero horth
  · rintro rfl
    intro g _ x
    simp

/-- Source `mem_Iirr_ker1`: the layer between the kernels `1` and `G`
consists exactly of the nontrivial irreducible characters. -/
@[simp]
theorem mem_Iirr_ker1 (chi : IrreducibleCharacter G k) :
    chi ∈ Iirr_kerD (k := k) ⊤ ⊥ ↔
      chi ≠ IrreducibleCharacter.trivial := by
  rw [mem_Iirr_kerD]
  simp only [bot_le, true_and]
  rw [top_le_translationKernel_irreducible_iff]

end

end Submission.OddOrder.PF
