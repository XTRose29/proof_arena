import Mathlib.Analysis.Real.Sqrt
import Submission.OddOrder.MathlibSupport.IrreducibleDegreeIndexBound
import Submission.OddOrder.MathlibSupport.IrreducibleHallExtensionFDRep
import Submission.OddOrder.MathlibSupport.QuotientCentralScalarAction
import Submission.OddOrder.PF.Section01.IrreducibleCharacterTranslationKernel
import Submission.OddOrder.PF.Section01.NonzeroCharacterConstituent

/-!
# Peterfalvi 1.8: an irreducible degree bound

The restriction of an ambient irreducible character to `C` has an
irreducible constituent.  A subgroup central modulo a subgroup in its
kernel acts by scalars on that constituent, so Burnside density bounds the
square of its degree by `[C : D]`.  Frobenius reciprocity and induction then
give the ambient factor `[G : C]`.
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped Classical
open CategoryTheory

universe u

namespace ClassFunction

variable {G k : Type u} [Group G] [Fintype G]
  [Field k] [IsAlgClosed k] [CharZero k]

/-- Representation-kernel form of Peterfalvi 1.8. -/
theorem irr1_bound_quo_of_le_representation_ker
    (B C D : Subgroup G)
    (hBC : B ≤ C) [hBnC : (B.subgroupOf C).Normal]
    (hBD : B ≤ D) (hDC : D ≤ C)
    (chi : IrreducibleCharacter G k)
    (hBker : B ≤ chi.representation.ρ.ker)
    (hcenter :
      (D.subgroupOf C).map
          (QuotientGroup.mk' (B.subgroupOf C)) ≤
        Subgroup.center (C ⧸ B.subgroupOf C)) :
    (Module.finrank k chi.representation : ℝ) ≤
      (C.index : ℝ) *
        Real.sqrt ((D.subgroupOf C).index : ℝ) := by
  let K := B.subgroupOf C
  let L := D.subgroupOf C
  let R : FDRep k C := FDRep.restrictToSubgroup C chi.representation
  letI : Fintype C := Fintype.ofFinite _
  letI : Fintype K := Fintype.ofFinite _
  letI : Invertible (Nat.card C : k) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Simple chi.representation := chi.representation_simple
  letI : Nontrivial chi.representation :=
    FDRep.nontrivial_of_simple chi.representation
  letI : Nontrivial R := by
    dsimp only [R, FDRep.restrictToSubgroup]
    infer_instance
  obtain ⟨psi, hpsiR⟩ :=
    exists_irreducible_constituent_of_nontrivial R
  have hRchar : ofRepresentation R.ρ =
      restrict C (chi : ClassFunction G k) := by
    rw [FDRep.ofRepresentation_restrictToSubgroup,
      chi.ofRepresentation_representation]
  have hpsiRes : psi.IsConstituent
      (restrict C (chi : ClassFunction G k)) := by
    rwa [← hRchar]
  have hchiInd : chi.IsConstituent
      (induce C (psi : ClassFunction C k)) :=
    (psi.isConstituent_restrict_iff_induce C chi).1 hpsiRes
  have hKkerR : K ≤ R.ρ.ker := by
    intro b hb
    rw [MonoidHom.mem_ker]
    change chi.representation.ρ ((b : C) : G) = 1
    exact MonoidHom.mem_ker.mp (hBker hb)
  have hRkerPsi : R.ρ.ker ≤ psi.representation.ρ.ker :=
    FDRep.ker_le_irreducible_ker_of_isConstituent R psi hpsiR
  have hKkerPsi : K ≤ psi.representation.ρ.ker :=
    hKkerR.trans hRkerPsi
  letI : Simple psi.representation := psi.representation_simple
  letI : Representation.IsIrreducible psi.representation.ρ :=
    _root_.Submission.OddOrder.MathlibSupport.representation_isIrreducible_of_simple_fdRep
      psi.representation
  have hscalar : ∀ d : L, ∃ c : k,
      psi.representation.ρ (d : C) =
        c • (1 : Module.End k psi.representation) :=
    _root_.Submission.OddOrder.MathlibSupport.subgroup_acts_scalar_of_map_le_quotient_center
        K L psi.representation.ρ hKkerPsi hcenter
  have hpsiSq : Module.finrank k psi.representation ^ 2 ≤ L.index :=
    _root_.Submission.OddOrder.MathlibSupport.Representation.IsIrreducible.finrank_sq_le_index_of_scalar_subgroup
        psi.representation.ρ L hscalar
  let W : FDRep k G := FDRep.induceFromSubgroup C psi.representation
  have hWchar : ofRepresentation W.ρ =
      induce C (psi : ClassFunction C k) := by
    dsimp only [W]
    exact (ofRepresentation_induceFromSubgroup_general
      C psi.representation).trans
        (congrArg (induce C) psi.ofRepresentation_representation)
  have hchiW : chi.IsConstituent (ofRepresentation W.ρ) := by
    rwa [hWchar]
  have hdegreeLe : Module.finrank k chi.representation ≤
      Module.finrank k W :=
    FDRep.finrank_irreducible_le_of_isConstituent W chi hchiW
  have hWdim : Module.finrank k W =
      C.index * Module.finrank k psi.representation := by
    apply Nat.cast_injective (R := k)
    calc
      (Module.finrank k W : k) = W.character 1 := (FDRep.char_one W).symm
      _ = ofRepresentation W.ρ 1 := rfl
      _ = induce C (psi : ClassFunction C k) 1 := by rw [hWchar]
      _ = (C.index : k) * psi 1 := induce_one C _
      _ = (C.index : k) *
          (Module.finrank k psi.representation : k) := by
        rw [IrreducibleCharacter.apply_one_eq_finrank]
      _ = (C.index * Module.finrank k psi.representation : ℕ) := by
        rw [Nat.cast_mul]
  have hdegreeNat : Module.finrank k chi.representation ≤
      C.index * Module.finrank k psi.representation := by
    rw [← hWdim]
    exact hdegreeLe
  have hdegreeReal : (Module.finrank k chi.representation : ℝ) ≤
      (C.index : ℝ) *
        (Module.finrank k psi.representation : ℝ) := by
    exact_mod_cast hdegreeNat
  have hpsiSqReal :
      (Module.finrank k psi.representation : ℝ) ^ 2 ≤
        (L.index : ℝ) := by
    exact_mod_cast hpsiSq
  have hsqrtSq : Real.sqrt (L.index : ℝ) ^ 2 = (L.index : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hpsiSqrt : (Module.finrank k psi.representation : ℝ) ≤
      Real.sqrt (L.index : ℝ) := by
    have hdegreeNonneg :
        0 ≤ (Module.finrank k psi.representation : ℝ) := by positivity
    have hsqrtNonneg : 0 ≤ Real.sqrt (L.index : ℝ) :=
      Real.sqrt_nonneg _
    nlinarith
  exact hdegreeReal.trans
    (mul_le_mul_of_nonneg_left hpsiSqrt (by positivity))

/-- Peterfalvi 1.8, source `irr1_bound_quo`. -/
theorem irr1_bound_quo
    (B C D : Subgroup G)
    (hBC : B ≤ C) [hBnC : (B.subgroupOf C).Normal]
    (hBD : B ≤ D) (hDC : D ≤ C)
    (chi : IrreducibleCharacter G k)
    (hBker : B ≤ translationKernel (chi : ClassFunction G k))
    (hcenter :
      (D.subgroupOf C).map
          (QuotientGroup.mk' (B.subgroupOf C)) ≤
        Subgroup.center (C ⧸ B.subgroupOf C)) :
    (Module.finrank k chi.representation : ℝ) ≤
      (C.index : ℝ) *
        Real.sqrt ((D.subgroupOf C).index : ℝ) := by
  apply irr1_bound_quo_of_le_representation_ker
    B C D hBC hBD hDC chi
  · rw [← translationKernel_irreducibleCharacter chi]
    exact hBker
  · exact hcenter

end ClassFunction

end

end Submission.OddOrder.PF
