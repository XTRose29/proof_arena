import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Submission.OddOrder.MathlibSupport.ExtraspecialCyclicFixedVector
import Submission.OddOrder.MathlibSupport.ExtraspecialNormalRestrictionNonmodular
import Submission.OddOrder.MathlibSupport.MaschkeNormalConstituent
import Submission.OddOrder.MathlibSupport.RepresentationBaseChange
import Submission.OddOrder.MathlibSupport.SubrepresentationInvariants

/-!
Descent of the extraspecial fixed-vector theorem from an algebraic closure.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped TensorProduct

universe u v w

variable {k : Type u} {A : Type v} {V : Type w}
variable [Field k] [Group A] [Finite A]
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]

noncomputable section

set_option maxHeartbeats 800000 in
/- The nonmodular form of the extraspecial prime-complement fixed-vector
theorem, obtained by scalar extension and an irreducible ambient
constituent. -/
theorem extraspecial_prime_action_invariants_ne_bot_of_card_ne_zero
    {P H : Subgroup A} {p : ℕ}
    (hp : p.Prime) (hpP : IsPGroup p P) (hP : IsExtraspecial P)
    (hHprime : (Nat.card H).Prime)
    (hPH : P.IsComplement' H)
    (hHP : H ≤ Subgroup.normalizer P)
    (hcop : (Nat.card P).Coprime (Nat.card H))
    (hodd : Odd (Nat.card A))
    (hcardA : (Nat.card A : k) ≠ 0)
    (hmapCenter : (Subgroup.center P).map P.subtype ≤ Subgroup.center A)
    (hcentralizer : centralizerWithin P H =
      (Subgroup.center P).map P.subtype)
    (rho : Representation k A V) (hrho : Function.Injective rho) :
    Representation.invariants (rho.comp H.subtype) ≠ ⊥ := by
  classical
  intro hfix
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fact (Nat.card H).Prime := ⟨hHprime⟩
  letI : IsCyclic H := isCyclic_of_prime_card rfl
  letI : P.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff]
    apply top_unique
    rw [← hPH.sup_eq_top]
    exact sup_le Subgroup.le_normalizer hHP
  letI : IsCyclic (A ⧸ P) := by
    let e := hPH.symm.QuotientMulEquiv
    exact isCyclic_of_injective e.toMonoidHom e.injective

  let K := AlgebraicClosure k
  let W := K ⊗[k] V
  let rhoK : Representation K A W := representationBaseChange rho
  have hrhoK : Function.Injective rhoK :=
    representationBaseChange_injective rho hrho
  have hcardAK : (Nat.card A : K) ≠ 0 := by
    intro hzero
    apply hcardA
    apply (algebraMap k K).injective
    simpa [K] using hzero
  have hcardPK : (Nat.card P : K) ≠ 0 := by
    intro hzero
    apply hcardAK
    rw [← P.card_mul_index, Nat.cast_mul, hzero, zero_mul]
  have hfixK : Representation.invariants (rhoK.comp H.subtype) = ⊥ := by
    simpa [rhoK, representationBaseChange, MonoidHom.comp_assoc] using
      representationBaseChange_invariants_eq_bot_of_cyclic
        (A := K) (rho.comp H.subtype) hfix

  let Z : Subgroup A := (Subgroup.center P).map P.subtype
  letI : Z.Normal := by
    constructor
    intro z hz g
    have hzcenter : z ∈ Subgroup.center A := hmapCenter hz
    have hgz : g * z = z * g :=
      Subgroup.mem_center_iff.mp hzcenter g
    simpa [hgz] using hz
  have hZne : Z ≠ ⊥ := by
    intro hZbot
    apply hP.center_ne_bot
    rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    apply Subgroup.mem_bot.mpr
    apply Subtype.ext
    have hzmap : ((z : P) : A) ∈ Z := ⟨z, hz, rfl⟩
    exact Subgroup.mem_bot.mp (hZbot ▸ hzmap)
  have hZnot : ¬ Z ≤ rhoK.ker := by
    intro hle
    apply hZne
    apply le_antisymm
    · rw [← rhoK.ker_eq_bot_iff.mpr hrhoK]
      exact hle
    · exact bot_le
  obtain ⟨U, hU, hUZ⟩ :=
    exists_irreducible_subrepresentation_not_le_ker_of_normal
      rhoK Z hcardAK hZnot
  letI := hU
  let sigma := U.toRepresentation
  let sigmaP := sigma.comp P.subtype
  have hfixSigma :=
    subrepresentation_invariants_eq_bot rhoK H U hfixK

  have hcenterNot : ¬ Subgroup.center P ≤ sigmaP.ker := by
    intro hle
    apply hUZ
    rintro a ⟨z, hz, rfl⟩
    have hzker := hle hz
    rw [MonoidHom.mem_ker] at hzker ⊢
    exact hzker
  have hsigmaP : Function.Injective sigmaP := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases hP.normal_eq_bot_or_center_le hpP sigmaP.ker with
      hbot | hcenterLe
    · exact hbot
    · exact False.elim (hcenterNot hcenterLe)

  obtain ⟨T, hT, hTcenter⟩ :=
    exists_irreducible_subrepresentation_not_le_ker_of_normal
      (k := K) (G := P) (V := U.toSubmodule)
      sigmaP (Subgroup.center P) hcardPK hcenterNot
  letI := hT
  let tau := T.toRepresentation
  have htau : Function.Injective tau := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases hP.normal_eq_bot_or_center_le hpP tau.ker with
      hbot | hcenterLe
    · exact hbot
    · exact False.elim (hTcenter hcenterLe)
  have htauExact := htau
  dsimp [tau] at htauExact
  have hcentralTop :
      Subgroup.centralizer (centerWithin P : Set A) = ⊤ := by
    apply top_unique
    intro g _
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hzcenter : z ∈ Subgroup.center A := by
      apply hmapCenter
      rw [map_center_eq_centerWithin P]
      exact hz
    exact (Subgroup.mem_center_iff.mp hzcenter g).symm
  have hsigmaPIrr :=
    @IsExtraspecial.normalRestriction_irreducible_of_quotient_isCyclic_of_card_ne_zero
      K A U.toSubmodule _ _ _ _ _ _ _ p _ P _ _ hP hpP hcardPK
        sigma hU T hT htauExact hcentralTop
  letI := hsigmaPIrr

  have hcore :=
    @extraspecial_prime_action_invariants_ne_bot K A U.toSubmodule
      _ _ _ _ _ _ _ P H p hp hpP hP hHprime hHP hcop hodd hcardAK
        hmapCenter hcentralizer sigma hsigmaPIrr hsigmaP
  exact hcore hfixSigma

end

end Submission.OddOrder.MathlibSupport
