import Submission.OddOrder.BG.Section03.SemidirectProperKernel
import Submission.OddOrder.MathlibSupport.RepresentationSubgroupRestriction

/-!
The proper-kernel recursive branch of Bender-Glauberman Theorem 3.4.
-/

namespace Submission.OddOrder.BG.Section03

open Submission.OddOrder.MathlibSupport

universe u v w

variable {G : Type u} [Group G] [Fintype G]
variable {K R H : Subgroup G}
variable {k : Type v} [Field k]
variable {V : Type w} [AddCommGroup V] [Module k V]

noncomputable section

/-- The strong-induction hypothesis for Theorem 3.4, restricted to
intermediate subgroups of the current ambient group. -/
def OddPrimeSemidirectInductionHypothesis
    (rho : _root_.Representation k G V) : Prop :=
  ∀ (J : Subgroup G) [IsSolvable J] (L T : Subgroup J) [L.Normal],
    Nat.card J < Nat.card G →
    L.IsComplement' T →
    Nat.Coprime (Nat.card L) (Nat.card T) →
    Odd (Nat.card J) →
    (Nat.card T).Prime →
    (Nat.card J : k) ≠ 0 →
    _root_.Representation.invariants
      ((rho.comp J.subtype).comp T.subtype :
        _root_.Representation k T V) = ⊥ →
    ⁅T, L⁆ ≤ (rho.comp J.subtype :
      _root_.Representation k J V).ker

/-- A proper normalized subgroup of the kernel satisfies the desired
commutator bound by strong induction on the generated subgroup. -/
theorem properKernel_commutator_le_representation_ker
    [IsSolvable G]
    (rho : _root_.Representation k G V)
    (hKR : K.IsComplement' R)
    (hcop : Nat.Coprime (Nat.card K) (Nat.card R))
    (hodd : Odd (Nat.card G))
    (hRprime : (Nat.card R).Prime)
    (hGcard : (Nat.card G : k) ≠ 0)
    (hfix : _root_.Representation.invariants
      (rho.comp R.subtype : _root_.Representation k R V) = ⊥)
    (ih : OddPrimeSemidirectInductionHypothesis rho)
    (hHK : H < K)
    (hnorm : R ≤ Subgroup.normalizer (H : Set G)) :
    ⁅R, H⁆ ≤ rho.ker := by
  classical
  let J : Subgroup G := R ⊔ H
  let HJ : Subgroup J := H.subgroupOf J
  let RJ : Subgroup J := R.subgroupOf J
  letI : IsSolvable J := isSolvable_sup
  letI : HJ.Normal :=
    Subgroup.normal_subgroupOf_sup_of_le_normalizer hnorm
  have hlt : Nat.card J < Nat.card G := by
    simpa [J] using natCard_sup_lt_of_properKernel hKR hHK hnorm
  have hcomp : HJ.IsComplement' RJ := by
    simpa [J, HJ, RJ] using
      properKernel_subgroupOf_isComplement hKR hHK.le hnorm
  have hcopJ : Nat.Coprime (Nat.card HJ) (Nat.card RJ) := by
    simpa [J, HJ, RJ] using
      natCard_coprime_subgroupOf_properKernel hcop hHK.le
  have hoddJ : Odd (Nat.card J) := by
    simpa [J] using odd_natCard_sup (H := H) (R := R) hodd
  have hcardRJ : Nat.card RJ = Nat.card R :=
    natCard_subgroupOf_eq (show R ≤ J from le_sup_left)
  have hprimeRJ : (Nat.card RJ).Prime := by rwa [hcardRJ]
  have hJcard : (Nat.card J : k) ≠ 0 := by
    intro hzero
    apply hGcard
    rw [← J.card_mul_index, Nat.cast_mul, hzero, zero_mul]
  have hfixJ : _root_.Representation.invariants
      ((rho.comp J.subtype).comp RJ.subtype :
        _root_.Representation k RJ V) = ⊥ := by
    simpa [RJ] using invariants_comp_subgroupOf_eq_bot rho
      (show R ≤ J from le_sup_left) hfix
  have hlocal : ⁅RJ, HJ⁆ ≤
      (rho.comp J.subtype : _root_.Representation k J V).ker :=
    ih J HJ RJ hlt hcomp hcopJ hoddJ hprimeRJ hJcard hfixJ
  exact commutator_le_ker_of_subgroupOf rho
    (show H ≤ J from le_sup_right) (show R ≤ J from le_sup_left) hlocal

end

end Submission.OddOrder.BG.Section03
