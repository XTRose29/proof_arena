import Submission.OddOrder.BG.Section03.OddPrimeSemidirectProperKernel

/-!
The ambient-group form of the strong induction used in
Bender-Glauberman Theorem 3.4.

The local reductions naturally recurse to subgroups of the current group,
while the faithful-constituent reduction recurses to a quotient.  This file
packages the common cardinality induction interface and recovers the local
subgroup interface used by the earlier reductions.
-/

namespace Submission.OddOrder.BG.Section03

universe u v w

noncomputable section

/-- The strong-induction hypothesis for Theorem 3.4 over arbitrary finite
groups in the current universe. -/
def OddPrimeSemidirectGlobalInductionHypothesis
    (k : Type v) [Field k] (bound : Nat) : Prop :=
  ∀ (J : Type u) [Group J] [Fintype J] [IsSolvable J]
    (W : Type w) [AddCommGroup W] [Module k W] [Finite W]
    (rhoJ : _root_.Representation k J W)
    (L T : Subgroup J) [L.Normal],
    Nat.card J < bound →
    L.IsComplement' T →
    Nat.Coprime (Nat.card L) (Nat.card T) →
    Odd (Nat.card J) →
    (Nat.card T).Prime →
    (Nat.card J : k) ≠ 0 →
    _root_.Representation.invariants
      (rhoJ.comp T.subtype : _root_.Representation k T W) = ⊥ →
    ⁅T, L⁆ ≤ rhoJ.ker

/-- Global cardinality induction supplies the subgroup induction hypothesis
used by the proper-kernel branch. -/
theorem OddPrimeSemidirectGlobalInductionHypothesis.toSubgroup
    {G : Type u} [Group G] [Fintype G]
    {k : Type v} [Field k]
    {V : Type w} [AddCommGroup V] [Module k V] [Finite V]
    (ih : OddPrimeSemidirectGlobalInductionHypothesis.{u, v, w}
      k (Nat.card G))
    (rho : _root_.Representation k G V) :
    OddPrimeSemidirectInductionHypothesis rho := by
  classical
  intro J _ L T _ hlt hcomp hcop hodd hprime hcard hfix
  letI : Fintype J := Fintype.ofFinite J
  exact ih J V (rho.comp J.subtype) L T hlt hcomp hcop hodd hprime hcard hfix

end

end Submission.OddOrder.BG.Section03
