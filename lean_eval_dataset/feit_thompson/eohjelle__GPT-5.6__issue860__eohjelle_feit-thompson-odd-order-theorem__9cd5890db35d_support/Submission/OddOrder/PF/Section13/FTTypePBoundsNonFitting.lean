import Submission.OddOrder.PF.Section13.FTTypePCyclicCover

/-!
# Peterfalvi Section 13: the non-Fitting lower bound

This module exposes Peterfalvi (13.9)(b) from the cyclic-generator cover.
-/

namespace Submission.OddOrder.PF

noncomputable section

open Submission.OddOrder.MathlibSupport
open Submission.OddOrder.BG.Section07
open scoped BigOperators Classical

variable {G : Type} [Group G] [Finite G] [IsMinSimpleOddGroup G]
variable {S U W W₁ W₂ : Subgroup G}
variable {defW : IsInternalDirectProductIn W₁ W₂ W}

attribute [local instance 10] cyclicCoverFintype

/-- `PFsection13.v: FTtypeP_sum_nonFitting_lb`, Peterfalvi (13.9)(b). -/
theorem FTtypeP_sum_nonFitting_lb
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (K : Subgroup G)
    (tau1 : ClassFunction S ℂ →ₗ[ℂ] ClassFunction G ℂ)
    (lambda : ClassFunction S ℂ)
    (hcoh : @coherent_with S G
      _ S.instFintypeSubtypeMemOfDecidablePred _ (cyclicCoverFintype G)
      (↑(ftTypePCoreFamily S) : Set (ClassFunction S ℂ))
      (nonidentitySet S) ctx.tau tau1)
    (hTIred : typeP_TIred_coherent ctx tau1)
    (hcalS : lambda ∈ ftTypePCoreFamily S)
    (hirr : lambda ∈ irr_Ind_Fitting S) :
    (ftTypePSetCard (ftTypePNonFittingSet ctx K) : ℝ) ≤
      ∑ x ∈ FTTypePBoundsInfrastructureInternal.finiteSet
          (ftTypePNonFittingSet ctx K),
        (Complex.normSq (tau1 lambda x) +
          Complex.normSq (ftTypePEta10 ctx x)) :=
  FTTypePCyclicCoverInternal.sum_nonFitting_lb
    ctx K tau1 lambda hcoh hTIred hcalS hirr

end

end Submission.OddOrder.PF
