import Submission.OddOrder.BG.AppendixAB.PStableGenerated
import Submission.OddOrder.BG.AppendixAB.PuigPCore
import Submission.OddOrder.MathlibSupport.PCoreFunctorial

/-!
Lifting the A.5.1 quotient conclusion back to the ambient `p`-core.

The remaining group-theoretic input in A.5.2 is that `C_G(P)` is a `p`-group
under the solvability, trivial `p'`-core, and centralizer hypotheses.  This file
proves everything after that input and records its exact shape for B.3.
-/

namespace Submission.OddOrder.BG.AppendixAB

open Submission.OddOrder.BG.Section01
open Submission.OddOrder.MathlibSupport

variable {G : Type*} [Group G] [Finite G]

/-- The quotient-lifting half of Bender-Glauberman A.5.2. -/
theorem abelianGenerated_le_pCore_of_isPStable_of_centralizer_isPGroup
    {p : ℕ} {P X : Subgroup G} [P.Normal]
    (hstable : IsPStable p G) (hP : IsPGroup p P)
    (hgen : GeneratedBy (PNormalizedAbelian p P) X)
    (hC : IsPGroup p (Subgroup.centralizer (P : Set G))) :
    X ≤ pCore p G := by
  let C := Subgroup.centralizer (P : Set G)
  let q := QuotientGroup.mk' C
  have hmap : X.map q ≤ pCore p (G ⧸ C) := by
    exact abelianGenerated_quotient_le_pCore_of_isPStable hstable hP hgen
  rw [← map_pCore_quotient_eq hC, Subgroup.map_le_map_iff,
    QuotientGroup.ker_mk'] at hmap
  have hCcore : C ≤ pCore p G := le_pCore hC (by infer_instance)
  simpa [sup_eq_left.mpr hCcore] using hmap

/-- Reduction of the B.3 constrained-generator input to the exact
centralizer-is-a-`p`-group statement proved by the coprime-action part of
A.5.2. -/
theorem abelianGeneratedConstrained_of_isPStable_of_centralizer_isPGroup
    {p : ℕ} (hstable : IsPStable p G)
    (hcentralizer : ∀ {P : Subgroup G},
      IsPGroup p P → P.Normal →
      pPrimeCore p G = ⊥ →
      centralizerWithin (pCore p G) P ≤ P →
      IsPGroup p (Subgroup.centralizer (P : Set G))) :
    AbelianGeneratedConstrained p G := by
  intro P X hP hPnormal hgen hprimeCore hcent
  letI : P.Normal := hPnormal
  exact abelianGenerated_le_pCore_of_isPStable_of_centralizer_isPGroup
    hstable hP hgen (hcentralizer hP hPnormal hprimeCore hcent)

end Submission.OddOrder.BG.AppendixAB
