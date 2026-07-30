import Submission.OddOrder.BG.Section08.NonPCoreFittingMaximalOvergroup

/-!
# Bender--Glauberman Theorem 8.1(b): Fitting reductions

Generic solvable-group reductions used at the start of the SCN branch of
Theorem 8.1.  When the Fitting subgroup is a `p`-group, the `p'`-core is
trivial, the Fitting subgroup is the mapped `p`-core, and hence it lies in
every mapped Sylow `p`-subgroup.
-/

namespace Submission.OddOrder.BG.Section08

open Submission.OddOrder.MathlibSupport

universe u

/-- If the Fitting subgroup of a finite solvable subgroup is a `p`-group,
then its `p'`-core is trivial. -/
theorem pPrimeCore_eq_bot_of_fittingWithin_isPGroup
    {G : Type u} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] (M : Subgroup G)
    (hsol : IsSolvable M)
    (hFp : IsPGroup p (fittingWithin M)) :
    pPrimeCore p M = ⊥ := by
  let eF : fittingCore M ≃* fittingWithin M :=
    (fittingCore M).equivMapOfInjective M.subtype M.subtype_injective
  have hF : IsPGroup p (fittingCore M) :=
    hFp.of_equiv eF.symm
  have hprimeF : pPrimeCore p (fittingCore M) = ⊥ := by
    have hdisjoint : Disjoint (⊤ : Subgroup (fittingCore M))
        (pPrimeCore p (fittingCore M)) :=
      disjoint_pPrimeCore_of_isPGroup (hF.to_subgroup ⊤)
    simpa using hdisjoint
  have hfit : fittingWithin (pPrimeCore p M) = ⊥ := by
    simpa [fittingWithin, hprimeF] using
      (map_fittingCore_pPrimeCore_eq_map_pPrimeCore_fittingCore
        (G := M) p)
  have hsolCore : IsSolvable (pPrimeCore p M) := by
    letI : IsSolvable M := hsol
    infer_instance
  exact eq_bot_of_fittingWithin_eq_bot_of_isSolvable
    (pPrimeCore p M) hsolCore hfit

/-- If the Fitting subgroup of a finite solvable subgroup is a `p`-group,
then it is exactly the ambient image of the `p`-core. -/
theorem fittingWithin_eq_map_pCore_of_isPGroup
    {G : Type u} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] (M : Subgroup G)
    (hsol : IsSolvable M)
    (hFp : IsPGroup p (fittingWithin M)) :
    fittingWithin M = (pCore p M).map M.subtype := by
  rw [fittingWithin,
    fittingCore_eq_pCore_of_pPrimeCore_eq_bot p
      (pPrimeCore_eq_bot_of_fittingWithin_isPGroup p M hsol hFp)]

/-- If the Fitting subgroup of a finite solvable subgroup is a `p`-group,
then it lies in the ambient image of every Sylow `p`-subgroup. -/
theorem fittingWithin_le_map_sylow_of_isPGroup
    {G : Type u} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] (M : Subgroup G) (P : Sylow p M)
    (hsol : IsSolvable M)
    (hFp : IsPGroup p (fittingWithin M)) :
    fittingWithin M ≤ (P : Subgroup M).map M.subtype := by
  rw [fittingWithin_eq_map_pCore_of_isPGroup p M hsol hFp]
  exact Subgroup.map_mono (pCore_le_sylow P)

end Submission.OddOrder.BG.Section08
