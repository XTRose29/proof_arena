import Submission.OddOrder.MathlibSupport.PPrimePCore

/-!
Quotient behavior of the two-step `p'`, `p` core.

Quotienting by `O_{p',p}(G)` leaves a group with trivial `p`-core.  The proof
factors the quotient through `G / O_{p'}(G)`; the kernel of the induced map is
the full p-core of that intermediate quotient.
-/

namespace Submission.OddOrder.MathlibSupport

variable {G : Type*} [Group G] [Finite G] {p : ℕ}

/-- The canonical map from the p-prime-core quotient to the two-step-core
quotient. -/
noncomputable def pPrimeCoreQuotientToPPrimePCoreQuotient (p : ℕ)
    (G : Type*) [Group G] [Finite G] :
    (G ⧸ pPrimeCore p G) →* (G ⧸ pPrimePCore p G) :=
  QuotientGroup.lift (pPrimeCore p G)
    (QuotientGroup.mk' (pPrimePCore p G)) (by
      rw [QuotientGroup.ker_mk']
      exact pPrimeCore_le_pPrimePCore)

theorem pPrimeCoreQuotientToPPrimePCoreQuotient_surjective :
    Function.Surjective (pPrimeCoreQuotientToPPrimePCoreQuotient p G) := by
  apply QuotientGroup.lift_surjective_of_surjective
  exact QuotientGroup.mk'_surjective (pPrimePCore p G)

theorem pPrimeCoreQuotientToPPrimePCoreQuotient_ker :
    (pPrimeCoreQuotientToPPrimePCoreQuotient p G).ker =
      pCore p (G ⧸ pPrimeCore p G) := by
  rw [pPrimeCoreQuotientToPPrimePCoreQuotient, QuotientGroup.ker_lift,
    QuotientGroup.ker_mk', pPrimePCore_map_quotient_eq]

/-- The p-core of `G / O_{p',p}(G)` is trivial. -/
theorem pCore_quotient_pPrimePCore_eq_bot :
    pCore p (G ⧸ pPrimePCore p G) = ⊥ := by
  let f := pPrimeCoreQuotientToPPrimePCoreQuotient p G
  let O := pCore p (G ⧸ pPrimeCore p G)
  let Pbar := pCore p (G ⧸ pPrimePCore p G)
  have hf : Function.Surjective f :=
    pPrimeCoreQuotientToPPrimePCoreQuotient_surjective
  have hfker : f.ker = O :=
    pPrimeCoreQuotientToPPrimePCoreQuotient_ker
  have hpreP : IsPGroup p (Pbar.comap f) := by
    apply pCore_isPGroup.comap_of_ker_isPGroup
    rw [hfker]
    exact pCore_isPGroup
  have hpre : Pbar.comap f ≤ O := by
    exact le_pCore hpreP (by infer_instance)
  apply le_antisymm
  · calc
      Pbar = (Pbar.comap f).map f :=
        (Subgroup.map_comap_eq_self_of_surjective hf Pbar).symm
      _ ≤ O.map f := Subgroup.map_mono hpre
      _ = ⊥ := by
        apply (Subgroup.map_eq_bot_iff O).mpr
        rw [hfker]
  · exact bot_le

end Submission.OddOrder.MathlibSupport
