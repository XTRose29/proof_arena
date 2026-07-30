import Submission.OddOrder.MathlibSupport.PCore

/-!
Functoriality of the `p`-core under surjective homomorphisms.

The reverse inclusion requires the kernel to be a `p`-group, so that the
preimage of the target `p`-core is again a normal `p`-subgroup.
-/

namespace Submission.OddOrder.MathlibSupport

variable {G K : Type*} [Group G] [Group K] {p : ℕ}

theorem map_pCore_le_of_surjective (f : G →* K) (hf : Function.Surjective f) :
    (pCore p G).map f ≤ pCore p K :=
  le_pCore (pCore_isPGroup.map f)
    (Subgroup.Normal.map (by infer_instance) f hf)

theorem map_pCore_eq_of_surjective_of_ker_isPGroup (f : G →* K)
    (hf : Function.Surjective f) (hker : IsPGroup p f.ker) :
    (pCore p G).map f = pCore p K := by
  apply le_antisymm (map_pCore_le_of_surjective f hf)
  have hpreP : IsPGroup p ((pCore p K).comap f) :=
    pCore_isPGroup.comap_of_ker_isPGroup f hker
  have hpre : (pCore p K).comap f ≤ pCore p G :=
    le_pCore hpreP (by infer_instance)
  calc
    pCore p K = ((pCore p K).comap f).map f :=
      (Subgroup.map_comap_eq_self_of_surjective hf _).symm
    _ ≤ (pCore p G).map f := Subgroup.map_mono hpre

theorem map_pCore_quotient_eq {N : Subgroup G} [N.Normal] (hN : IsPGroup p N) :
    (pCore p G).map (QuotientGroup.mk' N) = pCore p (G ⧸ N) := by
  apply map_pCore_eq_of_surjective_of_ker_isPGroup
  · exact QuotientGroup.mk'_surjective N
  · rw [QuotientGroup.ker_mk']
    exact hN

end Submission.OddOrder.MathlibSupport
