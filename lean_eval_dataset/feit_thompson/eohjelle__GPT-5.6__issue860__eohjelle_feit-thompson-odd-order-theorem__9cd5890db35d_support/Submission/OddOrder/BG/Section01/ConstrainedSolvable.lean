import Submission.OddOrder.BG.Section01.Constrained
import Submission.OddOrder.MathlibSupport.PPrimePCoreSylow

/-!
Finite solvable groups are `p`-constrained.

This is the mathlib-shaped form of Bender-Glauberman Proposition 1.15a.  The
proof passes to `G / O_{p'}(G)`, where the image of the chosen Sylow subgroup
is the full `p`-core and the p-prime core is trivial.  The Fitting
self-centralizer theorem then gives the required inclusion.
-/

namespace Submission.OddOrder.BG.Section01

open Submission.OddOrder.MathlibSupport

variable {G : Type*} [Group G] [Finite G]

theorem solvable_isPConstrained {p : ℕ} [Fact p.Prime] [IsSolvable G] :
    IsPConstrained p G := by
  intro P x hx
  let N : Subgroup G := pPrimeCore p G
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  let O : Subgroup (G ⧸ N) := pCore p (G ⧸ N)
  have hcentQ : Subgroup.centralizer (O : Set (G ⧸ N)) ≤ O := by
    apply centralizer_pCore_le_pCore_of_pPrimeCore_eq_bot
    exact pPrimeCore_quotient_self_eq_bot
  change q x ∈ O
  apply hcentQ
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hPmap : (sylowInAmbient P).map q = O := by
    simpa [sylowInAmbient, N, q, O] using
      sylow_pPrimePCore_map_quotient_eq P
  have hyMap : y ∈ (sylowInAmbient P).map q := by
    rw [hPmap]
    exact hy
  obtain ⟨z, hz, rfl⟩ := hyMap
  have hzx := Subgroup.mem_centralizer_iff.mp hx z hz
  simpa using congrArg q hzx

end Submission.OddOrder.BG.Section01
