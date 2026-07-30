import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Submission.OddOrder.MathlibSupport.Centralizer

/-!
Centralizers of nonidentity elements in prime-order subgroups.
-/

namespace Submission.OddOrder.MathlibSupport

universe u

variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
/-- Every nonidentity element of a prime-order subgroup generates that
subgroup, stated after mapping the cyclic subgroup back to the ambient group. -/
theorem zpowers_eq_of_mem_subgroup_prime_card
    (R : Subgroup G) (hRprime : (Nat.card R).Prime)
    {x : G} (hxR : x ∈ R) (hx : x ≠ 1) :
    Subgroup.zpowers x = R := by
  letI : Fact (Nat.card R).Prime := ⟨hRprime⟩
  let xR : R := ⟨x, hxR⟩
  have hxRne : xR ≠ 1 := by
    intro h
    apply hx
    exact congrArg Subtype.val h
  have hcyclic : Subgroup.zpowers xR = ⊤ :=
    zpowers_eq_top_of_prime_card rfl hxRne
  have hmapped := congrArg (Subgroup.map R.subtype) hcyclic
  simpa [xR, MonoidHom.map_zpowers, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype] using hmapped

omit [Finite G] in
/-- In a prime-order subgroup, centralizing one nonidentity element is
equivalent to centralizing the whole subgroup. -/
theorem centralizerWithin_zpowers_eq_of_mem_prime_card
    (K R : Subgroup G) (hRprime : (Nat.card R).Prime)
    {x : G} (hxR : x ∈ R) (hx : x ≠ 1) :
    centralizerWithin K (Subgroup.zpowers x) = centralizerWithin K R := by
  rw [zpowers_eq_of_mem_subgroup_prime_card R hRprime hxR hx]

end Submission.OddOrder.MathlibSupport
