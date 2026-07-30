import Submission.OddOrder.BG.AppendixAB.QuadraticAnticommutatorCentral
import Submission.OddOrder.MathlibSupport.CentralIntertwining

/-!
The quadratic central operator as an intertwining endomorphism.
-/

namespace Submission.OddOrder.BG.AppendixAB

open scoped IsMulCommutative
open Submission.OddOrder.BG.Section01
open Submission.OddOrder.MathlibSupport

variable {G : Type*} [Group G]

/-- The anticommutator centralizing the local two-generator representation,
bundled as an intertwining endomorphism. -/
def quadraticCentralIntertwining
    (E : Subgroup G) (p : ℕ) [IsMulCommutative E]
    [Module (ZMod p) (Additive E)]
    {x y : G}
    (hxN : x ∈ Subgroup.normalizer (E : Set G))
    (hyN : y ∈ Subgroup.normalizer (E : Set G))
    (hx : IsQuadraticPElement p E x)
    (hy : IsQuadraticPElement p E y) :
    let q := QuotientGroup.mk' (normalizerCentralizer E)
    let Q := pairGenerated (q ⟨x, hxN⟩) (q ⟨y, hyN⟩)
    let rho := localSubgroupConjugationRepresentation E p Q
    Representation.IntertwiningMap rho rho := by
  dsimp only
  let q := QuotientGroup.mk' (normalizerCentralizer E)
  let xq := q ⟨x, hxN⟩
  let yq := q ⟨y, hyN⟩
  let Q := pairGenerated xq yq
  let rho := localSubgroupConjugationRepresentation E p Q
  let A := quadraticAnticommutator E p ⟨x, hxN⟩ ⟨y, hyN⟩
  apply centralIntertwiningMap rho A
  intro z
  exact quadraticAnticommutator_commutes_quotient_pairGenerated
    E p hxN hyN hx hy z

@[simp]
theorem quadraticCentralIntertwining_toLinearMap
    (E : Subgroup G) (p : ℕ) [IsMulCommutative E]
    [Module (ZMod p) (Additive E)]
    {x y : G}
    (hxN : x ∈ Subgroup.normalizer (E : Set G))
    (hyN : y ∈ Subgroup.normalizer (E : Set G))
    (hx : IsQuadraticPElement p E x)
    (hy : IsQuadraticPElement p E y) :
    (quadraticCentralIntertwining E p hxN hyN hx hy).toLinearMap =
      quadraticAnticommutator E p ⟨x, hxN⟩ ⟨y, hyN⟩ :=
  rfl

end Submission.OddOrder.BG.AppendixAB
