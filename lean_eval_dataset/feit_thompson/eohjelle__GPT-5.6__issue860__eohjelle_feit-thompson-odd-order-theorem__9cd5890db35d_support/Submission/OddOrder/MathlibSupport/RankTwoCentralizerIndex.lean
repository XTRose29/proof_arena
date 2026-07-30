import Submission.OddOrder.MathlibSupport.Section05RankTwoAction
import Submission.OddOrder.MathlibSupport.Centralizer

/-!
# Centralizer index for a normal rank-two elementary subgroup

The conjugation action of a finite `p`-group on a normal elementary-abelian
subgroup of rank two has image of order at most `p`.  Its kernel is the
centralizer of that subgroup, giving the relative-index bound used in
Bender--Glauberman 7.5(b).
-/

namespace Submission.OddOrder.MathlibSupport

universe u

/-- The centralizer in a finite `p`-group of a normal elementary-abelian
rank-two subgroup has relative index at most `p`. -/
theorem centralizerWithin_relIndex_le_prime_of_normal_rank_two
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {P B : Subgroup G}
    (hP : IsPGroup p P) (hBP : B ≤ P)
    (hBnormal : (B.subgroupOf P).Normal)
    (hB : IsElementaryAbelianOfRank p 2 B) :
    (centralizerWithin P B).relIndex P ≤ p := by
  let C : Subgroup G := centralizerWithin P B
  have hnorm : P ≤ Subgroup.normalizer (B : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hBP).mp hBnormal
  let normalizerHom : P →* Subgroup.normalizer (B : Set G) :=
    P.subtype.codRestrict (Subgroup.normalizer (B : Set G)) fun x ↦
      hnorm x.2
  let rho : P →* MulAut B :=
    B.normalizerMonoidHom.comp normalizerHom
  let H : Subgroup P := C.subgroupOf P
  have hker : rho.ker = H := by
    ext x
    change rho x = 1 ↔ (x : G) ∈ C
    change normalizerHom x ∈ B.normalizerMonoidHom.ker ↔
      (x : G) ∈ P ∧ (x : G) ∈ Subgroup.centralizer (B : Set G)
    simp only [x.property, true_and]
    rw [Subgroup.normalizerMonoidHom_ker]
    rfl
  have hquot : Nat.card (P ⧸ rho.ker) ≤ p :=
    section05_natCard_quotient_ker_mulAut_le_prime hP hB rho
  calc
    C.relIndex P = H.index := rfl
    _ = rho.ker.index := by rw [hker]
    _ = Nat.card (P ⧸ rho.ker) := rho.ker.index_eq_card
    _ ≤ p := hquot

end Submission.OddOrder.MathlibSupport
