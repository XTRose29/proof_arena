import Submission.OddOrder.MathlibSupport.ElementaryAbelianRepresentation
import Submission.OddOrder.MathlibSupport.ElementaryAbelian
import Submission.OddOrder.MathlibSupport.PSubgroupGeneralLinearTwo

/-!
The cardinal bound for a `p`-group acting on an elementary-abelian group of
rank two.  This is the linear-action estimate used twice in
Bender--Glauberman Lemma 5.2.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped IsMulCommutative

universe u v

variable {G : Type u} {K : Type v} [Group G] [Finite G] [Group K]
variable {p : ℕ} [Fact p.Prime]

/-- The quotient by the kernel of a `p`-group action on an
elementary-abelian rank-two group has cardinality at most `p`. -/
theorem section05_natCard_quotient_ker_mulAut_le_prime
    [Finite K] (hK : IsPGroup p K) {E : Subgroup G}
    (hE : IsElementaryAbelianOfRank p 2 E) (rho : K →* MulAut E) :
    Nat.card (K ⧸ rho.ker) ≤ p := by
  letI : IsMulCommutative E := hE.commutative
  letI : AddCommGroup (Additive E) := inferInstance
  letI : Module (ZMod p) (Additive E) :=
    elementaryAbelianZModModule E p hE.pow_eq_one
  let linearize :
      MulAut E →* LinearMap.GeneralLinearGroup (ZMod p) (Additive E) :=
    (mulAutRepresentation E p).asGroupHom
  let rhoGL :
      K →* LinearMap.GeneralLinearGroup (ZMod p) (Additive E) :=
    linearize.comp rho
  have hker : rhoGL.ker = rho.ker :=
    MonoidHom.ker_comp_of_injective rho linearize
      (mulAutRepresentation_asGroupHom_injective E p)
  have hRangeP : IsPGroup p rhoGL.range := by
    rw [rhoGL.range_eq_map]
    exact (hK.to_subgroup (⊤ : Subgroup K)).map rhoGL
  letI : Finite rhoGL.range :=
    Finite.of_surjective rhoGL.rangeRestrict
      rhoGL.rangeRestrict_surjective
  have hEcard : Nat.card (Additive E) = p ^ 2 :=
    (Nat.card_congr Additive.ofMul).trans hE.card_eq
  have hRangeCard : Nat.card rhoGL.range ≤ p :=
    natCard_le_prime_of_isPGroup_subgroup_linearGL_card_le_sq
      rhoGL.range hRangeP (by rw [hEcard])
  calc
    Nat.card (K ⧸ rho.ker) = Nat.card (K ⧸ rhoGL.ker) := by rw [hker]
    _ = Nat.card rhoGL.range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange rhoGL).toEquiv
    _ ≤ p := hRangeCard

end Submission.OddOrder.MathlibSupport
