import Submission.OddOrder.MathlibSupport.ElementaryAbelian
import Submission.OddOrder.MathlibSupport.ElementaryAbelianRepresentation
import Submission.OddOrder.MathlibSupport.NormalSubgroupPowerSeries
import Submission.OddOrder.MathlibSupport.PSubgroupGeneralLinearTwo
import Submission.OddOrder.MathlibSupport.SelfCentralizing
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.Exponent

/-!
Bender--Glauberman Proposition 4.8(a).

MathComp states the hypothesis using numerical `p`-rank.  As elsewhere in
this port, rank at most two is expanded into the absence of an elementary
abelian subgroup of rank three.
-/

namespace Submission.OddOrder.BG.Section04

open Submission.OddOrder.MathlibSupport
open scoped IsMulCommutative

universe u

variable {G : Type u} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]

/-- `BGsection4.v: rank2_exponent_p_p3group` (Proposition 4.8(a)). -/
theorem natCard_le_prime_cube_of_exponent_prime_of_no_elementaryAbelian_rank_three
    (hG : IsPGroup p G)
    (hrank : ¬ ∃ E : Subgroup G, IsElementaryAbelianOfRank p 3 E)
    (hexponent : Monoid.exponent G ∣ p) :
    Nat.card G ≤ p ^ 3 := by
  classical
  have hpowG : ∀ g : G, g ^ p = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hexponent
  obtain ⟨M, hM, hcentralizer⟩ :=
    exists_selfCentralizing_isNormalAbelian hG
  letI : M.Normal := hM.normal
  letI : IsMulCommutative M := hM.isMulCommutative
  have hMp : IsPGroup p M := hG.to_subgroup M
  have hMpow : ∀ x : M, x ^ p = 1 := by
    intro x
    apply Subtype.ext
    exact hpowG x
  obtain ⟨n, hMcard⟩ := hMp.exists_card_eq
  have hn : n ≤ 2 := by
    by_contra hnle
    have hthree : 3 ≤ n := by omega
    obtain ⟨E, hEM, _hEnormal, hEcard⟩ :=
      exists_normal_subgroup_card_pow_le hG M hMcard hthree
    have hEcomm : IsMulCommutative E := by
      apply isMulCommutative_iff.mpr
      intro x y
      apply Subtype.ext
      change (x : G) * (y : G) = (y : G) * (x : G)
      exact congrArg (fun z : M => (z : G))
        (mul_comm (⟨x, hEM x.2⟩ : M) ⟨y, hEM y.2⟩)
    apply hrank
    refine ⟨E,
      { isPGroup := hG.to_subgroup E
        commutative := hEcomm
        pow_eq_one := ?_
        card_eq := hEcard }⟩
    intro x
    apply Subtype.ext
    exact hpowG x
  letI hAddCommGroup : AddCommGroup (Additive M) := inferInstance
  letI hModule : Module (ZMod p) (Additive M) :=
    elementaryAbelianZModModule M p hMpow
  let normalizerHom : G →* Subgroup.normalizer (M : Set G) :=
    (MonoidHom.id G).codRestrict (Subgroup.normalizer (M : Set G)) fun g => by
      rw [Subgroup.normalizer_eq_top_iff.mpr hM.normal]
      trivial
  let rhoAut := M.normalizerMonoidHom.comp normalizerHom
  have hrhoAutKer : rhoAut.ker = M := by
    ext g
    change normalizerHom g ∈ M.normalizerMonoidHom.ker ↔ g ∈ M
    rw [Subgroup.normalizerMonoidHom_ker]
    change g ∈ Subgroup.centralizer (M : Set G) ↔ g ∈ M
    simpa only [hcentralizer]
  let linearize := (mulAutRepresentation M p).asGroupHom
  let rhoGL := linearize.comp rhoAut
  have hrhoGLKerEq : rhoGL.ker = rhoAut.ker :=
    MonoidHom.ker_comp_of_injective rhoAut linearize
      (mulAutRepresentation_asGroupHom_injective M p)
  have hrhoGLKer : rhoGL.ker = M := hrhoGLKerEq.trans hrhoAutKer
  have hMcardLe : Nat.card M ≤ p ^ 2 := by
    rw [hMcard]
    exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos hn
  have hAddCardLe : Nat.card (Additive M) ≤ p ^ 2 := by
    calc
      Nat.card (Additive M) = Nat.card M := Nat.card_congr Additive.ofMul
      _ ≤ p ^ 2 := hMcardLe
  have hRangeP : IsPGroup p rhoGL.range := by
    rw [rhoGL.range_eq_map]
    exact (hG.to_subgroup (⊤ : Subgroup G)).map rhoGL
  have hRangeCard : Nat.card rhoGL.range ≤ p :=
    natCard_le_prime_of_isPGroup_subgroup_linearGL_card_le_sq
      rhoGL.range hRangeP hAddCardLe
  have hQcard : Nat.card (G ⧸ rhoGL.ker) ≤ p := by
    calc
      Nat.card (G ⧸ rhoGL.ker) = Nat.card rhoGL.range :=
        Nat.card_congr (QuotientGroup.quotientKerEquivRange rhoGL).toEquiv
      _ ≤ p := hRangeCard
  calc
    Nat.card G = Nat.card (G ⧸ rhoGL.ker) * Nat.card rhoGL.ker :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup rhoGL.ker
    _ = Nat.card (G ⧸ rhoGL.ker) * Nat.card M := by rw [hrhoGLKer]
    _ ≤ p * p ^ 2 := Nat.mul_le_mul hQcard hMcardLe
    _ = p ^ 3 := by ring

end Submission.OddOrder.BG.Section04
