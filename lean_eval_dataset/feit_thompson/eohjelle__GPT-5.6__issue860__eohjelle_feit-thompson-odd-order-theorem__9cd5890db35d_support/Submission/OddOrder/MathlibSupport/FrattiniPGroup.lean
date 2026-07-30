import Mathlib.GroupTheory.Frattini
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Algebra.Module.ZMod
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Submission.OddOrder.MathlibSupport.ElementaryAbelianSubmodule

/-!
Frattini-quotient support for finite `p`-groups.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped IsMulCommutative

universe u

variable {G : Type u} [Group G]

/-- A quotient by a maximal normal subgroup is simple. -/
theorem isSimpleGroup_quotient_of_isCoatom {H : Subgroup G} [H.Normal]
    (hH : IsCoatom H) : IsSimpleGroup (G ⧸ H) := by
  letI : Nontrivial (G ⧸ H) :=
    QuotientGroup.nontrivial_iff.mpr hH.ne_top
  refine ⟨fun K _ ↦ ?_⟩
  have hle := QuotientGroup.le_comap_mk' H K
  rcases hH.le_iff.mp hle with htop | hbot
  · right
    apply Subgroup.comap_injective (QuotientGroup.mk'_surjective H)
    simpa using htop
  · left
    apply Subgroup.comap_injective (QuotientGroup.mk'_surjective H)
    simpa using hbot

namespace IsPGroup

variable {p : ℕ} [Fact p.Prime] [Finite G]

/-- Every maximal subgroup of a finite `p`-group is normal. -/
theorem isCoatom_normal (hpG : IsPGroup p G) {H : Subgroup G}
    (hH : IsCoatom H) : H.Normal := by
  letI : Group.IsNilpotent G := hpG.isNilpotent
  have hnormal : ∀ K : Subgroup G, IsCoatom K → K.Normal :=
    (Group.isNilpotent_of_finite_tfae.out 0 2).mp (by infer_instance)
  exact hnormal H hH

/-- A maximal-subgroup quotient of a finite `p`-group has cardinality `p`. -/
theorem card_quotient_isCoatom (hpG : IsPGroup p G) {H : Subgroup G}
    (hH : IsCoatom H) : Nat.card (G ⧸ H) = p := by
  letI : H.Normal := isCoatom_normal hpG hH
  letI : IsSimpleGroup (G ⧸ H) := isSimpleGroup_quotient_of_isCoatom hH
  have hpQ : IsPGroup p (G ⧸ H) := hpG.to_quotient H
  letI : Group.IsNilpotent (G ⧸ H) := hpQ.isNilpotent
  letI : IsCyclic (G ⧸ H) := inferInstance
  have hcardPrime : (Nat.card (G ⧸ H)).Prime := IsSimpleGroup.prime_card
  have hcardNeOne : Nat.card (G ⧸ H) ≠ 1 := hcardPrime.ne_one
  have hpDvd : p ∣ Nat.card (G ⧸ H) :=
    hpQ.card_eq_or_dvd.resolve_left hcardNeOne
  have hpPrime : p.Prime := Fact.out
  exact ((Nat.dvd_prime hcardPrime).mp hpDvd).resolve_left
    hpPrime.ne_one |>.symm

/-- Every `p`th power in a finite `p`-group belongs to its Frattini
subgroup. -/
theorem pow_prime_mem_frattini (hpG : IsPGroup p G) (x : G) :
    x ^ p ∈ frattini G := by
  rw [frattini, Order.radical]
  simp only [Subgroup.mem_iInf]
  intro H hH
  change IsCoatom H at hH
  letI : H.Normal := isCoatom_normal hpG hH
  apply (QuotientGroup.eq_one_iff (x ^ p)).mp
  change (x : G ⧸ H) ^ p = 1
  rw [← card_quotient_isCoatom hpG hH]
  exact pow_card_eq_one'

/-- The Frattini quotient of a finite `p`-group has exponent dividing `p`. -/
theorem quotient_frattini_pow_prime (hpG : IsPGroup p G)
    (x : G ⧸ frattini G) : x ^ p = 1 := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (frattini G) x
  change ((x ^ p : G) : G ⧸ frattini G) = 1
  exact (QuotientGroup.eq_one_iff (x ^ p)).mpr
    (pow_prime_mem_frattini hpG x)

/-- The commutator subgroup of a finite `p`-group lies in its Frattini
subgroup. -/
theorem commutator_le_frattini (hpG : IsPGroup p G) :
    _root_.commutator G ≤ frattini G := by
  rw [frattini, Order.radical, le_iInf_iff]
  intro H
  rw [le_iInf_iff]
  intro hH
  change IsCoatom H at hH
  letI : H.Normal := isCoatom_normal hpG hH
  letI : IsSimpleGroup (G ⧸ H) := isSimpleGroup_quotient_of_isCoatom hH
  have hpQ : IsPGroup p (G ⧸ H) := hpG.to_quotient H
  letI : Group.IsNilpotent (G ⧸ H) := hpQ.isNilpotent
  letI : IsCyclic (G ⧸ H) := inferInstance
  exact Subgroup.Normal.quotient_commutative_iff_commutator_le.mp
    IsCyclic.isMulCommutative

/-- A finite abelian group of prime exponent has trivial Frattini subgroup. -/
theorem frattini_eq_bot_of_isMulCommutative_of_pow_prime
    [IsMulCommutative G] (hpow : ∀ x : G, x ^ p = 1) :
    frattini G = ⊥ := by
  letI : Module (ZMod p) (Additive G) :=
    AddCommGroup.zmodModule fun x ↦ by
      change x.toMul ^ p = 1
      exact hpow x.toMul
  exact frattini_eq_bot_of_elementaryAbelianModule G p

end IsPGroup

end Submission.OddOrder.MathlibSupport
