import Submission.OddOrder.MathlibSupport.ElementaryAbelian
import Submission.OddOrder.MathlibSupport.SubgroupCardinality
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Tactic.Group

/-!
Elementary-abelian direct products inside an ambient finite group.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped IsMulCommutative Pointwise

universe u

variable {G : Type u} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]

omit [Finite G] in
/-- A subgroup of prime cardinality is elementary abelian of rank one. -/
theorem isElementaryAbelianOfRank_one_of_card_eq_prime
    {S : Subgroup G} (hS : Nat.card S = p) :
    IsElementaryAbelianOfRank p 1 S := by
  letI : IsCyclic S := isCyclic_of_prime_card hS
  have hcomm : IsMulCommutative S := inferInstance
  have hpow : ∀ s : S, s ^ p = 1 := by
    intro s
    simpa [hS] using (pow_card_eq_one' (x := s))
  exact
    { isPGroup := IsPGroup.of_card (n := 1) (by simpa using hS)
      commutative := hcomm
      pow_eq_one := hpow
      card_eq := by simpa using hS }

omit [Finite G] in
/-- Cardinality of a disjoint subgroup product when the left subgroup
normalizes the right subgroup. -/
theorem natCard_sup_eq_mul_of_disjoint_of_le_normalizer
    {H K : Subgroup G} (hdis : Disjoint H K)
    (hnorm : H ≤ Subgroup.normalizer (K : Set G)) :
    Nat.card (H ⊔ K : Subgroup G) = Nat.card H * Nat.card K := by
  let L : Subgroup G := H ⊔ K
  let f : H × K → L := fun x ↦
    ⟨(x.1 : G) * x.2,
      L.mul_mem
        ((show H ≤ L by dsimp [L]; exact le_sup_left) x.1.2)
        ((show K ≤ L by dsimp [L]; exact le_sup_right) x.2.2)⟩
  have hfinj : Function.Injective f := by
    rintro ⟨h₁, k₁⟩ ⟨h₂, k₂⟩ heq
    have heqG : (h₁ : G) * k₁ = (h₂ : G) * k₂ :=
      congrArg Subtype.val heq
    have hcross : (h₂ : G)⁻¹ * h₁ = (k₂ : G) * (k₁ : G)⁻¹ := by
      calc
        (h₂ : G)⁻¹ * h₁ =
            (h₂ : G)⁻¹ * ((h₁ : G) * k₁) * (k₁ : G)⁻¹ := by group
        _ = (h₂ : G)⁻¹ * ((h₂ : G) * k₂) * (k₁ : G)⁻¹ := by rw [heqG]
        _ = (k₂ : G) * (k₁ : G)⁻¹ := by group
    have hcrossH : (h₂ : G)⁻¹ * h₁ ∈ H :=
      H.mul_mem (H.inv_mem h₂.2) h₁.2
    have hcrossK : (h₂ : G)⁻¹ * h₁ ∈ K := by
      rw [hcross]
      exact K.mul_mem k₂.2 (K.inv_mem k₁.2)
    have hcrossBot : (h₂ : G)⁻¹ * h₁ ∈ (⊥ : Subgroup G) := by
      rw [← disjoint_iff.mp hdis]
      exact ⟨hcrossH, hcrossK⟩
    have hcrossOne : (h₂ : G)⁻¹ * h₁ = 1 :=
      Subgroup.mem_bot.mp hcrossBot
    have hh : (h₁ : G) = h₂ := by
      calc
        (h₁ : G) = h₂ * ((h₂ : G)⁻¹ * h₁) := by group
        _ = h₂ := by rw [hcrossOne, mul_one]
    have hk : (k₁ : G) = k₂ := by
      rw [hh] at heqG
      exact mul_left_cancel heqG
    exact Prod.ext (Subtype.ext hh) (Subtype.ext hk)
  have hfsurj : Function.Surjective f := by
    intro x
    have hxprod : (x : G) ∈ (H : Set G) * (K : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right H K hnorm]
      exact x.2
    rcases hxprod with ⟨h, hh, k, hk, hx⟩
    refine ⟨(⟨h, hh⟩, ⟨k, hk⟩), ?_⟩
    exact Subtype.ext hx
  let e : H × K ≃ L := Equiv.ofBijective f ⟨hfinj, hfsurj⟩
  calc
    Nat.card (H ⊔ K : Subgroup G) = Nat.card L := by rfl
    _ = Nat.card (H × K) :=
      (Nat.card_congr e).symm
    _ = Nat.card H * Nat.card K := Nat.card_prod H K

omit [Finite G] in
/-- Cardinality of an internal direct product, stated using elementwise
commutation and lattice disjointness. -/
theorem natCard_sup_eq_mul_of_disjoint_of_commute
    {H K : Subgroup G} (hdis : Disjoint H K)
    (hcomm : ∀ h ∈ H, ∀ k ∈ K, Commute h k) :
    Nat.card (H ⊔ K : Subgroup G) = Nat.card H * Nat.card K := by
  apply natCard_sup_eq_mul_of_disjoint_of_le_normalizer hdis
  intro h hh
  apply Subgroup.centralizer_le_normalizer (K : Set G)
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  exact (hcomm h hh k hk).eq.symm

omit [Finite G] [Fact p.Prime] in
/-- The supremum of commuting, disjoint elementary-abelian subgroups has
the sum of their ranks. -/
theorem isElementaryAbelianOfRank_sup_of_disjoint_of_commute
    {m n : ℕ} {H K : Subgroup G}
    (hG : IsPGroup p G)
    (hH : IsElementaryAbelianOfRank p m H)
    (hK : IsElementaryAbelianOfRank p n K)
    (hdis : Disjoint H K)
    (hcomm : ∀ h ∈ H, ∀ k ∈ K, Commute h k) :
    IsElementaryAbelianOfRank p (m + n) (H ⊔ K : Subgroup G) := by
  have hnorm : H ≤ Subgroup.normalizer (K : Set G) := by
    intro h hh
    apply Subgroup.centralizer_le_normalizer (K : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact (hcomm h hh k hk).eq.symm
  let L : Subgroup G := H ⊔ K
  have hdecomp : ∀ x : L,
      ∃ h : H, ∃ k : K, (x : G) = (h : G) * k := by
    intro x
    have hxprod : (x : G) ∈ (H : Set G) * (K : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right H K hnorm]
      exact x.2
    rcases hxprod with ⟨h, hh, k, hk, hx⟩
    exact ⟨⟨h, hh⟩, ⟨k, hk⟩, hx.symm⟩
  have hsupComm : IsMulCommutative L := by
    apply isMulCommutative_iff.mpr
    intro x y
    obtain ⟨h₁, k₁, hx⟩ := hdecomp x
    obtain ⟨h₂, k₂, hy⟩ := hdecomp y
    have hh : Commute (h₁ : G) h₂ := by
      letI : IsMulCommutative H := hH.commutative
      exact congrArg Subtype.val (mul_comm h₁ h₂)
    have hkk : Commute (k₁ : G) k₂ := by
      letI : IsMulCommutative K := hK.commutative
      exact congrArg Subtype.val (mul_comm k₁ k₂)
    have hh₁k₂ : Commute (h₁ : G) k₂ :=
      hcomm h₁ h₁.2 k₂ k₂.2
    have hh₂k₁ : Commute (h₂ : G) k₁ :=
      hcomm h₂ h₂.2 k₁ k₁.2
    apply Subtype.ext
    change (x : G) * y = (y : G) * x
    rw [hx, hy]
    exact (hh.mul_right hh₁k₂).mul_left
      (hh₂k₁.symm.mul_right hkk)
  have hsupPow : ∀ x : L, x ^ p = 1 := by
    intro x
    obtain ⟨h, k, hx⟩ := hdecomp x
    apply Subtype.ext
    change (x : G) ^ p = 1
    rw [hx, (hcomm h h.2 k k.2).mul_pow]
    have hhp : (h : G) ^ p = 1 :=
      congrArg Subtype.val (hH.pow_eq_one h)
    have hkp : (k : G) ^ p = 1 :=
      congrArg Subtype.val (hK.pow_eq_one k)
    rw [hhp, hkp, one_mul]
  exact
    { isPGroup := hG.to_subgroup L
      commutative := hsupComm
      pow_eq_one := hsupPow
      card_eq := by
        rw [natCard_sup_eq_mul_of_disjoint_of_commute hdis hcomm,
          hH.card_eq, hK.card_eq, ← pow_add] }

end Submission.OddOrder.MathlibSupport
