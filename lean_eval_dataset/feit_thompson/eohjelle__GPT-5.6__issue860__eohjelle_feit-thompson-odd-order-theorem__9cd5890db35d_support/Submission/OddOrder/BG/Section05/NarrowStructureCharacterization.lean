import Submission.OddOrder.BG.Section04.MetacyclicOmegaOne
import Submission.OddOrder.BG.Section05.NarrowCentralizerCharacterization
import Submission.OddOrder.MathlibSupport.Metacyclic
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Tactic.Group

/-!
The structural characterization of narrow odd `p`-groups.
-/

namespace Submission.OddOrder.BG.Section05

open Submission.OddOrder.MathlibSupport
open scoped IsMulCommutative Pointwise

noncomputable section

universe u

variable {G : Type u} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]

private def mulEquivSupOfDisjointOfCommute
    {H K : Subgroup G} (hdis : Disjoint H K)
    (hcomm : ∀ h ∈ H, ∀ k ∈ K, Commute h k) :
    H × K ≃* (H ⊔ K : Subgroup G) := by
  have hnorm : H ≤ Subgroup.normalizer (K : Set G) := by
    intro h hh
    apply Subgroup.centralizer_le_normalizer (K : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact (hcomm h hh k hk).eq.symm
  let L : Subgroup G := H ⊔ K
  let f : H × K →* L :=
    { toFun := fun x ↦
        ⟨(x.1 : G) * x.2,
          L.mul_mem
            ((show H ≤ L by dsimp [L]; exact le_sup_left) x.1.2)
            ((show K ≤ L by dsimp [L]; exact le_sup_right) x.2.2)⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro x y
        apply Subtype.ext
        symm
        change ((x.1 : G) * x.2) * ((y.1 : G) * y.2) =
          ((x.1 : G) * y.1) * ((x.2 : G) * y.2)
        have hcross : Commute (x.2 : G) y.1 :=
          (hcomm y.1 y.1.2 x.2 x.2.2).symm
        calc
          ((x.1 : G) * x.2) * ((y.1 : G) * y.2) =
              (x.1 : G) * ((x.2 : G) * y.1) * y.2 := by group
          _ = (x.1 : G) * ((y.1 : G) * x.2) * y.2 := by
            rw [hcross.eq]
          _ = ((x.1 : G) * y.1) * ((x.2 : G) * y.2) := by group }
  apply MulEquiv.ofBijective f
  constructor
  · rintro ⟨h₁, k₁⟩ ⟨h₂, k₂⟩ heq
    have heqG : (h₁ : G) * k₁ = (h₂ : G) * k₂ :=
      congrArg (fun z : L ↦ (z : G)) heq
    have hcross : (h₂ : G)⁻¹ * h₁ = (k₂ : G) * (k₁ : G)⁻¹ := by
      calc
        (h₂ : G)⁻¹ * h₁ =
            (h₂ : G)⁻¹ * ((h₁ : G) * k₁) * (k₁ : G)⁻¹ := by group
        _ = (h₂ : G)⁻¹ * ((h₂ : G) * k₂) * (k₁ : G)⁻¹ := by
          rw [heqG]
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
  · intro x
    have hxprod : (x : G) ∈ (H : Set G) * (K : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right H K hnorm]
      exact x.2
    rcases hxprod with ⟨h, hh, k, hk, hx⟩
    refine ⟨(⟨h, hh⟩, ⟨k, hk⟩), ?_⟩
    exact Subtype.ext hx

omit [Finite G] in
private theorem isMetacyclic_sup_of_disjoint_of_commute
    {H K : Subgroup G} (hH : IsCyclic H) (hK : IsCyclic K)
    (hdis : Disjoint H K)
    (hcomm : ∀ h ∈ H, ∀ k ∈ K, Commute h k) :
    IsMetacyclic (H ⊔ K : Subgroup G) := by
  let e : (H ⊔ K : Subgroup G) ≃* H × K :=
    (mulEquivSupOfDisjointOfCommute hdis hcomm).symm
  exact isMetacyclic_of_mulEquiv (H ⊔ K : Subgroup G) e
    (isMetacyclic_prod_of_isCyclic hH hK)

/-- `BGsection5.v:narrow_structureP` (Bender--Glauberman Theorem 5.3).

MathComp states this as a reflection lemma.  Here both sides are
propositions, so the source equivalence is expressed directly as an `iff`,
with the source proposition `narrow_structure` on the left. -/
theorem narrow_structureP
    (hG : IsPGroup p G) (hodd : Odd (Nat.card G))
    (hRank3 : ∃ A : Subgroup G, IsElementaryAbelianOfRank p 3 A) :
    NarrowStructure p (⊤ : Subgroup G) ↔
      IsNarrow p (⊤ : Subgroup G) := by
  constructor
  · rintro ⟨S, C, _hSTop, _hCTop, hScard, hCcyclic,
      hSCdis, hSCcomm, hSupCent⟩
    apply (narrow_centP hG hodd hRank3).mpr
    refine ⟨S, hScard, ?_⟩
    rintro ⟨F, hFCent, hF⟩
    let H : Subgroup G := S ⊔ C
    have hFH : F ≤ H := by
      dsimp [H]
      rw [hSupCent]
      exact hFCent
    let F' : Subgroup H := F.subgroupOf H
    have hF' : IsElementaryAbelianOfRank p 3 F' := by
      refine
        { isPGroup := (hG.to_subgroup H).to_subgroup F'
          commutative := ?_
          pow_eq_one := ?_
          card_eq := ?_ }
      · apply isMulCommutative_iff.mpr
        intro x y
        letI : IsMulCommutative F := hF.commutative
        apply Subtype.ext
        exact Subtype.ext (congrArg (fun z : F ↦ (z : G))
          (mul_comm (⟨(x : G), x.2⟩ : F) ⟨(y : G), y.2⟩))
      · intro x
        apply Subtype.ext
        exact Subtype.ext (congrArg (fun z : F ↦ (z : G))
          (hF.pow_eq_one ⟨(x : G), x.2⟩))
      · exact (natCard_subgroupOf_eq hFH).trans hF.card_eq
    have hHmeta : IsMetacyclic H := by
      dsimp [H]
      exact isMetacyclic_sup_of_disjoint_of_commute
        (isCyclic_of_prime_card hScard) hCcyclic hSCdis hSCcomm
    have hHp : IsPGroup p H := hG.to_subgroup H
    have hHodd : Odd (Nat.card H) := odd_natCard_subgroup H hodd
    by_cases hHcyclic : IsCyclic H
    · letI : IsCyclic H := hHcyclic
      letI : IsCyclic F' := inferInstance
      letI := Fintype.ofFinite F'
      classical
      have hFcardLe : Nat.card F' ≤ p := by
        rw [Nat.card_eq_fintype_card]
        simpa only [hF'.pow_eq_one, Finset.filter_true,
          Finset.card_univ] using
          (IsCyclic.card_pow_eq_one_le
            (α := F') (Fact.out : p.Prime).pos)
      rw [hF'.card_eq] at hFcardLe
      have hpLt : p < p ^ 3 := by
        simpa only [pow_one] using
          (Nat.pow_lt_pow_right (Fact.out : p.Prime).one_lt
            (by omega : (1 : ℕ) < 3))
      omega
    · have hOmega : IsElementaryAbelianOfRank p 2 (omegaOne p H) :=
        Submission.OddOrder.BG.Section04.omegaOne_isElementaryAbelian_rank_two_of_isMetacyclic
          hHmeta hHp hHodd hHcyclic
      have hFOmega : F' ≤ omegaOne p H := by
        intro x hx
        apply mem_omegaOne_of_pow_eq_one
        exact congrArg Subtype.val (hF'.pow_eq_one ⟨x, hx⟩)
      have hpows : p ^ 3 ≤ p ^ 2 := by
        rw [← hF'.card_eq, ← hOmega.card_eq]
        exact Subgroup.card_le_of_le hFOmega
      have : (3 : ℕ) ≤ 2 :=
        (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp hpows
      omega
  · intro hNarrow
    obtain ⟨S, hScard, hCentRank⟩ :=
      (narrow_centP hG hodd hRank3).mp hNarrow
    let T : Subgroup G := omegaUpperCentralTwoCentralizer p G
    let C : Subgroup G := centralizerWithin T S
    have hDprod :=
      narrow_cent_dprod hG hodd hRank3 hNarrow hScard hCentRank
    change IsCyclic C ∧
      Disjoint S (commutator G) ∧
      Disjoint S T ∧
      Disjoint S C ∧
      (∀ s ∈ S, ∀ c ∈ C, Commute s c) ∧
      S ⊔ C = centralizerWithin (⊤ : Subgroup G) S at hDprod
    rcases hDprod with
      ⟨hCcyclic, _hSDer, _hST, hSCdis, hSCcomm, hSupCent⟩
    exact ⟨S, C, le_top, le_top, hScard, hCcyclic,
      hSCdis, hSCcomm, hSupCent⟩

end

end Submission.OddOrder.BG.Section05
