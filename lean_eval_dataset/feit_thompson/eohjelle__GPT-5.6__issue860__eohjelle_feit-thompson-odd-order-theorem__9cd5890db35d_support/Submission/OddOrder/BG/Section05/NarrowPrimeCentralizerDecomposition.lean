import Submission.OddOrder.BG.Section05.NarrowPrimeSupMaximal
import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
The subgroup decomposition used in Bender--Glauberman Theorem 5.3(d).
-/

namespace Submission.OddOrder.BG.Section05

open Submission.OddOrder.MathlibSupport
open scoped IsMulCommutative Pointwise

universe u

variable {G : Type u} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]

/-- Let `T = C_G(Ω₁(Z₂(G)))` and `C = C_T(S)`. Under the hypotheses
of Theorem 5.3(d), `S` misses both `T` and the derived subgroup, and
`S` and `C` form the internal direct product `C_G(S)`. -/
theorem narrow_prime_centralizer_decomposition
    (hG : IsPGroup p G) (hodd : Odd (Nat.card G))
    (hRank3 : ∃ A : Subgroup G, IsElementaryAbelianOfRank p 3 A)
    (hNarrow : IsNarrow p (⊤ : Subgroup G))
    {S : Subgroup G} (hScard : Nat.card S = p)
    (hCentRank : ¬ ∃ F : Subgroup G,
      F ≤ centralizerWithin (⊤ : Subgroup G) S ∧
        IsElementaryAbelianOfRank p 3 F) :
    let T := omegaUpperCentralTwoCentralizer p G
    let C := centralizerWithin T S
    Disjoint S (commutator G) ∧
      Disjoint S T ∧
      Disjoint S C ∧
      (∀ s ∈ S, ∀ c ∈ C, Commute s c) ∧
      S ⊔ C = centralizerWithin (⊤ : Subgroup G) S := by
  let Z : Subgroup G := omegaOneCenter p G
  let SZ : Subgroup G := S ⊔ Z
  let T : Subgroup G := omegaUpperCentralTwoCentralizer p G
  let C : Subgroup G := centralizerWithin T S
  obtain ⟨hSZdis, hSZelem, hSZmax⟩ :=
    narrow_prime_sup_omegaOneCenter_pmax
      hG hRank3 hNarrow hScard hCentRank
  have hSZnotT : ¬ SZ ≤ T := by
    simpa [SZ, T] using
      (not_le_omegaUpperCentralTwoCentralizer
        hG hodd hRank3 hSZelem hSZmax)
  have hZT : Z ≤ T := by
    intro z hz
    change z ∈ Subgroup.centralizer
      (omegaOneUpperCentralTwo p G : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro w _
    exact Subgroup.mem_center_iff.mp
      (omegaOneCenter_le_center p hz) w
  have hSnotT : ¬ S ≤ T := by
    intro hST
    exact hSZnotT (sup_le hST hZT)
  have hSTdis : Disjoint S T := by
    rw [disjoint_iff]
    by_contra hInfNe
    have hdiv : Nat.card (S ⊓ T : Subgroup G) ∣ p := by
      rw [← hScard]
      exact Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp hdiv with hcardOne | hcardP
    · apply hInfNe
      exact Subgroup.eq_bot_of_card_eq (S ⊓ T : Subgroup G) hcardOne
    · have hInfS : S ⊓ T = S := by
        apply Subgroup.eq_of_le_of_card_ge inf_le_left
        rw [hcardP, hScard]
      apply hSnotT
      intro s hs
      have hsInf : s ∈ S ⊓ T := by rw [hInfS]; exact hs
      exact hsInf.2
  have hTnormal : T.Normal := by
    dsimp [T]
    infer_instance
  letI : T.Normal := hTnormal
  have hTindex : T.index = p := by
    simpa [T] using
      (omegaUpperCentralTwoCentralizer_index_eq_prime
        hG hodd hRank3 hSZelem hSZmax)
  have hSTtop : S ⊔ T = ⊤ := by
    have hSnormT : S ≤ Subgroup.normalizer (T : Set G) := by
      rw [Subgroup.normalizer_eq_top_iff.mpr hTnormal]
      exact le_top
    have hcardST : Nat.card (S ⊔ T : Subgroup G) = Nat.card G := by
      rw [natCard_sup_eq_mul_of_disjoint_of_le_normalizer hSTdis hSnormT,
        hScard, ← hTindex, Nat.mul_comm]
      exact T.card_mul_index
    exact Subgroup.eq_top_of_card_eq _ hcardST
  have hDerT : commutator G ≤ T := by
    have hQcard : Nat.card (G ⧸ T) = p := by
      rw [← T.index_eq_card, hTindex]
    letI : IsCyclic (G ⧸ T) := isCyclic_of_prime_card hQcard
    apply Subgroup.Normal.quotient_commutative_iff_commutator_le.mp
    infer_instance
  have hSDerDis : Disjoint S (commutator G) :=
    hSTdis.mono_right hDerT
  have hSCdis : Disjoint S C :=
    hSTdis.mono_right (centralizerWithin_le_left T S)
  have hSCcomm : ∀ s ∈ S, ∀ c ∈ C, Commute s c := by
    intro s hs c hc
    exact (mem_centralizerWithin.mp hc).2 s hs
  have hS : IsElementaryAbelianOfRank p 1 S :=
    isElementaryAbelianOfRank_one_of_card_eq_prime hScard
  have hSupCent : S ⊔ C = centralizerWithin (⊤ : Subgroup G) S := by
    apply le_antisymm
    · apply sup_le
      · intro s hs
        refine mem_centralizerWithin.mpr ⟨trivial, ?_⟩
        intro x hx
        letI : IsMulCommutative S := hS.commutative
        exact congrArg Subtype.val
          (mul_comm (⟨x, hx⟩ : S) ⟨s, hs⟩)
      · intro c hc
        refine mem_centralizerWithin.mpr ⟨trivial, ?_⟩
        exact (mem_centralizerWithin.mp hc).2
    · intro x hx
      have hxprod : x ∈ (T : Set G) * (S : Set G) := by
        rw [← Subgroup.normal_mul T S, sup_comm, hSTtop]
        trivial
      rcases hxprod with ⟨t, ht, s, hs, hts⟩
      have hsCent : s ∈ centralizerWithin (⊤ : Subgroup G) S := by
        refine mem_centralizerWithin.mpr ⟨trivial, ?_⟩
        intro y hy
        letI : IsMulCommutative S := hS.commutative
        exact congrArg Subtype.val
          (mul_comm (⟨y, hy⟩ : S) ⟨s, hs⟩)
      have hxsCent : x * s⁻¹ ∈ centralizerWithin (⊤ : Subgroup G) S :=
        (centralizerWithin (⊤ : Subgroup G) S).mul_mem hx
          ((centralizerWithin (⊤ : Subgroup G) S).inv_mem hsCent)
      have htEq : t = x * s⁻¹ := by
        rw [← hts]
        group
      have htC : t ∈ C := by
        refine mem_centralizerWithin.mpr ⟨ht, ?_⟩
        rw [htEq]
        exact (mem_centralizerWithin.mp hxsCent).2
      rw [← hts]
      exact (S ⊔ C).mul_mem
        ((show C ≤ S ⊔ C from le_sup_right) htC)
        ((show S ≤ S ⊔ C from le_sup_left) hs)
  exact ⟨hSDerDis, hSTdis, hSCdis, hSCcomm, hSupCent⟩

end Submission.OddOrder.BG.Section05
