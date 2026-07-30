import Submission.OddOrder.BG.Section03.FrobeniusPartitionEquiv

/-!
Finite-sum form of the Frobenius partition.
-/

namespace Submission.OddOrder.BG.Section03

universe u v

variable {G : Type u} [Group G] [Fintype G]
variable {K R : Subgroup G}
variable {A : Type v} [AddCommMonoid A]

noncomputable section

local instance : DecidableEq G := Classical.decEq G
local instance : DecidablePred (fun g : G ↦ g ∈ K) := Classical.decPred _
local instance : DecidablePred (fun g : G ↦ g ∈ R) := Classical.decPred _

namespace IsFrobeniusDecomposition

/-- Split a sum over the ambient group into the kernel and its complement. -/
theorem sum_eq_sum_kernel_add_sum_outside
    (f : G → A) :
    (∑ g : G, f g) = (∑ k : K, f k) + (∑ g : Outside K, f g) := by
  classical
  simpa using
    (Fintype.sum_subtype_add_sum_subtype (fun g : G ↦ g ∈ K) f).symm

/-- Reindex the sum outside the kernel by kernel conjugators and nonidentity
complement elements. -/
theorem sum_outside_eq_sum_conjugates_nonidentity
    (h : IsFrobeniusDecomposition K R) (f : G → A) :
    (∑ g : Outside K, f g) =
      ∑ x : K, ∑ r : Nonidentity R,
        f ((x : G) * (r.1 : G) * (x : G)⁻¹) := by
  classical
  have hreindex :
      (∑ xr : K × Nonidentity R, f (h.conjugateOutside xr)) =
        ∑ g : Outside K, f g := by
    have hbij : Function.Bijective h.conjugateOutside :=
      ⟨h.conjugateOutside_injective, h.conjugateOutside_surjective⟩
    exact hbij.sum_comp (fun g : Outside K ↦ f g)
  rw [← hreindex, Fintype.sum_prod_type]
  rfl

/-- Separate the identity term from a complement sum. -/
theorem sum_complement_eq_one_add_sum_nonidentity
    (x : K) (f : G → A) :
    (∑ r : R, f ((x : G) * (r : G) * (x : G)⁻¹)) =
      f 1 + ∑ r : Nonidentity R,
        f ((x : G) * (r.1 : G) * (x : G)⁻¹) := by
  classical
  let e : Nonidentity R ≃ (Finset.univ.erase (1 : R) : Finset R) :=
    { toFun := fun r ↦
        ⟨r.1, Finset.mem_erase.mpr ⟨r.2, Finset.mem_univ r.1⟩⟩
      invFun := fun r ↦ ⟨r.1, (Finset.mem_erase.mp r.2).1⟩
      left_inv := fun r ↦ by rfl
      right_inv := fun r ↦ by rfl }
  have hnonidentity :
      (∑ r : Nonidentity R,
        f ((x : G) * (r.1 : G) * (x : G)⁻¹)) =
      ∑ r ∈ Finset.univ.erase (1 : R),
        f ((x : G) * (r : G) * (x : G)⁻¹) := by
    calc
      _ = ∑ r : (Finset.univ.erase (1 : R) : Finset R),
          f ((x : G) * (r : R) * (x : G)⁻¹) := by
        apply Fintype.sum_equiv e
        intro r
        rfl
      _ = _ := by
        simpa using
          (Finset.sum_coe_sort (Finset.univ.erase (1 : R))
            (fun r : R ↦ f ((x : G) * (r : G) * (x : G)⁻¹)))
  rw [hnonidentity]
  simpa using
    (Finset.add_sum_erase Finset.univ
      (fun r : R ↦ f ((x : G) * (r : G) * (x : G)⁻¹))
      (Finset.mem_univ (1 : R))).symm

/-- The additive identity attached to the Frobenius partition. The identity
element occurs once in the kernel sum and once in every conjugate-complement
sum, accounting for the extra `|K|` copies on the left. -/
theorem sum_add_card_nsmul_one_eq_kernel_add_conjugates
    (h : IsFrobeniusDecomposition K R) (f : G → A) :
    (∑ g : G, f g) + Fintype.card K • f 1 =
      (∑ k : K, f k) +
        ∑ x : K, ∑ r : R,
          f ((x : G) * (r : G) * (x : G)⁻¹) := by
  classical
  rw [sum_eq_sum_kernel_add_sum_outside f,
    h.sum_outside_eq_sum_conjugates_nonidentity f]
  simp_rw [sum_complement_eq_one_add_sum_nonidentity]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ]
  ac_rfl

end IsFrobeniusDecomposition

end

end Submission.OddOrder.BG.Section03
