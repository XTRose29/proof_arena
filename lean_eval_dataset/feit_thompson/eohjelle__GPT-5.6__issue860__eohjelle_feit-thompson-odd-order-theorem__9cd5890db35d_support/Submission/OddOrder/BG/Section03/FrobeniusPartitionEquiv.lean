import Submission.OddOrder.BG.Section03.FrobeniusPartitionUnique

/-!
An explicit equivalence underlying the finite Frobenius partition.
-/

namespace Submission.OddOrder.BG.Section03

universe u

variable {G : Type u} [Group G] [Finite G]
variable {K R : Subgroup G}

/-- Nonidentity elements of a subgroup. -/
abbrev Nonidentity (H : Subgroup G) := {h : H // h ≠ 1}

/-- Elements outside a subgroup. -/
abbrev Outside (H : Subgroup G) := {g : G // g ∉ H}

namespace IsFrobeniusDecomposition

/-- Conjugating a nonidentity complement element by a kernel element produces
an element outside the kernel. -/
def conjugateOutside
    (h : IsFrobeniusDecomposition K R) :
    K × Nonidentity R → Outside K := fun xr ↦
  ⟨(xr.1 : G) * (xr.2.1 : G) * (xr.1 : G)⁻¹, by
    intro hmem
    have hrK : (xr.2.1 : G) ∈ K := by
      have : (xr.1 : G)⁻¹ *
          ((xr.1 : G) * (xr.2.1 : G) * (xr.1 : G)⁻¹) *
            (xr.1 : G) ∈ K :=
        K.mul_mem (K.mul_mem (K.inv_mem xr.1.property) hmem) xr.1.property
      convert this using 1; group
    have hrOne : (xr.2.1 : G) = 1 := by
      apply Subgroup.mem_bot.mp
      rw [← disjoint_iff.mp h.disjoint]
      exact ⟨hrK, xr.2.1.property⟩
    exact xr.2.2 (Subtype.ext hrOne)⟩

/-- Injectivity is the uniqueness half of the Frobenius partition. -/
theorem conjugateOutside_injective
    (h : IsFrobeniusDecomposition K R) :
    Function.Injective h.conjugateOutside := by
  rintro ⟨x, r⟩ ⟨y, s⟩ hrs
  have hrsG := congrArg Subtype.val hrs
  let g : G := (x : G) * (r.1 : G) * (x : G)⁻¹
  have hg : g ∉ K := (h.conjugateOutside (x, r)).property
  rcases h.existsUnique_kernel_conjugate_complement_of_not_mem hg with
    ⟨z, hz, huniq⟩
  have hxmem : g ∈ R.map (MulAut.conj (x : G)).toMonoidHom :=
    ⟨(r.1 : G), r.1.property, rfl⟩
  have hymem : g ∈ R.map (MulAut.conj (y : G)).toMonoidHom := by
    refine ⟨(s.1 : G), s.1.property, ?_⟩
    exact hrsG.symm
  have hxy : x = y := (huniq x hxmem).trans (huniq y hymem).symm
  subst y
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    apply Subtype.ext
    apply (MulAut.conj (x : G)).injective
    exact hrsG

/-- Surjectivity is the covering half of the Frobenius partition. -/
theorem conjugateOutside_surjective
    (h : IsFrobeniusDecomposition K R) :
    Function.Surjective h.conjugateOutside := by
  intro g
  obtain ⟨x, hx⟩ :=
    h.exists_kernel_conjugate_complement_of_not_mem g.property
  rcases hx with ⟨r, hr, hrEq⟩
  have hrNe : (⟨r, hr⟩ : R) ≠ 1 := by
    intro hrOne
    apply g.property
    have hrOneG : r = 1 := congrArg Subtype.val hrOne
    have hgOne : (g : G) = 1 := by
      rw [← hrEq, hrOneG]
      simp
    rw [hgOne]
    exact K.one_mem
  refine ⟨⟨x, ⟨⟨r, hr⟩, hrNe⟩⟩, ?_⟩
  apply Subtype.ext
  exact hrEq

/-- The Frobenius partition as an equivalence: elements outside the kernel
are uniquely a kernel conjugate of a nonidentity complement element. -/
noncomputable def outsideEquivKernelProdNonidentity
    (h : IsFrobeniusDecomposition K R) :
    Outside K ≃ K × Nonidentity R :=
  (Equiv.ofBijective h.conjugateOutside
    ⟨h.conjugateOutside_injective, h.conjugateOutside_surjective⟩).symm

end IsFrobeniusDecomposition

end Submission.OddOrder.BG.Section03
