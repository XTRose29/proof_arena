import Mathlib.GroupTheory.Commutator.Basic
import Submission.OddOrder.BG.Section03.FrobeniusBasic

/-!
Normalizer and center consequences of an internal Frobenius decomposition.
-/

namespace Submission.OddOrder.BG.Section03

open scoped commutatorElement

universe u

variable {G : Type u} [Group G]
variable {K R : Subgroup G}

namespace IsFrobeniusDecomposition

/-- Every ambient element has unique kernel/complement coordinates. -/
theorem existsUnique_kernel_mul_complement
    (h : IsFrobeniusDecomposition K R) (g : G) :
    ∃! kr : K × R, (kr.1 : G) * (kr.2 : G) = g :=
  h.isComplement.existsUnique g

/-- The Frobenius complement is self-normalizing. -/
theorem normalizer_complement_le
    (h : IsFrobeniusDecomposition K R) :
    Subgroup.normalizer (R : Set G) ≤ R := by
  intro g hg
  rcases h.existsUnique_kernel_mul_complement g with
    ⟨⟨k, r⟩, hkr, _⟩
  have hkNormalizer : (k : G) ∈ Subgroup.normalizer (R : Set G) := by
    have hrNormalizer : (r : G)⁻¹ ∈ Subgroup.normalizer (R : Set G) :=
      (Subgroup.normalizer (R : Set G)).inv_mem (Subgroup.le_normalizer r.property)
    have hkEq : (k : G) = g * (r : G)⁻¹ := by
      rw [← hkr]
      simp
    rw [hkEq]
    exact (Subgroup.normalizer (R : Set G)).mul_mem hg hrNormalizer
  letI : Nontrivial R := R.bot_or_nontrivial.resolve_left h.complement_ne_bot
  obtain ⟨s, hs⟩ := exists_ne (1 : R)
  have hconjR : (k : G) * (s : G) * (k : G)⁻¹ ∈ R :=
    (hkNormalizer (s : G)).mp s.property
  have hcommR : ⁅(k : G), (s : G)⁆ ∈ R := by
    rw [commutatorElement_def]
    exact R.mul_mem hconjR (R.inv_mem s.property)
  have hcommK : ⁅(k : G), (s : G)⁆ ∈ K := by
    rw [commutatorElement_def]
    rw [mul_assoc (k : G) (s : G) (k : G)⁻¹,
      mul_assoc (k : G) ((s : G) * (k : G)⁻¹) (s : G)⁻¹]
    exact K.mul_mem k.property
      (h.kernel_normal.conj_mem (k : G)⁻¹ (K.inv_mem k.property) (s : G))
  have hcommOne : ⁅(k : G), (s : G)⁆ = 1 := by
    apply Subgroup.mem_bot.mp
    rw [← disjoint_iff.mp h.disjoint]
    exact ⟨hcommK, hcommR⟩
  have hsk : (s : G) * (k : G) * (s : G)⁻¹ = (k : G) := by
    have hks : (k : G) * (s : G) = (s : G) * (k : G) :=
      commutatorElement_eq_one_iff_mul_comm.mp hcommOne
    calc
      (s : G) * (k : G) * (s : G)⁻¹ =
          (k : G) * (s : G) * (s : G)⁻¹ := by rw [hks]
      _ = k := by simp
  have hkOne : k = 1 := h.fixedPointFree s hs k hsk
  rw [← hkr, hkOne]
  simpa only [Prod.fst, Prod.snd, Subgroup.coe_one, one_mul] using r.property

/-- The normalizer of a Frobenius complement is exactly the complement. -/
theorem normalizer_complement_eq
    (h : IsFrobeniusDecomposition K R) :
    Subgroup.normalizer (R : Set G) = R :=
  le_antisymm h.normalizer_complement_le Subgroup.le_normalizer

/-- Every element centralizing the whole complement belongs to it. -/
theorem centralizer_complement_le
    (h : IsFrobeniusDecomposition K R) :
    Subgroup.centralizer (R : Set G) ≤ R :=
  (Subgroup.centralizer_le_normalizer (R : Set G)).trans
    h.normalizer_complement_le

/-- Distinct conjugates of the Frobenius complement intersect trivially. -/
theorem disjoint_complement_conjugate_of_not_mem
    (h : IsFrobeniusDecomposition K R) {g : G} (hg : g ∉ R) :
    Disjoint R (R.map (MulAut.conj g).toMonoidHom) := by
  rw [disjoint_iff_inf_le]
  intro x hx
  rcases hx.2 with ⟨t, ht, htEq⟩
  rcases h.existsUnique_kernel_mul_complement g with
    ⟨⟨k, r⟩, hkr, _⟩
  let tR : R := ⟨(r : G) * t * (r : G)⁻¹,
    R.mul_mem (R.mul_mem r.property ht) (R.inv_mem r.property)⟩
  have hxEq : x = (k : G) * (tR : G) * (k : G)⁻¹ := by
    rw [← htEq]
    change g * t * g⁻¹ = _
    rw [← hkr]
    dsimp [tR]
    group
  apply Subgroup.mem_bot.mpr
  by_contra hxOne
  have htR_ne : tR ≠ 1 := by
    intro htOne
    apply hxOne
    rw [hxEq, htOne]
    simp
  have hcommR : ⁅(k : G), (tR : G)⁆ ∈ R := by
    rw [commutatorElement_def, ← hxEq]
    exact R.mul_mem hx.1 (R.inv_mem tR.property)
  have hcommK : ⁅(k : G), (tR : G)⁆ ∈ K := by
    rw [commutatorElement_def]
    rw [mul_assoc (k : G) (tR : G) (k : G)⁻¹,
      mul_assoc (k : G) ((tR : G) * (k : G)⁻¹) (tR : G)⁻¹]
    exact K.mul_mem k.property
      (h.kernel_normal.conj_mem (k : G)⁻¹ (K.inv_mem k.property) (tR : G))
  have hcommOne : ⁅(k : G), (tR : G)⁆ = 1 := by
    apply Subgroup.mem_bot.mp
    rw [← disjoint_iff.mp h.disjoint]
    exact ⟨hcommK, hcommR⟩
  have htk : (tR : G) * (k : G) * (tR : G)⁻¹ = (k : G) := by
    have hkt : (k : G) * (tR : G) = (tR : G) * (k : G) :=
      commutatorElement_eq_one_iff_mul_comm.mp hcommOne
    calc
      (tR : G) * (k : G) * (tR : G)⁻¹ =
          (k : G) * (tR : G) * (tR : G)⁻¹ := by rw [hkt]
      _ = k := by simp
  have hkOne : k = 1 := h.fixedPointFree tR htR_ne k htk
  apply hg
  have hgEq : g = (r : G) := by
    rw [← hkr, hkOne]
    simp
  rw [hgEq]
  exact r.property

/-- A group admitting a nontrivial Frobenius decomposition has trivial
center. -/
theorem center_eq_bot
    (h : IsFrobeniusDecomposition K R) :
    Subgroup.center G = ⊥ := by
  apply le_bot_iff.mp
  intro z hz
  have hzR : z ∈ R :=
    h.normalizer_complement_le
      (Subgroup.center_le_normalizer (R : Set G) hz)
  let zR : R := ⟨z, hzR⟩
  by_contra hzOne
  have hzR_ne : zR ≠ 1 := by
    intro hzR_one
    apply hzOne
    exact congrArg Subtype.val hzR_one
  apply h.kernel_ne_bot
  apply le_bot_iff.mp
  intro k hk
  let kK : K := ⟨k, hk⟩
  have hcomm : z * k = k * z := ((Subgroup.mem_center_iff.mp hz) k).symm
  have hfix : z * k * z⁻¹ = k := by
    calc
      z * k * z⁻¹ = k * z * z⁻¹ := by rw [hcomm]
      _ = k := by simp
  have hkOne : kK = 1 := h.fixedPointFree zR hzR_ne kK hfix
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val hkOne)

end IsFrobeniusDecomposition

end Submission.OddOrder.BG.Section03
