import Submission.OddOrder.BG.Section03.FrobeniusBasic

/-!
Kernel/complement algebra in quotients of a Frobenius decomposition.
-/

namespace Submission.OddOrder.BG.Section03

universe u

variable {G : Type u} [Group G]
variable {K R N : Subgroup G}

namespace IsFrobeniusDecomposition

/-- A quotient by a subgroup of the kernel is injective on the Frobenius
complement. -/
theorem quotientMap_injective_on_complement
    (h : IsFrobeniusDecomposition K R) [N.Normal] (hNK : N ≤ K) :
    Function.Injective
      (fun r : R ↦ QuotientGroup.mk' N (r : G)) := by
  intro r s hrs
  have hn : (r : G)⁻¹ * (s : G) ∈ N :=
    QuotientGroup.eq.mp hrs
  have hk : (r : G)⁻¹ * (s : G) ∈ K := hNK hn
  have hr : (r : G)⁻¹ * (s : G) ∈ R :=
    R.mul_mem (R.inv_mem r.property) s.property
  have hKR : K ⊓ R = ⊥ := disjoint_iff.mp h.disjoint
  have hone : (r : G)⁻¹ * (s : G) = 1 := by
    apply Subgroup.mem_bot.mp
    rw [← hKR]
    exact ⟨hk, hr⟩
  apply Subtype.ext
  exact inv_mul_eq_one.mp hone

/-- The complement subgroup map into a kernel quotient is injective. -/
theorem quotientComplement_subgroupMap_injective
    (h : IsFrobeniusDecomposition K R) [N.Normal] (hNK : N ≤ K) :
    Function.Injective
      ((QuotientGroup.mk' N).subgroupMap R) := by
  intro r s hrs
  apply h.quotientMap_injective_on_complement hNK
  exact congrArg Subtype.val hrs

/-- The complement image remains nontrivial in every quotient by a subgroup
of the kernel. -/
theorem quotient_complement_ne_bot
    (h : IsFrobeniusDecomposition K R) [N.Normal] (hNK : N ≤ K) :
    R.map (QuotientGroup.mk' N) ≠ ⊥ := by
  intro hbot
  apply h.complement_ne_bot
  apply le_bot_iff.mp
  intro r hr
  have hqr : QuotientGroup.mk' N r ∈
      R.map (QuotientGroup.mk' N) := ⟨r, hr, rfl⟩
  rw [hbot] at hqr
  have hqOne : QuotientGroup.mk' N r = 1 := Subgroup.mem_bot.mp hqr
  have hrOne : (⟨r, hr⟩ : R) = 1 :=
    h.quotientMap_injective_on_complement hNK (by simpa using hqOne)
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val hrOne)

/-- A proper quotient of the kernel has nontrivial image. -/
theorem quotient_kernel_ne_bot
    [N.Normal] (hNK : N < K) :
    K.map (QuotientGroup.mk' N) ≠ ⊥ := by
  intro hbot
  have hKN : K ≤ (QuotientGroup.mk' N).ker :=
    (Subgroup.map_eq_bot_iff K).mp hbot
  rw [QuotientGroup.ker_mk'] at hKN
  exact hNK.2 hKN

/-- The quotient image of the Frobenius kernel remains normal. -/
theorem quotient_kernel_normal
    (h : IsFrobeniusDecomposition K R) [N.Normal] :
    (K.map (QuotientGroup.mk' N)).Normal :=
  Subgroup.Normal.map h.kernel_normal (QuotientGroup.mk' N)
    (QuotientGroup.mk'_surjective N)

/-- Kernel and complement images remain complementary after quotienting by
an arbitrary subgroup of the kernel. -/
theorem quotient_isComplement
    (h : IsFrobeniusDecomposition K R) [N.Normal] (hNK : N ≤ K) :
    (K.map (QuotientGroup.mk' N)).IsComplement'
      (R.map (QuotientGroup.mk' N)) := by
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  let Kq : Subgroup (G ⧸ N) := K.map q
  let Rq : Subgroup (G ⧸ N) := R.map q
  letI : Kq.Normal := h.quotient_kernel_normal
  have hsup : Kq ⊔ Rq = ⊤ := by
    dsimp [Kq, Rq]
    rw [← Subgroup.map_sup, h.sup_eq_top,
      Subgroup.map_top_of_surjective q (QuotientGroup.mk'_surjective N)]
  have hdis : Disjoint Kq Rq := by
    rw [disjoint_iff_inf_le]
    intro z hz
    rcases hz.1 with ⟨k, hk, hkz⟩
    rcases hz.2 with ⟨r, hr, hrz⟩
    have hkr : q k = q r := hkz.trans hrz.symm
    have hn : k⁻¹ * r ∈ N := QuotientGroup.eq.mp hkr
    have hkinK : k⁻¹ * r ∈ K := hNK hn
    have hrK : r ∈ K := by
      have hrEq : r = k * (k⁻¹ * r) := by group
      rw [hrEq]
      exact K.mul_mem hk hkinK
    have hKR : K ⊓ R = ⊥ := disjoint_iff.mp h.disjoint
    have hrOne : r = 1 := by
      apply Subgroup.mem_bot.mp
      rw [← hKR]
      exact ⟨hrK, hr⟩
    apply Subgroup.mem_bot.mpr
    rw [← hrz, hrOne, map_one]
  apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdis
  rw [← Subgroup.normal_mul Kq Rq, hsup]
  rfl

/-- The quotient kernel/complement data satisfy every Frobenius condition except
the fixed-point condition. This packages the algebraic part of Bender-
Glauberman Lemma 3.2. -/
theorem quotient_decomposition_of_fixedPointFree
    (h : IsFrobeniusDecomposition K R) [N.Normal] (hNK : N < K)
    (hfixed : ∀ r : R.map (QuotientGroup.mk' N), r ≠ 1 →
      ∀ k : K.map (QuotientGroup.mk' N),
        (r : G ⧸ N) * (k : G ⧸ N) * (r : G ⧸ N)⁻¹ = (k : G ⧸ N) →
          k = 1) :
    IsFrobeniusDecomposition
      (K.map (QuotientGroup.mk' N))
      (R.map (QuotientGroup.mk' N)) where
  isComplement := h.quotient_isComplement hNK.1
  kernel_normal := h.quotient_kernel_normal
  kernel_ne_bot := quotient_kernel_ne_bot hNK
  complement_ne_bot := h.quotient_complement_ne_bot hNK.1
  fixedPointFree := hfixed

end IsFrobeniusDecomposition

end Submission.OddOrder.BG.Section03
