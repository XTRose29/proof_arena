import Submission.Helpers

namespace Submission.Layers

open scoped InnerProductSpace ComplexOrder

open Module

noncomputable def prefixProjection {K E : Type*} [RCLike K]
    [NormedAddCommGroup E] [InnerProductSpace K E] {N : ℕ}
    (b : OrthonormalBasis (Fin N) K E) (k : Fin N) : E →ₗ[K] E :=
  (∑ j ∈ Finset.Iic k, InnerProductSpace.rankOne K (b j) (b j)).toLinearMap

noncomputable def suffixProjection {K E : Type*} [RCLike K]
    [NormedAddCommGroup E] [InnerProductSpace K E] {N : ℕ}
    (b : OrthonormalBasis (Fin N) K E) (k : Fin N) : E →ₗ[K] E :=
  (∑ j ∈ Finset.Ioi k, InnerProductSpace.rankOne K (b j) (b j)).toLinearMap

lemma prefixProjection_apply_basis {K E : Type*} [RCLike K]
    [NormedAddCommGroup E] [InnerProductSpace K E] {N : ℕ}
    (b : OrthonormalBasis (Fin N) K E) (k i : Fin N) :
    prefixProjection b k (b i) = if i ≤ k then b i else 0 := by
  simp [prefixProjection, InnerProductSpace.rankOne_apply, b.inner_eq_ite]

lemma prefixProjection_isPositive {K E : Type*} [RCLike K]
    [NormedAddCommGroup E] [InnerProductSpace K E] {N : ℕ}
    (b : OrthonormalBasis (Fin N) K E) (k : Fin N) :
    (prefixProjection b k).IsPositive := by
  rw [prefixProjection, ContinuousLinearMap.isPositive_toLinearMap_iff]
  exact ContinuousLinearMap.isPositive_sum _ fun j _ ↦
    InnerProductSpace.isPositive_rankOne_self (b j)

lemma suffixProjection_isPositive {K E : Type*} [RCLike K]
    [NormedAddCommGroup E] [InnerProductSpace K E] {N : ℕ}
    (b : OrthonormalBasis (Fin N) K E) (k : Fin N) :
    (suffixProjection b k).IsPositive := by
  rw [suffixProjection, ContinuousLinearMap.isPositive_toLinearMap_iff]
  exact ContinuousLinearMap.isPositive_sum _ fun j _ ↦
    InnerProductSpace.isPositive_rankOne_self (b j)

private lemma sum_rankOne_eq_id {K E : Type*} [RCLike K]
    [NormedAddCommGroup E] [InnerProductSpace K E] {N : ℕ}
    (b : OrthonormalBasis (Fin N) K E) :
    (∑ j, InnerProductSpace.rankOne K (b j) (b j)).toLinearMap = LinearMap.id := by
  exact congrArg ContinuousLinearMap.toLinearMap
    (OrthonormalBasis.sum_rankOne_eq_id b)

lemma prefix_add_suffix {K E : Type*} [RCLike K]
    [NormedAddCommGroup E] [InnerProductSpace K E] {N : ℕ}
    (b : OrthonormalBasis (Fin N) K E) (k : Fin N) :
    prefixProjection b k + suffixProjection b k = LinearMap.id := by
  have hd : Disjoint (Finset.Iic k) (Finset.Ioi k) := by
    simp [Finset.disjoint_left]
  have hu : Finset.Iic k ∪ Finset.Ioi k = Finset.univ := by
    ext i
    simp only [Finset.mem_union, Finset.mem_Iic, Finset.mem_Ioi, Finset.mem_univ, iff_true]
    exact le_or_gt i k
  rw [prefixProjection, suffixProjection, ← ContinuousLinearMap.toLinearMap_add,
    ← Finset.sum_union hd, hu]
  exact sum_rankOne_eq_id b

lemma trace_prefixProjection {K E : Type*} [RCLike K]
    [NormedAddCommGroup E] [InnerProductSpace K E] [FiniteDimensional K E]
    {N : ℕ} (b : OrthonormalBasis (Fin N) K E) (k : Fin N) :
    (prefixProjection b k).trace K E = (k.val + 1 : K) := by
  rw [prefixProjection, ContinuousLinearMap.toLinearMap_sum, map_sum]
  simp [InnerProductSpace.trace_rankOne, inner_self_eq_norm_sq_to_K,
    b.orthonormal.norm_eq_one]

lemma prefix_update_shift_nonneg {K E : Type*} [RCLike K]
    [NormedAddCommGroup E] [InnerProductSpace K E] [FiniteDimensional K E]
    {N : ℕ} {S : E →ₗ[K] E} (hS : S.IsSymmetric) (hn : finrank K E = N)
    (b : OrthonormalBasis (Fin N) K E) (k : Fin N) {t : ℝ} (ht : 0 ≤ t)
    (hU : (S + (t : K) • prefixProjection b k).IsSymmetric) (i : Fin N) :
    0 ≤ hU.eigenvalues hn i - hS.eigenvalues hn i := by
  have htK : (0 : K) ≤ (t : K) := RCLike.ofReal_nonneg.mpr ht
  have hpos := (prefixProjection_isPositive b k).smul_of_nonneg htK
  have hmono := Helpers.eigenvalues_mono_of_re_inner_le hS hU hn (fun x ↦ by
    have hx := hpos.re_inner_nonneg_right x
    simpa only [LinearMap.add_apply, inner_add_right, map_add] using
      le_add_of_nonneg_right hx)
  exact sub_nonneg.mpr (hmono i)

lemma prefix_update_shift_le {K E : Type*} [RCLike K]
    [NormedAddCommGroup E] [InnerProductSpace K E] [FiniteDimensional K E]
    {N : ℕ} {S : E →ₗ[K] E} (hS : S.IsSymmetric) (hn : finrank K E = N)
    (b : OrthonormalBasis (Fin N) K E) (k : Fin N) {t : ℝ} (ht : 0 ≤ t)
    (hU : (S + (t : K) • prefixProjection b k).IsSymmetric) (i : Fin N) :
    hU.eigenvalues hn i - hS.eigenvalues hn i ≤ t := by
  have htK : (0 : K) ≤ (t : K) := RCLike.ofReal_nonneg.mpr ht
  have hqpos := (suffixProjection_isPositive b k).smul_of_nonneg htK
  have hidpos : ((t : K) • (LinearMap.id : E →ₗ[K] E)).IsPositive :=
    LinearMap.isPositive_id.smul_of_nonneg htK
  have hshift : (S + (t : K) • LinearMap.id).IsSymmetric :=
    hS.add hidpos.isSymmetric
  have heq : S + (t : K) • LinearMap.id =
      (S + (t : K) • prefixProjection b k) + (t : K) • suffixProjection b k := by
    rw [← prefix_add_suffix b k, smul_add, add_assoc]
  have hmono := Helpers.eigenvalues_mono_of_re_inner_le hU hshift hn (fun x ↦ by
    rw [heq]
    have hx := hqpos.re_inner_nonneg_right x
    simpa only [LinearMap.add_apply, inner_add_right, map_add] using
      le_add_of_nonneg_right hx)
  have heig := Helpers.eigenvalues_add_real_smul_id hS hn t hshift
  rw [heig] at hmono
  linarith [hmono i]

lemma sum_prefix_update_shift {K E : Type*} [RCLike K]
    [NormedAddCommGroup E] [InnerProductSpace K E] [FiniteDimensional K E]
    {N : ℕ} {S : E →ₗ[K] E} (hS : S.IsSymmetric) (hn : finrank K E = N)
    (b : OrthonormalBasis (Fin N) K E) (k : Fin N) (t : ℝ)
    (hU : (S + (t : K) • prefixProjection b k).IsSymmetric) :
    ∑ i, (hU.eigenvalues hn i - hS.eigenvalues hn i) = (k.val + 1) * t := by
  rw [Finset.sum_sub_distrib, ← hU.re_trace_eq_sum_eigenvalues hn,
    ← hS.re_trace_eq_sum_eigenvalues hn]
  simp [map_add, map_smul, trace_prefixProjection, mul_comm]

end Submission.Layers
