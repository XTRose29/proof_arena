import Submission.FilteredPresentation
import Submission.CohomologyComparison

namespace Submission.GolodShafarevich

open LeanEval.GroupTheory
open Submission.GroupAlgebra Submission.Hilbert Submission.GeneratorRank
  Submission.Presentation Submission.RelationCocycle
  Submission.FilteredPresentation

variable (k : Type*) (G : Type) [Field k] [Group G] [Finite G]

noncomputable local instance relationKernelFiniteDimensional {d : ℕ}
    (g : Fin d → G) : FiniteDimensional k (RelationKernel k G g) :=
  FiniteDimensional.of_injective
    ({ toFun := fun x ↦ x.1
       map_add' := fun _ _ ↦ rfl
       map_smul' := fun _ _ ↦ rfl } :
      RelationKernel k G g →ₗ[k] FreeRelations k G d)
    (by
      intro x y hxy
      exact Subtype.ext hxy)

/-- The part of the kernel of the relation map lying in the `n`th free
augmentation power.  Keeping this as a subspace of the fixed ambient free
module makes its monotonicity transparent. -/
noncomputable def relationMapKernelPower {d r : ℕ} (g : Fin d → G)
    (y : Fin r → RelationKernel k G g) (n : ℕ) :
    Submodule k (FreeRelations k G r) :=
  freePower k G r n ⊓ LinearMap.ker (relationMapLinear k G g y)

omit [Finite G] in
theorem relationMapKernelPower_antitone {d r : ℕ} (g : Fin d → G)
    (y : Fin r → RelationKernel k G g) :
    Antitone (relationMapKernelPower k G g y) := by
  intro m n hmn
  exact inf_le_inf ((freePower_antitone k G r) hmn) le_rfl

noncomputable def restrictedRelationKernelEquiv {d r : ℕ} (g : Fin d → G)
    (y : Fin r → RelationKernel k G g) (n : ℕ) :
    LinearMap.ker ((relationMapLinear k G g y).domRestrict (freePower k G r n))
      ≃ₗ[k] relationMapKernelPower k G g y n where
  toFun x := ⟨x.1.1, x.1.2, by
    exact LinearMap.mem_ker.mpr (by
      simpa only [LinearMap.domRestrict_apply] using LinearMap.mem_ker.mp x.2)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun x := ⟨⟨x.1, x.2.1⟩, by
    rw [LinearMap.mem_ker, LinearMap.domRestrict_apply]
    exact x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem finrank_freePower_eq_relationImage_add_kernel {d r : ℕ}
    (g : Fin d → G) (y : Fin r → RelationKernel k G g) (n : ℕ) :
    Module.finrank k (freePower k G r n) =
      Module.finrank k (relationImagePower k G g y n) +
        Module.finrank k (relationMapKernelPower k G g y n) := by
  have h := LinearMap.finrank_range_add_finrank_ker
    ((relationMapLinear k G g y).domRestrict (freePower k G r n))
  rw [LinearMap.range_domRestrict,
    LinearEquiv.finrank_eq (restrictedRelationKernelEquiv k G g y n)] at h
  exact h.symm

theorem filteredWeight_relationImage_le_freePower {d r N : ℕ}
    (g : Fin d → G) (y : Fin r → RelationKernel k G g)
    {t : ℝ} (ht : 0 ≤ t) :
    Helpers.filteredWeight N
        (fun n ↦ Module.finrank k (relationImagePower k G g y n)) t ≤
      Helpers.filteredWeight N
        (fun n ↦ Module.finrank k (freePower k G r n)) t := by
  let u : ℕ → ℕ := fun n ↦
    Module.finrank k (relationImagePower k G g y n)
  let c : ℕ → ℕ := fun n ↦
    Module.finrank k (relationMapKernelPower k G g y n)
  let f : ℕ → ℕ := fun n ↦ Module.finrank k (freePower k G r n)
  have hc : Antitone c := fun _ _ hmn ↦
    Submodule.finrank_mono ((relationMapKernelPower_antitone k G g y) hmn)
  have hnonneg : 0 ≤ Helpers.filteredWeight N c t :=
    Helpers.filteredWeight_nonneg hc ht
  have hfc : f = fun n ↦ u n + c n := by
    funext n
    exact finrank_freePower_eq_relationImage_add_kernel k G g y n
  change Helpers.filteredWeight N u t ≤ Helpers.filteredWeight N f t
  rw [hfc, Helpers.filteredWeight_add]
  exact le_add_of_nonneg_right hnonneg

omit [Finite G] in
theorem kernelPower_one_eq_top {d : ℕ} (g : Fin d → G)
    (hlin : LinearIndependent k (fun i ↦ groupToCotangent k G (g i))) :
    kernelPower k G g 1 = ⊤ := by
  apply top_unique
  intro x _
  exact fun i ↦ by
    simpa only [Submodule.pow_one] using
      relationKernel_coordinate_mem_augmentationIdeal k G g hlin x i

theorem filteredWeight_kernel_le_relationImage {d r N : ℕ}
    (g : Fin d → G)
    (hlin : LinearIndependent k (fun i ↦ groupToCotangent k G (g i)))
    (y : Fin r → RelationKernel k G g)
    (hy : Function.Surjective (relationMap k G g y))
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Helpers.filteredWeight N
        (fun n ↦ Module.finrank k (kernelPower k G g (n + 1))) t ≤
      Helpers.filteredWeight N
        (fun n ↦ Module.finrank k (relationImagePower k G g y n)) t := by
  apply Helpers.filteredWeight_le_of_le
  · intro n
    exact Submodule.finrank_mono
      (relationImagePower_le_kernelPower_succ k G g hlin y n)
  · rw [relationImagePower_zero_eq_top k G g y hy,
      kernelPower_one_eq_top k G g hlin]
  · exact ht0
  · exact ht1

omit [Finite G] in
theorem augmentationPower_eq_bot_of_pow_eq_bot (m n : ℕ)
    (hm : augmentationIdeal k G ^ m = ⊥) (hmn : m ≤ n) :
    augmentationPower k G n = ⊥ := by
  apply le_antisymm
  · exact (Ideal.pow_le_pow_right hmn).trans (le_of_eq hm)
  · exact bot_le

theorem eval_hilbertPolynomial_eq_filteredWeight (m : ℕ)
    (hm : augmentationIdeal k G ^ m = ⊥) (t : ℝ) :
    (hilbertPolynomial k G).eval t =
      Helpers.filteredWeight m
        (fun n ↦ Module.finrank k (augmentationPower k G n)) t := by
  let a : ℕ → ℕ := fun n ↦ Module.finrank k (augmentationPower k G n)
  have ha : Antitone a := fun _ _ hmn ↦
    Submodule.finrank_mono ((augmentationPower_antitone k G) hmn)
  have ham : a m = 0 := by
    dsimp only [a]
    rw [augmentationPower_eq_bot_of_pow_eq_bot k G m m hm le_rfl, finrank_bot]
  have hcoeff (n : ℕ) :
      (hilbertPolynomial k G).coeff n = (a n : ℝ) - a (n + 1) := by
    rw [coeff_hilbertPolynomial, hilbertCoeff]
    change ((a n - a (n + 1) : ℕ) : ℝ) = _
    rw [Nat.cast_sub (ha (Nat.le_succ n))]
  have hsupp : (hilbertPolynomial k G).support ⊆ Finset.range m := by
    intro n hn
    rw [Finset.mem_range]
    by_contra hnot
    have hmn : m ≤ n := Nat.le_of_not_gt hnot
    have han : a n = 0 := by
      dsimp only [a]
      rw [augmentationPower_eq_bot_of_pow_eq_bot k G m n hm hmn, finrank_bot]
    have hans : a (n + 1) = 0 := by
      dsimp only [a]
      rw [augmentationPower_eq_bot_of_pow_eq_bot k G m (n + 1) hm
        (hmn.trans (Nat.le_succ n)), finrank_bot]
    exact (Polynomial.mem_support_iff.mp hn) (by rw [hcoeff, han, hans]; norm_num)
  have heval : (hilbertPolynomial k G).eval t =
      ∑ n ∈ Finset.range m, ((a n : ℝ) - a (n + 1)) * t ^ n := by
    rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
    calc
      ∑ n ∈ (hilbertPolynomial k G).support,
          (hilbertPolynomial k G).coeff n * t ^ n =
          ∑ n ∈ Finset.range m,
            (hilbertPolynomial k G).coeff n * t ^ n := by
        apply Finset.sum_subset hsupp
        intro n _ hn
        simp only [Polynomial.mem_support_iff, not_not] at hn
        simp [hn]
      _ = ∑ n ∈ Finset.range m, ((a n : ℝ) - a (n + 1)) * t ^ n := by
        apply Finset.sum_congr rfl
        intro n _
        rw [hcoeff]
  have ham' : (Module.finrank k (augmentationPower k G m) : ℝ) = 0 := by
    exact_mod_cast ham
  rw [heval, Helpers.filteredWeight_eq_sum_range, ham', zero_mul, add_zero]

omit [Finite G] in
theorem kernelPower_zero_eq_top {d : ℕ} (g : Fin d → G) :
    kernelPower k G g 0 = ⊤ := by
  apply top_unique
  intro x _
  change ∀ i, x.1 i ∈ augmentationIdeal k G ^ 0
  intro i
  rw [Submodule.pow_zero, Ideal.one_eq_top]
  exact Submodule.mem_top

omit [Finite G] in
theorem kernelPower_eq_bot_of_pow_eq_bot {d n : ℕ} (g : Fin d → G)
    (hn : augmentationIdeal k G ^ n = ⊥) :
    kernelPower k G g n = ⊥ := by
  apply le_antisymm
  · intro x hx
    rw [Submodule.mem_bot]
    apply Subtype.ext
    funext i
    have hi := hx i
    rw [hn] at hi
    exact hi
  · exact bot_le

/-- The filtered dimension identities of a minimal presentation imply the
weighted Golod--Shafarevich estimate at every parameter in `[0, 1]`. -/
theorem hilbert_weighted_inequality {d r : ℕ} (g : Fin d → G)
    (hlin : LinearIndependent k (fun i ↦ groupToCotangent k G (g i)))
    (hsurj : Function.Surjective (presentationMap k G g))
    (y : Fin r → RelationKernel k G g)
    (hy : Function.Surjective (relationMap k G g y))
    (hnil : IsNilpotent (augmentationIdeal k G))
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    1 ≤ (1 - (d : ℝ) * t + (r : ℝ) * t ^ 2) *
      (hilbertPolynomial k G).eval t := by
  let A : ℕ → ℕ := fun n ↦ Module.finrank k (augmentationPower k G n)
  let K : ℕ → ℕ := fun n ↦ Module.finrank k (kernelPower k G g n)
  obtain ⟨m, hm⟩ := hnil
  have hdim (n : ℕ) : d * A n = K n + A (n + 1) := by
    calc
      d * A n = Module.finrank k (freePower k G d n) :=
        (finrank_freePower k G d n).symm
      _ = K n + A (n + 1) :=
        finrank_freePower_eq_kernel_add_power k G g hsurj n
  have hdimWeight :
      (d : ℝ) * Helpers.filteredWeight m A t =
        Helpers.filteredWeight m K t +
          Helpers.filteredWeight m (fun n ↦ A (n + 1)) t := by
    calc
      (d : ℝ) * Helpers.filteredWeight m A t =
          Helpers.filteredWeight m (fun n ↦ d * A n) t :=
        (Helpers.filteredWeight_nat_mul m d A t).symm
      _ = Helpers.filteredWeight m (fun n ↦ K n + A (n + 1)) t := by
        congr 1
        funext n
        exact hdim n
      _ = Helpers.filteredWeight m K t +
          Helpers.filteredWeight m (fun n ↦ A (n + 1)) t :=
        Helpers.filteredWeight_add m K (fun n ↦ A (n + 1)) t
  have hAle : A 1 ≤ A 0 := by
    dsimp only [A]
    exact Submodule.finrank_mono
      ((augmentationPower_antitone k G) (Nat.zero_le 1))
  have hA0 : A 0 - A 1 = 1 := by
    simpa only [A, hilbertCoeff, Nat.zero_add] using hilbertCoeff_zero k G
  have hAdiff : (A 0 : ℝ) - A 1 = 1 := by
    rw [← Nat.cast_sub hAle, hA0]
    norm_num
  have hAzero : A (m + 1) = 0 := by
    dsimp only [A]
    rw [augmentationPower_eq_bot_of_pow_eq_bot k G m (m + 1) hm
      (Nat.le_succ m), finrank_bot]
  have hArec :
      Helpers.filteredWeight m A t =
        1 + t * Helpers.filteredWeight m (fun n ↦ A (n + 1)) t := by
    calc
      Helpers.filteredWeight m A t = Helpers.filteredWeight (m + 1) A t :=
        (Helpers.filteredWeight_succ_eq_of_eq_zero m A t hAzero).symm
      _ = (A 0 : ℝ) - A 1 +
          t * Helpers.filteredWeight m (fun n ↦ A (n + 1)) t := rfl
      _ = 1 + t * Helpers.filteredWeight m (fun n ↦ A (n + 1)) t := by
        rw [hAdiff]
  have hK01 : K 0 = K 1 := by
    dsimp only [K]
    rw [kernelPower_zero_eq_top k G g, kernelPower_one_eq_top k G g hlin]
  have hm1 : augmentationIdeal k G ^ (m + 1) = ⊥ := by
    apply le_antisymm
    · exact (Ideal.pow_le_pow_right (Nat.le_succ m)).trans (le_of_eq hm)
    · exact bot_le
  have hKzero : K (m + 1) = 0 := by
    dsimp only [K]
    rw [kernelPower_eq_bot_of_pow_eq_bot k G g hm1, finrank_bot]
  have hKrec :
      Helpers.filteredWeight m K t =
        t * Helpers.filteredWeight m (fun n ↦ K (n + 1)) t := by
    calc
      Helpers.filteredWeight m K t = Helpers.filteredWeight (m + 1) K t :=
        (Helpers.filteredWeight_succ_eq_of_eq_zero m K t hKzero).symm
      _ = (K 0 : ℝ) - K 1 +
          t * Helpers.filteredWeight m (fun n ↦ K (n + 1)) t := rfl
      _ = t * Helpers.filteredWeight m (fun n ↦ K (n + 1)) t := by
        rw [hK01]
        ring
  have hfree :
      Helpers.filteredWeight m
          (fun n ↦ Module.finrank k (freePower k G r n)) t =
        (r : ℝ) * Helpers.filteredWeight m A t := by
    calc
      Helpers.filteredWeight m
          (fun n ↦ Module.finrank k (freePower k G r n)) t =
          Helpers.filteredWeight m (fun n ↦ r * A n) t := by
        congr 1
        funext n
        exact finrank_freePower k G r n
      _ = (r : ℝ) * Helpers.filteredWeight m A t :=
        Helpers.filteredWeight_nat_mul m r A t
  have hrelations :
      Helpers.filteredWeight m (fun n ↦ K (n + 1)) t ≤
        (r : ℝ) * Helpers.filteredWeight m A t := by
    calc
      Helpers.filteredWeight m (fun n ↦ K (n + 1)) t ≤
          Helpers.filteredWeight m
            (fun n ↦ Module.finrank k (relationImagePower k G g y n)) t :=
        filteredWeight_kernel_le_relationImage k G g hlin y hy ht0 ht1
      _ ≤ Helpers.filteredWeight m
          (fun n ↦ Module.finrank k (freePower k G r n)) t :=
        filteredWeight_relationImage_le_freePower k G g y ht0
      _ = (r : ℝ) * Helpers.filteredWeight m A t := hfree
  have hshift :
      Helpers.filteredWeight m (fun n ↦ A (n + 1)) t =
        (d : ℝ) * Helpers.filteredWeight m A t -
          Helpers.filteredWeight m K t := by
    linarith [hdimWeight]
  rw [eval_hilbertPolynomial_eq_filteredWeight k G m hm t]
  calc
    1 = Helpers.filteredWeight m A t -
        t * Helpers.filteredWeight m (fun n ↦ A (n + 1)) t := by
      linarith [hArec]
    _ = (1 - (d : ℝ) * t) * Helpers.filteredWeight m A t +
        t * Helpers.filteredWeight m K t := by
      rw [hshift]
      ring
    _ = (1 - (d : ℝ) * t) * Helpers.filteredWeight m A t +
        t ^ 2 * Helpers.filteredWeight m (fun n ↦ K (n + 1)) t := by
      rw [hKrec]
      ring
    _ ≤ (1 - (d : ℝ) * t) * Helpers.filteredWeight m A t +
        t ^ 2 * ((r : ℝ) * Helpers.filteredWeight m A t) := by
      simpa only [add_comm] using add_le_add_left
        (mul_le_mul_of_nonneg_left hrelations (sq_nonneg t))
        ((1 - (d : ℝ) * t) * Helpers.filteredWeight m A t)
    _ = (1 - (d : ℝ) * t + (r : ℝ) * t ^ 2) *
        Helpers.filteredWeight m A t := by ring

/-- The Golod--Shafarevich inequality for a minimal group-algebra
presentation, expressed using its space of minimal relations. -/
theorem minimalPresentation_inequality {d : ℕ} (g : Fin d → G)
    (hlin : LinearIndependent k (fun i ↦ groupToCotangent k G (g i)))
    (hspan : Submodule.span k
      (Set.range fun i ↦ groupToCotangent k G (g i)) = ⊤)
    (hnil : IsNilpotent (augmentationIdeal k G)) (hd : 0 < d) :
    (d : ℝ) ^ 2 <
      4 * (Module.finrank k (RelationSpace k G g) : ℝ) := by
  let r := Module.finrank k (RelationSpace k G g)
  change (d : ℝ) ^ 2 < 4 * (r : ℝ)
  have hspan' : Submodule.span k
      (groupToCotangent k G '' Set.range g) = ⊤ := by
    rw [show groupToCotangent k G '' Set.range g =
        Set.range (fun i ↦ groupToCotangent k G (g i)) by
      ext x
      constructor
      · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨g i, ⟨i, rfl⟩, rfl⟩]
    exact hspan
  have hsurj : Function.Surjective (presentationMap k G g) :=
    presentationMap_surjective_of_cotangent_span k G g hspan' hnil
  obtain ⟨y, _, hyspan⟩ := exists_relationGenerators k G g hnil
  have hy : Function.Surjective (relationMap k G g y) :=
    relationMap_surjective_of_span_eq_top k G g y hyspan
  have hdreal : 0 < (d : ℝ) := by exact_mod_cast hd
  by_cases hdlarge : 2 ≤ d
  · refine Helpers.golod_shafarevich_weighted_numeric hdreal
      (hilbertPolynomial k G) ?_ ?_
    · intro n
      rw [coeff_hilbertPolynomial]
      exact hilbertCoeff_nonneg k G n
    · dsimp only
      apply hilbert_weighted_inequality k G g hlin hsurj y hy hnil
      · positivity
      · apply (div_le_iff₀ hdreal).2
        have hdlarge' : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hdlarge
        simpa only [one_mul] using hdlarge'
  · have hdone : d = 1 := by omega
    subst d
    have hweight := hilbert_weighted_inequality k G g hlin hsurj y hy hnil
      (t := (1 : ℝ)) (by norm_num) (by norm_num)
    have hrpos : 0 < r := by
      by_contra hr
      have hrzero : r = 0 := Nat.eq_zero_of_not_pos hr
      change Module.finrank k (RelationSpace k G g) = 0 at hrzero
      rw [hrzero] at hweight
      norm_num at hweight
    have hrreal : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hrpos
    norm_num
    nlinarith

end Submission.GolodShafarevich
