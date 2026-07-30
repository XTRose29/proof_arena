import Mathlib

open Finset Nat Real
open scoped BigOperators

noncomputable section

namespace Submission.BrunSieve

private theorem sum_product_three {α β γ : Type*} [DecidableEq α] [DecidableEq β]
    [DecidableEq γ] (s : Finset α) (t : Finset β) (u : Finset γ)
    (f : α → ℝ) (g : β → ℝ) (h : γ → ℝ) :
    (∑ p ∈ (s ×ˢ t) ×ˢ u, f p.1.1 * (g p.1.2 * h p.2)) =
      (∑ a ∈ s, f a) * (∑ b ∈ t, g b) * ∑ c ∈ u, h c := by
  rw [sum_product, sum_product]
  symm
  rw [mul_assoc, sum_mul]
  apply sum_congr rfl
  intro a _
  rw [sum_mul, mul_sum]
  apply sum_congr rfl
  intro b _
  rw [← mul_assoc, mul_sum]
  apply sum_congr rfl
  intro c _
  ring

def posInterval (M : ℕ) : Finset ℕ := Icc 1 M

def harmonicPartial (M : ℕ) : ℝ :=
  ∑ n ∈ posInterval M, (n : ℝ)⁻¹

def zetaTwoPartial (M : ℕ) : ℝ :=
  ∑ n ∈ posInterval M, ((n : ℝ) ^ 2)⁻¹

def coprimePairs (M : ℕ) : Finset (ℕ × ℕ) :=
  (posInterval M ×ˢ posInterval M).filter fun p => p.1.Coprime p.2

def coprimePairSum (M : ℕ) : ℝ :=
  ∑ p ∈ coprimePairs M, ((p.1 * p.2 : ℕ) : ℝ)⁻¹

def gcdDecomp (p : ℕ × ℕ) : ℕ × (ℕ × ℕ) :=
  (p.1.gcd p.2, (p.1 / p.1.gcd p.2, p.2 / p.1.gcd p.2))

theorem gcdDecomp_mapsTo (M : ℕ) :
    Set.MapsTo gcdDecomp (↑(posInterval M ×ˢ posInterval M) : Set (ℕ × ℕ))
      (↑(posInterval M ×ˢ coprimePairs M) : Set (ℕ × (ℕ × ℕ))) := by
  rintro ⟨a, b⟩ hab
  rcases mem_product.mp hab with ⟨ha, hb⟩
  simp only [posInterval, mem_Icc] at ha hb
  have hgpos : 0 < a.gcd b := gcd_pos_of_pos_left _ ha.1
  have hg_le_a : a.gcd b ≤ a := gcd_le_left _ ha.1
  have hg_le_b : a.gcd b ≤ b := gcd_le_right _ hb.1
  have hxda : 0 < a / a.gcd b := Nat.div_pos hg_le_a hgpos
  have hydb : 0 < b / a.gcd b := Nat.div_pos hg_le_b hgpos
  change (a.gcd b, (a / a.gcd b, b / a.gcd b)) ∈
    posInterval M ×ˢ coprimePairs M
  exact mem_product.mpr ⟨
    mem_Icc.mpr ⟨hgpos, hg_le_a.trans ha.2⟩,
    mem_filter.mpr ⟨mem_product.mpr ⟨
      mem_Icc.mpr ⟨hxda, (Nat.div_le_self _ _).trans ha.2⟩,
      mem_Icc.mpr ⟨hydb, (Nat.div_le_self _ _).trans hb.2⟩⟩,
      coprime_div_gcd_div_gcd hgpos⟩⟩

theorem gcdDecomp_injOn (M : ℕ) :
    Set.InjOn gcdDecomp (↑(posInterval M ×ˢ posInterval M) : Set (ℕ × ℕ)) := by
  rintro ⟨a, b⟩ _hab ⟨c, d⟩ _hcd h
  simp only [gcdDecomp, Prod.mk.injEq] at h
  have ha : a.gcd b * (a / a.gcd b) = a := Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)
  have hb : a.gcd b * (b / a.gcd b) = b := Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)
  have hc : c.gcd d * (c / c.gcd d) = c := Nat.mul_div_cancel' (Nat.gcd_dvd_left c d)
  have hd : c.gcd d * (d / c.gcd d) = d := Nat.mul_div_cancel' (Nat.gcd_dvd_right c d)
  rcases h with ⟨hg, hx, hy⟩
  apply Prod.ext
  · calc
      a = a.gcd b * (a / a.gcd b) := ha.symm
      _ = c.gcd d * (c / c.gcd d) := congrArg₂ (· * ·) hg hx
      _ = c := hc
  · calc
      b = a.gcd b * (b / a.gcd b) := hb.symm
      _ = c.gcd d * (d / c.gcd d) := congrArg₂ (· * ·) hg hy
      _ = d := hd

theorem gcdDecomp_weight (p : ℕ × ℕ) :
    (((p.1 * p.2 : ℕ) : ℝ))⁻¹ =
      ((((p.1.gcd p.2 : ℕ) : ℝ) ^ 2)⁻¹ *
        (((p.1 / p.1.gcd p.2) * (p.2 / p.1.gcd p.2) : ℕ) : ℝ)⁻¹) := by
  have ha : p.1.gcd p.2 * (p.1 / p.1.gcd p.2) = p.1 :=
    Nat.mul_div_cancel' (Nat.gcd_dvd_left p.1 p.2)
  have hb : p.1.gcd p.2 * (p.2 / p.1.gcd p.2) = p.2 :=
    Nat.mul_div_cancel' (Nat.gcd_dvd_right p.1 p.2)
  have hab : p.1 * p.2 =
      (p.1.gcd p.2) ^ 2 *
        ((p.1 / p.1.gcd p.2) * (p.2 / p.1.gcd p.2)) := by
    calc
      p.1 * p.2 =
          (p.1.gcd p.2 * (p.1 / p.1.gcd p.2)) *
            (p.1.gcd p.2 * (p.2 / p.1.gcd p.2)) := congrArg₂ (· * ·) ha.symm hb.symm
      _ = _ := by ring
  rw [hab]
  push_cast
  ring

theorem harmonic_sq_le_zeta_mul_coprime (M : ℕ) :
    harmonicPartial M ^ 2 ≤ zetaTwoPartial M * coprimePairSum M := by
  classical
  let source := posInterval M ×ˢ posInterval M
  let target := posInterval M ×ˢ coprimePairs M
  let weight : (ℕ × ℕ) → ℝ := fun p => (((p.1 * p.2 : ℕ) : ℝ))⁻¹
  let targetWeight : (ℕ × (ℕ × ℕ)) → ℝ := fun p =>
    (((p.1 : ℝ) ^ 2)⁻¹ * (((p.2.1 * p.2.2 : ℕ) : ℝ))⁻¹)
  calc
    harmonicPartial M ^ 2 = ∑ p ∈ source, weight p := by
      change harmonicPartial M ^ 2 =
        ∑ p ∈ posInterval M ×ˢ posInterval M, weight p
      rw [harmonicPartial, pow_two, sum_mul]
      simp_rw [mul_sum]
      rw [sum_product]
      apply sum_congr rfl
      intro a _
      apply sum_congr rfl
      intro b _
      simp only [weight, Nat.cast_mul, mul_inv]
    _ = ∑ p ∈ source.image gcdDecomp, targetWeight p := by
      rw [sum_image (by simpa only [source] using gcdDecomp_injOn M)]
      apply sum_congr rfl
      intro p hp
      simp only [source, mem_product, posInterval, mem_Icc] at hp
      simpa only [weight, targetWeight, gcdDecomp] using gcdDecomp_weight p
    _ ≤ ∑ p ∈ target, targetWeight p := by
      apply sum_le_sum_of_subset_of_nonneg
      · apply image_subset_iff.mpr
        intro p hp
        exact gcdDecomp_mapsTo M hp
      · intro p _hp _hpi
        exact mul_nonneg (inv_nonneg.mpr (sq_nonneg _))
          (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ = zetaTwoPartial M * coprimePairSum M := by
      change (∑ p ∈ posInterval M ×ˢ coprimePairs M, targetWeight p) = _
      rw [sum_product, zetaTwoPartial, coprimePairSum, sum_mul]
      simp_rw [mul_sum]
      rfl

theorem zetaTwoPartial_le_two (M : ℕ) : zetaTwoPartial M ≤ 2 := by
  by_cases hM : M = 0
  · simp [zetaTwoPartial, posInterval, hM]
  have hM1 : 1 ≤ M := Nat.one_le_iff_ne_zero.mpr hM
  rw [zetaTwoPartial, posInterval,
    ← sum_erase_add (Icc 1 M) _ (left_mem_Icc.mpr hM1)]
  have hrest :
      ∑ n ∈ (Icc 1 M).erase 1, ((n : ℝ) ^ 2)⁻¹ ≤ 1 := by
    rw [Icc_erase_left, ← Ico_succ_succ_eq_Ioc]
    calc
      ∑ n ∈ Ico 2 (M + 1), ((n : ℝ) ^ 2)⁻¹ ≤
          ∑ n ∈ Ico 2 (M + 1),
            (((n - 1 : ℕ) : ℝ)⁻¹ - (n : ℝ)⁻¹) := by
        gcongr with n hn
        simp only [mem_Ico] at hn
        have hn2 : 2 ≤ n := hn.1
        have hncast : (2 : ℝ) ≤ n := by exact_mod_cast hn2
        have hnpos : (0 : ℝ) < n := by positivity
        have hnsubpos : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by
          exact_mod_cast (show 0 < n - 1 by omega)
        rw [inv_sub_inv (ne_of_gt hnsubpos) (ne_of_gt hnpos)]
        norm_num [Nat.cast_sub (by omega : 1 ≤ n)]
        rw [← mul_inv]
        apply (inv_le_inv₀ (sq_pos_of_pos hnpos) (mul_pos hnpos (by linarith [hncast]))).2
        norm_num [pow_two]
        nlinarith
      _ = 1 - (M : ℝ)⁻¹ := by
        rw [sum_Ico_eq_sum_range]
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, hM,
          Nat.sub_add_cancel hM1]
          using sum_range_sub' (fun k : ℕ => (((k + 1 : ℕ) : ℝ))⁻¹) (M - 1)
      _ ≤ 1 := by
        have : 0 ≤ (M : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg M)
        linarith
  norm_num at hrest ⊢
  linarith

theorem harmonic_sq_le_two_coprime (M : ℕ) :
    harmonicPartial M ^ 2 ≤ 2 * coprimePairSum M := by
  calc
    harmonicPartial M ^ 2 ≤ zetaTwoPartial M * coprimePairSum M :=
      harmonic_sq_le_zeta_mul_coprime M
    _ ≤ 2 * coprimePairSum M := by
      apply mul_le_mul_of_nonneg_right (zetaTwoPartial_le_two M)
      exact sum_nonneg fun p _hp => inv_nonneg.mpr (Nat.cast_nonneg _)

noncomputable def squarefreePart (n : ℕ) : ℕ :=
  Classical.choose (sq_mul_squarefree n)

noncomputable def squarePart (n : ℕ) : ℕ :=
  Classical.choose (Classical.choose_spec (sq_mul_squarefree n))

theorem squareDecomposition (n : ℕ) :
    squarePart n ^ 2 * squarefreePart n = n :=
  (Classical.choose_spec (Classical.choose_spec (sq_mul_squarefree n))).1

theorem squarefree_squarefreePart (n : ℕ) : Squarefree (squarefreePart n) :=
  (Classical.choose_spec (Classical.choose_spec (sq_mul_squarefree n))).2

theorem squarePart_pos {n : ℕ} (hn : 0 < n) : 0 < squarePart n := by
  rw [← squareDecomposition n] at hn
  exact (pow_pos_iff (by norm_num : 2 ≠ 0)).mp (Nat.pos_of_mul_pos_right hn)

theorem squarefreePart_pos {n : ℕ} (hn : 0 < n) : 0 < squarefreePart n := by
  rw [← squareDecomposition n] at hn
  exact Nat.pos_of_mul_pos_left hn

theorem squarePart_dvd (n : ℕ) : squarePart n ∣ n := by
  refine ⟨squarePart n * squarefreePart n, ?_⟩
  calc
    n = squarePart n ^ 2 * squarefreePart n := (squareDecomposition n).symm
    _ = squarePart n * (squarePart n * squarefreePart n) := by ring

theorem squarefreePart_dvd (n : ℕ) : squarefreePart n ∣ n := by
  refine ⟨squarePart n ^ 2, ?_⟩
  rw [mul_comm]
  exact (squareDecomposition n).symm

def squarefreeCoprimePairs (M : ℕ) : Finset (ℕ × ℕ) :=
  (coprimePairs M).filter fun p => Squarefree p.1 ∧ Squarefree p.2

def squarefreeCoprimePairSum (M : ℕ) : ℝ :=
  ∑ p ∈ squarefreeCoprimePairs M, (((p.1 * p.2 : ℕ) : ℝ))⁻¹

noncomputable def squareDecomp (p : ℕ × ℕ) : (ℕ × ℕ) × (ℕ × ℕ) :=
  ((squarePart p.1, squarePart p.2), (squarefreePart p.1, squarefreePart p.2))

theorem squareDecomp_mapsTo (M : ℕ) :
    Set.MapsTo squareDecomp (↑(coprimePairs M) : Set (ℕ × ℕ))
      (↑((posInterval M ×ˢ posInterval M) ×ˢ squarefreeCoprimePairs M) :
        Set ((ℕ × ℕ) × (ℕ × ℕ))) := by
  rintro ⟨a, b⟩ hab
  have hab' := mem_filter.mp hab
  rcases mem_product.mp hab'.1 with ⟨ha, hb⟩
  simp only [posInterval, mem_Icc] at ha hb
  have hsapos := squarePart_pos ha.1
  have hsbpos := squarePart_pos hb.1
  have hsfapos := squarefreePart_pos ha.1
  have hsfbpos := squarefreePart_pos hb.1
  have hsa_le : squarePart a ≤ a := Nat.le_of_dvd ha.1 (squarePart_dvd a)
  have hsb_le : squarePart b ≤ b := Nat.le_of_dvd hb.1 (squarePart_dvd b)
  have hsfa_le : squarefreePart a ≤ a := Nat.le_of_dvd ha.1 (squarefreePart_dvd a)
  have hsfb_le : squarefreePart b ≤ b := Nat.le_of_dvd hb.1 (squarefreePart_dvd b)
  change ((squarePart a, squarePart b), (squarefreePart a, squarefreePart b)) ∈
    (posInterval M ×ˢ posInterval M) ×ˢ squarefreeCoprimePairs M
  apply mem_product.mpr
  constructor
  · exact mem_product.mpr ⟨mem_Icc.mpr ⟨hsapos, hsa_le.trans ha.2⟩,
      mem_Icc.mpr ⟨hsbpos, hsb_le.trans hb.2⟩⟩
  · apply mem_filter.mpr
    refine ⟨mem_filter.mpr ⟨mem_product.mpr ⟨
      mem_Icc.mpr ⟨hsfapos, hsfa_le.trans ha.2⟩,
      mem_Icc.mpr ⟨hsfbpos, hsfb_le.trans hb.2⟩⟩, ?_⟩, ?_⟩
    · exact Coprime.of_dvd (squarefreePart_dvd a) (squarefreePart_dvd b) hab'.2
    · exact ⟨squarefree_squarefreePart a, squarefree_squarefreePart b⟩

theorem squareDecomp_injOn (M : ℕ) :
    Set.InjOn squareDecomp (↑(coprimePairs M) : Set (ℕ × ℕ)) := by
  rintro ⟨a, b⟩ _hab ⟨c, d⟩ _hcd h
  have hsa := congrArg (fun x => x.1.1) h
  have hsb := congrArg (fun x => x.1.2) h
  have hsfa := congrArg (fun x => x.2.1) h
  have hsfb := congrArg (fun x => x.2.2) h
  simp only [squareDecomp] at hsa hsb hsfa hsfb
  apply Prod.ext
  · calc
      a = squarePart a ^ 2 * squarefreePart a := (squareDecomposition a).symm
      _ = squarePart c ^ 2 * squarefreePart c :=
        congrArg₂ (fun x y => x ^ 2 * y) hsa hsfa
      _ = c := squareDecomposition c
  · calc
      b = squarePart b ^ 2 * squarefreePart b := (squareDecomposition b).symm
      _ = squarePart d ^ 2 * squarefreePart d :=
        congrArg₂ (fun x y => x ^ 2 * y) hsb hsfb
      _ = d := squareDecomposition d

theorem squareDecomp_weight (p : ℕ × ℕ) :
    (((p.1 * p.2 : ℕ) : ℝ))⁻¹ =
      (((((squarePart p.1) : ℝ) ^ 2)⁻¹ *
          ((((squarePart p.2) : ℝ) ^ 2)⁻¹ *
            (((squarefreePart p.1 * squarefreePart p.2 : ℕ) : ℝ))⁻¹))) := by
  have hab : p.1 * p.2 =
      ((squarePart p.1) ^ 2 * (squarePart p.2) ^ 2) *
        (squarefreePart p.1 * squarefreePart p.2) := by
    calc
      p.1 * p.2 =
          (squarePart p.1 ^ 2 * squarefreePart p.1) *
            (squarePart p.2 ^ 2 * squarefreePart p.2) :=
        congrArg₂ (· * ·) (squareDecomposition p.1).symm (squareDecomposition p.2).symm
      _ = _ := by ring
  rw [hab]
  push_cast
  ring

theorem coprime_le_zeta_sq_mul_squarefree (M : ℕ) :
    coprimePairSum M ≤ zetaTwoPartial M ^ 2 * squarefreeCoprimePairSum M := by
  classical
  let target := (posInterval M ×ˢ posInterval M) ×ˢ squarefreeCoprimePairs M
  let targetWeight : ((ℕ × ℕ) × (ℕ × ℕ)) → ℝ := fun p =>
    (((p.1.1 : ℝ) ^ 2)⁻¹ *
      (((p.1.2 : ℝ) ^ 2)⁻¹ * (((p.2.1 * p.2.2 : ℕ) : ℝ))⁻¹))
  calc
    coprimePairSum M =
        ∑ p ∈ (coprimePairs M).image squareDecomp, targetWeight p := by
      rw [sum_image (squareDecomp_injOn M)]
      apply sum_congr rfl
      intro p _hp
      simpa only [coprimePairSum, targetWeight, squareDecomp] using squareDecomp_weight p
    _ ≤ ∑ p ∈ target, targetWeight p := by
      apply sum_le_sum_of_subset_of_nonneg
      · apply image_subset_iff.mpr
        intro p hp
        exact squareDecomp_mapsTo M hp
      · intro p _hp _hpi
        positivity
    _ = zetaTwoPartial M ^ 2 * squarefreeCoprimePairSum M := by
      change (∑ p ∈ (posInterval M ×ˢ posInterval M) ×ˢ squarefreeCoprimePairs M,
        targetWeight p) = _
      rw [zetaTwoPartial, squarefreeCoprimePairSum, pow_two]
      simpa only [targetWeight] using
        sum_product_three (posInterval M) (posInterval M) (squarefreeCoprimePairs M)
          (fun n => ((n : ℝ) ^ 2)⁻¹) (fun n => ((n : ℝ) ^ 2)⁻¹)
          (fun p => (((p.1 * p.2 : ℕ) : ℝ))⁻¹)

theorem coprime_le_four_squarefree (M : ℕ) :
    coprimePairSum M ≤ 4 * squarefreeCoprimePairSum M := by
  calc
    coprimePairSum M ≤ zetaTwoPartial M ^ 2 * squarefreeCoprimePairSum M :=
      coprime_le_zeta_sq_mul_squarefree M
    _ ≤ 4 * squarefreeCoprimePairSum M := by
      have hznonneg : 0 ≤ zetaTwoPartial M := by
        rw [zetaTwoPartial]
        positivity
      have hsfnonneg : 0 ≤ squarefreeCoprimePairSum M := by
        rw [squarefreeCoprimePairSum]
        positivity
      apply mul_le_mul_of_nonneg_right
      · nlinarith [zetaTwoPartial_le_two M]
      · exact hsfnonneg

theorem harmonic_sq_le_eight_squarefree (M : ℕ) :
    harmonicPartial M ^ 2 ≤ 8 * squarefreeCoprimePairSum M := by
  calc
    harmonicPartial M ^ 2 ≤ 2 * coprimePairSum M := harmonic_sq_le_two_coprime M
    _ ≤ 2 * (4 * squarefreeCoprimePairSum M) := by
      gcongr
      exact coprime_le_four_squarefree M
    _ = 8 * squarefreeCoprimePairSum M := by ring

end Submission.BrunSieve
