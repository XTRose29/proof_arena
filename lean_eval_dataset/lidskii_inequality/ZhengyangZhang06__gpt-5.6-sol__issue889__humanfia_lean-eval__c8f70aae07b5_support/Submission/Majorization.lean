import Mathlib

namespace Submission.Majorization

private lemma convexOn_abs_rpow {p : ℝ} (hp : 1 ≤ p) :
    ConvexOn ℝ Set.univ (fun x : ℝ ↦ |x| ^ p) := by
  have himage : (fun x : ℝ ↦ |x|) '' Set.univ = Set.Ici 0 := by
    ext y
    constructor
    · rintro ⟨x, -, rfl⟩
      exact abs_nonneg x
    · intro hy
      exact ⟨y, Set.mem_univ y, abs_of_nonneg hy⟩
  have habs : ConvexOn ℝ Set.univ (fun x : ℝ ↦ |x|) := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b ha hb _
    dsimp
    calc
      |a * x + b * y| ≤ |a * x| + |b * y| := by
        simpa only [Real.norm_eq_abs] using norm_add_le (a * x) (b * y)
      _ = a * |x| + b * |y| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
  have hpow : ConvexOn ℝ ((fun x : ℝ ↦ |x|) '' Set.univ) (fun x : ℝ ↦ x ^ p) := by
    rw [himage]
    exact convexOn_rpow hp
  have hmono : MonotoneOn (fun x : ℝ ↦ x ^ p) ((fun x : ℝ ↦ |x|) '' Set.univ) := by
    rw [himage]
    exact Real.monotoneOn_rpow_Ici_of_exponent_nonneg (by positivity)
  change ConvexOn ℝ Set.univ ((fun x : ℝ ↦ x ^ p) ∘ fun x : ℝ ↦ |x|)
  exact hpow.comp habs hmono

private lemma convex_support {f : ℝ → ℝ} {x d : ℝ}
    (hf : ConvexOn ℝ Set.univ f) (hder : HasDerivAt f d x) (y : ℝ) :
    f x - f y ≤ d * (x - y) := by
  rcases lt_trichotomy x y with hxy | rfl | hyx
  · have h := hf.le_slope_of_hasDerivAt (Set.mem_univ x) (Set.mem_univ y) hxy hder
    rw [slope_def_field] at h
    have hm := (le_div_iff₀ (sub_pos.mpr hxy)).mp h
    nlinarith
  · simp
  · have h := hf.slope_le_of_hasDerivAt (Set.mem_univ y) (Set.mem_univ x) hyx hder
    rw [slope_def_field] at h
    have hm := (div_le_iff₀ (sub_pos.mpr hyx)).mp h
    nlinarith

def seqAt {N : ℕ} (x : Fin N → ℝ) (i : ℕ) : ℝ :=
  if hi : i < N then x ⟨i, hi⟩ else 0

@[simp]
lemma seqAt_of_lt {N : ℕ} (x : Fin N → ℝ) {i : ℕ} (hi : i < N) :
    seqAt x i = x ⟨i, hi⟩ := by
  simp [seqAt, hi]

lemma sum_seqAt {N : ℕ} (f : ℝ → ℝ) (x : Fin N → ℝ) :
    ∑ i, f (x i) = ∑ i ∈ Finset.range N, f (seqAt x i) := by
  calc
    ∑ i : Fin N, f (x i) = ∑ i : Fin N, f (seqAt x i.val) := by
      apply Finset.sum_congr rfl
      intro (i : Fin N) _
      rw [seqAt_of_lt x i.isLt]
    _ = ∑ i ∈ Finset.range N, f (seqAt x i) :=
      Fin.sum_univ_eq_sum_range (fun i ↦ f (seqAt x i)) N

private lemma sum_le_sum_of_sorted_prefix {N : ℕ} {x y : Fin N → ℝ}
    (hx : Antitone x)
    (hpartial : ∀ k, k ≤ N →
      ∑ i ∈ Finset.range k, seqAt x i ≤ ∑ i ∈ Finset.range k, seqAt y i)
    (htotal : ∑ i, x i = ∑ i, y i)
    {f w : ℝ → ℝ} (hw : Monotone w)
    (hsupport : ∀ a b, f a - f b ≤ w a * (a - b)) :
    ∑ i, f (x i) ≤ ∑ i, f (y i) := by
  let a : ℕ → ℝ := fun i ↦ seqAt x i - seqAt y i
  let v : ℕ → ℝ := fun i ↦ w (seqAt x i)
  let A : ℕ → ℝ := fun k ↦ ∑ i ∈ Finset.range k, a i
  have hA (k : ℕ) (hk : k ≤ N) : A k ≤ 0 := by
    dsimp [A, a]
    rw [Finset.sum_sub_distrib]
    exact sub_nonpos.mpr (hpartial k hk)
  have hAN : A N = 0 := by
    dsimp [A, a]
    rw [Finset.sum_sub_distrib]
    have hxsum : ∑ i ∈ Finset.range N, seqAt x i = ∑ i, x i := by
      simpa only [id_eq] using (sum_seqAt id x).symm
    have hysum : ∑ i ∈ Finset.range N, seqAt y i = ∑ i, y i := by
      simpa only [id_eq] using (sum_seqAt id y).symm
    rw [hxsum, hysum, htotal, sub_self]
  have hv (i : ℕ) (hi : i < N - 1) : v (i + 1) - v i ≤ 0 := by
    have hiN : i < N := by omega
    have hi1N : i + 1 < N := by omega
    have hxi : seqAt x (i + 1) ≤ seqAt x i := by
      rw [seqAt_of_lt x hi1N, seqAt_of_lt x hiN]
      exact hx (Fin.mk_le_mk.mpr (Nat.le_succ i))
    exact sub_nonpos.mpr (hw hxi)
  have hab : ∑ i ∈ Finset.range N, v i * a i ≤ 0 := by
    have hparts := Finset.sum_range_by_parts v a N
    simp only [smul_eq_mul] at hparts
    rw [hparts]
    change v (N - 1) * A N -
      ∑ i ∈ Finset.range (N - 1), (v (i + 1) - v i) * A (i + 1) ≤ 0
    rw [hAN, mul_zero, zero_sub]
    apply neg_nonpos.mpr
    apply Finset.sum_nonneg
    intro i hi
    have hi' : i < N - 1 := Finset.mem_range.mp hi
    have hiN : i + 1 ≤ N := by omega
    exact mul_nonneg_of_nonpos_of_nonpos
      (hv i hi') (hA (i + 1) hiN)
  rw [sum_seqAt f x, sum_seqAt f y, ← sub_nonpos, ← Finset.sum_sub_distrib]
  calc
    ∑ i ∈ Finset.range N, (f (seqAt x i) - f (seqAt y i)) ≤
        ∑ i ∈ Finset.range N, v i * a i := by
      apply Finset.sum_le_sum
      intro i _
      exact hsupport (seqAt x i) (seqAt y i)
    _ ≤ 0 := hab

private lemma monotone_sign : Monotone Real.sign := by
  intro a b hab
  simp only [Real.sign]
  split_ifs <;> norm_num <;> linarith

private lemma abs_support (a b : ℝ) :
    |a| - |b| ≤ Real.sign a * (a - b) := by
  rcases lt_trichotomy a 0 with ha | rfl | ha
  · rw [Real.sign_of_neg ha, abs_of_neg ha]
    nlinarith [neg_le_abs b]
  · simp
  · rw [Real.sign_of_pos ha, abs_of_pos ha]
    nlinarith [le_abs_self b]

lemma sum_abs_rpow_le_of_sorted_prefix {N : ℕ} {x y : Fin N → ℝ}
    (hx : Antitone x)
    (hpartial : ∀ k, k ≤ N →
      ∑ i ∈ Finset.range k, seqAt x i ≤ ∑ i ∈ Finset.range k, seqAt y i)
    (htotal : ∑ i, x i = ∑ i, y i) {p : ℝ} (hp : 1 ≤ p) :
    ∑ i, |x i| ^ p ≤ ∑ i, |y i| ^ p := by
  rcases hp.eq_or_lt with rfl | hp
  · simpa using sum_le_sum_of_sorted_prefix hx hpartial htotal monotone_sign abs_support
  · let f : ℝ → ℝ := fun z ↦ |z| ^ p
    let w : ℝ → ℝ := fun z ↦ p * |z| ^ (p - 2) * z
    have hf : ConvexOn ℝ Set.univ f := convexOn_abs_rpow hp.le
    have hder (z : ℝ) : HasDerivAt f (w z) z := hasDerivAt_abs_rpow z hp
    have hw : Monotone w := by
      intro a b hab
      have hm := hf.monotoneOn_deriv
        (fun z _ ↦ (hder z).differentiableAt) (Set.mem_univ a) (Set.mem_univ b) hab
      simpa only [(hder a).deriv, (hder b).deriv] using hm
    change ∑ i, f (x i) ≤ ∑ i, f (y i)
    exact sum_le_sum_of_sorted_prefix (f := f) (w := w) hx hpartial htotal hw
      (fun a b ↦ convex_support hf (hder a) b)

lemma sum_abs_rpow_le_of_permuted_prefix {N : ℕ} {x y : Fin N → ℝ}
    (hpartial : ∀ (σ : Equiv.Perm (Fin N)) k, k ≤ N →
      ∑ i ∈ Finset.range k, seqAt (x ∘ σ) i ≤
        ∑ i ∈ Finset.range k, seqAt y i)
    (htotal : ∑ i, x i = ∑ i, y i) {p : ℝ} (hp : 1 ≤ p) :
    ∑ i, |x i| ^ p ≤ ∑ i, |y i| ^ p := by
  let σ : Equiv.Perm (Fin N) := Fin.revPerm.trans (Tuple.sort x)
  let xs : Fin N → ℝ := x ∘ σ
  have hxs : Antitone xs := by
    intro i j hij
    exact Tuple.monotone_sort x (Fin.rev_le_rev.mpr hij)
  have htotal' : ∑ i, xs i = ∑ i, y i := by
    calc
      ∑ i, xs i = ∑ i, x i := by
        simpa [xs, Function.comp_def] using σ.sum_comp Finset.univ x
      _ = ∑ i, y i := htotal
  have h := sum_abs_rpow_le_of_sorted_prefix hxs (hpartial σ) htotal' hp
  calc
    ∑ i, |x i| ^ p = ∑ i, |xs i| ^ p := by
      simpa [xs, Function.comp_def] using
        (σ.sum_comp Finset.univ (fun i ↦ |x i| ^ p) (by simp)).symm
    _ ≤ ∑ i, |y i| ^ p := h

end Submission.Majorization
