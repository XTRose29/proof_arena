import Mathlib

-- BEGIN INLINED FILE: Mathlib/Support/lidskii_inequality_145b211497/SchurDiagonal.lean
open scoped BigOperators
open Finset Set Matrix

namespace LidskiiAux

lemma convex_abs_rpow (p:ℝ) (hp:1≤p) :
    ConvexOn ℝ (Set.univ : Set ℝ) (fun x : ℝ => |x| ^ p) := by
  have hf : ConvexOn ℝ (Set.univ : Set ℝ) (fun x : ℝ => |x|) := by
    -- prove directly from triangle inequality
    refine ⟨convex_univ, ?_⟩
    intro a ha b hb u v hu hv huv
    simp only
    calc
      |u • a + v • b| = |u * a + v * b| := by rfl
      _ ≤ |u*a| + |v*b| := abs_add_le _ _
      _ = u • |a| + v • |b| := by simp [abs_mul, abs_of_nonneg hu, abs_of_nonneg hv, smul_eq_mul]
  have him : (fun x : ℝ => |x|) '' Set.univ = Set.Ici (0 : ℝ) := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      change 0 ≤ |x|
      exact abs_nonneg _
    · intro hz
      have hz0 : 0 ≤ z := hz
      exact ⟨z, Set.mem_univ _, (abs_of_nonneg hz0)⟩
  have hg : ConvexOn ℝ ((fun x : ℝ => |x|) '' Set.univ) (fun y : ℝ => y ^ p) := by
    rw [him]
    exact convexOn_rpow hp
  have hmon : MonotoneOn (fun y : ℝ => y ^ p) ((fun x : ℝ => |x|) '' Set.univ) := by
    intro a ha b hb hab
    have a0 : 0 ≤ a := by simpa [him] using ha
    exact Real.rpow_le_rpow a0 hab (by linarith)
  simpa [Function.comp_def] using hg.comp hf hmon

-- try Jensen lemma

variable {ι κ : Type*} [Fintype ι] [Fintype κ]
open scoped BigOperators

lemma sum_abs_mulVec_le (p : ℝ) (hp : 1 ≤ p)
    (M : ι → κ → ℝ) (hrow : ∀ i, ∑ j : κ, M i j = 1)
    (hcol : ∀ j, ∑ i : ι, M i j = 1)
    (hn : ∀ i j, 0 ≤ M i j)
    (x : κ → ℝ) :
    ∑ i : ι, |∑ j : κ, M i j * x j| ^ p ≤
      ∑ j : κ, |x j| ^ p := by
  classical
  have rowle (i : ι) :
      |∑ j : κ, M i j * x j| ^ p ≤ ∑ j : κ, M i j * (|x j| ^ p) := by
    -- use ConvexOn.map_sum_le?
    have h := (convex_abs_rpow p hp).map_sum_le
      (t := (Finset.univ : Finset κ)) (w := M i) (p := x)
      (fun j hj => hn i j) (by simpa using hrow i) (by simp)
    exact h
  calc
    (∑ i : ι, |∑ j : κ, M i j * x j| ^ p) ≤
        ∑ i : ι, ∑ j : κ, M i j * (|x j| ^ p) :=
      Finset.sum_le_sum (fun i hi => rowle i)
    _ = ∑ j : κ, |x j| ^ p := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      rw [← Finset.sum_mul]
      rw [hcol j]
      simp

open scoped ComplexConjugate InnerProductSpace ComplexOrder

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]
variable {m : ℕ}

lemma diag_expansion (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric)
    (hm : Module.finrank ℂ E = m)
    (e : E) :
    RCLike.re (inner ℂ e (T e)) =
      ∑ j : Fin m, ‖inner ℂ e (hT.eigenvectorBasis hm j)‖ ^ 2 *
        (hT.eigenvalues hm j) := by
  let b := hT.eigenvectorBasis hm
  -- expand e using b, linearity
  have he : ∑ j : Fin m, (inner ℂ (b j) e) • b j = e :=
    OrthonormalBasis.sum_repr' b e
  -- target equality complex re of sum
  have hcomp : inner ℂ e (T e) =
      ∑ j : Fin m, (inner ℂ (b j) e) *
        (hT.eigenvalues hm j : ℂ) * (inner ℂ e (b j)) := by
    calc
      inner ℂ e (T e) = inner ℂ e (T (∑ j : Fin m, (inner ℂ (b j) e) • b j)) := by rw [he]
      _ = ∑ j : Fin m, (inner ℂ (b j) e) * (hT.eigenvalues hm j : ℂ) * (inner ℂ e (b j)) := by
        rw [map_sum, inner_sum]
        apply Finset.sum_congr rfl
        intro j hj
        rw [map_smul]
        rw [inner_smul_right]
        rw [hT.apply_eigenvectorBasis hm j]
        -- inner e ((λ) • b)
        rw [inner_smul_right]
        -- manipulate star? scalar in second linear -> no star
        change _
        simp [b]
        ring
  rw [hcomp, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  -- use conjugate inner
  have hc : inner ℂ (b j) e = conj (inner ℂ e (b j)) := by
    simpa using (inner_conj_symm e (b j))
  -- show real part product
  rw [hc]
  have hrearr (z : ℂ) (r : ℝ) : conj z * (r : ℂ) * z =
        ((conj z) * z) * (r : ℂ) := by ring
  rw [hrearr, Complex.conj_mul']
  rw [RCLike.mul_re]
  -- both factors have zero imaginary part
  rw [← Complex.ofReal_pow]
  change (Complex.ofReal (‖inner ℂ e (b j)‖ ^ 2)).re *
      (Complex.ofReal (hT.eigenvalues hm j)).re -
      (Complex.ofReal (‖inner ℂ e (b j)‖ ^ 2)).im *
      (Complex.ofReal (hT.eigenvalues hm j)).im = _
  rw [Complex.ofReal_re, Complex.ofReal_re, Complex.ofReal_im, Complex.ofReal_im]
  change _
  simp [b]


section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]
variable {m : ℕ}
variable {ι : Type*} [Fintype ι]

lemma overlap_row (u : OrthonormalBasis ι ℂ E)
    (b : OrthonormalBasis (Fin m) ℂ E) (i : ι) :
    ∑ j : Fin m, ‖inner ℂ (u i) (b j)‖ ^ 2 = 1 := by
  rw [b.sum_sq_norm_inner_left]
  rw [u.orthonormal.norm_eq_one]
  norm_num

lemma overlap_col (u : OrthonormalBasis ι ℂ E)
    (b : OrthonormalBasis (Fin m) ℂ E) (j : Fin m) :
    ∑ i : ι, ‖inner ℂ (u i) (b j)‖ ^ 2 = 1 := by
  rw [u.sum_sq_norm_inner_right]
  rw [b.orthonormal.norm_eq_one]
  norm_num

lemma schur_horn_pow_diag
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]
    {ι : Type*} [Fintype ι]
    {m : ℕ}
    (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric)
    (hm : Module.finrank ℂ E = m)
    (u : OrthonormalBasis ι ℂ E)
    (p : ℝ) (hp : 1 ≤ p) :
    ∑ i : ι, |RCLike.re (inner ℂ (u i) (T (u i)))| ^ p ≤
      ∑ j : Fin m, |hT.eigenvalues hm j| ^ p := by
  classical
  let b := hT.eigenvectorBasis hm
  let M : ι → Fin m → ℝ := fun i j => ‖inner ℂ (u i) (b j)‖ ^ 2
  have hr (i : ι) : ∑ j : Fin m, M i j = 1 := by
    exact overlap_row u b i
  have hc (j : Fin m) : ∑ i : ι, M i j = 1 := by
    exact overlap_col u b j
  have hn (i : ι) (j : Fin m) : 0 ≤ M i j := by
    dsimp [M]
    positivity
  have hd (i : ι) : RCLike.re (inner ℂ (u i) (T (u i))) =
        ∑ j : Fin m, M i j * (hT.eigenvalues hm j) := by
    simpa [M, b] using diag_expansion T hT hm (u i)
  convert (sum_abs_mulVec_le (ι := ι) (κ := Fin m) p hp M hr hc hn
      (hT.eigenvalues hm)) using 1 <;> simp [hd]

end
end
end LidskiiAux

-- END INLINED FILE: Mathlib/Support/lidskii_inequality_145b211497/SchurDiagonal.lean

-- BEGIN INLINED FILE: Mathlib/Support/lidskii_inequality_145b211497/ScalarWeighted.lean
open scoped BigOperators
open Finset
namespace LidskiiAux

lemma weighted_antitone_sum_le {m k : ℕ} (hk : k ≤ m)
    (a t : Fin m → ℝ) (ha : Antitone a)
    (ht0 : ∀ i, 0 ≤ t i) (ht1 : ∀ i, t i ≤ 1)
    (htsum : ∑ i, t i = k) :
    (∑ i : Fin m, t i * a i) ≤
      ∑ i ∈ Finset.univ.filter (fun i : Fin m => i.val < k), a i := by
  classical
  by_cases hkm : k < m
  · let c : ℝ := a ⟨k, hkm⟩
    let I : Finset (Fin m) := Finset.univ.filter (fun i : Fin m => i.val < k)
    let J : Finset (Fin m) := Finset.univ.filter (fun i : Fin m => k ≤ i.val)
    have hpart (f : Fin m → ℝ) :
        (∑ i : Fin m, f i) = (∑ i ∈ I, f i) + (∑ i ∈ J, f i) := by
      rw [← Finset.sum_union]
      · congr 1
        ext i
        simp [I,J]
        omega
      · -- disjoint
        apply Finset.disjoint_left.mpr
        intro x hxI hxJ
        have h1 : x.val < k := (Finset.mem_filter.mp hxI).2
        have h2 : k ≤ x.val := (Finset.mem_filter.mp hxJ).2
        omega
    have hIcard : (I.card : ℝ) = k := by
      have h : I.card = k := by
        -- fintype fin m count
        simpa [I, Nat.min_eq_right hk] using
          (@Fin.card_filter_val_lt m k)
      exact_mod_cast h
    have htbal : ∑ j ∈ J, t j = ∑ i ∈ I, (1 - t i) := by
      have := htsum
      rw [hpart t] at this
      -- I.card relation
      rw [Finset.sum_sub_distrib]
      simp only [Finset.sum_const_zero, Finset.sum_const, nsmul_eq_mul]
      rw [hIcard]
      linarith
    have hsub : (∑ i : Fin m, t i * a i) -
           (∑ i ∈ I, a i) ≤ 0 := by
      calc
        (∑ i : Fin m, t i * a i) - (∑ i ∈ I, a i) =
          (∑ j ∈ J, t j * (a j - c)) -
            (∑ i ∈ I, (1 - t i) * (a i - c)) := by
              rw [hpart (fun i => t i * a i)]
              have hJexp : (∑ j ∈ J, t j * (a j - c)) =
                    (∑ j ∈ J, t j * a j) - (∑ j ∈ J, t j) * c := by
                simp [mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]
              have hIexp : (∑ i ∈ I, (1 - t i) * (a i - c)) =
                    (∑ i ∈ I, a i) - (∑ i ∈ I, t i * a i) -
                         (∑ i ∈ I, (1 - t i)) * c := by
                have hI1 : (∑ i ∈ I, (1 - t i) * a i) =
                    (∑ i ∈ I, a i) - ∑ i ∈ I, t i * a i := by
                  simp [sub_mul, Finset.sum_sub_distrib]
                simp_rw [mul_sub]
                simp [Finset.sum_sub_distrib, Finset.sum_mul, hI1]
                simp_rw [sub_mul, one_mul]
                simp [Finset.sum_sub_distrib, Finset.sum_mul]
              rw [hJexp, hIexp]
              rw [htbal]
              ring
        _ ≤ 0 := by
          have hnegJ : ∑ j ∈ J, t j * (a j - c) ≤ 0 := by
            apply Finset.sum_nonpos
            intro j hj
            have hkj : k ≤ j.val := (Finset.mem_filter.mp hj).2
            have hac : a j ≤ c := by
              dsimp [c]
              apply ha
              exact (Fin.mk_le_mk.mpr hkj)
            exact mul_nonpos_of_nonneg_of_nonpos (ht0 _) (sub_nonpos.mpr hac)
          have hposI : 0 ≤ ∑ i ∈ I, (1 - t i) * (a i - c) := by
            apply Finset.sum_nonneg
            intro i hi
            have hik : i.val < k := (Finset.mem_filter.mp hi).2
            have hai : c ≤ a i := by
              dsimp [c]
              apply ha
              exact (Fin.mk_le_mk.mpr (Nat.le_of_lt hik))
            exact mul_nonneg (sub_nonneg.mpr (ht1 _)) (sub_nonneg.mpr hai)
          linarith
    dsimp [I] at hsub ⊢
    linarith

  · have hkeq : k = m := by omega
    subst k
    -- all entries t=1 since sum/card
    have htall (i : Fin m) : t i = 1 := by
      -- use sum equality + bounds
      by_contra hne
      have hlt : t i < 1 := lt_of_le_of_ne (ht1 i) hne
      -- show total < m
      have hsum_le : ∑ j : Fin m, t j ≤ ∑ j : Fin m, (1:ℝ) :=
        Finset.sum_le_sum (fun j hj => ht1 j)
      have hsum_lt : ∑ j : Fin m, t j < ∑ j : Fin m, (1:ℝ) := by
        exact (Finset.sum_lt_sum (s:= (Finset.univ : Finset (Fin m)))
          (fun j hj => ht1 j)
          (by exact ⟨i, Finset.mem_univ _, hlt⟩))
      -- simp conflict with htsum
      have hh : (∑ j : Fin m, t j) = (m:ℝ) := by exact_mod_cast htsum
      have hones : (∑ j : Fin m, (1:ℝ)) = (m:ℝ) := by simp
      linarith
    simp_rw [htall]
    simp

end LidskiiAux

-- END INLINED FILE: Mathlib/Support/lidskii_inequality_145b211497/ScalarWeighted.lean

-- BEGIN INLINED FILE: Mathlib/Support/lidskii_inequality_145b211497/KyFan.lean
open scoped BigOperators InnerProductSpace
open Finset
open LidskiiAux
namespace LidskiiAux

lemma kyfan_diag_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]
    {ι : Type*} [Fintype ι]
    {m : ℕ}
    (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric)
    (hm : Module.finrank ℂ E = m)
    (u : OrthonormalBasis ι ℂ E)
    (I : Finset ι) :
    (∑ i ∈ I, RCLike.re (inner ℂ (u i) (T (u i)))) ≤
      ∑ j ∈ Finset.univ.filter (fun j : Fin m => j.val < I.card),
        hT.eigenvalues hm j := by
  classical
  have hk : I.card ≤ m := by
    have hcard : Module.finrank ℂ E = Fintype.card ι :=
        Module.finrank_eq_card_basis u.toBasis
    have hle : I.card ≤ Fintype.card ι := Finset.card_le_univ _
    omega
  let b := hT.eigenvectorBasis hm
  let M : ι → Fin m → ℝ := fun i j => ‖inner ℂ (u i) (b j)‖ ^ 2
  let t : Fin m → ℝ := fun j => ∑ i ∈ I, M i j
  let a : Fin m → ℝ := hT.eigenvalues hm
  have hanti : Antitone a := hT.eigenvalues_antitone hm
  have t0 (j : Fin m): 0 ≤ t j := by
    dsimp [t, M]
    positivity
  have tle (j : Fin m): t j ≤ 1 := by
    have hh : t j ≤ ∑ i : ι, M i j := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ I) (fun _ _ _ => by dsimp [M]; positivity)
    simpa [M] using ((show t j ≤ ∑ i : ι, M i j from hh).trans_eq (overlap_col u b j))
  have tsum : (∑ j, t j) = (I.card : ℝ) := by
    -- interchange sums row
    change (∑ j : Fin m, ∑ i ∈ I, M i j) = _
    rw [Finset.sum_comm]
    calc
      (∑ i ∈ I, ∑ j : Fin m, M i j) = ∑ i ∈ I, (1:ℝ) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact overlap_row u b i
      _ = (I.card : ℝ) := by simp
  have hwt := weighted_antitone_sum_le hk a t hanti t0 tle tsum
  calc
    (∑ i ∈ I, RCLike.re (inner ℂ (u i) (T (u i)))) =
        ∑ j : Fin m, t j * a j := by
          -- expand the Rayleigh coefficients in the spectral basis
          simp_rw [diag_expansion T hT hm]
          change (∑ i ∈ I, ∑ j : Fin m, M i j * a j) = _
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro j hj
          simp [t, Finset.sum_mul]
    _ ≤ _ := hwt

end LidskiiAux

namespace LidskiiAux
/-!
Small Ky Fan maximum principles.  The version `kyfan_diag_le` above works with
an *entire* orthonormal basis and a subset of its indices.  Two useful points
about that statement are slightly easy to miss: its right hand side really is
the `k` largest eigenvalues (and not just an upper bound), and it applies just
as well to an orthonormal `k`-frame (one does not need to make up the other
vectors of the basis).  We record those facts here.  These lemmas contain no
compactness/existence argument: the maximum is attained by the spectral
orthonormal basis.  The frame version is obtained by extending an
orthonormal family to a basis; in particular it also applies to the frames
coming from subspaces.
-/

/-- The prefix of `Fin m` which has length `k` has card `k`, if `k ≤ m`. -/
lemma topFinset_card {m k : ℕ} (hk : k ≤ m) :
    (Finset.univ.filter (fun j : Fin m => j.val < k)).card = k := by
  classical
  simpa [Nat.min_eq_right hk] using (@Fin.card_filter_val_lt m k)

/-- The diagonal of a self-adjoint operator in its spectral orthonormal
basis is its eigenvalue.  This formulation only uses real parts, to match
`diag_expansion`/`kyfan_diag_le`. -/
lemma sum_castLE_prefix {m k : ℕ} (hk : k ≤ m)
    (F : Fin m → ℝ) (G : Fin k → ℝ)
    (hFG : ∀ i : Fin k, G i = F (Fin.castLE hk i)) :
    (∑ i : Fin k, G i) =
      ∑ j ∈ Finset.univ.filter (fun j : Fin m => j.val < k), F j := by
  classical
  -- The inverse on the prefix just keeps the same natural value.
  have h := Finset.sum_bij'
       (s := (Finset.univ : Finset (Fin k)))
       (t := Finset.univ.filter (fun j : Fin m => j.val < k))
       (f := G) (g := F)
       (fun i hi => Fin.castLE hk i)
       (fun j hj => (⟨j.val, (Finset.mem_filter.mp hj).2⟩ : Fin k))
       (by
          intro i hi
          apply Finset.mem_filter.mpr
          constructor
          · exact Finset.mem_univ _
          · exact i.isLt)
       (by intro j hj; exact Finset.mem_univ _)
       (by intro i hi; exact Fin.ext rfl)
       (by intro j hj; exact Fin.ext rfl)
       (by intro i hi; exact hFG i)
  simpa using h

/-- The useful frame form of the upper Ky Fan principle.  An orthonormal
`Fin k` family need not have been presented as part of a basis.  We extend it
to a `Fin m` basis (zero values outside the prefix are only placeholders for
the extension lemma) and apply `kyfan_diag_le`.

Stating this for `Fin k` loses no information about finite frames: a
reindexing gives the variant for any finite index type. -/
lemma kyfan_frame_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]
    {m k : ℕ}
    (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric)
    (hm : Module.finrank ℂ E = m)
    (v : Fin k → E) (hv : Orthonormal ℂ v)
    (hk : k ≤ m) :
    (∑ i : Fin k, RCLike.re (inner ℂ (v i) (T (v i)))) ≤
      ∑ j ∈ Finset.univ.filter (fun j : Fin m => j.val < k),
        hT.eigenvalues hm j := by
  classical
  let w : Fin m → E := fun i => if h : i.val < k then
      v ⟨i.val, h⟩ else 0
  let s : Set (Fin m) := {i | i.val < k}
  have hw : Orthonormal ℂ (s.restrict w) := by
    rw [orthonormal_iff_ite]
    intro i j
    have hi : (i : Fin m).val < k := i.property
    have hj : (j : Fin m).val < k := j.property
    simp only [Set.restrict, w, dif_pos hi, dif_pos hj]
    have hv' := (orthonormal_iff_ite.mp hv) (⟨(i : Fin m).val, hi⟩ : Fin k)
        (⟨(j : Fin m).val, hj⟩ : Fin k)
    by_cases h : i = j
    · subst j
      simpa using hv'
    · have h' : (⟨(i : Fin m).val, hi⟩ : Fin k) ≠
            ⟨(j : Fin m).val, hj⟩ := by
          intro e
          apply h
          apply Subtype.ext
          exact Fin.ext_iff.mpr (Fin.mk.inj_iff.mp e)
      simpa [h, h'] using hv'
  have hcard : Module.finrank ℂ E = Fintype.card (Fin m) := by
    simpa using hm
  obtain ⟨u, hu⟩ :=
    Orthonormal.exists_orthonormalBasis_extension_of_card_eq hcard hw
  let I : Finset (Fin m) := Finset.univ.filter (fun j : Fin m => j.val < k)
  have heqUw :
      (∑ j ∈ I, RCLike.re (inner ℂ (u j) (T (u j)))) =
      (∑ j ∈ I, RCLike.re (inner ℂ (w j) (T (w j)))) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : j.val < k := (Finset.mem_filter.mp hj).2
    have hjs : j ∈ s := by exact hj'
    rw [hu j hjs]
  have hsumvw :
      (∑ i : Fin k, RCLike.re (inner ℂ (v i) (T (v i)))) =
      (∑ j ∈ I, RCLike.re (inner ℂ (w j) (T (w j)))) := by
    have hfg : ∀ i : Fin k,
        RCLike.re (inner ℂ (v i) (T (v i))) =
        RCLike.re (inner ℂ (w (Fin.castLE hk i))
                             (T (w (Fin.castLE hk i)))) := by
      intro i
      have hi : (Fin.castLE hk i : Fin m).val < k := i.isLt
      have he : w (Fin.castLE hk i) = v i := by
        simp [w, hi]
      simp [he]
    exact sum_castLE_prefix hk
       (fun j : Fin m => RCLike.re (inner ℂ (w j) (T (w j))))
       (fun i : Fin k => RCLike.re (inner ℂ (v i) (T (v i)))) hfg
  have hle := kyfan_diag_le T hT hm u I
  have hIcard : I.card = k := by
    dsimp [I]
    exact topFinset_card hk
  calc
    (∑ i : Fin k, RCLike.re (inner ℂ (v i) (T (v i)))) =
        (∑ j ∈ I, RCLike.re (inner ℂ (u j) (T (u j)))) :=
          hsumvw.trans heqUw.symm
    _ ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin m => j.val < I.card),
          hT.eigenvalues hm j := hle
    _ = ∑ j ∈ Finset.univ.filter (fun j : Fin m => j.val < k),
          hT.eigenvalues hm j := by rw [hIcard]

end LidskiiAux

-- END INLINED FILE: Mathlib/Support/lidskii_inequality_145b211497/KyFan.lean

-- BEGIN INLINED FILE: Mathlib/Support/lidskii_inequality_145b211497/Flags.lean
open scoped InnerProductSpace BigOperators
open Matrix Finset Set
namespace LidskiiAux
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {m : ℕ}
noncomputable def topIdx (m r : ℕ) : Finset (Fin m) := Finset.univ.filter (fun j : Fin m => j.val < r)
noncomputable def topSpan (u : OrthonormalBasis (Fin m) ℂ E) (r : ℕ) : Submodule ℂ E := by
  classical
  exact Submodule.span ℂ (↑((topIdx m r).image (⇑u)) : Set E)
lemma finrank_topSpan (u : OrthonormalBasis (Fin m) ℂ E) (r : ℕ) :
  Module.finrank ℂ (topSpan u r) = min r m := by
  classical
  let b := OrthonormalBasis.span u.orthonormal (topIdx m r)
  have hb : Module.finrank ℂ (topSpan u r) = Fintype.card (topIdx m r) := by
    -- finrank_eq of basis b
    have h := Module.finrank_eq_card_basis b.toBasis
    -- b has index subtype topIdx, target submodule maybe defeq
    
    change Module.finrank ℂ (topSpan u r) = _
    --
    unfold topSpan
    -- try
    convert h using 1
  rw [hb]
  rw [Fintype.card_coe]
  simpa [topIdx, Nat.min_comm] using (@Fin.card_filter_val_lt m r)
end LidskiiAux
namespace LidskiiAux
open scoped ComplexConjugate
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {m : ℕ}
lemma mem_topSpan (u : OrthonormalBasis (Fin m) ℂ E) (r : ℕ) (j : Fin m)
    (hj : j.val < r) : u j ∈ topSpan u r := by
  classical
  -- make set member
  refine Submodule.subset_span ?_
  change u j ∈ (↑((topIdx m r).image (⇑u)) : Set E)
  exact Finset.mem_image.mpr ⟨j, (by simp [topIdx, hj]), rfl⟩

lemma out_orth (u : OrthonormalBasis (Fin m) ℂ E) (r : ℕ) (j : Fin m)
    (hj : r ≤ j.val) (x : E) (hx : x ∈ topSpan u r) : inner ℂ x (u j) = 0 := by
  classical
  have hle : topSpan u r ≤ (ℂ ∙ (u j))ᗮ := by
    -- span_le
    apply (Submodule.span_le).2
    intro y hy
    change y ∈ (↑((topIdx m r).image (⇑u)) : Set E) at hy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
    apply (Submodule.mem_orthogonal_singleton_iff_inner_left).2
    have hne : i ≠ j := by
      intro h; subst j
      have : i.val < r := (Finset.mem_filter.mp hi).2
      omega
    simpa [hne] using ((orthonormal_iff_ite.mp u.orthonormal) i j)
  have hmemb : x ∈ (ℂ ∙ (u j))ᗮ := hle hx
  exact (Submodule.mem_orthogonal_singleton_iff_inner_left).1 hmemb
end LidskiiAux
namespace LidskiiAux
open scoped ComplexConjugate
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]
variable {m : ℕ}
open LidskiiAux
lemma rayleigh_top_ge (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric)
    (hm : Module.finrank ℂ E = m) (q : Fin m)
    (x : E) (hx : x ∈ topSpan (hT.eigenvectorBasis hm) (q.val+1))
    (hxnorm : ‖x‖ = 1) :
    hT.eigenvalues hm q ≤
       RCLike.re (inner ℂ x (T x)) := by
  classical
  let b := hT.eigenvectorBasis hm
  let a : Fin m → ℝ := hT.eigenvalues hm
  let w : Fin m → ℝ := fun j => ‖inner ℂ x (b j)‖ ^ 2
  have hw_sum : (∑ j : Fin m, w j) = 1 := by
    dsimp [w, b]
    rw [(hT.eigenvectorBasis hm).sum_sq_norm_inner_left x]
    rw [hxnorm]
    norm_num
  have hterm (j : Fin m) : w j * a q ≤ w j * a j := by
    by_cases hj : j.val ≤ q.val
    · have ha : a q ≤ a j := by
        dsimp [a]
        exact hT.eigenvalues_antitone hm (Fin.mk_le_mk.mpr hj)
      exact mul_le_mul_of_nonneg_left ha (by dsimp [w]; positivity)
    · have hj' : q.val + 1 ≤ j.val := by omega
      have hz : inner ℂ x (b j) = 0 := by
        dsimp [b]
        exact out_orth (hT.eigenvectorBasis hm) (q.val+1) j hj' x hx
      have w0 : w j = 0 := by simp [w, hz]
      simp [w0]
  calc
    hT.eigenvalues hm q = ∑ j : Fin m, w j * a q := by
      rw [← Finset.sum_mul, hw_sum]
      simp [a]
    _ ≤ ∑ j : Fin m, w j * a j := Finset.sum_le_sum (fun j hj => hterm j)
    _ = RCLike.re (inner ℂ x (T x)) := by
      symm
      simpa [w, a, b] using LidskiiAux.diag_expansion T hT hm x
end LidskiiAux
namespace LidskiiAux
open scoped ComplexConjugate
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {m : ℕ}
noncomputable def botSpan (u : OrthonormalBasis (Fin m) ℂ E)
    (q : Fin m) : Submodule ℂ E := by
  classical
  exact Submodule.span ℂ (↑((Finset.Ici q).image (⇑u)) : Set E)
lemma finrank_botSpan (u : OrthonormalBasis (Fin m) ℂ E) (q : Fin m) :
  Module.finrank ℂ (botSpan u q) = m - q.val := by
  classical
  let b := OrthonormalBasis.span u.orthonormal (Finset.Ici q)
  have h := Module.finrank_eq_card_basis b.toBasis
  have hb : Module.finrank ℂ (botSpan u q) = Fintype.card (Finset.Ici q) := by
    change Module.finrank ℂ (botSpan u q) = _
    unfold botSpan
    convert h using 1
  rw [hb, Fintype.card_coe, Fin.card_Ici]

lemma mem_botSpan (u : OrthonormalBasis (Fin m) ℂ E) (q j : Fin m)
    (hj : q.val ≤ j.val) : u j ∈ botSpan u q := by
  classical
  refine Submodule.subset_span ?_
  exact Finset.mem_image.mpr ⟨j, (by simp [Finset.mem_Ici, Fin.le_iff_val_le_val, hj]), rfl⟩
lemma out_bot_orth (u : OrthonormalBasis (Fin m) ℂ E) (q j : Fin m)
    (hj : j.val < q.val) (x : E) (hx : x ∈ botSpan u q) : inner ℂ x (u j)=0 := by
  classical
  have hle : botSpan u q ≤ (ℂ ∙ (u j))ᗮ := by
    apply (Submodule.span_le).2
    intro y hy
    change y ∈ (↑((Finset.Ici q).image (⇑u)) : Set E) at hy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
    apply (Submodule.mem_orthogonal_singleton_iff_inner_left).2
    have hne : i ≠ j := by
      intro h; subst j
      have hqi : q ≤ i := Finset.mem_Ici.mp hi
      have hval : q.val ≤ i.val := Fin.mk_le_mk.mp hqi
      omega
    simpa [hne] using ((orthonormal_iff_ite.mp u.orthonormal) i j)
  exact (Submodule.mem_orthogonal_singleton_iff_inner_left).1 (hle hx)

open LidskiiAux
variable [FiniteDimensional ℂ E]
lemma rayleigh_bot_le (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric)
    (hm : Module.finrank ℂ E = m) (q : Fin m)
    (x : E) (hx : x ∈ botSpan (hT.eigenvectorBasis hm) q)
    (hxnorm : ‖x‖ = 1) :
    RCLike.re (inner ℂ x (T x)) ≤ hT.eigenvalues hm q := by
  classical
  let b := hT.eigenvectorBasis hm
  let a : Fin m → ℝ := hT.eigenvalues hm
  let w : Fin m → ℝ := fun j => ‖inner ℂ x (b j)‖ ^ 2
  have hw_sum : (∑ j : Fin m, w j) = 1 := by
    dsimp [w, b]
    rw [(hT.eigenvectorBasis hm).sum_sq_norm_inner_left x]
    rw [hxnorm]
    norm_num
  have hterm (j : Fin m) : w j * a j ≤ w j * a q := by
    by_cases hj : q.val ≤ j.val
    · have ha : a j ≤ a q := by
        dsimp [a]
        exact hT.eigenvalues_antitone hm (Fin.mk_le_mk.mpr hj)
      exact mul_le_mul_of_nonneg_left ha (by dsimp [w]; positivity)
    · have hj' : j.val < q.val := by omega
      have hz : inner ℂ x (b j) = 0 := by
        dsimp [b]
        exact out_bot_orth (hT.eigenvectorBasis hm) q j hj' x hx
      have w0 : w j = 0 := by simp [w, hz]
      simp [w0]
  calc
    RCLike.re (inner ℂ x (T x)) = ∑ j : Fin m, w j * a j := by
        simpa [w, a, b] using LidskiiAux.diag_expansion T hT hm x
    _ ≤ ∑ j : Fin m, w j * a q := Finset.sum_le_sum (fun j hj => hterm j)
    _ = hT.eigenvalues hm q := by
        rw [← Finset.sum_mul, hw_sum]
        simp [a]
end LidskiiAux
namespace LidskiiAux
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
 [FiniteDimensional ℂ E]
lemma inf_has_unit (U V : Submodule ℂ E)
    (hgt : Module.finrank ℂ E < Module.finrank ℂ U + Module.finrank ℂ V) :
    ∃ x : E, x ∈ U ∧ x ∈ V ∧ ‖x‖ = 1 := by
  -- dimension inf positive
  have hleTop : Module.finrank ℂ (U ⊔ V : Submodule ℂ E) ≤ Module.finrank ℂ E :=
    Submodule.finrank_le _
  have hEq := Submodule.finrank_sup_add_finrank_inf_eq U V
  have hpos : 0 < Module.finrank ℂ (U ⊓ V : Submodule ℂ E) := by
    omega
  have hne : (U ⊓ V : Submodule ℂ E) ≠ ⊥ :=
    Submodule.nontrivial_iff_ne_bot.mp (Module.finrank_pos_iff.mp hpos)
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hynorm : ‖y‖ ≠ 0 := (norm_ne_zero_iff.mpr hy0)
  let x : E := ((‖y‖ : ℂ)⁻¹) • y
  have hx : x ∈ U ⊓ V := (U ⊓ V).smul_mem ((‖y‖ : ℂ)⁻¹) hy
  refine ⟨x, hx.1, hx.2, ?_⟩
  dsimp [x]
  rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg y)]
  -- now inverse real?
  change ((‖y‖)⁻¹) * ‖y‖ = 1
  exact inv_mul_cancel₀ hynorm
end LidskiiAux
namespace LidskiiAux
open scoped InnerProductSpace BigOperators
open Matrix LidskiiAux
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
 [FiniteDimensional ℂ E]
variable {m : ℕ}
lemma sub_one_selected
    (T S : E →ₗ[ℂ] E) (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    (hm : Module.finrank ℂ E = m) (q : Fin m) :
    hS.eigenvalues hm q - hT.eigenvalues hm q ≤
      (hS.sub hT).eigenvalues hm ⟨0, Nat.zero_lt_of_lt q.isLt⟩ := by
  classical
  let bS := hS.eigenvectorBasis hm
  let bT := hT.eigenvectorBasis hm
  have hftop : Module.finrank ℂ (topSpan bS (q.val+1)) = q.val+1 := by
    rw [finrank_topSpan]
    exact min_eq_left (by omega)
  have hfbot : Module.finrank ℂ (botSpan bT q) = m - q.val := finrank_botSpan _ _
  have hgt : Module.finrank ℂ E <
      Module.finrank ℂ (topSpan bS (q.val+1)) + Module.finrank ℂ (botSpan bT q) := by
    rw [hm, hftop, hfbot]
    omega
  obtain ⟨x, hxS, hxT, hxnorm⟩ :=
    inf_has_unit (topSpan bS (q.val+1)) (botSpan bT q) hgt
  have hge : hS.eigenvalues hm q ≤ RCLike.re (inner ℂ x (S x)) := by
    exact rayleigh_top_ge S hS hm q x hxS hxnorm
  have hle : RCLike.re (inner ℂ x (T x)) ≤ hT.eigenvalues hm q := by
    exact rayleigh_bot_le T hT hm q x hxT hxnorm
  have hk : 1 ≤ m := Nat.succ_le_iff.mpr (Nat.zero_lt_of_lt q.isLt)
  let v : Fin 1 → E := fun _ => x
  have hv : Orthonormal ℂ v := by
    rw [orthonormal_iff_ite]
    intro i j
    have hi : i = 0 := Fin.eq_zero _
    have hj : j = 0 := Fin.eq_zero _
    subst i; subst j
    simp [v, inner_self_eq_norm_sq_to_K, hxnorm]
  have hc := LidskiiAux.kyfan_frame_le (S-T) (hS.sub hT) hm v hv hk
  rw [Fin.sum_univ_one] at hc
  have hcdiag : RCLike.re (inner ℂ x ((S-T) x)) ≤
      (hS.sub hT).eigenvalues hm ⟨0, Nat.zero_lt_of_lt q.isLt⟩ := by
    have hpref :
      (∑ j ∈ Finset.univ.filter (fun j : Fin m => j.val < 1),
        (hS.sub hT).eigenvalues hm j) =
        (hS.sub hT).eigenvalues hm ⟨0, Nat.zero_lt_of_lt q.isLt⟩ := by
      have hcast := LidskiiAux.sum_castLE_prefix hk
        (fun j : Fin m => (hS.sub hT).eigenvalues hm j)
        (fun i : Fin 1 => (hS.sub hT).eigenvalues hm (Fin.castLE hk i))
        (by intro; rfl)
      rw [Fin.sum_univ_one] at hcast
      -- castLE 0
      calc
        _ = (hS.sub hT).eigenvalues hm (Fin.castLE hk (0 : Fin 1)) := hcast.symm
        _ = _ := by congr 2
    rw [hpref] at hc
    simpa [v] using hc
  have hdiag : RCLike.re (inner ℂ x ((S-T) x)) =
        RCLike.re (inner ℂ x (S x)) - RCLike.re (inner ℂ x (T x)) := by
    simp [LinearMap.sub_apply, map_sub]
  rw [hdiag] at hcdiag
  linarith
end LidskiiAux

namespace LidskiiAux
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {m : ℕ}
/-- Upper spans form an honest flag. -/
lemma topSpan_mono (u : OrthonormalBasis (Fin m) ℂ E)
    {r s : ℕ} (hrs : r ≤ s) : topSpan u r ≤ topSpan u s := by
  classical
  apply (Submodule.span_le).2
  intro y hy
  change y ∈ (↑((topIdx m r).image (⇑u)) : Set E) at hy
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
  apply mem_topSpan u s i
  have hr : i.val < r := (Finset.mem_filter.mp hi).2
  omega
/-- The opposite spans reverse their lower cutoff. -/
lemma botSpan_anti (u : OrthonormalBasis (Fin m) ℂ E)
    {i j : Fin m} (hij : i ≤ j) : botSpan u j ≤ botSpan u i := by
  classical
  apply (Submodule.span_le).2
  intro y hy
  change y ∈ (↑((Finset.Ici j).image (⇑u)) : Set E) at hy
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hy
  apply mem_botSpan u i q
  have hval : j.val ≤ q.val := Fin.mk_le_mk.mp (Finset.mem_Ici.mp hq)
  have hval' : i.val ≤ j.val := Fin.mk_le_mk.mp hij
  omega

/-- Repeated intersection still leaves a new direction when a subspace has
finrank larger than the old frame. This elementary dimension step is useful
in flag inductions; it avoids any choice of bases for the intersection. -/
lemma exists_unit_mem_of_finrank_gt_frame
    [FiniteDimensional ℂ E]
    (U : Submodule ℂ E) {r : ℕ} (v : Fin r → E) (hv : Orthonormal ℂ v)
    (hU : r < Module.finrank ℂ U) :
    ∃ x : E, x ∈ U ∧ (∀ i, inner ℂ (v i) x = 0) ∧ ‖x‖ = 1 := by
  classical
  let V : Submodule ℂ E := Submodule.span ℂ (Set.range v)
  have hfv : Module.finrank ℂ V = r := by
    change Module.finrank ℂ (Submodule.span ℂ (Set.range v)) = _
    simpa using (finrank_span_eq_card hv.linearIndependent)
  have htot : Module.finrank ℂ (Vᗮ) + Module.finrank ℂ V = Module.finrank ℂ E := by
    have h := Submodule.finrank_add_finrank_orthogonal V
    omega
  have hleU : Module.finrank ℂ U ≤ Module.finrank ℂ E := Submodule.finrank_le _
  have hgt : Module.finrank ℂ E <
      Module.finrank ℂ U + Module.finrank ℂ (Vᗮ) := by omega
  obtain ⟨x, hxU, hxO, hnorm⟩ := inf_has_unit U (Vᗮ) hgt
  refine ⟨x, hxU, ?_, hnorm⟩
  intro i
  apply (Submodule.mem_orthogonal V x).1 hxO
  apply Submodule.subset_span
  exact ⟨i, rfl⟩
end LidskiiAux

-- END INLINED FILE: Mathlib/Support/lidskii_inequality_145b211497/Flags.lean

-- BEGIN INLINED FILE: Mathlib/Support/lidskii_inequality_145b211497/FlagReduction.lean
open scoped InnerProductSpace BigOperators
open Finset Matrix
namespace LidskiiAux
/-- On the upper spectral flag of S, *every* admissible orthonormal
k-frame has S-trace at least the sum of the indicated eigenvalues.
This is the easy half of the flag (Wielandt) principle. -/
lemma flag_trace_ge_selected
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
      [FiniteDimensional ℂ E]
    {m k : ℕ}
    (S : E →ₗ[ℂ] E) (hS : S.IsSymmetric)
    (hm : Module.finrank ℂ E = m)
    (idx : Fin k → Fin m)
    (v : Fin k → E) (hv : Orthonormal ℂ v)
    (hmem : ∀ r, v r ∈ topSpan (hS.eigenvectorBasis hm) ((idx r).val+1)) :
    (∑ r : Fin k, hS.eigenvalues hm (idx r)) ≤
       ∑ r : Fin k, RCLike.re (inner ℂ (v r) (S (v r))) := by
  classical
  apply Finset.sum_le_sum
  intro r hr
  have hnorm : ‖v r‖ = 1 := hv.norm_eq_one r
  exact rayleigh_top_ge S hS hm (idx r) (v r) (hmem r) hnorm

/-- Conditional flag form of the selected Lidskii inequality.  This
isolates exactly the nontrivial Wielandt minimization: construction of
one frame in the S spectral flag whose T trace is small.  Once such a
frame is supplied, elementary flag estimates and Ky--Fan on S-T finish. -/
lemma selected_sub_le_of_flag
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
      [FiniteDimensional ℂ E]
    {m k : ℕ}
    (T S : E →ₗ[ℂ] E) (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    (hm : Module.finrank ℂ E = m) (hk : k ≤ m)
    (idx : Fin k → Fin m)
    (hframe : ∃ v : Fin k → E, Orthonormal ℂ v ∧
       (∀ r, v r ∈ topSpan (hS.eigenvectorBasis hm) ((idx r).val+1)) ∧
       (∑ r : Fin k, RCLike.re (inner ℂ (v r) (T (v r)))) ≤
          ∑ r : Fin k, hT.eigenvalues hm (idx r)) :
    (∑ r : Fin k, (hS.eigenvalues hm (idx r) - hT.eigenvalues hm (idx r))) ≤
       ∑ j ∈ Finset.univ.filter (fun j : Fin m => j.val < k),
             (hS.sub hT).eigenvalues hm j := by
  classical
  obtain ⟨v, hv, hvS, hvT⟩ := hframe
  have hsle := flag_trace_ge_selected S hS hm idx v hv hvS
  have hC := kyfan_frame_le (S-T) (hS.sub hT) hm v hv hk
  have hdiag :
      (∑ r : Fin k, RCLike.re (inner ℂ (v r) ((S-T) (v r)))) =
       (∑ r : Fin k, RCLike.re (inner ℂ (v r) (S (v r)))) -
       (∑ r : Fin k, RCLike.re (inner ℂ (v r) (T (v r)))) := by
         simp [LinearMap.sub_apply, map_sub, Finset.sum_sub_distrib]
  rw [hdiag] at hC
  have hsum :
      (∑ r : Fin k, (hS.eigenvalues hm (idx r) - hT.eigenvalues hm (idx r))) =
        (∑ r : Fin k, hS.eigenvalues hm (idx r)) -
        ∑ r : Fin k, hT.eigenvalues hm (idx r) := by
          rw [Finset.sum_sub_distrib]
  rw [hsum]
  linarith

end LidskiiAux

-- END INLINED FILE: Mathlib/Support/lidskii_inequality_145b211497/FlagReduction.lean

-- BEGIN INLINED FILE: Mathlib/Support/lidskii_inequality_145b211497/GapIndex.lean
open scoped BigOperators
open Finset Set
namespace LidskiiAux
/-- Put an injected enumeration of selected indices into increasing order.  We keep
 the equality of the two finite images: the selected problem only involves sums
 over that image, whereas jumps are easiest to state on a monotone enumeration. -/
lemma sorted_selected_range {m k : ℕ} (idx : Fin k → Fin m)
    (hi : Function.Injective idx) :
    ∃ f : Fin k ↪o Fin m,
      (Finset.univ.image idx) = Finset.univ.image (fun r : Fin k => f r) := by
  classical
  let s : Finset (Fin m) := Finset.univ.image idx
  have hs : s.card = k := by
    dsimp [s]
    simpa using (Finset.card_image_of_injective
      (Finset.univ : Finset (Fin k)) hi)
  let f : Fin k ↪o Fin m := s.orderEmbOfFin hs
  refine ⟨f, ?_⟩
  -- `orderEmbOfFin` enumerates all of `s`
  ext j
  constructor
  · intro hj
    have hj' : j ∈ s := hj
    let x : s := ⟨j, hj'⟩
    let r : Fin k := (s.orderIsoOfFin hs).symm x
    have hr : r ∈ (Finset.univ : Finset (Fin k)) := Finset.mem_univ _
    have hfr : (f r : Fin m) = j := by
      change ((s.orderEmbOfFin hs) r : Fin m) = j
      -- both are the underlying value of the order-isomorphism
      change ((s.orderIsoOfFin hs r : s) : Fin m) = j
      have hx : s.orderIsoOfFin hs r = x :=
        (s.orderIsoOfFin hs).apply_symm_apply x
      simpa [x] using congrArg (fun y : s => (y : Fin m)) hx
    exact Finset.mem_image.mpr ⟨r, hr, hfr⟩
  · intro hj
    obtain ⟨r, -, rfl⟩ := Finset.mem_image.mp hj
    change (f r : Fin m) ∈ s
    change ((s.orderEmbOfFin hs) r : Fin m) ∈ s
    exact (s.orderIsoOfFin hs r).property

end LidskiiAux

-- END INLINED FILE: Mathlib/Support/lidskii_inequality_145b211497/GapIndex.lean

-- BEGIN INLINED FILE: Mathlib/Support/lidskii_inequality_145b211497/FlagSorted.lean
open scoped InnerProductSpace BigOperators
open Finset Set Matrix
namespace LidskiiAux

/-- If two injective lists enumerate the same finite subset, they differ by a
permutation of the list.  The useful content here is the *pointwise* equality,
not just equality of the two ranges: it lets one carry the flags, whose radii
depend on the column, along the very same permutation. -/
lemma equiv_of_fin_image_eq {m k : ℕ}
    (a b : Fin k → Fin m) (ha : Function.Injective a)
    (hb : Function.Injective b)
    (hab : Finset.univ.image a = Finset.univ.image b) :
    ∃ e : Fin k ≃ Fin k, ∀ r : Fin k, a r = b (e r) := by
  classical
  have hpre (r : Fin k) : ∃ s : Fin k, b s = a r := by
    have hr : a r ∈ Finset.univ.image a :=
      Finset.mem_image.mpr ⟨r, Finset.mem_univ _, rfl⟩
    rw [hab] at hr
    obtain ⟨s, -, hs⟩ := Finset.mem_image.mp hr
    exact ⟨s, hs⟩
  let f : Fin k → Fin k := fun r => Classical.choose (hpre r)
  have hfval (r : Fin k) : b (f r) = a r :=
    Classical.choose_spec (hpre r)
  have hf : Function.Injective f := by
    intro r s hrs
    apply ha
    have h := congrArg b hrs
    -- both chosen preimages have their prescribed values
    rw [hfval r, hfval s] at h
    exact h
  let e : Fin k ≃ Fin k := Equiv.ofBijective f
    ((Fintype.bijective_iff_injective_and_card f).2 ⟨hf, rfl⟩)
  refine ⟨e, ?_⟩
  intro r
  -- `ofBijective` has the same forward map
  change a r = b (f r)
  exact (hfval r).symm

/-- Reindexing a numerical sum along equal injective images.  This avoids a
second sorting argument each time the selected perturbation sum is written;
all three occurrences (the S trace, the T trace and their difference) are
moved by the single permutation supplied above. -/
lemma sum_comp_eq_of_image {m k : ℕ}
    (a b : Fin k → Fin m) (ha : Function.Injective a)
    (hb : Function.Injective b)
    (hab : Finset.univ.image a = Finset.univ.image b)
    (z : Fin m → ℝ) :
    (∑ r : Fin k, z (a r)) = ∑ r : Fin k, z (b r) := by
  classical
  obtain ⟨e, he⟩ := equiv_of_fin_image_eq a b ha hb hab
  calc
    (∑ r : Fin k, z (a r)) = ∑ r : Fin k, z (b (e r)) := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [he r]
    _ = ∑ r : Fin k, z (b r) := Equiv.sum_comp e (fun r : Fin k => z (b r))

/-- The entire Wielandt flag target, not just its image, is invariant under
reordering the selected positions.  This is a useful sharpening of the
``their images agree'' reduction: a flag for the *increasing* enumeration
really gives a flag for the enumeration in which a large scalar coordinate
was chosen.

No extremal argument is hidden here.  Relabel the columns by the permutation
of their common image.  Orthonormality and both traces use that very
permutation; the flag condition uses the pointwise equality of the indices. -/
lemma flag_target_reindex
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
      [FiniteDimensional ℂ E]
    {m k : ℕ}
    (u : OrthonormalBasis (Fin m) ℂ E)
    (T : E →ₗ[ℂ] E) (lam : Fin m → ℝ)
    (a b : Fin k → Fin m) (ha : Function.Injective a)
    (hb : Function.Injective b)
    (hab : Finset.univ.image a = Finset.univ.image b)
    (hframe : ∃ w : Fin k → E, Orthonormal ℂ w ∧
       (∀ r, w r ∈ topSpan u ((b r).val+1)) ∧
       (∑ r : Fin k, RCLike.re (inner ℂ (w r) (T (w r)))) ≤
          ∑ r : Fin k, lam (b r)) :
    ∃ v : Fin k → E, Orthonormal ℂ v ∧
       (∀ r, v r ∈ topSpan u ((a r).val+1)) ∧
       (∑ r : Fin k, RCLike.re (inner ℂ (v r) (T (v r)))) ≤
          ∑ r : Fin k, lam (a r) := by
  classical
  obtain ⟨e, he⟩ := equiv_of_fin_image_eq a b ha hb hab
  obtain ⟨w, hw, hwf, hwT⟩ := hframe
  let v : Fin k → E := fun r => w (e r)
  have hv : Orthonormal ℂ v := by
    rw [orthonormal_iff_ite]
    intro i j
    have h0 := (orthonormal_iff_ite.mp hw) (e i) (e j)
    by_cases h : i = j
    · subst j
      simpa [v] using h0
    · have h' : e i ≠ e j := by intro hh; exact h (e.injective hh)
      simpa [v, h, h'] using h0
  have hvf : ∀ r, v r ∈ topSpan u ((a r).val+1) := by
    intro r
    have h0 := hwf (e r)
    have hval : (a r).val = (b (e r)).val :=
      congrArg (fun z : Fin m => z.val) (he r)
    simpa [v, hval] using h0
  refine ⟨v, hv, hvf, ?_⟩
  have hl : (∑ r : Fin k,
       RCLike.re (inner ℂ (v r) (T (v r)))) =
        ∑ r : Fin k, RCLike.re (inner ℂ (w r) (T (w r))) := by
    exact Equiv.sum_comp e
      (fun r : Fin k => RCLike.re (inner ℂ (w r) (T (w r))))
  have hr : (∑ r : Fin k, lam (a r)) =
        ∑ r : Fin k, lam (b r) :=
    sum_comp_eq_of_image a b ha hb hab lam
  rw [hl, hr]
  exact hwT

/-- In particular one may restrict the still-unproved flag problem to
*increasing* lists.  `sorted_selected_range` constructs their increasing
order embedding.  This is the useful input shape for a cut induction: free
slices are now compared by the natural order on `Fin`, not by a permutation
of the original subset. -/
lemma flag_target_of_all_orderEmb
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
      [FiniteDimensional ℂ E]
    {m k : ℕ}
    (u : OrthonormalBasis (Fin m) ℂ E)
    (T : E →ₗ[ℂ] E) (lam : Fin m → ℝ)
    (H : ∀ f : Fin k ↪o Fin m,
       ∃ w : Fin k → E, Orthonormal ℂ w ∧
          (∀ r, w r ∈ topSpan u ((f r).val+1)) ∧
          (∑ r : Fin k, RCLike.re (inner ℂ (w r) (T (w r)))) ≤
             ∑ r : Fin k, lam (f r))
    (a : Fin k → Fin m) (ha : Function.Injective a) :
    ∃ v : Fin k → E, Orthonormal ℂ v ∧
       (∀ r, v r ∈ topSpan u ((a r).val+1)) ∧
       (∑ r : Fin k, RCLike.re (inner ℂ (v r) (T (v r)))) ≤
          ∑ r : Fin k, lam (a r) := by
  classical
  obtain ⟨f, hf⟩ := sorted_selected_range a ha
  exact flag_target_reindex u T lam a (fun r : Fin k => f r)
    ha f.injective hf (H f)


/-- Crude but important size bounds for an increasing selected flag.  They are
false for a merely injected enumeration.  There are still `k-1-r` strictly
later entries above column `r`; hence its cut cannot lie above `m-k+r`.
Keeping the statement with an addition avoids any truncated subtraction in
the slice dimension counts. -/
lemma orderEmb_val_room {m k : ℕ} (f : Fin k ↪o Fin m) (r : Fin k) :
    r.val ≤ (f r).val ∧ (f r).val + (k-1-r.val) < m := by
  -- successive entries of a strict embedding of naturals gain at least one
  have step (t : ℕ) (ht : t+1 < k) :
      (f (⟨t, by omega⟩ : Fin k)).val + 1 ≤
        (f (⟨t+1, ht⟩ : Fin k)).val := by
    have hlt : (⟨t, by omega⟩ : Fin k) < ⟨t+1, ht⟩ :=
      Fin.mk_lt_mk.mpr (by omega)
    have hh := f.strictMono hlt
    exact Nat.succ_le_of_lt (Fin.mk_lt_mk.mp hh)
  have lower : ∀ t : ℕ, ∀ ht : t < k,
      t ≤ (f (⟨t, ht⟩ : Fin k)).val := by
    intro t
    induction t with
    | zero =>
        intro ht; exact Nat.zero_le _
    | succ t ih =>
        intro ht
        have ht0 : t < k := by omega
        have hprev := ih ht0
        have hnext := step t (by omega)
        omega
  constructor
  · exact lower r.val r.isLt
  · -- moving `s` steps above `r` gains at least `s`; use the last entry
    have climb : ∀ s : ℕ, ∀ hs : r.val + s < k,
        (f r).val + s ≤
          (f (⟨r.val+s, hs⟩ : Fin k)).val := by
      intro s
      induction s with
      | zero =>
          intro hs
          simpa using (le_refl (f r).val)
      | succ s ih =>
          intro hs
          have hs0 : r.val + s < k := by omega
          have h0 := ih hs0
          have h1 := step (r.val+s) (by omega)
          have heq :
              (⟨r.val+s+1, by omega⟩ : Fin k) =
                (⟨r.val+(s+1), hs⟩ : Fin k) := by
            apply Fin.ext
            simp
            omega
          rw [heq] at h1
          omega
    have vlast :=
      (f (⟨k-1, by have := r.isLt; omega⟩ : Fin k)).isLt
    have hc := climb (k-1-r.val) (by have := r.isLt; omega)
    -- the endpoint in `hc` is definitionally `r+(k-1-r)=k-1`
    have hend : (f r).val + (k-1-r.val) ≤
         (f (⟨k-1, by have := r.isLt; omega⟩ : Fin k)).val := by
      convert hc using 1 <;> apply congrArg (fun z : Fin k =>
        (f z).val) ?_ <;> try { apply Fin.ext; simp; omega }
    omega

end LidskiiAux

-- END INLINED FILE: Mathlib/Support/lidskii_inequality_145b211497/FlagSorted.lean

-- BEGIN INLINED FILE: Mathlib/Support/lidskii_inequality_145b211497/FlagBuild.lean
open scoped InnerProductSpace BigOperators ComplexConjugate
open Finset Set Matrix
namespace LidskiiAux
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]
/-- Finite-dimensional nested subspaces of sizes `r+1` contain a triangular
orthonormal frame.  This little flag-construction does not use any spectral
facts: at the last step intersect the last subspace with the orthogonal of
the already chosen columns.  Keeping the index as a natural number makes
successive restriction along `Fin.castSucc` painless.

It is useful in the flag-minimum argument whenever one has produced a
new invariant subspace of a prescribed dimension; there is no compactness
or extremum implicit in this lemma. -/
lemma exists_orthonormal_mem_flag
    (U : ℕ → Submodule ℂ E) (hmono : Monotone U) :
    ∀ k : ℕ, (∀ r : Fin k, r.val+1 ≤ Module.finrank ℂ (U r.val)) →
      ∃ v : Fin k → E, Orthonormal ℂ v ∧ (∀ r, v r ∈ U r.val) := by
  classical
  intro k
  induction k with
  | zero =>
      intro hk
      let v : Fin 0 → E := Fin.elim0
      refine ⟨v, ?_, ?_⟩
      · rw [orthonormal_iff_ite]
        intro i
        exact Fin.elim0 i
      · intro r
        exact Fin.elim0 r
  | succ k ih =>
      intro hk
      have hpre : ∀ r : Fin k, r.val+1 ≤ Module.finrank ℂ (U r.val) := by
        intro r
        have hx := hk (Fin.castSucc r)
        change r.val + 1 ≤ Module.finrank ℂ (U r.val) at hx
        exact hx
      obtain ⟨v, hv, hvU⟩ := ih hpre
      let V : Submodule ℂ E := Submodule.span ℂ (Set.range v)
      have hV : Module.finrank ℂ V = k := by
        change Module.finrank ℂ (Submodule.span ℂ (Set.range v)) = _
        simpa using (finrank_span_eq_card hv.linearIndependent)
      have horth := Submodule.finrank_add_finrank_orthogonal V
      have hlastdim : k + 1 ≤ Module.finrank ℂ (U k) := by
        have hx := hk (Fin.last k)
        change k + 1 ≤ Module.finrank ℂ (U k) at hx
        exact hx
      have hgt : Module.finrank ℂ E <
          Module.finrank ℂ (U k) + Module.finrank ℂ (Vᗮ) := by
        omega
      obtain ⟨y, hyU, hyV, hynorm⟩ := inf_has_unit (U k) (Vᗮ) hgt
      have hyorth (r : Fin k) : inner ℂ y (v r) = 0 := by
        have hr : v r ∈ V :=
          Submodule.subset_span (Set.mem_range_self r)
        exact (V.mem_orthogonal' y).mp hyV _ hr
      let w : Fin (k+1) → E := Fin.lastCases y (fun r : Fin k => v r)
      have hwlast : w (Fin.last k) = y := by simp [w]
      have hwcast (r : Fin k) : w (Fin.castSucc r) = v r := by
        simp [w]
      have hw : Orthonormal ℂ w := by
        rw [orthonormal_iff_ite]
        intro a b
        refine Fin.lastCases ?_ (fun a' => ?_) a
        · refine Fin.lastCases ?_ (fun b' => ?_) b
          · -- last,last
            simp [w, inner_self_eq_norm_sq_to_K, hynorm]
          · -- last,old
            have hne : (Fin.last k : Fin (k+1)) ≠ Fin.castSucc b' :=
              Ne.symm (Fin.castSucc_ne_last b')
            simp [w, hne, hyorth b']
        · refine Fin.lastCases ?_ (fun b' => ?_) b
          · -- old,last; use conjugate symmetry of the earlier zero
            have hz : inner ℂ (v a') y = 0 := by
              calc
                inner ℂ (v a') y =
                    (starRingEnd ℂ) (inner ℂ y (v a')) :=
                      (inner_conj_symm (𝕜:=ℂ) (v a') y).symm
                _ = 0 := by rw [hyorth a']; simp
            have hne : (Fin.castSucc a' : Fin (k+1)) ≠ Fin.last k :=
              Fin.castSucc_ne_last a'
            simp [w, hne, hz]
          · have hv' := (orthonormal_iff_ite.mp hv) a' b'
            -- `castSucc` is injective
            by_cases h : a' = b'
            · subst b'
              simpa [w] using hv'
            · have h' : (Fin.castSucc a' : Fin (k+1)) ≠ Fin.castSucc b' := by
                intro hh
                exact h (Fin.castSucc_inj.mp hh)
              simpa [w, h, h'] using hv'
      have hwU : ∀ r : Fin (k+1), w r ∈ U r.val := by
        intro r
        refine Fin.lastCases ?_ (fun r' => ?_) r
        · simpa [w] using hyU
        · simpa [w] using hvU r'
      exact ⟨w, hw, hwU⟩
end LidskiiAux

-- END INLINED FILE: Mathlib/Support/lidskii_inequality_145b211497/FlagBuild.lean

-- BEGIN INLINED FILE: Mathlib/Support/lidskii_inequality_145b211497/TailMass.lean
open scoped BigOperators InnerProductSpace
open Finset Set
namespace LidskiiAux
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

/-- Elementary bridge from a column echelon form in the second basis to the
prefix-mass formulation. This is useful at an intersection-of-flags step:
only the *number* of columns which have left the orthogonal tail is
important, not their individual Rayleigh quotients. No invariance of the
operator is used here. -/
lemma prefix_overlap_of_column_tails {m k : ℕ}
    (u : OrthonormalBasis (Fin m) ℂ E)
    (v : Fin k → E) (hv : Orthonormal ℂ v)
    (I : Finset (Fin m)) (b : Fin k → ℕ)
    (hz : ∀ r : Fin k, ∀ j : Fin m, j.val < b r →
       inner ℂ (v r) (u j) = 0)
    (hcard : ∀ l : ℕ, l ≤ m →
       ((Finset.univ.filter (fun r : Fin k => b r < l)).card : ℝ) ≤
        ∑ j ∈ Finset.univ.filter (fun j : Fin m => j.val < l),
          (if j ∈ I then (1:ℝ) else 0)) :
    ∀ l : ℕ, l ≤ m →
       (∑ j ∈ Finset.univ.filter (fun j : Fin m => j.val < l),
          ∑ r : Fin k, ‖inner ℂ (v r) (u j)‖ ^ 2) ≤
        ∑ j ∈ Finset.univ.filter (fun j : Fin m => j.val < l),
          (if j ∈ I then (1:ℝ) else 0) := by
  classical
  intro l hl
  let J : Finset (Fin m) := Finset.univ.filter (fun j : Fin m => j.val < l)
  let R : Finset (Fin k) := Finset.univ.filter (fun r : Fin k => b r < l)
  let c : Fin k → Fin m → ℝ := fun r j => ‖inner ℂ (v r) (u j)‖ ^ 2
  have hzero {r : Fin k} (hr : r ∉ R) :
      (∑ j ∈ J, c r j) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hlj : j.val < l := (Finset.mem_filter.mp hj).2
    have hbr : l ≤ b r := by
      by_contra hh
      have hlt : b r < l := by omega
      exact hr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩)
    have hjb : j.val < b r := lt_of_lt_of_le hlj hbr
    simp [c, hz r j hjb]
  have hpart : (∑ r : Fin k, ∑ j ∈ J, c r j) =
       ∑ r ∈ R, ∑ j ∈ J, c r j := by
    apply (Finset.sum_subset (s₁ := R) (s₂ := (Finset.univ : Finset (Fin k)))
       (by exact Finset.subset_univ _ ) ?_).symm
    intro r hr hrnot
    exact hzero hrnot
  have hone (r : Fin k) : (∑ j ∈ J, c r j) ≤ 1 := by
    calc
      (∑ j ∈ J, c r j) ≤ ∑ j : Fin m, c r j := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        intro i hi hnot
        dsimp [c]
        positivity
      _ = ‖v r‖ ^ 2 := by
        simpa [c] using (u.sum_sq_norm_inner_left (v r))
      _ = 1 := by rw [hv.norm_eq_one r]; norm_num
  have hle : (∑ r ∈ R, ∑ j ∈ J, c r j) ≤ (R.card : ℝ) := by
    calc
      _ ≤ ∑ r ∈ R, (1:ℝ) :=
        Finset.sum_le_sum (fun r hr => hone r)
      _ = (R.card : ℝ) := by simp
  have hc := hcard l hl
  change (R.card : ℝ) ≤ _ at hc
  -- swap the two finite sums on the left; outside the active set every
  -- coefficient is zero.
  change (∑ j ∈ J, ∑ r : Fin k, c r j) ≤ _
  have heq : (∑ j ∈ J, ∑ r : Fin k, c r j) =
        ∑ r : Fin k, ∑ j ∈ J, c r j := by
    -- expand the inner sums over univ before `sum_comm`
    simp_rw [Finset.sum_comm (s := J) (t := (Finset.univ : Finset (Fin k)))]
  rw [heq, hpart]
  exact le_trans hle hc
end LidskiiAux

namespace LidskiiAux
/-- Counting version of the right hand side of a flagged cut. It is handy
when a subspace is first put in echelon form against the other flag. -/
lemma count_selected_prefix {m k : ℕ}
   (idx : Fin k → Fin m) (hi : Function.Injective idx) (l : ℕ) :
   (∑ j ∈ Finset.univ.filter (fun j : Fin m => j.val < l),
       (if j ∈ Finset.univ.image idx then (1:ℝ) else 0)) =
       ((Finset.univ.filter (fun r : Fin k => (idx r).val < l)).card : ℝ) := by
 classical
 let J : Finset (Fin m) := Finset.univ.filter (fun j : Fin m => j.val < l)
 let I : Finset (Fin m) := Finset.univ.image idx
 let R : Finset (Fin k) := Finset.univ.filter (fun r : Fin k => (idx r).val < l)
 have hfilter : J.filter (fun j => j ∈ I) = R.image idx := by
   ext j
   simp [J,I,R]
   aesop

 -- The summand is just a characteristic function.
 change (∑ j ∈ J, if j ∈ I then (1:ℝ) else 0) = (R.card : ℝ)
 calc
   _ = ((J.filter (fun j => j ∈ I)).card : ℝ) := by
     calc
       _ = ((J ∩ I).card : ℝ) := by simp
       _ = ((J.filter (fun j => j ∈ I)).card : ℝ) := by congr 2
   _ = ((R.image idx).card : ℝ) := by rw [hfilter]
   _ = (R.card : ℝ) := by
     rw [Finset.card_image_of_injective _ hi]
end LidskiiAux

-- END INLINED FILE: Mathlib/Support/lidskii_inequality_145b211497/TailMass.lean

-- BEGIN INLINED FILE: Mathlib/Support/lidskii_inequality_145b211497/TwoFlagMass.lean
open scoped BigOperators InnerProductSpace
open Finset Set Matrix
set_option maxHeartbeats 800000

namespace LidskiiAux
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

/-- The mass of the projection onto an orthonormal frame only depends on
its span.  We state it for finite frames, not bases -- in the flag argument
one has two quite different adapted bases of the same plane. -/
lemma sum_sq_inner_eq_of_span_eq {k : ℕ}
    (v w : Fin k → E) (hv : Orthonormal ℂ v) (hw : Orthonormal ℂ w)
    (hs : Submodule.span ℂ (Set.range v) =
          Submodule.span ℂ (Set.range w)) (x : E) :
    (∑ r : Fin k, ‖inner ℂ (v r) x‖ ^ 2) =
      ∑ r : Fin k, ‖inner ℂ (w r) x‖ ^ 2 := by
  classical
  let W : Submodule ℂ E := Submodule.span ℂ (Set.range v)
  have hvW (r : Fin k) : v r ∈ W :=
    Submodule.subset_span (Set.mem_range_self r)
  have hwW (r : Fin k) : w r ∈ W := by
    -- transfer through the common span
    change w r ∈ Submodule.span ℂ (Set.range v)
    rw [hs]
    exact Submodule.subset_span (Set.mem_range_self r)
  let vv : Fin k → W := fun r => ⟨v r, hvW r⟩
  let ww : Fin k → W := fun r => ⟨w r, hwW r⟩
  have hv' : Orthonormal ℂ vv := by
    rw [orthonormal_iff_ite]
    intro i j
    simpa [vv] using (orthonormal_iff_ite.mp hv i j)
  have hw' : Orthonormal ℂ ww := by
    rw [orthonormal_iff_ite]
    intro i j
    simpa [ww] using (orthonormal_iff_ite.mp hw i j)
  have hdimW : Module.finrank ℂ W = k := by
    dsimp [W]
    simpa using (finrank_span_eq_card hv.linearIndependent)
  -- A `k`-element orthonormal family in this `k` plane is a basis.
  have hspanv : (⊤ : Submodule ℂ W) ≤ Submodule.span ℂ (Set.range vv) := by
    have hd : Module.finrank ℂ (Submodule.span ℂ (Set.range vv)) = k := by
      simpa using (finrank_span_eq_card hv'.linearIndependent)
    have ht : Submodule.span ℂ (Set.range vv) = (⊤ : Submodule ℂ W) :=
      Submodule.eq_top_of_finrank_eq (by simpa [hdimW] using hd)
    simp [ht]
  have hspanw : (⊤ : Submodule ℂ W) ≤ Submodule.span ℂ (Set.range ww) := by
    have hd : Module.finrank ℂ (Submodule.span ℂ (Set.range ww)) = k := by
      simpa using (finrank_span_eq_card hw'.linearIndependent)
    have ht : Submodule.span ℂ (Set.range ww) = (⊤ : Submodule ℂ W) :=
      Submodule.eq_top_of_finrank_eq (by simpa [hdimW] using hd)
    simp [ht]
  let bv : OrthonormalBasis (Fin k) ℂ W := OrthonormalBasis.mk hv' hspanv
  let bw : OrthonormalBasis (Fin k) ℂ W := OrthonormalBasis.mk hw' hspanw
  have hbv (r : Fin k) : bv r = vv r := by
    exact congrFun (OrthonormalBasis.coe_mk hv' hspanv) r
  have hbw (r : Fin k) : bw r = ww r := by
    exact congrFun (OrthonormalBasis.coe_mk hw' hspanw) r
  let y : W := W.orthogonalProjectionOnto x
  have hvinner (r : Fin k) :
      inner ℂ (vv r) y = inner ℂ (v r) x := by
    exact Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left (vv r) x
  have hwinner (r : Fin k) :
      inner ℂ (ww r) y = inner ℂ (w r) x := by
    exact Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left (ww r) x
  calc
    (∑ r : Fin k, ‖inner ℂ (v r) x‖ ^ 2) =
        ∑ r : Fin k, ‖inner ℂ (bv r) y‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro r hr
          rw [hbv r, hvinner]
    _ = ‖y‖ ^ 2 := bv.sum_sq_norm_inner_right y
    _ = (∑ r : Fin k, ‖inner ℂ (bw r) y‖ ^ 2) :=
      (bw.sum_sq_norm_inner_right y).symm
    _ = ∑ r : Fin k, ‖inner ℂ (w r) x‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro r hr
          rw [hbw r, hwinner]
end LidskiiAux

namespace LidskiiAux
open scoped BigOperators InnerProductSpace
open Finset Set Matrix
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

/-- Two adapted orthonormal frames of the *same* plane provide exactly the
prefix overlap needed in Abel's lemma.  One frame will carry the increasing
`S` flag; in this elementary lemma only the other frame matters.  Its
columns lie in the successive bottom planes of `b`.  Notice why equality of
spans, rather than pointwise comparison of the columns, is the right
hypothesis: a different orthonormal basis of a plane has the same projection
mass at each `b j`. -/
lemma prefix_overlap_of_two_flag_frames {m k : ℕ}
    (b : OrthonormalBasis (Fin m) ℂ E)
    (idx : Fin k → Fin m) (hi : Function.Injective idx)
    (v w : Fin k → E) (hv : Orthonormal ℂ v) (hw : Orthonormal ℂ w)
    (hspan : Submodule.span ℂ (Set.range v) =
             Submodule.span ℂ (Set.range w))
    (hwbot : ∀ r : Fin k, w r ∈ botSpan b (idx r)) :
    let I : Finset (Fin m) := Finset.univ.image idx
    ∀ l : ℕ, l ≤ m →
      (∑ j ∈ Finset.univ.filter (fun j : Fin m => j.val < l),
         ∑ r : Fin k, ‖inner ℂ (v r) (b j)‖ ^ 2) ≤
        ∑ j ∈ Finset.univ.filter (fun j : Fin m => j.val < l),
          (if j ∈ I then (1:ℝ) else 0) := by
  classical
  dsimp
  have hz : ∀ r : Fin k, ∀ j : Fin m, j.val < (idx r).val →
       inner ℂ (w r) (b j) = 0 := by
    intro r j hj
    exact out_bot_orth b (idx r) j hj (w r) (hwbot r)
  have hc : ∀ l : ℕ, l ≤ m →
       ((Finset.univ.filter (fun r : Fin k => (idx r).val < l)).card : ℝ) ≤
        ∑ j ∈ Finset.univ.filter (fun j : Fin m => j.val < l),
          (if j ∈ Finset.univ.image idx then (1:ℝ) else 0) := by
    intro l hl
    -- both sides count exactly these selected positions
    exact le_of_eq (count_selected_prefix idx hi l).symm
  have hh := prefix_overlap_of_column_tails
    b w hw (Finset.univ.image idx) (fun r : Fin k => (idx r).val)
      hz hc
  intro l hl
  calc
    (∑ j ∈ Finset.univ.filter (fun j : Fin m => j.val < l),
         ∑ r : Fin k, ‖inner ℂ (v r) (b j)‖ ^ 2)
       = (∑ j ∈ Finset.univ.filter (fun j : Fin m => j.val < l),
         ∑ r : Fin k, ‖inner ℂ (w r) (b j)‖ ^ 2) := by
           apply Finset.sum_congr rfl
           intro j hj
           exact sum_sq_inner_eq_of_span_eq v w hv hw hspan (b j)
    _ ≤ _ := hh l hl
end LidskiiAux

namespace LidskiiAux
open scoped BigOperators InnerProductSpace
open Finset Set Matrix
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]
set_option maxHeartbeats 800000

/-- Dimension form of the elementary flag construction.  A common `k`-plane
with the indicated prefix and suffix incidence conditions already suffices.
Gram--Schmidt is done separately along the two nested flags; its outputs
are not the same columns, but they span the same plane.  This isolates the
remaining incidence problem from all metric/projection issues. -/
lemma two_flag_frames_of_subspace {m k : ℕ}
    (u b : OrthonormalBasis (Fin m) ℂ E)
    (f : Fin k ↪o Fin m)
    (W : Submodule ℂ E) (hdW : Module.finrank ℂ W = k)
    (hF : ∀ i : Fin k,
       i.val + 1 ≤ Module.finrank ℂ
         (topSpan u ((f i).val+1) ⊓ W : Submodule ℂ E))
    (hG : ∀ i : Fin k,
       k - i.val ≤ Module.finrank ℂ
         (botSpan b (f i) ⊓ W : Submodule ℂ E)) :
    ∃ v w : Fin k → E, Orthonormal ℂ v ∧ Orthonormal ℂ w ∧
       (∀ i, v i ∈ topSpan u ((f i).val+1)) ∧
       (∀ i, w i ∈ botSpan b (f i)) ∧
       Submodule.span ℂ (Set.range v) = Submodule.span ℂ (Set.range w) := by
  classical
  -- the first (increasing) flag, stopped at `W` after `k`
  let U : ℕ → Submodule ℂ E := fun r =>
    if hr : r < k then topSpan u ((f ⟨r, hr⟩).val+1) ⊓ W else W
  have hmono : Monotone U := by
    intro r s hrs
    dsimp [U]
    split_ifs with hr hs hs
    · intro x hx
      refine ⟨?_, hx.2⟩
      have hfin : (⟨r, hr⟩ : Fin k) ≤ ⟨s, hs⟩ := Fin.mk_le_mk.mpr hrs
      have hle : (f (⟨r,hr⟩ : Fin k)).val + 1 ≤
          (f (⟨s,hs⟩ : Fin k)).val + 1 := by
        have := (f.monotone hfin)
        exact Nat.add_le_add_right (Fin.mk_le_mk.mp this) _
      exact topSpan_mono u hle hx.1
    · intro x hx
      exact hx.2
    · -- impossible branch `¬ r<k`, `s<k`
      exfalso
      exact hr (lt_of_le_of_lt hrs hs)
    · intro x hx
      exact hx
  have hdim : ∀ i : Fin k, i.val+1 ≤ Module.finrank ℂ (U i.val) := by
    intro i
    change i.val+1 ≤ Module.finrank ℂ
      ((if h : i.val < k then
        topSpan u ((f ⟨i.val,h⟩).val+1) ⊓ W else W) : Submodule ℂ E)
    rw [dif_pos i.isLt]
    simpa using hF i
  obtain ⟨v, hv, hvU⟩ := exists_orthonormal_mem_flag U hmono k hdim
  have hvF (i : Fin k) : v i ∈ topSpan u ((f i).val+1) := by
    have h := hvU i
    dsimp [U] at h
    split_ifs at h with hi
    · exact h.1
    · exact (hi i.isLt).elim
  have hvW (i : Fin k) : v i ∈ W := by
    have h := hvU i
    dsimp [U] at h
    split_ifs at h with hi
    · exact h.2
    · exact (hi i.isLt).elim
  -- Reverse the bottom flag; as `r` increases these tails grow.
  let rev : Fin k → Fin k := @Fin.rev k
  let V : ℕ → Submodule ℂ E := fun r =>
    if hr : r < k then botSpan b (f (rev ⟨r, hr⟩)) ⊓ W else W
  have hmonov : Monotone V := by
    intro r s hrs
    dsimp [V]
    split_ifs with hr hs hs
    · intro x hx
      refine ⟨?_, hx.2⟩
      -- reverse turns the order around; bottom tails are antitone in the cut
      have hfin : (⟨r, hr⟩ : Fin k) ≤ ⟨s, hs⟩ := Fin.mk_le_mk.mpr hrs
      have hrev : rev (⟨s, hs⟩ : Fin k) ≤ rev ⟨r, hr⟩ := by
        dsimp [rev]
        exact Fin.mk_le_mk.mpr (by
          dsimp [Fin.rev]
          omega)
      have hf' : (f (rev ⟨s, hs⟩)).val ≤
          (f (rev ⟨r, hr⟩)).val :=
        Fin.mk_le_mk.mp (f.monotone hrev)
      exact botSpan_anti b (Fin.mk_le_mk.mpr hf') hx.1
    · intro x hx
      exact hx.2
    · exfalso
      exact hr (lt_of_le_of_lt hrs hs)
    · intro x hx
      exact hx
  have hdimv : ∀ r : Fin k, r.val+1 ≤ Module.finrank ℂ (V r.val) := by
    intro r
    change r.val+1 ≤ Module.finrank ℂ
      ((if h : r.val < k then
        botSpan b (f (rev ⟨r.val,h⟩)) ⊓ W else W) : Submodule ℂ E)
    rw [dif_pos r.isLt]
    have hh := hG (rev r)
    have hval : (rev ⟨r.val, r.isLt⟩ : Fin k) = rev r := rfl
    have hnum : k - (rev r).val = r.val + 1 := by
      dsimp [rev, Fin.rev]
      have rr := r.isLt
      omega
    rw [hval]
    omega
  obtain ⟨z, hz, hzV⟩ := exists_orthonormal_mem_flag V hmonov k hdimv
  -- put the columns back in the original order
  let w : Fin k → E := fun i => z (rev i)
  have hw : Orthonormal ℂ w := by
    rw [orthonormal_iff_ite]
    intro i j
    have h0 := (orthonormal_iff_ite.mp hz) (rev i) (rev j)
    by_cases h : i = j
    · subst j
      simpa [w] using h0
    · have hn : rev i ≠ rev j := by
        intro hh
        exact h ((Fin.rev_involutive.injective) hh)
      simpa [w, h, hn] using h0
  have hwB (i : Fin k) : w i ∈ botSpan b (f i) := by
    have h0 := hzV (rev i)
    dsimp [V] at h0
    split_ifs at h0 with hi
    · have hrev : rev ⟨(rev i).val, hi⟩ = i := by
        have he : (⟨(rev i).val, hi⟩ : Fin k) = rev i := by rfl
        change Fin.rev (⟨(rev i).val, hi⟩ : Fin k) = i
        rw [he]
        exact Fin.rev_involutive i
      have hx : z (rev i) ∈ botSpan b (f i) := by
        simpa [hrev] using h0.1
      exact hx
    · exact (hi (rev i).isLt).elim
  have hwW (i : Fin k) : w i ∈ W := by
    have h0 := hzV (rev i)
    dsimp [V] at h0
    split_ifs at h0 with hi
    · exact h0.2
    · exact (hi (rev i).isLt).elim
  have hsv : Submodule.span ℂ (Set.range v) = W := by
    apply Submodule.eq_of_le_of_finrank_le
      (Submodule.span_le.mpr (by
        intro x hx
        obtain ⟨i, rfl⟩ := hx
        exact hvW i))
    have hfr := finrank_span_eq_card hv.linearIndependent
    simpa [hdW] using (show Module.finrank ℂ W ≤
      Module.finrank ℂ (Submodule.span ℂ (Set.range v)) from by
        rw [hdW, hfr]; simp)
  have hsw : Submodule.span ℂ (Set.range w) = W := by
    apply Submodule.eq_of_le_of_finrank_le
      (Submodule.span_le.mpr (by
        intro x hx
        obtain ⟨i, rfl⟩ := hx
        exact hwW i))
    have hfr := finrank_span_eq_card hw.linearIndependent
    simpa [hdW] using (show Module.finrank ℂ W ≤
      Module.finrank ℂ (Submodule.span ℂ (Set.range w)) from by
        rw [hdW, hfr]; simp)
  exact ⟨v, w, hv, hw, hvF, hwB, hsv.trans hsw.symm⟩
end LidskiiAux

-- END INLINED FILE: Mathlib/Support/lidskii_inequality_145b211497/TwoFlagMass.lean

-- BEGIN INLINED FILE: Mathlib/Support/lidskii_inequality_145b211497/FlagPlane.lean
open scoped InnerProductSpace BigOperators ComplexConjugate
open Finset Set Matrix
namespace LidskiiAux
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

lemma botSpan_anti_le {m : ℕ} (b : OrthonormalBasis (Fin m) ℂ E)
    (i j : Fin m) (hij : i.val ≤ j.val) : botSpan b j ≤ botSpan b i := by
  classical
  refine (Submodule.span_le).2 ?_
  intro x hx
  change x ∈ (↑((Finset.Ici j).image (⇑b)) : Set E) at hx
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
  apply mem_botSpan b i t
  have ht' := Finset.mem_Ici.mp ht
  have hv := Fin.mk_le_mk.mp ht'
  exact le_trans hij hv

/-- Two full flags contain a `k` plane with dual Schubert incidences.
This is the elementary modular-lattice construction: add the last column,
and, if a tail condition is still tight, take the new line in the *last*
tight tail.  Dimension of `F_last ∩ G_j` is large enough to escape the old
plane. -/
lemma exists_two_flag_plane {m : ℕ} (hm : Module.finrank ℂ E = m)
    (u b : OrthonormalBasis (Fin m) ℂ E) :
    ∀ k : ℕ, ∀ f : Fin k ↪o Fin m,
    ∃ W : Submodule ℂ E, Module.finrank ℂ W = k ∧
      (∀ i : Fin k, i.val + 1 ≤ Module.finrank ℂ
        (topSpan u ((f i).val+1) ⊓ W : Submodule ℂ E)) ∧
      (∀ i : Fin k, k - i.val ≤ Module.finrank ℂ
        (botSpan b (f i) ⊓ W : Submodule ℂ E)) := by
  classical
  intro k
  induction k with
  | zero =>
      intro f
      refine ⟨⊥, by simp, ?_, ?_⟩
      · intro i; exact Fin.elim0 i
      · intro i; exact Fin.elim0 i
  | succ s ih =>
      intro f
      let g : Fin s ↪o Fin m :=
        { toFun := fun i => f (Fin.castSucc i)
          inj' := by
            intro i j h
            exact Fin.castSucc_inj.mp (f.injective h)
          map_rel_iff' := by
            intro i j
            change f (Fin.castSucc i) ≤ f (Fin.castSucc j) ↔ i ≤ j
            rw [f.le_iff_le]
            exact Fin.mk_le_mk }
      obtain ⟨P, hP, hPF, hPG⟩ := ih g
      let last : Fin (s+1) := Fin.last s
      let F : Submodule ℂ E := topSpan u ((f last).val+1)
      let G : Fin (s+1) → Submodule ℂ E := fun i => botSpan b (f i)
      have hFdim : Module.finrank ℂ F = (f last).val + 1 := by
        dsimp [F]
        rw [finrank_topSpan, min_eq_left]
        exact Nat.succ_le_of_lt (f last).isLt
      -- the old plane is already in the last initial space
      have hPFle : P ≤ F := by
        by_cases hs : s = 0
        · have hz : P = ⊥ := (Submodule.finrank_eq_zero).1 (by simpa [hs] using hP)
          rw [hz]
          exact bot_le
        · have hspos : 0 < s := Nat.pos_of_ne_zero hs
          let r : Fin s := ⟨s-1, by omega⟩
          have hr := hPF r
          have heq : (topSpan u ((g r).val+1) ⊓ P : Submodule ℂ E) = P := by
            apply Submodule.eq_of_le_of_finrank_le inf_le_right
            rw [hP]
            -- the preceding last index is `s-1`
            have hv : r.val + 1 = s := by dsimp [r]; omega
            omega
          have hpre : P ≤ topSpan u ((g r).val+1) := by
            intro x hx
            have hx' : x ∈ (topSpan u ((g r).val+1) ⊓ P : Submodule ℂ E) := by
              rw [heq]
              exact hx
            exact hx'.1
          have hleidx : (g r).val + 1 ≤ (f last).val + 1 := by
            have hle0 : (Fin.castSucc r : Fin (s+1)) ≤ last := by
              exact Fin.mk_le_mk.mpr (by dsimp [last, r]; omega)
            have hle1 := f.monotone hle0
            change (f (Fin.castSucc r)).val + 1 ≤ (f last).val + 1
            have hval := Fin.mk_le_mk.mp hle1
            omega
          intro x hx
          exact topSpan_mono u hleidx (hpre hx)
      have hold (i : Fin (s+1)) : s - i.val ≤ Module.finrank ℂ (G i ⊓ P : Submodule ℂ E) := by
        by_cases hi : i.val < s
        · let r : Fin s := ⟨i.val, hi⟩
          have hh := hPG r
          have hcast : (Fin.castSucc r : Fin (s+1)) = i := Fin.ext rfl
          change s - r.val ≤ Module.finrank ℂ (botSpan b (f (Fin.castSucc r)) ⊓ P : Submodule ℂ E)
          change s - r.val ≤ Module.finrank ℂ (botSpan b (f (Fin.castSucc r)) ⊓ P : Submodule ℂ E) at hh
          exact hh
        · have hiz : s ≤ i.val := Nat.le_of_not_gt hi
          have hz : s - i.val = 0 := Nat.sub_eq_zero_of_le hiz
          rw [hz]
          exact Nat.zero_le _
      let D : Finset (Fin (s+1)) := Finset.univ.filter
        (fun i : Fin (s+1) => Module.finrank ℂ (G i ⊓ P : Submodule ℂ E) < (s+1) - i.val)
      -- install a new line, either arbitrary in `F`, or in the last deficient tail
      by_cases hD : D.Nonempty
      · let j : Fin (s+1) := D.max' hD
        have hjD : j ∈ D := Finset.max'_mem D hD
        have hjlt : Module.finrank ℂ (G j ⊓ P : Submodule ℂ E) < (s+1) - j.val :=
          (Finset.mem_filter.mp hjD).2
        have hidxdiff : (f j).val ≤ (f last).val := by
          have hle : j ≤ last := Fin.mk_le_mk.mpr (Nat.le_of_lt_succ j.isLt)
          exact Fin.mk_le_mk.mp (f.monotone hle)
        have hUlarge : (s+1) - j.val ≤
            Module.finrank ℂ (F ⊓ G j : Submodule ℂ E) := by
          have hsup := Submodule.finrank_sup_add_finrank_inf_eq F (G j)
          have hle := Submodule.finrank_le (F ⊔ G j : Submodule ℂ E)
          have hGdim : Module.finrank ℂ (G j) = m - (f j).val := by
            dsimp [G]
            exact finrank_botSpan b (f j)
          rw [hm] at hle
          rw [hFdim, hGdim] at hsup
          have hstep : (s - j.val) ≤ (f last).val - (f j).val := by
            -- the value grows at least by the distance in an order embedding
            -- use room twice? strict climb follows by counting steps; room lemma on a shifted pair is simpler by arithmetic induction
            have climb : ∀ t : ℕ, ∀ ht : j.val + t < s+1,
                (f j).val + t ≤ (f (⟨j.val+t, ht⟩ : Fin (s+1))).val := by
              intro t
              induction t with
              | zero =>
                  intro ht
                  simpa using (Nat.le_refl (f j).val)
              | succ t ih0 =>
                  intro ht
                  have ht0 : j.val + t < s+1 := by omega
                  have hp0 := ih0 ht0
                  have hcur : (⟨j.val+t, ht0⟩ : Fin (s+1)) < ⟨j.val+(t+1), ht⟩ :=
                    Fin.mk_lt_mk.mpr (by omega)
                  have hp1 := f.strictMono hcur
                  have hv := Fin.mk_lt_mk.mp hp1
                  omega
            have hc := climb (s-j.val) (by omega)
            have he : j.val + (s-j.val) = s := by omega
            have hefin : (⟨j.val+(s-j.val), by omega⟩ : Fin (s+1)) = last :=
              Fin.ext (by dsimp [last]; omega)
            have hc' : (f j).val + (s-j.val) ≤ (f last).val := by
              simpa [hefin] using hc
            omega
          -- dimensions of intersections in ambient m
          omega
        have hnot : ¬ (F ⊓ G j : Submodule ℂ E) ≤ P := by
          intro hle'
          have hh : (F ⊓ G j : Submodule ℂ E) ≤ (G j ⊓ P : Submodule ℂ E) := by
            intro x hx
            exact ⟨hx.2, hle' hx⟩
          have hmno := Submodule.finrank_mono hh
          omega
        have hex : ∃ y : E, y ∈ (F ⊓ G j : Submodule ℂ E) ∧ y ∉ P := by
          by_contra hn
          push_neg at hn
          exact hnot (fun x hx => hn x hx)
        obtain ⟨y, hyU, hyP⟩ := hex
        let W : Submodule ℂ E := P ⊔ (ℂ ∙ y)
        have hWdim : Module.finrank ℂ W = s+1 := by
          dsimp [W]
          rw [Submodule.finrank_sup_span_singleton hyP, hP]
        refine ⟨W, hWdim, ?_, ?_⟩
        · intro i
          by_cases hil : i = last
          · subst i
            have hWF : W ≤ F := by
              refine sup_le hPFle ?_
              exact Submodule.span_le.mpr (by
                intro z hz
                have he : z = y := by simpa using hz
                simpa [he] using hyU.1)
            have hiEq : (topSpan u ((f last).val+1) ⊓ W : Submodule ℂ E) = W := by
              exact inf_eq_right.mpr hWF
            have hv := (orderEmb_val_room f last).1
            dsimp [last]
            change s + 1 ≤ Module.finrank ℂ (topSpan u ((f (Fin.last s)).val+1) ⊓ W : Submodule ℂ E)
            rw [show topSpan u ((f (Fin.last s)).val+1) = F by rfl, inf_eq_right.mpr hWF, hWdim]
          · have hil' : i.val < s := by
              have hx := i.isLt
              have hne : i.val ≠ s := by
                intro he
                apply hil
                exact Fin.ext (by simpa [last] using he)
              omega
            let r : Fin s := ⟨i.val, hil'⟩
            have hh := hPF r
            have hmono : (topSpan u ((f i).val+1) ⊓ P : Submodule ℂ E) ≤
                         (topSpan u ((f i).val+1) ⊓ W : Submodule ℂ E) := by
              exact inf_le_inf_left _ le_sup_left
            have hdim := Submodule.finrank_mono hmono
            have hcast : (Fin.castSucc r : Fin (s+1)) = i := Fin.ext rfl
            change r.val + 1 ≤ Module.finrank ℂ (topSpan u ((f (Fin.castSucc r)).val+1) ⊓ P : Submodule ℂ E) at hh
            have hh' : i.val + 1 ≤ Module.finrank ℂ (topSpan u ((f i).val+1) ⊓ P : Submodule ℂ E) := by
              convert hh using 1 <;> simp [r, hcast] <;> try rfl
            exact le_trans hh' hdim
        · intro i
          by_cases hiD : i ∈ D
          · have hij : i ≤ j := Finset.le_max' D i hiD
            have hyGi : y ∈ G i := by
              have hval : (f i).val ≤ (f j).val :=
                Fin.mk_le_mk.mp (f.monotone hij)
              exact botSpan_anti_le b (f i) (f j) hval hyU.2
            have hsmall : ((G i ⊓ P : Submodule ℂ E) ⊔ (ℂ ∙ y)) ≤
                    (G i ⊓ W : Submodule ℂ E) := by
              refine sup_le ?_ ?_
              · intro x hx
                exact ⟨hx.1, (show P ≤ P ⊔ (ℂ ∙ y) from le_sup_left) hx.2⟩
              · refine Submodule.span_le.mpr ?_
                intro x hx
                have heq : x = y := by simpa using hx
                subst x
                exact ⟨hyGi, (show (ℂ ∙ y) ≤ P ⊔ (ℂ ∙ y) from le_sup_right) (Submodule.mem_span_singleton_self y)⟩
            have hyNP : y ∉ (G i ⊓ P : Submodule ℂ E) := by
              intro hh
              exact hyP hh.2
            have hinc := Submodule.finrank_sup_span_singleton hyNP
            have hmon := Submodule.finrank_mono hsmall
            have old := hold i
            dsimp [G] at old ⊢
            change Module.finrank ℂ ((G i ⊓ P) ⊔ (ℂ ∙ y) : Submodule ℂ E) = _ at hinc
            dsimp [G] at hinc hmon
            omega
          · have hiok : (s+1) - i.val ≤ Module.finrank ℂ (G i ⊓ P : Submodule ℂ E) := by
              have hnlt : ¬ Module.finrank ℂ (G i ⊓ P : Submodule ℂ E) < (s+1)-i.val := by
                intro hlt
                exact hiD (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩)
              omega
            have hmono : (G i ⊓ P : Submodule ℂ E) ≤ (G i ⊓ W : Submodule ℂ E) :=
              inf_le_inf_left _ le_sup_left
            have hdim := Submodule.finrank_mono hmono
            exact le_trans hiok hdim
      · -- no tail is tight; an arbitrary new direction in the last initial space works
        have hnot : ¬ F ≤ P := by
          intro hle'
          have hmon := Submodule.finrank_mono hle'
          have hv := (orderEmb_val_room f last).1
          rw [hFdim, hP] at hmon
          have hv' : s ≤ (f last).val := by simpa [last] using hv
          omega
        have hex : ∃ y : E, y ∈ F ∧ y ∉ P := by
          by_contra hn
          push_neg at hn
          exact hnot (fun x hx => hn x hx)
        obtain ⟨y, hyF, hyP⟩ := hex
        let W : Submodule ℂ E := P ⊔ (ℂ ∙ y)
        have hWdim : Module.finrank ℂ W = s+1 := by
          dsimp [W]
          rw [Submodule.finrank_sup_span_singleton hyP, hP]
        refine ⟨W, hWdim, ?_, ?_⟩
        · intro i
          by_cases hil : i = last
          · subst i
            have hWF : W ≤ F := by
              refine sup_le hPFle ?_
              exact Submodule.span_le.mpr (by
                intro z hz
                have he : z = y := by simpa using hz
                simpa [he] using hyF)
            change s + 1 ≤ Module.finrank ℂ (topSpan u ((f (Fin.last s)).val+1) ⊓ W : Submodule ℂ E)
            rw [show topSpan u ((f (Fin.last s)).val+1) = F by rfl, inf_eq_right.mpr hWF, hWdim]
          · have hil' : i.val < s := by
              have hx := i.isLt
              have hne : i.val ≠ s := by
                intro he
                apply hil
                exact Fin.ext (by simpa [last] using he)
              omega
            let r : Fin s := ⟨i.val, hil'⟩
            have hh := hPF r
            have hmono : (topSpan u ((f i).val+1) ⊓ P : Submodule ℂ E) ≤
                         (topSpan u ((f i).val+1) ⊓ W : Submodule ℂ E) := by
              exact inf_le_inf_left _ le_sup_left
            have hdim := Submodule.finrank_mono hmono
            have hcast : (Fin.castSucc r : Fin (s+1)) = i := Fin.ext rfl
            change r.val + 1 ≤ Module.finrank ℂ (topSpan u ((f (Fin.castSucc r)).val+1) ⊓ P : Submodule ℂ E) at hh
            have hh' : i.val + 1 ≤ Module.finrank ℂ (topSpan u ((f i).val+1) ⊓ P : Submodule ℂ E) := by
              convert hh using 1 <;> simp [r, hcast] <;> try rfl
            exact le_trans hh' hdim
        · intro i
          have hiok : (s+1) - i.val ≤ Module.finrank ℂ (G i ⊓ P : Submodule ℂ E) := by
            have hnlt : ¬ Module.finrank ℂ (G i ⊓ P : Submodule ℂ E) < (s+1)-i.val := by
              intro hlt
              have hmD : i ∈ D := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩
              exact hD ⟨i, hmD⟩
            omega
          have hmono : (G i ⊓ P : Submodule ℂ E) ≤ (G i ⊓ W : Submodule ℂ E) :=
            inf_le_inf_left _ le_sup_left
          exact le_trans hiok (Submodule.finrank_mono hmono)

end LidskiiAux

-- END INLINED FILE: Mathlib/Support/lidskii_inequality_145b211497/FlagPlane.lean

-- BEGIN INLINED FILE: Mathlib/Support/lidskii_inequality_145b211497/WeightedCuts.lean
open scoped BigOperators
open Finset
namespace LidskiiAux
/-- Summation by parts with prefix sums, stated for ranges. Keeping the
functions on `ℕ` avoids all casts at a cut of a selected set. -/
lemma sum_mul_eq_prefix_parts (a z : ℕ → ℝ) : ∀ m : ℕ,
    (∑ i ∈ Finset.range (m+1), z i * a i) =
      (∑ i ∈ Finset.range (m+1), z i) * a m +
        ∑ i ∈ Finset.range m,
          (∑ t ∈ Finset.range (i+1), z t) * (a i - a (i+1)) := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
      change (∑ i ∈ Finset.range ((m+1)+1), z i * a i) = _
      calc
        (∑ i ∈ Finset.range ((m+1)+1), z i * a i) =
            (∑ i ∈ Finset.range (m+1), z i * a i) +
               z (m+1) * a (m+1) := by
                 rw [Finset.sum_range_succ]
        _ = ((∑ i ∈ Finset.range (m+1), z i) * a m +
                ∑ i ∈ Finset.range m,
                  (∑ t ∈ Finset.range (i+1), z t) * (a i - a (i+1))) +
               z (m+1) * a (m+1) := by rw [ih]
        _ = (∑ i ∈ Finset.range ((m+1)+1), z i) * a (m+1) +
                ∑ i ∈ Finset.range (m+1),
                  (∑ t ∈ Finset.range (i+1), z t) * (a i - a (i+1)) := by
              rw [Finset.sum_range_succ (f := fun i => z i) (m+1),
                  Finset.sum_range_succ
                    (f := fun i =>
                      (∑ t ∈ Finset.range (i+1), z t) * (a i - a (i+1))) m]
              ring

/-- Abel's elementary prefix criterion. A signed measure of total mass zero
whose every initial segment is nonnegative has nonnegative integral against
any decreasing sequence. This is the scalar cancellation behind a block (or
multi-block) Ky--Fan estimate. -/
lemma antitone_dot_nonneg_of_prefix (a z : ℕ → ℝ) (m : ℕ)
    (ha : ∀ i, a (i+1) ≤ a i)
    (hp : ∀ l, l ≤ m → 0 ≤ ∑ i ∈ Finset.range l, z i)
    (hz : (∑ i ∈ Finset.range m, z i) = 0) :
    0 ≤ ∑ i ∈ Finset.range m, z i * a i := by
  cases m with
  | zero => simp
  | succ m =>
    rw [sum_mul_eq_prefix_parts a z m, hz]
    simp
    -- every term in the difference sum is nonnegative
    apply Finset.sum_nonneg
    intro i hi
    have him : i < m := Finset.mem_range.mp hi
    have hp' : 0 ≤ ∑ t ∈ Finset.range (i+1), z t := hp _ (by omega)
    exact mul_nonneg hp' (sub_nonneg.mpr (ha i))
/-- A convenient two-weight version of the prefix criterion. No bounds on the
individual coefficients are needed -- only the prefix inequalities and the
same total mass. In an eigenbasis `t` is the column-mass distribution and
`s` is the indicator of the chosen spectral positions. -/
lemma antitone_sum_mul_le_of_prefix (a t s : ℕ → ℝ) (m : ℕ)
    (ha : ∀ i, a (i+1) ≤ a i)
    (hp : ∀ l, l ≤ m →
       (∑ i ∈ Finset.range l, t i) ≤ ∑ i ∈ Finset.range l, s i)
    (htot : (∑ i ∈ Finset.range m, t i) = ∑ i ∈ Finset.range m, s i) :
    (∑ i ∈ Finset.range m, t i * a i) ≤
       ∑ i ∈ Finset.range m, s i * a i := by
  let z : ℕ → ℝ := fun i => s i - t i
  have hz : (∑ i ∈ Finset.range m, z i) = 0 := by
    simp [z, Finset.sum_sub_distrib]
    linarith
  have hp' : ∀ l, l ≤ m → 0 ≤ ∑ i ∈ Finset.range l, z i := by
    intro l hl
    simpa [z, Finset.sum_sub_distrib, sub_nonneg] using hp l hl
  have h := antitone_dot_nonneg_of_prefix a z m ha hp' hz
  -- expand the signed integral
  simp [z, sub_mul, Finset.sum_sub_distrib] at h
  linarith
end LidskiiAux

-- END INLINED FILE: Mathlib/Support/lidskii_inequality_145b211497/WeightedCuts.lean

-- BEGIN INLINED FILE: Mathlib/Support/lidskii_inequality_145b211497/WeightedFlag.lean
open scoped BigOperators InnerProductSpace
open Finset Set Matrix
namespace LidskiiAux
private lemma sum_fin_eq_range' {m : ℕ} (F : Fin m → ℝ) :
 (∑ j : Fin m, F j) = ∑ i ∈ Finset.range m, (if h : i < m then F ⟨i,h⟩ else 0) := by
  simpa using (Fin.sum_univ_eq_sum_range (fun i => if h : i < m then F ⟨i,h⟩ else 0) m)

lemma sum_fin_filter_eq_range' {m : ℕ} (F : Fin m → ℝ) (l : ℕ) (hl : l ≤ m) :
 (∑ j ∈ (Finset.univ.filter (fun j:Fin m => j.val < l)), F j) =
 ∑ i ∈ Finset.range l, (if h : i < m then F ⟨i,h⟩ else 0) := by
  classical
  rw [Finset.sum_filter]
  have hconv :
      (∑ a : Fin m, (if a.val < l then F a else 0)) =
        ∑ i ∈ Finset.range m,
          (if hi : i < m then (if i < l then F ⟨i,hi⟩ else 0) else 0) := by
      simpa using (Fin.sum_univ_eq_sum_range
         (fun i => if hi : i < m then (if i < l then F ⟨i,hi⟩ else 0) else 0) m)
  rw [hconv]
  calc
    (∑ i ∈ Finset.range m,
          (if hi : i < m then (if i < l then F ⟨i,hi⟩ else 0) else 0)) =
      ∑ i ∈ Finset.range l,
          (if hi : i < m then (if i < l then F ⟨i,hi⟩ else 0) else 0) := by
        apply (Finset.sum_subset (Finset.range_mono hl) ?_).symm
        intro i hi hi'
        have hh : ¬ i < l := by
          intro h; exact hi' (Finset.mem_range.mpr h)
        simp [hh]
    _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        have il : i < l := Finset.mem_range.mp hi
        have im : i < m := lt_of_lt_of_le il hl
        simp [il, im]

/-- Abel's prefix lemma, on `Fin m`. The version on naturals in
`WeightedCuts` is slightly awkward at the last eigenvalue; this short
transport is useful at a sorted flag.  Notice that the two weights need not
lie between zero and one. The only assumptions are their initial masses and
their equal total mass. -/
lemma antitone_fin_sum_le_of_prefix {m : ℕ}
    (a t s : Fin m → ℝ) (ha : Antitone a)
    (hp : ∀ l : ℕ, l ≤ m →
       (∑ j ∈ Finset.univ.filter (fun j : Fin m => j.val < l), t j) ≤
        ∑ j ∈ Finset.univ.filter (fun j : Fin m => j.val < l), s j)
    (htot : (∑ j : Fin m, t j) = ∑ j : Fin m, s j) :
    (∑ j : Fin m, t j * a j) ≤ ∑ j : Fin m, s j * a j := by
  classical
  cases m with
  | zero => simp
  | succ n =>
    let a' : ℕ → ℝ := fun i => if h : i < n+1 then a ⟨i,h⟩ else a ⟨n, by omega⟩
    let t' : ℕ → ℝ := fun i => if h : i < n+1 then t ⟨i,h⟩ else 0
    let s' : ℕ → ℝ := fun i => if h : i < n+1 then s ⟨i,h⟩ else 0
    have ha' : ∀ i, a' (i+1) ≤ a' i := by
      intro i
      by_cases hi : i < n+1
      · by_cases hu : i+1 < n+1
        · dsimp [a']
          simp [hi, hu]
          exact ha (Fin.mk_le_mk.mpr (by omega))
        · have hin : i = n := by omega
          subst i
          -- the last genuine entry and the constant tail agree
          simp [a']
      · have hu : ¬ i+1 < n+1 := by omega
        have hi' : ¬ i ≤ n := by omega
        have hu' : ¬ i < n := by omega
        simp [a', hi', hu']
    have htp : ∀ l, l ≤ n+1 →
         (∑ i ∈ Finset.range l, t' i) ≤ ∑ i ∈ Finset.range l, s' i := by
      intro l hl
      rw [← sum_fin_filter_eq_range' t l hl,
          ← sum_fin_filter_eq_range' s l hl]
      exact hp l hl
    have htt : (∑ i ∈ Finset.range (n+1), t' i) =
         ∑ i ∈ Finset.range (n+1), s' i := by
      rw [sum_fin_eq_range' t, sum_fin_eq_range' s] at htot
      simpa [t', s'] using htot
    have h := antitone_sum_mul_le_of_prefix a' t' s' (n+1) ha' htp htt
    rw [sum_fin_eq_range' (fun j : Fin (n+1) => t j * a j),
        sum_fin_eq_range' (fun j : Fin (n+1) => s j * a j)]
    convert h using 1
    · apply Finset.sum_congr rfl
      intro i hi
      have hlt : i < n+1 := Finset.mem_range.mp hi
      have hle : i ≤ n := by omega
      simp [a', t', hlt, hle]
    · apply Finset.sum_congr rfl
      intro i hi
      have hlt : i < n+1 := Finset.mem_range.mp hi
      have hle : i ≤ n := by omega
      simp [a', s', hlt, hle]


section flagweights
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
 [FiniteDimensional ℂ E]
/-- The purely numerical half of the still substantial increasing-flag
problem. For a frame put its column masses in the eigenbasis of `T`.  If no
initial segment carries more mass than the selected positions, its trace is
at most their selected spectral sum. This is often a more usable target for
a construction than individual Rayleigh bounds; the latter are generally
false for a flag with a gap. -/
lemma flag_trace_le_of_prefix_overlap
    {m k : ℕ} (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric)
    (hm : Module.finrank ℂ E = m)
    (idx : Fin k → Fin m) (hi : Function.Injective idx)
    (v : Fin k → E) (hv : Orthonormal ℂ v)
    (hp : let s : Finset (Fin m) := Finset.univ.image idx
      ∀ l : ℕ, l ≤ m →
       (∑ j ∈ Finset.univ.filter (fun j : Fin m => j.val < l),
          ∑ r : Fin k, ‖inner ℂ (v r) (hT.eigenvectorBasis hm j)‖ ^ 2) ≤
        ∑ j ∈ Finset.univ.filter (fun j : Fin m => j.val < l),
          (if j ∈ s then (1:ℝ) else 0)) :
    (∑ r : Fin k, RCLike.re (inner ℂ (v r) (T (v r)))) ≤
        ∑ r : Fin k, hT.eigenvalues hm (idx r) := by
  classical
  let b := hT.eigenvectorBasis hm
  let a : Fin m → ℝ := hT.eigenvalues hm
  let t : Fin m → ℝ := fun j => ∑ r : Fin k, ‖inner ℂ (v r) (b j)‖ ^ 2
  let I : Finset (Fin m) := Finset.univ.image idx
  let s : Fin m → ℝ := fun j => if j ∈ I then 1 else 0
  have htt : (∑ j : Fin m, t j) = (k:ℝ) := by
    dsimp [t]
    rw [Finset.sum_comm]
    calc
      (∑ i : Fin k, ∑ j : Fin m, ‖inner ℂ (v i) (b j)‖ ^ 2) =
          ∑ i : Fin k, (1:ℝ) := by
            apply Finset.sum_congr rfl
            intro i hi'
            rw [b.sum_sq_norm_inner_left]
            rw [hv.norm_eq_one]
            norm_num
      _ = (k:ℝ) := by simp
  have hsI : I.card = k := by
    dsimp [I]
    simpa using (Finset.card_image_of_injective
      (Finset.univ : Finset (Fin k)) hi)
  have hss : (∑ j : Fin m, s j) = (k:ℝ) := by
     -- sum of an indicator
     classical
     change (∑ j : Fin m, if j ∈ I then (1:ℝ) else 0) = _
     have hsub : I ⊆ (Finset.univ : Finset (Fin m)) := Finset.subset_univ _
     -- filter sums count the set
     calc
      (∑ j : Fin m, if j ∈ I then (1:ℝ) else 0) =
          ∑ j ∈ (Finset.univ ∩ I), (1:ℝ) := by
            exact Finset.sum_ite_mem (Finset.univ : Finset (Fin m)) I (fun _ => (1:ℝ))
      _ = (k:ℝ) := by simp [hsI]
  have htot : (∑ j : Fin m, t j) = ∑ j : Fin m, s j := htt.trans hss.symm
  have hpre : ∀ l : ℕ, l ≤ m →
     (∑ j ∈ Finset.univ.filter (fun j : Fin m => j.val < l), t j) ≤
       ∑ j ∈ Finset.univ.filter (fun j : Fin m => j.val < l), s j := by
       simpa [t, s, I] using hp
  have hscalar := antitone_fin_sum_le_of_prefix a t s
       (hT.eigenvalues_antitone hm) hpre htot
  -- expand the column masses, then replace the indicator by the injective
  -- enumeration. None of this uses an ordering of that enumeration.
  have hdiag : (∑ r : Fin k, RCLike.re (inner ℂ (v r) (T (v r)))) =
         ∑ j : Fin m, t j * a j := by
     simp_rw [diag_expansion T hT hm]
     change (∑ r : Fin k, ∑ j : Fin m,
        ‖inner ℂ (v r) (b j)‖ ^ 2 * a j) = _
     rw [Finset.sum_comm]
     apply Finset.sum_congr rfl
     intro j hj
     simp [t, Finset.sum_mul]
  have hsdiag : (∑ j : Fin m, s j * a j) =
        ∑ r : Fin k, a (idx r) := by
     have hsub : I ⊆ (Finset.univ : Finset (Fin m)) := Finset.subset_univ _
     calc
      (∑ j : Fin m, s j * a j) = ∑ j ∈ I, a j := by
        change (∑ j : Fin m, (if j ∈ I then (1:ℝ) else 0) * a j) = _
        simp only [ite_mul, one_mul, zero_mul]
        simpa using
          (Finset.sum_ite_mem (Finset.univ : Finset (Fin m)) I a)
      _ = ∑ r : Fin k, a (idx r) := by
        simpa [I] using (Finset.sum_image
          (s := (Finset.univ : Finset (Fin k)))
          (f := fun j : Fin m => a j)
          (g := idx) (Set.injOn_of_injective hi))
  rw [hdiag, ← hsdiag]
  exact hscalar
end flagweights
end LidskiiAux

-- END INLINED FILE: Mathlib/Support/lidskii_inequality_145b211497/WeightedFlag.lean

-- BEGIN INLINED FILE: Mathlib/Support/lidskii_inequality_145b211497/ScalarMajorization.lean
open scoped BigOperators
open Finset
namespace LidskiiAux
/-! A scalar Hardy--Littlewood lemma in the form needed after all selected
cuts have been established.  This is independent of flags. -/

private noncomputable def rpSlope (p x : ℝ) : ℝ :=
  if h : x = 0 then 0 else
    ( (SignType.sign x : ℝ) * p) * |x| ^ (p-1)

private lemma rpSlope_zero (p:ℝ) : rpSlope p 0 = 0 := by simp [rpSlope]
private lemma rpSlope_deriv {p x:ℝ} (hp : 1 ≤ p) (hx : x ≠ 0) :
    HasDerivAt (fun z : ℝ => |z| ^ p) (rpSlope p x) x := by
  have h1 := hasDerivAt_abs hx
  have h2 := h1.rpow_const (p := p) (Or.inl (abs_ne_zero.mpr hx))
  -- the derivative supplied by `rpow_const` has the factors associated
  -- differently
  convert h2 using 1 <;> simp [rpSlope, hx] <;> ring

private lemma rp_tangent (p : ℝ) (hp : 1 ≤ p) (x y : ℝ) :
    |x| ^ p + rpSlope p x * (y-x) ≤ |y| ^ p := by
  classical
  by_cases hx : x = 0
  · subst x
    have hnon : 0 ≤ |y| ^ p := Real.rpow_nonneg (abs_nonneg _) _
    simpa [rpSlope, Real.zero_rpow (by linarith : p ≠ 0)] using hnon
  have hd := rpSlope_deriv hp hx
  by_cases hxy : x < y
  · have hh := (convex_abs_rpow p hp).le_slope_of_hasDerivAt
        (x := x) (y := y) (by simp) (by simp) hxy hd
    rw [slope_def_field] at hh
    have hyx : 0 < y-x := sub_pos.mpr hxy
    have hmul := (le_div_iff₀ hyx).1 hh
    linarith
  · have hyxle : y ≤ x := le_of_not_gt hxy
    by_cases he : y = x
    · subst y; simp
    · have hlt : y < x := lt_of_le_of_ne hyxle he
      have hh := (convex_abs_rpow p hp).slope_le_of_hasDerivAt
         (x := y) (y := x) (by simp) (by simp) hlt hd
      rw [slope_def_field] at hh
      have hpos : 0 < x-y := sub_pos.mpr hlt
      have hmul := (div_le_iff₀ hpos).1 hh
      linarith

private lemma rpSlope_mono (p : ℝ) (hp : 1 ≤ p) :
    Monotone (rpSlope p) := by
  intro x y hxy
  by_cases he : x = y
  · simpa [he]
  have hlt : x < y := lt_of_le_of_ne hxy he
  have h1 := rp_tangent p hp x y
  have h2 := rp_tangent p hp y x
  nlinarith

/-- Finite-vector majorization. `a` is already in decreasing order.  It is
important that the premise asks about *injections*, not about a chosen
sorting of `x`: this is exactly the shape furnished by selected flags. -/
lemma lp_of_injective_prefix_selected {m : ℕ}
    (a x : Fin m → ℝ) (ha : Antitone a)
    (htot : (∑ i : Fin m, x i) = ∑ i : Fin m, a i)
    (hsel : ∀ (k : ℕ) (hk : k ≤ m)
       (idx : Fin k → Fin m), Function.Injective idx →
        (∑ r : Fin k, x (idx r)) ≤
          ∑ j ∈ Finset.univ.filter (fun j : Fin m => j.val < k), a j)
    (p : ℝ) (hp : 1 ≤ p) :
    (∑ i : Fin m, |x i| ^ p) ≤ ∑ i : Fin m, |a i| ^ p := by
  classical
  -- decreasing arrangement of x, obtained by sorting -x increasingly.
  let σ : Equiv.Perm (Fin m) := Tuple.sort (fun i : Fin m => - x i)
  let y : Fin m → ℝ := fun i => x (σ i)
  have hyanti : Antitone y := by
    have hmon := Tuple.monotone_sort (fun i : Fin m => - x i)
    intro i j hij
    have hz := hmon hij
    change x (σ j) ≤ x (σ i)
    change - x (σ i) ≤ - x (σ j) at hz
    linarith
  have hpref : ∀ l : ℕ, l ≤ m →
      (∑ j ∈ Finset.univ.filter (fun j : Fin m => j.val < l), y j) ≤
       ∑ j ∈ Finset.univ.filter (fun j : Fin m => j.val < l), a j := by
    intro l hl
    let ix : Fin l → Fin m := fun r => σ (Fin.castLE hl r)
    have hix : Function.Injective ix := by
      intro r s h
      exact Fin.castLE_inj.1 (σ.injective h)
    have h := hsel l hl ix hix
    have hycast : (∑ r : Fin l, y (Fin.castLE hl r)) =
        ∑ j ∈ Finset.univ.filter (fun j : Fin m => j.val < l), y j :=
      sum_castLE_prefix hl _ _ (fun r => rfl)
    change (∑ r : Fin l, y (Fin.castLE hl r)) ≤ _ at h
    simpa [hycast] using h
  have hytot : (∑ i : Fin m, y i) = ∑ i : Fin m, a i := by
    change (∑ i : Fin m, x (σ i)) = _
    simpa using ( (Equiv.sum_comp σ x).trans htot)
  let d : Fin m → ℝ := fun i => rpSlope p (y i)
  have hdanti : Antitone d := by
    intro i j hij
    exact rpSlope_mono p hp (hyanti hij)
  have hdot : (∑ i : Fin m, y i * d i) ≤ ∑ i : Fin m, a i * d i :=
    antitone_fin_sum_le_of_prefix d y a hdanti hpref hytot
  have hterm (i : Fin m) :
      |y i| ^ p + d i * (a i - y i) ≤ |a i| ^ p := by
    simpa [d] using (rp_tangent p hp (y i) (a i))
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin m)))
        (fun i _ => hterm i)
  have hya : (∑ i : Fin m, |y i| ^ p) ≤ ∑ i : Fin m, |a i| ^ p := by
    -- the linear correction has nonnegative sum by `hdot`
    simp only [Finset.sum_add_distrib] at hs
    have hcorr : 0 ≤ ∑ i : Fin m, d i * (a i - y i) := by
      simp only [mul_sub, Finset.sum_sub_distrib]
      -- commute factors in the two dot products
      have hh : (∑ i : Fin m, d i * y i) ≤ ∑ i : Fin m, d i * a i := by
        simpa [mul_comm] using hdot
      linarith
    linarith
  -- undo the sorting permutation
  have hperm : (∑ i : Fin m, |x i| ^ p) = ∑ i : Fin m, |y i| ^ p := by
    change (∑ i : Fin m, |x i| ^ p) = ∑ i : Fin m, |x (σ i)| ^ p
    exact (Equiv.sum_comp σ (fun i : Fin m => |x i| ^ p)).symm
  simpa [hperm] using hya
end LidskiiAux

-- END INLINED FILE: Mathlib/Support/lidskii_inequality_145b211497/ScalarMajorization.lean

-- BEGIN INLINED FILE: Mathlib/Support/lidskii_inequality_145b211497/DimTwo.lean
open scoped BigOperators InnerProductSpace
open Finset Matrix
namespace LidskiiAux
lemma full_diag_eq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]
    {ι : Type*} [Fintype ι]
    {m : ℕ} (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric)
    (hm : Module.finrank ℂ E = m)
    (u : OrthonormalBasis ι ℂ E) :
    (∑ i : ι, RCLike.re (inner ℂ (u i) (T (u i)))) =
      ∑ j : Fin m, hT.eigenvalues hm j := by
  classical
  let b := hT.eigenvectorBasis hm
  -- expand
  simp_rw [diag_expansion T hT hm]
  have hconv :
    (∑ i : ι, ∑ j : Fin m, ‖inner ℂ (u i) (b j)‖ ^ 2 * hT.eigenvalues hm j) =
      ∑ j : Fin m, ∑ i : ι, ‖inner ℂ (u i) (b j)‖ ^ 2 * hT.eigenvalues hm j := by
        rw [Finset.sum_comm]
  rw [hconv]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← Finset.sum_mul]
  rw [overlap_col u b j]
  simp

lemma eigen_sum_sub
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]
    {m : ℕ} (T S : E →ₗ[ℂ] E) (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    (hm : Module.finrank ℂ E = m) :
    (∑ j : Fin m, (hS.sub hT).eigenvalues hm j) =
      (∑ j : Fin m, hS.eigenvalues hm j) - ∑ j : Fin m, hT.eigenvalues hm j := by
  classical
  let u := hS.eigenvectorBasis hm
  have eS := full_diag_eq S hS hm u
  have eT := full_diag_eq T hT hm u
  have eC := full_diag_eq (S-T) (hS.sub hT) hm u
  rw [← eC, ← eS, ← eT]
  simp [LinearMap.sub_apply, map_sub, Finset.sum_sub_distrib]
end LidskiiAux

-- END INLINED FILE: Mathlib/Support/lidskii_inequality_145b211497/DimTwo.lean

namespace Submission

-- BEGIN INLINED FILE: Main.lean

open Matrix
/-ResultDefinitionsBegin-/
/-ResultProofDefinitionsBegin-/
/-ResultProofDefinitionsEnd-/
/-ResultDefinitionsEnd-/

/-ResultBegin-/

theorem lidskii_inequality {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    {p : ℝ} (_hp : 1 ≤ p) :
    ∑ j, |hA.eigenvalues₀ j - hB.eigenvalues₀ j| ^ p ≤
      ∑ j, |(hB.sub hA).eigenvalues₀ j| ^ p :=
/-ResultProofBegin-/ by
  classical
  let E := EuclideanSpace ℂ n
  let T : E →ₗ[ℂ] E := Matrix.toEuclideanLin A
  let S : E →ₗ[ℂ] E := Matrix.toEuclideanLin B
  have hT : T.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  have hS : S.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hB
  have hdim : Module.finrank ℂ E = Fintype.card n := by
    simp [E]
  have hcore :
      (∑ j : Fin (Fintype.card n), |hT.eigenvalues hdim j - hS.eigenvalues hdim j| ^ p) ≤
        ∑ j : Fin (Fintype.card n), |(hS.sub hT).eigenvalues hdim j| ^ p := by
    let m : ℕ := Fintype.card n
    -- the trace identity
    have htrace :
        (∑ j : Fin (Fintype.card n),
           (hS.sub hT).eigenvalues hdim j) =
          (∑ j : Fin (Fintype.card n), hS.eigenvalues hdim j) -
          ∑ j : Fin (Fintype.card n), hT.eigenvalues hdim j :=
      LidskiiAux.eigen_sum_sub T S hT hS hdim
    have hselected_of_flag (k : ℕ) (hk : k ≤ Fintype.card n)
        (i : Fin k → Fin (Fintype.card n))
        (hv : ∃ v : Fin k → E, Orthonormal ℂ v ∧
          (∀ r, v r ∈ LidskiiAux.topSpan (hS.eigenvectorBasis hdim)
                            ((i r).val + 1)) ∧
          (∑ r : Fin k, RCLike.re (inner ℂ (v r) (T (v r)))) ≤
              ∑ r : Fin k, hT.eigenvalues hdim (i r)) :
        (∑ r : Fin k,
           (hS.eigenvalues hdim (i r) - hT.eigenvalues hdim (i r))) ≤
          ∑ j ∈ Finset.univ.filter
            (fun j : Fin (Fintype.card n) => j.val < k),
             (hS.sub hT).eigenvalues hdim j :=
      LidskiiAux.selected_sub_le_of_flag T S hT hS hdim hk i hv
    -- the incidence plane for two opposite complete flags gives the needed
    -- overlap estimate for every increasing selection.
    have hflags_sorted (k : ℕ) :
        ∀ f : Fin k ↪o Fin (Fintype.card n),
          ∃ v : Fin k → E, Orthonormal ℂ v ∧
            (∀ r, v r ∈ LidskiiAux.topSpan (hS.eigenvectorBasis hdim)
                               ((f r).val + 1)) ∧
            (∑ r : Fin k, RCLike.re (inner ℂ (v r) (T (v r)))) ≤
               ∑ r : Fin k, hT.eigenvalues hdim (f r) := by
      intro f
      obtain ⟨W, hW, hWF, hWG⟩ :=
        LidskiiAux.exists_two_flag_plane hdim
          (hS.eigenvectorBasis hdim) (hT.eigenvectorBasis hdim) k f
      obtain ⟨v, w, hv, hw, hvF, hwG, hvw⟩ :=
        LidskiiAux.two_flag_frames_of_subspace
          (hS.eigenvectorBasis hdim) (hT.eigenvectorBasis hdim)
          f W hW hWF hWG
      refine ⟨v, hv, hvF, ?_⟩
      apply LidskiiAux.flag_trace_le_of_prefix_overlap T hT hdim
        (fun r : Fin k => (f r : Fin (Fintype.card n))) f.injective v hv
      exact LidskiiAux.prefix_overlap_of_two_flag_frames
        (hT.eigenvectorBasis hdim)
        (fun r : Fin k => (f r : Fin (Fintype.card n))) f.injective
        v w hv hw hvw hwG
    -- sorting just relabels the columns
    have hall : ∀ (k : ℕ) (hk : k ≤ Fintype.card n)
        (idx : Fin k → Fin (Fintype.card n)), Function.Injective idx →
          (∑ r : Fin k,
            (hS.eigenvalues hdim (idx r) - hT.eigenvalues hdim (idx r))) ≤
             ∑ j ∈ Finset.univ.filter
                (fun j : Fin (Fintype.card n) => j.val < k),
                 (hS.sub hT).eigenvalues hdim j := by
      intro k hk idx hi
      apply hselected_of_flag k hk idx
      exact LidskiiAux.flag_target_of_all_orderEmb
        (hS.eigenvectorBasis hdim) T (hT.eigenvalues hdim)
        (hflags_sorted k) idx hi
    let aa : Fin (Fintype.card n) → ℝ := (hS.sub hT).eigenvalues hdim
    let xx : Fin (Fintype.card n) → ℝ := fun j =>
      hS.eigenvalues hdim j - hT.eigenvalues hdim j
    have haa : Antitone aa := (hS.sub hT).eigenvalues_antitone hdim
    have hxx : (∑ j : Fin (Fintype.card n), xx j) =
            ∑ j : Fin (Fintype.card n), aa j := by
      dsimp [xx, aa]
      rw [Finset.sum_sub_distrib]
      exact htrace.symm
    have hLP := LidskiiAux.lp_of_injective_prefix_selected aa xx haa hxx (by
      intro k hk idx hi
      exact hall k hk idx hi) p _hp
    calc
      (∑ j : Fin (Fintype.card n),
         |hT.eigenvalues hdim j - hS.eigenvalues hdim j| ^ p) =
          ∑ j : Fin (Fintype.card n), |xx j| ^ p := by
            apply Finset.sum_congr rfl
            intro j hj
            dsimp [xx]
            rw [abs_sub_comm]
      _ ≤ ∑ j : Fin (Fintype.card n), |aa j| ^ p := hLP
      _ = _ := by rfl
  dsimp [Matrix.IsHermitian.eigenvalues₀]
  simpa [T, S, hdim] using hcore
/-ResultProofEnd-/
/-ResultEnd-/
-- END INLINED FILE: Main.lean

end Submission
