import Submission.LayerMajorization
import Submission.Layers

namespace Submission.SpectralPath

open scoped InnerProductSpace

open Module
open Submission.Majorization
open Submission.LayerMajorization

lemma eigenvalues_eq_of_eq {K E : Type*} [RCLike K]
    [NormedAddCommGroup E] [InnerProductSpace K E] [FiniteDimensional K E]
    {N : ℕ} {S T : E →ₗ[K] E} (hS : S.IsSymmetric) (hT : T.IsSymmetric)
    (hn : finrank K E = N) (hST : S = T) :
    hS.eigenvalues hn = hT.eigenvalues hn := by
  subst T
  rfl

theorem sum_abs_eigenvalues_add_sub_le {K E : Type*} [RCLike K]
    [NormedAddCommGroup E] [InnerProductSpace K E] [FiniteDimensional K E]
    {N : ℕ} {T C : E →ₗ[K] E} (hT : T.IsSymmetric) (hC : C.IsSymmetric)
    (hn : finrank K E = N) {p : ℝ} (hp : 1 ≤ p) :
    ∑ i, |(hT.add hC).eigenvalues hn i - hT.eigenvalues hn i| ^ p ≤
      ∑ i, |hC.eigenvalues hn i| ^ p := by
  classical
  cases N with
  | zero => simp
  | succ N =>
      let hTC : (T + C).IsSymmetric := hT.add hC
      let c : Fin (N + 1) → ℝ := hC.eigenvalues hn
      let b : OrthonormalBasis (Fin (N + 1)) K E := hC.eigenvectorBasis hn
      let t : Fin N → ℝ := fun k ↦
        seqAt c k.val - seqAt c (k.val + 1)
      have ht (k : Fin N) : 0 ≤ t k := by
        dsimp [t]
        rw [seqAt_of_lt c (by omega), seqAt_of_lt c (by omega)]
        exact sub_nonneg.mpr <| hC.eigenvalues_antitone hn <|
          Fin.mk_le_mk.mpr (by omega)

      let U : Fin N → E →ₗ[K] E := fun k ↦
        (t k : K) • Submission.Layers.prefixProjection b k.castSucc
      have hU (k : Fin N) : (U k).IsSymmetric := by
        dsimp [U]
        exact ((Submission.Layers.prefixProjection_isPositive b k.castSucc).smul_of_nonneg
          (RCLike.ofReal_nonneg.mpr (ht k))).isSymmetric

      have hC_decomp :
          C = (c (Fin.last N) : K) • LinearMap.id + ∑ k, U k := by
        apply b.toBasis.ext
        intro i
        have hcoeff := descending_layer_decomposition c i
        have hcoeffK :
            (c i : K) = (c (Fin.last N) : K) +
              ∑ k : Fin N, if i ≤ k.castSucc then (t k : K) else 0 := by
          calc
            (c i : K) = (c (Fin.last N) : K) +
                ∑ k : Fin N,
                  (initialSegment k.castSucc
                    (seqAt c k.val - seqAt c (k.val + 1)) i : K) := by
              simpa only [map_add, map_sum] using
                congrArg (RCLike.ofReal : ℝ → K) hcoeff
            _ = _ := by
              congr 1
              apply Fintype.sum_congr
              intro k
              by_cases hik : i ≤ k.castSucc
              · simp [initialSegment, hik, t, map_sub]
              · simp [initialSegment, hik]
        calc
          C (b i) = (c i : K) • b i := hC.apply_eigenvectorBasis hn i
          _ = (c (Fin.last N) : K) • b i +
              ∑ k : Fin N, (t k : K) •
                (if i ≤ k.castSucc then b i else 0) := by
            rw [hcoeffK, add_smul, Finset.sum_smul]
            apply congrArg ((c (Fin.last N) : K) • b i + ·)
            apply Fintype.sum_congr
            intro k
            split <;> simp_all
          _ = ((c (Fin.last N) : K) • (LinearMap.id : E →ₗ[K] E) +
              ∑ k, U k) (b i) := by
            simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
              LinearMap.sum_apply, U, Submission.Layers.prefixProjection_apply_basis]

      let S₀ : E →ₗ[K] E := T + (c (Fin.last N) : K) • LinearMap.id
      have hS₀ : S₀.IsSymmetric := by
        dsimp [S₀]
        exact hT.add <| LinearMap.IsSymmetric.id.smul (by simp)

      let u : ℕ → E →ₗ[K] E := fun k ↦ if hk : k < N then U ⟨k, hk⟩ else 0
      have hu (k : ℕ) : (u k).IsSymmetric := by
        dsimp [u]
        split
        · exact hU _
        · exact LinearMap.IsSymmetric.zero

      let S : ℕ → E →ₗ[K] E := fun q ↦ S₀ + ∑ k ∈ Finset.range q, u k
      have hS (q : ℕ) : (S q).IsSymmetric := by
        dsimp [S]
        exact hS₀.add <| LinearMap.isSymmetric_sum (Finset.range q) fun k _ ↦ hu k
      have hstep (k : Fin N) : S (k.val + 1) = S k.val + U k := by
        dsimp [S, S₀]
        rw [Finset.sum_range_succ]
        simp only [u, dif_pos k.isLt]
        abel
      have hsum_u :
          ∑ k ∈ Finset.range N, u k = ∑ k : Fin N, U k := by
        rw [← Fin.sum_univ_eq_sum_range u N]
        apply Fintype.sum_congr
        intro k
        simp [u, k.isLt]
      have hfinal : S N = T + C := by
        dsimp [S]
        rw [hsum_u]
        dsimp [S₀]
        rw [add_assoc, ← hC_decomp]

      let d : Fin N → Fin (N + 1) → ℝ := fun k i ↦
        (hS (k.val + 1)).eigenvalues hn i - (hS k.val).eigenvalues hn i
      have hAfter (k : Fin N) :
          (S k.val + (t k : K) • Submission.Layers.prefixProjection b k.castSucc).IsSymmetric := by
        exact (hS k.val).add (hU k)
      have heigAfter (k : Fin N) :
          (hAfter k).eigenvalues hn = (hS (k.val + 1)).eigenvalues hn := by
        exact eigenvalues_eq_of_eq (hAfter k) (hS (k.val + 1)) hn (hstep k).symm
      have hd0 (k : Fin N) (i : Fin (N + 1)) : 0 ≤ d k i := by
        have h := Submission.Layers.prefix_update_shift_nonneg
          (hS k.val) hn b k.castSucc (ht k) (hAfter k) i
        simpa only [d, heigAfter k] using h
      have hdt (k : Fin N) (i : Fin (N + 1)) : d k i ≤ t k := by
        have h := Submission.Layers.prefix_update_shift_le
          (hS k.val) hn b k.castSucc (ht k) (hAfter k) i
        simpa only [d, heigAfter k] using h
      have hdsum (k : Fin N) :
          ∑ i, d k i = (k.castSucc.val + 1) * t k := by
        have h := Submission.Layers.sum_prefix_update_shift
          (hS k.val) hn b k.castSucc (t k) (hAfter k)
        simpa only [d, heigAfter k] using h

      have heig_zero :
          (hS 0).eigenvalues hn =
            fun i ↦ hT.eigenvalues hn i + c (Fin.last N) := by
        have h := Submission.Helpers.eigenvalues_add_real_smul_id
          hT hn (c (Fin.last N)) hS₀
        have hzero : S 0 = S₀ := by simp [S]
        exact (eigenvalues_eq_of_eq (hS 0) hS₀ hn hzero).trans h
      have heig_final :
          (hS N).eigenvalues hn = hTC.eigenvalues hn := by
        exact eigenvalues_eq_of_eq (hS N) hTC hn hfinal
      have hd_tel (i : Fin (N + 1)) :
          ∑ k, d k i =
            (hS N).eigenvalues hn i - (hS 0).eigenvalues hn i := by
        change (∑ k : Fin N,
          ((hS (k.val + 1)).eigenvalues hn i - (hS k.val).eigenvalues hn i)) = _
        calc
          _ = ∑ k ∈ Finset.range N,
              ((hS (k + 1)).eigenvalues hn i - (hS k).eigenvalues hn i) :=
            Fin.sum_univ_eq_sum_range
              (fun k ↦ (hS (k + 1)).eigenvalues hn i - (hS k).eigenvalues hn i) N
          _ = _ := Finset.sum_range_sub (fun k ↦ (hS k).eigenvalues hn i) N

      let x : Fin (N + 1) → ℝ := fun i ↦
        hTC.eigenvalues hn i - hT.eigenvalues hn i
      let y : Fin (N + 1) → ℝ := c
      have hx (i : Fin (N + 1)) :
          x i = c (Fin.last N) + ∑ k, d k i := by
        rw [hd_tel i, congrFun heig_final i, congrFun heig_zero i]
        dsimp [x]
        ring
      have hy (i : Fin (N + 1)) :
          y i = c (Fin.last N) +
            ∑ k : Fin N, initialSegment k.castSucc (t k) i := by
        simpa [y, t] using descending_layer_decomposition c i
      have hpartial (σ : Equiv.Perm (Fin (N + 1))) (q : ℕ) (hq : q ≤ N + 1) :
          ∑ i ∈ Finset.range q, seqAt (x ∘ σ) i ≤
            ∑ i ∈ Finset.range q, seqAt y i :=
        prefix_sum_le_of_layer_decomposition (c (Fin.last N)) d
          (fun k ↦ k.castSucc) t hd0 hdt hdsum hx hy σ q hq
      have htotal : ∑ i, x i = ∑ i, y i := by
        dsimp [x, y, c, hTC]
        rw [Finset.sum_sub_distrib, ← (hT.add hC).re_trace_eq_sum_eigenvalues hn,
          ← hT.re_trace_eq_sum_eigenvalues hn, ← hC.re_trace_eq_sum_eigenvalues hn]
        simp [map_add]
      exact sum_abs_rpow_le_of_permuted_prefix hpartial htotal hp

end Submission.SpectralPath
