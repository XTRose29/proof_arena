import Mathlib

open scoped Matrix
open NormedSpace Filter

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

set_option maxHeartbeats 800000

namespace Submission

variable {n : ℕ}

lemma exp_smul_eq_scalar_mul (A : Matrix (Fin n) (Fin n) ℂ) (t μ : ℂ) :
    exp (t • A) = algebraMap ℂ _ (exp (t * μ)) * exp (t • (A - algebraMap ℂ _ μ)) := by
  have hsplit : t • A = algebraMap ℂ _ (t * μ) + t • (A - algebraMap ℂ _ μ) := by
    simp only [Algebra.algebraMap_eq_smul_one, smul_sub, mul_smul]; abel
  conv_lhs => rw [hsplit]
  rw [exp_add_of_commute (Algebra.commutes (t * μ) _), algebraMap_exp_comm]

/-- Helper: higher powers of a nilpotent matrix kill a vector -/
lemma mulVec_pow_eq_zero_of_le {A₀ : Matrix (Fin n) (Fin n) ℂ} {v : Fin n → ℂ} {k : ℕ}
    (hv : (A₀ ^ k).mulVec v = 0) {l : ℕ} (hl : k ≤ l) :
    (A₀ ^ l).mulVec v = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hl
  rw [show k + m = m + k from by omega, pow_add]
  simp only [← Matrix.mulVec_mulVec]
  rw [hv, Matrix.mulVec_zero]

/-
exp of a matrix applied to a vector truncates to a finite sum when the matrix
    is nilpotent on that vector.
-/
lemma exp_smul_mulVec_eq_sum (N : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) (k : ℕ)
    (hv : (N ^ k).mulVec v = 0) (t : ℂ) :
    (exp (t • N)).mulVec v =
      ∑ j ∈ Finset.range k, (t ^ j / (j.factorial : ℂ)) • (N ^ j).mulVec v := by
  -- Use `exp_eq_tsum ℂ` to write `exp (t • N)` as a sum.
  have h_exp : exp (t • N) = ∑' j, ((1 / (j.factorial : ℂ)) • (t ^ j • N ^ j)) := by
    convert ( exp_eq_tsum ℂ ) using 1;
    any_goals exact Matrix ( Fin n ) ( Fin n ) ℂ;
    all_goals try infer_instance;
    constructor <;> intro h <;> simp_all +decide [ Algebra.smul_def ];
    · convert exp_eq_tsum ℂ using 1;
      exact funext fun x => tsum_congr fun n => by rw [ Algebra.smul_def ] ;
    · simp +decide [ Algebra.algebraMap_eq_smul_one, smul_pow, mul_pow ];
  have h_comm : ∀ (s : Finset ℕ) (f : ℕ → Matrix (Fin n) (Fin n) ℂ), (∑ j ∈ s, f j) *ᵥ v = ∑ j ∈ s, f j *ᵥ v :=
    fun s f => Matrix.sum_mulVec s f v;
  have h_comm : Filter.Tendsto (fun s : Finset ℕ => (∑ j ∈ s, ((1 / (j.factorial : ℂ)) • (t ^ j • N ^ j))) *ᵥ v) Filter.atTop (nhds ((∑' j, ((1 / (j.factorial : ℂ)) • (t ^ j • N ^ j))) *ᵥ v)) := by
    have h_comm : Summable (fun j : ℕ => ((1 / (j.factorial : ℂ)) • (t ^ j • N ^ j))) := by
      refine' Pi.summable.mpr _;
      intro i; refine' Pi.summable.mpr _; intro j; simp +decide [ Matrix.mulVec, dotProduct ] ;
      -- Since $N$ is a matrix, $(N^j)_{ij}$ is bounded.
      have h_bound : ∃ C : ℝ, ∀ j : ℕ, ∀ i j' : Fin n, ‖(N ^ j) i j'‖ ≤ C ^ j := by
        use ∑ i, ∑ j, ‖N i j‖;
        intro j i j'; induction' j with j ih generalizing i j' <;> simp_all +decide [ pow_succ, Matrix.mul_apply ];
        · by_cases hij : i = j' <;> aesop;
        · refine' le_trans ( norm_sum_le _ _ ) _;
          simp_all +decide [ Finset.mul_sum _ _ _, norm_mul ];
          exact Finset.sum_le_sum fun x _ => le_trans ( mul_le_mul_of_nonneg_right ( ih _ _ ) ( norm_nonneg _ ) ) ( Finset.single_le_sum ( fun y _ => mul_nonneg ( pow_nonneg ( Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg ( N i j ) ) _ ) ( norm_nonneg ( N x y ) ) ) ( Finset.mem_univ _ ) );
      obtain ⟨ C, hC ⟩ := h_bound; refine' Summable.of_norm _; simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ] ;
      refine' Summable.of_nonneg_of_le ( fun j => by positivity ) ( fun j => _ ) ( Real.summable_pow_div_factorial ( ‖t‖ * C ) );
      rw [ inv_mul_eq_div, div_le_div_iff_of_pos_right ( by positivity ) ] ; convert mul_le_mul_of_nonneg_left ( hC j i _ ) ( by positivity : 0 ≤ ‖t‖ ^ j ) using 1 ; ring;
    have h_comm : Filter.Tendsto (fun s : Finset ℕ => (∑ j ∈ s, ((1 / (j.factorial : ℂ)) • (t ^ j • N ^ j)))) Filter.atTop (nhds (∑' j, ((1 / (j.factorial : ℂ)) • (t ^ j • N ^ j)))) := by
      exact h_comm.hasSum;
    exact Filter.Tendsto.comp ( Continuous.tendsto ( show Continuous fun m : Matrix ( Fin n ) ( Fin n ) ℂ => m *ᵥ v from continuous_id.matrix_mulVec continuous_const ) _ ) h_comm;
  have h_comm : Filter.Tendsto (fun s : Finset ℕ => ∑ j ∈ s, ((1 / (j.factorial : ℂ)) • (t ^ j • N ^ j)) *ᵥ v) Filter.atTop (nhds (∑ j ∈ Finset.range k, ((1 / (j.factorial : ℂ)) • (t ^ j • N ^ j)) *ᵥ v)) := by
    have h_comm : ∀ j ≥ k, ((1 / (j.factorial : ℂ)) • (t ^ j • N ^ j)) *ᵥ v = 0 := by
      intro j hj
      have h_nilpotent : (N ^ j) *ᵥ v = 0 :=
        mulVec_pow_eq_zero_of_le hv hj;
      simp_all +decide [ Matrix.mulVec, funext_iff ];
      simp_all +decide [ dotProduct, Finset.mul_sum _ _ _, mul_assoc, mul_left_comm, Finset.sum_mul ];
      exact fun x => by simpa [ mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ] using mul_eq_zero_of_right ( t ^ j * ( j.factorial : ℂ ) ⁻¹ ) ( h_nilpotent x ) ;
    refine' tendsto_const_nhds.congr' _;
    filter_upwards [ Filter.eventually_ge_atTop ( Finset.range k ) ] with s hs;
    rw [ ← Finset.sum_subset hs ];
    exact fun x hx hx' => h_comm x <| le_of_not_gt fun hx'' => hx' <| Finset.mem_range.mpr hx'';
  simp_all +decide [ div_eq_inv_mul, Matrix.mulVec_smul ];
  convert tendsto_nhds_unique ‹Tendsto ( fun s : Finset ℕ => ∑ j ∈ s, ( ( j.factorial : ℂ ) ⁻¹ • t ^ j • N ^ j ) *ᵥ v ) atTop ( nhds ( ( ∑' j : ℕ, ( j.factorial : ℂ ) ⁻¹ • t ^ j • N ^ j ) *ᵥ v ) ) › h_comm using 1;
  simp +decide [ Matrix.mulVec, funext_iff ];
  simp +decide [ mul_assoc, dotProduct ];
  simp +decide [ mul_assoc, Finset.mul_sum _ _ _ ]

/-
Polynomial times decaying exponential tends to zero (real version)
-/
lemma tendsto_rpow_mul_exp_neg_re {α : ℝ} (hα : α < 0) (k : ℕ) :
    Tendsto (fun t : ℝ => |t| ^ k * Real.exp (α * t)) atTop (nhds 0) := by
  -- Since $|t| = t$ for $t \geq 0$, we can rewrite the limit expression as $\lim_{t \to \infty} t^k e^{\alpha t}$.
  suffices h_suff : Filter.Tendsto (fun t : ℝ => t ^ k * Real.exp (α * t)) Filter.atTop (nhds 0) by
    exact h_suff.congr' ( by filter_upwards [ Filter.eventually_ge_atTop 0 ] with t ht using by rw [ abs_of_nonneg ht ] );
  -- Let $y = -\alpha t$, therefore the limit becomes $\lim_{y \to \infty} \left(\frac{-y}{\alpha}\right)^k e^{-y}$.
  suffices h_suff : Filter.Tendsto (fun y => (-y / α) ^ k * Real.exp (-y)) Filter.atTop (nhds 0) by
    convert h_suff.comp ( Filter.tendsto_id.const_mul_atTop ( neg_pos.mpr hα ) ) using 2 ; norm_num ; ring_nf;
    norm_num [ hα.ne ];
  convert Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k |> Filter.Tendsto.const_mul ( ( -1 / α ) ^ k ) using 2 <;> ring

/-
On the generalized eigenspace for eigenvalue μ with Re(μ) < 0,
    exp(t•A).mulVec v → 0 as t → ∞.
-/
lemma exp_mulVec_genEigenspace_tendsto_zero (A : Matrix (Fin n) (Fin n) ℂ) (μ : ℂ)
    (hμ : μ.re < 0) (v : Fin n → ℂ) (k : ℕ)
    (hv : ((A - algebraMap ℂ _ μ) ^ k).mulVec v = 0) :
    Tendsto (fun t : ℝ => (exp ((t : ℂ) • A)).mulVec v) atTop (nhds 0) := by
  -- Apply the key formula (exp_smul_mulVec_eq_sum and exp_smul_eq_scalar_mul):
  have h_formula : ∀ t : ℝ, (exp ((t : ℂ) • A)).mulVec v = Complex.exp (t * μ) • (∑ j ∈ Finset.range k, (t ^ j / (j.factorial : ℂ)) • ((A - algebraMap ℂ _ μ) ^ j).mulVec v) := by
    intro t
    have := exp_smul_eq_scalar_mul A (t : ℂ) μ
    have := exp_smul_mulVec_eq_sum (A - algebraMap ℂ _ μ) v k hv (t : ℂ)
    simp_all +decide [ Matrix.mulVec_smul ];
    convert congr_arg ( fun x => ( algebraMap ℂ ( Matrix ( Fin n ) ( Fin n ) ℂ ) ) ( Complex.exp ( t * μ ) ) *ᵥ x ) this using 1;
    · ext; simp +decide [ Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum_div ] ;
    · erw [ Algebra.algebraMap_eq_smul_one ] ; simp +decide [ Matrix.smul_eq_diagonal_mul ];
      erw [ Algebra.algebraMap_eq_smul_one ] ; simp +decide [ Matrix.smul_eq_diagonal_mul ];
  -- For decay: The norm of each term exp(t*μ) * t^j/j! when t is real is exp(t·Re(μ)) · |t|^j / j! which tends to 0 since Re(μ) < 0.
  have h_decay : ∀ j : ℕ, Tendsto (fun t : ℝ => Complex.exp (t * μ) * (t ^ j / (j.factorial : ℂ))) atTop (nhds 0) := by
    intro j;
    have h_decay : Filter.Tendsto (fun t : ℝ => Real.exp (t * μ.re) * (t ^ j / (j.factorial : ℝ))) Filter.atTop (nhds 0) := by
      have := tendsto_rpow_mul_exp_neg_re hμ j;
      simpa [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm ] using this.mul_const ( ( j.factorial : ℝ ) ⁻¹ ) |> Filter.Tendsto.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with t ht using by rw [ abs_of_pos ht ] ; ring );
    rw [ tendsto_zero_iff_norm_tendsto_zero ] at *;
    simp_all +decide [ Complex.norm_exp ];
  simp_all +decide [ funext_iff, tendsto_pi_nhds ];
  exact fun x => by simpa [ Finset.mul_sum _ _ _, mul_assoc, mul_left_comm, Finset.sum_mul ] using tendsto_finset_sum _ fun i _ => Filter.Tendsto.mul_const _ ( h_decay i ) ;

/-
If all eigenvalues of A have negative real part, then exp(t•A).mulVec v → 0.
-/
lemma exp_mulVec_tendsto_zero_complex (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ μ : ℂ, Module.End.HasEigenvalue (Matrix.toLin' A) μ → μ.re < 0)
    (v : Fin n → ℂ) :
    Tendsto (fun t : ℝ => (exp ((t : ℂ) • A)).mulVec v) atTop (nhds 0) := by
  -- By Module.End.iSup_maxGenEigenspace_eq_top, we can write $v$ as a finite sum of generalized eigenvectors.
  have h_decomp : ∃ (f : Finset ℂ) (w : ℂ → (Fin n) → ℂ), v = ∑ μ ∈ f, w μ ∧ ∀ μ ∈ f, ∃ k : ℕ, ((A - algebraMap ℂ _ μ) ^ k).mulVec (w μ) = 0 := by
    -- By Module.End.iSup_maxGenEigenspace_eq_top, we can write $v$ as a finite sum of generalized eigenvectors using the fact that the union of the generalized eigenspaces is the entire space.
    have h_union : v ∈ ⨆ (μ : ℂ), (Module.End.maxGenEigenspace (Matrix.toLin' A)) μ := by
      convert Submodule.mem_top ( x := v );
      convert Module.End.iSup_maxGenEigenspace_eq_top ( Matrix.toLin' A );
    rw [ Submodule.mem_iSup_iff_exists_finsupp ] at h_union;
    obtain ⟨ f, hf₁, hf₂ ⟩ := h_union; use f.support, fun μ => f μ; simp_all +decide [ Finsupp.sum ] ;
    intro μ hμ; specialize hf₁ μ; simp_all +decide [ Module.End.HasUnifEigenvalue, Module.End.eigenspace ] ;
    convert hf₁ using 1;
    ext k; simp +decide [ Matrix.toLin'_apply, Algebra.smul_def ] ;
    erw [ show ( Matrix.toLin' A - ( algebraMap ℂ ( Module.End ℂ ( Fin n → ℂ ) ) ) μ ) ^ k = Matrix.toLin' ( ( A - ( algebraMap ℂ ( Matrix ( Fin n ) ( Fin n ) ℂ ) ) μ ) ^ k ) from ?_ ];
    · rfl;
    · induction k <;> simp_all +decide [ pow_succ, Matrix.toLin'_mul ];
      · rfl;
      · ext; simp +decide [ Algebra.algebraMap_eq_smul_one ] ;
  -- For each μ with w μ ≠ 0, μ is an eigenvalue (HasEigenvalue), so by hA, Re(μ) < 0.
  obtain ⟨f, w, hv, hw⟩ := h_decomp
  have h_eigenvalues : ∀ μ ∈ f, w μ ≠ 0 → Module.End.HasEigenvalue (Matrix.toLin' A) μ := by
    intro μ hμ hwμ
    obtain ⟨k, hk⟩ := hw μ hμ
    have h_eigenvalue : ∃ v : Fin n → ℂ, v ≠ 0 ∧ (A - algebraMap ℂ _ μ).mulVec v = 0 := by
      contrapose! hk;
      refine' Nat.recOn k _ _ <;> simp_all +decide [ pow_succ', Matrix.mulVec_mulVec ];
      intro k hk; specialize hk; specialize hk; simp_all +decide [ ← Matrix.mulVec_mulVec ] ;
    obtain ⟨ v, hv, hv' ⟩ := h_eigenvalue; simp_all +decide [ Module.End.HasUnifEigenvalue, Matrix.sub_mulVec ] ;
    simp_all +decide [ Submodule.eq_bot_iff ];
    simp_all +decide [ sub_eq_zero, Algebra.algebraMap_eq_smul_one ];
    exact ⟨ v, by simpa [ Matrix.smul_eq_diagonal_mul ] using hv', hv ⟩;
  -- By linearity, exp(t•A).mulVec v = ∑ exp(t•A).mulVec (w μ) → 0.
  have h_sum : Tendsto (fun t : ℝ => ∑ μ ∈ f, (exp ((t : ℂ) • A)).mulVec (w μ)) atTop (nhds 0) := by
    have h_sum : ∀ μ ∈ f, Tendsto (fun t : ℝ => (exp ((t : ℂ) • A)).mulVec (w μ)) atTop (nhds 0) := by
      intro μ hμ; specialize hw μ hμ; by_cases h : w μ = 0 <;> simp_all +decide [ Module.End.HasUnifEigenvalue ] ;
      convert exp_mulVec_genEigenspace_tendsto_zero A μ ( hA μ ( h_eigenvalues μ hμ h ) ) ( w μ ) hw.choose hw.choose_spec using 1;
    simpa only [ Finset.sum_const_zero ] using tendsto_finset_sum _ h_sum;
  convert h_sum using 2 ; ext i ; simp +decide [ hv, Matrix.mulVec, dotProduct, Finset.mul_sum _ _ _ ];
  exact Finset.sum_comm

end Submission