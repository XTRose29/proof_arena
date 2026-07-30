import Mathlib

namespace Submission

open scoped Matrix

open Asymptotics
open Filter Topology
open IsAbsoluteValue
open scoped BigOperators
open scoped Matrix.Norms.Operator

lemma tendsto_norm_zero_of_tendsto_zero {α E : Type*} [SeminormedAddCommGroup E]
    {l : Filter α} {f : α → E} (hf : Filter.Tendsto f l (nhds 0)) :
    Filter.Tendsto (fun a => ‖f a‖) l (nhds 0) := by
  simpa using hf.norm

lemma tendsto_zero_of_subsingleton {α E : Type*} [TopologicalSpace E] [Zero E] [Subsingleton E]
    {l : Filter α} (f : α → E) : Filter.Tendsto f l (nhds 0) := by
  have hfun : f = fun _ : α => (0 : E) := by
    funext a
    exact Subsingleton.elim _ _
  rw [hfun]
  exact tendsto_const_nhds

lemma tendsto_norm_atTop_of_subsingleton {E : Type*} [SeminormedAddCommGroup E]
    [Subsingleton E] (f : ℝ → E) :
    Filter.Tendsto (fun t : ℝ => ‖f t‖) Filter.atTop (nhds 0) := by
  exact tendsto_norm_zero_of_tendsto_zero (tendsto_zero_of_subsingleton f)

lemma fin_zero_solution_norm_tendsto (_A : Matrix (Fin 0) (Fin 0) ℝ)
    (x : ℝ → (Fin 0 → ℝ)) :
    Filter.Tendsto (fun t : ℝ => ‖x t‖) Filter.atTop (nhds 0) := by
  exact tendsto_norm_atTop_of_subsingleton x

lemma tendsto_sub_const_atTop (c : ℝ) :
    Filter.Tendsto (fun t : ℝ => t - c) Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  refine ⟨b + c, ?_⟩
  intro a ha
  linarith

lemma tendsto_norm_zero_of_eventually_eq {α E : Type*} [SeminormedAddCommGroup E]
    {l : Filter α} {f g : α → E}
    (hfg : f =ᶠ[l] g) (hg : Filter.Tendsto g l (nhds 0)) :
    Filter.Tendsto (fun a => ‖f a‖) l (nhds 0) := by
  exact tendsto_norm_zero_of_tendsto_zero (hg.congr' hfg.symm)

lemma matrix_exp_isUnit_real (n : ℕ) (B : Matrix (Fin n) (Fin n) ℝ) :
    IsUnit (NormedSpace.exp B : Matrix (Fin n) (Fin n) ℝ) := by
  simpa using Matrix.isUnit_exp B

lemma matrix_exp_neg_mul_self (n : ℕ) (B : Matrix (Fin n) (Fin n) ℝ) :
    (NormedSpace.exp (-B) : Matrix (Fin n) (Fin n) ℝ) * NormedSpace.exp B = 1 := by
  have hneg := Matrix.exp_neg B
  have hunit : IsUnit (NormedSpace.exp B : Matrix (Fin n) (Fin n) ℝ) :=
    matrix_exp_isUnit_real n B
  rw [hneg]
  exact Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hunit)

lemma matrix_exp_self_mul_neg (n : ℕ) (B : Matrix (Fin n) (Fin n) ℝ) :
    (NormedSpace.exp B : Matrix (Fin n) (Fin n) ℝ) * NormedSpace.exp (-B) = 1 := by
  have hneg := Matrix.exp_neg B
  have hunit : IsUnit (NormedSpace.exp B : Matrix (Fin n) (Fin n) ℝ) :=
    matrix_exp_isUnit_real n B
  rw [hneg]
  exact Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hunit)

lemma tendsto_of_solution_formula_and_decay {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (x : ℝ → (Fin n → ℝ)) (v : Fin n → ℝ)
    (hformula : ∀ᶠ t in Filter.atTop,
      x t = (NormedSpace.exp (((t - 1) : ℝ) • A) : Matrix (Fin n) (Fin n) ℝ) *ᵥ v)
    (hdecay : Filter.Tendsto
      (fun s : ℝ => (NormedSpace.exp (s • A) : Matrix (Fin n) (Fin n) ℝ) *ᵥ v)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun t : ℝ => ‖x t‖) Filter.atTop (nhds 0) := by
  have hshift : Filter.Tendsto (fun t : ℝ => t - 1) Filter.atTop Filter.atTop :=
    tendsto_sub_const_atTop 1
  have hmodel : Filter.Tendsto
      (fun t : ℝ =>
        (NormedSpace.exp (((t - 1) : ℝ) • A) : Matrix (Fin n) (Fin n) ℝ) *ᵥ v)
      Filter.atTop (nhds 0) := by
    exact hdecay.comp hshift
  have hxeq : (fun t : ℝ =>
        (NormedSpace.exp (((t - 1) : ℝ) • A) : Matrix (Fin n) (Fin n) ℝ) *ᵥ v)
      =ᶠ[Filter.atTop] x := by
    filter_upwards [hformula] with t ht
    exact ht.symm
  have hxzero : Filter.Tendsto x Filter.atTop (nhds 0) := hmodel.congr' hxeq
  exact tendsto_norm_zero_of_tendsto_zero hxzero

lemma matrix_map_algebraMap_continuous (n : ℕ) :
    Continuous (fun M : Matrix (Fin n) (Fin n) ℝ => M.map (algebraMap ℝ ℂ)) := by
  simpa using (Continuous.matrix_map (m := Fin n) (n := Fin n)
    (A := fun M : Matrix (Fin n) (Fin n) ℝ => M) continuous_id
    Complex.continuous_ofReal)

lemma matrix_exp_map_algebraMap_real_complex (n : ℕ) (B : Matrix (Fin n) (Fin n) ℝ) :
    (NormedSpace.exp B : Matrix (Fin n) (Fin n) ℝ).map (algebraMap ℝ ℂ)
      = (NormedSpace.exp (B.map (algebraMap ℝ ℂ)) : Matrix (Fin n) (Fin n) ℂ) := by
  have h := NormedSpace.map_exp (RingHom.mapMatrix (algebraMap ℝ ℂ) :
      Matrix (Fin n) (Fin n) ℝ →+* Matrix (Fin n) (Fin n) ℂ)
      (matrix_map_algebraMap_continuous n) B
  simpa using h

lemma matrix_map_real_smul_algebraMap_real_complex (n : ℕ) (t : ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    ((t • A : Matrix (Fin n) (Fin n) ℝ).map (algebraMap ℝ ℂ))
      = t • (A.map (algebraMap ℝ ℂ) : Matrix (Fin n) (Fin n) ℂ) := by
  exact Matrix.map_smul (algebraMap ℝ ℂ) t (by intro a; norm_num) A

lemma complexification_exp_mulVec_real (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (v : Fin n → ℝ) (t : ℝ) :
    (fun i : Fin n => (((NormedSpace.exp (t • A) : Matrix (Fin n) (Fin n) ℝ) *ᵥ v) i : ℂ))
      = ((NormedSpace.exp (t • (A.map (algebraMap ℝ ℂ)) : Matrix (Fin n) (Fin n) ℂ))
          : Matrix (Fin n) (Fin n) ℂ) *ᵥ (fun i : Fin n => (v i : ℂ)) := by
  ext i
  have hmap := RingHom.map_mulVec (algebraMap ℝ ℂ)
      (NormedSpace.exp (t • A) : Matrix (Fin n) (Fin n) ℝ) v i
  rw [matrix_exp_map_algebraMap_real_complex n (t • A)] at hmap
  rw [matrix_map_real_smul_algebraMap_real_complex n t A] at hmap
  simpa [Function.comp_def] using hmap

lemma real_tendsto_zero_of_complexification_tendsto_zero {n : ℕ} {l : Filter ℝ}
    {f : ℝ → Fin n → ℝ}
    (hfC : Filter.Tendsto (fun t : ℝ => fun i : Fin n => ((f t i : ℝ) : ℂ)) l (nhds 0)) :
    Filter.Tendsto f l (nhds 0) := by
  rw [tendsto_pi_nhds]
  intro i
  have hiC : Filter.Tendsto (fun t : ℝ => ((f t i : ℝ) : ℂ)) l (nhds (0 : ℂ)) := by
    exact (continuous_apply i).tendsto 0 |>.comp hfC
  have hiR : Filter.Tendsto (fun t : ℝ => (((f t i : ℝ) : ℂ).re)) l (nhds ((0 : ℂ).re)) :=
    Complex.continuous_re.tendsto 0 |>.comp hiC
  simpa using hiR

noncomputable def complexExpDecaySubmodule (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) :
    Submodule ℂ (Fin n → ℂ) where
  carrier := {v | Filter.Tendsto
      (fun t : ℝ => (NormedSpace.exp (t • A) : Matrix (Fin n) (Fin n) ℂ) *ᵥ v)
      Filter.atTop (nhds 0)}
  zero_mem' := by
    simp
  add_mem' := by
    intro v w hv hw
    simpa [Matrix.mulVec_add] using hv.add hw
  smul_mem' := by
    intro c v hv
    simpa [Matrix.mulVec_smul] using hv.const_smul c

lemma complexExpDecaySubmodule_mem {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    {v : Fin n → ℂ} :
    v ∈ complexExpDecaySubmodule n A ↔ Filter.Tendsto
      (fun t : ℝ => (NormedSpace.exp (t • A) : Matrix (Fin n) (Fin n) ℂ) *ᵥ v)
      Filter.atTop (nhds 0) :=
  Iff.rfl

lemma polynomial_continuous_eval₂ {R S : Type*} [Semiring S] [TopologicalSpace R]
    [Semiring R] [IsTopologicalSemiring R] (p : Polynomial S) (f : S →+* R) :
    Continuous fun x => Polynomial.eval₂ f x p := by
  simp only [Polynomial.eval₂_eq_sum]
  exact continuous_finset_sum _ fun c _ => continuous_const.mul (continuous_pow _)

lemma polynomial_continuous {R : Type*} [Semiring R] [TopologicalSpace R]
    [IsTopologicalSemiring R] (p : Polynomial R) : Continuous fun x => Polynomial.eval x p :=
  polynomial_continuous_eval₂ p _

theorem polynomial_tendsto_abv_eval₂_atTop {R S k α : Type*} [Semiring R] [Ring S]
    [Field k] [LinearOrder k] [IsStrictOrderedRing k]
    (f : R →+* S) (abv : S → k) [IsAbsoluteValue abv] (p : Polynomial R) (hd : 0 < Polynomial.degree p)
    (hf : f (Polynomial.leadingCoeff p) ≠ 0) {l : Filter α} {z : α → S} (hz : Tendsto (abv ∘ z) l atTop) :
    Tendsto (fun x => abv (p.eval₂ f (z x))) l atTop := by
  revert hf; refine Polynomial.degree_pos_induction_on p hd ?_ ?_ ?_ <;> clear hd p
  · rintro _ - hc
    rw [Polynomial.leadingCoeff_mul_X, Polynomial.leadingCoeff_C] at hc
    simpa [abv_mul abv] using hz.const_mul_atTop ((abv_pos abv).2 hc)
  · intro _ _ ihp hf
    rw [Polynomial.leadingCoeff_mul_X] at hf
    simpa [abv_mul abv] using (ihp hf).atTop_mul_atTop₀ hz
  · intro _ a hd ihp hf
    rw [add_comm, Polynomial.leadingCoeff_add_of_degree_lt (Polynomial.degree_C_le.trans_lt hd)] at hf
    refine .atTop_of_add_const (abv (-f a)) ?_
    refine tendsto_atTop_mono (fun _ => abv_add abv _ _) ?_
    simpa using ihp hf

theorem polynomial_tendsto_norm_atTop {R α : Type*} [NormedRing R] [IsAbsoluteValue (norm : R → ℝ)]
    (p : Polynomial R) (h : 0 < Polynomial.degree p) {l : Filter α} {z : α → R}
    (hz : Tendsto (fun x => ‖z x‖) l atTop) : Tendsto (fun x => ‖p.eval (z x)‖) l atTop := by
  exact polynomial_tendsto_abv_eval₂_atTop (RingHom.id R) norm p h (by
    simpa using mt Polynomial.leadingCoeff_eq_zero.1 (Polynomial.ne_zero_of_degree_gt h)) hz

theorem polynomial_exists_forall_norm_le {R : Type*} [NormedRing R] [IsAbsoluteValue (norm : R → ℝ)]
    [ProperSpace R] (p : Polynomial R) : ∃ x, ∀ y, ‖Polynomial.eval x p‖ ≤ ‖p.eval y‖ :=
  if hp0 : 0 < Polynomial.degree p then
    (polynomial_continuous p).norm.exists_forall_le <| polynomial_tendsto_norm_atTop p hp0 tendsto_norm_cocompact_atTop
  else
    ⟨Polynomial.coeff p 0, by rw [Polynomial.eq_C_of_degree_le_zero (le_of_not_gt hp0)]; simp⟩

lemma complex_exists_pow_eq (k : ℕ) (hk : 0 < k) (z : ℂ) : ∃ w : ℂ, w ^ k = z := by
  by_cases hz : z = 0
  · refine ⟨0, ?_⟩
    simp [hz, hk.ne']
  · refine ⟨Complex.exp (Complex.log z / (k : ℂ)), ?_⟩
    rw [← Complex.exp_nat_mul]
    have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
    have hmul : (k : ℂ) * (Complex.log z / (k : ℂ)) = Complex.log z := by
      field_simp [hkC]
    rw [hmul, Complex.exp_log hz]

lemma complex_polynomial_local_descent {p : Polynomial ℂ} (hp : 0 < Polynomial.degree p)
    {z₀ : ℂ} (ha0 : Polynomial.eval z₀ p ≠ 0) :
    ∃ z : ℂ, ‖Polynomial.eval z p‖ < ‖Polynomial.eval z₀ p‖ := by
  classical
  let a : ℂ := Polynomial.eval z₀ p
  let q : Polynomial ℂ := Polynomial.comp p (Polynomial.X + Polynomial.C z₀)
  have hqeval (w : ℂ) : Polynomial.eval w q = Polynomial.eval (w + z₀) p := by
    dsimp [q]
    rw [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
  let r : Polynomial ℂ := q - Polynomial.C a
  have hrcoeff0 : Polynomial.coeff r 0 = 0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero]
    dsimp [r, a]
    simp [hqeval 0]
  have hrne : r ≠ 0 := by
    intro hr0
    have hqconst : q = Polynomial.C a := by
      dsimp [r] at hr0
      exact sub_eq_zero.mp hr0
    have hpconst : p = Polynomial.C a := by
      apply Polynomial.funext
      intro z
      have h := congr_arg (fun P : Polynomial ℂ => Polynomial.eval (z - z₀) P) hqconst
      simp [q, Polynomial.eval_comp] at h
      have hz : z - z₀ + z₀ = z := by abel
      simpa [a, hz] using h
    have hdeg_le : Polynomial.degree p ≤ 0 := by
      rw [hpconst]
      exact Polynomial.degree_C_le
    exact not_lt_of_ge hdeg_le hp
  let k : ℕ := Polynomial.natTrailingDegree r
  have hkpos : 0 < k := by
    have hkne : k ≠ 0 := by
      change Polynomial.natTrailingDegree r ≠ 0
      exact (Polynomial.natTrailingDegree_ne_zero).mpr ⟨hrne, hrcoeff0⟩
    exact Nat.pos_of_ne_zero hkne
  have hcoeffk : Polynomial.coeff r k ≠ 0 := by
    dsimp [k]
    exact (Polynomial.coeff_natTrailingDegree_ne_zero).mpr hrne
  have hXdiv : Polynomial.X ^ k ∣ r := by
    rw [Polynomial.X_pow_dvd_iff]
    intro d hd
    exact Polynomial.coeff_eq_zero_of_lt_natTrailingDegree (p := r) (by simpa [k] using hd)
  rcases hXdiv with ⟨s, hs⟩
  have hbne : Polynomial.eval 0 s ≠ 0 := by
    have hck : Polynomial.coeff (Polynomial.X ^ k * s) k ≠ 0 := by
      rw [← hs]
      exact hcoeffk
    have hcoeff : Polynomial.coeff (Polynomial.X ^ k * s) k = Polynomial.coeff s 0 := by
      have := Polynomial.coeff_X_pow_mul s k 0
      simpa using this
    have hs0 : Polynomial.coeff s 0 ≠ 0 := by
      rwa [hcoeff] at hck
    simpa [Polynomial.coeff_zero_eq_eval_zero] using hs0
  let b : ℂ := Polynomial.eval 0 s
  obtain ⟨θ, hθpow⟩ : ∃ θ : ℂ, θ ^ k = -a / b := complex_exists_pow_eq k hkpos (-a / b)
  have hθpow_ne : θ ^ k ≠ 0 := by
    have hdiv : -a / b ≠ 0 := div_ne_zero (neg_ne_zero.mpr ha0) hbne
    simpa [hθpow] using hdiv
  have hθnorm_pos : 0 < ‖θ ^ k‖ := norm_pos_iff.mpr hθpow_ne
  have hηpos : 0 < ‖a‖ / (2 * ‖θ ^ k‖) := by
    positivity
  have hcont : ContinuousAt (fun w : ℂ => Polynomial.eval w s) 0 :=
    (polynomial_continuous s).continuousAt
  have hlim : Tendsto (fun w : ℂ => Polynomial.eval w s - b) (nhds 0) (nhds 0) := by
    simpa [b] using hcont.tendsto.sub (tendsto_const_nhds (x := b))
  have hev : ∀ᶠ w : ℂ in nhds 0, ‖Polynomial.eval w s - b‖ < ‖a‖ / (2 * ‖θ ^ k‖) := by
    simpa [dist_eq_norm] using (Metric.tendsto_nhds.mp hlim) _ hηpos
  rcases Metric.mem_nhds_iff.mp hev with ⟨δ, hδpos, hδ⟩
  let ε : ℝ := min (1 / 2) (δ / (2 * (‖θ‖ + 1)))
  have hεpos : 0 < ε := by
    dsimp [ε]
    refine lt_min (by norm_num) ?_
    positivity
  have hεlt1 : ε < 1 := by
    dsimp [ε]
    exact lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hεle : ε ≤ δ / (2 * (‖θ‖ + 1)) := by
    dsimp [ε]
    exact min_le_right _ _
  let w : ℂ := (ε : ℂ) * θ
  have hwnhds : w ∈ Metric.ball (0 : ℂ) δ := by
    have hnormθ_nonneg : 0 ≤ ‖θ‖ := norm_nonneg θ
    have hdenpos : 0 < 2 * (‖θ‖ + 1) := by positivity
    have hw_le : ‖w‖ ≤ δ / 2 := by
      dsimp [w]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hεpos]
      have hmul := mul_le_mul_of_nonneg_right hεle hnormθ_nonneg
      calc
        ε * ‖θ‖ ≤ (δ / (2 * (‖θ‖ + 1))) * ‖θ‖ := hmul
        _ ≤ δ / 2 := by
          have hδnonneg : 0 ≤ δ := le_of_lt hδpos
          have hfrac : ‖θ‖ / (‖θ‖ + 1) ≤ 1 := by
            have hpos : 0 < ‖θ‖ + 1 := by positivity
            rw [div_le_one hpos]
            linarith [norm_nonneg θ]
          calc
            (δ / (2 * (‖θ‖ + 1))) * ‖θ‖ = (δ / 2) * (‖θ‖ / (‖θ‖ + 1)) := by field_simp [ne_of_gt hdenpos, ne_of_gt (by positivity : 0 < ‖θ‖ + 1)]
            _ ≤ (δ / 2) * 1 := by
              exact mul_le_mul_of_nonneg_left hfrac (by positivity)
            _ = δ / 2 := by ring
    have hw_lt : ‖w‖ < δ := lt_of_le_of_lt hw_le (by linarith)
    simpa [Metric.mem_ball, dist_eq_norm] using hw_lt
  have hsdiff : ‖Polynomial.eval w s - b‖ < ‖a‖ / (2 * ‖θ ^ k‖) := hδ hwnhds
  refine ⟨w + z₀, ?_⟩
  have hq_formula : Polynomial.eval w q = a + w ^ k * Polynomial.eval w s := by
    calc
      Polynomial.eval w q = Polynomial.eval w (r + Polynomial.C a) := by
        dsimp [r]
        rw [sub_add_cancel]
      _ = Polynomial.eval w r + a := by simp [a]
      _ = Polynomial.eval w (Polynomial.X ^ k * s) + a := by rw [hs]
      _ = w ^ k * Polynomial.eval w s + a := by simp [Polynomial.eval_mul]
      _ = a + w ^ k * Polynomial.eval w s := by ring
  have hbθ : b * θ ^ k = -a := by
    rw [hθpow]
    dsimp [b]
    field_simp [hbne]
  have hw_pow : w ^ k = (ε : ℂ) ^ k * θ ^ k := by
    dsimp [w]
    rw [mul_pow]
  have hmain_eq : Polynomial.eval (w + z₀) p = (1 - (ε : ℂ) ^ k) * a + ((ε : ℂ) ^ k * θ ^ k) * (Polynomial.eval w s - b) := by
    rw [← hqeval w, hq_formula, hw_pow]
    rw [mul_sub]
    have hthis : ((ε : ℂ) ^ k * θ ^ k) * b = -((ε : ℂ) ^ k * a) := by
      calc
        ((ε : ℂ) ^ k * θ ^ k) * b = (ε : ℂ) ^ k * (b * θ ^ k) := by ring
        _ = (ε : ℂ) ^ k * (-a) := by rw [hbθ]
        _ = -((ε : ℂ) ^ k * a) := by ring
    rw [hthis]
    ring
  rw [hmain_eq]
  have hεpow_pos : 0 < ε ^ k := pow_pos hεpos k
  have hεpow_lt1 : ε ^ k < 1 := by
    exact pow_lt_one₀ (le_of_lt hεpos) hεlt1 hkpos.ne'
  have hfirst_norm : ‖(1 - (ε : ℂ) ^ k) * a‖ = (1 - ε ^ k) * ‖a‖ := by
    rw [norm_mul]
    have hcast : (1 : ℂ) - (ε : ℂ) ^ k = ((1 - ε ^ k : ℝ) : ℂ) := by norm_cast
    rw [hcast, Complex.norm_real, Real.norm_eq_abs]
    have hnonneg : 0 ≤ 1 - ε ^ k := by linarith
    rw [abs_of_nonneg hnonneg]
  have hsecond_le : ‖((ε : ℂ) ^ k * θ ^ k) * (Polynomial.eval w s - b)‖ < (ε ^ k) * (‖a‖ / 2) := by
    rw [norm_mul, norm_mul]
    have hcastε : ((ε : ℂ) ^ k) = ((ε ^ k : ℝ) : ℂ) := by norm_cast
    rw [hcastε, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hεpow_pos]
    have hmul := mul_lt_mul_of_pos_left hsdiff (mul_pos hεpow_pos hθnorm_pos)
    calc
      ε ^ k * ‖θ ^ k‖ * ‖Polynomial.eval w s - b‖
          < ε ^ k * ‖θ ^ k‖ * (‖a‖ / (2 * ‖θ ^ k‖)) := by
        simpa [mul_assoc] using hmul
      _ = ε ^ k * (‖a‖ / 2) := by
        field_simp [ne_of_gt hθnorm_pos]
  calc
    ‖(1 - (ε : ℂ) ^ k) * a + ((ε : ℂ) ^ k * θ ^ k) * (Polynomial.eval w s - b)‖
        ≤ ‖(1 - (ε : ℂ) ^ k) * a‖ + ‖((ε : ℂ) ^ k * θ ^ k) * (Polynomial.eval w s - b)‖ := norm_add_le _ _
    _ < (1 - ε ^ k) * ‖a‖ + ε ^ k * (‖a‖ / 2) := by
      exact add_lt_add_of_le_of_lt (le_of_eq hfirst_norm) hsecond_le
    _ < ‖a‖ := by
      have ha_norm_pos : 0 < ‖a‖ := norm_pos_iff.mpr ha0
      nlinarith [hεpow_pos, ha_norm_pos]

lemma complex_polynomial_exists_root {p : Polynomial ℂ} (hp : 0 < Polynomial.degree p) :
    ∃ z : ℂ, Polynomial.eval z p = 0 := by
  classical
  obtain ⟨z₀, hmin⟩ := polynomial_exists_forall_norm_le p
  by_contra h
  push Not at h
  obtain ⟨z, hzlt⟩ := complex_polynomial_local_descent hp (h z₀)
  have := hmin z
  linarith

noncomputable def detSubScalarPoly (m : ℕ) (M : Matrix (Fin m) (Fin m) ℂ) : Polynomial ℂ :=
  Matrix.det ((Polynomial.X : Polynomial ℂ) • (1 : Matrix (Fin m) (Fin m) (Polynomial ℂ)) + (-M).map Polynomial.C)

lemma detSubScalarPoly_degree_pos (m : ℕ) (M : Matrix (Fin m) (Fin m) ℂ) (hm : 0 < m) :
    0 < Polynomial.degree (detSubScalarPoly m M) := by
  classical
  have hcoeff : Polynomial.coeff (detSubScalarPoly m M) m = (1 : ℂ) := by
    dsimp [detSubScalarPoly]
    simpa using (Polynomial.coeff_det_X_add_C_card (A := (1 : Matrix (Fin m) (Fin m) ℂ)) (B := -M))
  have hle : (m : WithBot ℕ) ≤ Polynomial.degree (detSubScalarPoly m M) := by
    exact Polynomial.le_degree_of_ne_zero (p := detSubScalarPoly m M) (n := m) (by rw [hcoeff]; exact one_ne_zero)
  have hposm : (0 : WithBot ℕ) < (m : WithBot ℕ) := by
    exact_mod_cast hm
  exact lt_of_lt_of_le hposm hle

lemma detSubScalarPoly_eval (m : ℕ) (M : Matrix (Fin m) (Fin m) ℂ) (μ : ℂ) :
    Polynomial.eval μ (detSubScalarPoly m M) = (μ • (1 : Matrix (Fin m) (Fin m) ℂ) - M).det := by
  classical
  dsimp [detSubScalarPoly]
  have h := RingHom.map_det (Polynomial.evalRingHom μ)
      ((Polynomial.X : Polynomial ℂ) • (1 : Matrix (Fin m) (Fin m) (Polynomial ℂ)) + (-M).map Polynomial.C)
  change (Polynomial.evalRingHom μ) ((Polynomial.X : Polynomial ℂ) • (1 : Matrix (Fin m) (Fin m) (Polynomial ℂ)) + (-M).map Polynomial.C).det = (μ • (1 : Matrix (Fin m) (Fin m) ℂ) - M).det
  rw [h]
  congr 1
  ext i j
  by_cases hij : i = j
  · subst j
    simp
    ring
  · simp [hij]

lemma complex_matrix_det_sub_scalar_exists_zero (m : ℕ) (M : Matrix (Fin m) (Fin m) ℂ)
    (hm : 0 < m) :
    ∃ μ : ℂ, (M - μ • (1 : Matrix (Fin m) (Fin m) ℂ)).det = 0 := by
  classical
  obtain ⟨μ, hμ⟩ := complex_polynomial_exists_root (detSubScalarPoly_degree_pos m M hm)
  refine ⟨μ, ?_⟩
  have hdet1 : (μ • (1 : Matrix (Fin m) (Fin m) ℂ) - M).det = 0 := by
    simpa [detSubScalarPoly_eval] using hμ
  have hneg : M - μ • (1 : Matrix (Fin m) (Fin m) ℂ) = - (μ • (1 : Matrix (Fin m) (Fin m) ℂ) - M) := by
    ext i j
    simp
  rw [hneg, Matrix.det_neg]
  simp [hdet1]


lemma not_isUnit_of_eq_zero_field {K : Type*} [Field K] {a : K} (ha : a = 0) :
    ¬ IsUnit a := by
  intro h
  rw [ha] at h
  exact not_isUnit_zero h

lemma complex_basis_matrix_exists_eigenvalue {m : ℕ} {V : Type*} [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V]
    (b : Module.Basis (Fin m) ℂ V) (M : Matrix (Fin m) (Fin m) ℂ) (hm : 0 < m) :
    ∃ μ : ℂ, Module.End.HasEigenvalue ((Matrix.toLinAlgEquiv b) M : Module.End ℂ V) μ := by
  obtain ⟨μ, hdet⟩ := complex_matrix_det_sub_scalar_exists_zero m M hm
  refine ⟨μ, ?_⟩
  let N : Matrix (Fin m) (Fin m) ℂ := M - μ • (1 : Matrix (Fin m) (Fin m) ℂ)
  have hNdet : N.det = 0 := by simpa [N] using hdet
  have hN_not_unit : ¬ IsUnit N := by
    intro hunit
    have hdetunit : IsUnit N.det := (Matrix.isUnit_iff_isUnit_det N).mp hunit
    rw [hNdet] at hdetunit
    exact not_isUnit_zero hdetunit
  have hlin_not_unit : ¬ IsUnit (((Matrix.toLinAlgEquiv b) N) : Module.End ℂ V) := by
    intro hunit
    have hpre : IsUnit N := by
      have hmapped :
          IsUnit ((Matrix.toLinAlgEquiv b).symm
            (((Matrix.toLinAlgEquiv b) N) : Module.End ℂ V)) :=
        IsUnit.map
          ((Matrix.toLinAlgEquiv b).symm : (Module.End ℂ V) →+* Matrix (Fin m) (Fin m) ℂ)
          hunit
      simpa using hmapped
    exact hN_not_unit hpre
  have hker_ne :
      LinearMap.ker (((Matrix.toLinAlgEquiv b) N) : Module.End ℂ V) ≠ ⊥ := by
    intro hker
    exact hlin_not_unit
      ((LinearMap.isUnit_iff_ker_eq_bot (((Matrix.toLinAlgEquiv b) N) : Module.End ℂ V)).mpr
        hker)
  have hNlin : (((Matrix.toLinAlgEquiv b) N) : Module.End ℂ V) =
      ((Matrix.toLinAlgEquiv b) M : Module.End ℂ V) - μ • 1 := by
    dsimp [N]
    rw [map_sub, map_smul, map_one]
  rw [Module.End.hasEigenvalue_iff, Module.End.eigenspace, Module.End.genEigenspace_one,
    ← hNlin]
  exact hker_ne

lemma complex_end_exists_eigenvalue {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [Nontrivial V] (f : Module.End ℂ V) :
    ∃ μ : ℂ, f.HasEigenvalue μ := by
  classical
  let d : ℕ := Module.finrank ℂ V
  have hd : 0 < d := Module.finrank_pos_iff.mpr (by infer_instance)
  let b : Module.Basis (Fin d) ℂ V := Module.finBasis ℂ V
  let M : Matrix (Fin d) (Fin d) ℂ := (LinearMap.toMatrixAlgEquiv b) f
  obtain ⟨μ, hμ⟩ := complex_basis_matrix_exists_eigenvalue b M hd
  refine ⟨μ, ?_⟩
  have hfM : ((Matrix.toLinAlgEquiv b) M : Module.End ℂ V) = f := by
    dsimp [M]
    exact Matrix.toLinAlgEquiv_toMatrixAlgEquiv b f
  simpa [hfM] using hμ

theorem complex_iSup_maxGenEigenspace_eq_top {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (f : Module.End ℂ V) :
    ⨆ (μ : ℂ), f.maxGenEigenspace μ = ⊤ := by
  classical
  suffices ∀ n : ℕ, Module.finrank ℂ V = n → ⨆ (μ : ℂ), f.maxGenEigenspace μ = ⊤ by
    exact this _ rfl
  intro n h_dim
  induction n using Nat.strong_induction_on generalizing V with
  | h n ih =>
      rcases n with _ | n
      · rw [← top_le_iff]
        simp only [Submodule.finrank_eq_zero.1 (Eq.trans (finrank_top ℂ V) h_dim), bot_le]
      · haveI : Nontrivial V := Module.finrank_pos_iff.mp (by
          rw [h_dim]
          exact Nat.succ_pos n)
        obtain ⟨μ₀, hμ₀⟩ : ∃ μ₀ : ℂ, f.HasEigenvalue μ₀ :=
          complex_end_exists_eigenvalue f
        let ES := f.genEigenspace μ₀ (Module.finrank ℂ V)
        let ER := f.genEigenrange μ₀ (Module.finrank ℂ V)
        have h_f_ER : ∀ x : V, x ∈ ER → f x ∈ ER := fun x hx =>
          Module.End.map_genEigenrange_le (Submodule.mem_map_of_mem hx)
        let f' : Module.End ℂ ER := f.restrict h_f_ER
        have h_dim_ES_pos : 0 < Module.finrank ℂ ES := by
          dsimp +instances only [ES]
          rw [h_dim]
          exact Module.End.pos_finrank_genEigenspace_of_hasEigenvalue hμ₀ (Nat.succ_pos n)
        have h_dim_add : Module.finrank ℂ ER + Module.finrank ℂ ES = Module.finrank ℂ V := by
          dsimp +instances only [ER, ES]
          rw [Module.End.genEigenspace_nat, Module.End.genEigenrange_nat]
          exact LinearMap.finrank_range_add_finrank_ker ((f - μ₀ • 1) ^ Module.finrank ℂ V)
        have h_dim_ER : Module.finrank ℂ ER < n.succ := by
          rw [h_dim] at h_dim_add
          omega
        have ih_ER : ⨆ (μ : ℂ), f'.maxGenEigenspace μ = ⊤ :=
          ih (Module.finrank ℂ ER) h_dim_ER f' rfl
        have ih_ER' : ⨆ (μ : ℂ), (f'.maxGenEigenspace μ).map ER.subtype = ER := by
          simp only [(Submodule.map_iSup _ _).symm, ih_ER, Submodule.map_subtype_top ER]
        have hff' :
            ∀ μ : ℂ, (f'.maxGenEigenspace μ).map ER.subtype ≤ f.maxGenEigenspace μ := by
          intro μ
          rw [Module.End.maxGenEigenspace, Module.End.genEigenspace_restrict]
          exact Submodule.map_comap_le ER.subtype (f.maxGenEigenspace μ)
        have hER : ER ≤ ⨆ (μ : ℂ), f.maxGenEigenspace μ := by
          rw [← ih_ER']
          exact iSup_mono hff'
        have hES : ES ≤ ⨆ (μ : ℂ), f.maxGenEigenspace μ :=
          ((f.genEigenspace μ₀).mono le_top).trans (le_iSup f.maxGenEigenspace μ₀)
        have h_disjoint : Disjoint ER ES :=
          Module.End.generalized_eigenvec_disjoint_range_ker f μ₀
        change ⨆ (μ : ℂ), f.maxGenEigenspace μ = ⊤
        rw [← top_le_iff, ← Submodule.eq_top_of_disjoint ER ES h_dim_add.ge h_disjoint]
        exact sup_le hER hES

lemma complex_matrix_exp_mulVec_tendsto_zero_of_iSup_maxGen_le_decay (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℂ)
    (htop : ⨆ μ : ℂ,
      Module.End.maxGenEigenspace (Matrix.toLin' A : Module.End ℂ (Fin n → ℂ)) μ = ⊤)
    (hgen : ∀ μ : ℂ,
      Module.End.maxGenEigenspace (Matrix.toLin' A : Module.End ℂ (Fin n → ℂ)) μ
        ≤ complexExpDecaySubmodule n A)
    (v : Fin n → ℂ) :
    Filter.Tendsto
      (fun t : ℝ => (NormedSpace.exp (t • A) : Matrix (Fin n) (Fin n) ℂ) *ᵥ v)
      Filter.atTop (nhds 0) := by
  have hvtop : v ∈ (⨆ μ : ℂ,
      Module.End.maxGenEigenspace (Matrix.toLin' A : Module.End ℂ (Fin n → ℂ)) μ) := by
    simpa [htop]
  exact (complexExpDecaySubmodule_mem).mp
    (((Submodule.mem_iSup
      (fun μ : ℂ =>
        Module.End.maxGenEigenspace (Matrix.toLin' A : Module.End ℂ (Fin n → ℂ)) μ)).mp
        hvtop) (complexExpDecaySubmodule n A) hgen)

lemma re_neg_of_mem_maxGenEigenspace_ne_zero {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : ∀ μ : ℂ,
      Module.End.HasEigenvalue (Matrix.toLin' A : Module.End ℂ (Fin n → ℂ)) μ → μ.re < 0)
    {μ : ℂ} {v : Fin n → ℂ}
    (hv : v ∈ Module.End.maxGenEigenspace
      (Matrix.toLin' A : Module.End ℂ (Fin n → ℂ)) μ)
    (hv0 : v ≠ 0) : μ.re < 0 := by
  rw [Module.End.mem_maxGenEigenspace] at hv
  rcases hv with ⟨k, hk⟩
  have hvgen : v ∈
      (Module.End.genEigenspace (Matrix.toLin' A : Module.End ℂ (Fin n → ℂ)) μ)
        (k : ℕ∞) := by
    rw [Module.End.mem_genEigenspace_nat]
    exact hk
  have hne :
      (Module.End.genEigenspace (Matrix.toLin' A : Module.End ℂ (Fin n → ℂ)) μ)
        (k : ℕ∞) ≠ ⊥ := by
    intro hbot
    have : v = 0 := by
      rw [← Submodule.mem_bot (R := ℂ), ← hbot]
      exact hvgen
    exact hv0 this
  have hHasGen :
      Module.End.HasGenEigenvalue
        (Matrix.toLin' A : Module.End ℂ (Fin n → ℂ)) μ k := by
    rwa [Module.End.hasGenEigenvalue_iff]
  exact hA μ (Module.End.hasEigenvalue_of_hasGenEigenvalue hHasGen)

lemma real_pow_exp_neg_const_tendsto_zero (k : ℕ) {c : ℝ} (hc : 0 < c) :
    Filter.Tendsto (fun t : ℝ => t ^ k * Real.exp (-(c * t))) Filter.atTop (nhds 0) := by
  have hbase := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k
  have hct : Filter.Tendsto (fun t : ℝ => c * t) Filter.atTop Filter.atTop := by
    exact Filter.Tendsto.const_mul_atTop hc Filter.tendsto_id
  have hcomp := hbase.comp hct
  have hscale : Filter.Tendsto
      (fun t : ℝ => (c ^ k)⁻¹ * ((c * t) ^ k * Real.exp (-(c * t))))
      Filter.atTop (nhds ((c ^ k)⁻¹ * 0)) := by
    exact hcomp.const_mul _
  have hcpow_ne : c ^ k ≠ 0 := pow_ne_zero k (ne_of_gt hc)
  have heq : (fun t : ℝ => t ^ k * Real.exp (-(c * t))) =ᶠ[Filter.atTop]
      (fun t : ℝ => (c ^ k)⁻¹ * ((c * t) ^ k * Real.exp (-(c * t)))) := by
    filter_upwards [] with t
    rw [mul_pow]
    field_simp [hcpow_ne]
  simpa using hscale.congr' heq.symm

lemma complex_pow_mul_cexp_tendsto_zero_of_re_neg (k : ℕ) {μ : ℂ} (hμ : μ.re < 0) :
    Filter.Tendsto (fun t : ℝ => (t : ℂ) ^ k * Complex.exp ((t : ℂ) * μ))
      Filter.atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  let c : ℝ := - μ.re
  have hc : 0 < c := by dsimp [c]; linarith
  have hreal : Filter.Tendsto (fun t : ℝ => t ^ k * Real.exp (-(c * t))) Filter.atTop (nhds 0) :=
    real_pow_exp_neg_const_tendsto_zero k hc
  have hnormeq : (fun t : ℝ => ‖(t : ℂ) ^ k * Complex.exp ((t : ℂ) * μ)‖)
      =ᶠ[Filter.atTop] (fun t : ℝ => t ^ k * Real.exp (-(c * t))) := by
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
    rw [norm_mul, norm_pow, Complex.norm_exp]
    have hnorm_t : ‖(t : ℂ)‖ = t := by
      simp [Real.norm_eq_abs, abs_of_nonneg ht]
    have hre : (((t : ℂ) * μ).re) = -(c * t) := by
      simp [Complex.mul_re, c]
      ring
    rw [hnorm_t, hre]
  exact hreal.congr' hnormeq.symm

theorem cauSeq_tendsto_limit_local {β : Type*} [NormedRing β]
    [hn : IsAbsoluteValue (norm : β → ℝ)]
    (f : CauSeq β norm) [CauSeq.IsComplete β norm] : Tendsto f atTop (𝓝 f.lim) :=
  tendsto_nhds.mpr
    (by
      intro s os lfs
      suffices ∃ a : ℕ, ∀ b : ℕ, b ≥ a → f b ∈ s by simpa using this
      rcases Metric.isOpen_iff.1 os _ lfs with ⟨ε, ⟨hε, hεs⟩⟩
      obtain ⟨N, hN⟩ := Setoid.symm (CauSeq.equiv_lim f) _ hε
      exists N
      intro b hb
      apply hεs
      dsimp [Metric.ball]
      rw [dist_comm, dist_eq_norm]
      exact hN b hb)

namespace NormedSpace

theorem complex_exp_eq_normedSpace_exp_local : Complex.exp = NormedSpace.exp := by
  refine funext fun x => ?_
  rw [Complex.exp, NormedSpace.exp_eq_tsum_div]
  exact tendsto_nhds_unique (cauSeq_tendsto_limit_local (Complex.exp' x))
    (NormedSpace.expSeries_div_summable x).hasSum.tendsto_sum_nat

theorem real_exp_eq_normedSpace_exp_local : Real.exp = NormedSpace.exp := by
  ext x
  exact mod_cast congr_fun complex_exp_eq_normedSpace_exp_local x

end NormedSpace

lemma complex_pow_mul_normed_exp_tendsto_zero_of_re_neg (k : ℕ) {μ : ℂ} (hμ : μ.re < 0) :
    Filter.Tendsto (fun t : ℝ => (t : ℂ) ^ k * (NormedSpace.exp ((t : ℂ) * μ) : ℂ))
      Filter.atTop (nhds 0) := by
  have h := complex_pow_mul_cexp_tendsto_zero_of_re_neg k hμ
  simpa [NormedSpace.complex_exp_eq_normedSpace_exp_local] using h

lemma matrix_exp_scalar_complex (n : ℕ) (z : ℂ) :
    (NormedSpace.exp (z • (1 : Matrix (Fin n) (Fin n) ℂ)) : Matrix (Fin n) (Fin n) ℂ)
      = (NormedSpace.exp z : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  rw [← Matrix.diagonal_one]
  simp only [← Matrix.diagonal_smul]
  rw [Matrix.exp_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    simp
  · simp [Matrix.diagonal, hij]

noncomputable def matrixMulVecRightCLM_complex (n : ℕ) (v : Fin n → ℂ) :
    Matrix (Fin n) (Fin n) ℂ →L[ℂ] (Fin n → ℂ) :=
  ContinuousLinearMap.mk ((Matrix.mulVecBilin ℂ ℂ).flip v)
    (by
      simpa using (continuous_id.matrix_mulVec
        (continuous_const : Continuous fun _ : Matrix (Fin n) (Fin n) ℂ => v)))

lemma matrix_pow_mulVec_eq_zero_of_le {n k j : ℕ} (N : Matrix (Fin n) (Fin n) ℂ)
    (v : Fin n → ℂ) (hNv : N ^ k *ᵥ v = 0) (hkj : k ≤ j) :
    N ^ j *ᵥ v = 0 := by
  have hj : j = (j - k) + k := by omega
  rw [hj, pow_add, ← Matrix.mulVec_mulVec]
  simp [hNv]

lemma matrix_exp_smul_nilpotent_on_vector_eq_sum (n k : ℕ)
    (N : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ)
    (hNv : N ^ k *ᵥ v = 0) (t : ℂ) :
    ((NormedSpace.exp (t • N) : Matrix (Fin n) (Fin n) ℂ) *ᵥ v) =
      ∑ j ∈ Finset.range k, ((((j.factorial : ℂ)⁻¹) * t ^ j) • (N ^ j *ᵥ v)) := by
  let L := matrixMulVecRightCLM_complex n v
  have hs : Summable fun j : ℕ =>
      ((j.factorial : ℂ)⁻¹) • ((t • N) ^ j : Matrix (Fin n) (Fin n) ℂ) := by
    have hs_norm : Summable (fun j : ℕ =>
        ‖((j.factorial : ℂ)⁻¹) • ((t • N) ^ j : Matrix (Fin n) (Fin n) ℂ)‖) :=
      NormedSpace.norm_expSeries_summable' (𝕂 := ℂ)
        (𝔸 := Matrix (Fin n) (Fin n) ℂ) (t • N)
    exact @Summable.of_norm ℕ (Matrix (Fin n) (Fin n) ℂ) _
      (FiniteDimensional.complete ℂ _) _ hs_norm
  calc
    ((NormedSpace.exp (t • N) : Matrix (Fin n) (Fin n) ℂ) *ᵥ v)
        = L (NormedSpace.exp (t • N) : Matrix (Fin n) (Fin n) ℂ) := by rfl
    _ = L (∑' j : ℕ,
        ((j.factorial : ℂ)⁻¹) • ((t • N) ^ j : Matrix (Fin n) (Fin n) ℂ)) := by
      rw [NormedSpace.exp_eq_tsum ℂ]
    _ = ∑' j : ℕ, L (((j.factorial : ℂ)⁻¹) •
        ((t • N) ^ j : Matrix (Fin n) (Fin n) ℂ)) := by
      rw [ContinuousLinearMap.map_tsum L hs]
    _ = ∑ j ∈ Finset.range k, ((((j.factorial : ℂ)⁻¹) * t ^ j) •
        (N ^ j *ᵥ v)) := by
      rw [tsum_eq_sum]
      · apply Finset.sum_congr rfl
        intro j hj
        dsimp [L, matrixMulVecRightCLM_complex]
        rw [smul_pow, Matrix.smul_mulVec, Matrix.smul_mulVec, ← smul_smul]
      · intro j hj
        dsimp [L, matrixMulVecRightCLM_complex]
        have hkj : k ≤ j := not_lt.mp (by simpa [Finset.mem_range] using hj)
        have hz : N ^ j *ᵥ v = 0 := matrix_pow_mulVec_eq_zero_of_le N v hNv hkj
        rw [smul_pow, Matrix.smul_mulVec, Matrix.smul_mulVec]
        simp [hz]

lemma matrix_exp_gen_formula (n k : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) (μ : ℂ)
    (v : Fin n → ℂ)
    (hNv : (A - μ • (1 : Matrix (Fin n) (Fin n) ℂ)) ^ k *ᵥ v = 0) (t : ℂ) :
    ((NormedSpace.exp (t • A) : Matrix (Fin n) (Fin n) ℂ) *ᵥ v) =
      (NormedSpace.exp (t * μ) : ℂ) •
        (∑ j ∈ Finset.range k, ((((j.factorial : ℂ)⁻¹) * t ^ j) •
          ((A - μ • (1 : Matrix (Fin n) (Fin n) ℂ)) ^ j *ᵥ v))) := by
  let N : Matrix (Fin n) (Fin n) ℂ := A - μ • (1 : Matrix (Fin n) (Fin n) ℂ)
  have hA : A = μ • (1 : Matrix (Fin n) (Fin n) ℂ) + N := by
    dsimp [N]
    abel
  have hsplit : t • A = (t * μ) • (1 : Matrix (Fin n) (Fin n) ℂ) + t • N := by
    rw [hA, smul_add, smul_smul]
  rw [hsplit]
  have hcomm : Commute ((t * μ) • (1 : Matrix (Fin n) (Fin n) ℂ)) (t • N) :=
    (Commute.one_left (t • N)).smul_left (t * μ)
  rw [Matrix.exp_add_of_commute _ _ hcomm]
  rw [matrix_exp_scalar_complex n (t * μ)]
  rw [← Matrix.mulVec_mulVec]
  rw [Matrix.smul_mulVec]
  simp only [Matrix.one_mulVec]
  congr 1
  exact matrix_exp_smul_nilpotent_on_vector_eq_sum n k N v (by simpa [N] using hNv) t

lemma tendsto_finset_sum_zero {ι α E : Type*} [AddCommMonoid E] [TopologicalSpace E]
    [ContinuousAdd E] {l : Filter α} (s : Finset ι) (f : ι → α → E)
    (hf : ∀ i ∈ s, Filter.Tendsto (f i) l (nhds 0)) :
    Filter.Tendsto (fun a => ∑ i ∈ s, f i a) l (nhds 0) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using
        (tendsto_const_nhds :
          Filter.Tendsto (fun _ : α => (0 : E)) l (nhds 0))
  | insert i s his ih =>
      have hi : Filter.Tendsto (f i) l (nhds 0) := hf i (by simp [his])
      have hs : Filter.Tendsto (fun a => ∑ j ∈ s, f j a) l (nhds 0) :=
        ih (by intro j hj; exact hf j (by simp [hj]))
      simpa [Finset.sum_insert, his] using hi.add hs

lemma scalar_poly_normed_exp_smul_tendsto_zero {n : ℕ} (j : ℕ) {μ : ℂ}
    (hμ : μ.re < 0) (w : Fin n → ℂ) :
    Filter.Tendsto (fun t : ℝ =>
      ((NormedSpace.exp ((t : ℂ) * μ) : ℂ) * (((j.factorial : ℂ)⁻¹) * (t : ℂ) ^ j)) • w)
      Filter.atTop (nhds 0) := by
  have hbase := complex_pow_mul_normed_exp_tendsto_zero_of_re_neg j hμ
  have hscale : Filter.Tendsto
      (fun t : ℝ => ((j.factorial : ℂ)⁻¹) *
        ((t : ℂ) ^ j * (NormedSpace.exp ((t : ℂ) * μ) : ℂ)))
      Filter.atTop (nhds 0) := by
    simpa using hbase.const_mul ((j.factorial : ℂ)⁻¹)
  have hscalar : Filter.Tendsto
      (fun t : ℝ => (NormedSpace.exp ((t : ℂ) * μ) : ℂ) *
        (((j.factorial : ℂ)⁻¹) * (t : ℂ) ^ j))
      Filter.atTop (nhds 0) := by
    refine hscale.congr' ?_
    filter_upwards [] with t
    ring
  simpa using hscalar.smul
    (tendsto_const_nhds : Filter.Tendsto (fun _ : ℝ => w) Filter.atTop (nhds w))

lemma maxGenEigenspace_le_complexExpDecaySubmodule_of_re_neg (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ μ : ℂ, Module.End.HasEigenvalue (Matrix.toLin' A) μ → μ.re < 0)
    (μ : ℂ) :
    Module.End.maxGenEigenspace (Matrix.toLin' A : Module.End ℂ (Fin n → ℂ)) μ
      ≤ complexExpDecaySubmodule n A := by
  intro v hv
  by_cases hv0 : v = 0
  · subst v
    exact (complexExpDecaySubmodule n A).zero_mem
  have hμ : μ.re < 0 := re_neg_of_mem_maxGenEigenspace_ne_zero hA hv hv0
  rw [Module.End.mem_maxGenEigenspace] at hv
  rcases hv with ⟨k, hk⟩
  have hNlin : Matrix.toLin' (A - μ • (1 : Matrix (Fin n) (Fin n) ℂ)) =
      (Matrix.toLin' A : Module.End ℂ (Fin n → ℂ)) - μ • 1 := by
    ext w i
    simp [Matrix.toLin'_apply]
  have hNv : (A - μ • (1 : Matrix (Fin n) (Fin n) ℂ)) ^ k *ᵥ v = 0 := by
    rw [← Matrix.toLin'_apply, Matrix.toLin'_pow, hNlin]
    exact hk
  have hmodel : Filter.Tendsto (fun t : ℝ =>
      (NormedSpace.exp ((t : ℂ) • A) : Matrix (Fin n) (Fin n) ℂ) *ᵥ v)
      Filter.atTop (nhds 0) := by
    have hformula : (fun t : ℝ =>
        (NormedSpace.exp ((t : ℂ) • A) : Matrix (Fin n) (Fin n) ℂ) *ᵥ v) =
        (fun t : ℝ => (NormedSpace.exp ((t : ℂ) * μ) : ℂ) •
          (∑ j ∈ Finset.range k, ((((j.factorial : ℂ)⁻¹) * (t : ℂ) ^ j) •
            ((A - μ • (1 : Matrix (Fin n) (Fin n) ℂ)) ^ j *ᵥ v)))) := by
      funext t
      exact matrix_exp_gen_formula n k A μ v hNv (t : ℂ)
    rw [hformula]
    simp_rw [Finset.smul_sum]
    simp_rw [smul_smul]
    exact tendsto_finset_sum_zero (α := ℝ) (E := Fin n → ℂ) (l := Filter.atTop)
      (Finset.range k)
      (fun j (t : ℝ) =>
        ((NormedSpace.exp ((t : ℂ) * μ) : ℂ) *
          (((j.factorial : ℂ)⁻¹) * (t : ℂ) ^ j)) •
          ((A - μ • (1 : Matrix (Fin n) (Fin n) ℂ)) ^ j *ᵥ v))
      (by
        intro j hj
        exact scalar_poly_normed_exp_smul_tendsto_zero j hμ _)
  refine hmodel.congr' ?_
  filter_upwards [] with t
  congr 2

lemma complex_matrix_exp_mulVec_tendsto_zero_of_re_neg (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ μ : ℂ, Module.End.HasEigenvalue (Matrix.toLin' A) μ → μ.re < 0)
    (v : Fin n → ℂ) :
    Filter.Tendsto
      (fun t : ℝ => (NormedSpace.exp (t • A) : Matrix (Fin n) (Fin n) ℂ) *ᵥ v)
      Filter.atTop (nhds 0) := by
  classical
  by_cases hn : n = 0
  · subst n
    exact tendsto_zero_of_subsingleton _
  · have hgen : ∀ μ : ℂ,
        Module.End.maxGenEigenspace (Matrix.toLin' A : Module.End ℂ (Fin n → ℂ)) μ
          ≤ complexExpDecaySubmodule n A :=
      maxGenEigenspace_le_complexExpDecaySubmodule_of_re_neg n A hA
    have htop : ⨆ μ : ℂ,
        Module.End.maxGenEigenspace (Matrix.toLin' A : Module.End ℂ (Fin n → ℂ)) μ = ⊤ := by
      exact complex_iSup_maxGenEigenspace_eq_top (Matrix.toLin' A : Module.End ℂ (Fin n → ℂ))
    exact complex_matrix_exp_mulVec_tendsto_zero_of_iSup_maxGen_le_decay n A htop hgen v

lemma matrix_exp_mulVec_tendsto_zero_of_re_neg (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ μ : ℂ,
        Module.End.HasEigenvalue
          (Matrix.toLin' (A.map (algebraMap ℝ ℂ))) μ → μ.re < 0)
    (v : Fin n → ℝ) :
    Filter.Tendsto
      (fun t : ℝ => (NormedSpace.exp (t • A) : Matrix (Fin n) (Fin n) ℝ) *ᵥ v)
      Filter.atTop (nhds 0) := by
  classical
  have hC : Filter.Tendsto
      (fun t : ℝ =>
        (NormedSpace.exp (t • (A.map (algebraMap ℝ ℂ)) : Matrix (Fin n) (Fin n) ℂ)
          : Matrix (Fin n) (Fin n) ℂ) *ᵥ (fun i : Fin n => (v i : ℂ)))
      Filter.atTop (nhds 0) :=
    complex_matrix_exp_mulVec_tendsto_zero_of_re_neg n (A.map (algebraMap ℝ ℂ)) hA
      (fun i : Fin n => (v i : ℂ))
  have hcomp : Filter.Tendsto
      (fun t : ℝ => fun i : Fin n =>
        (((NormedSpace.exp (t • A) : Matrix (Fin n) (Fin n) ℝ) *ᵥ v) i : ℂ))
      Filter.atTop (nhds 0) := by
    refine hC.congr' ?_
    filter_upwards [] with t
    exact (complexification_exp_mulVec_real n A v t).symm
  exact real_tendsto_zero_of_complexification_tendsto_zero hcomp

lemma solution_formula_of_exp_neg_const (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (x : ℝ → (Fin n → ℝ))
    (hconst : ∀ ⦃t : ℝ⦄, 1 ≤ t →
      (NormedSpace.exp (-(((t - 1) : ℝ) • A)) : Matrix (Fin n) (Fin n) ℝ) *ᵥ x t = x 1) :
    ∀ ⦃t : ℝ⦄, 1 ≤ t →
      x t = (NormedSpace.exp (((t - 1) : ℝ) • A) : Matrix (Fin n) (Fin n) ℝ) *ᵥ x 1 := by
  intro t ht
  let B : Matrix (Fin n) (Fin n) ℝ := ((t - 1) : ℝ) • A
  have hinv : (NormedSpace.exp B : Matrix (Fin n) (Fin n) ℝ) * NormedSpace.exp (-B) = 1 :=
    matrix_exp_self_mul_neg n B
  calc
    x t = (1 : Matrix (Fin n) (Fin n) ℝ) *ᵥ x t := by
      rw [Matrix.one_mulVec]
    _ = ((NormedSpace.exp B : Matrix (Fin n) (Fin n) ℝ) * NormedSpace.exp (-B)) *ᵥ x t := by
      rw [hinv]
    _ = (NormedSpace.exp B : Matrix (Fin n) (Fin n) ℝ) *ᵥ
          ((NormedSpace.exp (-B) : Matrix (Fin n) (Fin n) ℝ) *ᵥ x t) := by
      rw [← Matrix.mulVec_mulVec]
    _ = (NormedSpace.exp B : Matrix (Fin n) (Fin n) ℝ) *ᵥ x 1 := by
      rw [hconst ht]
    _ = (NormedSpace.exp (((t - 1) : ℝ) • A) : Matrix (Fin n) (Fin n) ℝ) *ᵥ x 1 := by
      rfl

lemma expSeries_partialSum_two_matrix (n : ℕ) (y : Matrix (Fin n) (Fin n) ℝ) :
    (NormedSpace.expSeries ℝ (Matrix (Fin n) (Fin n) ℝ)).partialSum 2 y = 1 + y := by
  rw [FormalMultilinearSeries.partialSum]
  simp [Finset.sum_range_succ, NormedSpace.expSeries_apply_eq, add_comm]

lemma matrix_exp_hasFDerivAt_zero (n : ℕ) :
    HasFDerivAt (NormedSpace.exp : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ)
      (ContinuousLinearMap.id ℝ (Matrix (Fin n) (Fin n) ℝ)) 0 := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  have hf := (NormedSpace.hasFPowerSeriesAt_exp_zero_of_radius_pos
    (𝕂 := ℝ) (𝔸 := Matrix (Fin n) (Fin n) ℝ)
    (NormedSpace.expSeries_radius_pos (𝕂 := ℝ)
      (𝔸 := Matrix (Fin n) (Fin n) ℝ))).isBigO_sub_partialSum_pow 2
  have hsmall : (fun y : Matrix (Fin n) (Fin n) ℝ => ‖y‖ ^ 2)
      =o[nhds 0] fun y : Matrix (Fin n) (Fin n) ℝ => y := by
    rw [← Asymptotics.isLittleO_norm_right]
    simpa [pow_one] using
      (Asymptotics.isLittleO_norm_pow_norm_pow
        (E' := Matrix (Fin n) (Fin n) ℝ) (m := 1) (n := 2) (by norm_num))
  refine (hf.congr_left ?_).trans_isLittleO hsmall
  intro y
  rw [expSeries_partialSum_two_matrix n y, NormedSpace.exp_zero]
  simp [sub_eq_add_neg, add_comm, add_left_comm]

noncomputable def matrixLeftMulCLM (n : ℕ) (C : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ →L[ℝ] Matrix (Fin n) (Fin n) ℝ :=
  ContinuousLinearMap.mk (LinearMap.mulLeft ℝ C)
    (by
      simpa using (continuous_const.matrix_mul (R := ℝ)
        (A := fun _ : Matrix (Fin n) (Fin n) ℝ => C)
        (B := fun X : Matrix (Fin n) (Fin n) ℝ => X) continuous_id))

lemma matrix_exp_line_hasDerivAt (n : ℕ) (B : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (NormedSpace.exp (s • B) : Matrix (Fin n) (Fin n) ℝ))
      ((NormedSpace.exp (t • B) : Matrix (Fin n) (Fin n) ℝ) * B) t := by
  let E := Matrix (Fin n) (Fin n) ℝ
  let L : ℝ →L[ℝ] E := (ContinuousLinearMap.id ℝ ℝ).smulRight B
  let C : E := NormedSpace.exp (t • B)
  let LM := matrixLeftMulCLM n C
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  have hexp_o :
      (fun z : E => (NormedSpace.exp (0 + z) : E) - NormedSpace.exp (0 : E) -
        (ContinuousLinearMap.id ℝ E) z) =o[nhds 0] fun z : E => z := by
    exact hasFDerivAt_iff_isLittleO_nhds_zero.mp (matrix_exp_hasFDerivAt_zero n)
  have hLtend : Filter.Tendsto (fun h : ℝ => L h) (nhds 0) (nhds 0) := by
    simpa using (Continuous.tendsto (ContinuousLinearMap.continuous L) (0 : ℝ))
  have hrL :
      ((fun z : E => (NormedSpace.exp (0 + z) : E) - NormedSpace.exp (0 : E) -
        (ContinuousLinearMap.id ℝ E) z) ∘ fun h : ℝ => L h)
        =o[nhds 0] ((fun z : E => z) ∘ fun h : ℝ => L h) :=
    hexp_o.comp_tendsto hLtend
  have hLbig : (fun h : ℝ => L h) =O[nhds 0] fun h : ℝ => h := by
    simpa using ContinuousLinearMap.isBigO_comp L (fun h : ℝ => h) (nhds 0)
  have hr : (fun h : ℝ => ((NormedSpace.exp (h • B) : E) - 1 - h • B))
      =o[nhds 0] fun h : ℝ => h := by
    refine (hrL.trans_isBigO hLbig).congr_left ?_
    intro h
    simp [L, NormedSpace.exp_zero]
  have hLM : (fun h : ℝ => LM ((NormedSpace.exp (h • B) : E) - 1 - h • B))
      =o[nhds 0] fun h : ℝ => h := by
    exact (ContinuousLinearMap.isBigO_comp LM
      (fun h : ℝ => ((NormedSpace.exp (h • B) : E) - 1 - h • B))
      (nhds 0)).trans_isLittleO hr
  refine hLM.congr_left ?_
  intro h
  dsimp [LM, C, matrixLeftMulCLM]
  have harg : (t + h) • B = t • B + h • B := by rw [add_smul]
  have hcomm : Commute (t • B) (h • B) := (Commute.refl B).smul_left t |>.smul_right h
  rw [harg, NormedSpace.exp_add_of_commute hcomm]
  simp [Algebra.mul_smul_comm, sub_eq_add_neg, mul_add, add_comm, add_left_comm]

lemma matrix_exp_neg_shift_hasDerivAt (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    HasDerivAt
      (fun u : ℝ => (NormedSpace.exp (((u - 1) : ℝ) • (-A)) : Matrix (Fin n) (Fin n) ℝ))
      ((NormedSpace.exp (((t - 1) : ℝ) • (-A)) : Matrix (Fin n) (Fin n) ℝ) * (-A)) t := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  have hline := matrix_exp_line_hasDerivAt n (-A) (t - 1)
  have ho := (hasDerivAt_iff_isLittleO_nhds_zero.mp hline)
  exact ho.congr_left (by
    intro h
    have hs : ((t + h - 1 : ℝ)) = (t - 1) + h := by ring
    rw [hs])

lemma matrix_exp_integrating_factor_hasDerivAt (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    HasDerivAt
      (fun u : ℝ => (NormedSpace.exp (-(((u - 1) : ℝ) • A)) : Matrix (Fin n) (Fin n) ℝ))
      ((NormedSpace.exp (-(((t - 1) : ℝ) • A)) : Matrix (Fin n) (Fin n) ℝ) * (-A)) t := by
  simpa [neg_smul] using matrix_exp_neg_shift_hasDerivAt n A t

lemma sq_isLittleO_id_at_zero :
    (fun h : ℝ => h * h) =o[nhds 0] fun h : ℝ => h := by
  have hsq : (fun h : ℝ => ‖h‖ ^ 2) =o[nhds 0] fun h : ℝ => ‖h‖ ^ 1 :=
    Asymptotics.isLittleO_norm_pow_norm_pow (E' := ℝ) (m := 1) (n := 2) (by norm_num)
  have hsq' : (fun h : ℝ => ‖h‖ ^ 2) =o[nhds 0] fun h : ℝ => h := by
    rw [← Asymptotics.isLittleO_norm_right]
    simpa [pow_one] using hsq
  refine hsq'.congr_left ?_
  intro h
  rw [Real.norm_eq_abs, sq]
  exact abs_mul_abs_self h

lemma hasDerivAt_bilinear_apply
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : E →L[ℝ] F →L[ℝ] G)
    {f : ℝ → E} {g : ℝ → F} {f' : E} {g' : F} {t : ℝ}
    (hf : HasDerivAt f f' t) (hg : HasDerivAt g g' t) :
    HasDerivAt (fun u : ℝ => L (f u) (g u)) (L (f t) g' + L f' (g t)) t := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  let df : ℝ → E := fun h => f (t + h) - f t
  let dg : ℝ → F := fun h => g (t + h) - g t
  let rf : ℝ → E := fun h => df h - h • f'
  let rg : ℝ → F := fun h => dg h - h • g'
  have hrf : rf =o[nhds 0] fun h : ℝ => h := by
    simpa [rf, df] using (hasDerivAt_iff_isLittleO_nhds_zero.mp hf)
  have hrg : rg =o[nhds 0] fun h : ℝ => h := by
    simpa [rg, dg] using (hasDerivAt_iff_isLittleO_nhds_zero.mp hg)
  have herrPair : (fun h : ℝ => (rf h, rg h)) =o[nhds 0] fun h : ℝ => h :=
    hrf.prod_left hrg
  have hlin : (fun h : ℝ => L.deriv₂ (f t, g t) (rf h, rg h))
      =o[nhds 0] fun h : ℝ => h := by
    exact (ContinuousLinearMap.isBigO_comp (L.deriv₂ (f t, g t))
      (fun h : ℝ => (rf h, rg h)) (nhds 0)).trans_isLittleO herrPair
  have hfbig0 : (fun u : ℝ => f u - f t) =O[nhds t] fun u : ℝ => u - t := hf.isBigO_sub
  have hshift : Filter.Tendsto (fun h : ℝ => t + h) (nhds 0) (nhds t) := by
    simpa using ((continuous_const.add continuous_id).tendsto (0 : ℝ))
  have hfbig : df =O[nhds 0] fun h : ℝ => h := by
    have hcomp := hfbig0.comp_tendsto hshift
    refine hcomp.congr ?_ ?_
    · intro h; rfl
    · intro h; dsimp; ring
  have hgbig0 : (fun u : ℝ => g u - g t) =O[nhds t] fun u : ℝ => u - t := hg.isBigO_sub
  have hgbig : dg =O[nhds 0] fun h : ℝ => h := by
    have hcomp := hgbig0.comp_tendsto hshift
    refine hcomp.congr ?_ ?_
    · intro h; rfl
    · intro h; dsimp; ring
  have hprodO : (fun h : ℝ => ‖df h‖ * ‖dg h‖) =O[nhds 0] fun h : ℝ => h * h := by
    exact hfbig.norm_left.mul hgbig.norm_left
  have hbilO : (fun h : ℝ => L (df h) (dg h)) =O[nhds 0]
      fun h : ℝ => ‖df h‖ * ‖dg h‖ := by
    simpa using (L.isBoundedBilinearMap.isBigO_comp (g := df) (h := dg) (l := nhds 0))
  have hquad : (fun h : ℝ => L (df h) (dg h)) =o[nhds 0] fun h : ℝ => h :=
    (hbilO.trans hprodO).trans_isLittleO sq_isLittleO_id_at_zero
  have hsum : (fun h : ℝ => L.deriv₂ (f t, g t) (rf h, rg h) + L (df h) (dg h))
      =o[nhds 0] fun h : ℝ => h := hlin.add hquad
  refine hsum.congr_left ?_
  intro h
  dsimp [df, dg, rf, rg]
  have hfadd : f (t + h) = f t + (f (t + h) - f t) := by abel
  have hgadd : g (t + h) = g t + (g (t + h) - g t) := by abel
  rw [hfadd, hgadd, ContinuousLinearMap.map_add_add]
  simp only [ContinuousLinearMap.coe_deriv₂, map_sub, map_smul,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply]
  simp only [smul_add]
  abel

noncomputable def matrixMulVecCLM (n : ℕ) :
    Matrix (Fin n) (Fin n) ℝ →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  LinearMap.mkContinuous₂ (Matrix.mulVecBilin ℝ ℝ)
    (1 : ℝ) (by
      intro M v
      simpa using (Matrix.linfty_opNorm_mulVec M v))

lemma matrix_mulVec_hasDerivAt {n : ℕ} {M : ℝ → Matrix (Fin n) (Fin n) ℝ}
    {v : ℝ → Fin n → ℝ} {M' : Matrix (Fin n) (Fin n) ℝ} {v' : Fin n → ℝ} {t : ℝ}
    (hM : HasDerivAt M M' t) (hv : HasDerivAt v v' t) :
    HasDerivAt (fun u : ℝ => M u *ᵥ v u) (M t *ᵥ v' + M' *ᵥ v t) t := by
  simpa [matrixMulVecCLM] using hasDerivAt_bilinear_apply (matrixMulVecCLM n) hM hv

lemma exp_neg_mulVec_solution_hasDerivAt_zero (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (x : ℝ → (Fin n → ℝ))
    (hx : ∀ t : ℝ, 0 < t → HasDerivAt x (A.mulVec (x t)) t)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt
      (fun u : ℝ => (NormedSpace.exp (-(((u - 1) : ℝ) • A)) : Matrix (Fin n) (Fin n) ℝ) *ᵥ x u)
      0 t := by
  have hM := matrix_exp_integrating_factor_hasDerivAt n A t
  have hx' := hx t ht
  have hp := matrix_mulVec_hasDerivAt (n := n) hM hx'
  refine hp.congr_deriv ?_
  let M : Matrix (Fin n) (Fin n) ℝ := NormedSpace.exp (-(((t - 1) : ℝ) • A))
  change M *ᵥ (A *ᵥ x t) + (M * (-A)) *ᵥ x t = 0
  rw [← Matrix.mulVec_mulVec]
  rw [Matrix.neg_mulVec]
  rw [Matrix.mulVec_neg]
  abel

lemma local_lipschitz_of_hasDerivAt_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {u : ℝ} {eps : ℝ} (heps : 0 < eps) (hu : HasDerivAt f 0 u) :
    ∃ δ > 0, ∀ v : ℝ, |v - u| < δ → ‖f v - f u‖ ≤ eps * |v - u| := by
  have ho : (fun v : ℝ => f v - f u) =o[nhds u] (fun v : ℝ => v - u) := by
    simpa using hu.isLittleO
  have hev : ∀ᶠ v in nhds u, ‖f v - f u‖ ≤ eps * ‖v - u‖ := by
    exact (Asymptotics.isLittleO_iff.mp ho) heps
  rcases (Metric.mem_nhds_iff.mp hev) with ⟨δ, hδ, hball⟩
  refine ⟨δ, hδ, ?_⟩
  intro v hv
  have hvball : v ∈ Metric.ball u δ := by
    simpa [Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs, abs_sub_comm] using hv
  have h := hball hvball
  simpa [Real.norm_eq_abs] using h

lemma norm_sub_le_mul_sub_of_hasDerivAt_zero_on_Icc {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {a b eps : ℝ} (hab : a ≤ b) (heps : 0 < eps)
    (hderiv : ∀ u : ℝ, u ∈ Set.Icc a b → HasDerivAt f 0 u) :
    ‖f b - f a‖ ≤ eps * (b - a) := by
  classical
  let S : Set ℝ := {u | u ∈ Set.Icc a b ∧ ∀ v : ℝ, v ∈ Set.Icc a u →
      ‖f v - f a‖ ≤ eps * (v - a)}
  have haS : a ∈ S := by
    refine ⟨⟨le_rfl, hab⟩, ?_⟩
    intro v hv
    have hv_eq : v = a := by linarith [hv.1, hv.2]
    subst v
    rw [sub_self, norm_zero, sub_self, mul_zero]
  have hSne : S.Nonempty := ⟨a, haS⟩
  have hSbdd : BddAbove S := ⟨b, by intro u hu; exact hu.1.2⟩
  let c : ℝ := sSup S
  have hc_le_b : c ≤ b := csSup_le hSne (by intro u hu; exact hu.1.2)
  have ha_le_c : a ≤ c := le_csSup hSbdd haS
  have hc_mem_Icc : c ∈ Set.Icc a b := ⟨ha_le_c, hc_le_b⟩
  obtain ⟨δc, hδc, hδc_prop⟩ :=
    local_lipschitz_of_hasDerivAt_zero heps (hderiv c hc_mem_Icc)
  have hc_prop : ∀ v : ℝ, v ∈ Set.Icc a c → ‖f v - f a‖ ≤ eps * (v - a) := by
    intro v hv
    by_cases hvc : v = c
    · subst v
      by_cases hca : c = a
      · rw [hca, sub_self, norm_zero, sub_self, mul_zero]
      · have hthr_lt : c - δc / 2 < c := by linarith [hδc]
        obtain ⟨w, hwS, hcw⟩ := (lt_csSup_iff hSbdd hSne).1 hthr_lt
        have hw_le_c : w ≤ c := le_csSup hSbdd hwS
        have hdist_lt : |w - c| < δc := by
          have : c - w < δc := by linarith
          have habs : |w - c| = c - w := by
            rw [abs_of_nonpos (sub_nonpos.mpr hw_le_c)]
            ring
          rw [habs]
          exact this
        have hloc_w : ‖f c - f w‖ ≤ eps * (c - w) := by
          have h := hδc_prop w hdist_lt
          have habs : |w - c| = c - w := by
            rw [abs_of_nonpos (sub_nonpos.mpr hw_le_c)]
            ring
          rw [← norm_sub_rev, habs] at h
          exact h
        have hPw : ‖f w - f a‖ ≤ eps * (w - a) := hwS.2 w ⟨hwS.1.1, le_rfl⟩
        calc
          ‖f c - f a‖ = ‖(f c - f w) + (f w - f a)‖ := by
            congr 1
            abel
          _ ≤ ‖f c - f w‖ + ‖f w - f a‖ := norm_add_le _ _
          _ ≤ eps * (c - w) + eps * (w - a) := add_le_add hloc_w hPw
          _ = eps * (c - a) := by ring
    · have hvlt : v < c := lt_of_le_of_ne hv.2 hvc
      obtain ⟨u, huS, hvu⟩ := (lt_csSup_iff hSbdd hSne).1 hvlt
      exact huS.2 v ⟨hv.1, le_of_lt hvu⟩
  have hcS : c ∈ S := ⟨hc_mem_Icc, hc_prop⟩
  have hc_eq_b : c = b := by
    by_contra hne
    have hcb : c < b := lt_of_le_of_ne hc_le_b hne
    let η : ℝ := min (δc / 2) ((b - c) / 2)
    have hη_pos : 0 < η := by
      dsimp [η]
      exact lt_min (by linarith) (by linarith)
    have hη_le_δ : η ≤ δc / 2 := min_le_left _ _
    have hη_le_bc : η ≤ (b - c) / 2 := min_le_right _ _
    let d : ℝ := c + η
    have hcd : c < d := by dsimp [d]; linarith
    have hd_le_b : d ≤ b := by dsimp [d, η] at *; linarith
    have hdS : d ∈ S := by
      refine ⟨⟨?_, hd_le_b⟩, ?_⟩
      · dsimp [d]; linarith
      · intro v hv
        by_cases hvc_le : v ≤ c
        · exact hc_prop v ⟨hv.1, hvc_le⟩
        · have hcv : c ≤ v := le_of_not_ge hvc_le
          have hv_le_d : v ≤ d := hv.2
          have hdist : |v - c| < δc := by
            have hvdc : v - c ≤ η := by dsimp [d] at hv_le_d; linarith
            have hvdc_nonneg : 0 ≤ v - c := sub_nonneg.mpr hcv
            have habs : |v - c| = v - c := abs_of_nonneg hvdc_nonneg
            rw [habs]
            have : η < δc := by linarith
            exact lt_of_le_of_lt hvdc this
          have hloc_v : ‖f v - f c‖ ≤ eps * (v - c) := by
            have h := hδc_prop v hdist
            have hvdc_nonneg : 0 ≤ v - c := sub_nonneg.mpr hcv
            simpa [abs_of_nonneg hvdc_nonneg] using h
          have hPc : ‖f c - f a‖ ≤ eps * (c - a) := hc_prop c ⟨ha_le_c, le_rfl⟩
          calc
            ‖f v - f a‖ = ‖(f v - f c) + (f c - f a)‖ := by
              congr 1
              abel
            _ ≤ ‖f v - f c‖ + ‖f c - f a‖ := norm_add_le _ _
            _ ≤ eps * (v - c) + eps * (c - a) := add_le_add hloc_v hPc
            _ = eps * (v - a) := by ring
    have hd_le_c : d ≤ c := le_csSup hSbdd hdS
    exact not_lt_of_ge hd_le_c hcd
  have hb_mem_Iac : b ∈ Set.Icc a c := ⟨hab, le_of_eq hc_eq_b.symm⟩
  simpa [c] using hc_prop b hb_mem_Iac

lemma eq_of_hasDerivAt_zero_on_Icc {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hderiv : ∀ u : ℝ, u ∈ Set.Icc a b → HasDerivAt f 0 u) :
    f b = f a := by
  by_cases hba : b = a
  · rw [hba]
  · have hablt : a < b := lt_of_le_of_ne hab (Ne.symm hba)
    have hsubpos : 0 < b - a := sub_pos.mpr hablt
    have hle0 : ‖f b - f a‖ ≤ 0 := by
      apply le_of_forall_pos_le_add
      intro η hη
      have heps : 0 < η / (b - a) := div_pos hη hsubpos
      have hmain := norm_sub_le_mul_sub_of_hasDerivAt_zero_on_Icc
        (f := f) (a := a) (b := b) (eps := η / (b - a)) hab heps hderiv
      have hcalc : (η / (b - a)) * (b - a) = η := by
        field_simp [ne_of_gt hsubpos]
      calc
        ‖f b - f a‖ ≤ (η / (b - a)) * (b - a) := hmain
        _ = 0 + η := by rw [hcalc, zero_add]
    have hnorm0 : ‖f b - f a‖ = 0 := le_antisymm hle0 (norm_nonneg _)
    have hzero : f b - f a = 0 := norm_eq_zero.mp hnorm0
    exact sub_eq_zero.mp hzero

lemma exp_neg_mulVec_solution_const_of_hasDerivAt (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (x : ℝ → (Fin n → ℝ))
    (hx : ∀ t : ℝ, 0 < t → HasDerivAt x (A.mulVec (x t)) t) :
    ∀ ⦃t : ℝ⦄, 1 ≤ t →
      (NormedSpace.exp (-(((t - 1) : ℝ) • A)) : Matrix (Fin n) (Fin n) ℝ) *ᵥ x t = x 1 := by
  classical
  by_cases hn : n = 0
  · subst n
    intro t ht
    exact Subsingleton.elim _ _
  · intro t ht
    let y : ℝ → (Fin n → ℝ) := fun u =>
        (NormedSpace.exp (-(((u - 1) : ℝ) • A)) : Matrix (Fin n) (Fin n) ℝ) *ᵥ x u
    have hyderiv : ∀ u : ℝ, 0 < u → HasDerivAt y 0 u := by
      intro u hu
      simpa [y] using exp_neg_mulVec_solution_hasDerivAt_zero n A x hx hu
    have hyconst : y t = y 1 := by
      refine eq_of_hasDerivAt_zero_on_Icc (f := y) (a := 1) (b := t) ht ?_
      intro u hu
      exact hyderiv u (lt_of_lt_of_le zero_lt_one hu.1)
    calc
      (NormedSpace.exp (-(((t - 1) : ℝ) • A)) : Matrix (Fin n) (Fin n) ℝ) *ᵥ x t = y t := rfl
      _ = y 1 := hyconst
      _ = x 1 := by
        simp [y, Matrix.one_mulVec]

lemma solution_eq_matrix_exp_of_hasDerivAt (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (x : ℝ → (Fin n → ℝ))
    (hx : ∀ t : ℝ, 0 < t → HasDerivAt x (A.mulVec (x t)) t) :
    ∀ ⦃t : ℝ⦄, 1 ≤ t →
      x t = (NormedSpace.exp (((t - 1) : ℝ) • A) : Matrix (Fin n) (Fin n) ℝ) *ᵥ x 1 := by
  exact solution_formula_of_exp_neg_const n A x
    (exp_neg_mulVec_solution_const_of_hasDerivAt n A x hx)

lemma solution_eventually_eq_matrix_exp_of_hasDerivAt (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (x : ℝ → (Fin n → ℝ))
    (hx : ∀ t : ℝ, 0 < t → HasDerivAt x (A.mulVec (x t)) t) :
    ∀ᶠ t in Filter.atTop,
      x t = (NormedSpace.exp (((t - 1) : ℝ) • A) : Matrix (Fin n) (Fin n) ℝ) *ᵥ x 1 := by
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with t ht
  exact solution_eq_matrix_exp_of_hasDerivAt n A x hx ht

open scoped Matrix

theorem linear_ode_asymptotic_stability (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ μ : ℂ,
        Module.End.HasEigenvalue
          (Matrix.toLin' (A.map (algebraMap ℝ ℂ))) μ → μ.re < 0)
    (x : ℝ → (Fin n → ℝ))
    (hx : ∀ t : ℝ, 0 < t → HasDerivAt x (A.mulVec (x t)) t) :
    Filter.Tendsto (fun t : ℝ => ‖x t‖) Filter.atTop (nhds 0) := by
  classical
  by_cases hn : n = 0
  · subst n
    exact fin_zero_solution_norm_tendsto A x
  · exact tendsto_of_solution_formula_and_decay A x (x 1)
      (solution_eventually_eq_matrix_exp_of_hasDerivAt n A x hx)
      (matrix_exp_mulVec_tendsto_zero_of_re_neg n A hA (x 1))

end Submission
