/-
Downloaded from the public lean-eval leaderboard provenance.
problem_id: dirichlet_eigenvalues_eq_nat_sq
user: sqrt-of-2
model: GPT 5.5
submission_repo: sqrt-of-2/5d253653afb78ab2e57ae1446599c9eb
submission_ref: 83414975249f7c62a1e816c2609eb3471635213c
issue_number: 223
-/
import Mathlib

open scoped Real

namespace Submission

noncomputable def odeCLM (lam : ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) where
  toLinearMap :=
    { toFun := fun z => (z.2, -(lam * z.1))
      map_add' := by
        intro x y
        ext <;> simp [mul_add] <;> ring
      map_smul' := by
        intro c x
        ext <;> simp [mul_left_comm] }
  cont := by fun_prop

lemma odeCLM_apply (lam : ℝ) (z : ℝ × ℝ) :
    odeCLM lam z = (z.2, -(lam * z.1)) := rfl

lemma dirichlet_solution_unique_right {lam : ℝ} {y z : ℝ → ℝ} {a b : ℝ}
    (hy : ∀ x ∈ Set.Icc a b, HasDerivAt y (deriv y x) x)
    (hy' : ∀ x ∈ Set.Icc a b, HasDerivAt (deriv y) (-(lam * y x)) x)
    (hz : ∀ x ∈ Set.Icc a b, HasDerivAt z (deriv z x) x)
    (hz' : ∀ x ∈ Set.Icc a b, HasDerivAt (deriv z) (-(lam * z x)) x)
    (hya : y a = z a) (hda : deriv y a = deriv z a) :
    ∀ x ∈ Set.Icc a b, y x = z x := by
  let Y : ℝ → ℝ × ℝ := fun x => (y x, deriv y x)
  let Z : ℝ → ℝ × ℝ := fun x => (z x, deriv z x)
  have hv : ∀ t ∈ Set.Ico a b, LipschitzOnWith ‖odeCLM lam‖₊ (odeCLM lam) Set.univ := by
    intro t ht
    exact (odeCLM lam).lipschitz.lipschitzOnWith
  have hYcont : ContinuousOn Y (Set.Icc a b) := by
    exact (HasDerivAt.continuousOn fun x hx => hy x hx).prodMk
      (HasDerivAt.continuousOn fun x hx => hy' x hx)
  have hZcont : ContinuousOn Z (Set.Icc a b) := by
    exact (HasDerivAt.continuousOn fun x hx => hz x hx).prodMk
      (HasDerivAt.continuousOn fun x hx => hz' x hx)
  have hYder : ∀ t ∈ Set.Ico a b, HasDerivWithinAt Y ((odeCLM lam) (Y t)) (Set.Ici t) t := by
    intro t ht
    have htI : t ∈ Set.Icc a b := ⟨ht.1, le_of_lt ht.2⟩
    convert ((hy t htI).prodMk (hy' t htI)).hasDerivWithinAt using 1
  have hZder : ∀ t ∈ Set.Ico a b, HasDerivWithinAt Z ((odeCLM lam) (Z t)) (Set.Ici t) t := by
    intro t ht
    have htI : t ∈ Set.Icc a b := ⟨ht.1, le_of_lt ht.2⟩
    convert ((hz t htI).prodMk (hz' t htI)).hasDerivWithinAt using 1
  have hEq : Set.EqOn Y Z (Set.Icc a b) :=
    ODE_solution_unique_of_mem_Icc_right (K := ‖odeCLM lam‖₊) (s := fun _ => Set.univ)
      hv hYcont hYder (by intro t ht; trivial) hZcont hZder (by intro t ht; trivial) (by
        ext <;> simp [Y, Z, hya, hda])
  intro x hx
  have := hEq hx
  simpa [Y, Z] using congrArg Prod.fst this

lemma sin_scaled_hasDerivAt (μ c x : ℝ) :
    HasDerivAt (fun x : ℝ => c * Real.sin (μ * x)) (c * μ * Real.cos (μ * x)) x := by
  have harg : HasDerivAt (fun x : ℝ => μ * x) μ x := by
    simpa using (hasDerivAt_id x).const_mul μ
  have hs : HasDerivAt (fun x : ℝ => Real.sin (μ * x)) (μ * Real.cos (μ * x)) x := by
    convert (Real.hasDerivAt_sin (μ * x)).comp x harg using 1
    ring
  convert hs.const_mul c using 1
  ring

lemma deriv_sin_scaled (μ c : ℝ) :
    deriv (fun x : ℝ => c * Real.sin (μ * x)) =
      fun x => c * μ * Real.cos (μ * x) := by
  funext x
  exact (sin_scaled_hasDerivAt μ c x).deriv

lemma sin_scaled_second_hasDerivAt (μ c x : ℝ) :
    HasDerivAt (deriv (fun x : ℝ => c * Real.sin (μ * x)))
      (-(μ ^ 2 * (c * Real.sin (μ * x)))) x := by
  rw [deriv_sin_scaled]
  have harg : HasDerivAt (fun x : ℝ => μ * x) μ x := by
    simpa using (hasDerivAt_id x).const_mul μ
  have hc0 : HasDerivAt (fun x : ℝ => Real.cos (μ * x)) (-μ * Real.sin (μ * x)) x := by
    convert (Real.hasDerivAt_cos (μ * x)).comp x harg using 1
    ring
  have hc : HasDerivAt (fun x : ℝ => c * μ * Real.cos (μ * x))
      ((c * μ) * (-μ * Real.sin (μ * x))) x := by
    simpa [mul_assoc] using hc0.const_mul (c * μ)
  convert hc using 1 <;> ring

lemma sinh_scaled_hasDerivAt (ν c x : ℝ) :
    HasDerivAt (fun x : ℝ => c * Real.sinh (ν * x)) (c * ν * Real.cosh (ν * x)) x := by
  have harg : HasDerivAt (fun x : ℝ => ν * x) ν x := by
    simpa using (hasDerivAt_id x).const_mul ν
  have hs : HasDerivAt (fun x : ℝ => Real.sinh (ν * x)) (Real.cosh (ν * x) * ν) x :=
    (Real.hasDerivAt_sinh (ν * x)).comp x harg
  convert hs.const_mul c using 1
  ring

lemma deriv_sinh_scaled (ν c : ℝ) :
    deriv (fun x : ℝ => c * Real.sinh (ν * x)) =
      fun x => c * ν * Real.cosh (ν * x) := by
  funext x
  exact (sinh_scaled_hasDerivAt ν c x).deriv

lemma sinh_scaled_second_hasDerivAt (ν c x : ℝ) :
    HasDerivAt (deriv (fun x : ℝ => c * Real.sinh (ν * x)))
      (ν ^ 2 * (c * Real.sinh (ν * x))) x := by
  rw [deriv_sinh_scaled]
  have harg : HasDerivAt (fun x : ℝ => ν * x) ν x := by
    simpa using (hasDerivAt_id x).const_mul ν
  have hc0 : HasDerivAt (fun x : ℝ => Real.cosh (ν * x)) (Real.sinh (ν * x) * ν) x :=
    (Real.hasDerivAt_cosh (ν * x)).comp x harg
  have hc : HasDerivAt (fun x : ℝ => c * ν * Real.cosh (ν * x))
      ((c * ν) * (Real.sinh (ν * x) * ν)) x := by
    simpa [mul_assoc] using hc0.const_mul (c * ν)
  convert hc using 1 <;> ring

lemma linear_scaled_hasDerivAt (c x : ℝ) :
    HasDerivAt (fun x : ℝ => c * x) c x := by
  simpa using (hasDerivAt_id x).const_mul c

lemma deriv_linear_scaled (c : ℝ) :
    deriv (fun x : ℝ => c * x) = fun _ => c := by
  funext x
  exact (linear_scaled_hasDerivAt c x).deriv

lemma linear_scaled_second_hasDerivAt (c x : ℝ) :
    HasDerivAt (deriv (fun x : ℝ => c * x)) 0 x := by
  rw [deriv_linear_scaled]
  exact hasDerivAt_const x c

theorem dirichlet_eigenvalues_eq_nat_sq (lam : ℝ) :
    (∃ (y : ℝ → ℝ) (J : Set ℝ),
        IsOpen J ∧ Set.Icc (0 : ℝ) Real.pi ⊆ J ∧
        (∀ x ∈ J, HasDerivAt y (deriv y x) x) ∧
        (∀ x ∈ J, HasDerivAt (deriv y) (-(lam * y x)) x) ∧
        y 0 = 0 ∧ y Real.pi = 0 ∧
        ∃ x ∈ Set.Ioo (0 : ℝ) Real.pi, y x ≠ 0) ↔
      ∃ n : ℕ, 0 < n ∧ lam = (n : ℝ) ^ 2 := by
  constructor
  · intro h
    rcases h with ⟨y, J, hJopen, hJsub, hyJ, hyJ', hy0, hyπ, x0, hx0, hyx0⟩
    have hyI : ∀ x ∈ Set.Icc (0 : ℝ) Real.pi, HasDerivAt y (deriv y x) x :=
      fun x hx => hyJ x (hJsub hx)
    have hyI' : ∀ x ∈ Set.Icc (0 : ℝ) Real.pi, HasDerivAt (deriv y) (-(lam * y x)) x :=
      fun x hx => hyJ' x (hJsub hx)
    by_cases hpos : 0 < lam
    · let μ : ℝ := Real.sqrt lam
      let c : ℝ := deriv y 0 / μ
      let z : ℝ → ℝ := fun x => c * Real.sin (μ * x)
      have hμpos : 0 < μ := by
        dsimp [μ]
        exact Real.sqrt_pos.2 hpos
      have hμsq : μ ^ 2 = lam := by
        dsimp [μ]
        rw [Real.sq_sqrt hpos.le]
      have hz : ∀ x ∈ Set.Icc (0 : ℝ) Real.pi, HasDerivAt z (deriv z x) x := by
        intro x hx
        have hs := sin_scaled_hasDerivAt μ c x
        convert hs using 1
        exact hs.deriv
      have hz' : ∀ x ∈ Set.Icc (0 : ℝ) Real.pi, HasDerivAt (deriv z) (-(lam * z x)) x := by
        intro x hx
        have hs := sin_scaled_second_hasDerivAt μ c x
        convert hs using 1
        simp [z, hμsq]
      have hz0 : z 0 = y 0 := by simp [z, hy0]
      have hdz0 : deriv z 0 = deriv y 0 := by
        rw [show deriv z = fun x => c * μ * Real.cos (μ * x) by
          dsimp [z]
          exact deriv_sin_scaled μ c]
        dsimp [c]
        field_simp [(ne_of_gt hμpos)]
        simp
      have heq := dirichlet_solution_unique_right (lam := lam) (y := y) (z := z)
        hyI hyI' hz hz' hz0.symm hdz0.symm
      have hczero_or : c = 0 ∨ Real.sin (μ * Real.pi) = 0 := by
        have hpi_mem : Real.pi ∈ Set.Icc (0 : ℝ) Real.pi := ⟨Real.pi_pos.le, le_rfl⟩
        have hEq := heq Real.pi hpi_mem
        have : c * Real.sin (μ * Real.pi) = 0 := by
          simpa [z, hyπ] using hEq.symm
        exact mul_eq_zero.mp this
      have hcne : c ≠ 0 := by
        intro hc
        have hxI : x0 ∈ Set.Icc (0 : ℝ) Real.pi := ⟨hx0.1.le, hx0.2.le⟩
        have hEq := heq x0 hxI
        apply hyx0
        simpa [z, hc] using hEq
      have hsin0 : Real.sin (μ * Real.pi) = 0 := hczero_or.resolve_left hcne
      rcases Real.sin_eq_zero_iff.mp hsin0 with ⟨k, hk⟩
      have hkμ : (k : ℝ) = μ := by
        exact (mul_right_injective₀ (ne_of_gt Real.pi_pos)) (by simpa [mul_comm] using hk)
      have hkposR : 0 < (k : ℝ) := by simpa [hkμ] using hμpos
      have hkpos : 0 < k := by exact_mod_cast hkposR
      have hknonneg : 0 ≤ k := le_of_lt hkpos
      have hkto : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hknonneg
      have hkto_pos : 0 < k.toNat := by
        have : (0 : ℤ) < (k.toNat : ℤ) := by simpa [hkto] using hkpos
        exact_mod_cast this
      refine ⟨k.toNat, hkto_pos, ?_⟩
      have hcast : ((k.toNat : ℕ) : ℝ) = μ := by
        rw [← hkμ]
        have : ((k.toNat : ℕ) : ℝ) = (k : ℝ) := by exact_mod_cast hkto
        exact this
      rw [← hμsq, ← hcast]
    · have hle : lam ≤ 0 := le_of_not_gt hpos
      rcases lt_or_eq_of_le hle with hneg | hzero
      · let ν : ℝ := Real.sqrt (-lam)
        let c : ℝ := deriv y 0 / ν
        let z : ℝ → ℝ := fun x => c * Real.sinh (ν * x)
        have hνpos : 0 < ν := by
          dsimp [ν]
          exact Real.sqrt_pos.2 (neg_pos.2 hneg)
        have hνsq : ν ^ 2 = -lam := by
          dsimp [ν]
          rw [Real.sq_sqrt (neg_nonneg.2 hle)]
        have hz : ∀ x ∈ Set.Icc (0 : ℝ) Real.pi, HasDerivAt z (deriv z x) x := by
          intro x hx
          have hs := sinh_scaled_hasDerivAt ν c x
          convert hs using 1
          exact hs.deriv
        have hz' : ∀ x ∈ Set.Icc (0 : ℝ) Real.pi, HasDerivAt (deriv z) (-(lam * z x)) x := by
          intro x hx
          have hs := sinh_scaled_second_hasDerivAt ν c x
          convert hs using 1
          simp [z, hνsq]
        have hz0 : z 0 = y 0 := by simp [z, hy0]
        have hdz0 : deriv z 0 = deriv y 0 := by
          rw [show deriv z = fun x => c * ν * Real.cosh (ν * x) by
            dsimp [z]
            exact deriv_sinh_scaled ν c]
          dsimp [c]
          field_simp [(ne_of_gt hνpos)]
          simp
        have heq := dirichlet_solution_unique_right (lam := lam) (y := y) (z := z)
          hyI hyI' hz hz' hz0.symm hdz0.symm
        have hc : c = 0 := by
          have hpi_mem : Real.pi ∈ Set.Icc (0 : ℝ) Real.pi := ⟨Real.pi_pos.le, le_rfl⟩
          have hEq := heq Real.pi hpi_mem
          have : c * Real.sinh (ν * Real.pi) = 0 := by
            simpa [z, hyπ] using hEq.symm
          have hsinh_ne : Real.sinh (ν * Real.pi) ≠ 0 := by
            rw [Real.sinh_ne_zero]
            positivity
          exact (mul_eq_zero.mp this).resolve_right hsinh_ne
        exfalso
        have hxI : x0 ∈ Set.Icc (0 : ℝ) Real.pi := ⟨hx0.1.le, hx0.2.le⟩
        have hEq := heq x0 hxI
        apply hyx0
        simpa [z, hc] using hEq
      · let c : ℝ := deriv y 0
        let z : ℝ → ℝ := fun x => c * x
        have hz : ∀ x ∈ Set.Icc (0 : ℝ) Real.pi, HasDerivAt z (deriv z x) x := by
          intro x hx
          have hs := linear_scaled_hasDerivAt c x
          convert hs using 1
          exact hs.deriv
        have hz' : ∀ x ∈ Set.Icc (0 : ℝ) Real.pi, HasDerivAt (deriv z) (-(lam * z x)) x := by
          intro x hx
          have hs := linear_scaled_second_hasDerivAt c x
          convert hs using 1
          simp [z, hzero]
        have hz0 : z 0 = y 0 := by simp [z, hy0]
        have hdz0 : deriv z 0 = deriv y 0 := by
          rw [show deriv z = fun _ => c by
            dsimp [z]
            exact deriv_linear_scaled c]
        have heq := dirichlet_solution_unique_right (lam := lam) (y := y) (z := z)
          hyI hyI' hz hz' hz0.symm hdz0.symm
        have hc : c = 0 := by
          have hpi_mem : Real.pi ∈ Set.Icc (0 : ℝ) Real.pi := ⟨Real.pi_pos.le, le_rfl⟩
          have hEq := heq Real.pi hpi_mem
          have : c * Real.pi = 0 := by
            simpa [z, hyπ] using hEq.symm
          exact (mul_eq_zero.mp this).resolve_right (ne_of_gt Real.pi_pos)
        exfalso
        have hxI : x0 ∈ Set.Icc (0 : ℝ) Real.pi := ⟨hx0.1.le, hx0.2.le⟩
        have hEq := heq x0 hxI
        apply hyx0
        simpa [z, hc] using hEq
  · rintro ⟨n, hn, rfl⟩
    refine ⟨fun x => Real.sin ((n : ℝ) * x), Set.univ, isOpen_univ, by simp, ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx
      have harg : HasDerivAt (fun x : ℝ => (n : ℝ) * x) (n : ℝ) x := by
        simpa using (hasDerivAt_id x).const_mul (n : ℝ)
      have hs : HasDerivAt (fun x : ℝ => Real.sin ((n : ℝ) * x))
          ((n : ℝ) * Real.cos ((n : ℝ) * x)) x := by
        convert (Real.hasDerivAt_sin ((n : ℝ) * x)).comp x harg using 1
        ring
      convert hs using 1
      exact hs.deriv
    · intro x hx
      have hderiv : deriv (fun x : ℝ => Real.sin ((n : ℝ) * x)) =
          fun x => (n : ℝ) * Real.cos ((n : ℝ) * x) := by
        funext x
        have harg : HasDerivAt (fun x : ℝ => (n : ℝ) * x) (n : ℝ) x := by
          simpa using (hasDerivAt_id x).const_mul (n : ℝ)
        have hs : HasDerivAt (fun x : ℝ => Real.sin ((n : ℝ) * x))
            ((n : ℝ) * Real.cos ((n : ℝ) * x)) x := by
          convert (Real.hasDerivAt_sin ((n : ℝ) * x)).comp x harg using 1
          ring
        exact hs.deriv
      rw [hderiv]
      have harg : HasDerivAt (fun x : ℝ => (n : ℝ) * x) (n : ℝ) x := by
        simpa using (hasDerivAt_id x).const_mul (n : ℝ)
      have hc : HasDerivAt (fun x : ℝ => (n : ℝ) * Real.cos ((n : ℝ) * x))
          (-( (n : ℝ) ^ 2 * Real.sin ((n : ℝ) * x))) x := by
        have hc0 : HasDerivAt (fun x : ℝ => Real.cos ((n : ℝ) * x))
            (-(n : ℝ) * Real.sin ((n : ℝ) * x)) x := by
          convert (Real.hasDerivAt_cos ((n : ℝ) * x)).comp x harg using 1
          ring
        convert hc0.const_mul (n : ℝ) using 1 <;> ring
      convert hc using 1 <;> ring
    · simp
    · simpa using Real.sin_nat_mul_pi n
    · refine ⟨Real.pi / (2 * n), ?_, ?_⟩
      constructor
      · positivity
      · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        have htwo : (2 : ℝ) ≤ 2 * (n : ℝ) := by nlinarith
        have hle : Real.pi / (2 * (n : ℝ)) ≤ Real.pi / 2 := by
          exact div_le_div_of_nonneg_left Real.pi_pos.le (by positivity) htwo
        nlinarith [Real.pi_pos, hle]
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
      have harg : (n : ℝ) * (Real.pi / (2 * n)) = Real.pi / 2 := by
        field_simp [hn0]
      change Real.sin ((n : ℝ) * (Real.pi / (2 * n))) ≠ 0
      rw [harg, Real.sin_pi_div_two]
      norm_num

end Submission
