import Mathlib
open Real
open Set

set_option maxHeartbeats 800000

namespace Submission

lemma hasDerivAt_sin_mul (ω x : ℝ) : HasDerivAt (fun x' : ℝ => sin (ω * x')) (ω * cos (ω * x)) x := by
  have h : HasDerivAt (fun x' : ℝ => ω * x') ω x := by
    simpa using (HasDerivAt.const_mul ω (hasDerivAt_id x))
  simpa [mul_comm] using h.sin

lemma hasDerivAt_cos_mul (ω x : ℝ) : HasDerivAt (fun x' : ℝ => cos (ω * x')) (-ω * sin (ω * x)) x := by
  have h : HasDerivAt (fun x' : ℝ => ω * x') ω x := by
    simpa using (HasDerivAt.const_mul ω (hasDerivAt_id x))
  have hcos := (Real.hasDerivAt_cos (ω * x)).comp x h
  simpa [mul_comm, mul_left_comm, mul_assoc] using hcos

lemma aux_deriv_F (y : ℝ → ℝ) (lam ω : ℝ) (hωsq : ω^2 = lam) (hωpos : ω > 0) (x : ℝ) 
    (hx_deriv_y : HasDerivAt y (deriv y x) x)
    (hx_deriv_deriv : HasDerivAt (deriv y) (-(lam * y x)) x) : 
    HasDerivAt (fun x' : ℝ => y x' * sin (ω * x') + (deriv y x' / ω) * cos (ω * x')) 0 x := by
  have h_ysin : HasDerivAt (fun x' : ℝ => y x' * sin (ω * x')) 
      ((deriv y x) * sin (ω * x) + y x * (ω * cos (ω * x))) x :=
    HasDerivAt.mul hx_deriv_y (hasDerivAt_sin_mul ω x)
  have h_term2 : HasDerivAt (fun x' : ℝ => (deriv y x' / ω) * cos (ω * x')) 
      (-(lam * y x) / ω * cos (ω * x) + (deriv y x / ω) * (-ω * sin (ω * x))) x := by
    have h_deriv_div : HasDerivAt (fun x' : ℝ => deriv y x' / ω) (-(lam * y x) / ω) x := by
      simpa [div_eq_mul_inv, mul_comm] using (HasDerivAt.const_mul (1/ω) hx_deriv_deriv)
    have h_cos := hasDerivAt_cos_mul ω x
    exact HasDerivAt.mul h_deriv_div h_cos
  have h_total : HasDerivAt (fun x' : ℝ => y x' * sin (ω * x') + (deriv y x' / ω) * cos (ω * x'))
      (((deriv y x) * sin (ω * x) + y x * (ω * cos (ω * x))) + 
       (-(lam * y x) / ω * cos (ω * x) + (deriv y x / ω) * (-ω * sin (ω * x)))) x :=
    HasDerivAt.add h_ysin h_term2
  have hω_ne : ω ≠ 0 := by linarith
  have h_sin_zero : (deriv y x) * sin (ω * x) + (deriv y x / ω) * (-ω * sin (ω * x)) = 0 := by
    field_simp [hω_ne]; ring
  have h_cos_zero : y x * (ω * cos (ω * x)) + (-(lam * y x) / ω) * cos (ω * x) = 0 := by
    calc
      y x * (ω * cos (ω * x)) + (-(lam * y x) / ω) * cos (ω * x)
          = y x * cos (ω * x) * (ω - lam / ω) := by ring
      _ = y x * cos (ω * x) * (ω - ω^2 / ω) := by rw [hωsq]
      _ = y x * cos (ω * x) * (ω - ω) := by field_simp [hω_ne]
      _ = y x * cos (ω * x) * 0 := by ring
      _ = 0 := by ring
  have h_simplify : ((deriv y x) * sin (ω * x) + y x * (ω * cos (ω * x))) + 
    (-(lam * y x) / ω * cos (ω * x) + (deriv y x / ω) * (-ω * sin (ω * x))) = 0 := by
    calc
      ((deriv y x) * sin (ω * x) + y x * (ω * cos (ω * x))) + 
      (-(lam * y x) / ω * cos (ω * x) + (deriv y x / ω) * (-ω * sin (ω * x)))
          = ((deriv y x) * sin (ω * x) + (deriv y x / ω) * (-ω * sin (ω * x))) +
            (y x * (ω * cos (ω * x)) + (-(lam * y x) / ω) * cos (ω * x)) := by ring
      _ = 0 + 0 := by rw [h_sin_zero, h_cos_zero]
      _ = 0 := by simp
  have h_total' : HasDerivAt (fun x' : ℝ => y x' * sin (ω * x') + (deriv y x' / ω) * cos (ω * x'))
      (((deriv y x) * sin (ω * x) + y x * (ω * cos (ω * x))) + 
       (-(lam * y x) / ω * cos (ω * x) + -(deriv y x / ω * (ω * sin (ω * x))))) x := by
    have h_eq : ((deriv y x) * sin (ω * x) + y x * (ω * cos (ω * x))) + 
      (-(lam * y x) / ω * cos (ω * x) + (deriv y x / ω) * (-ω * sin (ω * x))) =
      ((deriv y x) * sin (ω * x) + y x * (ω * cos (ω * x))) + 
      (-(lam * y x) / ω * cos (ω * x) + -(deriv y x / ω * (ω * sin (ω * x)))) := by ring
    simpa [h_eq] using h_total
  have h_simplify' : ((deriv y x) * sin (ω * x) + y x * (ω * cos (ω * x))) + 
    (-(lam * y x) / ω * cos (ω * x) + -(deriv y x / ω * (ω * sin (ω * x)))) = 0 := by
    calc
      ((deriv y x) * sin (ω * x) + y x * (ω * cos (ω * x))) + 
      (-(lam * y x) / ω * cos (ω * x) + -(deriv y x / ω * (ω * sin (ω * x))))
          = ((deriv y x) * sin (ω * x) + y x * (ω * cos (ω * x))) + 
            (-(lam * y x) / ω * cos (ω * x) + (deriv y x / ω) * (-ω * sin (ω * x))) := by ring
      _ = 0 := h_simplify
  simpa [h_simplify'] using h_total'

lemma aux_deriv_G (y : ℝ → ℝ) (lam ω : ℝ) (hωsq : ω^2 = lam) (hωpos : ω > 0) (x : ℝ) 
    (hx_deriv_y : HasDerivAt y (deriv y x) x)
    (hx_deriv_deriv : HasDerivAt (deriv y) (-(lam * y x)) x) : 
    HasDerivAt (fun x' : ℝ => y x' * cos (ω * x') - (deriv y x' / ω) * sin (ω * x')) 0 x := by
  have h_ycos : HasDerivAt (fun x' : ℝ => y x' * cos (ω * x')) 
      ((deriv y x) * cos (ω * x) + y x * (-ω * sin (ω * x))) x :=
    HasDerivAt.mul hx_deriv_y (hasDerivAt_cos_mul ω x)
  have h_term2 : HasDerivAt (fun x' : ℝ => (deriv y x' / ω) * sin (ω * x')) 
      (-(lam * y x) / ω * sin (ω * x) + (deriv y x / ω) * (ω * cos (ω * x))) x := by
    have h_deriv_div : HasDerivAt (fun x' : ℝ => deriv y x' / ω) (-(lam * y x) / ω) x := by
      simpa [div_eq_mul_inv, mul_comm] using (HasDerivAt.const_mul (1/ω) hx_deriv_deriv)
    have h_sin := hasDerivAt_sin_mul ω x
    exact HasDerivAt.mul h_deriv_div h_sin
  have h_sub_raw : HasDerivAt (fun x' : ℝ => y x' * cos (ω * x') - (deriv y x' / ω) * sin (ω * x'))
      (((deriv y x) * cos (ω * x) + y x * (-ω * sin (ω * x))) - 
       (-(lam * y x) / ω * sin (ω * x) + (deriv y x / ω) * (ω * cos (ω * x)))) x :=
    HasDerivAt.sub h_ycos h_term2
  have hω_ne : ω ≠ 0 := by linarith
  have h_simplify : ((deriv y x) * cos (ω * x) + y x * (-ω * sin (ω * x))) - 
    (-(lam * y x) / ω * sin (ω * x) + (deriv y x / ω) * (ω * cos (ω * x))) = 0 := by
    calc
      ((deriv y x) * cos (ω * x) + y x * (-ω * sin (ω * x))) - 
      (-(lam * y x) / ω * sin (ω * x) + (deriv y x / ω) * (ω * cos (ω * x)))
          = (deriv y x) * cos (ω * x) - (deriv y x / ω) * (ω * cos (ω * x)) +
            y x * (-ω * sin (ω * x)) + (lam * y x / ω) * sin (ω * x) := by ring
      _ = ((deriv y x) * cos (ω * x) - (deriv y x) * cos (ω * x)) +
            y x * sin (ω * x) * (-ω + lam / ω) := by
              field_simp [hω_ne]; ring
      _ = 0 + y x * sin (ω * x) * (-ω + lam / ω) := by ring
      _ = y x * sin (ω * x) * (-ω + lam / ω) := by simp
      _ = y x * sin (ω * x) * (-ω + ω^2 / ω) := by rw [hωsq]
      _ = y x * sin (ω * x) * (-ω + ω) := by field_simp [hω_ne]
      _ = y x * sin (ω * x) * 0 := by ring
      _ = 0 := by ring
  have h_sub_deriv_eq : ((deriv y x) * cos (ω * x) + y x * (-ω * sin (ω * x))) - 
    (-(lam * y x) / ω * sin (ω * x) + (deriv y x / ω) * (ω * cos (ω * x))) = 
    (deriv y x) * cos (ω * x) + -(y x * (ω * sin (ω * x))) -
    (-(lam * y x) / ω * sin (ω * x) + (deriv y x / ω) * (ω * cos (ω * x))) := by ring
  have h_simplify' : (deriv y x) * cos (ω * x) + -(y x * (ω * sin (ω * x))) -
    (-(lam * y x) / ω * sin (ω * x) + (deriv y x / ω) * (ω * cos (ω * x))) = 0 := by
    rw [← h_sub_deriv_eq, h_simplify]
  simpa [h_simplify'] using h_sub_raw

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
    rcases h with ⟨y, J, hJopen, hJsub, hy, hy', hy0, hypi, hnonz⟩
    rcases hnonz with ⟨x0, hx0mem, hx0nonz⟩
    have h0J : (0 : ℝ) ∈ J := hJsub (Set.left_mem_Icc.mpr (by nlinarith [Real.pi_pos]))
    have hpiJ : Real.pi ∈ J := hJsub (Set.right_mem_Icc.mpr (by nlinarith [Real.pi_pos]))
    have hx0J : x0 ∈ J := hJsub (Set.mem_Icc.mpr ⟨hx0mem.1.le, hx0mem.2.le⟩)
    have hx0Icc : x0 ∈ Set.Icc (0 : ℝ) Real.pi := Set.mem_Icc.mpr ⟨hx0mem.1.le, hx0mem.2.le⟩
    
    by_cases hlam_pos : lam > 0
    · set ω := Real.sqrt lam with hω
      have hωpos : ω > 0 := Real.sqrt_pos.mpr hlam_pos
      have hωsq : ω^2 = lam := Real.sq_sqrt (by linarith)
      
      set C := connectedComponentIn J 0 with hC
      have hCopen : IsOpen C := IsOpen.connectedComponentIn (F := J) (x := 0) hJopen
      have hCpre : IsPreconnected C := isPreconnected_connectedComponentIn
      have h0C : (0 : ℝ) ∈ C := mem_connectedComponentIn h0J
      have hpiC : Real.pi ∈ C := by
        have hpre_Icc : IsPreconnected (Set.Icc (0 : ℝ) Real.pi) := isPreconnected_Icc
        have hsubset : Set.Icc (0 : ℝ) Real.pi ⊆ C :=
          hpre_Icc.subset_connectedComponentIn (Set.left_mem_Icc.mpr (by nlinarith [Real.pi_pos])) hJsub
        exact hsubset (Set.right_mem_Icc.mpr (by nlinarith [Real.pi_pos]))
      have hx0C : x0 ∈ C := by
        have hpre_Icc : IsPreconnected (Set.Icc (0 : ℝ) Real.pi) := isPreconnected_Icc
        have hsubset : Set.Icc (0 : ℝ) Real.pi ⊆ C :=
          hpre_Icc.subset_connectedComponentIn (Set.left_mem_Icc.mpr (by nlinarith [Real.pi_pos])) hJsub
        exact hsubset hx0Icc
      
      let F : ℝ → ℝ := fun x => y x * sin (ω * x) + (deriv y x / ω) * cos (ω * x)
      let G : ℝ → ℝ := fun x => y x * cos (ω * x) - (deriv y x / ω) * sin (ω * x)
      
      have hF_deriv : ∀ x ∈ J, HasDerivAt F 0 x := by
        intro x hx; dsimp [F]; exact aux_deriv_F y lam ω hωsq hωpos x (hy x hx) (hy' x hx)
      have hG_deriv : ∀ x ∈ J, HasDerivAt G 0 x := by
        intro x hx; dsimp [G]; exact aux_deriv_G y lam ω hωsq hωpos x (hy x hx) (hy' x hx)
      
      have hF_const : ∀ x ∈ C, F x = F 0 := by
        have hF_diff : DifferentiableOn ℝ F C := by
          intro x hx
          have hxJ : x ∈ J := connectedComponentIn_subset J 0 hx
          exact (hF_deriv x hxJ).differentiableAt.differentiableWithinAt
        have hF_deriv_zero : C.EqOn (deriv F) 0 := by
          intro x hx
          have hxJ : x ∈ J := connectedComponentIn_subset J 0 hx
          exact (hF_deriv x hxJ).deriv
        intro x hx
        exact hCopen.is_const_of_deriv_eq_zero hCpre hF_diff hF_deriv_zero hx h0C
      
      have hG_const : ∀ x ∈ C, G x = G 0 := by
        have hG_diff : DifferentiableOn ℝ G C := by
          intro x hx
          have hxJ : x ∈ J := connectedComponentIn_subset J 0 hx
          exact (hG_deriv x hxJ).differentiableAt.differentiableWithinAt
        have hG_deriv_zero : C.EqOn (deriv G) 0 := by
          intro x hx
          have hxJ : x ∈ J := connectedComponentIn_subset J 0 hx
          exact (hG_deriv x hxJ).deriv
        intro x hx
        exact hCopen.is_const_of_deriv_eq_zero hCpre hG_diff hG_deriv_zero hx h0C
      
      have hF0 : F 0 = (deriv y 0) / ω := by
        dsimp [F]; simp [hy0]
      have hG0 : G 0 = 0 := by
        dsimp [G]; simp [hy0]
      
      have hG_eq : ∀ x ∈ C, y x * cos (ω * x) = (deriv y x / ω) * sin (ω * x) := by
        intro x hx
        have hGx : G x = 0 := by
          rw [hG_const x hx, hG0]
        dsimp [G] at hGx
        linarith
      
      have hF_eq : ∀ x ∈ C, y x * sin (ω * x) + (deriv y x / ω) * cos (ω * x) = (deriv y 0) / ω := by
        intro x hx
        have hFx : F x = F 0 := hF_const x hx
        dsimp [F] at hFx
        simpa [hy0] using hFx
      
      have hy_solution : ∀ x ∈ C, y x = ((deriv y 0) / ω) * sin (ω * x) := by
        intro x hx
        have hGx := hG_eq x hx
        have hFx := hF_eq x hx
        have hy_sin_expr : y x * sin (ω * x) = (deriv y 0) / ω - (deriv y x / ω) * cos (ω * x) := by
          linarith
        calc
          y x = y x * (sin (ω * x) ^ 2 + cos (ω * x) ^ 2) := by
            rw [Real.sin_sq_add_cos_sq, mul_one]
          _ = (y x * cos (ω * x)) * cos (ω * x) + (y x * sin (ω * x)) * sin (ω * x) := by ring
          _ = ((deriv y x / ω) * sin (ω * x)) * cos (ω * x) + 
              ((deriv y 0) / ω - (deriv y x / ω) * cos (ω * x)) * sin (ω * x) := by
            rw [hGx, hy_sin_expr]
          _ = ((deriv y 0) / ω) * sin (ω * x) := by ring
      
      have hypi_solution : y Real.pi = ((deriv y 0) / ω) * sin (ω * Real.pi) := hy_solution Real.pi hpiC
      rw [hypi] at hypi_solution
      
      have hsin_omega_pi : sin (ω * Real.pi) = 0 := by
        by_cases hderiv0zero : deriv y 0 = 0
        · have hy_zero_on_C : ∀ x ∈ C, y x = 0 := by
            intro x hx
            rw [hy_solution x hx, hderiv0zero]; simp
          have hy0zero : y x0 = 0 := hy_zero_on_C x0 hx0C
          exact absurd hy0zero hx0nonz
        · have htemp : ((deriv y 0) / ω) * sin (ω * Real.pi) = 0 := hypi_solution.symm
          have h_cases := mul_eq_zero.mp htemp
          rcases h_cases with (hdiv | hsin)
          · have hzero : deriv y 0 = 0 := by
              calc
                deriv y 0 = ((deriv y 0) / ω) * ω := by field_simp [hωpos.ne']
                _ = 0 * ω := by rw [hdiv]
                _ = 0 := by ring
            exact absurd hzero hderiv0zero
          · exact hsin
      
      rw [Real.sin_eq_zero_iff] at hsin_omega_pi
      rcases hsin_omega_pi with ⟨k, hk⟩
      have hk_eq_omega : (k : ℝ) = ω := by
        nlinarith [Real.pi_pos]
      have hk_pos : (0 : ℤ) < k := by
        by_contra! hk_nonpos
        have hk_nonpos' : (k : ℝ) ≤ 0 := by exact_mod_cast hk_nonpos
        nlinarith
      set n := k.natAbs with hn
      have hn_pos : 0 < n := by
        have hk_ne_zero : k ≠ 0 := by linarith
        exact Int.natAbs_pos.mpr hk_ne_zero
      refine ⟨n, hn_pos, ?_⟩
      calc
        lam = ω^2 := hωsq.symm
        _ = (k : ℝ)^2 := by rw [hk_eq_omega]
        _ = ((n : ℕ) : ℝ)^2 := by simp [hn]
    · have hle : lam ≤ 0 := by linarith
      
      have hg_nonneg_deriv : ∀ x ∈ Set.Ioo (0 : ℝ) Real.pi, 0 ≤ deriv (fun t : ℝ => y t * deriv y t) x := by
        intro x hx
        have hxJ : x ∈ J := hJsub (Set.mem_Icc.mpr ⟨hx.1.le, hx.2.le⟩)
        have hyx : HasDerivAt y (deriv y x) x := hy x hxJ
        have hy'x : HasDerivAt (deriv y) (-(lam * y x)) x := hy' x hxJ
        have hg_deriv : HasDerivAt (fun t : ℝ => y t * deriv y t) ((deriv y x)^2 + y x * (-(lam * y x))) x := by
          have h := HasDerivAt.mul hyx hy'x
          simpa [sq] using h
        have hg_deriv_val : deriv (fun t : ℝ => y t * deriv y t) x = (deriv y x)^2 - lam * (y x)^2 := by
          have := hg_deriv.deriv; rw [this]; ring
        rw [hg_deriv_val]
        nlinarith [sq_nonneg (deriv y x), sq_nonneg (y x)]
      
      have hg_cont : ContinuousOn (fun t : ℝ => y t * deriv y t) (Set.Icc (0 : ℝ) Real.pi) := by
        intro z hz
        have hzJ : z ∈ J := hJsub hz
        have hyz : HasDerivAt y (deriv y z) z := hy z hzJ
        have hy'z : HasDerivAt (deriv y) (-(lam * y z)) z := hy' z hzJ
        exact (ContinuousAt.mul hyz.continuousAt hy'z.continuousAt).continuousWithinAt
      
      have hg_diff : DifferentiableOn ℝ (fun t : ℝ => y t * deriv y t) (Set.Ioo (0 : ℝ) Real.pi) := by
        intro z hz
        have hzJ : z ∈ J := hJsub (Set.mem_Icc.mpr ⟨hz.1.le, hz.2.le⟩)
        have hyz : HasDerivAt y (deriv y z) z := hy z hzJ
        have hy'z : HasDerivAt (deriv y) (-(lam * y z)) z := hy' z hzJ
        have hg_deriv : HasDerivAt (fun t : ℝ => y t * deriv y t) ((deriv y z)^2 + y z * (-(lam * y z))) z := by
          have h := HasDerivAt.mul hyz hy'z
          simpa [sq] using h
        exact hg_deriv.differentiableAt.differentiableWithinAt
      
      have hg_mono : MonotoneOn (fun t : ℝ => y t * deriv y t) (Set.Icc (0 : ℝ) Real.pi) := by
        apply monotoneOn_of_deriv_nonneg (convex_Icc 0 Real.pi) hg_cont
        · rw [interior_Icc]; exact hg_diff
        · intro x hx; rw [interior_Icc] at hx; exact hg_nonneg_deriv x hx
      
      have hg0_val : y 0 * deriv y 0 = 0 := by simp [hy0]
      have hgpi_val : y Real.pi * deriv y Real.pi = 0 := by simp [hypi]
      
      have hg_eq0 : ∀ x ∈ Set.Icc (0 : ℝ) Real.pi, y x * deriv y x = 0 := by
        intro x hx
        have hx0_mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) Real.pi := Set.left_mem_Icc.mpr (by nlinarith [Real.pi_pos])
        have hxpi_mem : Real.pi ∈ Set.Icc (0 : ℝ) Real.pi := Set.right_mem_Icc.mpr (by nlinarith [Real.pi_pos])
        have hx0_le_x : (0 : ℝ) ≤ x := hx.1
        have hx_le_pi : x ≤ Real.pi := hx.2
        have hlow : (fun t : ℝ => y t * deriv y t) (0 : ℝ) ≤ (fun t : ℝ => y t * deriv y t) x :=
          hg_mono hx0_mem hx hx0_le_x
        have hhigh : (fun t : ℝ => y t * deriv y t) x ≤ (fun t : ℝ => y t * deriv y t) Real.pi :=
          hg_mono hx hxpi_mem hx_le_pi
        have hlow' : 0 ≤ y x * deriv y x := by simpa [hg0_val] using hlow
        have hhigh' : y x * deriv y x ≤ 0 := by simpa [hgpi_val] using hhigh
        nlinarith
      
      have hy'_x0 : deriv y x0 = 0 := by
        have hprod : y x0 * deriv y x0 = 0 := hg_eq0 x0 hx0Icc
        exact mul_eq_zero.mp hprod |>.resolve_left hx0nonz
      
      by_cases hlam_zero : lam = 0
      · subst hlam_zero
        set C := connectedComponentIn J 0 with hC
        have hCopen : IsOpen C := IsOpen.connectedComponentIn (F := J) (x := 0) hJopen
        have hCpre : IsPreconnected C := isPreconnected_connectedComponentIn
        have h0C : (0 : ℝ) ∈ C := mem_connectedComponentIn h0J
        have hx0C : x0 ∈ C := by
          have hpre_Icc : IsPreconnected (Set.Icc (0 : ℝ) Real.pi) := isPreconnected_Icc
          have hsubset : Set.Icc (0 : ℝ) Real.pi ⊆ C :=
            hpre_Icc.subset_connectedComponentIn (Set.left_mem_Icc.mpr (by nlinarith [Real.pi_pos])) hJsub
          exact hsubset hx0Icc
        have hy'_const : ∀ x ∈ C, deriv y x = deriv y 0 := by
          have h_diff : DifferentiableOn ℝ (deriv y) C := by
            intro t ht
            have htJ : t ∈ J := connectedComponentIn_subset J 0 ht
            have h' : HasDerivAt (deriv y) (0 : ℝ) t := by simpa using hy' t htJ
            exact h'.differentiableAt.differentiableWithinAt
          have h_deriv_zero : C.EqOn (deriv (deriv y)) 0 := by
            intro t ht
            have htJ : t ∈ J := connectedComponentIn_subset J 0 ht
            have h' : HasDerivAt (deriv y) (0 : ℝ) t := by simpa using hy' t htJ
            exact h'.deriv
          intro t ht
          exact hCopen.is_const_of_deriv_eq_zero hCpre h_diff h_deriv_zero ht h0C
        
        have hy'_zero_on_C : ∀ x ∈ C, deriv y x = 0 := by
          intro x hx
          calc
            deriv y x = deriv y 0 := hy'_const x hx
            _ = deriv y x0 := (hy'_const x0 hx0C).symm
            _ = 0 := hy'_x0
        
        have hy_zero_on_C : ∀ x ∈ C, y x = 0 := by
          have hy_diff : DifferentiableOn ℝ y C := by
            intro t ht
            have htJ : t ∈ J := connectedComponentIn_subset J 0 ht
            exact (hy t htJ).differentiableAt.differentiableWithinAt
          have hy_deriv_zero : C.EqOn (deriv y) 0 := by
            intro t ht
            exact hy'_zero_on_C t ht
          intro x hx
          have h_eq := hCopen.is_const_of_deriv_eq_zero hCpre hy_diff hy_deriv_zero hx h0C
          rw [hy0] at h_eq
          exact h_eq
        
        have hy0_x0 : y x0 = 0 := hy_zero_on_C x0 hx0C
        exact absurd hy0_x0 hx0nonz
      · have hlam_neg : lam < 0 := lt_of_le_of_ne hle hlam_zero
        
        set C := connectedComponentIn J 0 with hC
        have hCopen : IsOpen C := IsOpen.connectedComponentIn (F := J) (x := 0) hJopen
        have hCpre : IsPreconnected C := isPreconnected_connectedComponentIn
        have h0C : (0 : ℝ) ∈ C := mem_connectedComponentIn h0J
        have hx0C : x0 ∈ C := by
          have hpre_Icc : IsPreconnected (Set.Icc (0 : ℝ) Real.pi) := isPreconnected_Icc
          have hsubset : Set.Icc (0 : ℝ) Real.pi ⊆ C :=
            hpre_Icc.subset_connectedComponentIn (Set.left_mem_Icc.mpr (by nlinarith [Real.pi_pos])) hJsub
          exact hsubset hx0Icc
        
        let E : ℝ → ℝ := fun x => (deriv y x)^2 + lam * (y x)^2
        have hE_deriv : ∀ x ∈ J, HasDerivAt E 0 x := by
          intro x hx
          have hyx : HasDerivAt y (deriv y x) x := hy x hx
          have hy'x : HasDerivAt (deriv y) (-(lam * y x)) x := hy' x hx
          have h_deriv_sq1 : HasDerivAt (fun t : ℝ => (deriv y t)^2) (2 * (deriv y x) * (-(lam * y x))) x := by
            have htemp := HasDerivAt.mul hy'x hy'x
            have h_eq : 2 * (deriv y x) * (-(lam * y x)) = (-(lam * y x * deriv y x) + -(deriv y x * (lam * y x))) := by ring
            have htemp' : HasDerivAt (fun t : ℝ => (deriv y t)^2) (-(lam * y x * deriv y x) + -(deriv y x * (lam * y x))) x := by
              simpa [sq] using htemp
            simpa [h_eq] using htemp'
          have h_deriv_sq2 : HasDerivAt (fun t : ℝ => lam * (y t)^2) (lam * (2 * y x * (deriv y x))) x := by
            have h_sq : HasDerivAt (fun t : ℝ => (y t)^2) (2 * y x * (deriv y x)) x := by
              have htemp := HasDerivAt.mul hyx hyx
              have h_eq : 2 * y x * (deriv y x) = (deriv y x * y x + y x * deriv y x) := by ring
              have htemp' : HasDerivAt (fun t : ℝ => (y t)^2) (deriv y x * y x + y x * deriv y x) x := by
                simpa [sq] using htemp
              simpa [h_eq] using htemp'
            simpa [mul_comm, mul_left_comm, mul_assoc] using (HasDerivAt.const_mul lam h_sq)
          have hE : HasDerivAt E (2 * (deriv y x) * (-(lam * y x)) + lam * (2 * y x * (deriv y x))) x :=
            HasDerivAt.add h_deriv_sq1 h_deriv_sq2
          have h_simplify : -(2 * (deriv y x) * (lam * y x)) + lam * (2 * y x * (deriv y x)) = 0 := by ring
          have h_eq : 2 * (deriv y x) * (-(lam * y x)) + lam * (2 * y x * (deriv y x)) = -(2 * (deriv y x) * (lam * y x)) + lam * (2 * y x * (deriv y x)) := by ring
          simpa [h_eq, h_simplify] using hE
        
        have hE_const : ∀ x ∈ C, E x = E 0 := by
          have hE_diff : DifferentiableOn ℝ E C := by
            intro x hx
            have hxJ : x ∈ J := connectedComponentIn_subset J 0 hx
            exact (hE_deriv x hxJ).differentiableAt.differentiableWithinAt
          have hE_deriv_zero : C.EqOn (deriv E) 0 := by
            intro x hx
            have hxJ : x ∈ J := connectedComponentIn_subset J 0 hx
            exact (hE_deriv x hxJ).deriv
          intro x hx
          exact hCopen.is_const_of_deriv_eq_zero hCpre hE_diff hE_deriv_zero hx h0C
        
        have hE0 : E 0 = (deriv y 0)^2 := by
          dsimp [E]; simp [hy0]
        
        have h_rolle : ∃ c ∈ Set.Ioo (0 : ℝ) Real.pi, deriv y c = 0 := by
          have h_cont : ContinuousOn y (Set.Icc (0 : ℝ) Real.pi) := by
            intro z hz
            have hzJ : z ∈ J := hJsub hz
            exact (hy z hzJ).continuousAt.continuousWithinAt
          exact exists_deriv_eq_zero (by exact Real.pi_pos) h_cont (by rw [hy0, hypi])
        
        rcases h_rolle with ⟨c, hc_mem, hc_deriv⟩
        
        have hcC : c ∈ C := by
          have hpre_Icc : IsPreconnected (Set.Icc (0 : ℝ) Real.pi) := isPreconnected_Icc
          have hsubset : Set.Icc (0 : ℝ) Real.pi ⊆ C :=
            hpre_Icc.subset_connectedComponentIn (Set.left_mem_Icc.mpr (by nlinarith [Real.pi_pos])) hJsub
          exact hsubset (Set.mem_Icc.mpr ⟨hc_mem.1.le, hc_mem.2.le⟩)
        
        have hEc : E c = lam * (y c)^2 := by
          dsimp [E]; simp [hc_deriv]
        
        have hEc_eq_E0 : E c = E 0 := hE_const c hcC
        rw [hE0, hEc] at hEc_eq_E0
        
        have hderiv0_zero : deriv y 0 = 0 := by
          have h_nonpos : (deriv y 0)^2 ≤ 0 := by
            have h_rhs_nonpos : lam * (y c)^2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _)
            nlinarith
          nlinarith
        
        have hE_zero_at_x0 : E x0 = 0 := by
          rw [hE_const x0 hx0C, hE0, hderiv0_zero]; simp
        dsimp [E] at hE_zero_at_x0
        
        have hy'_x0_nonzero : deriv y x0 ≠ 0 := by
          have h_neg_lam_pos : 0 < -lam := by linarith
          have h_y_sq_pos : 0 < (y x0)^2 := pow_two_pos_of_ne_zero hx0nonz
          have h_pos : 0 < -lam * (y x0)^2 := mul_pos h_neg_lam_pos h_y_sq_pos
          have h_eq : (deriv y x0)^2 = -lam * (y x0)^2 := by nlinarith
          have h_sq_pos : 0 < (deriv y x0)^2 := by rw [h_eq]; exact h_pos
          intro hzero
          apply h_sq_pos.ne.symm
          simpa [hzero]
        
        have hprod_zero : y x0 * deriv y x0 = 0 := hg_eq0 x0 hx0Icc
        have hy'_x0_zero : deriv y x0 = 0 := mul_eq_zero.mp hprod_zero |>.resolve_left hx0nonz
        
        exact absurd hy'_x0_zero hy'_x0_nonzero
    
  · intro h
    rcases h with ⟨n, hnpos, hlam⟩
    subst hlam
    set y := fun x : ℝ => sin ((n : ℝ) * x) with hy
    refine ⟨y, Set.univ, isOpen_univ, by intro x hx; exact trivial, ?_, ?_, ?_, ?_, ?_⟩
    · intro x _
      have h_deriv : HasDerivAt y ((n : ℝ) * cos ((n : ℝ) * x)) x := by
        dsimp [y]
        have hc : HasDerivAt (fun x' : ℝ => (n : ℝ) * x') (n : ℝ) x := by
          simpa using (HasDerivAt.const_mul (n : ℝ) (hasDerivAt_id x))
        simpa [mul_comm] using hc.sin
      have h_deriv_val : deriv y x = (n : ℝ) * cos ((n : ℝ) * x) := h_deriv.deriv
      rw [h_deriv_val]
      exact h_deriv
    · intro x _
      have h_deriv_y_val : deriv y = fun x' : ℝ => (n : ℝ) * cos ((n : ℝ) * x') := by
        ext x'
        have h_deriv_y_x' : HasDerivAt y ((n : ℝ) * cos ((n : ℝ) * x')) x' := by
          dsimp [y]
          have hc : HasDerivAt (fun z : ℝ => (n : ℝ) * z) (n : ℝ) x' := by
            simpa using (HasDerivAt.const_mul (n : ℝ) (hasDerivAt_id x'))
          simpa [mul_comm] using hc.sin
        exact h_deriv_y_x'.deriv
      rw [h_deriv_y_val]
      have h_deriv_second : HasDerivAt (fun x' : ℝ => (n : ℝ) * cos ((n : ℝ) * x')) (-((n : ℝ)^2) * sin ((n : ℝ) * x)) x := by
        have hc2 : HasDerivAt (fun x' : ℝ => (n : ℝ) * x') (n : ℝ) x := by
          simpa using (HasDerivAt.const_mul (n : ℝ) (hasDerivAt_id x))
        have hcos : HasDerivAt (fun x' : ℝ => cos ((n : ℝ) * x')) (-sin ((n : ℝ) * x) * (n : ℝ)) x :=
          ((Real.hasDerivAt_cos ((n : ℝ) * x)).comp x hc2)
        have h_mul : HasDerivAt (fun x' : ℝ => (n : ℝ) * cos ((n : ℝ) * x')) ((n : ℝ) * (-sin ((n : ℝ) * x) * (n : ℝ))) x :=
          (HasDerivAt.const_mul (n : ℝ) hcos)
        have h_simplify : (n : ℝ) * (-sin ((n : ℝ) * x) * (n : ℝ)) = -((n : ℝ)^2) * sin ((n : ℝ) * x) := by ring
        rw [h_simplify] at h_mul
        exact h_mul
      have h_eq_goal : -(((n : ℝ) ^ 2) * y x) = -((n : ℝ)^2) * sin ((n : ℝ) * x) := by
        dsimp [y]; ring
      simpa [h_eq_goal] using h_deriv_second
    · dsimp [y]; simp
    · dsimp [y]; simpa using Real.sin_nat_mul_pi n
    · have hpos : 0 < Real.pi / (2 * (n : ℝ)) := by
        have h2n_pos : 0 < 2 * (n : ℝ) := by
          have hnpos' : (0 : ℝ) < n := by exact_mod_cast hnpos
          nlinarith
        exact div_pos Real.pi_pos h2n_pos
      have hlt : Real.pi / (2 * (n : ℝ)) < Real.pi := by
        have hnpos' : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.one_le_of_lt hnpos)
        have h2n_pos : 0 < 2 * (n : ℝ) := by nlinarith
        have h2n_gt_one : 1 < 2 * (n : ℝ) := by nlinarith
        have h_recip : 1 / (2 * (n : ℝ)) < 1 := by
          have hpos_one : 0 < (1 : ℝ) := by norm_num
          have htemp := (one_div_lt_one_div h2n_pos hpos_one).mpr h2n_gt_one
          simpa using htemp
        calc
          Real.pi / (2 * (n : ℝ)) = Real.pi * (1 / (2 * (n : ℝ))) := by ring
          _ < Real.pi * 1 := mul_lt_mul_of_pos_left h_recip Real.pi_pos
          _ = Real.pi := by simp
      have hx_mem : Real.pi / (2 * (n : ℝ)) ∈ Set.Ioo (0 : ℝ) Real.pi :=
        Set.mem_Ioo.mpr ⟨hpos, hlt⟩
      have hy_nonzero : y (Real.pi / (2 * (n : ℝ))) ≠ 0 := by
        dsimp [y]
        have h_arg : (n : ℝ) * (Real.pi / (2 * (n : ℝ))) = Real.pi / 2 := by
          field_simp [show (n : ℝ) ≠ 0 from Nat.cast_ne_zero.mpr hnpos.ne']
        rw [h_arg]
        rw [Real.sin_pi_div_two]
        norm_num
      exact ⟨Real.pi / (2 * (n : ℝ)), hx_mem, hy_nonzero⟩

end Submission