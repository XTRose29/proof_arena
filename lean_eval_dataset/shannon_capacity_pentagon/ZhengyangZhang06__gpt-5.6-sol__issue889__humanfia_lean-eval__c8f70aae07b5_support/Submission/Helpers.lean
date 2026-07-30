import ChallengeDeps

open LeanEval.Combinatorics.ShannonCapacityPentagon
open Filter
open scoped BigOperators InnerProductSpace Topology

namespace Submission.Helpers

private noncomputable def τ : ℝ := (Real.sqrt 5 - 1) / 2

private noncomputable def ρ : ℝ := Real.sqrt τ

private noncomputable def δ : ℝ := (Real.sqrt (Real.sqrt 5))⁻¹

private lemma sqrt_five_sq : (Real.sqrt 5) ^ 2 = 5 := by
  norm_num

private lemma sqrt_five_pos : 0 < Real.sqrt 5 := by
  positivity

private lemma τ_pos : 0 < τ := by
  have h : 1 < Real.sqrt 5 := by
    nlinarith [sqrt_five_sq, Real.sqrt_nonneg (5 : ℝ)]
  dsimp [τ]
  linarith

private lemma τ_sq_add : τ ^ 2 + τ = 1 := by
  dsimp [τ]
  nlinarith [sqrt_five_sq]

private lemma ρ_sq : ρ ^ 2 = τ := by
  exact Real.sq_sqrt τ_pos.le

private lemma δ_pos : 0 < δ := by
  dsimp [δ]
  positivity

private lemma δ_sq : δ ^ 2 = (Real.sqrt 5)⁻¹ := by
  have hroot : (Real.sqrt (Real.sqrt 5)) ^ 2 = Real.sqrt 5 :=
    Real.sq_sqrt sqrt_five_pos.le
  dsimp [δ]
  rw [inv_pow, hroot]

private lemma τ_cube : τ ^ 3 = 2 * τ - 1 := by
  calc
    τ ^ 3 = τ * τ ^ 2 := by ring
    _ = τ * (1 - τ) := by rw [show τ ^ 2 = 1 - τ by linarith [τ_sq_add]]
    _ = 2 * τ - 1 := by nlinarith [τ_sq_add]

private lemma sqrt_five_eq : Real.sqrt 5 = 2 * τ + 1 := by
  dsimp [τ]
  ring

private lemma ρτ_sq : (ρ * τ) ^ 2 = τ ^ 3 := by
  rw [mul_pow, ρ_sq]
  ring

private lemma δρτ_sq : (δ * ρ * τ) ^ 2 = δ ^ 2 * τ ^ 3 := by
  rw [mul_pow, mul_pow, ρ_sq]
  ring

private noncomputable def lovaszVec (v : Fin 5) : EuclideanSpace ℝ (Fin 3) :=
  match v.val with
  | 0 => !₂[1, 0, 0]
  | 1 => !₂[τ, ρ, 0]
  | 2 => !₂[0, ρ, τ]
  | 3 => !₂[0, 0, 1]
  | _ => !₂[τ, -(ρ * τ), τ]

private noncomputable def handleVec : EuclideanSpace ℝ (Fin 3) :=
  !₂[δ, δ * ρ * τ, δ]

private lemma lovaszVec_inner_self (v : Fin 5) :
    ⟪lovaszVec v, lovaszVec v⟫_ℝ = 1 := by
  rw [PiLp.inner_apply]
  fin_cases v
  · norm_num [lovaszVec, Fin.sum_univ_succ]
  · simp [lovaszVec, Fin.sum_univ_succ]
    nlinarith [τ_sq_add, ρ_sq]
  · simp [lovaszVec, Fin.sum_univ_succ]
    nlinarith [τ_sq_add, ρ_sq]
  · norm_num [lovaszVec, Fin.sum_univ_succ]
  · simp [lovaszVec, Fin.sum_univ_succ]
    nlinarith [τ_sq_add, ρτ_sq]

private lemma handleVec_inner_self :
    ⟪handleVec, handleVec⟫_ℝ = 1 := by
  rw [PiLp.inner_apply]
  simp [handleVec, Fin.sum_univ_succ]
  have hs : δ ^ 2 * (2 + τ ^ 3) = 1 := by
    rw [δ_sq, τ_cube]
    rw [show 2 + (2 * τ - 1) = Real.sqrt 5 by linarith [sqrt_five_eq]]
    exact inv_mul_cancel₀ sqrt_five_pos.ne'
  nlinarith [δρτ_sq]

private lemma lovaszVec_inner_handle (v : Fin 5) :
    ⟪lovaszVec v, handleVec⟫_ℝ = δ := by
  rw [PiLp.inner_apply]
  fin_cases v
  · simp [lovaszVec, handleVec, Fin.sum_univ_succ]
  · simp [lovaszVec, handleVec, Fin.sum_univ_succ]
    ring_nf
    rw [ρ_sq]
    rw [show δ * τ * τ = δ * τ ^ 2 by ring]
    rw [show τ ^ 2 = 1 - τ by linarith [τ_sq_add]]
    ring
  · simp [lovaszVec, handleVec, Fin.sum_univ_succ]
    ring_nf
    rw [ρ_sq]
    rw [show δ * τ * τ = δ * τ ^ 2 by ring]
    rw [show τ ^ 2 = 1 - τ by linarith [τ_sq_add]]
    ring
  · simp [lovaszVec, handleVec, Fin.sum_univ_succ]
  · simp [lovaszVec, handleVec, Fin.sum_univ_succ]
    ring_nf
    rw [ρ_sq]
    rw [show δ * τ ^ 2 * τ = δ * τ ^ 3 by ring, τ_cube]
    ring

private lemma lovaszVec_inner_zero {v w : Fin 5} (hvw : v ≠ w)
    (hnadj : ¬(SimpleGraph.cycleGraph 5).Adj v w) :
    ⟪lovaszVec v, lovaszVec w⟫_ℝ = 0 := by
  rw [PiLp.inner_apply]
  fin_cases v <;> fin_cases w <;>
    simp [SimpleGraph.cycleGraph_adj', lovaszVec, Fin.sum_univ_succ] at hvw hnadj ⊢
  all_goals try exact (hnadj (by decide)).elim
  all_goals try ring_nf
  all_goals try rw [ρ_sq]
  all_goals try ring

private noncomputable def tensorVec (n : ℕ) (x : Fin n → Fin 5) :
    EuclideanSpace ℝ (Fin n → Fin 3) :=
  WithLp.toLp 2 fun z => ∏ i, lovaszVec (x i) (z i)

private noncomputable def tensorHandle (n : ℕ) :
    EuclideanSpace ℝ (Fin n → Fin 3) :=
  WithLp.toLp 2 fun z => ∏ i, handleVec (z i)

private lemma sum_pi_prod {n : ℕ} (f : Fin n → Fin 3 → ℝ) :
    (∑ z : Fin n → Fin 3, ∏ i, f i (z i)) = ∏ i, ∑ a : Fin 3, f i a := by
  classical
  simpa using
    (Finset.sum_prod_piFinset (R := ℝ) (s := (Finset.univ : Finset (Fin 3))) f)

private lemma tensorVec_inner (n : ℕ) (x y : Fin n → Fin 5) :
    ⟪tensorVec n x, tensorVec n y⟫_ℝ =
      ∏ i, ⟪lovaszVec (x i), lovaszVec (y i)⟫_ℝ := by
  rw [PiLp.inner_apply]
  simp only [tensorVec, PiLp.toLp_apply, Real.inner_apply]
  simp_rw [← Finset.prod_mul_distrib]
  rw [sum_pi_prod (fun i a => lovaszVec (x i) a * lovaszVec (y i) a)]
  apply Finset.prod_congr rfl
  intro i _
  rw [PiLp.inner_apply]
  simp only [Real.inner_apply]

private lemma tensorVec_inner_self (n : ℕ) (x : Fin n → Fin 5) :
    ⟪tensorVec n x, tensorVec n x⟫_ℝ = 1 := by
  rw [tensorVec_inner]
  simp only [lovaszVec_inner_self, Finset.prod_const_one]

private lemma tensorHandle_inner_self (n : ℕ) :
    ⟪tensorHandle n, tensorHandle n⟫_ℝ = 1 := by
  rw [PiLp.inner_apply]
  simp only [tensorHandle, PiLp.toLp_apply, Real.inner_apply]
  simp_rw [← Finset.prod_mul_distrib]
  rw [sum_pi_prod (fun _ a => handleVec a * handleVec a)]
  have hbase : (∑ a : Fin 3, handleVec a * handleVec a) = 1 := by
    change ⟪handleVec, handleVec⟫_ℝ = 1
    exact handleVec_inner_self
  simp only [hbase, Finset.prod_const_one]

private lemma tensorVec_inner_handle (n : ℕ) (x : Fin n → Fin 5) :
    ⟪tensorVec n x, tensorHandle n⟫_ℝ = δ ^ n := by
  rw [PiLp.inner_apply]
  simp only [tensorVec, tensorHandle, PiLp.toLp_apply, Real.inner_apply]
  simp_rw [← Finset.prod_mul_distrib]
  rw [sum_pi_prod (fun i a => lovaszVec (x i) a * handleVec a)]
  have hbase (i : Fin n) :
      (∑ a : Fin 3, lovaszVec (x i) a * handleVec a) = δ := by
    have h := lovaszVec_inner_handle (x i)
    rw [PiLp.inner_apply] at h
    simpa only [Real.inner_apply] using h
  simp only [hbase, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

private lemma tensorVec_inner_zero_of_not_adj {n : ℕ} {x y : Fin n → Fin 5}
    (hxy : x ≠ y) (hnadj : ¬(strongPower (SimpleGraph.cycleGraph 5) n).Adj x y) :
    ⟪tensorVec n x, tensorVec n y⟫_ℝ = 0 := by
  have hi : ∃ i, x i ≠ y i ∧ ¬(SimpleGraph.cycleGraph 5).Adj (x i) (y i) := by
    by_contra! h
    exact hnadj ⟨hxy, fun i => by
      by_cases heq : x i = y i
      · exact Or.inl heq
      · exact Or.inr (h i heq)⟩
  obtain ⟨i, hne, hnot⟩ := hi
  rw [tensorVec_inner]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (lovaszVec_inner_zero hne hnot)

private lemma independent_card_le_sqrt_five_pow {n : ℕ}
    {s : Finset (Fin n → Fin 5)}
    (hs : IsIndependent (strongPower (SimpleGraph.cycleGraph 5) n) s) :
    (s.card : ℝ) ≤ (Real.sqrt 5) ^ n := by
  let v : ↥s → EuclideanSpace ℝ (Fin n → Fin 3) := fun x => tensorVec n x.1
  have hv : Orthonormal ℝ v := by
    rw [orthonormal_iff_ite]
    intro x y
    by_cases hxy : x = y
    · subst y
      rw [if_pos rfl]
      exact tensorVec_inner_self n x.1
    · have hval : x.1 ≠ y.1 := fun h => hxy (Subtype.ext h)
      have hnot := hs x.2 y.2 hval
      rw [if_neg hxy]
      exact tensorVec_inner_zero_of_not_adj hval hnot
  have hb := hv.sum_inner_products_le (tensorHandle n) (s := Finset.univ)
  have hnorm : ‖tensorHandle n‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq]
    exact tensorHandle_inner_self n
  rw [hnorm] at hb
  have hδn : 0 ≤ δ ^ n := pow_nonneg δ_pos.le n
  dsimp [v] at hb
  simp_rw [tensorVec_inner_handle] at hb
  simp only [abs_of_nonneg hδn, Finset.sum_const, nsmul_eq_mul] at hb
  have hcoef : (δ ^ n) ^ 2 = ((Real.sqrt 5) ^ n)⁻¹ := by
    calc
      (δ ^ n) ^ 2 = (δ * δ) ^ n := by rw [pow_two, mul_pow]
      _ = (δ ^ 2) ^ n := by rw [pow_two]
      _ = ((Real.sqrt 5)⁻¹) ^ n := by rw [δ_sq]
      _ = ((Real.sqrt 5) ^ n)⁻¹ := by rw [inv_pow]
  rw [hcoef] at hb
  have hp : 0 < (Real.sqrt 5) ^ n := pow_pos sqrt_five_pos n
  have hdiv : (s.card : ℝ) / (Real.sqrt 5) ^ n ≤ 1 := by
    simpa [div_eq_mul_inv, Finset.card_attach] using hb
  have hle := (div_le_iff₀ hp).mp hdiv
  simpa using hle

private def pentagonPair (v : Fin 5) : Fin 2 → Fin 5 :=
  match v.val with
  | 0 => ![0, 0]
  | 1 => ![1, 2]
  | 2 => ![2, 4]
  | 3 => ![3, 1]
  | _ => ![4, 3]

@[simp]
private lemma pentagonPair_zero (v : Fin 5) : pentagonPair v 0 = v := by
  fin_cases v <;> rfl

private lemma pentagonPair_separates (v w : Fin 5) (hvw : v ≠ w) :
    ∃ i : Fin 2,
      pentagonPair v i ≠ pentagonPair w i ∧
        ¬(SimpleGraph.cycleGraph 5).Adj (pentagonPair v i) (pentagonPair w i) := by
  fin_cases v <;> fin_cases w <;>
    simp [pentagonPair, SimpleGraph.cycleGraph_adj', Fin.exists_fin_two] at hvw ⊢
  all_goals decide

private def pairedIndex {n : ℕ} (j : Fin (n / 2)) (i : Fin 2) : Fin n :=
  ⟨(finProdFinEquiv (j, i)).val,
    (finProdFinEquiv (j, i)).isLt.trans_le (Nat.div_mul_le_self n 2)⟩

private def pairedWord (n : ℕ) (x : Fin (n / 2) → Fin 5) : Fin n → Fin 5 :=
  fun i =>
    if h : i.val < n / 2 * 2 then
      let ji := finProdFinEquiv.symm (⟨i.val, h⟩ : Fin (n / 2 * 2))
      pentagonPair (x ji.1) ji.2
    else
      0

@[simp]
private lemma pairedWord_pairedIndex {n : ℕ} (x : Fin (n / 2) → Fin 5)
    (j : Fin (n / 2)) (i : Fin 2) :
    pairedWord n x (pairedIndex j i) = pentagonPair (x j) i := by
  have hlt : (pairedIndex j i).val < n / 2 * 2 := by
    change (finProdFinEquiv (j, i)).val < n / 2 * 2
    exact (finProdFinEquiv (j, i)).isLt
  have heq :
      finProdFinEquiv.symm
          (⟨(pairedIndex j i).val, hlt⟩ : Fin (n / 2 * 2)) =
        (j, i) := by
    apply finProdFinEquiv.injective
    rw [Equiv.apply_symm_apply]
    rfl
  simp only [pairedWord, dif_pos hlt]
  rw [heq]

private lemma pairedWord_injective (n : ℕ) : Function.Injective (pairedWord n) := by
  intro x y hxy
  funext j
  have hj := congrFun hxy (pairedIndex j (0 : Fin 2))
  simpa using hj

private def pairedEmbedding (n : ℕ) :
    (Fin (n / 2) → Fin 5) ↪ (Fin n → Fin 5) :=
  ⟨pairedWord n, pairedWord_injective n⟩

private def pairedCodeSet (n : ℕ) : Finset (Fin n → Fin 5) :=
  Finset.univ.map (pairedEmbedding n)

private lemma pairedCodeSet_card (n : ℕ) :
    (pairedCodeSet n).card = 5 ^ (n / 2) := by
  simp [pairedCodeSet]

private lemma pairedCodeSet_independent (n : ℕ) :
    IsIndependent (strongPower (SimpleGraph.cycleGraph 5) n) (pairedCodeSet n) := by
  intro v hv w hw hvw hadj
  simp only [pairedCodeSet, Finset.mem_map] at hv hw
  obtain ⟨x, _, rfl⟩ := hv
  obtain ⟨y, _, rfl⟩ := hw
  have hxy : x ≠ y := fun h => hvw (congrArg (pairedEmbedding n) h)
  have hcoord : ∃ j, x j ≠ y j := by
    by_contra! h
    exact hxy (funext h)
  obtain ⟨j, hj⟩ := hcoord
  obtain ⟨i, hne, hnadj⟩ := pentagonPair_separates (x j) (y j) hj
  have hi := hadj.2 (pairedIndex j i)
  change
    pairedWord n x (pairedIndex j i) = pairedWord n y (pairedIndex j i) ∨
      (SimpleGraph.cycleGraph 5).Adj
        (pairedWord n x (pairedIndex j i)) (pairedWord n y (pairedIndex j i))
    at hi
  simp only [pairedWord_pairedIndex] at hi
  exact hi.elim (fun h => hne h) (fun h => hnadj h)

private lemma independentData_bddAbove (V : Type*) [Fintype V] (G : SimpleGraph V) :
    BddAbove {m : ℕ | ∃ s : Finset V, IsIndependent G s ∧ s.card = m} := by
  refine ⟨Fintype.card V, ?_⟩
  rintro m ⟨s, _, rfl⟩
  exact Finset.card_le_univ s

private lemma independentData_nonempty (V : Type*) [Fintype V] (G : SimpleGraph V) :
    Set.Nonempty {m : ℕ | ∃ s : Finset V, IsIndependent G s ∧ s.card = m} := by
  refine ⟨0, ∅, ?_, rfl⟩
  simp [IsIndependent]

private lemma independenceNumber_lower (n : ℕ) :
    5 ^ (n / 2) ≤
      independenceNumber (Fin n → Fin 5) (strongPower (SimpleGraph.cycleGraph 5) n) := by
  rw [independenceNumber]
  apply le_csSup (independentData_bddAbove _ _)
  exact ⟨pairedCodeSet n, pairedCodeSet_independent n, pairedCodeSet_card n⟩

private lemma independenceNumber_upper (n : ℕ) :
    (independenceNumber (Fin n → Fin 5)
        (strongPower (SimpleGraph.cycleGraph 5) n) : ℝ) ≤
      (Real.sqrt 5) ^ n := by
  have hmem :=
    Nat.sSup_mem
      (independentData_nonempty (Fin n → Fin 5)
        (strongPower (SimpleGraph.cycleGraph 5) n))
      (independentData_bddAbove (Fin n → Fin 5)
        (strongPower (SimpleGraph.cycleGraph 5) n))
  change ∃ s : Finset (Fin n → Fin 5),
    IsIndependent (strongPower (SimpleGraph.cycleGraph 5) n) s ∧
      s.card =
        independenceNumber (Fin n → Fin 5)
          (strongPower (SimpleGraph.cycleGraph 5) n) at hmem
  obtain ⟨s, hs, hcard⟩ := hmem
  calc
    (independenceNumber (Fin n → Fin 5)
        (strongPower (SimpleGraph.cycleGraph 5) n) : ℝ) =
        s.card := by exact_mod_cast hcard.symm
    _ ≤ (Real.sqrt 5) ^ n := independent_card_le_sqrt_five_pow hs

private lemma pairedExponent_tendsto :
    Tendsto
      (fun k : ℕ => (((k + 1) / 2 : ℕ) : ℝ) * ((k + 1 : ℝ)⁻¹))
      Filter.atTop (𝓝 (1 / 2 : ℝ)) := by
  have hmod :
      Tendsto
        (fun k : ℕ => (((k + 1) % 2 : ℕ) : ℝ) / (k + 1 : ℝ))
        Filter.atTop (𝓝 0) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      ((Filter.tendsto_add_atTop_iff_nat 1).2
        (tendsto_mod_div_atTop_nhds_zero_nat (by norm_num : 0 < 2)))
  have hlim :
      Tendsto
        (fun k : ℕ =>
          (1 / 2 : ℝ) -
            (1 / 2 : ℝ) * ((((k + 1) % 2 : ℕ) : ℝ) / (k + 1 : ℝ)))
        Filter.atTop (𝓝 (1 / 2 : ℝ)) := by
    convert tendsto_const_nhds.sub (tendsto_const_nhds.mul hmod) using 1
    all_goals norm_num
  refine hlim.congr' (Filter.Eventually.of_forall fun k => ?_)
  have hdivmod : ((k + 1) / 2) * 2 + (k + 1) % 2 = k + 1 :=
    calc
      (k + 1) / 2 * 2 + (k + 1) % 2 =
          2 * ((k + 1) / 2) + (k + 1) % 2 := by rw [Nat.mul_comm]
      _ = k + 1 := Nat.div_add_mod (k + 1) 2
  have hdivmodReal :
      (((k + 1) / 2 : ℕ) : ℝ) * 2 + (((k + 1) % 2 : ℕ) : ℝ) =
        (k + 1 : ℝ) := by
    exact_mod_cast hdivmod
  have hk : (k + 1 : ℝ) ≠ 0 := by positivity
  field_simp [hk]
  nlinarith

theorem hasShannonCapacityPentagon :
    HasShannonCapacity (SimpleGraph.cycleGraph 5) (Real.sqrt 5) := by
  unfold HasShannonCapacity
  have hlower (k : ℕ) :
      (5 : ℝ) ^
          ((((k + 1) / 2 : ℕ) : ℝ) * ((k + 1 : ℝ)⁻¹)) ≤
        Real.rpow
          (independenceNumber (Fin (k + 1) → Fin 5)
            (strongPower (SimpleGraph.cycleGraph 5) (k + 1)) : ℝ)
          ((k + 1 : ℝ)⁻¹) := by
    have hcast :
        ((5 ^ ((k + 1) / 2) : ℕ) : ℝ) ≤
          (independenceNumber (Fin (k + 1) → Fin 5)
            (strongPower (SimpleGraph.cycleGraph 5) (k + 1)) : ℝ) := by
      exact_mod_cast (independenceNumber_lower (k + 1))
    have hrpow :=
      Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ (5 ^ ((k + 1) / 2) : ℕ))
        hcast (by positivity : (0 : ℝ) ≤ (k + 1 : ℝ)⁻¹)
    calc
      (5 : ℝ) ^
          ((((k + 1) / 2 : ℕ) : ℝ) * ((k + 1 : ℝ)⁻¹)) =
          ((5 : ℝ) ^ ((k + 1) / 2)) ^ ((k + 1 : ℝ)⁻¹) :=
        Real.rpow_natCast_mul (by norm_num) _ _
      _ = ((5 ^ ((k + 1) / 2) : ℕ) : ℝ) ^ ((k + 1 : ℝ)⁻¹) := by
        norm_cast
      _ ≤ _ := hrpow
  have hupper (k : ℕ) :
      Real.rpow
          (independenceNumber (Fin (k + 1) → Fin 5)
            (strongPower (SimpleGraph.cycleGraph 5) (k + 1)) : ℝ)
          ((k + 1 : ℝ)⁻¹) ≤
        Real.sqrt 5 := by
    have hrpow :=
      Real.rpow_le_rpow
        (Nat.cast_nonneg
          (independenceNumber (Fin (k + 1) → Fin 5)
            (strongPower (SimpleGraph.cycleGraph 5) (k + 1))))
        (independenceNumber_upper (k + 1))
        (by positivity : (0 : ℝ) ≤ (k + 1 : ℝ)⁻¹)
    calc
      Real.rpow
          (independenceNumber (Fin (k + 1) → Fin 5)
            (strongPower (SimpleGraph.cycleGraph 5) (k + 1)) : ℝ)
          ((k + 1 : ℝ)⁻¹) ≤
          ((Real.sqrt 5) ^ (k + 1)) ^ ((k + 1 : ℝ)⁻¹) := hrpow
      _ = Real.sqrt 5 := by
        simpa using
          (Real.pow_rpow_inv_natCast (Real.sqrt_nonneg 5) (Nat.succ_ne_zero k))
  have hlower_tendsto :
      Tendsto
        (fun k : ℕ =>
          (5 : ℝ) ^
            ((((k + 1) / 2 : ℕ) : ℝ) * ((k + 1 : ℝ)⁻¹)))
        Filter.atTop (𝓝 (Real.sqrt 5)) := by
    simpa [Real.sqrt_eq_rpow] using
      (tendsto_const_nhds.rpow pairedExponent_tendsto
        (Or.inl (by norm_num : (5 : ℝ) ≠ 0)))
  exact
    tendsto_of_tendsto_of_tendsto_of_le_of_le
      hlower_tendsto tendsto_const_nhds hlower hupper

end Submission.Helpers
