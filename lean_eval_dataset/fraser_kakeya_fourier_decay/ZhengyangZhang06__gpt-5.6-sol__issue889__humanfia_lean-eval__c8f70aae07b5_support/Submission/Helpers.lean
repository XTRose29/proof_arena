import ChallengeDeps

open LeanEval.Combinatorics.FraserKakeyaProblem
open scoped BigOperators

namespace Submission.Helpers

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The sum and product of an unordered pair, viewed as a point of the plane. -/
def pairPoint : Sym2 F → Space F 2 :=
  Sym2.lift ⟨fun a b => ![a + b, a * b], fun a b => by
    ext i
    fin_cases i <;> simp [add_comm, mul_comm]⟩

omit [Fintype F] [DecidableEq F] in
@[simp]
theorem pairPoint_mk (a b : F) : pairPoint s(a, b) = ![a + b, a * b] :=
  rfl

/-- A planar Kakeya set: coefficient pairs of split monic quadratics, with one vertical line. -/
def planarFinset : Finset (Space F 2) :=
  Finset.univ.image pairPoint ∪ Finset.univ.image fun t : F => ![0, t]

def planarSet : Set (Space F 2) :=
  ↑(planarFinset (F := F))

theorem planarFinset_card_le :
    (planarFinset (F := F)).card ≤ Fintype.card (Sym2 F) + Fintype.card F := by
  classical
  exact (Finset.card_union_le _ _).trans <|
    Nat.add_le_add Finset.card_image_le Finset.card_image_le

theorem planarFinset_card_real_bound :
    2 * ((planarFinset (F := F)).card : ℝ) ≤
      (Fintype.card F : ℝ) * ((Fintype.card F : ℝ) + 3) := by
  calc
    2 * ((planarFinset (F := F)).card : ℝ) ≤
        2 * (Fintype.card (Sym2 F) + Fintype.card F : ℕ) := by
          exact_mod_cast Nat.mul_le_mul_left 2 (planarFinset_card_le (F := F))
    _ = (Fintype.card F : ℝ) * ((Fintype.card F : ℝ) + 3) := by
      rw [Sym2.card, Nat.cast_add, Nat.cast_choose_two]
      push_cast
      ring

theorem planar_isKakeya : IsKakeya (planarSet (F := F)) := by
  classical
  intro x
  by_cases hx : x 0 = 0
  · refine ⟨0, ?_⟩
    rintro z ⟨a, rfl⟩
    change 0 + a • x ∈ (planarFinset (F := F) : Set (Space F 2))
    apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    refine ⟨a * x 1, Finset.mem_univ _, ?_⟩
    ext i
    fin_cases i <;> simp [hx]
  · let m : F := x 1 / x 0
    refine ⟨![m, 0], ?_⟩
    rintro z ⟨a, rfl⟩
    change ![m, 0] + a • x ∈ (planarFinset (F := F) : Set (Space F 2))
    apply Finset.mem_union_left
    apply Finset.mem_image.mpr
    refine ⟨s(m, a * x 0), Finset.mem_univ _, ?_⟩
    rw [pairPoint_mk]
    ext i
    fin_cases i
    · simp [m, add_comm]
    · simp [m]
      field_simp

/-- The first two coordinates of a vector in dimension `2 + n`. -/
def head₂ {n : ℕ} (x : Space F (2 + n)) : Space F 2 :=
  fun i => x (Fin.castAdd n i)

/-- Extend a planar vector by zero in the remaining coordinates. -/
def extend₂ {n : ℕ} (x : Space F 2) : Space F (2 + n) :=
  Fin.addCases x fun _ => 0

omit [Fintype F] [DecidableEq F] in
@[simp]
theorem head₂_extend₂ {n : ℕ} (x : Space F 2) :
    head₂ (extend₂ (n := n) x) = x := by
  ext i
  simp [head₂, extend₂]

omit [Fintype F] [DecidableEq F] in
@[simp]
theorem head₂_add_smul {n : ℕ} (y x : Space F (2 + n)) (a : F) :
    head₂ (y + a • x) = head₂ y + a • head₂ x := by
  ext i
  simp [head₂]

/-- Lift the planar construction to arbitrary dimension without changing its projection. -/
def liftedPlanarSet {n : ℕ} : Set (Space F (2 + n)) :=
  {x | head₂ x ∈ planarSet (F := F)}

theorem liftedPlanar_isKakeya {n : ℕ} :
    IsKakeya (liftedPlanarSet (F := F) (n := n)) := by
  intro x
  obtain ⟨y, hy⟩ := planar_isKakeya (F := F) (head₂ x)
  refine ⟨extend₂ (n := n) y, ?_⟩
  rintro z ⟨a, rfl⟩
  change head₂ (extend₂ (n := n) y + a • x) ∈ planarSet (F := F)
  rw [head₂_add_smul, head₂_extend₂]
  exact hy ⟨a, rfl⟩

theorem sum_char_dot_plane (χ : AddChar F ℂ) (hχ : χ.IsPrimitive) (z : Space F 2) :
    ∑ ξ : Space F 2, χ (dot ξ z) =
      if z = 0 then (Fintype.card F : ℂ) ^ 2 else 0 := by
  classical
  rw [Fintype.sum_equiv (finTwoArrowEquiv F)
    (fun ξ : Space F 2 => χ (dot ξ z))
    (fun p : F × F => χ (p.1 * z 0 + p.2 * z 1))]
  · rw [Fintype.sum_prod_type]
    simp_rw [AddChar.map_add_eq_mul]
    simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul]
    rw [AddChar.sum_mulShift (z 0) hχ, AddChar.sum_mulShift (z 1) hχ]
    by_cases hz : z = 0
    · subst z
      simp [pow_two]
    · have hcoord : z 0 ≠ 0 ∨ z 1 ≠ 0 := by
        contrapose! hz
        ext i
        fin_cases i <;> simp_all
      rcases hcoord with h0 | h1
      · simp [hz, h0]
      · simp [hz, h1]
  · intro ξ
    simp [dot, Fin.sum_univ_two]

omit [DecidableEq F] in
theorem star_char_neg (χ : AddChar F ℂ) (a : F) :
    (starRingEnd ℂ) (χ (-a)) = χ a := by
  calc
    (starRingEnd ℂ) (χ (-a)) = (χ (-a))⁻¹ :=
      (AddChar.inv_apply_eq_conj χ (-a)).symm
    _ = χ a := by rw [AddChar.map_neg_eq_inv, inv_inv]

omit [Fintype F] [DecidableEq F] in
theorem dot_sub_right {d : ℕ} (ξ x y : Space F d) :
    dot ξ (y - x) = dot ξ y - dot ξ x := by
  simp [dot, mul_sub, Finset.sum_sub_distrib]

omit [DecidableEq F] in
theorem fourier_mul_star_expand (χ : AddChar F ℂ) (ν : Space F 2 → ℝ)
    (ξ : Space F 2) :
    fourier χ ν ξ * (starRingEnd ℂ) (fourier χ ν ξ) =
      ∑ x : Space F 2, ∑ y : Space F 2,
        χ (dot ξ (y - x)) * ((ν x * ν y : ℝ) : ℂ) := by
  classical
  unfold LeanEval.Combinatorics.FraserKakeyaProblem.fourier
  rw [map_sum, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  rw [map_mul]
  rw [star_char_neg χ (dot ξ y)]
  rw [show (starRingEnd ℂ) ((ν y : ℝ) : ℂ) = (ν y : ℂ) by
    simpa only [starRingEnd_apply] using Complex.conj_ofReal (ν y)]
  calc
    χ (-dot ξ x) * (ν x : ℂ) * (χ (dot ξ y) * (ν y : ℂ)) =
        (χ (-dot ξ x) * χ (dot ξ y)) * ((ν x : ℂ) * (ν y : ℂ)) := by ring
    _ = χ (-dot ξ x + dot ξ y) * ((ν x : ℂ) * (ν y : ℂ)) := by
      rw [AddChar.map_add_eq_mul]
    _ = χ (dot ξ (y - x)) * ((ν x * ν y : ℝ) : ℂ) := by
      rw [dot_sub_right]
      congr 1
      · ring_nf
      · simp

theorem parseval_plane_complex (χ : AddChar F ℂ) (hχ : χ.IsPrimitive)
    (ν : Space F 2 → ℝ) :
    ∑ ξ : Space F 2,
        fourier χ ν ξ * (starRingEnd ℂ) (fourier χ ν ξ) =
      (Fintype.card F : ℂ) ^ 2 * ∑ x : Space F 2, ((ν x) ^ 2 : ℂ) := by
  classical
  calc
    _ = ∑ ξ : Space F 2, ∑ x : Space F 2, ∑ y : Space F 2,
          χ (dot ξ (y - x)) * ((ν x * ν y : ℝ) : ℂ) := by
        apply Finset.sum_congr rfl
        intro ξ _
        exact fourier_mul_star_expand χ ν ξ
    _ = ∑ x : Space F 2, ∑ y : Space F 2, ∑ ξ : Space F 2,
          χ (dot ξ (y - x)) * ((ν x * ν y : ℝ) : ℂ) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.sum_comm]
    _ = ∑ x : Space F 2, ∑ y : Space F 2,
          (∑ ξ : Space F 2, χ (dot ξ (y - x))) * ((ν x * ν y : ℝ) : ℂ) := by
        apply Finset.sum_congr rfl
        intro x _
        apply Finset.sum_congr rfl
        intro y _
        rw [Finset.sum_mul]
    _ = ∑ x : Space F 2, ∑ y : Space F 2,
          (if y - x = 0 then (Fintype.card F : ℂ) ^ 2 else 0) *
            ((ν x * ν y : ℝ) : ℂ) := by
        simp_rw [sum_char_dot_plane χ hχ]
    _ = (Fintype.card F : ℂ) ^ 2 * ∑ x : Space F 2, ((ν x) ^ 2 : ℂ) := by
        simp [sub_eq_zero, Finset.mul_sum, pow_two]

theorem parseval_plane (χ : AddChar F ℂ) (hχ : χ.IsPrimitive)
    (ν : Space F 2 → ℝ) :
    ∑ ξ : Space F 2, ‖fourier χ ν ξ‖ ^ 2 =
      (Fintype.card F : ℝ) ^ 2 * ∑ x : Space F 2, (ν x) ^ 2 := by
  apply Complex.ofReal_injective
  calc
    ((∑ ξ : Space F 2, ‖fourier χ ν ξ‖ ^ 2 : ℝ) : ℂ) =
        ∑ ξ : Space F 2, (‖fourier χ ν ξ‖ ^ 2 : ℂ) := by
            simp
    _ = ∑ ξ : Space F 2,
        fourier χ ν ξ * (starRingEnd ℂ) (fourier χ ν ξ) := by
            apply Finset.sum_congr rfl
            intro ξ _
            rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
            exact (Complex.ofReal_pow _ _).symm
    _ = (Fintype.card F : ℂ) ^ 2 * ∑ x : Space F 2, ((ν x) ^ 2 : ℂ) :=
      parseval_plane_complex χ hχ ν
    _ = (((Fintype.card F : ℝ) ^ 2 * ∑ x : Space F 2, (ν x) ^ 2 : ℝ) : ℂ) := by
      simp

theorem planar_sum_sq_lower {ν : Space F 2 → ℝ}
    (hνsum : ∑ x, ν x = 1)
    (hνsupport : ∀ x, ν x ≠ 0 → x ∈ planarSet (F := F)) :
    2 ≤ (Fintype.card F : ℝ) * ((Fintype.card F : ℝ) + 3) *
      ∑ x : Space F 2, (ν x) ^ 2 := by
  classical
  have hsum_planar : ∑ x ∈ planarFinset (F := F), ν x = 1 := by
    rw [← hνsum]
    apply Finset.sum_subset (Finset.subset_univ _)
    intro x _ hx
    by_contra hne
    exact hx (hνsupport x hne)
  have hcauchy := sq_sum_le_card_mul_sum_sq
    (s := planarFinset (F := F)) (f := ν)
  rw [hsum_planar, one_pow] at hcauchy
  have hsq_nonneg : 0 ≤ ∑ x ∈ planarFinset (F := F), (ν x) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hsq_le : (∑ x ∈ planarFinset (F := F), (ν x) ^ 2) ≤
      ∑ x : Space F 2, (ν x) ^ 2 := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun _ _ _ => sq_nonneg _)
  have hcard := planarFinset_card_real_bound (F := F)
  calc
    2 ≤ 2 * (((planarFinset (F := F)).card : ℝ) *
        ∑ x ∈ planarFinset (F := F), (ν x) ^ 2) := by nlinarith
    _ ≤ ((Fintype.card F : ℝ) * ((Fintype.card F : ℝ) + 3)) *
        ∑ x ∈ planarFinset (F := F), (ν x) ^ 2 := by
          simpa [mul_assoc] using mul_le_mul_of_nonneg_right hcard hsq_nonneg
    _ ≤ ((Fintype.card F : ℝ) * ((Fintype.card F : ℝ) + 3)) *
        ∑ x : Space F 2, (ν x) ^ 2 := by
          exact mul_le_mul_of_nonneg_left hsq_le (by positivity)
    _ = (Fintype.card F : ℝ) * ((Fintype.card F : ℝ) + 3) *
        ∑ x : Space F 2, (ν x) ^ 2 := by ring

omit [DecidableEq F] in
theorem fourier_zero_of_sum_eq_one (χ : AddChar F ℂ) {ν : Space F 2 → ℝ}
    (hνsum : ∑ x, ν x = 1) :
    fourier χ ν 0 = 1 := by
  unfold LeanEval.Combinatorics.FraserKakeyaProblem.fourier
  simp only [dot, Pi.zero_apply, zero_mul, Finset.sum_const_zero,
    neg_zero, AddChar.map_zero_eq_one, one_mul]
  rw [← Complex.ofReal_sum, hνsum]
  norm_num

theorem nonzero_energy_lower (χ : AddChar F ℂ) (hχ : χ.IsPrimitive)
    {ν : Space F 2 → ℝ} (hνsum : ∑ x, ν x = 1)
    (hνsupport : ∀ x, ν x ≠ 0 → x ∈ planarSet (F := F)) :
    (Fintype.card F : ℝ) - 3 ≤
      ((Fintype.card F : ℝ) + 3) *
        ∑ ξ ∈ (Finset.univ : Finset (Space F 2)).erase 0,
          ‖fourier χ ν ξ‖ ^ 2 := by
  classical
  let q : ℝ := Fintype.card F
  let total : ℝ := ∑ ξ : Space F 2,
    ‖fourier χ ν ξ‖ ^ 2
  let rest : ℝ := ∑ ξ ∈ (Finset.univ : Finset (Space F 2)).erase 0,
    ‖fourier χ ν ξ‖ ^ 2
  let squareMass : ℝ := ∑ x : Space F 2, (ν x) ^ 2
  have hsquare : 2 ≤ q * (q + 3) * squareMass := by
    simpa [q, squareMass] using planar_sum_sq_lower (F := F) hνsum hνsupport
  have hparseval : total = q ^ 2 * squareMass := by
    simpa [total, q, squareMass] using parseval_plane χ hχ ν
  have hqnonneg : 0 ≤ q := by positivity
  have henergy : 2 * q ≤ (q + 3) * total := by
    calc
      2 * q ≤ q * (q * (q + 3) * squareMass) := by
        simpa [mul_assoc, mul_comm, mul_left_comm] using
          mul_le_mul_of_nonneg_left hsquare hqnonneg
      _ = (q + 3) * (q ^ 2 * squareMass) := by ring
      _ = (q + 3) * total := by rw [← hparseval]
  have hzero :
      ‖fourier χ ν 0‖ ^ 2 = 1 := by
    rw [fourier_zero_of_sum_eq_one χ hνsum]
    norm_num
  have hsplit : total = rest + 1 := by
    dsimp [total, rest]
    calc
      (∑ ξ : Space F 2, ‖fourier χ ν ξ‖ ^ 2) =
          (∑ ξ ∈ (Finset.univ : Finset (Space F 2)).erase 0,
            ‖fourier χ ν ξ‖ ^ 2) + ‖fourier χ ν 0‖ ^ 2 :=
        (Finset.sum_erase_add Finset.univ
          (fun ξ : Space F 2 => ‖fourier χ ν ξ‖ ^ 2)
          (Finset.mem_univ 0)).symm
      _ = _ := by rw [hzero]
  dsimp [q, rest] at henergy hsplit ⊢
  nlinarith

theorem exists_large_fourier_plane (χ : AddChar F ℂ) (hχ : χ.IsPrimitive)
    {κ : ℝ} (hκ : 0 < κ)
    (hthreshold : κ ^ 2 * ((Fintype.card F : ℝ) + 3) ≤
      (Fintype.card F : ℝ) - 3)
    {ν : Space F 2 → ℝ} (hνsum : ∑ x, ν x = 1)
    (hνsupport : ∀ x, ν x ≠ 0 → x ∈ planarSet (F := F)) :
    ∃ ξ : Space F 2, ξ ≠ 0 ∧
      κ * (Fintype.card F : ℝ)⁻¹ ≤ ‖fourier χ ν ξ‖ := by
  classical
  let q : ℝ := Fintype.card F
  let frequencies : Finset (Space F 2) := Finset.univ.erase 0
  let energy : ℝ := ∑ ξ ∈ frequencies, ‖fourier χ ν ξ‖ ^ 2
  have hq : 0 < q := by positivity
  have henergy := nonzero_energy_lower χ hχ hνsum hνsupport
  have hkappa_energy : κ ^ 2 ≤ energy := by
    have hprod : κ ^ 2 * (q + 3) ≤ (q + 3) * energy := by
      calc
        κ ^ 2 * (q + 3) ≤ q - 3 := by simpa [q] using hthreshold
        _ ≤ (q + 3) * energy := by simpa [q, energy, frequencies] using henergy
    have hq3 : 0 < q + 3 := by positivity
    exact le_of_mul_le_mul_right (by simpa [mul_comm] using hprod) hq3
  by_contra! hlarge
  have hvector_ne : (![1, 0] : Space F 2) ≠ 0 := by
    intro h
    have h0 := congrFun h 0
    simp at h0
  have hfrequencies : frequencies.Nonempty := by
    refine ⟨![1, 0], ?_⟩
    exact Finset.mem_erase.mpr ⟨hvector_ne, Finset.mem_univ _⟩
  have hterm : ∀ ξ ∈ frequencies,
      q ^ 2 * ‖fourier χ ν ξ‖ ^ 2 < κ ^ 2 := by
    intro ξ hξ
    have hξne : ξ ≠ 0 := (Finset.mem_erase.mp hξ).1
    have hnorm := hlarge ξ hξne
    have hscaled : q * ‖fourier χ ν ξ‖ < κ := by
      have := mul_lt_mul_of_pos_left hnorm hq
      calc
        q * ‖fourier χ ν ξ‖ < q * (κ * q⁻¹) := this
        _ = κ := by field_simp
    have hsquare := (sq_lt_sq₀
      (mul_nonneg hq.le (norm_nonneg _)) hκ.le).2 hscaled
    nlinarith
  have hsum_scaled : q ^ 2 * energy < (frequencies.card : ℝ) * κ ^ 2 := by
    calc
      q ^ 2 * energy = ∑ ξ ∈ frequencies,
          q ^ 2 * ‖fourier χ ν ξ‖ ^ 2 := by
            simp [energy, Finset.mul_sum]
      _ < ∑ _ξ ∈ frequencies, κ ^ 2 :=
        Finset.sum_lt_sum_of_nonempty hfrequencies hterm
      _ = (frequencies.card : ℝ) * κ ^ 2 := by simp
  have hcard_nat : frequencies.card ≤ Fintype.card F ^ 2 := by
    calc
      frequencies.card ≤ (Finset.univ : Finset (Space F 2)).card :=
        Finset.card_erase_le
      _ = Fintype.card F ^ 2 := by simp
  have hcard : (frequencies.card : ℝ) ≤ q ^ 2 := by
    have hcard' : (frequencies.card : ℝ) ≤ ((Fintype.card F ^ 2 : ℕ) : ℝ) := by
      exact_mod_cast hcard_nat
    simpa [q] using hcard'
  have hscaled_lt : q ^ 2 * energy < q ^ 2 * κ ^ 2 :=
    hsum_scaled.trans_le (mul_le_mul_of_nonneg_right hcard (sq_nonneg κ))
  have henergy_lt : energy < κ ^ 2 := by
    exact lt_of_mul_lt_mul_left hscaled_lt (sq_nonneg q)
  exact (not_le_of_gt henergy_lt) hkappa_energy

theorem exists_sharpness_threshold {κ : ℝ} (hκ : 0 < κ) (hκone : κ < 1) :
    ∃ Q : ℕ, ∀ (F' : Type*) [Field F'] [Fintype F'] [DecidableEq F'],
      Q ≤ Fintype.card F' →
        κ ^ 2 * ((Fintype.card F' : ℝ) + 3) ≤
          (Fintype.card F' : ℝ) - 3 := by
  have hkappa_sq : κ ^ 2 < 1 := by
    simpa using (sq_lt_sq₀ hκ.le (by norm_num : (0 : ℝ) ≤ 1)).2 hκone
  have hdelta : 0 < 1 - κ ^ 2 := sub_pos.mpr hkappa_sq
  obtain ⟨Q, hQ⟩ := exists_nat_ge (3 * (κ ^ 2 + 1) / (1 - κ ^ 2))
  refine ⟨Q, ?_⟩
  intro F' _ _ _ hcard
  let q : ℝ := Fintype.card F'
  have hQq : (Q : ℝ) ≤ q := by
    have hQq' : (Q : ℝ) ≤ (Fintype.card F' : ℝ) := by
      exact_mod_cast hcard
    simpa [q] using hQq'
  have hratio : 3 * (κ ^ 2 + 1) / (1 - κ ^ 2) ≤ q := hQ.trans hQq
  have hmul := mul_le_mul_of_nonneg_left hratio hdelta.le
  have hbase : 3 * (κ ^ 2 + 1) ≤ q * (1 - κ ^ 2) := by
    calc
      3 * (κ ^ 2 + 1) = (1 - κ ^ 2) *
          (3 * (κ ^ 2 + 1) / (1 - κ ^ 2)) := by field_simp
      _ ≤ (1 - κ ^ 2) * q := hmul
      _ = q * (1 - κ ^ 2) := by ring
  dsimp [q] at hbase ⊢
  nlinarith

/-- The pushforward of a finite measure to its first two coordinates. -/
def marginal {n : ℕ} (μ : Space F (2 + n) → ℝ) (u : Space F 2) : ℝ :=
  ∑ x : Space F (2 + n) with head₂ x = u, μ x

omit [Field F] in
theorem sum_marginal {n : ℕ} (μ : Space F (2 + n) → ℝ) :
    ∑ u : Space F 2, marginal μ u = ∑ x, μ x := by
  classical
  simpa [marginal] using
    (Finset.sum_fiberwise (Finset.univ : Finset (Space F (2 + n))) head₂ μ)

theorem marginal_support {n : ℕ} {μ : Space F (2 + n) → ℝ}
    (hμ : ∀ x, μ x ≠ 0 → x ∈ liftedPlanarSet (F := F) (n := n))
    {u : Space F 2} (hu : marginal μ u ≠ 0) : u ∈ planarSet (F := F) := by
  classical
  obtain ⟨x, hxmem, hx⟩ := Finset.exists_ne_zero_of_sum_ne_zero hu
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hxmem
  rw [← hxmem]
  exact hμ x hx

omit [Fintype F] [DecidableEq F] in
theorem dot_extend₂ {n : ℕ} (u : Space F 2) (x : Space F (2 + n)) :
    dot (extend₂ (n := n) u) x = dot u (head₂ x) := by
  unfold dot
  rw [Fin.sum_univ_add]
  simp [extend₂, head₂]

theorem fourier_extend₂_eq_marginal {n : ℕ} (χ : AddChar F ℂ)
    (μ : Space F (2 + n) → ℝ) (ξ : Space F 2) :
    fourier χ μ (extend₂ (n := n) ξ) = fourier χ (marginal μ) ξ := by
  classical
  unfold LeanEval.Combinatorics.FraserKakeyaProblem.fourier
  simp_rw [dot_extend₂]
  calc
    (∑ x : Space F (2 + n), χ (-(dot ξ (head₂ x))) * (μ x : ℂ)) =
        ∑ u : Space F 2, ∑ x : Space F (2 + n) with head₂ x = u,
          χ (-(dot ξ (head₂ x))) * (μ x : ℂ) := by
            rw [Finset.sum_fiberwise]
    _ = ∑ u : Space F 2, χ (-(dot ξ u)) *
          (∑ x : Space F (2 + n) with head₂ x = u, (μ x : ℂ)) := by
            apply Finset.sum_congr rfl
            intro u _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro x hx
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
            rw [hx]
    _ = ∑ u : Space F 2, χ (-(dot ξ u)) * (marginal μ u : ℂ) := by
            apply Finset.sum_congr rfl
            intro u _
            congr 1
            simp [marginal]

theorem sharpness_lifted {n : ℕ} {κ : ℝ} (hκ : 0 < κ)
    (hthreshold : κ ^ 2 * ((Fintype.card F : ℝ) + 3) ≤
      (Fintype.card F : ℝ) - 3) :
    ∀ μ : Space F (2 + n) → ℝ,
      IsProbabilityMeasureOn (liftedPlanarSet (F := F) (n := n)) μ →
        ∃ ξ : Space F (2 + n), ξ ≠ 0 ∧
          κ * (Fintype.card F : ℝ)⁻¹ ≤
            ‖fourier (AddChar.FiniteField.primitiveChar_to_Complex F) μ ξ‖ := by
  intro μ hμ
  rcases hμ with ⟨_, hμsum, hμsupport⟩
  let ν : Space F 2 → ℝ := marginal μ
  have hνsum : ∑ x, ν x = 1 := by
    simpa [ν] using (sum_marginal μ).trans hμsum
  have hνsupport : ∀ x, ν x ≠ 0 → x ∈ planarSet (F := F) := by
    intro x hx
    exact marginal_support hμsupport hx
  obtain ⟨ξ, hξ, hbound⟩ := exists_large_fourier_plane
    (AddChar.FiniteField.primitiveChar_to_Complex F)
    (AddChar.FiniteField.primitiveChar_to_Complex_isPrimitive F)
    hκ hthreshold hνsum hνsupport
  refine ⟨extend₂ (n := n) ξ, ?_, ?_⟩
  · intro hext
    apply hξ
    rw [← head₂_extend₂ (n := n) ξ, hext]
    rfl
  · rw [fourier_extend₂_eq_marginal]
    exact hbound

/-- The dot product with a fixed vector, as a linear functional. -/
def dotLinear {d : ℕ} (ξ : Space F d) : Space F d →ₗ[F] F where
  toFun := dot ξ
  map_add' x y := by
    simp [dot, mul_add, Finset.sum_add_distrib]
  map_smul' a x := by
    simp [dot, mul_left_comm, Finset.mul_sum]

omit [Fintype F] in
theorem dotLinear_surjective {d : ℕ} {ξ : Space F d} (hξ : ξ ≠ 0) :
    Function.Surjective (dotLinear ξ) := by
  classical
  have hcoord : ∃ i, ξ i ≠ 0 := by
    by_contra! h
    apply hξ
    funext i
    exact h i
  obtain ⟨i, hi⟩ := hcoord
  intro b
  refine ⟨fun j => if j = i then b / ξ i else 0, ?_⟩
  simp [dotLinear, dot]
  field_simp

theorem orthogonal_card_mul_card {d : ℕ} {ξ : Space F d} (hξ : ξ ≠ 0) :
    ((Finset.univ.filter fun x : Space F d => dot ξ x = 0).card) * Fintype.card F =
      Fintype.card (Space F d) := by
  classical
  let L := dotLinear ξ
  have hsurj : Function.Surjective L := dotLinear_surjective hξ
  have hrange : LinearMap.range L = ⊤ := LinearMap.range_eq_top.mpr hsurj
  have hrank := LinearMap.finrank_range_add_finrank_ker L
  rw [hrange] at hrank
  have hcard_space := Module.card_eq_pow_finrank (K := F) (V := Space F d)
  have hcard_ker := Module.card_eq_pow_finrank (K := F) (V := LinearMap.ker L)
  have hker_filter : Fintype.card (LinearMap.ker L) =
      (Finset.univ.filter fun x : Space F d => dot ξ x = 0).card := by
    rw [Fintype.card_subtype]
    congr 1
    ext x
    simp [L, dotLinear]
  calc
    ((Finset.univ.filter fun x : Space F d => dot ξ x = 0).card) * Fintype.card F =
        Fintype.card (LinearMap.ker L) * Fintype.card F := by rw [hker_filter]
    _ = Fintype.card F ^ Module.finrank F (LinearMap.ker L) * Fintype.card F := by
      rw [hcard_ker]
    _ = Fintype.card F ^ (Module.finrank F (LinearMap.ker L) + 1) := by
      rw [pow_add, pow_one]
    _ = Fintype.card F ^ Module.finrank F (Space F d) := by
      congr 1
      simpa [add_comm] using hrank
    _ = Fintype.card (Space F d) := hcard_space.symm

/-- A chosen affine-line base point for each direction in a Kakeya set. -/
def selectedBase {d : ℕ} {K : Set (Space F d)} (hK : IsKakeya K)
    (x : Space F d) : Space F d :=
  Classical.choose (hK x)

omit [Fintype F] [DecidableEq F] in
theorem selectedLine_subset {d : ℕ} {K : Set (Space F d)} (hK : IsKakeya K)
    (x : Space F d) : affineLine (selectedBase hK x) x ⊆ K :=
  Classical.choose_spec (hK x)

/-- Number of chosen line incidences at a point, represented in `ℝ`. -/
def incidenceCount {d : ℕ} {K : Set (Space F d)} (hK : IsKakeya K)
    (z : Space F d) : ℝ :=
  ∑ x : Space F d, ∑ a : F,
    if selectedBase hK x + a • x = z then 1 else 0

def incidenceNormalizer (d : ℕ) : ℝ :=
  (Fintype.card (Space F d) : ℝ) * (Fintype.card F : ℝ)

def incidenceMeasure {d : ℕ} {K : Set (Space F d)} (hK : IsKakeya K)
    (z : Space F d) : ℝ :=
  incidenceCount hK z / incidenceNormalizer (F := F) d

theorem sum_incidenceCount {d : ℕ} {K : Set (Space F d)} (hK : IsKakeya K) :
    ∑ z : Space F d, incidenceCount hK z = incidenceNormalizer (F := F) d := by
  classical
  unfold incidenceCount incidenceNormalizer
  calc
    (∑ z : Space F d, ∑ x : Space F d, ∑ a : F,
        if selectedBase hK x + a • x = z then 1 else 0) =
        ∑ x : Space F d, ∑ a : F, ∑ z : Space F d,
          if selectedBase hK x + a • x = z then 1 else 0 := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro x _
            rw [Finset.sum_comm]
    _ = ∑ _x : Space F d, ∑ _a : F, (1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro x _
          apply Finset.sum_congr rfl
          intro a _
          simp
    _ = (Fintype.card (Space F d) : ℝ) * (Fintype.card F : ℝ) := by simp

theorem incidenceMeasure_isProbability {d : ℕ} {K : Set (Space F d)}
    (hK : IsKakeya K) : IsProbabilityMeasureOn K (incidenceMeasure hK) := by
  classical
  have hnormalizer : incidenceNormalizer (F := F) d ≠ 0 := by
    unfold incidenceNormalizer
    positivity
  refine ⟨?_, ?_, ?_⟩
  · intro z
    unfold incidenceMeasure incidenceCount incidenceNormalizer
    positivity
  · unfold incidenceMeasure
    rw [← Finset.sum_div, sum_incidenceCount]
    exact div_self hnormalizer
  · intro z hz
    have hcount : incidenceCount hK z ≠ 0 := by
      intro hzero
      apply hz
      simp [incidenceMeasure, hzero]
    obtain ⟨x, _, hx⟩ := Finset.exists_ne_zero_of_sum_ne_zero hcount
    obtain ⟨a, _, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
    have hpoint : selectedBase hK x + a • x = z := by
      by_contra hne
      simp [hne] at ha
    exact selectedLine_subset hK x ⟨a, hpoint.symm⟩

theorem weighted_incidence_sum {d : ℕ} {K : Set (Space F d)} (hK : IsKakeya K)
    (g : Space F d → ℂ) :
    ∑ z : Space F d, g z * (incidenceCount hK z : ℂ) =
      ∑ x : Space F d, ∑ a : F, g (selectedBase hK x + a • x) := by
  classical
  have hcast (z : Space F d) : (incidenceCount hK z : ℂ) =
      ∑ x : Space F d, ∑ a : F,
        if selectedBase hK x + a • x = z then 1 else 0 := by
    unfold incidenceCount
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro x _
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro a _
    by_cases hpoint : selectedBase hK x + a • x = z <;> simp [hpoint]
  simp_rw [hcast, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp

omit [Fintype F] [DecidableEq F] in
theorem dot_add_smul_right {d : ℕ} (ξ y x : Space F d) (a : F) :
    dot ξ (y + a • x) = dot ξ y + a * dot ξ x := by
  unfold dot
  calc
    (∑ i, ξ i * (y + a • x) i) = ∑ i, (ξ i * y i + a * (ξ i * x i)) := by
      apply Finset.sum_congr rfl
      intro i _
      simp
      ring
    _ = (∑ i, ξ i * y i) + a * ∑ i, ξ i * x i := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]

theorem sum_char_affine {d : ℕ} (χ : AddChar F ℂ) (hχ : χ.IsPrimitive)
    (ξ y x : Space F d) :
    ∑ a : F, χ (-(dot ξ (y + a • x))) =
      if dot ξ x = 0 then (Fintype.card F : ℂ) * χ (-(dot ξ y)) else 0 := by
  classical
  simp_rw [dot_add_smul_right]
  have hneg (a : F) : -(dot ξ y + a * dot ξ x) =
      -(dot ξ y) + a * (-(dot ξ x)) := by ring
  simp_rw [hneg, AddChar.map_add_eq_mul]
  rw [← Finset.mul_sum, AddChar.sum_mulShift (-(dot ξ x)) hχ]
  by_cases hdot : dot ξ x = 0 <;> simp [hdot, mul_comm]

theorem fourier_incidence_eq {d : ℕ} {K : Set (Space F d)} (hK : IsKakeya K)
    (χ : AddChar F ℂ) (hχ : χ.IsPrimitive) (ξ : Space F d) :
    fourier χ (incidenceMeasure hK) ξ =
      ((incidenceNormalizer (F := F) d)⁻¹ : ℝ) *
        ∑ x : Space F d,
          if dot ξ x = 0 then
            (Fintype.card F : ℂ) * χ (-(dot ξ (selectedBase hK x))) else 0 := by
  classical
  unfold LeanEval.Combinatorics.FraserKakeyaProblem.fourier
  calc
    (∑ z : Space F d, χ (-(dot ξ z)) * (incidenceMeasure hK z : ℂ)) =
        (((incidenceNormalizer (F := F) d)⁻¹ : ℝ) : ℂ) *
          ∑ z : Space F d, χ (-(dot ξ z)) * (incidenceCount hK z : ℂ) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro z _
            unfold incidenceMeasure
            push_cast
            ring
    _ = (((incidenceNormalizer (F := F) d)⁻¹ : ℝ) : ℂ) *
          ∑ x : Space F d, ∑ a : F,
            χ (-(dot ξ (selectedBase hK x + a • x))) := by
              rw [weighted_incidence_sum]
    _ = (((incidenceNormalizer (F := F) d)⁻¹ : ℝ) : ℂ) *
          ∑ x : Space F d,
            if dot ξ x = 0 then
              (Fintype.card F : ℂ) * χ (-(dot ξ (selectedBase hK x))) else 0 := by
                congr 1
                apply Finset.sum_congr rfl
                intro x _
                exact sum_char_affine χ hχ ξ (selectedBase hK x) x

theorem incidence_fourier_bound {d : ℕ} {K : Set (Space F d)} (hK : IsKakeya K)
    (χ : AddChar F ℂ) (hχ : χ.IsPrimitive) {ξ : Space F d} (hξ : ξ ≠ 0) :
    ‖fourier χ (incidenceMeasure hK) ξ‖ ≤ (Fintype.card F : ℝ)⁻¹ := by
  classical
  let orthogonal : Finset (Space F d) :=
    Finset.univ.filter fun x => dot ξ x = 0
  let q : ℝ := Fintype.card F
  let ambient : ℝ := Fintype.card (Space F d)
  let normalizer : ℝ := incidenceNormalizer (F := F) d
  have hnormalizer : 0 < normalizer := by
    dsimp [normalizer, incidenceNormalizer, ambient, q]
    positivity
  have hnormalizer_inv : 0 ≤ normalizer⁻¹ := inv_nonneg.mpr hnormalizer.le
  have hscalar_norm : ‖((normalizer⁻¹ : ℝ) : ℂ)‖ = normalizer⁻¹ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnormalizer)]
  have hcard_nat : orthogonal.card * Fintype.card F = Fintype.card (Space F d) := by
    simpa [orthogonal] using orthogonal_card_mul_card (F := F) hξ
  have hcard_real : (orthogonal.card : ℝ) * q = ambient := by
    have hcast : ((orthogonal.card * Fintype.card F : ℕ) : ℝ) =
        (Fintype.card (Space F d) : ℝ) := by exact_mod_cast hcard_nat
    simpa [q, ambient] using hcast
  rw [fourier_incidence_eq hK χ hχ ξ]
  change ‖((normalizer⁻¹ : ℝ) : ℂ) *
    ∑ x : Space F d,
      if dot ξ x = 0 then
        (Fintype.card F : ℂ) * χ (-(dot ξ (selectedBase hK x))) else 0‖ ≤ q⁻¹
  rw [← Finset.sum_filter]
  change ‖((normalizer⁻¹ : ℝ) : ℂ) *
    ∑ x ∈ orthogonal,
      (Fintype.card F : ℂ) * χ (-(dot ξ (selectedBase hK x)))‖ ≤ q⁻¹
  calc
    _ = normalizer⁻¹ * ‖∑ x ∈ orthogonal,
        (Fintype.card F : ℂ) * χ (-(dot ξ (selectedBase hK x)))‖ := by
          rw [norm_mul, hscalar_norm]
    _ ≤ normalizer⁻¹ * ∑ x ∈ orthogonal,
        ‖(Fintype.card F : ℂ) * χ (-(dot ξ (selectedBase hK x)))‖ := by
          exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) hnormalizer_inv
    _ = normalizer⁻¹ * ((orthogonal.card : ℝ) * q) := by
          congr 1
          simp [q, AddChar.norm_apply]
    _ = q⁻¹ := by
          rw [hcard_real]
          dsimp [normalizer, incidenceNormalizer, ambient, q]
          field_simp

end

end Submission.Helpers
