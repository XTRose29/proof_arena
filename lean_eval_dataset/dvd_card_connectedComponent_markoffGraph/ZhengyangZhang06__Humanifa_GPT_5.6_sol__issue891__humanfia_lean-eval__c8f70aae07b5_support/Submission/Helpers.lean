import ChallengeDeps

open LeanEval.Combinatorics
open scoped BigOperators

namespace Submission.Helpers

variable {p : ℕ}

def vieta0Val (x : Fin 3 → ZMod p) : Fin 3 → ZMod p :=
  Function.update x 0 ((3 : ZMod p) * x 1 * x 2 - x 0)

def vieta1Val (x : Fin 3 → ZMod p) : Fin 3 → ZMod p :=
  Function.update x 1 ((3 : ZMod p) * x 0 * x 2 - x 1)

def vieta2Val (x : Fin 3 → ZMod p) : Fin 3 → ZMod p :=
  Function.update x 2 ((3 : ZMod p) * x 0 * x 1 - x 2)

@[simp] theorem vieta0Val_zero (x : Fin 3 → ZMod p) :
    vieta0Val x 0 = (3 : ZMod p) * x 1 * x 2 - x 0 := by
  simp [vieta0Val]

@[simp] theorem vieta0Val_one (x : Fin 3 → ZMod p) : vieta0Val x 1 = x 1 := by
  simp [vieta0Val]

@[simp] theorem vieta0Val_two (x : Fin 3 → ZMod p) : vieta0Val x 2 = x 2 := by
  simp [vieta0Val]

@[simp] theorem vieta1Val_zero (x : Fin 3 → ZMod p) : vieta1Val x 0 = x 0 := by
  simp [vieta1Val]

@[simp] theorem vieta1Val_one (x : Fin 3 → ZMod p) :
    vieta1Val x 1 = (3 : ZMod p) * x 0 * x 2 - x 1 := by
  simp [vieta1Val]

@[simp] theorem vieta1Val_two (x : Fin 3 → ZMod p) : vieta1Val x 2 = x 2 := by
  simp [vieta1Val]

@[simp] theorem vieta2Val_zero (x : Fin 3 → ZMod p) : vieta2Val x 0 = x 0 := by
  simp [vieta2Val]

@[simp] theorem vieta2Val_one (x : Fin 3 → ZMod p) : vieta2Val x 1 = x 1 := by
  simp [vieta2Val]

@[simp] theorem vieta2Val_two (x : Fin 3 → ZMod p) :
    vieta2Val x 2 = (3 : ZMod p) * x 0 * x 1 - x 2 := by
  simp [vieta2Val]

def vieta0 (x : MarkoffTriple p) : MarkoffTriple p where
  val := vieta0Val x.1
  property := by
    constructor
    · intro hzero
      have h0' : (3 : ZMod p) * x.1 1 * x.1 2 - x.1 0 = 0 := by
        simpa using congr_fun hzero 0
      have h1 : x.1 1 = 0 := by
        simpa using congr_fun hzero 1
      have h2 : x.1 2 = 0 := by
        simpa using congr_fun hzero 2
      have h0neg : -x.1 0 = 0 := by
        simpa [h1, h2] using h0'
      have h0 : x.1 0 = 0 := neg_eq_zero.mp h0neg
      exact x.2.1 <| by
        funext i
        fin_cases i <;> simp [h0, h1, h2]
    · simp [vieta0Val]
      linear_combination x.2.2

def vieta1 (x : MarkoffTriple p) : MarkoffTriple p where
  val := vieta1Val x.1
  property := by
    constructor
    · intro hzero
      have h0 : x.1 0 = 0 := by
        simpa using congr_fun hzero 0
      have h1' : (3 : ZMod p) * x.1 0 * x.1 2 - x.1 1 = 0 := by
        simpa using congr_fun hzero 1
      have h2 : x.1 2 = 0 := by
        simpa using congr_fun hzero 2
      have h1neg : -x.1 1 = 0 := by
        simpa [h0, h2] using h1'
      have h1 : x.1 1 = 0 := neg_eq_zero.mp h1neg
      exact x.2.1 <| by
        funext i
        fin_cases i <;> simp [h0, h1, h2]
    · simp [vieta1Val]
      linear_combination x.2.2

def vieta2 (x : MarkoffTriple p) : MarkoffTriple p where
  val := vieta2Val x.1
  property := by
    constructor
    · intro hzero
      have h0 : x.1 0 = 0 := by
        simpa using congr_fun hzero 0
      have h1 : x.1 1 = 0 := by
        simpa using congr_fun hzero 1
      have h2' : (3 : ZMod p) * x.1 0 * x.1 1 - x.1 2 = 0 := by
        simpa using congr_fun hzero 2
      have h2neg : -x.1 2 = 0 := by
        simpa [h0, h1] using h2'
      have h2 : x.1 2 = 0 := neg_eq_zero.mp h2neg
      exact x.2.1 <| by
        funext i
        fin_cases i <;> simp [h0, h1, h2]
    · simp [vieta2Val]
      linear_combination x.2.2

@[simp] theorem vieta0_apply_zero (x : MarkoffTriple p) :
    (vieta0 x).1 0 = (3 : ZMod p) * x.1 1 * x.1 2 - x.1 0 :=
  rfl

@[simp] theorem vieta0_apply_one (x : MarkoffTriple p) : (vieta0 x).1 1 = x.1 1 :=
  rfl

@[simp] theorem vieta0_apply_two (x : MarkoffTriple p) : (vieta0 x).1 2 = x.1 2 :=
  rfl

@[simp] theorem vieta1_apply_zero (x : MarkoffTriple p) : (vieta1 x).1 0 = x.1 0 :=
  rfl

@[simp] theorem vieta1_apply_one (x : MarkoffTriple p) :
    (vieta1 x).1 1 = (3 : ZMod p) * x.1 0 * x.1 2 - x.1 1 :=
  rfl

@[simp] theorem vieta1_apply_two (x : MarkoffTriple p) : (vieta1 x).1 2 = x.1 2 :=
  rfl

@[simp] theorem vieta2_apply_zero (x : MarkoffTriple p) : (vieta2 x).1 0 = x.1 0 :=
  rfl

@[simp] theorem vieta2_apply_one (x : MarkoffTriple p) : (vieta2 x).1 1 = x.1 1 :=
  rfl

@[simp] theorem vieta2_apply_two (x : MarkoffTriple p) :
    (vieta2 x).1 2 = (3 : ZMod p) * x.1 0 * x.1 1 - x.1 2 :=
  rfl

@[simp] theorem vieta0_involutive (x : MarkoffTriple p) : vieta0 (vieta0 x) = x := by
  apply Subtype.ext
  funext i
  fin_cases i <;> simp [vieta0, vieta0Val]

@[simp] theorem vieta1_involutive (x : MarkoffTriple p) : vieta1 (vieta1 x) = x := by
  apply Subtype.ext
  funext i
  fin_cases i <;> simp [vieta1, vieta1Val]

@[simp] theorem vieta2_involutive (x : MarkoffTriple p) : vieta2 (vieta2 x) = x := by
  apply Subtype.ext
  funext i
  fin_cases i <;> simp [vieta2, vieta2Val]

theorem adj_vieta0 {x : MarkoffTriple p} (h : x ≠ vieta0 x) :
    (markoffGraph p).Adj x (vieta0 x) := by
  refine ⟨h, Or.inl ?_⟩
  simp [vieta0, vieta0Val]

theorem adj_vieta1 {x : MarkoffTriple p} (h : x ≠ vieta1 x) :
    (markoffGraph p).Adj x (vieta1 x) := by
  refine ⟨h, Or.inr <| Or.inl ?_⟩
  simp [vieta1, vieta1Val]

theorem adj_vieta2 {x : MarkoffTriple p} (h : x ≠ vieta2 x) :
    (markoffGraph p).Adj x (vieta2 x) := by
  refine ⟨h, Or.inr <| Or.inr ?_⟩
  simp [vieta2, vieta2Val]

theorem vieta0_mem_component {c : (markoffGraph p).ConnectedComponent} {x : MarkoffTriple p}
    (hx : x ∈ c) : vieta0 x ∈ c := by
  by_cases h : x = vieta0 x
  · simpa [← h] using hx
  · exact c.mem_supp_of_adj_mem_supp hx (adj_vieta0 h)

theorem vieta1_mem_component {c : (markoffGraph p).ConnectedComponent} {x : MarkoffTriple p}
    (hx : x ∈ c) : vieta1 x ∈ c := by
  by_cases h : x = vieta1 x
  · simpa [← h] using hx
  · exact c.mem_supp_of_adj_mem_supp hx (adj_vieta1 h)

theorem vieta2_mem_component {c : (markoffGraph p).ConnectedComponent} {x : MarkoffTriple p}
    (hx : x ∈ c) : vieta2 x ∈ c := by
  by_cases h : x = vieta2 x
  · simpa [← h] using hx
  · exact c.mem_supp_of_adj_mem_supp hx (adj_vieta2 h)

def vieta0ComponentEquiv (c : (markoffGraph p).ConnectedComponent) : c ≃ c where
  toFun x := ⟨vieta0 x.1, vieta0_mem_component x.2⟩
  invFun x := ⟨vieta0 x.1, vieta0_mem_component x.2⟩
  left_inv x := Subtype.ext (vieta0_involutive x.1)
  right_inv x := Subtype.ext (vieta0_involutive x.1)

def vieta1ComponentEquiv (c : (markoffGraph p).ConnectedComponent) : c ≃ c where
  toFun x := ⟨vieta1 x.1, vieta1_mem_component x.2⟩
  invFun x := ⟨vieta1 x.1, vieta1_mem_component x.2⟩
  left_inv x := Subtype.ext (vieta1_involutive x.1)
  right_inv x := Subtype.ext (vieta1_involutive x.1)

def vieta2ComponentEquiv (c : (markoffGraph p).ConnectedComponent) : c ≃ c where
  toFun x := ⟨vieta2 x.1, vieta2_mem_component x.2⟩
  invFun x := ⟨vieta2 x.1, vieta2_mem_component x.2⟩
  left_inv x := Subtype.ext (vieta2_involutive x.1)
  right_inv x := Subtype.ext (vieta2_involutive x.1)

@[simp] theorem vieta0ComponentEquiv_val (c : (markoffGraph p).ConnectedComponent) (x : c) :
    (vieta0ComponentEquiv c x).1 = vieta0 x.1 :=
  rfl

@[simp] theorem vieta1ComponentEquiv_val (c : (markoffGraph p).ConnectedComponent) (x : c) :
    (vieta1ComponentEquiv c x).1 = vieta1 x.1 :=
  rfl

@[simp] theorem vieta2ComponentEquiv_val (c : (markoffGraph p).ConnectedComponent) (x : c) :
    (vieta2ComponentEquiv c x).1 = vieta2 x.1 :=
  rfl

theorem sum_vieta0ComponentEquiv (c : (markoffGraph p).ConnectedComponent) [Fintype c]
    {A : Type*} [AddCommMonoid A] (f : c → A) :
    ∑ x, f (vieta0ComponentEquiv c x) = ∑ x, f x :=
  (vieta0ComponentEquiv c).sum_comp f

theorem sum_vieta1ComponentEquiv (c : (markoffGraph p).ConnectedComponent) [Fintype c]
    {A : Type*} [AddCommMonoid A] (f : c → A) :
    ∑ x, f (vieta1ComponentEquiv c x) = ∑ x, f x :=
  (vieta1ComponentEquiv c).sum_comp f

theorem sum_vieta2ComponentEquiv (c : (markoffGraph p).ConnectedComponent) [Fintype c]
    {A : Type*} [AddCommMonoid A] (f : c → A) :
    ∑ x, f (vieta2ComponentEquiv c x) = ∑ x, f x :=
  (vieta2ComponentEquiv c).sum_comp f

theorem dvd_natCard_iff_cast_eq_zero (c : (markoffGraph p).ConnectedComponent) :
    p ∣ Nat.card c ↔ (Nat.card c : ZMod p) = 0 := by
  rw [CharP.cast_eq_zero_iff (ZMod p) p]

theorem zmod_natCast_ne_zero_of_pos_of_lt {n : ℕ} (hn : 0 < n) (hnp : n < p) :
    (n : ZMod p) ≠ 0 := by
  intro hzero
  have hpdvd : p ∣ n := (CharP.cast_eq_zero_iff (ZMod p) p n).mp hzero
  have hp_le_n : p ≤ n := Nat.le_of_dvd hn hpdvd
  omega

def ratio0 (x : MarkoffTriple p) : ZMod p :=
  x.1 0 * (x.1 1 * x.1 2)⁻¹

def ratio1 (x : MarkoffTriple p) : ZMod p :=
  x.1 1 * (x.1 0 * x.1 2)⁻¹

def ratio2 (x : MarkoffTriple p) : ZMod p :=
  x.1 2 * (x.1 0 * x.1 1)⁻¹

theorem markoff_coboundary_sum (hp : Nat.Prime p) (hgt : 3 < p) (x : MarkoffTriple p) :
    (ratio0 x - ratio0 (vieta0 x)) +
        (ratio1 x - ratio1 (vieta1 x)) +
        (ratio2 x - ratio2 (vieta2 x)) =
      (-3 : ZMod p) := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  have hthree : (3 : ZMod p) ≠ 0 :=
    zmod_natCast_ne_zero_of_pos_of_lt (p := p) (n := 3) (by omega) hgt
  let a : ZMod p := x.1 0
  let b : ZMod p := x.1 1
  let c : ZMod p := x.1 2
  have hmarkoff : a ^ 2 + b ^ 2 + c ^ 2 = (3 : ZMod p) * a * b * c := by
    simpa [a, b, c] using x.2.2
  have hnotzero : ¬(a = 0 ∧ b = 0 ∧ c = 0) := by
    rintro ⟨ha, hb, hc⟩
    apply x.2.1
    funext i
    fin_cases i <;> simp [a, b, c, ha, hb, hc]
  have hmain :
      (a * (b * c)⁻¹ - ((3 : ZMod p) * b * c - a) * (b * c)⁻¹) +
          (b * (a * c)⁻¹ - ((3 : ZMod p) * a * c - b) * (a * c)⁻¹) +
          (c * (a * b)⁻¹ - ((3 : ZMod p) * a * b - c) * (a * b)⁻¹) =
        (-3 : ZMod p) := by
    by_cases ha : a = 0
    · by_cases hb : b = 0
      · have hc : c = 0 := by
          have hc2 : c ^ 2 = 0 := by
            simpa [ha, hb] using hmarkoff
          exact sq_eq_zero_iff.mp hc2
        exact (hnotzero ⟨ha, hb, hc⟩).elim
      · have hc : c ≠ 0 := by
          intro hc
          have hb2 : b ^ 2 = 0 := by
            simpa [ha, hc] using hmarkoff
          exact hb (sq_eq_zero_iff.mp hb2)
        simp [ha]
        field_simp [hb, hc, hthree]
    · by_cases hb : b = 0
      · have hc : c ≠ 0 := by
          intro hc
          have ha2 : a ^ 2 = 0 := by
            simpa [hb, hc] using hmarkoff
          exact ha (sq_eq_zero_iff.mp ha2)
        simp [hb]
        field_simp [ha, hc, hthree]
      · by_cases hc : c = 0
        · simp [hc]
          field_simp [ha, hb, hthree]
        · field_simp [ha, hb, hc, hthree]
          linear_combination 2 * hmarkoff
  simpa [ratio0, ratio1, ratio2, a, b, c] using hmain

theorem sum_ratio0_coboundary (c : (markoffGraph p).ConnectedComponent) [Fintype c] :
    ∑ x : c, (ratio0 x.1 - ratio0 (vieta0 x.1)) = 0 := by
  classical
  rw [Finset.sum_sub_distrib]
  have hperm : ∑ x : c, ratio0 (vieta0 x.1) = ∑ x : c, ratio0 x.1 := by
    simpa using sum_vieta0ComponentEquiv c (fun x : c => ratio0 x.1)
  rw [hperm, sub_self]

theorem sum_ratio1_coboundary (c : (markoffGraph p).ConnectedComponent) [Fintype c] :
    ∑ x : c, (ratio1 x.1 - ratio1 (vieta1 x.1)) = 0 := by
  classical
  rw [Finset.sum_sub_distrib]
  have hperm : ∑ x : c, ratio1 (vieta1 x.1) = ∑ x : c, ratio1 x.1 := by
    simpa using sum_vieta1ComponentEquiv c (fun x : c => ratio1 x.1)
  rw [hperm, sub_self]

theorem sum_ratio2_coboundary (c : (markoffGraph p).ConnectedComponent) [Fintype c] :
    ∑ x : c, (ratio2 x.1 - ratio2 (vieta2 x.1)) = 0 := by
  classical
  rw [Finset.sum_sub_distrib]
  have hperm : ∑ x : c, ratio2 (vieta2 x.1) = ∑ x : c, ratio2 x.1 := by
    simpa using sum_vieta2ComponentEquiv c (fun x : c => ratio2 x.1)
  rw [hperm, sub_self]

theorem dvd_card_connectedComponent_markoffGraph_aux (hp : Nat.Prime p) (hgt : 3 < p) :
    ∀ c : (markoffGraph p).ConnectedComponent, p ∣ Nat.card c := by
  classical
  intro c
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fintype c := Fintype.ofFinite c
  have hthree : (3 : ZMod p) ≠ 0 :=
    zmod_natCast_ne_zero_of_pos_of_lt (p := p) (n := 3) (by omega) hgt
  have hsum :
      (∑ x : c,
          ((ratio0 x.1 - ratio0 (vieta0 x.1)) +
            (ratio1 x.1 - ratio1 (vieta1 x.1)) +
            (ratio2 x.1 - ratio2 (vieta2 x.1)))) = 0 := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    rw [sum_ratio0_coboundary c, sum_ratio1_coboundary c, sum_ratio2_coboundary c]
    simp
  have hconst :
      (∑ x : c,
          ((ratio0 x.1 - ratio0 (vieta0 x.1)) +
            (ratio1 x.1 - ratio1 (vieta1 x.1)) +
            (ratio2 x.1 - ratio2 (vieta2 x.1)))) =
        (Fintype.card c : ZMod p) * (-3 : ZMod p) := by
    rw [Finset.sum_congr rfl (fun x _ => markoff_coboundary_sum hp hgt x.1),
      Finset.sum_const, nsmul_eq_mul]
    rfl
  apply (dvd_natCard_iff_cast_eq_zero c).2
  have hmul : (Fintype.card c : ZMod p) * (-3 : ZMod p) = 0 := hconst ▸ hsum
  have hcard : (Fintype.card c : ZMod p) = 0 :=
    (mul_eq_zero.mp hmul).resolve_right (neg_ne_zero.mpr hthree)
  simpa [Nat.card_eq_fintype_card] using hcard

end Submission.Helpers
