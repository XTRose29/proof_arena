import Mathlib

namespace Submission.Helpers

open Matrix
open scoped ENNReal NNReal

variable {n : Type*} [Fintype n] [DecidableEq n]

noncomputable def resolventSum (B : Matrix n n ℝ) (q : ℝ) (d : n → ℝ) : ℕ → n → ℝ
  | 0 => 0
  | N + 1 => resolventSum B q d N + (q⁻¹ ^ (N + 1)) • ((B ^ N) *ᵥ d)

omit [DecidableEq n] in
lemma exists_pos_le_of_forall_pos [Nonempty n] {f : n → ℝ} (hf : ∀ i, 0 < f i) :
    ∃ c, 0 < c ∧ ∀ i, c ≤ f i := by
  obtain ⟨i, _, hi⟩ := Finset.univ.exists_min_image f Finset.univ_nonempty
  exact ⟨f i, hf i, fun j ↦ hi j (Finset.mem_univ j)⟩

omit [DecidableEq n] in
lemma mulVec_nonneg {A : Matrix n n ℝ} {x : n → ℝ}
    (hA : ∀ i j, 0 ≤ A i j) (hx : ∀ i, 0 ≤ x i) (i : n) :
    0 ≤ (A *ᵥ x) i := by
  exact Finset.sum_nonneg fun j _ ↦ mul_nonneg (hA i j) (hx j)

omit [DecidableEq n] in
lemma mulVec_mono {A : Matrix n n ℝ} {x y : n → ℝ}
    (hA : ∀ i j, 0 ≤ A i j) (hxy : ∀ i, x i ≤ y i) (i : n) :
    (A *ᵥ x) i ≤ (A *ᵥ y) i := by
  exact Finset.sum_le_sum fun j _ ↦ mul_le_mul_of_nonneg_left (hxy j) (hA i j)

lemma pow_mulVec_le_smul {A : Matrix n n ℝ} {x : n → ℝ} {r : ℝ}
    (hA : ∀ i j, 0 ≤ A i j) (hr : 0 ≤ r)
    (hAx : ∀ i, (A *ᵥ x) i ≤ r * x i) :
    ∀ k i, ((A ^ k) *ᵥ x) i ≤ r ^ k * x i := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      intro i
      rw [pow_succ', ← Matrix.mulVec_mulVec]
      calc
        (A *ᵥ (A ^ k *ᵥ x)) i ≤ (A *ᵥ (r ^ k • x)) i :=
          mulVec_mono hA (fun j ↦ ih j) i
        _ = r ^ k * (A *ᵥ x) i := by simp [Matrix.mulVec_smul]
        _ ≤ r ^ k * (r * x i) := mul_le_mul_of_nonneg_left (hAx i) (pow_nonneg hr k)
        _ = r ^ (k + 1) * x i := by ring

lemma pow_mulVec_nonneg {A : Matrix n n ℝ} {x : n → ℝ}
    (hA : ∀ i j, 0 ≤ A i j) (hx : ∀ i, 0 ≤ x i) (k : ℕ) (i : n) :
    0 ≤ ((A ^ k) *ᵥ x) i :=
  mulVec_nonneg (Matrix.pow_apply_nonneg hA k) hx i

lemma pow_mulVec_le_add_one_pow {A : Matrix n n ℝ} {x : n → ℝ}
    (hA : ∀ i j, 0 ≤ A i j) (hx : ∀ i, 0 ≤ x i) :
    ∀ k i, ((A ^ k) *ᵥ x) i ≤ (((A + 1) ^ k) *ᵥ x) i := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      intro i
      rw [pow_succ', pow_succ', ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      calc
        (A *ᵥ (A ^ k *ᵥ x)) i ≤ (A *ᵥ ((A + 1) ^ k *ᵥ x)) i :=
          mulVec_mono hA (fun j ↦ ih j) i
        _ ≤ ((A + 1) *ᵥ ((A + 1) ^ k *ᵥ x)) i := by
          rw [Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply]
          exact le_add_of_nonneg_right <|
            pow_mulVec_nonneg (fun a b ↦ add_nonneg (hA a b) (by
              by_cases hab : a = b <;> simp [Matrix.one_apply, hab])) hx k i

lemma add_one_pow_mulVec_mono {A : Matrix n n ℝ} {x : n → ℝ}
    (hA : ∀ i j, 0 ≤ A i j) (hx : ∀ i, 0 ≤ x i) :
    Monotone fun k ↦ ((A + 1) ^ k) *ᵥ x := by
  apply monotone_nat_of_le_succ
  intro k i
  rw [pow_succ', ← Matrix.mulVec_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply]
  exact le_add_of_nonneg_left <|
    mulVec_nonneg hA
      (fun j ↦ pow_mulVec_nonneg (fun a b ↦ add_nonneg (hA a b) (by
        by_cases hab : a = b <;> simp [Matrix.one_apply, hab])) hx k j) i

lemma resolventSum_nonneg {B : Matrix n n ℝ} {q : ℝ} {d : n → ℝ}
    (hB : ∀ i j, 0 ≤ B i j) (hq : 0 ≤ q) (hd : ∀ i, 0 ≤ d i) :
    ∀ N i, 0 ≤ resolventSum B q d N i := by
  intro N
  induction N with
  | zero => simp [resolventSum]
  | succ N ih =>
      intro i
      rw [resolventSum, Pi.add_apply, Pi.smul_apply]
      exact add_nonneg (ih i) <|
        mul_nonneg (pow_nonneg (inv_nonneg.mpr hq) (N + 1))
          (pow_mulVec_nonneg hB hd N i)

lemma resolventSum_identity {B : Matrix n n ℝ} {q : ℝ} {d : n → ℝ}
    (hq : q ≠ 0) : ∀ N i,
    q * resolventSum B q d N i - (B *ᵥ resolventSum B q d N) i =
      d i - q⁻¹ ^ N * ((B ^ N) *ᵥ d) i := by
  intro N
  induction N with
  | zero => simp [resolventSum]
  | succ N ih =>
      intro i
      have hqpow : q * q⁻¹ ^ (N + 1) = q⁻¹ ^ N := by
        rw [pow_succ]
        calc
          q * (q⁻¹ ^ N * q⁻¹) = q⁻¹ ^ N * (q * q⁻¹) := by ring
          _ = q⁻¹ ^ N := by simp [hq]
      rw [resolventSum, Matrix.mulVec_add, Matrix.mulVec_smul, Pi.add_apply, Pi.smul_apply]
      calc
        q * (resolventSum B q d N i + q⁻¹ ^ (N + 1) * ((B ^ N) *ᵥ d) i) -
              ((B *ᵥ resolventSum B q d N) i +
                q⁻¹ ^ (N + 1) * (B *ᵥ (B ^ N *ᵥ d)) i) =
            (q * resolventSum B q d N i - (B *ᵥ resolventSum B q d N) i) +
              (q * q⁻¹ ^ (N + 1)) * ((B ^ N) *ᵥ d) i -
                q⁻¹ ^ (N + 1) * (B *ᵥ (B ^ N *ᵥ d)) i := by ring
        _ = (d i - q⁻¹ ^ N * ((B ^ N) *ᵥ d) i) +
              q⁻¹ ^ N * ((B ^ N) *ᵥ d) i -
                q⁻¹ ^ (N + 1) * ((B ^ (N + 1)) *ᵥ d) i := by
            rw [ih i, hqpow, Matrix.mulVec_mulVec, ← pow_succ']
        _ = d i - q⁻¹ ^ (N + 1) * ((B ^ (N + 1)) *ᵥ d) i := by ring

omit [DecidableEq n] in
lemma mulVec_pos_of_entry {B : Matrix n n ℝ} {x : n → ℝ} {i j : n}
    (hB : ∀ a b, 0 ≤ B a b) (hx : ∀ a, 0 ≤ x a)
    (hij : 0 < B i j) (hxj : 0 < x j) :
    0 < (B *ᵥ x) i := by
  calc
    0 < B i j * x j := mul_pos hij hxj
    _ ≤ ∑ k, B i k * x k :=
      Finset.single_le_sum (fun k _ ↦ mul_nonneg (hB i k) (hx k)) (Finset.mem_univ j)

omit [DecidableEq n] in
lemma exists_minimal_subinvariant [Nonempty n] (A : Matrix n n ℝ)
    (hA : ∀ i j, 0 ≤ A i j) :
    ∃ r : ℝ, ∃ x : n → ℝ,
      0 ≤ r ∧ x ∈ stdSimplex ℝ n ∧
      (∀ i, (A *ᵥ x) i ≤ r * x i) ∧
      ∀ {s : ℝ} {y : n → ℝ},
        0 ≤ s → y ∈ stdSimplex ℝ n →
        (∀ i, (A *ᵥ y) i ≤ s * y i) → r ≤ s := by
  let M : ℝ := ∑ i, ∑ j, A i j
  let constraints : Set (ℝ × (n → ℝ)) :=
    {p | ∀ i, (A *ᵥ p.2) i ≤ p.1 * p.2 i}
  let K : Set (ℝ × (n → ℝ)) :=
    (Set.Icc 0 M ×ˢ stdSimplex ℝ n) ∩ constraints
  have hrow_nonneg (i : n) : 0 ≤ ∑ j, A i j :=
    Finset.sum_nonneg fun j _ ↦ hA i j
  have hM_nonneg : 0 ≤ M :=
    Finset.sum_nonneg fun i _ ↦ hrow_nonneg i
  have hconstraints : IsClosed constraints := by
    change IsClosed {p : ℝ × (n → ℝ) | ∀ i, (A *ᵥ p.2) i ≤ p.1 * p.2 i}
    rw [show {p : ℝ × (n → ℝ) | ∀ i, (A *ᵥ p.2) i ≤ p.1 * p.2 i} =
        ⋂ i, {p | (A *ᵥ p.2) i ≤ p.1 * p.2 i} by ext p; simp]
    exact isClosed_iInter fun i ↦ isClosed_le (by fun_prop) (by fun_prop)
  have hKcompact : IsCompact K := by
    exact (isCompact_Icc.prod (isCompact_stdSimplex ℝ n)).inter_right hconstraints
  have hKnonempty : K.Nonempty := by
    let b : stdSimplex ℝ n := stdSimplex.barycenter
    refine ⟨(M, b.1), ⟨⟨⟨hM_nonneg, le_rfl⟩, b.2⟩, ?_⟩⟩
    intro i
    have hrow_le : ∑ j, A i j ≤ M := by
      exact Finset.single_le_sum (fun k _ ↦ hrow_nonneg k) (Finset.mem_univ i)
    change ∑ j, A i j * (Fintype.card n : ℝ)⁻¹ ≤
      M * (Fintype.card n : ℝ)⁻¹
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right hrow_le (by positivity)
  obtain ⟨p, hpK, hpmin⟩ :=
    hKcompact.exists_isMinOn hKnonempty continuous_fst.continuousOn
  refine ⟨p.1, p.2, hpK.1.1.1, hpK.1.2, hpK.2, ?_⟩
  intro s y hs hy hsy
  by_cases hsM : s ≤ M
  · exact hpmin (show (s, y) ∈ K from ⟨⟨⟨hs, hsM⟩, hy⟩, hsy⟩)
  · exact hpK.1.1.2.trans (lt_of_not_ge hsM).le

lemma subinvariant_pos_of_irreducible [Nonempty n] {A : Matrix n n ℝ}
    (hA : A.IsIrreducible) {r : ℝ} {x : n → ℝ}
    (hr : 0 ≤ r) (hx : x ∈ stdSimplex ℝ n)
    (hAx : ∀ i, (A *ᵥ x) i ≤ r * x i) :
    ∀ i, 0 < x i := by
  have hxsum_pos : 0 < ∑ i, x i := by simp [hx.2]
  obtain ⟨j, _, hxj⟩ :=
    (Finset.sum_pos_iff_of_nonneg (fun i _ ↦ hx.1 i)).mp hxsum_pos
  have hpow := (Matrix.isIrreducible_iff_exists_pow_pos hA.nonneg).mp hA
  intro i
  obtain ⟨k, _, hik⟩ := hpow i j
  have hleft : 0 < ((A ^ k) *ᵥ x) i :=
    mulVec_pos_of_entry (Matrix.pow_apply_nonneg hA.nonneg k) hx.1 hik hxj
  have hright : 0 < r ^ k * x i :=
    hleft.trans_le (pow_mulVec_le_smul hA.nonneg hr hAx k i)
  exact pos_of_mul_pos_right hright (pow_nonneg hr k)

lemma subinvariant_eigenvalue_pos [Nonempty n] {A : Matrix n n ℝ}
    (hA : A.IsIrreducible) {r : ℝ} {x : n → ℝ}
    (hr : 0 ≤ r) (hx : x ∈ stdSimplex ℝ n)
    (hAx : ∀ i, (A *ᵥ x) i ≤ r * x i) :
    0 < r := by
  have hxpos := subinvariant_pos_of_irreducible hA hr hx hAx
  let i : n := Classical.choice inferInstance
  obtain ⟨k, hk, hik⟩ :=
    (Matrix.isIrreducible_iff_exists_pow_pos hA.nonneg).mp hA i i
  have hleft : 0 < ((A ^ k) *ᵥ x) i :=
    mulVec_pos_of_entry (Matrix.pow_apply_nonneg hA.nonneg k) hx.1 hik (hxpos i)
  have hright : 0 < r ^ k * x i :=
    hleft.trans_le (pow_mulVec_le_smul hA.nonneg hr hAx k i)
  have hrpow : 0 < r ^ k := pos_of_mul_pos_left hright (hxpos i).le
  have hr_ne : r ≠ 0 := by
    intro hr0
    simp [hr0, hk.ne'] at hrpow
  exact hr.lt_of_ne (Ne.symm hr_ne)

lemma exists_add_one_pow_mulVec_pos [Nonempty n] {A : Matrix n n ℝ}
    (hA : A.IsIrreducible) {d : n → ℝ}
    (hd : ∀ i, 0 ≤ d i) (hd0 : d ≠ 0) :
    ∃ N, ∀ i, 0 < (((A + 1) ^ N) *ᵥ d) i := by
  have hdpos : ∃ j, 0 < d j := by
    have hdne : ∃ j, d j ≠ 0 := by
      by_contra h
      push Not at h
      exact hd0 (funext h)
    obtain ⟨j, hj⟩ := hdne
    exact ⟨j, (hd j).lt_of_ne (Ne.symm hj)⟩
  obtain ⟨j, hdj⟩ := hdpos
  have hpow := (Matrix.isIrreducible_iff_exists_pow_pos hA.nonneg).mp hA
  let k : n → ℕ := fun i ↦ Classical.choose (hpow i j)
  have hk (i : n) : 0 < k i ∧ 0 < (A ^ k i) i j :=
    Classical.choose_spec (hpow i j)
  let N : ℕ := ∑ i, k i
  have hkN (i : n) : k i ≤ N := by
    exact Finset.single_le_sum (fun a _ ↦ Nat.zero_le (k a)) (Finset.mem_univ i)
  refine ⟨N, fun i ↦ ?_⟩
  have hAk : 0 < ((A ^ k i) *ᵥ d) i :=
    mulVec_pos_of_entry (Matrix.pow_apply_nonneg hA.nonneg (k i)) hd (hk i).2 hdj
  have hBk : 0 < (((A + 1) ^ k i) *ᵥ d) i :=
    hAk.trans_le (pow_mulVec_le_add_one_pow hA.nonneg hd (k i) i)
  exact hBk.trans_le ((add_one_pow_mulVec_mono hA.nonneg hd (hkN i)) i)

lemma exists_positive_eigenpair [Nonempty n] (A : Matrix n n ℝ)
    (hA : A.IsIrreducible) :
    ∃ r : ℝ, ∃ x : n → ℝ,
      0 < r ∧ (∀ i, 0 < x i) ∧ A *ᵥ x = r • x := by
  obtain ⟨r, x, hr, hx, hAx, hmin⟩ :=
    exists_minimal_subinvariant A hA.nonneg
  have hxpos := subinvariant_pos_of_irreducible hA hr hx hAx
  have hrpos := subinvariant_eigenvalue_pos hA hr hx hAx
  have heig : A *ᵥ x = r • x := by
    by_contra hne
    let d : n → ℝ := r • x - A *ᵥ x
    have hd (i : n) : 0 ≤ d i := by
      simp only [d, Pi.sub_apply, Pi.smul_apply]
      exact sub_nonneg.mpr (hAx i)
    have hd0 : d ≠ 0 := by
      intro hd0
      apply hne
      have hzero : r • x - A *ᵥ x = 0 := by simpa only [d] using hd0
      exact (sub_eq_zero.mp hzero).symm
    obtain ⟨N, hNd⟩ := exists_add_one_pow_mulVec_pos hA hd hd0
    let B : Matrix n n ℝ := A + 1
    let q : ℝ := r + 1
    let z : n → ℝ := resolventSum B q d N
    have hB (i j : n) : 0 ≤ B i j := by
      simp only [B, Matrix.add_apply]
      exact add_nonneg (hA.nonneg i j) (by
        by_cases hij : i = j <;> simp [Matrix.one_apply, hij])
    have hqpos : 0 < q := by dsimp [q]; linarith
    have hz (i : n) : 0 ≤ z i :=
      resolventSum_nonneg hB hqpos.le hd N i
    obtain ⟨c, hcpos, hc⟩ := exists_pos_le_of_forall_pos
      (f := fun i ↦ x i / (z i + 1)) fun i ↦ div_pos (hxpos i) (by linarith [hz i])
    let ε : ℝ := min 1 c / 2
    have hmpos : 0 < min 1 c := lt_min one_pos hcpos
    have hεpos : 0 < ε := by dsimp [ε]; positivity
    have hεlt_one : ε < 1 := by
      have hmle : min 1 c ≤ 1 := min_le_left 1 c
      dsimp [ε]
      linarith
    have hεle_c : ε ≤ c := by
      have hmle : min 1 c ≤ c := min_le_right 1 c
      dsimp [ε]
      linarith
    let y : n → ℝ := x - ε • z
    have hypos (i : n) : 0 < y i := by
      have hden : 0 < z i + 1 := by linarith [hz i]
      have hεratio : ε ≤ x i / (z i + 1) := hεle_c.trans (hc i)
      have hmul : ε * (z i + 1) ≤ x i := (le_div_iff₀ hden).mp hεratio
      have hlt : ε * z i < ε * (z i + 1) := by
        exact mul_lt_mul_of_pos_left (by linarith) hεpos
      change 0 < x i - ε * z i
      linarith
    have hslack (i : n) : 0 < r * y i - (A *ᵥ y) i := by
      have hid := resolventSum_identity (B := B) (q := q) (d := d)
        hqpos.ne' N i
      have hpowpos : 0 < q⁻¹ ^ N := pow_pos (inv_pos.mpr hqpos) N
      have hlast : 0 < q⁻¹ ^ N * (((A + 1) ^ N) *ᵥ d) i :=
        mul_pos hpowpos (hNd i)
      have hpos :
          0 < (1 - ε) * d i + ε *
            (q⁻¹ ^ N * (((A + 1) ^ N) *ᵥ d) i) :=
        add_pos_of_nonneg_of_pos
          (mul_nonneg (sub_nonneg.mpr hεlt_one.le) (hd i))
          (mul_pos hεpos hlast)
      have hrewrite :
          r * y i - (A *ᵥ y) i =
            (1 - ε) * d i + ε *
              (q⁻¹ ^ N * (((A + 1) ^ N) *ᵥ d) i) := by
        calc
          r * y i - (A *ᵥ y) i = q * y i - (B *ᵥ y) i := by
            simp only [q, B, Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply]
            ring
          _ = (q * x i - (B *ᵥ x) i) -
                ε * (q * z i - (B *ᵥ z) i) := by
            simp only [y, Matrix.mulVec_sub, Matrix.mulVec_smul, Pi.sub_apply, Pi.smul_apply]
            ring
          _ = d i - ε * (d i - q⁻¹ ^ N * ((B ^ N) *ᵥ d) i) := by
            rw [hid]
            simp only [q, B, d, Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply,
              Pi.sub_apply, Pi.smul_apply]
            ring
          _ = (1 - ε) * d i + ε *
                (q⁻¹ ^ N * (((A + 1) ^ N) *ᵥ d) i) := by
            simp only [B]
            ring
      rw [hrewrite]
      exact hpos
    have hAy_nonneg (i : n) : 0 ≤ (A *ᵥ y) i :=
      mulVec_nonneg hA.nonneg (fun j ↦ (hypos j).le) i
    obtain ⟨δ, hδpos, hδ⟩ := exists_pos_le_of_forall_pos
      (f := fun i ↦ (r * y i - (A *ᵥ y) i) / y i)
      fun i ↦ div_pos (hslack i) (hypos i)
    let i₀ : n := Classical.choice inferInstance
    have hδle_r : δ ≤ r := by
      calc
        δ ≤ (r * y i₀ - (A *ᵥ y) i₀) / y i₀ := hδ i₀
        _ ≤ r := (div_le_iff₀ (hypos i₀)).mpr (by
          nlinarith [hAy_nonneg i₀])
    let η : ℝ := δ / 2
    have hηpos : 0 < η := by dsimp [η]; positivity
    have hηleδ : η ≤ δ := by dsimp [η]; linarith
    have hηle_r : η ≤ r := hηleδ.trans hδle_r
    let t : ℝ := r - η
    have ht_nonneg : 0 ≤ t := sub_nonneg.mpr hηle_r
    have ht_lt : t < r := sub_lt_self r hηpos
    have hAy_t (i : n) : (A *ᵥ y) i ≤ t * y i := by
      have hδmul : δ * y i ≤ r * y i - (A *ᵥ y) i :=
        (le_div_iff₀ (hypos i)).mp (hδ i)
      have hηmul : η * y i ≤ δ * y i :=
        mul_le_mul_of_nonneg_right hηleδ (hypos i).le
      dsimp [t]
      linarith
    let S : ℝ := ∑ i, y i
    have hSpos : 0 < S := by
      let i : n := Classical.choice inferInstance
      exact (Finset.sum_pos_iff_of_nonneg (fun j _ ↦ (hypos j).le)).mpr
        ⟨i, Finset.mem_univ i, hypos i⟩
    let w : n → ℝ := S⁻¹ • y
    have hw : w ∈ stdSimplex ℝ n := by
      constructor
      · intro i
        simp only [w, Pi.smul_apply]
        exact (mul_pos (inv_pos.mpr hSpos) (hypos i)).le
      · simp only [w, Pi.smul_apply, smul_eq_mul]
        rw [← Finset.mul_sum]
        change S⁻¹ * S = 1
        exact inv_mul_cancel₀ hSpos.ne'
    have hAw_t (i : n) : (A *ᵥ w) i ≤ t * w i := by
      simp only [w, Matrix.mulVec_smul, Pi.smul_apply]
      calc
        S⁻¹ * (A *ᵥ y) i ≤ S⁻¹ * (t * y i) :=
          mul_le_mul_of_nonneg_left (hAy_t i) (inv_nonneg.mpr hSpos.le)
        _ = t * (S⁻¹ * y i) := by ring
    exact (not_le_of_gt ht_lt) (hmin ht_nonneg hw hAw_t)
  exact ⟨r, x, hrpos, hxpos, heig⟩

lemma abs_spectrum_le_of_positive_eigenvector [Nonempty n]
    {A : Matrix n n ℝ} (hA : ∀ i j, 0 ≤ A i j)
    {r : ℝ} {x : n → ℝ} (hx : ∀ i, 0 < x i)
    (hAx : A *ᵥ x = r • x) {μ : ℝ} (hμ : μ ∈ spectrum ℝ A) :
    |μ| ≤ r := by
  have hμlin : μ ∈ spectrum ℝ (Matrix.toLin' A) := by simpa using hμ
  obtain ⟨w, hw⟩ :=
    (Module.End.HasEigenvalue.of_mem_spectrum hμlin).exists_hasEigenvector
  have hw0 : w ≠ 0 := (Module.End.hasEigenvector_iff.mp hw).2
  have hAw : A *ᵥ w = μ • w := by
    simpa only [Matrix.toLin'_apply] using hw.apply_eq_smul
  obtain ⟨j, _, hj⟩ := Finset.univ.exists_max_image
    (fun i ↦ |w i| / x i) Finset.univ_nonempty
  let c : ℝ := |w j| / x j
  have hwne : ∃ i, w i ≠ 0 := by
    by_contra h
    push Not at h
    exact hw0 (funext h)
  obtain ⟨k, hwk⟩ := hwne
  have hcpos : 0 < c := by
    have hkpos : 0 < |w k| / x k := div_pos (abs_pos.mpr hwk) (hx k)
    exact hkpos.trans_le (hj k (Finset.mem_univ k))
  have hw_le (i : n) : |w i| ≤ c * x i := by
    exact (div_le_iff₀ (hx i)).mp (hj i (Finset.mem_univ i))
  have hcj : c * x j = |w j| := by
    dsimp [c]
    exact div_mul_cancel₀ _ (hx j).ne'
  have hcxj : 0 < c * x j := mul_pos hcpos (hx j)
  have habsAw : |(A *ᵥ w) j| ≤ (A *ᵥ fun i ↦ |w i|) j := by
    calc
      |(A *ᵥ w) j| ≤ ∑ i, |A j i * w i| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i, A j i * |w i| := by
        apply Finset.sum_congr rfl
        intro i _
        rw [abs_mul, abs_of_nonneg (hA j i)]
  have hbound : |μ| * (c * x j) ≤ r * (c * x j) := by
    calc
      |μ| * (c * x j) = |μ * w j| := by rw [abs_mul, ← hcj]
      _ = |(A *ᵥ w) j| := by rw [congrFun hAw j]; simp
      _ ≤ (A *ᵥ fun i ↦ |w i|) j := habsAw
      _ ≤ (A *ᵥ c • x) j := mulVec_mono hA hw_le j
      _ = c * (A *ᵥ x) j := by simp [Matrix.mulVec_smul]
      _ = c * (r * x j) := by rw [congrFun hAx j]; simp
      _ = r * (c * x j) := by ring
  exact le_of_mul_le_mul_right hbound hcxj

lemma spectralRadius_eq_of_positive_eigenvector [Nonempty n]
    {A : Matrix n n ℝ} (hA : ∀ i j, 0 ≤ A i j)
    {r : ℝ} {x : n → ℝ} (hr : 0 < r) (hx : ∀ i, 0 < x i)
    (hAx : A *ᵥ x = r • x) :
    (spectralRadius ℝ A).toReal = r := by
  have hx0 : x ≠ 0 := by
    intro hx0
    let i : n := Classical.choice inferInstance
    simpa [hx0] using hx i
  have hrvec : Module.End.HasEigenvector (Matrix.toLin' A) r x := by
    rw [Module.End.hasEigenvector_iff]
    exact ⟨Module.End.mem_eigenspace_iff.mpr (by
      simpa only [Matrix.toLin'_apply] using hAx), hx0⟩
  have hrspec : r ∈ spectrum ℝ A := by
    rw [← Matrix.spectrum_toLin']
    exact (Module.End.hasEigenvalue_of_hasEigenvector hrvec).mem_spectrum
  let rnn : ℝ≥0 := ⟨r, hr.le⟩
  have hspectral : spectralRadius ℝ A = (rnn : ℝ≥0∞) := by
    apply le_antisymm
    · rw [spectralRadius]
      refine iSup₂_le fun μ hμ ↦ ?_
      exact_mod_cast abs_spectrum_le_of_positive_eigenvector hA hx hAx hμ
    · rw [spectralRadius]
      have hrnn : rnn = ‖r‖₊ := by
        exact (Real.nnnorm_of_nonneg hr.le).symm
      rw [hrnn]
      exact le_iSup_of_le r (le_iSup_of_le hrspec le_rfl)
  rw [hspectral]
  change r = r
  rfl

end Submission.Helpers
