import ChallengeDeps

namespace Submission.Hyperbolic

open LeanEval.Geometry
open scoped RealInnerProductSpace

noncomputable section

abbrev HVec := EuclideanSpace ℝ (Fin 2)

/-- The future sheet of the unit hyperboloid in `ℝ × ℝ²`. -/
structure HPoint where
  time : ℝ
  space : HVec
  time_pos : 0 < time
  unit : time ^ 2 - ‖space‖ ^ 2 = 1

@[ext]
lemma HPoint.ext {p q : HPoint} (ht : p.time = q.time)
    (hs : p.space = q.space) : p = q := by
  cases p
  cases q
  simp_all

/-- The Lorentz product, with the time coordinate positive. -/
def lorentz (p q : HPoint) : ℝ :=
  p.time * q.time - ⟪p.space, q.space⟫

abbrev LVec := ℝ × HVec

def minkowski (x y : LVec) : ℝ :=
  x.1 * y.1 - ⟪x.2, y.2⟫

def lift (p : HPoint) : LVec :=
  (p.time, p.space)

@[simp]
lemma minkowski_lift (p q : HPoint) :
    minkowski (lift p) (lift q) = lorentz p q := rfl

lemma lift_injective : Function.Injective lift := by
  intro p q h
  exact HPoint.ext (congrArg Prod.fst h) (congrArg Prod.snd h)

@[simp]
lemma minkowski_add_left (x y z : LVec) :
    minkowski (x + y) z = minkowski x z + minkowski y z := by
  simp [minkowski, inner_add_left]
  ring

@[simp]
lemma minkowski_add_right (x y z : LVec) :
    minkowski x (y + z) = minkowski x y + minkowski x z := by
  simp [minkowski, inner_add_right]
  ring

@[simp]
lemma minkowski_sub_left (x y z : LVec) :
    minkowski (x - y) z = minkowski x z - minkowski y z := by
  simp [minkowski, inner_sub_left]
  ring

@[simp]
lemma minkowski_sub_right (x y z : LVec) :
    minkowski x (y - z) = minkowski x y - minkowski x z := by
  simp [minkowski, inner_sub_right]
  ring

@[simp]
lemma minkowski_smul_left (r : ℝ) (x y : LVec) :
    minkowski (r • x) y = r * minkowski x y := by
  simp [minkowski, real_inner_smul_left]
  ring

@[simp]
lemma minkowski_smul_right (r : ℝ) (x y : LVec) :
    minkowski x (r • y) = r * minkowski x y := by
  simp [minkowski, real_inner_smul_right]
  ring

lemma minkowski_comm (x y : LVec) :
    minkowski x y = minkowski y x := by
  simp [minkowski, real_inner_comm]
  ring

@[simp]
lemma lorentz_self (p : HPoint) : lorentz p p = 1 := by
  rw [lorentz, real_inner_self_eq_norm_sq]
  simpa [pow_two] using p.unit

lemma lorentz_comm (p q : HPoint) : lorentz p q = lorentz q p := by
  rw [lorentz, lorentz, real_inner_comm]
  ring

lemma time_sq (p : HPoint) : p.time ^ 2 = 1 + ‖p.space‖ ^ 2 := by
  nlinarith [p.unit]

lemma one_add_norm_mul_norm_le_time_mul (p q : HPoint) :
    1 + ‖p.space‖ * ‖q.space‖ ≤ p.time * q.time := by
  have hp0 : 0 ≤ p.time := p.time_pos.le
  have hq0 : 0 ≤ q.time := q.time_pos.le
  have hnormp : 0 ≤ ‖p.space‖ := norm_nonneg _
  have hnormq : 0 ≤ ‖q.space‖ := norm_nonneg _
  have hleft : 0 ≤ 1 + ‖p.space‖ * ‖q.space‖ := by positivity
  have hright : 0 ≤ p.time * q.time := mul_nonneg hp0 hq0
  have hsq :
      (1 + ‖p.space‖ * ‖q.space‖) ^ 2 ≤
        (p.time * q.time) ^ 2 := by
    rw [mul_pow, time_sq p, time_sq q]
    nlinarith [sq_nonneg (‖p.space‖ - ‖q.space‖)]
  nlinarith [sq_nonneg
    (p.time * q.time - (1 + ‖p.space‖ * ‖q.space‖))]

lemma lorentz_ge_one (p q : HPoint) : 1 ≤ lorentz p q := by
  have hinner :
      ⟪p.space, q.space⟫ ≤ ‖p.space‖ * ‖q.space‖ :=
    real_inner_le_norm _ _
  have htime := one_add_norm_mul_norm_le_time_mul p q
  dsimp [lorentz]
  linarith

lemma lorentz_eq_one_iff (p q : HPoint) : lorentz p q = 1 ↔ p = q := by
  constructor
  · intro hpq
    let P : ℝ := ‖p.space‖
    let Q : ℝ := ‖q.space‖
    have hP0 : 0 ≤ P := norm_nonneg _
    have hQ0 : 0 ≤ Q := norm_nonneg _
    have hinner : ⟪p.space, q.space⟫ = p.time * q.time - 1 := by
      dsimp [lorentz] at hpq
      linarith
    have hupper : p.time * q.time ≤ 1 + P * Q := by
      change p.time * q.time ≤
        1 + ‖p.space‖ * ‖q.space‖
      have hcauchy := real_inner_le_norm p.space q.space
      linarith
    have hlower : 1 + P * Q ≤ p.time * q.time := by
      exact one_add_norm_mul_norm_le_time_mul p q
    have hprod : p.time * q.time = 1 + P * Q :=
      le_antisymm hupper hlower
    have hp_sq : p.time ^ 2 = 1 + P ^ 2 := by
      simpa [P] using time_sq p
    have hq_sq : q.time ^ 2 = 1 + Q ^ 2 := by
      simpa [Q] using time_sq q
    have hPQ : P = Q := by
      have hsq :
          (p.time * q.time) ^ 2 = (1 + P * Q) ^ 2 :=
        congrArg (fun z : ℝ => z ^ 2) hprod
      rw [mul_pow, hp_sq, hq_sq] at hsq
      nlinarith [sq_nonneg (P - Q)]
    have ht : p.time = q.time := by
      have hp0 := p.time_pos
      have hq0 := q.time_pos
      rw [hPQ] at hp_sq
      nlinarith [sq_nonneg (p.time + q.time)]
    have hv : p.space = q.space := by
      have hip : ⟪p.space, q.space⟫ = P ^ 2 := by
        rw [hinner, hprod, hPQ]
        ring
      have hnorm :
          ‖p.space - q.space‖ ^ 2 = 0 := by
        rw [← real_inner_self_eq_norm_sq, inner_sub_left,
          inner_sub_right, inner_sub_right, real_inner_comm q.space p.space,
          real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
        have hcomm :
            ⟪q.space, p.space⟫ = ⟪p.space, q.space⟫ :=
          (real_inner_comm q.space p.space).symm
        rw [hcomm, hip]
        change P ^ 2 - P ^ 2 - (P ^ 2 - Q ^ 2) = 0
        rw [hPQ]
        ring
      have : ‖p.space - q.space‖ = 0 := sq_eq_zero_iff.mp hnorm
      exact sub_eq_zero.mp (norm_eq_zero.mp this)
    exact HPoint.ext ht hv
  · rintro rfl
    exact lorentz_self p

lemma lorentz_gt_one {p q : HPoint} (h : p ≠ q) : 1 < lorentz p q :=
  lt_of_le_of_ne (lorentz_ge_one p q)
    (Ne.symm (mt (lorentz_eq_one_iff p q).mp h))

lemma tangent_time_abs_lt (b : HPoint) (u : LVec)
    (horth : minkowski (lift b) u = 0)
    (hunit : minkowski u u = -1) :
    |u.1| < b.time := by
  have hb_sq := time_sq b
  have hu_sq : ‖u.2‖ ^ 2 = u.1 ^ 2 + 1 := by
    rw [minkowski, real_inner_self_eq_norm_sq] at hunit
    nlinarith
  have hinner : ⟪b.space, u.2⟫ = b.time * u.1 := by
    change b.time * u.1 - ⟪b.space, u.2⟫ = 0 at horth
    linarith
  have habs :
      |b.time * u.1| ≤ ‖b.space‖ * ‖u.2‖ := by
    rw [← hinner]
    exact abs_real_inner_le_norm _ _
  have hsquares :
      (b.time * u.1) ^ 2 ≤
        (‖b.space‖ * ‖u.2‖) ^ 2 := by
    rw [← sq_abs (b.time * u.1)]
    exact (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 habs
  have hlt : u.1 ^ 2 < b.time ^ 2 := by
    rw [mul_pow, mul_pow, hb_sq, hu_sq] at hsquares
    nlinarith [sq_nonneg ‖b.space‖]
  have habs_sq : |u.1| ^ 2 < b.time ^ 2 := by
    simpa using hlt
  exact (sq_lt_sq₀ (abs_nonneg _) b.time_pos.le).mp habs_sq

/-- Central projection from the hyperboloid to the Klein disk. -/
def klein (p : HPoint) : HVec :=
  p.time⁻¹ • p.space

lemma space_eq_time_smul_klein (p : HPoint) :
    p.space = p.time • klein p := by
  simp [klein, smul_smul, p.time_pos.ne']

lemma norm_klein_sq (p : HPoint) :
    ‖klein p‖ ^ 2 = 1 - (p.time ^ 2)⁻¹ := by
  rw [klein, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos p.time_pos,
    mul_pow]
  rw [show ‖p.space‖ ^ 2 = p.time ^ 2 - 1 by nlinarith [p.unit]]
  field_simp [p.time_pos.ne']

lemma norm_klein_lt_one (p : HPoint) : ‖klein p‖ < 1 := by
  have hi : 0 < (p.time ^ 2)⁻¹ :=
    inv_pos.mpr (sq_pos_of_pos p.time_pos)
  have hk0 : 0 ≤ ‖klein p‖ := norm_nonneg _
  have hk_sq := norm_klein_sq p
  nlinarith [sq_nonneg (‖klein p‖ - 1)]

lemma klein_injective : Function.Injective klein := by
  intro p q hk
  have hsp : p.space = p.time • klein p :=
    space_eq_time_smul_klein p
  have hsq : q.space = q.time • klein q :=
    space_eq_time_smul_klein q
  have hpunit :
      p.time ^ 2 * (1 - ‖klein p‖ ^ 2) = 1 := by
    rw [norm_klein_sq]
    field_simp [p.time_pos.ne']
    ring
  have hqunit :
      q.time ^ 2 * (1 - ‖klein q‖ ^ 2) = 1 := by
    rw [norm_klein_sq]
    field_simp [q.time_pos.ne']
    ring
  have ht : p.time = q.time := by
    rw [hk] at hpunit
    have hp0 := p.time_pos
    have hq0 := q.time_pos
    have hcoef : 0 < 1 - ‖klein q‖ ^ 2 := by
      have := norm_klein_lt_one q
      nlinarith [norm_nonneg (klein q)]
    nlinarith [sq_nonneg (p.time + q.time)]
  apply HPoint.ext ht
  rw [hsp, hsq, ht, hk]

/-- The open Klein disk. -/
abbrev KDisk := {z : HVec // ‖z‖ < 1}

/-- Inverse central projection from the Klein disk to the hyperboloid. -/
def ofKlein (z : KDisk) : HPoint := by
  let r : ℝ := √(1 - ‖(z : HVec)‖ ^ 2)
  have hrarg : 0 < 1 - ‖(z : HVec)‖ ^ 2 := by
    have hz0 : 0 ≤ ‖(z : HVec)‖ := norm_nonneg _
    nlinarith [z.property, sq_nonneg (‖(z : HVec)‖ - 1)]
  have hr : 0 < r := Real.sqrt_pos.2 hrarg
  refine
    { time := r⁻¹
      space := r⁻¹ • (z : HVec)
      time_pos := inv_pos.mpr hr
      unit := ?_ }
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr, inv_pow]
  have hr_sq : r ^ 2 = 1 - ‖(z : HVec)‖ ^ 2 := by
    exact Real.sq_sqrt hrarg.le
  field_simp [hr.ne']
  nlinarith

@[simp]
lemma klein_ofKlein (z : KDisk) : klein (ofKlein z) = z := by
  have hr : √(1 - ‖(z : HVec)‖ ^ 2) ≠ 0 := by
    apply (Real.sqrt_pos.2 ?_).ne'
    have hz0 : 0 ≤ ‖(z : HVec)‖ := norm_nonneg _
    nlinarith [z.property, sq_nonneg (‖(z : HVec)‖ - 1)]
  dsimp [klein, ofKlein]
  rw [inv_inv, smul_smul, mul_inv_cancel₀ hr, one_smul]

def hyperbolicBetweenness (a b c : HPoint) : Prop :=
  Wbtw ℝ (klein a) (klein b) (klein c)

def hyperbolicCongruence (a b c d : HPoint) : Prop :=
  lorentz a b = lorentz c d

lemma wbtw_klein_of_lift_eq {a b c : HPoint} {α β : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (h : lift b = α • lift a + β • lift c) :
    Wbtw ℝ (klein a) (klein b) (klein c) := by
  have ht := congrArg Prod.fst h
  have hs := congrArg Prod.snd h
  change b.time = α * a.time + β * c.time at ht
  change b.space = α • a.space + β • c.space at hs
  let r : ℝ := β * c.time / b.time
  have hr0 : 0 ≤ r := div_nonneg (mul_nonneg hβ c.time_pos.le) b.time_pos.le
  have hr1 : r ≤ 1 := by
    rw [div_le_one b.time_pos]
    nlinarith [mul_nonneg hα a.time_pos.le]
  refine ⟨r, ⟨hr0, hr1⟩, ?_⟩
  ext i
  have hsi := congrArg (fun z : HVec => z i) hs
  change b.space i = α * a.space i + β * c.space i at hsi
  simp [AffineMap.lineMap_apply, klein, r]
  field_simp [a.time_pos.ne', b.time_pos.ne', c.time_pos.ne']
  linear_combination (a.space i) * ht - a.time * hsi

lemma hyperbolicCongruence_refl (a b : HPoint) :
    hyperbolicCongruence a b b a :=
  lorentz_comm a b

lemma hyperbolicCongruence_trans (a b c d e f : HPoint)
    (hcd : hyperbolicCongruence a b c d)
    (hef : hyperbolicCongruence a b e f) :
    hyperbolicCongruence c d e f :=
  hcd.symm.trans hef

lemma hyperbolicCongruence_id (a b c : HPoint)
    (h : hyperbolicCongruence a b c c) : a = b := by
  rw [hyperbolicCongruence, lorentz_self] at h
  exact (lorentz_eq_one_iff a b).mp h

lemma hyperbolicExtend (z b c d : HPoint) (hzb : z ≠ b) :
    ∃ x, hyperbolicBetweenness z b x ∧
      hyperbolicCongruence b x c d := by
  let h : ℝ := lorentz z b
  have hh : 1 < h := lorentz_gt_one hzb
  let s : ℝ := √(h ^ 2 - 1)
  have hsarg : 0 < h ^ 2 - 1 := by nlinarith
  have hs : 0 < s := Real.sqrt_pos.2 hsarg
  have hs_sq : s ^ 2 = h ^ 2 - 1 := Real.sq_sqrt hsarg.le
  let u : LVec := s⁻¹ • (h • lift b - lift z)
  have horth : minkowski (lift b) u = 0 := by
    rw [show u = s⁻¹ • (h • lift b - lift z) by rfl,
      minkowski_smul_right, minkowski_sub_right,
      minkowski_smul_right, minkowski_lift, minkowski_lift,
      lorentz_self, lorentz_comm b z]
    simp [h]
  have hnum :
      minkowski (h • lift b - lift z) (h • lift b - lift z) =
        1 - h ^ 2 := by
    simp [minkowski_comm, h]
    ring
  have hunit : minkowski u u = -1 := by
    rw [show u = s⁻¹ • (h • lift b - lift z) by rfl,
      minkowski_smul_left, minkowski_smul_right, hnum]
    field_simp [hs.ne']
    nlinarith
  let k : ℝ := lorentz c d
  have hk : 1 ≤ k := lorentz_ge_one c d
  have hkpos : 0 < k := lt_of_lt_of_le zero_lt_one hk
  let R : ℝ := √(k ^ 2 - 1)
  have hRarg : 0 ≤ k ^ 2 - 1 := by nlinarith
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have hR_sq : R ^ 2 = k ^ 2 - 1 := Real.sq_sqrt hRarg
  have hRlt : R < k := by
    apply (sq_lt_sq₀ hR hkpos.le).mp
    rw [hR_sq]
    nlinarith
  let xv : LVec := k • lift b + R • u
  have horth' : minkowski u (lift b) = 0 := by
    rw [minkowski_comm]
    exact horth
  have hxself : minkowski xv xv = 1 := by
    simp [xv, horth, horth', hunit]
    nlinarith [hR_sq]
  have hxtime : 0 < xv.1 := by
    have hu := tangent_time_abs_lt b u horth hunit
    by_cases hRz : R = 0
    · change 0 < k * b.time + R * u.1
      rw [hRz]
      simpa using mul_pos hkpos b.time_pos
    · have hRpos : 0 < R := lt_of_le_of_ne hR (Ne.symm hRz)
      have hmul : R * |u.1| < k * b.time := by
        calc
          R * |u.1| < R * b.time :=
            mul_lt_mul_of_pos_left hu hRpos
          _ < k * b.time :=
            mul_lt_mul_of_pos_right hRlt b.time_pos
      have hlower : -R * |u.1| ≤ R * u.1 := by
        have := mul_le_mul_of_nonneg_left (neg_abs_le u.1) hR
        nlinarith
      change 0 < k * b.time + R * u.1
      linarith
  let x : HPoint :=
    { time := xv.1
      space := xv.2
      time_pos := hxtime
      unit := by
        rw [← real_inner_self_eq_norm_sq]
        simpa [minkowski, pow_two] using hxself }
  have hxlift : lift x = xv := rfl
  have hcongr : hyperbolicCongruence b x c d := by
    change lorentz b x = lorentz c d
    rw [← minkowski_lift, hxlift]
    simp [xv, horth, k]
  let B : ℝ := R / s
  have hB : 0 ≤ B := div_nonneg hR hs.le
  let A : ℝ := k + B * h
  have hA : 0 < A := by
    dsimp [A]
    positivity
  have hxformula : lift x = A • lift b - B • lift z := by
    rw [hxlift]
    simp only [xv, u, B, A, div_eq_mul_inv, smul_sub,
      smul_smul]
    module
  have hbformula :
      lift b = (B / A) • lift z + (1 / A) • lift x := by
    rw [hxformula]
    simp only [smul_sub, smul_smul]
    field_simp [hA.ne']
    module
  refine ⟨x, ?_, hcongr⟩
  exact wbtw_klein_of_lift_eq
    (div_nonneg hB hA.le) (div_nonneg zero_le_one hA.le) hbformula

lemma hyperbolicSegmentConstruction (a b c d : HPoint) :
    ∃ x, hyperbolicBetweenness a b x ∧
      hyperbolicCongruence b x c d := by
  classical
  by_cases hab : a = b
  · subst a
    let o : KDisk := ⟨0, by norm_num⟩
    let e : KDisk :=
      ⟨(2 : ℝ)⁻¹ • EuclideanSpace.single 0 1, by
        norm_num [norm_smul]⟩
    let z : HPoint := if b = ofKlein o then ofKlein e else ofKlein o
    have hzb : z ≠ b := by
      dsimp [z]
      split_ifs with hb
      · intro h
        have hk : (e : HVec) = (o : HVec) := by
          simpa [hb] using congrArg klein h
        norm_num [e, o] at hk
      · exact fun h => hb h.symm
    rcases hyperbolicExtend z b c d hzb with ⟨x, _, hcx⟩
    exact ⟨x, wbtw_self_left ℝ (klein b) (klein x), hcx⟩
  · exact hyperbolicExtend a b c d hab

lemma forward_coefficients {a b c : HPoint} (hab : a ≠ b)
    (hbet : hyperbolicBetweenness a b c) :
    ∃ P Q : ℝ, Q ≤ 0 ∧ lift c = P • lift b + Q • lift a := by
  rcases hbet with ⟨r, ⟨hr0, hr1⟩, hr⟩
  have hrpos : 0 < r := by
    apply lt_of_le_of_ne hr0
    intro hrz
    have hrzero : r = 0 := hrz.symm
    have hka : klein a = klein b := by
      rw [← hr]
      simp [hrzero, AffineMap.lineMap_apply]
    exact hab (klein_injective hka)
  let P : ℝ := c.time / (r * b.time)
  let Q : ℝ := -(c.time * (1 - r)) / (r * a.time)
  have hQ : Q ≤ 0 := by
    dsimp [Q]
    exact div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr <| mul_nonneg c.time_pos.le (sub_nonneg.mpr hr1))
      (mul_nonneg hrpos.le a.time_pos.le)
  refine ⟨P, Q, hQ, ?_⟩
  apply Prod.ext
  · change c.time = P * b.time + Q * a.time
    dsimp [P, Q]
    field_simp [hrpos.ne', a.time_pos.ne', b.time_pos.ne']
    ring
  · ext i
    have hri := congrArg (fun z : HVec => z i) hr
    simp [AffineMap.lineMap_apply, klein] at hri
    field_simp [a.time_pos.ne', b.time_pos.ne', c.time_pos.ne'] at hri
    change c.space i = P * b.space i + Q * a.space i
    dsimp [P, Q]
    field_simp [hrpos.ne', a.time_pos.ne', b.time_pos.ne']
    linear_combination hri

lemma hyperbolicFiveSegment (a b c d a' b' c' d' : HPoint)
    (hab : a ≠ b)
    (habc : hyperbolicBetweenness a b c)
    (ha'b'c' : hyperbolicBetweenness a' b' c')
    (hAB : hyperbolicCongruence a b a' b')
    (hBC : hyperbolicCongruence b c b' c')
    (hAD : hyperbolicCongruence a d a' d')
    (hBD : hyperbolicCongruence b d b' d') :
    hyperbolicCongruence c d c' d' := by
  have ha'b' : a' ≠ b' := by
    intro heq
    subst b'
    rw [hyperbolicCongruence, lorentz_self] at hAB
    exact hab ((lorentz_eq_one_iff a b).mp hAB)
  rcases forward_coefficients hab habc with ⟨P, Q, hQ, hc⟩
  rcases forward_coefficients ha'b' ha'b'c' with
    ⟨P', Q', hQ', hc'⟩
  change lorentz a b = lorentz a' b' at hAB
  change lorentz b c = lorentz b' c' at hBC
  change lorentz a d = lorentz a' d' at hAD
  change lorentz b d = lorentz b' d' at hBD
  let h : ℝ := lorentz a b
  let j : ℝ := lorentz b c
  have hh : 1 < h := lorentz_gt_one hab
  have hj : j = P + Q * h := by
    change lorentz b c = P + Q * lorentz a b
    rw [← minkowski_lift, hc]
    simp [lorentz_comm]
  have hj' : j = P' + Q' * h := by
    change lorentz b c = P' + Q' * lorentz a b
    rw [hBC, ← minkowski_lift, hc']
    simp [← hAB, lorentz_comm]
  have hunit :
      1 = P ^ 2 + 2 * P * Q * h + Q ^ 2 := by
    rw [← lorentz_self c, ← minkowski_lift, hc]
    simp [h, lorentz_comm]
    ring
  have hunit' :
      1 = P' ^ 2 + 2 * P' * Q' * h + Q' ^ 2 := by
    rw [← lorentz_self c', ← minkowski_lift, hc']
    simp [h, ← hAB, lorentz_comm]
    ring
  have hrel : (h ^ 2 - 1) * Q ^ 2 = j ^ 2 - 1 := by
    linear_combination hunit - (j + P + Q * h) * hj
  have hrel' : (h ^ 2 - 1) * Q' ^ 2 = j ^ 2 - 1 := by
    linear_combination hunit' - (j + P' + Q' * h) * hj'
  have hQsq : Q ^ 2 = Q' ^ 2 := by
    apply (mul_left_cancel₀ (by nlinarith : h ^ 2 - 1 ≠ 0))
    nlinarith
  have hQQ : Q = Q' := by
    nlinarith [sq_nonneg (Q - Q'), sq_nonneg (Q + Q')]
  have hPP : P = P' := by
    nlinarith
  change lorentz c d = lorentz c' d'
  rw [← minkowski_lift, ← minkowski_lift, hc, hc']
  simp [hPP, hQQ, hAD, hBD]

lemma hyperbolicBetweenness_id (a b : HPoint)
    (h : hyperbolicBetweenness a b a) : a = b := by
  apply klein_injective
  exact ((wbtw_self_iff ℝ).mp h).symm

lemma hyperbolicInnerPasch (a b c p q : HPoint)
    (hapc : hyperbolicBetweenness a p c)
    (hbqc : hyperbolicBetweenness b q c) :
    ∃ x, hyperbolicBetweenness p x b ∧
      hyperbolicBetweenness q x a := by
  rcases hapc with ⟨u, ⟨hu0, hu1⟩, hp⟩
  rcases hbqc with ⟨v, ⟨hv0, hv1⟩, hq⟩
  let D : ℝ := u + v - u * v
  have hD₁ : D = u * (1 - v) + v := by simp [D]; ring
  have hD₂ : D = v * (1 - u) + u := by simp [D]; ring
  have hD0 : 0 ≤ D := by
    rw [hD₁]
    positivity
  by_cases hDz : D = 0
  · have hv : v = 0 := by
      rw [hD₁] at hDz
      nlinarith [mul_nonneg hu0 (sub_nonneg.mpr hv1)]
    have hu : u = 0 := by
      rw [hD₂, hv] at hDz
      simpa using hDz
    subst u
    subst v
    have hpa : klein p = klein a := by simpa using hp.symm
    have hqb : klein q = klein b := by simpa using hq.symm
    refine ⟨a, ?_, ?_⟩
    · rw [hyperbolicBetweenness, hpa]
      exact wbtw_self_left ℝ (klein a) (klein b)
    · rw [hyperbolicBetweenness, hqb]
      exact wbtw_self_right ℝ (klein b) (klein a)
  · have hDp : 0 < D := lt_of_le_of_ne hD0 (Ne.symm hDz)
    let r : ℝ := u * (1 - v) / D
    let s : ℝ := v * (1 - u) / D
    have hr0 : 0 ≤ r := by
      exact div_nonneg (mul_nonneg hu0 (sub_nonneg.mpr hv1)) hDp.le
    have hr1 : r ≤ 1 := by
      rw [div_le_one hDp]
      rw [hD₁]
      linarith
    have hs0 : 0 ≤ s := by
      exact div_nonneg (mul_nonneg hv0 (sub_nonneg.mpr hu1)) hDp.le
    have hs1 : s ≤ 1 := by
      rw [div_le_one hDp]
      rw [hD₂]
      linarith
    let z : HVec :=
      AffineMap.lineMap
        (AffineMap.lineMap (klein a) (klein c) u) (klein b) r
    have hA : (1 - r) * (1 - u) = s := by
      change (1 - u * (1 - v) / D) * (1 - u) =
        v * (1 - u) / D
      field_simp [hDz]
      rw [hD₁]
      ring
    have hB : r = (1 - s) * (1 - v) := by
      change u * (1 - v) / D =
        (1 - v * (1 - u) / D) * (1 - v)
      field_simp [hDz]
      rw [hD₂]
      ring
    have hC : (1 - r) * u = (1 - s) * v := by
      change (1 - u * (1 - v) / D) * u =
        (1 - v * (1 - u) / D) * v
      field_simp [hDz]
      ring
    have hz :
        z = AffineMap.lineMap
          (AffineMap.lineMap (klein b) (klein c) v) (klein a) s := by
      ext i
      simp [z, AffineMap.lineMap_apply]
      linear_combination
        (klein a i) * hA + (klein b i) * hB + (klein c i) * hC
    have hpzb : Wbtw ℝ (klein p) z (klein b) := by
      refine ⟨r, ⟨hr0, hr1⟩, ?_⟩
      rw [← hp]
    have hqza : Wbtw ℝ (klein q) z (klein a) := by
      refine ⟨s, ⟨hs0, hs1⟩, ?_⟩
      rw [← hq]
      exact hz.symm
    have hzmem : z ∈ Metric.ball (0 : HVec) 1 := by
      apply (convex_ball (0 : HVec) 1).mem_of_wbtw hpzb
      · simpa [Metric.mem_ball] using norm_klein_lt_one p
      · simpa [Metric.mem_ball] using norm_klein_lt_one b
    have hznorm : ‖z‖ < 1 := by
      simpa [Metric.mem_ball] using hzmem
    let zd : KDisk := ⟨z, hznorm⟩
    refine ⟨ofKlein zd, ?_, ?_⟩
    · simpa [hyperbolicBetweenness, zd] using hpzb
    · simpa [hyperbolicBetweenness, zd] using hqza

lemma hyperbolicLowerDimension :
    ∃ a b c : HPoint,
      ¬ hyperbolicBetweenness a b c ∧
      ¬ hyperbolicBetweenness b c a ∧
      ¬ hyperbolicBetweenness c a b := by
  let o : KDisk := ⟨0, by norm_num⟩
  let x : KDisk :=
    ⟨(2 : ℝ)⁻¹ • EuclideanSpace.single 0 1, by
      norm_num [norm_smul]⟩
  let y : KDisk :=
    ⟨(2 : ℝ)⁻¹ • EuclideanSpace.single 1 1, by
      norm_num [norm_smul]⟩
  refine ⟨ofKlein o, ofKlein x, ofKlein y, ?_, ?_, ?_⟩
  · rintro ⟨r, hr, h⟩
    have h0 := congrArg (fun p : HVec => p 0) h
    norm_num [hyperbolicBetweenness, o, x, y,
      AffineMap.lineMap_apply] at h0
  · rintro ⟨r, hr, h⟩
    have h1 := congrArg (fun p : HVec => p 1) h
    norm_num [hyperbolicBetweenness, o, x, y,
      AffineMap.lineMap_apply] at h1
  · rintro ⟨r, hr, h⟩
    have h0 := congrArg (fun p : HVec => p 0) h
    have h1 := congrArg (fun p : HVec => p 1) h
    norm_num [hyperbolicBetweenness, o, x, y,
      AffineMap.lineMap_apply] at h0 h1
    linarith

lemma equidistant_klein_equation {p q z : HPoint}
    (h : hyperbolicCongruence p z q z) :
    ⟪p.space - q.space, klein z⟫ = p.time - q.time := by
  change lorentz p z = lorentz q z at h
  rw [lorentz, lorentz, space_eq_time_smul_klein z,
    real_inner_smul_right, real_inner_smul_right] at h
  rw [inner_sub_left]
  apply (mul_left_cancel₀ z.time_pos.ne')
  nlinarith

lemma collinear_of_inner_eq (n : HVec) (r : ℝ) (hn : n ≠ 0)
    {a b c : HVec}
    (ha : ⟪n, a⟫ = r) (hb : ⟪n, b⟫ = r)
    (hc : ⟪n, c⟫ = r) :
    Collinear ℝ ({a, b, c} : Set HVec) := by
  have coord_eq (z : HVec) (hz : ⟪n, z⟫ = r) :
      n 0 * z 0 + n 1 * z 1 = r := by
    simpa [PiLp.inner_apply, Fin.sum_univ_two, mul_comm] using hz
  rw [collinear_iff_exists_forall_eq_smul_vadd]
  by_cases hn0 : n 0 = 0
  · have hn1 : n 1 ≠ 0 := by
      intro hn1
      apply hn
      ext i
      fin_cases i <;> assumption
    let p₀ : HVec :=
      (r / n 1) • EuclideanSpace.single 1 1
    let v : HVec := EuclideanSpace.single 0 1
    have hrepr (z : HVec) (hz : ⟪n, z⟫ = r) :
        ∃ t : ℝ, z = t • v +ᵥ p₀ := by
      refine ⟨z 0, ?_⟩
      ext i
      fin_cases i
      · simp [v, p₀]
      · simp [v, p₀]
        have hzcoord := coord_eq z hz
        rw [hn0, zero_mul, zero_add] at hzcoord
        field_simp [hn1]
        nlinarith
    refine ⟨p₀, v, ?_⟩
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hza | hzb | hzc
    · simpa [hza] using hrepr a ha
    · simpa [hzb] using hrepr b hb
    · simpa [hzc] using hrepr c hc
  · let p₀ : HVec :=
      (r / n 0) • EuclideanSpace.single 0 1
    let v : HVec :=
      EuclideanSpace.single 1 1 -
        (n 1 / n 0) • EuclideanSpace.single 0 1
    have hrepr (z : HVec) (hz : ⟪n, z⟫ = r) :
        ∃ t : ℝ, z = t • v +ᵥ p₀ := by
      refine ⟨z 1, ?_⟩
      ext i
      fin_cases i
      · simp [v, p₀]
        have hzcoord := coord_eq z hz
        field_simp [hn0]
        nlinarith
      · simp [v, p₀]
    refine ⟨p₀, v, ?_⟩
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hza | hzb | hzc
    · simpa [hza] using hrepr a ha
    · simpa [hzb] using hrepr b hb
    · simpa [hzc] using hrepr c hc

lemma hyperbolicUpperDimension (a b c p q : HPoint)
    (hpq : p ≠ q)
    (hpa : hyperbolicCongruence p a q a)
    (hpb : hyperbolicCongruence p b q b)
    (hpc : hyperbolicCongruence p c q c) :
    hyperbolicBetweenness a b c ∨
      hyperbolicBetweenness b c a ∨
      hyperbolicBetweenness c a b := by
  let n : HVec := p.space - q.space
  have hn : n ≠ 0 := by
    intro hn0
    have hspace : p.space = q.space := sub_eq_zero.mp hn0
    have htime : p.time = q.time := by
      have hp := time_sq p
      have hq := time_sq q
      rw [hspace] at hp
      nlinarith [p.time_pos, q.time_pos,
        sq_nonneg (p.time + q.time)]
    exact hpq (HPoint.ext htime hspace)
  have hcol : Collinear ℝ ({klein a, klein b, klein c} : Set HVec) := by
    apply collinear_of_inner_eq n (p.time - q.time) hn
    · exact equidistant_klein_equation hpa
    · exact equidistant_klein_equation hpb
    · exact equidistant_klein_equation hpc
  simpa [hyperbolicBetweenness] using hcol.wbtw_or_wbtw_or_wbtw

lemma hyperbolicContinuity (X Y : Set HPoint)
    (hcut :
      ∃ a, ∀ x ∈ X, ∀ y ∈ Y, hyperbolicBetweenness a x y) :
    ∃ b, ∀ x ∈ X, ∀ y ∈ Y, hyperbolicBetweenness x b y := by
  classical
  rcases hcut with ⟨a, ha⟩
  rcases X.eq_empty_or_nonempty with hX | hX
  · subst X
    exact ⟨a, by simp⟩
  rcases Y.eq_empty_or_nonempty with hY | hY
  · subst Y
    exact ⟨a, by simp⟩
  by_cases hXa : ∀ x ∈ X, x = a
  · refine ⟨a, ?_⟩
    intro x hx y hy
    rw [hXa x hx]
    exact wbtw_self_left ℝ (klein a) (klein y)
  push Not at hXa
  rcases hXa with ⟨x₀, hx₀, hx₀a⟩
  have hax₀ : a ≠ x₀ := hx₀a.symm
  let f : ℝ →ᵃ[ℝ] HVec := AffineMap.lineMap (klein a) (klein x₀)
  have hf : Function.Injective f :=
    AffineMap.lineMap_injective ℝ (fun h => hax₀ (klein_injective h))
  have hyRep : ∀ y : Y, ∃ r : ℝ, 1 ≤ r ∧ f r = klein y := by
    intro y
    have h := ha x₀ hx₀ y y.property
    change Wbtw ℝ (klein a) (klein x₀) (klein y) at h
    rcases h.right_mem_image_Ici_of_left_ne
        (fun h => hax₀ (klein_injective h)) with ⟨r, hr, hry⟩
    exact ⟨r, hr, hry⟩
  let cy : Y → ℝ := fun y => Classical.choose (hyRep y)
  have hcy_ge (y : Y) : 1 ≤ cy y :=
    (Classical.choose_spec (hyRep y)).1
  have hcy_eq (y : Y) : f (cy y) = klein y :=
    (Classical.choose_spec (hyRep y)).2
  let y₀ : Y := ⟨Classical.choose hY, Classical.choose_spec hY⟩
  have hxRep : ∀ x : X, ∃ r : ℝ, 0 ≤ r ∧ f r = klein x := by
    intro x
    have h := ha x x.property y₀ y₀.property
    change Wbtw ℝ (klein a) (klein x) (klein y₀) at h
    rcases h with ⟨t, ht, htx⟩
    refine ⟨t * cy y₀,
      mul_nonneg ht.1 (zero_le_one.trans (hcy_ge y₀)), ?_⟩
    calc
      f (t * cy y₀) =
          AffineMap.lineMap (klein a) (f (cy y₀)) t := by
            simp [f]
      _ = AffineMap.lineMap (klein a) (klein y₀) t := by
            rw [hcy_eq]
      _ = klein x := htx
  let cx : X → ℝ := fun x => Classical.choose (hxRep x)
  have hcx_ge (x : X) : 0 ≤ cx x :=
    (Classical.choose_spec (hxRep x)).1
  have hcx_eq (x : X) : f (cx x) = klein x :=
    (Classical.choose_spec (hxRep x)).2
  have hbounds (x : X) (y : Y) : 0 ≤ cx x ∧ cx x ≤ cy y := by
    have h := ha x x.property y y.property
    change Wbtw ℝ (klein a) (klein x) (klein y) at h
    have hf0 : f 0 = klein a := by simp [f]
    rw [← hf0, ← hcx_eq x, ← hcy_eq y] at h
    have hs : Wbtw ℝ (0 : ℝ) (cx x) (cy y) :=
      hf.wbtw_map_iff.mp h
    exact (wbtw_iff_of_le (zero_le_one.trans (hcy_ge y))).mp hs
  let A : Set ℝ := Set.range cx
  have hAne : A.Nonempty := by
    let x₀X : X := ⟨x₀, hx₀⟩
    refine ⟨cx x₀X, ?_⟩
    exact Set.mem_range_self x₀X
  have hAbdd : BddAbove A := by
    refine ⟨cy y₀, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact (hbounds x y₀).2
  let s : ℝ := sSup A
  have hwbtw (x : X) (y : Y) :
      Wbtw ℝ (klein x) (f s) (klein y) := by
    have hxs : cx x ≤ s :=
      le_csSup hAbdd (Set.mem_range_self x)
    have hsy : s ≤ cy y := by
      apply csSup_le hAne
      rintro _ ⟨z, rfl⟩
      exact (hbounds z y).2
    have hs : Wbtw ℝ (cx x) s (cy y) :=
      Wbtw.of_le_of_le hxs hsy
    have hmapped := hs.map f
    rw [hcx_eq x, hcy_eq y] at hmapped
    exact hmapped
  let x₀X : X := ⟨x₀, hx₀⟩
  have hzmem : f s ∈ Metric.ball (0 : HVec) 1 := by
    apply (convex_ball (0 : HVec) 1).mem_of_wbtw (hwbtw x₀X y₀)
    · simpa [Metric.mem_ball] using norm_klein_lt_one x₀X
    · simpa [Metric.mem_ball] using norm_klein_lt_one y₀
  have hznorm : ‖f s‖ < 1 := by
    simpa [Metric.mem_ball] using hzmem
  let z : KDisk := ⟨f s, hznorm⟩
  refine ⟨ofKlein z, ?_⟩
  intro x hx y hy
  simpa [hyperbolicBetweenness, z] using
    hwbtw (⟨x, hx⟩ : X) (⟨y, hy⟩ : Y)

def kvec (x y : ℝ) : HVec :=
  x • EuclideanSpace.single 0 1 +
    y • EuclideanSpace.single 1 1

@[simp]
lemma kvec_apply_zero (x y : ℝ) : kvec x y 0 = x := by
  simp [kvec]

@[simp]
lemma kvec_apply_one (x y : ℝ) : kvec x y 1 = y := by
  simp [kvec]

def diskPoint (x y : ℝ) (h : x ^ 2 + y ^ 2 < 1) : HPoint :=
  ofKlein
    ⟨kvec x y, by
      rw [← (sq_lt_sq₀ (norm_nonneg _) zero_le_one)]
      simpa [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two,
        Real.norm_eq_abs, sq_abs, kvec] using h⟩

@[simp]
lemma klein_diskPoint (x y : ℝ) (h : x ^ 2 + y ^ 2 < 1) :
    klein (diskPoint x y h) = kvec x y :=
  klein_ofKlein _

@[reducible]
def hyperbolicTarski : TarskiAbsolute HPoint where
  B := hyperbolicBetweenness
  C := hyperbolicCongruence
  congr_refl := hyperbolicCongruence_refl
  congr_trans := hyperbolicCongruence_trans
  congr_id := hyperbolicCongruence_id
  segment_construction := hyperbolicSegmentConstruction
  five_segment := hyperbolicFiveSegment
  betw_id := hyperbolicBetweenness_id
  inner_pasch := hyperbolicInnerPasch
  lower_dim := hyperbolicLowerDimension
  upper_dim := hyperbolicUpperDimension
  continuity := hyperbolicContinuity

set_option maxHeartbeats 800000 in
lemma hyperbolicTarski_notEuclidean :
    ¬ Euclidean HPoint hyperbolicTarski := by
  let a : HPoint := diskPoint 0 0 (by norm_num)
  let b : HPoint := diskPoint (-1 / 2) (1 / 4) (by norm_num)
  let c : HPoint := diskPoint (1 / 2) (1 / 4) (by norm_num)
  let d : HPoint := diskPoint 0 (1 / 4) (by norm_num)
  let t : HPoint := diskPoint 0 (1 / 2) (by norm_num)
  have hadt : hyperbolicBetweenness a d t := by
    refine ⟨(1 / 2 : ℝ), by norm_num, ?_⟩
    ext i
    fin_cases i <;>
      norm_num [a, d, t, AffineMap.lineMap_apply]
  have hbdc : hyperbolicBetweenness b d c := by
    refine ⟨(1 / 2 : ℝ), by norm_num, ?_⟩
    ext i
    fin_cases i <;>
      norm_num [b, d, c, AffineMap.lineMap_apply]
  have had : a ≠ d := by
    intro h
    have h1 := congrArg (fun z : HVec => z 1) (congrArg klein h)
    norm_num [a, d] at h1
  intro hE
  rcases hE a b c d t hadt hbdc had with
    ⟨x, y, habx, hacy, hxty⟩
  change hyperbolicBetweenness a b x at habx
  change hyperbolicBetweenness a c y at hacy
  change hyperbolicBetweenness x t y at hxty
  have habk : klein a ≠ klein b := by
    intro h
    have h0 := congrArg (fun z : HVec => z 0) h
    norm_num [a, b] at h0
  have hack : klein a ≠ klein c := by
    intro h
    have h0 := congrArg (fun z : HVec => z 0) h
    norm_num [a, c] at h0
  rcases habx.right_mem_image_Ici_of_left_ne habk with ⟨r, hr, hxr⟩
  rcases hacy.right_mem_image_Ici_of_left_ne hack with ⟨s, hs, hys⟩
  rcases hxty with ⟨v, hv, hvt⟩
  change 1 ≤ r at hr
  change 1 ≤ s at hs
  change 0 ≤ v ∧ v ≤ 1 at hv
  have hx0 := congrArg (fun z : HVec => z 0) hxr.symm
  have hx1 := congrArg (fun z : HVec => z 1) hxr.symm
  have hy0 := congrArg (fun z : HVec => z 0) hys.symm
  have hy1 := congrArg (fun z : HVec => z 1) hys.symm
  norm_num [a, b, c, AffineMap.lineMap_apply] at hx0 hx1 hy0 hy1
  have ht0 := congrArg (fun z : HVec => z 0) hvt
  have ht1 := congrArg (fun z : HVec => z 1) hvt
  simp [AffineMap.lineMap_apply, t, hx0, hx1, hy0, hy1] at ht0 ht1
  have hleft : (1 - v) * r = 1 := by
    nlinarith only [ht0, ht1]
  have hright : v * s = 1 := by
    nlinarith only [ht0, ht1]
  have hxnormsq := EuclideanSpace.real_norm_sq_eq (klein x)
  rw [Fin.sum_univ_two, hx0, hx1] at hxnormsq
  have hxnormlt := norm_klein_lt_one x
  have hxquad : 5 * r ^ 2 < 16 := by
    have hsquare : ‖klein x‖ ^ 2 < 1 := by
      nlinarith only [hxnormlt, norm_nonneg (klein x),
        sq_nonneg (‖klein x‖ - 1)]
    nlinarith only [hxnormsq, hsquare]
  have hynormsq := EuclideanSpace.real_norm_sq_eq (klein y)
  rw [Fin.sum_univ_two, hy0, hy1] at hynormsq
  have hynormlt := norm_klein_lt_one y
  have hyquad : 5 * s ^ 2 < 16 := by
    have hsquare : ‖klein y‖ ^ 2 < 1 := by
      nlinarith only [hynormlt, norm_nonneg (klein y),
        sq_nonneg (‖klein y‖ - 1)]
    nlinarith only [hynormsq, hsquare]
  have hrlt : r < 9 / 5 := by
    have hr0 : 0 ≤ r := zero_le_one.trans hr
    apply (sq_lt_sq₀ hr0 (by norm_num)).mp
    nlinarith only [hxquad]
  have hslt : s < 9 / 5 := by
    have hs0 : 0 ≤ s := zero_le_one.trans hs
    apply (sq_lt_sq₀ hs0 (by norm_num)).mp
    nlinarith only [hyquad]
  have hrs : r * s = r + s := by
    linear_combination s * hleft + r * hright
  have hprod : (r - 1) * (s - 1) = 1 := by
    calc
      (r - 1) * (s - 1) = r * s - r - s + 1 := by ring
      _ = 1 := by rw [hrs]; ring
  have hrpos : 0 < r - 1 := by
    have hr0 : 0 ≤ r - 1 := sub_nonneg.mpr hr
    have hrne : r - 1 ≠ 0 := by
      intro hrz
      rw [hrz, zero_mul] at hprod
      norm_num at hprod
    exact lt_of_le_of_ne hr0 (Ne.symm hrne)
  have hspos : 0 < s - 1 := by
    have hs0 : 0 ≤ s - 1 := sub_nonneg.mpr hs
    have hsne : s - 1 ≠ 0 := by
      intro hsz
      rw [hsz, mul_zero] at hprod
      norm_num at hprod
    exact lt_of_le_of_ne hs0 (Ne.symm hsne)
  have hprodlt : (r - 1) * (s - 1) < (4 / 5 : ℝ) * (4 / 5) := by
    calc
      (r - 1) * (s - 1) < (4 / 5) * (s - 1) :=
        mul_lt_mul_of_pos_right (by linarith only [hrlt]) hspos
      _ < (4 / 5) * (4 / 5) :=
        mul_lt_mul_of_pos_left (by linarith only [hslt]) (by norm_num)
  norm_num [hprod] at hprodlt

end

end Submission.Hyperbolic
