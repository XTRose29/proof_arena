import Submission.BoundaryTauberian
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Data.Finset.Pi
import Mathlib.Data.Fintype.Pi

open Complex Filter MeasureTheory Real Set Topology

namespace Submission.FiniteSupportPD

private abbrev finPairSub (L : ℕ) (d : ℤ) :=
  {p : Fin L × Fin L // (p.1.1 : ℤ) - p.2.1 = d}

private noncomputable instance (L : ℕ) (d : ℤ) : Fintype (finPairSub L d) := by
  letI : Finite (finPairSub L d) :=
    Finite.of_injective (fun p : finPairSub L d => p.1) Subtype.val_injective
  exact Fintype.ofFinite _

private def finPairSubEquivOfNonneg {L : ℕ} {d : ℤ}
    (hd : 0 ≤ d) (hL : d.natAbs < L) :
    finPairSub L d ≃ Fin (L - d.natAbs) where
  toFun p := ⟨p.1.2, by
    have heq := p.2
    have habs : (d.natAbs : ℤ) = d := Int.natAbs_of_nonneg hd
    omega⟩
  invFun b :=
    ⟨(⟨b.1 + d.natAbs, by omega⟩, ⟨b.1, by omega⟩), by
      push_cast
      rw [abs_of_nonneg hd]
      ring⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · apply Fin.ext
      change p.1.2.1 + d.natAbs = p.1.1.1
      have heq := p.2
      have habs : (d.natAbs : ℤ) = d := Int.natAbs_of_nonneg hd
      omega
    · rfl
  right_inv b := by rfl

private def finPairSubNegEquiv (L : ℕ) (d : ℤ) :
    finPairSub L d ≃ finPairSub L (-d) where
  toFun p := ⟨(p.1.2, p.1.1), by
    dsimp
    linarith [p.2]⟩
  invFun p := ⟨(p.1.2, p.1.1), by
    dsimp
    linarith [p.2]⟩
  left_inv p := by rfl
  right_inv p := by rfl

private lemma card_finPairSub {L : ℕ} {d : ℤ} (hL : d.natAbs < L) :
    Fintype.card (finPairSub L d) = L - d.natAbs := by
  by_cases hd : 0 ≤ d
  · simpa using Fintype.card_congr (finPairSubEquivOfNonneg hd hL)
  · have hneg : 0 ≤ -d := neg_nonneg.mpr (le_of_not_ge hd)
    have habs : (-d).natAbs = d.natAbs := Int.natAbs_neg d
    rw [← habs]
    simpa using Fintype.card_congr
      ((finPairSubNegEquiv L d).trans
        (finPairSubEquivOfNonneg hneg (by simpa [habs] using hL)))

private abbrev boxPairSub (ι : Type*) [Fintype ι] (L : ℕ) (d : ι → ℤ) :=
  {p : (ι → Fin L) × (ι → Fin L) //
    ∀ i, ((p.1 i : ℕ) : ℤ) - (p.2 i : ℕ) = d i}

private def boxPairSubEquiv (ι : Type*) [Fintype ι] (L : ℕ) (d : ι → ℤ) :
    boxPairSub ι L d ≃ (∀ i, finPairSub L (d i)) where
  toFun p i := ⟨(p.1.1 i, p.1.2 i), p.2 i⟩
  invFun q := ⟨(fun i => (q i).1.1, fun i => (q i).1.2), fun i => (q i).2⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext <;> funext i <;> rfl
  right_inv q := by
    funext i
    apply Subtype.ext
    rfl

private noncomputable instance (ι : Type*) [Fintype ι] (L : ℕ) (d : ι → ℤ) :
    Fintype (boxPairSub ι L d) := by
  letI : DecidableEq ι := Classical.decEq _
  letI : Fintype (∀ i, finPairSub L (d i)) := Pi.instFintype
  exact Fintype.ofEquiv (∀ i, finPairSub L (d i)) (boxPairSubEquiv ι L d).symm

private lemma card_boxPairSub {ι : Type*} [Fintype ι]
    {L : ℕ} {d : ι → ℤ} (hL : ∀ i, (d i).natAbs < L) :
    Fintype.card (boxPairSub ι L d) = ∏ i, (L - (d i).natAbs) := by
  classical
  rw [Fintype.card_congr (boxPairSubEquiv ι L d), Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro i _hi
  exact card_finPairSub (hL i)

private noncomputable def boxOverlapRatio {ι : Type*} [Fintype ι]
    (d : ι → ℤ) (L : ℕ) : ℝ :=
  Fintype.card (boxPairSub ι L d) / (L : ℝ) ^ Fintype.card ι

private lemma eventually_natAbs_lt {ι : Type*} [Fintype ι] (d : ι → ℤ) :
    ∀ᶠ L : ℕ in atTop, ∀ i, (d i).natAbs < L := by
  classical
  refine eventually_atTop.2 ⟨1 + ∑ i, (d i).natAbs, fun L hL i => ?_⟩
  have hi : (d i).natAbs ≤ ∑ j, (d j).natAbs :=
    Finset.single_le_sum (fun j _hj => Nat.zero_le (d j).natAbs) (Finset.mem_univ i)
  omega

private lemma tendsto_nat_sub_div (a : ℕ) :
    Filter.Tendsto (fun L : ℕ => ((L - a : ℕ) : ℝ) / (L : ℝ))
      atTop (𝓝 1) := by
  have hzero : Filter.Tendsto (fun L : ℕ => (a : ℝ) / (L : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hone : Filter.Tendsto (fun L : ℕ => 1 - (a : ℝ) / (L : ℝ))
      atTop (𝓝 1) := by simpa using tendsto_const_nhds.sub hzero
  apply hone.congr'
  filter_upwards [eventually_ge_atTop a, eventually_ne_atTop (0 : ℕ)] with L hL hL0
  rw [Nat.cast_sub hL]
  field_simp [hL0]

private lemma tendsto_boxOverlapRatio {ι : Type*} [Fintype ι] (d : ι → ℤ) :
    Filter.Tendsto (boxOverlapRatio d) atTop (𝓝 1) := by
  classical
  have hprod : Filter.Tendsto
      (fun L : ℕ => ∏ i, (((L - (d i).natAbs : ℕ) : ℝ) / (L : ℝ)))
      atTop (𝓝 1) := by
    simpa using tendsto_finsetProd (s := Finset.univ)
      (fun i _hi => tendsto_nat_sub_div (d i).natAbs)
  apply hprod.congr'
  filter_upwards [eventually_natAbs_lt d] with L hL
  unfold boxOverlapRatio
  rw [card_boxPairSub hL]
  push_cast
  rw [Finset.prod_div_distrib]
  congr 1
  simp

private def boxCoord {ι : Type*} {L : ℕ} (a : ι → Fin L) : ι → ℤ :=
  fun i => (a i : ℕ)

private def boxDiff {ι : Type*} {L : ℕ}
    (p : (ι → Fin L) × (ι → Fin L)) : ι → ℤ :=
  boxCoord p.1 - boxCoord p.2

private def boxPairSubEquivFilter (ι : Type*) [Fintype ι] [DecidableEq ι]
    (L : ℕ) (d : ι → ℤ) :
    boxPairSub ι L d ≃
      ↥((Finset.univ : Finset ((ι → Fin L) × (ι → Fin L))).filter
        fun p => boxDiff p = d) where
  toFun p := ⟨p.1, by
    simp only [Finset.mem_filter]
    constructor
    · exact Finset.mem_univ _
    funext i
    exact p.2 i⟩
  invFun p := ⟨p.1, fun i => congrFun (Finset.mem_filter.mp p.2).2 i⟩
  left_inv p := by rfl
  right_inv p := by rfl

private lemma card_filter_boxDiff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : ℕ) (d : ι → ℤ) :
    ((Finset.univ : Finset ((ι → Fin L) × (ι → Fin L))).filter
      fun p => boxDiff p = d).card = Fintype.card (boxPairSub ι L d) := by
  classical
  rw [← Fintype.card_coe]
  exact Fintype.card_congr (boxPairSubEquivFilter ι L d).symm

private lemma sum_boxDiff_eq_sum_overlap {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : ℕ) (S : Finset (ι → ℤ)) (F : (ι → ℤ) → ℂ)
    (hsupp : ∀ d, d ∉ S → F d = 0) :
    (∑ a : ι → Fin L, ∑ b : ι → Fin L, F (boxDiff (a, b))) =
      ∑ d ∈ S, (Fintype.card (boxPairSub ι L d) : ℂ) * F d := by
  classical
  rw [← Fintype.sum_prod_type']
  have hfiber := Finset.sum_fiberwise_eq_sum_filter
    (s := (Finset.univ : Finset ((ι → Fin L) × (ι → Fin L))))
    (t := S) boxDiff (fun p => F (boxDiff p))
  calc
    ∑ p : (ι → Fin L) × (ι → Fin L), F (boxDiff p) =
        ∑ p ∈ (Finset.univ.filter fun p : (ι → Fin L) × (ι → Fin L) =>
          boxDiff p ∈ S), F (boxDiff p) := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro p _hp hpnot
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hpnot
      exact hsupp (boxDiff p) hpnot
    _ = ∑ d ∈ S,
        ∑ p ∈ (Finset.univ.filter fun p : (ι → Fin L) × (ι → Fin L) =>
          boxDiff p = d), F (boxDiff p) := hfiber.symm
    _ = ∑ d ∈ S, (Fintype.card (boxPairSub ι L d) : ℂ) * F d := by
      apply Finset.sum_congr rfl
      intro d hd
      calc
        ∑ p with boxDiff p = d, F (boxDiff p) =
            ∑ p ∈ (Finset.univ.filter fun p : (ι → Fin L) × (ι → Fin L) =>
              boxDiff p = d), F d := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [(Finset.mem_filter.mp hp).2]
        _ = (Fintype.card (boxPairSub ι L d) : ℂ) * F d := by
          rw [Finset.sum_const, card_filter_boxDiff]
          simp

def IsQuadraticallyNonnegative (k : ℝ → ℂ) : Prop :=
  ∀ {n : Type} [Fintype n] (t : n → ℝ) (c : n → ℂ),
    0 ≤ (∑ i, ∑ j, star (c i) * k (t i - t j) * c j).re

private lemma star_exp_mul_exp {a b : ℝ} :
    star (Complex.exp (((a : ℂ) * I))) * Complex.exp (((b : ℂ) * I)) =
      Complex.exp (-((((a - b : ℝ) : ℂ) * I))) := by
  have harg : (starRingEnd ℂ) (((a : ℂ) * I)) = -((a : ℂ) * I) := by
    apply Complex.ext <;> simp
  rw [← starRingEnd_apply, ← Complex.exp_conj, harg, ← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma quadratic_fourierAtom_eq {n : Type} [Fintype n]
    (t : n → ℝ) (c : n → ℂ) (q y : ℝ) :
    (∑ i, ∑ j, star (c i) *
        ((q : ℂ) * Complex.exp
          (-((((t i - t j) * y : ℝ) : ℂ) * I))) * c j) =
      ((q * Complex.normSq
        (∑ i, Complex.exp (((t i * y : ℝ) : ℂ) * I) * c i) : ℝ) : ℂ) := by
  let v : n → ℂ := fun i =>
    Complex.exp (((t i * y : ℝ) : ℂ) * I) * c i
  have hatom (i j : n) :
      star (c i) *
          ((q : ℂ) * Complex.exp
            (-((((t i - t j) * y : ℝ) : ℂ) * I))) * c j =
        (q : ℂ) * star (v i) * v j := by
    rw [show ((t i - t j) * y : ℝ) = t i * y - t j * y by ring,
      ← star_exp_mul_exp]
    dsimp [v]
    simp only [map_mul]
    ring
  simp_rw [hatom]
  calc
    ∑ i, ∑ j, (q : ℂ) * star (v i) * v j =
        ∑ i, ((q : ℂ) * star (v i)) * ∑ j, v j := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [Finset.mul_sum]
    _ = (∑ i, (q : ℂ) * star (v i)) * ∑ j, v j := by
      rw [Finset.sum_mul]
    _ = ((q : ℂ) * ∑ i, star (v i)) * ∑ j, v j := by
      have hmul : (q : ℂ) * ∑ i, star (v i) =
          ∑ i, (q : ℂ) * star (v i) := by
        rw [Finset.mul_sum]
      rw [hmul]
    _ = (q : ℂ) *
        star (∑ i, v i) * ∑ j, v j := by
      have hstar : star (∑ i, v i) = ∑ i, star (v i) := by
        simpa only [starRingEnd_apply] using
          map_sum (starRingEnd ℂ) v Finset.univ
      rw [hstar]
    _ = ((q * Complex.normSq (∑ i, v i) : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [Complex.normSq_apply] <;> ring

noncomputable def fourierKernel {A : Type} [MeasurableSpace A]
    (q X : A → ℝ) (mu : Measure A) (t : ℝ) : ℂ :=
  ∫ a, (q a : ℂ) *
    Complex.exp (-((((t * X a : ℝ) : ℂ) * I))) ∂mu

lemma fourierKernel_quadraticallyNonnegative
    {A : Type} [MeasurableSpace A] {q X : A → ℝ} {mu : Measure A}
    (hq : ∀ᵐ a ∂mu, 0 ≤ q a)
    (hint : ∀ t : ℝ, Integrable (fun a => (q a : ℂ) *
      Complex.exp (-((((t * X a : ℝ) : ℂ) * I)))) mu) :
    IsQuadraticallyNonnegative (fourierKernel q X mu) := by
  intro n _inst t c
  let F : n → n → A → ℂ := fun i j a =>
    star (c i) * ((q a : ℂ) *
      Complex.exp (-(((((t i - t j) * X a : ℝ) : ℂ) * I)))) * c j
  have hFint (i j : n) : Integrable (F i j) mu :=
    ((hint (t i - t j)).const_mul (star (c i))).mul_const (c j)
  have hsumInt : Integrable (fun a => ∑ i, ∑ j, F i j a) mu := by
    apply integrable_finsetSum Finset.univ
    intro i _hi
    apply integrable_finsetSum Finset.univ
    intro j _hj
    exact hFint i j
  have heq :
      (∑ i, ∑ j, star (c i) * fourierKernel q X mu (t i - t j) * c j) =
        ∫ a, ∑ i, ∑ j, F i j a ∂mu := by
    rw [integral_finsetSum Finset.univ]
    · apply Finset.sum_congr rfl
      intro i _hi
      rw [integral_finsetSum Finset.univ]
      · apply Finset.sum_congr rfl
        intro j _hj
        dsimp [F, fourierKernel]
        rw [← integral_const_mul, ← integral_mul_const]
      · intro j _hj
        exact hFint i j
    · intro i _hi
      exact integrable_finsetSum Finset.univ fun j _hj => hFint i j
  rw [heq]
  calc
    0 ≤ ∫ a, (∑ i, ∑ j, F i j a).re ∂mu := by
      apply integral_nonneg_of_ae
      filter_upwards [hq] with a ha
      dsimp [F]
      have hre :
          (∑ i, ∑ j, star (c i) *
              ((q a : ℂ) * Complex.exp
                (-((((t i - t j) * X a : ℝ) : ℂ) * I))) * c j).re =
            q a * Complex.normSq
              (∑ i, Complex.exp (((t i * X a : ℝ) : ℂ) * I) * c i) := by
        simpa only [ofReal_re] using congrArg Complex.re
          (quadratic_fourierAtom_eq t c (q a) (X a))
      have hnon : 0 ≤
          (∑ i, ∑ j, star (c i) *
            ((q a : ℂ) * Complex.exp
              (-((((t i - t j) * X a : ℝ) : ℂ) * I))) * c j).re := by
        rw [hre]
        exact mul_nonneg ha (Complex.normSq_nonneg _)
      simpa only [starRingEnd_apply] using hnon
    _ = (∫ a, ∑ i, ∑ j, F i j a ∂mu).re := integral_re hsumInt

private lemma phase_kernel_eq {ι : Type*} {L : ℕ}
    (e : (ι → ℤ) →+ ℝ) (k : ℝ → ℂ) (x : ℝ)
    (a b : ι → Fin L) :
    star (Complex.exp (-(((e (boxCoord a) * x : ℝ) : ℂ) * I))) *
          k (e (boxCoord a) - e (boxCoord b)) *
          Complex.exp (-(((e (boxCoord b) * x : ℝ) : ℂ) * I)) =
      k (e (boxDiff (a, b))) *
        Complex.exp ((((e (boxDiff (a, b)) * x : ℝ) : ℂ) * I)) := by
  have hdiff : e (boxDiff (a, b)) = e (boxCoord a) - e (boxCoord b) := by
    rw [boxDiff, e.map_sub]
  rw [hdiff]
  calc
    _ = k (e (boxCoord a) - e (boxCoord b)) *
        (star (Complex.exp (-(((e (boxCoord a) * x : ℝ) : ℂ) * I))) *
          Complex.exp (-(((e (boxCoord b) * x : ℝ) : ℂ) * I))) := by ring
    _ = _ := by
      congr 1
      have harg :
          (starRingEnd ℂ) (-(((e (boxCoord a) * x : ℝ) : ℂ) * I)) =
            (((e (boxCoord a) * x : ℝ) : ℂ) * I) := by
        apply Complex.ext <;> simp
      rw [← starRingEnd_apply, ← Complex.exp_conj, harg, ← Complex.exp_add]
      congr 1
      push_cast
      ring

lemma fourierSum_nonneg_of_integer_coordinates
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (e : (ι → ℤ) →+ ℝ) (k : ℝ → ℂ)
    (hpd : IsQuadraticallyNonnegative k) (S : Finset (ι → ℤ))
    (hsupp : ∀ d, d ∉ S → k (e d) = 0) (x : ℝ) :
    0 ≤ (∑ d ∈ S,
      k (e d) * Complex.exp ((((e d * x : ℝ) : ℂ) * I))).re := by
  let G : (ι → ℤ) → ℂ := fun d =>
    k (e d) * Complex.exp ((((e d * x : ℝ) : ℂ) * I))
  let A : ℕ → ℂ := fun L =>
    ∑ d ∈ S, G d * (boxOverlapRatio d L : ℂ)
  have hGsupport : ∀ d, d ∉ S → G d = 0 := by
    intro d hd
    simp [G, hsupp d hd]
  have hnonneg : ∀ᶠ L : ℕ in atTop, 0 ≤ (A L).re := by
    filter_upwards [eventually_ne_atTop (0 : ℕ)] with L hL
    let t : (ι → Fin L) → ℝ := fun a => e (boxCoord a)
    let c : (ι → Fin L) → ℂ := fun a =>
      Complex.exp (-(((t a * x : ℝ) : ℂ) * I))
    have hquad := hpd t c
    have hphase :
        (∑ a, ∑ b, star (c a) * k (t a - t b) * c b) =
          ∑ a : ι → Fin L, ∑ b : ι → Fin L, G (boxDiff (a, b)) := by
      apply Finset.sum_congr rfl
      intro a _ha
      apply Finset.sum_congr rfl
      intro b _hb
      exact phase_kernel_eq e k x a b
    have hsum := sum_boxDiff_eq_sum_overlap (ι := ι) L S G hGsupport
    have hnorm :
        (∑ d ∈ S, (Fintype.card (boxPairSub ι L d) : ℂ) * G d) /
            (((L : ℝ) ^ Fintype.card ι : ℝ) : ℂ) = A L := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro d hd
      dsimp [A, boxOverlapRatio]
      push_cast
      ring
    have hqdiv : 0 ≤
        ((∑ a, ∑ b, star (c a) * k (t a - t b) * c b) /
          (((L : ℝ) ^ Fintype.card ι : ℝ) : ℂ)).re := by
      have hden : 0 ≤ (L : ℝ) ^ Fintype.card ι :=
        (pow_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hL)) _).le
      rw [Complex.div_re]
      simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero,
        Complex.normSq_ofReal, zero_div, add_zero]
      exact div_nonneg (mul_nonneg hquad hden) (mul_nonneg hden hden)
    rw [hphase, hsum, hnorm] at hqdiv
    exact hqdiv
  have hlim : Filter.Tendsto A atTop (𝓝 (∑ d ∈ S, G d)) := by
    dsimp [A]
    apply tendsto_finsetSum
    intro d hd
    have hr : Filter.Tendsto (fun L : ℕ => (boxOverlapRatio d L : ℂ))
        atTop (𝓝 1) := (tendsto_boxOverlapRatio d).ofReal
    simpa using tendsto_const_nhds.mul hr
  have hre := continuous_re.continuousAt.tendsto.comp hlim
  have hresult : 0 ≤ (∑ d ∈ S, G d).re := ge_of_tendsto hre hnonneg
  simpa [G] using hresult

end Submission.FiniteSupportPD
