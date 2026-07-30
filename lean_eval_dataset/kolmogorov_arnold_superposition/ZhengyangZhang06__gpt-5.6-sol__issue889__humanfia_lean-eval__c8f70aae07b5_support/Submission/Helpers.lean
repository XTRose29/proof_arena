import Mathlib

open Set Filter Topology
open scoped BigOperators BoundedContinuousFunction

namespace Submission.Helpers

noncomputable section

abbrev UnitInterval := Set.Icc (0 : ℝ) 1

abbrev Cube (n : ℕ) := Set.Icc (0 : Fin n → ℝ) 1

abbrev InnerFamily (n : ℕ) :=
  Fin (2 * n + 1) → Fin n → (UnitInterval →ᵇ ℝ)

abbrev OuterFamily (n : ℕ) :=
  Fin (2 * n + 1) → (ℝ →ᵇ ℝ)

def cubeCoord {n : ℕ} (x : Cube n) (l : Fin n) : UnitInterval :=
  ⟨x.1 l, x.2.1 l, x.2.2 l⟩

lemma continuous_cubeCoord {n : ℕ} (l : Fin n) :
    Continuous fun x : Cube n ↦ cubeCoord x l := by
  apply Continuous.subtype_mk
  exact (continuous_apply l).comp continuous_subtype_val

def cubeCoordMap {n : ℕ} (l : Fin n) : C(Cube n, UnitInterval) :=
  ⟨fun x ↦ cubeCoord x l, continuous_cubeCoord l⟩

def innerSum {n : ℕ} (ψ : InnerFamily n) (k : Fin (2 * n + 1)) : Cube n →ᵇ ℝ :=
  ∑ l, (ψ k l).compContinuous (cubeCoordMap l)

def superpose {n : ℕ} (ψ : InnerFamily n) (G : OuterFamily n) : Cube n →ᵇ ℝ :=
  ∑ k, (G k).compContinuous (innerSum ψ k).toContinuousMap

@[simp] lemma innerSum_apply {n : ℕ}
    (ψ : InnerFamily n) (k : Fin (2 * n + 1)) (x : Cube n) :
    innerSum ψ k x = ∑ l, ψ k l (cubeCoord x l) := by
  simp [innerSum, cubeCoordMap]

@[simp] lemma superpose_apply {n : ℕ}
    (ψ : InnerFamily n) (G : OuterFamily n) (x : Cube n) :
    superpose ψ G x = ∑ k, G k (innerSum ψ k x) := by
  simp [superpose]

lemma superpose_add {n : ℕ}
    (ψ : InnerFamily n) (G H : OuterFamily n) :
    superpose ψ (G + H) = superpose ψ G + superpose ψ H := by
  ext x
  simp [superpose_apply, Finset.sum_add_distrib]

lemma superpose_zero {n : ℕ}
    (ψ : InnerFamily n) : superpose ψ 0 = 0 := by
  ext x
  simp [superpose_apply]

lemma norm_superpose_le_sum_norm {n : ℕ}
    (ψ : InnerFamily n) (G : OuterFamily n) :
    ‖superpose ψ G‖ ≤ ∑ k, ‖G k‖ := by
  apply (BoundedContinuousFunction.norm_le (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)).2
  intro x
  calc
    ‖superpose ψ G x‖ = ‖∑ k, G k (innerSum ψ k x)‖ := by rw [superpose_apply]
    _ ≤ ∑ k, ‖G k (innerSum ψ k x)‖ := norm_sum_le _ _
    _ ≤ ∑ k, ‖G k‖ := Finset.sum_le_sum fun k _ ↦ (G k).norm_coe_le_norm _

lemma norm_superpose_sub_le {n : ℕ}
    (ψ : InnerFamily n) (G H : OuterFamily n) :
    ‖superpose ψ G - superpose ψ H‖ ≤ ∑ k, ‖G k - H k‖ := by
  have heq : superpose ψ G - superpose ψ H = superpose ψ (G - H) := by
    ext x
    simp [superpose_apply, Finset.sum_sub_distrib]
  rw [heq]
  exact norm_superpose_le_sum_norm ψ (G - H)

lemma continuous_innerSum {n : ℕ} (k : Fin (2 * n + 1)) :
    Continuous fun ψ : InnerFamily n ↦ innerSum ψ k := by
  apply continuous_finsetSum
  intro l _
  exact (BoundedContinuousFunction.continuous_compContinuous (cubeCoordMap l)).comp
    ((continuous_apply l).comp (continuous_apply k))

lemma continuous_superpose_inner {n : ℕ} [CompactSpace (Cube n)] (G : OuterFamily n) :
    Continuous fun ψ : InnerFamily n ↦ superpose ψ G := by
  apply continuous_finsetSum
  intro k _
  let E := ContinuousMap.isometryEquivBoundedOfCompact (Cube n) ℝ
  have hinner : Continuous fun ψ : InnerFamily n ↦ E.symm (innerSum ψ k) :=
    E.symm.continuous.comp (continuous_innerSum k)
  have hcomp : Continuous fun q : C(Cube n, ℝ) ↦ (G k).toContinuousMap.comp q :=
    ContinuousMap.continuous_postcomp (G k).toContinuousMap
  have hout : Continuous fun ψ : InnerFamily n ↦
      E ((G k).toContinuousMap.comp (E.symm (innerSum ψ k))) :=
    E.continuous.comp (hcomp.comp hinner)
  have heq : (fun ψ : InnerFamily n ↦
      E ((G k).toContinuousMap.comp (E.symm (innerSum ψ k)))) =
      fun ψ ↦ (G k).compContinuous (innerSum ψ k).toContinuousMap := by
    funext ψ
    ext x
    rfl
  rw [← heq]
  exact hout

def layerCountR (n : ℕ) : ℝ := 2 * n + 1

def stabilityRate (n : ℕ) : ℝ := 1 / (4 * layerCountR n)

def approximationRate (n : ℕ) : ℝ := 1 - 3 / (4 * layerCountR n)

def contractionRate (n : ℕ) : ℝ := 1 - 1 / (2 * layerCountR n)

lemma layerCountR_pos (n : ℕ) : 0 < layerCountR n := by
  simp [layerCountR]
  positivity

lemma stability_add_approximation (n : ℕ) :
    stabilityRate n + approximationRate n = contractionRate n := by
  have hm := layerCountR_pos n
  dsimp [stabilityRate, approximationRate, contractionRate]
  field_simp
  ring

lemma contractionRate_nonneg (n : ℕ) : 0 ≤ contractionRate n := by
  have hm : 1 ≤ layerCountR n := by
    simp [layerCountR]
  have hden : 1 ≤ 2 * layerCountR n := by linarith
  have hfrac : 1 / (2 * layerCountR n) ≤ 1 := (div_le_one (by positivity)).2 hden
  dsimp [contractionRate]
  linarith

lemma contractionRate_lt_one (n : ℕ) : contractionRate n < 1 := by
  have hm := layerCountR_pos n
  dsimp [contractionRate]
  exact sub_lt_self _ (by positivity)

lemma approximationRate_nonneg (n : ℕ) (hn : 1 ≤ n) : 0 ≤ approximationRate n := by
  have hm : (3 : ℝ) ≤ 4 * layerCountR n := by
    dsimp [layerCountR]
    exact_mod_cast (show 3 ≤ 4 * (2 * n + 1) by omega)
  have hden : (0 : ℝ) < 4 * layerCountR n := by
    have := layerCountR_pos n
    positivity
  have hfrac : 3 / (4 * layerCountR n) ≤ 1 := (div_le_one hden).2 hm
  dsimp [approximationRate]
  linarith

lemma exists_inner_modulus (n : ℕ) (p : InnerFamily n) {e : ℝ} (he : 0 < e) :
    ∃ d : ℝ, 0 < d ∧ ∀ k l (s t : UnitInterval), dist s t < d →
      dist (p k l s) (p k l t) < e := by
  letI : CompactSpace UnitInterval := isCompact_iff_compactSpace.mp isCompact_Icc
  let P : UnitInterval → (Fin (2 * n + 1) → Fin n → ℝ) :=
    fun t k l ↦ p k l t
  have hP : Continuous P := by
    apply continuous_pi
    intro k
    apply continuous_pi
    intro l
    exact (p k l).continuous
  obtain ⟨d, hd, hmod⟩ :=
    Metric.uniformContinuous_iff.mp
      (CompactSpace.uniformContinuous_of_continuous hP) e he
  refine ⟨d, hd, ?_⟩
  intro k l s t hst
  have hout := hmod hst
  calc
    dist (p k l s) (p k l t) = ‖(P s - P t) k l‖ := by
      simp [P, dist_eq_norm]
    _ ≤ ‖(P s - P t) k‖ := norm_le_pi_norm ((P s - P t) k) l
    _ ≤ ‖P s - P t‖ := norm_le_pi_norm (P s - P t) k
    _ = dist (P s) (P t) := by rw [dist_eq_norm]
    _ < e := hout

def digitCode (base n : ℕ) (a : Fin n → Fin base) : ℕ :=
  ∑ l, (a l).1 * base ^ l.1

lemma digitCode_succ (base n : ℕ) (a : Fin (n + 1) → Fin base) :
    digitCode base (n + 1) a = (a 0).1 + base * digitCode base n (fun l ↦ a l.succ) := by
  unfold digitCode
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ']
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  ring

lemma digitCode_injective (base n : ℕ) (hbase : 0 < base) :
    Function.Injective (digitCode base n) := by
  induction n with
  | zero =>
      intro a b _
      exact Subsingleton.elim _ _
  | succ n ih =>
      intro a b hab
      rw [digitCode_succ, digitCode_succ] at hab
      have hzero : (a 0).1 = (b 0).1 := by
        have hmod := congrArg (fun t ↦ t % base) hab
        simpa [Nat.add_mod, Nat.mod_eq_of_lt (a 0).2, Nat.mod_eq_of_lt (b 0).2,
          Nat.mul_mod] using hmod
      have htail : digitCode base n (fun l ↦ a l.succ) =
          digitCode base n (fun l ↦ b l.succ) := by
        rw [hzero] at hab
        exact Nat.mul_left_cancel hbase (Nat.add_left_cancel hab)
      have hfun := ih htail
      funext i
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · exact Fin.ext hzero
      · exact congr_fun hfun j

lemma exists_separating_perturbation (base n : ℕ) (hbase : 0 < base)
    (b : Fin n → Fin base → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ A : Fin n → Fin base → ℝ,
      (∀ l a, |A l a - b l a| < ε) ∧
      Function.Injective (fun a : Fin n → Fin base ↦ ∑ l, A l (a l)) := by
  classical
  let T := Fin n → Fin base
  let bsum (a : T) : ℝ := ∑ l, b l (a l)
  let code (a : T) : ℝ := digitCode base n a
  have hcode : Function.Injective code := by
    intro a c hac
    apply digitCode_injective base n hbase
    dsimp [code] at hac
    exact_mod_cast hac
  let forbidden : Set ℝ :=
    (fun p : T × T ↦ (bsum p.2 - bsum p.1) / (code p.1 - code p.2)) ''
      {p | p.1 ≠ p.2}
  have hforbidden : forbidden.Finite := (Set.toFinite {p : T × T | p.1 ≠ p.2}).image _
  let C : ℝ := (∑ l : Fin n, (base - 1) * base ^ l.1) + 1
  have hC : 0 < C := by
    dsimp [C]
    positivity
  let seq (q : ℕ) : ℝ := ε / (((q : ℝ) + 1) * C)
  have hseq_pos (q : ℕ) : 0 < seq q := by
    dsimp [seq]
    positivity
  have hseq_inj : Function.Injective seq := by
    intro p q hpq
    dsimp [seq] at hpq
    have hp : 0 < (p : ℝ) + 1 := by positivity
    have hq : 0 < (q : ℝ) + 1 := by positivity
    field_simp at hpq
    exact_mod_cast (by nlinarith : (p : ℝ) = q)
  have hrange : (Set.range seq).Infinite := infinite_range_of_injective hseq_inj
  have hexists : ∃ q, seq q ∉ forbidden := by
    by_contra h
    push Not at h
    have hsub : Set.range seq ⊆ forbidden := by
      rintro x ⟨q, rfl⟩
      exact h q
    exact hrange (hforbidden.subset hsub)
  obtain ⟨q, hq⟩ := hexists
  let θ := seq q
  let A : Fin n → Fin base → ℝ := fun l a ↦
    b l a + θ * (a.1 : ℝ) * (base : ℝ) ^ l.1
  refine ⟨A, ?_, ?_⟩
  · intro l a
    have hdigit : (a.1 * base ^ l.1 : ℝ) ≤ C - 1 := by
      have hterm : a.1 * base ^ l.1 ≤ ∑ j : Fin n, (base - 1) * base ^ j.1 := by
        calc
          a.1 * base ^ l.1 ≤ (base - 1) * base ^ l.1 := by gcongr; omega
          _ ≤ ∑ j : Fin n, (base - 1) * base ^ j.1 :=
            Finset.single_le_sum
              (f := fun j : Fin n ↦ (base - 1) * base ^ j.1)
              (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ l)
      dsimp [C]
      norm_num
      exact_mod_cast hterm
    have hθ : θ ≤ ε / C := by
      dsimp [θ, seq]
      have hden : C ≤ ((q : ℝ) + 1) * C := by
        nlinarith [show 0 ≤ (q : ℝ) by positivity]
      exact div_le_div_of_nonneg_left hε.le hC hden
    have hnonneg : 0 ≤ θ * (a.1 : ℝ) * (base : ℝ) ^ l.1 := by positivity
    rw [show A l a - b l a = θ * (a.1 : ℝ) * (base : ℝ) ^ l.1 by simp [A]]
    rw [abs_of_nonneg hnonneg]
    calc
      θ * (a.1 : ℝ) * (base : ℝ) ^ l.1 ≤
          (ε / C) * ((a.1 : ℝ) * (base : ℝ) ^ l.1) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_right hθ (by positivity)
      _ ≤ (ε / C) * (C - 1) :=
        mul_le_mul_of_nonneg_left hdigit (by positivity)
      _ < ε := by
        have : 0 < ε / C := by positivity
        calc
          ε / C * (C - 1) < ε / C * C := by gcongr; linarith
          _ = ε := by field_simp
  · intro a c hac
    by_contra hne
    have hcodes : code a ≠ code c := fun h ↦ hne (hcode h)
    have htheta : θ = (bsum c - bsum a) / (code a - code c) := by
      have hsum : bsum a + θ * code a = bsum c + θ * code c := by
        have hsuma : ∑ l, A l (a l) = bsum a + θ * code a := by
          simp only [A, Finset.sum_add_distrib]
          simp_rw [mul_assoc]
          rw [← Finset.mul_sum]
          simp [bsum, code, digitCode, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow]
        have hsumc : ∑ l, A l (c l) = bsum c + θ * code c := by
          simp only [A, Finset.sum_add_distrib]
          simp_rw [mul_assoc]
          rw [← Finset.mul_sum]
          simp [bsum, code, digitCode, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow]
        rw [← hsuma, ← hsumc]
        exact hac
      apply (eq_div_iff (sub_ne_zero.mpr hcodes)).2
      linarith
    apply hq
    refine ⟨(a, c), hne, ?_⟩
    simpa [θ] using htheta.symm

def gridScale (q m : ℕ) : ℝ := (((q - 1) * m : ℕ) : ℝ)

def gridMark (q m : ℕ) (j : Fin (q + 1)) (k : Fin m) : ℝ :=
  (finProdFinEquiv (j, k)).1 - m

def InGridGap (q m : ℕ) (j : Fin (q + 1)) (k : Fin m)
    (t : UnitInterval) : Prop :=
  |gridScale q m * t.1 - gridMark q m j k| < 1 / 3

def InGridTown (q m : ℕ) (k : Fin m) (a : Fin q)
    (t : UnitInterval) : Prop :=
  gridMark q m a.castSucc k + 1 / 3 ≤ gridScale q m * t.1 ∧
    gridScale q m * t.1 ≤ gridMark q m a.succ k - 1 / 3

lemma gridMark_formula (q m : ℕ) (j : Fin (q + 1)) (k : Fin m) :
    gridMark q m j k = (k.1 : ℝ) + m * j.1 - m := by
  simp [gridMark, finProdFinEquiv]

lemma gridMark_succ (q m : ℕ) (a : Fin q) (k : Fin m) :
    gridMark q m a.succ k = gridMark q m a.castSucc k + m := by
  simp [gridMark_formula]
  ring

lemma inGridGap_unique (q m : ℕ) {j₁ j₂ : Fin (q + 1)} {k₁ k₂ : Fin m}
    {t : UnitInterval} (h₁ : InGridGap q m j₁ k₁ t)
    (h₂ : InGridGap q m j₂ k₂ t) : j₁ = j₂ ∧ k₁ = k₂ := by
  have hpairs : (j₁, k₁) = (j₂, k₂) := by
    apply finProdFinEquiv.injective
    apply Fin.ext
    by_contra hne
    have horder : (finProdFinEquiv (j₁, k₁)).1 <
          (finProdFinEquiv (j₂, k₂)).1 ∨
        (finProdFinEquiv (j₂, k₂)).1 <
          (finProdFinEquiv (j₁, k₁)).1 :=
      Nat.lt_or_gt_of_ne hne
    rw [InGridGap, abs_lt] at h₁ h₂
    rcases horder with horder | horder
    · have hc : ((finProdFinEquiv (j₁, k₁)).1 : ℝ) + 1 ≤
          (finProdFinEquiv (j₂, k₂)).1 := by exact_mod_cast horder
      dsimp [gridMark] at h₁ h₂
      linarith
    · have hc : ((finProdFinEquiv (j₂, k₂)).1 : ℝ) + 1 ≤
          (finProdFinEquiv (j₁, k₁)).1 := by exact_mod_cast horder
      dsimp [gridMark] at h₁ h₂
      linarith
  exact ⟨congrArg Prod.fst hpairs, congrArg Prod.snd hpairs⟩

lemma interval_gap_cover_nat (r : ℕ) (c step y : ℝ)
    (hlo : c + 1 / 3 ≤ y)
    (hhi : y ≤ c + (r + 1) * step - 1 / 3)
    (hgap : ∀ j : ℕ, j ≤ r + 1 →
      ¬ |y - (c + j * step)| < 1 / 3) :
    ∃ a : ℕ, a ≤ r ∧ c + a * step + 1 / 3 ≤ y ∧
      y ≤ c + (a + 1) * step - 1 / 3 := by
  induction r generalizing c y with
  | zero =>
      exact ⟨0, le_rfl, by simpa using hlo, by norm_num at hhi ⊢; simpa using hhi⟩
  | succ r ih =>
      by_cases hfirst : y ≤ c + step - 1 / 3
      · exact ⟨0, Nat.zero_le _, by simpa using hlo, by simpa using hfirst⟩
      · have hnext : c + step + 1 / 3 ≤ y := by
          by_contra hlt
          have habs : |y - (c + step)| < 1 / 3 := by
            rw [abs_lt]
            constructor <;> linarith
          apply hgap 1 (by omega)
          simpa using habs
        have hhi' : c + step + (r + 1) * step - 1 / 3 ≥ y := by
          convert hhi using 1
          all_goals
            push_cast
            ring_nf
        have hgap' : ∀ j : ℕ, j ≤ r + 1 →
            ¬ |y - (c + step + j * step)| < 1 / 3 := by
          intro j hj
          convert hgap (j + 1) (by omega) using 1
          all_goals
            push_cast
            ring_nf
        obtain ⟨a, ha, hal, hau⟩ := ih (c + step) y hnext hhi' hgap'
        refine ⟨a + 1, by omega, ?_, ?_⟩
        · convert hal using 1
          all_goals
            push_cast
            ring_nf
        · convert hau using 1
          all_goals
            push_cast
            ring_nf

lemma exists_gridTown_or_gap (q m : ℕ) (hq : 1 ≤ q) (k : Fin m)
    (t : UnitInterval) :
    (∃ a : Fin q, InGridTown q m k a t) ∨
      ∃ j : Fin (q + 1), InGridGap q m j k t := by
  by_cases hgap : ∃ j : Fin (q + 1), InGridGap q m j k t
  · exact Or.inr hgap
  · left
    have hnogap (j : ℕ) (hj : j ≤ q) :
        ¬ |gridScale q m * t.1 - ((k.1 : ℝ) - m + j * m)| < 1 / 3 := by
      have hj' : j < q + 1 := by omega
      have := not_exists.mp hgap ⟨j, hj'⟩
      intro hjgap
      apply this
      rw [InGridGap]
      rw [gridMark_formula]
      convert hjgap using 1
      all_goals ring_nf
    have hlo : (k.1 : ℝ) - m + 1 / 3 ≤ gridScale q m * t.1 := by
      have hk : (k.1 : ℝ) + 1 ≤ m := by exact_mod_cast k.2
      have ht : 0 ≤ gridScale q m * t.1 :=
        mul_nonneg (by
          change 0 ≤ (((q - 1) * m : ℕ) : ℝ)
          positivity) t.2.1
      linarith
    have hhi : gridScale q m * t.1 ≤
        (k.1 : ℝ) - m + q * m - 1 / 3 := by
      have ht : t.1 ≤ 1 := t.2.2
      have hk : (k.1 : ℝ) ≥ 0 := by positivity
      have hm : 0 < m := Nat.pos_of_ne_zero fun hm ↦ Fin.elim0 (hm ▸ k)
      have hscale : gridScale q m = ((q : ℝ) - 1) * m := by
        simp [gridScale, Nat.cast_sub hq]
      have hscale_nonneg : 0 ≤ gridScale q m := by
        change 0 ≤ (((q - 1) * m : ℕ) : ℝ)
        positivity
      have hcenter : gridScale q m * t.1 ≤
          (k.1 : ℝ) - m + q * m := by
        rw [hscale]
        nlinarith
      by_contra hnot
      apply hnogap q le_rfl
      rw [abs_lt]
      constructor <;> linarith
    have hqsub : ((q - 1 : ℕ) : ℝ) + 1 = q := by
      exact_mod_cast Nat.sub_add_cancel hq
    obtain ⟨a, ha, hal, hau⟩ :=
      interval_gap_cover_nat (q - 1) ((k.1 : ℝ) - m) m
        (gridScale q m * t.1) hlo (by
          rw [show (((q - 1 : ℕ) : ℝ) + 1) = q from hqsub]
          exact hhi) (by
            intro j hj
            apply hnogap j
            omega)
    have ha' : a < q := by
      have : a ≤ q - 1 := ha
      omega
    refine ⟨⟨a, ha'⟩, ?_⟩
    simp only [InGridTown, gridMark_formula, Fin.val_castSucc, Fin.val_succ]
    constructor
    · convert hal using 1
      all_goals ring_nf
    · convert hau using 1
      all_goals
        push_cast
        ring_nf

def townMidpoint (q m : ℕ) (k : Fin m) (a : Fin q) : ℝ :=
  (gridMark q m a.castSucc k + gridMark q m a.succ k) / 2

def townSample (q m : ℕ) (hq : 1 < q) (hm : 0 < m)
    (k : Fin m) (a : Fin q) : UnitInterval := by
  let D := gridScale q m
  let y := max 0 (min D (townMidpoint q m k a))
  have hD : 0 < D := by
    dsimp [D, gridScale]
    exact_mod_cast Nat.mul_pos (Nat.sub_pos_of_lt hq) hm
  have hy0 : 0 ≤ y := le_max_left _ _
  have hyD : y ≤ D := by
    dsimp [y]
    rw [max_le_iff]
    exact ⟨hD.le, min_le_left _ _⟩
  exact ⟨y / D, (div_nonneg hy0 hD.le), (div_le_one hD).2 hyD⟩

lemma townSample_mem_of_mem (q m : ℕ) (hq : 1 < q) (hm : 0 < m)
    (k : Fin m) (a : Fin q) {t : UnitInterval} (ht : InGridTown q m k a t) :
    InGridTown q m k a (townSample q m hq hm k a) := by
  let D := gridScale q m
  let lo := gridMark q m a.castSucc k + 1 / 3
  let hi := gridMark q m a.succ k - 1 / 3
  let mid := townMidpoint q m k a
  have hD : 0 < D := by
    dsimp [D, gridScale]
    exact_mod_cast Nat.mul_pos (Nat.sub_pos_of_lt hq) hm
  have hlohi : lo ≤ hi := by
    dsimp [lo, hi]
    rw [gridMark_succ]
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hlomid : lo ≤ mid := by
    dsimp [lo, mid, townMidpoint]
    rw [gridMark_succ]
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hmidhi : mid ≤ hi := by
    dsimp [hi, mid, townMidpoint]
    rw [gridMark_succ]
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hloD : lo ≤ D := by
    calc
      lo ≤ D * t.1 := ht.1
      _ ≤ D * 1 := mul_le_mul_of_nonneg_left t.2.2 hD.le
      _ = D := mul_one D
  have hzeroHi : 0 ≤ hi := (mul_nonneg hD.le t.2.1).trans ht.2
  have hylo : lo ≤ max 0 (min D mid) := by
    apply le_max_of_le_right
    exact le_min hloD hlomid
  have hyhi : max 0 (min D mid) ≤ hi := by
    rw [max_le_iff]
    exact ⟨hzeroHi, (min_le_right D mid).trans hmidhi⟩
  change lo ≤ D * (max 0 (min D mid) / D) ∧
    D * (max 0 (min D mid) / D) ≤ hi
  rw [mul_div_cancel₀ _ hD.ne']
  exact ⟨hylo, hyhi⟩

lemma dist_townSample_lt (q m : ℕ) (hq : 1 < q) (hm : 0 < m)
    (k : Fin m) (a : Fin q) {t : UnitInterval} (ht : InGridTown q m k a t) :
    dist t (townSample q m hq hm k a) < 1 / (q - 1 : ℝ) := by
  have hs := townSample_mem_of_mem q m hq hm k a ht
  have hD : 0 < gridScale q m := by
    simp only [gridScale]
    exact_mod_cast Nat.mul_pos (Nat.sub_pos_of_lt hq) hm
  have hmark := gridMark_succ q m a k
  have hwidth : gridScale q m * |t.1 - (townSample q m hq hm k a).1| < m := by
    have habs : |gridScale q m *
        (t.1 - (townSample q m hq hm k a).1)| < m := by
      rw [abs_lt]
      constructor
      · nlinarith [ht.1, hs.2, hmark, show (2 / 3 : ℝ) < m by
          have : (1 : ℝ) ≤ m := by exact_mod_cast hm
          linarith]
      · nlinarith [hs.1, ht.2, hmark, show (2 / 3 : ℝ) < m by
          have : (1 : ℝ) ≤ m := by exact_mod_cast hm
          linarith]
    rw [abs_mul, abs_of_pos hD] at habs
    exact habs
  have hqm : gridScale q m = (q - 1 : ℝ) * m := by
    simp [gridScale, Nat.cast_sub hq.le]
  have hqpos : 0 < (q - 1 : ℝ) := sub_pos.mpr (by exact_mod_cast hq)
  have habs : |t.1 - (townSample q m hq hm k a).1| < 1 / (q - 1 : ℝ) := by
    rw [hqm] at hwidth
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    have hrewrite : ((q - 1 : ℝ) * m) *
        |t.1 - (townSample q m hq hm k a).1| =
        m * ((q - 1 : ℝ) * |t.1 - (townSample q m hq hm k a).1|) := by ring
    rw [hrewrite] at hwidth
    have hcancel : (q - 1 : ℝ) *
        |t.1 - (townSample q m hq hm k a).1| < 1 := by
      nlinarith [hwidth]
    exact (lt_div_iff₀ hqpos).2 (by simpa [mul_comm] using hcancel)
  change |t.1 - (townSample q m hq hm k a).1| < 1 / (q - 1 : ℝ)
  exact habs

lemma inGridTown_index_unique (q m : ℕ) (hm : 0 < m) (k : Fin m)
    {a b : Fin q} {t : UnitInterval} (ha : InGridTown q m k a t)
    (hb : InGridTown q m k b t) : a = b := by
  apply Fin.ext
  by_contra hne
  have hor : a.1 < b.1 ∨ b.1 < a.1 := Nat.lt_or_gt_of_ne hne
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  simp only [InGridTown, gridMark_formula, Fin.val_castSucc, Fin.val_succ] at ha hb
  rcases hor with hab | hba
  · have habR : (a.1 : ℝ) + 1 ≤ b.1 := by exact_mod_cast hab
    have hmul : (m : ℝ) * ((a.1 : ℝ) + 1) ≤ m * b.1 :=
      mul_le_mul_of_nonneg_left habR (by positivity)
    norm_num at ha hb
    nlinarith [ha.2, hb.1, hmul]
  · have hbaR : (b.1 : ℝ) + 1 ≤ a.1 := by exact_mod_cast hba
    have hmul : (m : ℝ) * ((b.1 : ℝ) + 1) ≤ m * a.1 :=
      mul_le_mul_of_nonneg_left hbaR (by positivity)
    norm_num at ha hb
    nlinarith [hb.2, ha.1, hmul]

def GridTown (q m : ℕ) (k : Fin m) (a : Fin q) : Set UnitInterval :=
  {t | InGridTown q m k a t}

lemma isClosed_gridTown (q m : ℕ) (k : Fin m) (a : Fin q) :
    IsClosed (GridTown q m k a) := by
  let scaled : UnitInterval → ℝ := fun t ↦ gridScale q m * t.1
  have hscaled : Continuous scaled := continuous_const.mul continuous_subtype_val
  exact (isClosed_le continuous_const hscaled).inter (isClosed_le hscaled continuous_const)

abbrev TownDomain (q m : ℕ) (k : Fin m) :=
  Σ a : Fin q, GridTown q m k a

def townEmbedding (q m : ℕ) (k : Fin m) : TownDomain q m k → UnitInterval :=
  fun p ↦ p.2.1

lemma townEmbedding_continuous (q m : ℕ) (k : Fin m) :
    Continuous (townEmbedding q m k) := by
  apply continuous_sigma
  intro a
  exact continuous_subtype_val

lemma townEmbedding_injective (q m : ℕ) (hm : 0 < m) (k : Fin m) :
    Function.Injective (townEmbedding q m k) := by
  rintro ⟨a, ta⟩ ⟨b, tb⟩ hab
  have ht : ta.1 = tb.1 := hab
  have habidx : a = b := by
    apply inGridTown_index_unique q m hm k ta.2
    have htb : InGridTown q m k b tb.1 := tb.2
    rw [← ht] at htb
    exact htb
  subst b
  have htab : ta = tb := Subtype.ext ht
  subst tb
  rfl

lemma exists_plateau_extension (q m d : ℕ) (hm : 0 < m)
    (k : Fin m) (p : Fin d → UnitInterval →ᵇ ℝ)
    (A : Fin d → Fin q → ℝ) {e : ℝ} (he : 0 ≤ e)
    (hclose : ∀ l a t, InGridTown q m k a t → |A l a - p l t| ≤ e) :
    ∃ p' : Fin d → UnitInterval →ᵇ ℝ,
      (∀ l, ‖p' l - p l‖ ≤ e) ∧
      ∀ l a t, InGridTown q m k a t → p' l t = A l a := by
  classical
  letI : CompactSpace UnitInterval := isCompact_iff_compactSpace.mp isCompact_Icc
  letI (a : Fin q) : CompactSpace (GridTown q m k a) :=
    isCompact_iff_compactSpace.mp (isClosed_gridTown q m k a).isCompact
  have hemb : IsClosedEmbedding (townEmbedding q m k) :=
    (townEmbedding_continuous q m k).isClosedEmbedding
      (townEmbedding_injective q m hm k)
  have hone (l : Fin d) : ∃ E : UnitInterval →ᵇ ℝ,
      ‖E‖ ≤ e ∧ ∀ a t, InGridTown q m k a t →
        E t = A l a - p l t := by
    let h : TownDomain q m k → ℝ := fun z ↦ A l z.1 - p l z.2.1
    have hh : Continuous h := by
      apply continuous_sigma
      intro a
      dsimp [h]
      exact continuous_const.sub ((p l).continuous.comp continuous_subtype_val)
    let hb : TownDomain q m k →ᵇ ℝ :=
      BoundedContinuousFunction.mkOfCompact ⟨h, hh⟩
    have hbnorm : ‖hb‖ ≤ e := by
      apply (BoundedContinuousFunction.norm_le he).2
      rintro ⟨a, t⟩
      simpa [hb, h, Real.norm_eq_abs] using hclose l a t.1 t.2
    obtain ⟨E, _hEnorm, hE⟩ :=
      BoundedContinuousFunction.exists_extension_norm_eq_of_isClosedEmbedding hb hemb
    refine ⟨E, _hEnorm.le.trans hbnorm, ?_⟩
    intro a t ht
    have hval := congr_fun hE (Sigma.mk a ⟨t, ht⟩)
    simpa [townEmbedding, hb, h] using hval
  choose E hEnorm hE using hone
  let p' : Fin d → UnitInterval →ᵇ ℝ := fun l ↦ p l + E l
  refine ⟨p', ?_, ?_⟩
  · intro l
    simpa [p'] using hEnorm l
  · intro l a t ht
    have := hE l a t ht
    simp [p', this]

def cellSample (q m n : ℕ) (hq : 1 < q) (hm : 0 < m)
    (k : Fin m) (a : Fin n → Fin q) : Cube n :=
  ⟨fun l ↦ (townSample q m hq hm k (a l)).1,
    ⟨fun l ↦ (townSample q m hq hm k (a l)).2.1,
      fun l ↦ (townSample q m hq hm k (a l)).2.2⟩⟩

lemma exists_outer_correction (q m n : ℕ) (hq : 1 < q) (hm : 0 < m)
    (k : Fin m) (A : Fin n → Fin q → ℝ)
    (hA : Function.Injective (fun a : Fin n → Fin q ↦ ∑ l, A l (a l)))
    (R : Cube n →ᵇ ℝ) :
    ∃ G : ℝ →ᵇ ℝ, ‖G‖ ≤ ‖R‖ / (m : ℝ) ∧
      ∀ a : Fin n → Fin q,
        G (∑ l, A l (a l)) = R (cellSample q m n hq hm k a) / (m : ℝ) := by
  classical
  let T := Fin n → Fin q
  let code : T → ℝ := fun a ↦ ∑ l, A l (a l)
  have hcode : Function.Injective code := hA
  have hc : Continuous code := continuous_of_discreteTopology
  have hclosed : IsClosedEmbedding code := hc.isClosedEmbedding hcode
  let h : T → ℝ := fun a ↦ R (cellSample q m n hq hm k a) / (m : ℝ)
  have hh : Continuous h := continuous_of_discreteTopology
  let hb : T →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact ⟨h, hh⟩
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hbnorm : ‖hb‖ ≤ ‖R‖ / (m : ℝ) := by
    apply (BoundedContinuousFunction.norm_le (div_nonneg (norm_nonneg _) hmR.le)).2
    intro a
    change ‖R (cellSample q m n hq hm k a) / (m : ℝ)‖ ≤ ‖R‖ / (m : ℝ)
    rw [norm_div]
    simp only [Real.norm_eq_abs, abs_of_pos hmR]
    exact div_le_div_of_nonneg_right (R.norm_coe_le_norm _) hmR.le
  obtain ⟨G, _hGnorm, hG⟩ :=
    BoundedContinuousFunction.exists_extension_norm_eq_of_isClosedEmbedding hb hclosed
  refine ⟨G, _hGnorm.le.trans hbnorm, ?_⟩
  intro a
  have hval := congr_fun hG a
  simpa [code, hb, h] using hval

def LayerHasTown (q n : ℕ) (x : Cube n) (k : Fin (2 * n + 1)) : Prop :=
  ∃ a : Fin n → Fin q, ∀ l,
    InGridTown q (2 * n + 1) k (a l) (cubeCoord x l)

noncomputable def badLayers (q n : ℕ) (x : Cube n) : Finset (Fin (2 * n + 1)) := by
  classical
  exact Finset.univ.filter fun k ↦ ¬ LayerHasTown q n x k

lemma badLayers_card_le (q n : ℕ) (hq : 1 ≤ q) (x : Cube n) :
    (badLayers q n x).card ≤ n := by
  classical
  have hwitness (k : {k // k ∈ badLayers q n x}) : ∃ l : Fin n, ∃ j : Fin (q + 1),
      InGridGap q (2 * n + 1) j k.1 (cubeCoord x l) := by
    have hk : ¬ LayerHasTown q n x k.1 := by
      have hk := k.2
      simp only [badLayers, Finset.mem_filter, Finset.mem_univ, true_and] at hk
      exact hk
    have hcoord : ∃ l : Fin n, ∀ a : Fin q,
        ¬ InGridTown q (2 * n + 1) k.1 a (cubeCoord x l) := by
      by_contra h
      push Not at h
      choose a ha using h
      exact hk ⟨a, ha⟩
    obtain ⟨l, hl⟩ := hcoord
    rcases exists_gridTown_or_gap q (2 * n + 1) hq k.1 (cubeCoord x l) with ht | hg
    · obtain ⟨a, ha⟩ := ht
      exact (hl a ha).elim
    · exact ⟨l, hg⟩
  choose coord gap hgap using hwitness
  have hcoord_inj : Function.Injective coord := by
    intro a b hab
    have hb : InGridGap q (2 * n + 1) (gap b) b.1 (cubeCoord x (coord a)) := by
      simpa [hab] using hgap b
    have hk := (inGridGap_unique q (2 * n + 1) (hgap a) hb).2
    exact Subtype.ext hk
  have hcard := Fintype.card_le_of_injective coord hcoord_inj
  rw [← Fintype.card_coe (badLayers q n x)]
  simpa using hcard

structure ApproximationStepResult (n : ℕ) [CompactSpace (Cube n)]
    (p : InnerFamily n) (H : OuterFamily n) (R : Cube n →ᵇ ℝ) (eta : ℝ) where
  nextInner : InnerFamily n
  correction : OuterFamily n
  inner_dist : dist nextInner p ≤ eta
  old_outer_change :
    ‖superpose nextInner H - superpose p H‖ ≤ stabilityRate n * ‖R‖
  correction_norm : ∀ k, ‖correction k‖ ≤ ‖R‖ / layerCountR n
  approximation :
    ‖R - superpose nextInner correction‖ ≤ approximationRate n * ‖R‖

theorem approximationStep_exists (n : ℕ) (hn : 1 ≤ n) [CompactSpace (Cube n)]
    (p : InnerFamily n) (H : OuterFamily n) (R : Cube n →ᵇ ℝ)
    (eta : ℝ) (heta : 0 < eta) :
    Nonempty (ApproximationStepResult n p H R eta) := by
  classical
  by_cases hRzero : ‖R‖ = 0
  · have hR : R = 0 := norm_eq_zero.mp hRzero
    refine ⟨{
      nextInner := p
      correction := 0
      inner_dist := by simp [heta.le]
      old_outer_change := by simp [hRzero]
      correction_norm := by intro k; simp [hRzero]
      approximation := by simp [hR, superpose_zero]
    }⟩
  · have hRpos : 0 < ‖R‖ := lt_of_le_of_ne (norm_nonneg R) (Ne.symm hRzero)
    have hstable : 0 < stabilityRate n * ‖R‖ := by
      apply mul_pos
      · dsimp [stabilityRate]
        exact one_div_pos.mpr (mul_pos (by norm_num) (layerCountR_pos n))
      · exact hRpos
    obtain ⟨dH, hdH, hHmod⟩ := Metric.continuousAt_iff.mp
      (continuous_superpose_inner H).continuousAt _ hstable
    let rho : ℝ := min eta dH / 2
    have hrho : 0 < rho := by
      dsimp [rho]
      positivity
    have hrho_eta : rho < eta := by
      dsimp [rho]
      have := min_le_left eta dH
      nlinarith
    have hrho_H : rho < dH := by
      dsimp [rho]
      have := min_le_right eta dH
      nlinarith
    obtain ⟨dp, hdp, hpmod⟩ := exists_inner_modulus n p (show 0 < rho / 2 by positivity)
    have heR : 0 < ‖R‖ / (4 * layerCountR n) := by
      have := layerCountR_pos n
      positivity
    obtain ⟨dR, hdR, hRmod⟩ := Metric.uniformContinuous_iff.mp
      (CompactSpace.uniformContinuous_of_continuous R.continuous) _ heR
    let dx := min dp dR
    have hdx : 0 < dx := by dsimp [dx]; positivity
    obtain ⟨Q : ℕ, hQ⟩ := exists_nat_gt (1 / dx)
    let q : ℕ := Q + 2
    have hq : 1 < q := by dsimp [q]; omega
    have hqpos : 0 < q := by omega
    have hden : 0 < (q - 1 : ℝ) := sub_pos.mpr (by exact_mod_cast hq)
    have hlarge : 1 / dx < (q - 1 : ℝ) := by
      dsimp [q]
      push_cast
      linarith
    have hfrac : 1 / (q - 1 : ℝ) < dx := by
      apply (div_lt_iff₀ hden).2
      have hmul := (div_lt_iff₀ hdx).mp hlarge
      nlinarith
    have hAexists (k : Fin (2 * n + 1)) :
        ∃ A : Fin n → Fin q → ℝ,
          (∀ l a, |A l a - p k l (townSample q (2 * n + 1) hq (by omega) k a)| < rho / 2) ∧
          Function.Injective (fun a : Fin n → Fin q ↦ ∑ l, A l (a l)) :=
      exists_separating_perturbation q n hqpos
        (fun l a ↦ p k l (townSample q (2 * n + 1) hq (by omega) k a))
        (by positivity)
    choose A hAclose hAinj using hAexists
    have htownclose (k : Fin (2 * n + 1)) (l : Fin n) (a : Fin q)
        (t : UnitInterval) (ht : InGridTown q (2 * n + 1) k a t) :
        |A k l a - p k l t| ≤ rho := by
      have hdist : dist t (townSample q (2 * n + 1) hq (by omega) k a) < dp :=
        lt_of_lt_of_le (dist_townSample_lt q (2 * n + 1) hq (by omega) k a ht)
          (le_trans hfrac.le (min_le_left dp dR))
      have hpclose := hpmod k l t
        (townSample q (2 * n + 1) hq (by omega) k a) hdist
      apply le_of_lt
      calc
        |A k l a - p k l t| ≤
            |A k l a - p k l (townSample q (2 * n + 1) hq (by omega) k a)| +
              |p k l (townSample q (2 * n + 1) hq (by omega) k a) - p k l t| :=
          abs_sub_le _ _ _
        _ < rho / 2 + rho / 2 := by
          apply add_lt_add (hAclose k l a)
          simpa [Real.dist_eq, abs_sub_comm] using hpclose
        _ = rho := by ring
    have hplateau (k : Fin (2 * n + 1)) :
        ∃ p' : Fin n → UnitInterval →ᵇ ℝ,
          (∀ l, ‖p' l - p k l‖ ≤ rho) ∧
          ∀ l a t, InGridTown q (2 * n + 1) k a t → p' l t = A k l a :=
      exists_plateau_extension q (2 * n + 1) n (by omega) k (p k) (A k)
        hrho.le (htownclose k)
    choose next hnextNorm hnextTown using hplateau
    let nextInner : InnerFamily n := fun k l ↦ next k l
    have hcorr (k : Fin (2 * n + 1)) :
        ∃ G : ℝ →ᵇ ℝ, ‖G‖ ≤ ‖R‖ / layerCountR n ∧
          ∀ a : Fin n → Fin q,
            G (∑ l, A k l (a l)) =
              R (cellSample q (2 * n + 1) n hq (by omega) k a) /
                layerCountR n := by
      simpa [layerCountR] using
        (exists_outer_correction q (2 * n + 1) n hq (by omega) k (A k) (hAinj k) R)
    choose correction hcorrNorm hcorrVal using hcorr
    have hnextDist : dist nextInner p ≤ rho := by
      rw [dist_eq_norm]
      apply (pi_norm_le_iff_of_nonneg hrho.le).2
      intro k
      apply (pi_norm_le_iff_of_nonneg hrho.le).2
      intro l
      exact hnextNorm k l
    refine ⟨{
      nextInner := nextInner
      correction := correction
      inner_dist := hnextDist.trans (le_of_lt hrho_eta)
      old_outer_change := ?_
      correction_norm := ?_
      approximation := ?_
    }⟩
    · have hout := hHmod (lt_of_le_of_lt hnextDist hrho_H)
      exact (by simpa [dist_eq_norm] using hout.le)
    · intro k
      simpa [layerCountR] using hcorrNorm k
    · apply (BoundedContinuousFunction.norm_le
          (mul_nonneg (approximationRate_nonneg n hn) (norm_nonneg R))).2
      intro x
      let goodError : ℝ := ‖R‖ / (4 * (layerCountR n) ^ 2)
      let badError : ℝ := 2 * ‖R‖ / layerCountR n
      have hmR : 0 < layerCountR n := layerCountR_pos n
      have hbad (k : Fin (2 * n + 1)) :
          ‖R x / layerCountR n - correction k (innerSum nextInner k x)‖ ≤ badError := by
        calc
          ‖R x / layerCountR n - correction k (innerSum nextInner k x)‖ ≤
              ‖R x / layerCountR n‖ + ‖correction k (innerSum nextInner k x)‖ :=
            norm_sub_le _ _
          _ ≤ ‖R‖ / layerCountR n + ‖R‖ / layerCountR n := by
            apply add_le_add
            · rw [norm_div]
              simp only [Real.norm_eq_abs, abs_of_pos hmR]
              exact div_le_div_of_nonneg_right (R.norm_coe_le_norm x) hmR.le
            · exact (correction k).norm_coe_le_norm _ |>.trans (by
                simpa [layerCountR] using hcorrNorm k)
          _ = badError := by dsimp [badError]; ring
      have hgood (k : Fin (2 * n + 1)) (hk : k ∉ badLayers q n x) :
          ‖R x / layerCountR n - correction k (innerSum nextInner k x)‖ ≤ goodError := by
        have hkTown : LayerHasTown q n x k := by
          simpa [badLayers] using hk
        obtain ⟨a, ha⟩ := hkTown
        have hinner : innerSum nextInner k x = ∑ l, A k l (a l) := by
          rw [innerSum_apply]
          apply Finset.sum_congr rfl
          intro l _
          exact hnextTown k l (a l) (cubeCoord x l) (ha l)
        have hcell : dist (cellSample q (2 * n + 1) n hq (by omega) k a) x < dR := by
          change ‖(cellSample q (2 * n + 1) n hq (by omega) k a).1 - x.1‖ < dR
          apply (pi_norm_lt_iff hdR).2
          intro l
          have hl := dist_townSample_lt q (2 * n + 1) hq (by omega) k (a l) (ha l)
          have hl' : dist (townSample q (2 * n + 1) hq (by omega) k (a l))
              (cubeCoord x l) < dR :=
            lt_of_lt_of_le (by simpa [dist_comm] using hl)
              (le_trans hfrac.le (min_le_right dp dR))
          change |(townSample q (2 * n + 1) hq (by omega) k (a l)).1 - x.1 l| < dR
          change |(townSample q (2 * n + 1) hq (by omega) k (a l)).1 - x.1 l| < dR at hl'
          exact hl'
        have hRclose := hRmod hcell
        rw [hinner, hcorrVal k a]
        have hdiff : |R x - R (cellSample q (2 * n + 1) n hq (by omega) k a)| <
            ‖R‖ / (4 * layerCountR n) := by
          simpa [Real.dist_eq, abs_sub_comm] using hRclose
        have hquot :
            ‖R x / layerCountR n -
                R (cellSample q (2 * n + 1) n hq (by omega) k a) /
                  layerCountR n‖ < goodError := by
          rw [← sub_div, norm_div]
          simp only [Real.norm_eq_abs, abs_of_pos hmR]
          calc
            |R x - R (cellSample q (2 * n + 1) n hq (by omega) k a)| /
                layerCountR n < (‖R‖ / (4 * layerCountR n)) / layerCountR n :=
              div_lt_div_of_pos_right hdiff hmR
            _ = goodError := by dsimp [goodError]; ring
        simpa [layerCountR] using hquot.le
      have hmean : R x = ∑ k : Fin (2 * n + 1), R x / layerCountR n := by
        simp [layerCountR, nsmul_eq_mul]
        field_simp
      have hpoint :
          ‖R x - superpose nextInner correction x‖ ≤
            (2 * n + 1 : ℝ) * goodError +
              (badLayers q n x).card * badError := by
        rw [superpose_apply, hmean, ← Finset.sum_sub_distrib]
        calc
          ‖∑ k, (R x / layerCountR n - correction k (innerSum nextInner k x))‖ ≤
              ∑ k, ‖R x / layerCountR n - correction k (innerSum nextInner k x)‖ :=
            norm_sum_le _ _
          _ ≤ ∑ k, (goodError + if k ∈ badLayers q n x then badError else 0) := by
            apply Finset.sum_le_sum
            intro k _
            by_cases hk : k ∈ badLayers q n x
            · simp only [hk, if_true]
              exact (hbad k).trans (le_add_of_nonneg_left (by dsimp [goodError]; positivity))
            · simp only [hk, if_false, add_zero]
              exact hgood k hk
          _ = (2 * n + 1 : ℝ) * goodError +
              (badLayers q n x).card * badError := by
            rw [Finset.sum_add_distrib]
            simp [nsmul_eq_mul]
      calc
        ‖R x - superpose nextInner correction x‖ ≤
            (2 * n + 1 : ℝ) * goodError +
              (badLayers q n x).card * badError := hpoint
        _ ≤ (2 * n + 1 : ℝ) * goodError + n * badError := by
          gcongr
          exact_mod_cast badLayers_card_le q n hq.le x
        _ = approximationRate n * ‖R‖ := by
          dsimp [goodError, badError, layerCountR, approximationRate]
          have hm : (0 : ℝ) < 2 * n + 1 := by positivity
          field_simp
          ring

/-- The analytic iteration needed by the superposition theorem.  Its geometric input is the
arbitrarily-small plateau perturbation supplied by `ApproximationStepResult`. -/
theorem exactSuperposition_of_approximationStep (n : ℕ) [CompactSpace (Cube n)]
    (F : Cube n →ᵇ ℝ)
    (hstep : ∀ (ψ : InnerFamily n) (H : OuterFamily n) (R : Cube n →ᵇ ℝ)
      (η : ℝ), 0 < η → Nonempty (ApproximationStepResult n ψ H R η)) :
    ∃ (ψ : InnerFamily n) (H : OuterFamily n), F = superpose ψ H := by
  classical
  let η (r : ℕ) : ℝ := (1 / 2 : ℝ) ^ r
  have hη (r : ℕ) : 0 < η r := by positivity
  let chooseStep (r : ℕ) (s : InnerFamily n × OuterFamily n) :
      ApproximationStepResult n s.1 s.2 (F - superpose s.1 s.2) (η r) :=
    Classical.choice (hstep s.1 s.2 (F - superpose s.1 s.2) (η r) (hη r))
  let next (r : ℕ) (s : InnerFamily n × OuterFamily n) :
      InnerFamily n × OuterFamily n :=
    let z := chooseStep r s
    (z.nextInner, s.2 + z.correction)
  let state : ℕ → InnerFamily n × OuterFamily n := fun r ↦
    Nat.rec (0, 0) (fun i s ↦ next i s) r
  let ψ (r : ℕ) := (state r).1
  let H (r : ℕ) := (state r).2
  let R (r : ℕ) : Cube n →ᵇ ℝ := F - superpose (ψ r) (H r)
  let z (r : ℕ) : ApproximationStepResult n (ψ r) (H r) (R r) (η r) :=
    chooseStep r (state r)
  have hstate_succ (r : ℕ) :
      state (r + 1) = ((z r).nextInner, H r + (z r).correction) := by
    rfl
  have hψ_succ (r : ℕ) : ψ (r + 1) = (z r).nextInner := by
    rw [show ψ (r + 1) = (state (r + 1)).1 from rfl, hstate_succ]
  have hH_succ (r : ℕ) : H (r + 1) = H r + (z r).correction := by
    rw [show H (r + 1) = (state (r + 1)).2 from rfl, hstate_succ]
  have hR_succ (r : ℕ) : ‖R (r + 1)‖ ≤ contractionRate n * ‖R r‖ := by
    have happ := (z r).approximation
    have hchange := (z r).old_outer_change
    have heq : R (r + 1) =
        (R r - superpose (z r).nextInner (z r).correction) +
          (superpose (ψ r) (H r) - superpose (z r).nextInner (H r)) := by
      dsimp [R]
      rw [hψ_succ, hH_succ, superpose_add]
      abel
    rw [heq]
    calc
      ‖(R r - superpose (z r).nextInner (z r).correction) +
          (superpose (ψ r) (H r) - superpose (z r).nextInner (H r))‖
          ≤ ‖R r - superpose (z r).nextInner (z r).correction‖ +
            ‖superpose (ψ r) (H r) - superpose (z r).nextInner (H r)‖ := norm_add_le _ _
      _ ≤ approximationRate n * ‖R r‖ + stabilityRate n * ‖R r‖ := by
        gcongr
        calc
          ‖superpose (ψ r) (H r) - superpose (z r).nextInner (H r)‖ =
              ‖superpose (z r).nextInner (H r) - superpose (ψ r) (H r)‖ := by
                rw [← norm_neg, neg_sub]
          _ ≤ stabilityRate n * ‖R r‖ := hchange
      _ = contractionRate n * ‖R r‖ := by
        rw [← stability_add_approximation]
        ring
  have hR_zero : R 0 = F := by
    dsimp [R, ψ, H, state]
    simp [superpose_zero]
  have hR_bound (r : ℕ) : ‖R r‖ ≤ (contractionRate n) ^ r * ‖F‖ := by
    induction r with
    | zero => simp [hR_zero]
    | succ r ihr =>
      calc
        ‖R (r + 1)‖ ≤ contractionRate n * ‖R r‖ := hR_succ r
        _ ≤ contractionRate n * ((contractionRate n) ^ r * ‖F‖) :=
          mul_le_mul_of_nonneg_left ihr (contractionRate_nonneg n)
        _ = (contractionRate n) ^ (r + 1) * ‖F‖ := by rw [pow_succ']; ring
  have hψ_dist (r : ℕ) : dist (ψ r) (ψ (r + 1)) ≤ (1 / 2 : ℝ) ^ r := by
    rw [hψ_succ, dist_comm]
    exact (z r).inner_dist
  have hψ_cauchy : CauchySeq ψ := by
    apply cauchySeq_of_le_geometric (1 / 2 : ℝ) 1
    · norm_num
    · intro r
      simpa using hψ_dist r
  let psiLim : InnerFamily n := limUnder atTop ψ
  have hψ_tendsto : Tendsto ψ atTop (𝓝 psiLim) := hψ_cauchy.tendsto_limUnder
  have hcorr_norm (r : ℕ) : ‖(z r).correction‖ ≤ ‖R r‖ / layerCountR n := by
    apply (pi_norm_le_iff_of_nonempty (z r).correction).2
    exact (z r).correction_norm
  have hH_dist (r : ℕ) :
      dist (H r) (H (r + 1)) ≤ (‖F‖ / layerCountR n) * (contractionRate n) ^ r := by
    have heq : H r - H (r + 1) = -(z r).correction := by
      rw [hH_succ]
      abel
    rw [dist_eq_norm, heq, norm_neg]
    calc
      ‖(z r).correction‖ ≤ ‖R r‖ / layerCountR n := hcorr_norm r
      _ ≤ ((contractionRate n) ^ r * ‖F‖) / layerCountR n :=
        div_le_div_of_nonneg_right (hR_bound r) (le_of_lt (layerCountR_pos n))
      _ = (‖F‖ / layerCountR n) * (contractionRate n) ^ r := by ring
  have hH_cauchy : CauchySeq H := by
    apply cauchySeq_of_le_geometric (contractionRate n) (‖F‖ / layerCountR n)
    · exact contractionRate_lt_one n
    · exact hH_dist
  let HLim : OuterFamily n := limUnder atTop H
  have hH_tendsto : Tendsto H atTop (𝓝 HLim) := hH_cauchy.tendsto_limUnder
  have hfixed_tendsto : Tendsto (fun r ↦ superpose (ψ r) HLim) atTop
      (𝓝 (superpose psiLim HLim)) :=
    (continuous_superpose_inner HLim).continuousAt.tendsto.comp hψ_tendsto
  have houter_dist_zero : Tendsto (fun r ↦
      dist (superpose (ψ r) HLim) (superpose (ψ r) (H r))) atTop (𝓝 0) := by
    have hbound (r : ℕ) :
        dist (superpose (ψ r) HLim) (superpose (ψ r) (H r)) ≤
          Fintype.card (Fin (2 * n + 1)) * ‖HLim - H r‖ := by
      rw [dist_eq_norm]
      calc
        ‖superpose (ψ r) HLim - superpose (ψ r) (H r)‖
            ≤ ∑ k, ‖HLim k - H r k‖ := norm_superpose_sub_le _ _ _
        _ ≤ Fintype.card (Fin (2 * n + 1)) • ‖HLim - H r‖ :=
          Pi.sum_norm_apply_le_norm (HLim - H r)
        _ = Fintype.card (Fin (2 * n + 1)) * ‖HLim - H r‖ := by
          simp [nsmul_eq_mul]
    have hsub : Tendsto (fun r ↦ HLim - H r) atTop (𝓝 (HLim - HLim)) :=
      tendsto_const_nhds.sub hH_tendsto
    apply squeeze_zero (fun r ↦ dist_nonneg) hbound
    have hcard : Tendsto
        (fun r : ℕ ↦ (Fintype.card (Fin (2 * n + 1)) : ℝ) * ‖HLim - H r‖)
        atTop (𝓝 ((Fintype.card (Fin (2 * n + 1)) : ℝ) * ‖HLim - HLim‖)) :=
      tendsto_const_nhds.mul hsub.norm
    simpa using hcard
  have hsuperpose_tendsto :
      Tendsto (fun r ↦ superpose (ψ r) (H r)) atTop (𝓝 (superpose psiLim HLim)) :=
    hfixed_tendsto.congr_dist houter_dist_zero
  have hR_tendsto_zero : Tendsto (fun r ↦ ‖R r‖) atTop (𝓝 0) := by
    apply squeeze_zero (fun r ↦ norm_nonneg (R r)) hR_bound
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (contractionRate_nonneg n)
        (contractionRate_lt_one n)).mul_const ‖F‖
  refine ⟨psiLim, HLim, ?_⟩
  have : Tendsto (fun r ↦ F - R r) atTop (𝓝 (F - 0)) := by
    exact tendsto_const_nhds.sub (tendsto_zero_iff_norm_tendsto_zero.mpr hR_tendsto_zero)
  have hF : Tendsto (fun r ↦ superpose (ψ r) (H r)) atTop (𝓝 F) := by
    simpa [R] using this
  exact tendsto_nhds_unique hF hsuperpose_tendsto

/-- A finite family of outer functions can be combined into one outer function by translating
the compact ranges on which they are used to pairwise disjoint intervals. -/
theorem combineOuterFunctions (n : ℕ) (hn : 1 ≤ n)
    (g : Fin (2 * n + 1) → ℝ → ℝ)
    (φ : Fin (2 * n + 1) → Fin n → ℝ → ℝ)
    (hg : ∀ k, Continuous (g k)) (hφ : ∀ k l, Continuous (φ k l)) :
    ∃ (G : ℝ → ℝ) (Φ : Fin (2 * n + 1) → Fin n → ℝ → ℝ),
      Continuous G ∧ (∀ k l, Continuous (Φ k l)) ∧
      ∀ x ∈ Set.Icc (0 : Fin n → ℝ) 1,
        (∑ k, g k (∑ l, φ k l (x l))) =
          ∑ k, G (∑ l, Φ k l (x l)) := by
  classical
  let m := 2 * n + 1
  let K : Set (Fin n → ℝ) := Set.Icc 0 1
  have hK : IsCompact K := isCompact_Icc
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let y (k : Fin m) (x : Fin n → ℝ) : ℝ := ∑ l, φ k l (x l)
  have hy (k : Fin m) : Continuous (y k) := by
    apply continuous_finsetSum
    intro l _
    exact (hφ k l).comp (continuous_apply l)
  let yc : C((Σ _k : Fin m, K), ℝ) :=
    ⟨fun p ↦ y p.1 p.2.1, by
      apply continuous_sigma
      intro k
      exact (hy k).comp continuous_subtype_val⟩
  let yb : (Σ _k : Fin m, K) →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact yc
  let B : ℝ := ‖yb‖ + 1
  have hB : 0 < B := by
    dsimp [B]
    positivity
  have hy_bound (k : Fin m) (x : K) : |y k x.1| < B := by
    have hle : |yb (Sigma.mk k x)| ≤ ‖yb‖ := by
      simpa only [Real.norm_eq_abs] using yb.norm_coe_le_norm (Sigma.mk k x)
    simpa [B, yb, yc] using lt_of_le_of_lt hle (lt_add_one ‖yb‖)
  let shift (k : Fin m) : ℝ := 3 * B * k.1
  let S (k : Fin m) : Set ℝ := y k '' K
  have hS (k : Fin m) : IsCompact (S k) := hK.image (hy k)
  letI (k : Fin m) : CompactSpace (S k) := isCompact_iff_compactSpace.mp (hS k)
  let D := Σ k, S k
  let e : D → ℝ := fun p ↦ p.2.1 + shift p.1
  have he_cont : Continuous e := by
    apply continuous_sigma
    intro k
    change Continuous (fun a : S k ↦ a.1 + shift k)
    exact continuous_subtype_val.add continuous_const
  have hS_bound (k : Fin m) (t : S k) : |t.1| < B := by
    rcases t.2 with ⟨x, hx, hxt⟩
    rw [← hxt]
    exact hy_bound k ⟨x, hx⟩
  have he_inj : Function.Injective e := by
    rintro ⟨kp, tp⟩ ⟨kq, tq⟩ hpq
    have hidx : kp = kq := by
      apply Fin.ext
      by_contra hne
      have hor : kp.1 < kq.1 ∨ kq.1 < kp.1 := Nat.lt_or_gt_of_ne hne
      rcases hor with hpqidx | hqpidx
      · have hcast : (kp.1 : ℝ) + 1 ≤ kq.1 := by exact_mod_cast hpqidx
        have hpabs := hS_bound kp tp
        have hqabs := hS_bound kq tq
        have hp_lo : -B < tp.1 := (abs_lt.mp hpabs).1
        have hp_hi : tp.1 < B := (abs_lt.mp hpabs).2
        have hq_lo : -B < tq.1 := (abs_lt.mp hqabs).1
        have hq_hi : tq.1 < B := (abs_lt.mp hqabs).2
        dsimp [e, shift] at hpq
        nlinarith
      · have hcast : (kq.1 : ℝ) + 1 ≤ kp.1 := by exact_mod_cast hqpidx
        have hpabs := hS_bound kp tp
        have hqabs := hS_bound kq tq
        have hp_lo : -B < tp.1 := (abs_lt.mp hpabs).1
        have hp_hi : tp.1 < B := (abs_lt.mp hpabs).2
        have hq_lo : -B < tq.1 := (abs_lt.mp hqabs).1
        have hq_hi : tq.1 < B := (abs_lt.mp hqabs).2
        dsimp [e, shift] at hpq
        nlinarith
    subst kq
    have ht : tp.1 = tq.1 := by
      dsimp [e] at hpq
      linarith
    have : tp = tq := Subtype.ext ht
    subst tq
    rfl
  have he : IsClosedEmbedding e := he_cont.isClosedEmbedding he_inj
  let h : D → ℝ := fun p ↦ g p.1 p.2.1
  have hh : Continuous h := by
    apply continuous_sigma
    intro k
    exact (hg k).comp continuous_subtype_val
  let hb : D →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact ⟨h, hh⟩
  obtain ⟨G, _hGnorm, hGe⟩ :=
    BoundedContinuousFunction.exists_extension_norm_eq_of_isClosedEmbedding hb (e := e) he
  let l0 : Fin n := ⟨0, hn⟩
  let Φ : Fin m → Fin n → ℝ → ℝ := fun k l t ↦
    φ k l t + if l = l0 then shift k else 0
  refine ⟨G, Φ, G.continuous, ?_, ?_⟩
  · intro k l
    exact (hφ k l).add continuous_const
  · intro x hx
    have hyS (k : Fin m) : y k x ∈ S k := ⟨x, hx, rfl⟩
    have hG (k : Fin m) : G (y k x + shift k) = g k (y k x) := by
      have heq := congr_fun hGe (Sigma.mk k ⟨y k x, hyS k⟩)
      change G (e (Sigma.mk k ⟨y k x, hyS k⟩)) =
        h (Sigma.mk k ⟨y k x, hyS k⟩) at heq
      simpa [e, h] using heq
    apply Finset.sum_congr rfl
    intro k _
    rw [← hG k]
    congr 1
    simp [Φ, y, Finset.sum_add_distrib, l0]

end

end Submission.Helpers
