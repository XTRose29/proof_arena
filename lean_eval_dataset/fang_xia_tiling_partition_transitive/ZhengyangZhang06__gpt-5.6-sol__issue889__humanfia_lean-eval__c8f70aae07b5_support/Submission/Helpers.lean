import ChallengeDeps

open LeanEval.Combinatorics.FangXiaTilingProblem
open scoped BigOperators

namespace Submission.Helpers

noncomputable section

local instance setFintype {α : Type*} [Fintype α] (S : Set α) : Fintype S :=
  Fintype.ofFinite _

noncomputable def propIndicator (p : Prop) : ℝ :=
  @ite ℝ p (Classical.propDecidable p) 1 0

abbrev LtPair (α : Type*) [LT α] := {p : α × α // p.1 < p.2}

abbrev NePair (α : Type*) := {p : α × α // p.1 ≠ p.2}

theorem swapOfLtPair_injective {α : Type*} [LinearOrder α] [Fintype α]
    [DecidableEq α] :
    Function.Injective (fun p : LtPair α => Equiv.swap p.val.1 p.val.2) := by
  intro p q h
  have hp := (Equiv.Perm.support_swap_iff p.val.1 p.val.2).2 p.property.ne
  have hq := (Equiv.Perm.support_swap_iff q.val.1 q.val.2).2 q.property.ne
  have hs : ({p.val.1, p.val.2} : Finset α) = {q.val.1, q.val.2} := by
    calc
      {p.val.1, p.val.2} = (Equiv.swap p.val.1 p.val.2).support := hp.symm
      _ = (Equiv.swap q.val.1 q.val.2).support := congrArg Equiv.Perm.support h
      _ = {q.val.1, q.val.2} := hq
  have hp1 : p.val.1 = q.val.1 ∨ p.val.1 = q.val.2 := by
    have : p.val.1 ∈ ({q.val.1, q.val.2} : Finset α) := by rw [← hs]; simp
    simpa [eq_comm] using this
  have hp2 : p.val.2 = q.val.1 ∨ p.val.2 = q.val.2 := by
    have : p.val.2 ∈ ({q.val.1, q.val.2} : Finset α) := by rw [← hs]; simp
    simpa [eq_comm] using this
  apply Subtype.ext
  apply Prod.ext <;> grind

def transpositionParam (n : ℕ) :
    Option (LtPair (Fin n)) → {σ // σ ∈ transpositionsWithOne n}
  | none => ⟨1, Or.inl rfl⟩
  | some p => ⟨Equiv.swap p.val.1 p.val.2,
      Or.inr ⟨p.val.1, p.val.2, p.property.ne, rfl⟩⟩

theorem transpositionParam_bijective (n : ℕ) : Function.Bijective (transpositionParam n) := by
  constructor
  · intro p q h
    cases p with
    | none =>
      cases q with
      | none => rfl
      | some q =>
        exfalso
        have h' : (1 : Equiv.Perm (Fin n)) = Equiv.swap q.val.1 q.val.2 :=
          congrArg Subtype.val h
        exact q.property.ne (Equiv.swap_eq_refl_iff.mp h'.symm)
    | some p =>
      cases q with
      | none =>
        exfalso
        have h' : Equiv.swap p.val.1 p.val.2 = (1 : Equiv.Perm (Fin n)) :=
          congrArg Subtype.val h
        exact p.property.ne (Equiv.swap_eq_refl_iff.mp h')
      | some q =>
        simp only [Option.some.injEq]
        exact swapOfLtPair_injective (congrArg Subtype.val h)
  · rintro ⟨σ, hσ⟩
    rcases hσ with rfl | ⟨i, j, hij, rfl⟩
    · exact ⟨none, rfl⟩
    · rcases lt_or_gt_of_ne hij with hij | hji
      · exact ⟨some ⟨(i, j), hij⟩, rfl⟩
      · refine ⟨some ⟨(j, i), hji⟩, ?_⟩
        apply Subtype.ext
        exact Equiv.swap_comm _ _

def transpositionEquiv (n : ℕ) :
    Option (LtPair (Fin n)) ≃ {σ // σ ∈ transpositionsWithOne n} :=
  Equiv.ofBijective (transpositionParam n) (transpositionParam_bijective n)

def diagOrNeParam (α : Type*) [DecidableEq α] : Sum α (NePair α) → α × α
  | Sum.inl a => (a, a)
  | Sum.inr p => p

theorem diagOrNeParam_bijective (α : Type*) [DecidableEq α] :
    Function.Bijective (diagOrNeParam α) := by
  constructor
  · intro p q h
    cases p with
    | inl p =>
      cases q with
      | inl q => simp_all [diagOrNeParam]
      | inr q =>
        exfalso
        exact q.property ((congrArg Prod.fst h).symm.trans (congrArg Prod.snd h))
    | inr p =>
      cases q with
      | inl q =>
        exfalso
        exact p.property ((congrArg Prod.fst h).trans (congrArg Prod.snd h).symm)
      | inr q => exact congrArg Sum.inr (Subtype.ext h)
  · rintro ⟨a, b⟩
    by_cases h : a = b
    · subst b
      exact ⟨Sum.inl a, rfl⟩
    · exact ⟨Sum.inr ⟨(a, b), h⟩, rfl⟩

def diagOrNeEquiv (α : Type*) [DecidableEq α] : Sum α (NePair α) ≃ α × α :=
  Equiv.ofBijective (diagOrNeParam α) (diagOrNeParam_bijective α)

def orientedPairParam {α : Type*} [LinearOrder α] : LtPair α × Bool → NePair α
  | (p, false) => ⟨p, p.property.ne⟩
  | (p, true) => ⟨(p.val.2, p.val.1), p.property.ne.symm⟩

theorem orientedPairParam_bijective {α : Type*} [LinearOrder α] :
    Function.Bijective (orientedPairParam : LtPair α × Bool → NePair α) := by
  constructor
  · rintro ⟨p, b⟩ ⟨q, c⟩ h
    cases b <;> cases c
    · simp only [orientedPairParam, Subtype.mk.injEq] at h
      exact congrArg (fun r => (r, false)) (Subtype.ext h)
    · simp only [orientedPairParam, Subtype.mk.injEq] at h
      grind
    · simp only [orientedPairParam, Subtype.mk.injEq] at h
      grind
    · simp only [orientedPairParam, Subtype.mk.injEq] at h
      have hpq : p = q :=
        Subtype.ext <| Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
      exact congrArg (fun r => (r, true)) hpq
  · rintro ⟨⟨a, b⟩, hab⟩
    rcases lt_or_gt_of_ne hab with hab | hba
    · exact ⟨(⟨(a, b), hab⟩, false), rfl⟩
    · exact ⟨(⟨(b, a), hba⟩, true), rfl⟩

def orientedPairEquiv {α : Type*} [LinearOrder α] : LtPair α × Bool ≃ NePair α :=
  Equiv.ofBijective orientedPairParam orientedPairParam_bijective

theorem sum_ordered_pairs {α : Type*} [Fintype α] [LinearOrder α]
    (F : α → α → ℝ) (hsymm : ∀ a b, F a b = F b a) :
    (∑ a, ∑ b, F a b) = (∑ a, F a a) + 2 * ∑ p : LtPair α, F p.val.1 p.val.2 := by
  calc
    _ = ∑ p : α × α, F p.1 p.2 :=
      (Fintype.sum_prod_type fun p : α × α => F p.1 p.2).symm
    _ = ∑ p : Sum α (NePair α), F (diagOrNeEquiv α p).1 (diagOrNeEquiv α p).2 :=
      ((diagOrNeEquiv α).sum_comp fun p => F p.1 p.2).symm
    _ = (∑ a, F a a) + ∑ p : NePair α, F p.val.1 p.val.2 := by
      rw [Fintype.sum_sum_type]
      rfl
    _ = (∑ a, F a a) + ∑ p : LtPair α × Bool,
        F (orientedPairEquiv p).val.1 (orientedPairEquiv p).val.2 := by
      congr 1
      exact ((orientedPairEquiv).sum_comp fun p => F p.val.1 p.val.2).symm
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp only [Fintype.sum_bool, orientedPairEquiv, Equiv.ofBijective_apply,
        orientedPairParam]
      simp_rw [hsymm]
      simp_rw [← two_mul]
      rw [← Finset.mul_sum]

def tileSum (n : ℕ) (f : Equiv.Perm (Fin n) → ℝ) (g : Equiv.Perm (Fin n)) : ℝ :=
  ∑ t : {σ // σ ∈ transpositionsWithOne n}, f (g * (t : Equiv.Perm (Fin n)))

theorem tileSum_eq (n : ℕ) (f : Equiv.Perm (Fin n) → ℝ) (g : Equiv.Perm (Fin n)) :
    tileSum n f g = f g + ∑ p : LtPair (Fin n),
      f (g * Equiv.swap p.val.1 p.val.2) := by
  unfold tileSum
  calc
    _ = ∑ p : Option (LtPair (Fin n)),
        f (g * (transpositionEquiv n p : Equiv.Perm (Fin n))) :=
      ((transpositionEquiv n).sum_comp
        (fun t => f (g * (t : Equiv.Perm (Fin n))))).symm
    _ = _ := by rw [Fintype.sum_option]; rfl

theorem two_mul_tileSum_eq (n : ℕ) (f : Equiv.Perm (Fin n) → ℝ)
    (g : Equiv.Perm (Fin n)) :
    2 * tileSum n f g = (2 - n) * f g +
      ∑ a : Fin n, ∑ b : Fin n, f (g * Equiv.swap a b) := by
  rw [tileSum_eq, sum_ordered_pairs]
  · have hdiag (a : Fin n) : f (g * Equiv.swap a a) = f g := by
      rw [Equiv.swap_self]
      exact congrArg f (mul_one g)
    simp_rw [hdiag]
    simp
    ring_nf
  · intro a b
    rw [Equiv.swap_comm]

theorem tileSum_sub (n : ℕ) (f₁ f₂ : Equiv.Perm (Fin n) → ℝ)
    (g : Equiv.Perm (Fin n)) :
    tileSum n (fun x => f₁ x - f₂ x) g = tileSum n f₁ g - tileSum n f₂ g := by
  simp [tileSum, Finset.sum_sub_distrib]

theorem swap_mul_swap_eq_swap_mul {α : Type*} [DecidableEq α]
    {x y z : α} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    Equiv.swap x z * Equiv.swap x y = Equiv.swap x y * Equiv.swap z y := by
  ext w
  simp only [Equiv.Perm.coe_mul, Function.comp_apply]
  simp [Equiv.swap_apply_def]
  grind

def rowRep {α : Type*} [DecidableEq α] (B : Finset α) (x : α) :
    Option B → Equiv.Perm α
  | none => 1
  | some y => Equiv.swap x y

def rowSum {α : Type*} [Fintype α] [DecidableEq α] (B : Finset α) (x : α)
    (f : Equiv.Perm α → ℝ) (g : Equiv.Perm α) : ℝ :=
  ∑ q : Option B, f (g * rowRep B x q)

theorem rowSum_right_swap {α : Type*} [Fintype α] [DecidableEq α]
    (B : Finset α) {x : α} (hx : x ∉ B) (f : Equiv.Perm α → ℝ)
    (hinv : ∀ (g : Equiv.Perm α) (y z : α), y ∈ B → z ∈ B →
      f (g * Equiv.swap y z) = f g)
    (g : Equiv.Perm α) (z : B) :
    rowSum B x f (g * Equiv.swap x z) = rowSum B x f g := by
  let e : Equiv.Perm (Option B) := Equiv.swap none (some z)
  calc
    _ = ∑ q : Option B, f (g * rowRep B x (e q)) := by
      apply Finset.sum_congr rfl
      intro q _
      cases q with
      | none => simp [rowRep, e]
      | some y =>
        by_cases hyz : y = z
        · subst y
          simp [rowRep, e, mul_assoc, Equiv.swap_mul_self]
        · have hxy : x ≠ y := fun h => hx (h ▸ y.property)
          have hxz : x ≠ (z : α) := fun h => hx (h ▸ z.property)
          have hswap := swap_mul_swap_eq_swap_mul hxy hxz
            (Subtype.coe_ne_coe.mpr hyz)
          have hey : e (some y) = some y := by
            exact Equiv.swap_apply_of_ne_of_ne (by simp) (by simpa using hyz)
          rw [hey]
          simp only [rowRep]
          rw [mul_assoc, hswap, ← mul_assoc]
          exact hinv (g * Equiv.swap x y) z y z.property y.property
    _ = _ := Fintype.sum_equiv e _ _ fun q => rfl

theorem rowEnergy_nonneg {α : Type*} [Fintype α] [DecidableEq α]
    (B : Finset α) {x : α} (hx : x ∉ B) (f : Equiv.Perm α → ℝ)
    (hinv : ∀ (g : Equiv.Perm α) (y z : α), y ∈ B → z ∈ B →
      f (g * Equiv.swap y z) = f g) :
    0 ≤ ∑ g, f g * rowSum B x f g := by
  let E : ℝ := ∑ g, f g * rowSum B x f g
  have hsquare : (∑ g, (rowSum B x f g) ^ 2) = (B.card + 1) * E := by
    calc
      _ = ∑ g, rowSum B x f g * ∑ q : Option B, f (g * rowRep B x q) := by
        simp only [rowSum, pow_two]
      _ = ∑ g, ∑ q : Option B, rowSum B x f g * f (g * rowRep B x q) := by
        simp_rw [Finset.mul_sum]
      _ = ∑ q : Option B, ∑ g, rowSum B x f g * f (g * rowRep B x q) := by
        rw [Finset.sum_comm]
      _ = ∑ _q : Option B, E := by
        apply Finset.sum_congr rfl
        intro q _
        cases q with
        | none => simp [E, rowRep, mul_comm]
        | some y =>
          have hreindex :
              (∑ g, rowSum B x f (g * Equiv.swap x y) *
                f (g * Equiv.swap x y)) = ∑ g, rowSum B x f g * f g :=
            Fintype.sum_equiv (Equiv.mulRight (Equiv.swap x y)) _ _ fun g => rfl
          simp_rw [rowSum_right_swap B hx f hinv] at hreindex
          simpa [E, rowRep, mul_comm] using hreindex
      _ = (B.card + 1) * E := by simp [Fintype.card_option, Fintype.card_coe]
  have hsnonneg : 0 ≤ ∑ g, (rowSum B x f g) ^ 2 := by positivity
  have hcard : (0 : ℝ) < B.card + 1 := by positivity
  nlinarith

def ltPairEquivSigma (k : ℕ) :
    LtPair (Fin k) ≃ Σ j : Fin k, Fin j.val where
  toFun p := ⟨p.val.2, ⟨p.val.1.val, p.property⟩⟩
  invFun q :=
    ⟨(⟨q.2.val, lt_trans q.2.isLt q.1.isLt⟩, q.1), q.2.isLt⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext <;> apply Fin.ext <;> rfl
  right_inv q := by
    rcases q with ⟨j, i⟩
    rfl

theorem sum_ltPair_snd (k : ℕ) (F : Fin k → ℝ) :
    (∑ p : LtPair (Fin k), F p.val.2) = ∑ j : Fin k, j.val * F j := by
  calc
    _ = ∑ q : Σ j : Fin k, Fin j.val, F q.1 :=
      (ltPairEquivSigma k).sum_comp (fun q => F q.1)
    _ = ∑ j : Fin k, ∑ _i : Fin j.val, F j := by rw [Fintype.sum_sigma]
    _ = _ := by simp

open PartitionShape

theorem contentSumAux_cast (k : ℕ) (l : List ℕ) :
    ((contentSumAux k l : ℤ) : ℝ) =
      ∑ i : Fin l.length, (l.get i : ℝ) *
        ((l.get i : ℝ) - 2 * ((k + i.val : ℕ) : ℝ) - 1) := by
  induction l generalizing k with
  | nil => simp [contentSumAux]
  | cons a l ih =>
    rw [contentSumAux]
    push_cast
    change (a : ℝ) * ((a : ℝ) - 2 * (k : ℝ) - 1) +
        ((contentSumAux (k + 1) l : ℤ) : ℝ) =
      ∑ i : Fin (l.length + 1), ((a :: l).get i : ℝ) *
        (((a :: l).get i : ℝ) - 2 * ((k : ℝ) + (i.val : ℝ)) - 1)
    rw [Fin.sum_univ_succ]
    rw [ih (k + 1)]
    congr 1
    · simp
    · apply Finset.sum_congr rfl
      intro i _
      simp only [Fin.val_succ, List.get_eq_getElem, List.getElem_cons_succ]
      push_cast
      ring

theorem content_coefficient {n : ℕ} (lam : PartitionShape n) :
    (2 - n : ℝ) + ∑ i : Fin lam.parts.length, (lam.parts.get i : ℝ) ^ 2 -
        2 * ∑ p : LtPair (Fin lam.parts.length), (lam.parts.get p.val.2 : ℝ) =
      2 + (lam.contentSum : ℝ) := by
  have hn : n = ∑ i : Fin lam.parts.length, lam.parts.get i := by
    calc
      n = lam.parts.sum := lam.sum_eq.symm
      _ = ∑ i : Fin lam.parts.length, lam.parts.get i := by
        rw [← List.sum_ofFn, List.ofFn_get]
  have hnr : (n : ℝ) = ∑ i : Fin lam.parts.length, (lam.parts.get i : ℝ) := by
    exact_mod_cast hn
  rw [PartitionShape.contentSum, contentSumAux_cast]
  have hp := sum_ltPair_snd lam.parts.length (fun j => (lam.parts.get j : ℝ))
  rw [hp]
  simp only [Nat.zero_add]
  rw [hnr]
  simp_rw [mul_sub, mul_one]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  have htwo :
      (∑ x : Fin lam.parts.length,
        (lam.parts.get x : ℝ) * (2 * (x.val : ℝ))) =
        2 * ∑ x : Fin lam.parts.length, (x.val : ℝ) * (lam.parts.get x : ℝ) := by
    calc
      _ = ∑ x : Fin lam.parts.length,
          2 * ((x.val : ℝ) * (lam.parts.get x : ℝ)) := by
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ = _ := (Finset.mul_sum Finset.univ
        (fun x : Fin lam.parts.length => (x.val : ℝ) * (lam.parts.get x : ℝ)) 2).symm
  rw [htwo]
  simp_rw [pow_two]
  ring

def normSq {α : Type*} [Fintype α] [DecidableEq α] (f : Equiv.Perm α → ℝ) : ℝ :=
  ∑ g, f g * f g

def swapCorr {α : Type*} [Fintype α] [DecidableEq α]
    (f : Equiv.Perm α → ℝ) (a b : α) : ℝ :=
  ∑ g, f g * f (g * Equiv.swap a b)

theorem swapCorr_comm {α : Type*} [Fintype α] [DecidableEq α]
    (f : Equiv.Perm α → ℝ) (a b : α) : swapCorr f a b = swapCorr f b a := by
  simp [swapCorr, Equiv.swap_comm]

theorem rowEnergy_eq {α : Type*} [Fintype α] [DecidableEq α]
    (B : Finset α) (x : α) (f : Equiv.Perm α → ℝ) :
    (∑ g, f g * rowSum B x f g) =
      normSq f + ∑ y ∈ B, swapCorr f x y := by
  calc
    _ = ∑ q : Option B, ∑ g, f g * f (g * rowRep B x q) := by
      unfold rowSum
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = normSq f + ∑ y : B, swapCorr f x y := by
      rw [Fintype.sum_option]
      simp [rowRep, normSq, swapCorr]
    _ = _ := by
      congr 1
      exact Finset.sum_attach B (fun y => swapCorr f x y)

def blockPairCorr {n : ℕ} {lam : PartitionShape n}
    (P : OrderedSetPartition lam) (f : Equiv.Perm (Fin n) → ℝ)
    (i j : Fin lam.parts.length) : ℝ :=
  ∑ a ∈ P.block i, ∑ b ∈ P.block j, swapCorr f a b

theorem blockPairCorr_comm {n : ℕ} {lam : PartitionShape n}
    (P : OrderedSetPartition lam) (f : Equiv.Perm (Fin n) → ℝ)
    (i j : Fin lam.parts.length) :
    blockPairCorr P f i j = blockPairCorr P f j i := by
  unfold blockPairCorr
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  exact swapCorr_comm f a b

theorem blockPairCorr_self {n : ℕ} {lam : PartitionShape n}
    (P : OrderedSetPartition lam) (f : Equiv.Perm (Fin n) → ℝ)
    (hinv : ∀ (g : Equiv.Perm (Fin n)) (i : Fin lam.parts.length) (a b : Fin n),
      a ∈ P.block i → b ∈ P.block i → f (g * Equiv.swap a b) = f g)
    (i : Fin lam.parts.length) :
    blockPairCorr P f i i = (lam.parts.get i : ℝ) ^ 2 * normSq f := by
  have hc (a : Fin n) (ha : a ∈ P.block i) (b : Fin n) (hb : b ∈ P.block i) :
      swapCorr f a b = normSq f := by
    unfold swapCorr normSq
    apply Finset.sum_congr rfl
    intro g _
    rw [hinv g i a b ha hb]
  unfold blockPairCorr
  calc
    _ = ∑ _a ∈ P.block i, ∑ _b ∈ P.block i, normSq f := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      exact hc a ha b hb
    _ = _ := by simp [P.card_block]; ring

theorem blockPairCorr_cross_lower {n : ℕ} {lam : PartitionShape n}
    (P : OrderedSetPartition lam) (f : Equiv.Perm (Fin n) → ℝ)
    (hinv : ∀ (g : Equiv.Perm (Fin n)) (i : Fin lam.parts.length) (a b : Fin n),
      a ∈ P.block i → b ∈ P.block i → f (g * Equiv.swap a b) = f g)
    {i j : Fin lam.parts.length} (hij : i < j) :
    0 ≤ (lam.parts.get j : ℝ) * normSq f + blockPairCorr P f i j := by
  have hdis : Disjoint (P.block i) (P.block j) := P.pairwise_disjoint hij.ne
  have hpoint (x : Fin n) (hxj : x ∈ P.block j) :
      0 ≤ normSq f + ∑ y ∈ P.block i, swapCorr f x y := by
    have hxi : x ∉ P.block i := (Finset.disjoint_left.mp hdis.symm) hxj
    have h := rowEnergy_nonneg (P.block i) hxi f
      (fun g a b ha hb => hinv g i a b ha hb)
    calc
      0 ≤ ∑ g, f g * rowSum (P.block i) x f g := h
      _ = normSq f + ∑ y ∈ P.block i, swapCorr f x y := rowEnergy_eq (P.block i) x f
  have hsum : 0 ≤ ∑ x ∈ P.block j,
      (normSq f + ∑ y ∈ P.block i, swapCorr f x y) :=
    Finset.sum_nonneg fun x hx => hpoint x hx
  rw [Finset.sum_add_distrib] at hsum
  have hcross :
      (∑ x ∈ P.block j, ∑ y ∈ P.block i, swapCorr f x y) = blockPairCorr P f i j := by
    change blockPairCorr P f j i = blockPairCorr P f i j
    exact blockPairCorr_comm P f j i
  rw [hcross] at hsum
  simpa [P.card_block] using hsum

theorem total_swapCorr_eq_blocks {n : ℕ} {lam : PartitionShape n}
    (P : OrderedSetPartition lam) (f : Equiv.Perm (Fin n) → ℝ) :
    (∑ a : Fin n, ∑ b : Fin n, swapCorr f a b) =
      ∑ i : Fin lam.parts.length, ∑ j : Fin lam.parts.length, blockPairCorr P f i j := by
  have hpdAll : (Set.univ : Set (Fin lam.parts.length)).PairwiseDisjoint P.block := by
    intro i _ j _ hij
    exact P.pairwise_disjoint hij
  have hpd : (↑(Finset.univ : Finset (Fin lam.parts.length)) :
      Set (Fin lam.parts.length)).PairwiseDisjoint P.block := by
    simpa using hpdAll
  change (∑ a ∈ Finset.univ, ∑ b ∈ Finset.univ, swapCorr f a b) = _
  rw [← P.union_eq_univ, Finset.sum_biUnion hpd]
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [Finset.sum_biUnion hpd]
  unfold blockPairCorr
  rw [Finset.sum_comm]

def tileEnergy (n : ℕ) (f : Equiv.Perm (Fin n) → ℝ) : ℝ :=
  ∑ g, f g * tileSum n f g

theorem two_mul_tileEnergy_eq (n : ℕ) (f : Equiv.Perm (Fin n) → ℝ) :
    2 * tileEnergy n f = (2 - n) * normSq f +
      ∑ a : Fin n, ∑ b : Fin n, swapCorr f a b := by
  unfold tileEnergy
  calc
    _ = ∑ g, f g * (2 * tileSum n f g) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro g _
      ring
    _ = ∑ g, f g * ((2 - n) * f g +
        ∑ a : Fin n, ∑ b : Fin n, f (g * Equiv.swap a b)) := by
      apply Finset.sum_congr rfl
      intro g _
      rw [two_mul_tileSum_eq]
    _ = _ := by
      simp_rw [mul_add, Finset.mul_sum, Finset.sum_add_distrib]
      rw [Finset.sum_comm]
      congr 1
      · unfold normSq
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro g _
        ring
      · apply Finset.sum_congr rfl
        intro a _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro b _
        rfl

set_option maxHeartbeats 800000 in
theorem tileEnergy_lower {n : ℕ} {lam : PartitionShape n}
    (P : OrderedSetPartition lam) (f : Equiv.Perm (Fin n) → ℝ)
    (hinv : ∀ (g : Equiv.Perm (Fin n)) (i : Fin lam.parts.length) (a b : Fin n),
      a ∈ P.block i → b ∈ P.block i → f (g * Equiv.swap a b) = f g) :
    (2 + (lam.contentSum : ℝ)) * normSq f ≤ 2 * tileEnergy n f := by
  have henergy := two_mul_tileEnergy_eq n f
  rw [total_swapCorr_eq_blocks P f] at henergy
  have houter := sum_ordered_pairs (blockPairCorr P f) (blockPairCorr_comm P f)
  have hdiag :
      (∑ i : Fin lam.parts.length, blockPairCorr P f i i) =
        (∑ i : Fin lam.parts.length, (lam.parts.get i : ℝ) ^ 2) * normSq f := by
    calc
      _ = ∑ i : Fin lam.parts.length, (lam.parts.get i : ℝ) ^ 2 * normSq f := by
        apply Finset.sum_congr rfl
        intro i _
        exact blockPairCorr_self P f hinv i
      _ = _ := (Finset.sum_mul Finset.univ
        (fun i : Fin lam.parts.length => (lam.parts.get i : ℝ) ^ 2) (normSq f)).symm
  rw [houter, hdiag] at henergy
  have hcross :
      0 ≤ ∑ p : LtPair (Fin lam.parts.length),
        ((lam.parts.get p.val.2 : ℝ) * normSq f +
          blockPairCorr P f p.val.1 p.val.2) :=
    Finset.sum_nonneg fun p _ => blockPairCorr_cross_lower P f hinv p.property
  rw [Finset.sum_add_distrib, ← Finset.sum_mul] at hcross
  have hcross2 :
      0 ≤ 2 * ((∑ p : LtPair (Fin lam.parts.length),
        (lam.parts.get p.val.2 : ℝ)) * normSq f +
        ∑ p : LtPair (Fin lam.parts.length),
          blockPairCorr P f p.val.1 p.val.2) :=
    mul_nonneg (by norm_num) hcross
  have hcoeff := content_coefficient lam
  have hcoeffN := congrArg (fun x : ℝ => x * normSq f) hcoeff
  ring_nf at henergy hcoeffN hcross2 ⊢
  linarith

theorem tileSum_eq_zero_imp {n : ℕ} {lam : PartitionShape n}
    (P : OrderedSetPartition lam) (hcontent : 0 ≤ lam.contentSum)
    (f : Equiv.Perm (Fin n) → ℝ)
    (hinv : ∀ (g : Equiv.Perm (Fin n)) (i : Fin lam.parts.length) (a b : Fin n),
      a ∈ P.block i → b ∈ P.block i → f (g * Equiv.swap a b) = f g)
    (hzero : ∀ g, tileSum n f g = 0) : f = 0 := by
  have hE : tileEnergy n f = 0 := by
    unfold tileEnergy
    apply Finset.sum_eq_zero
    intro g _
    rw [hzero]
    ring
  have hlower := tileEnergy_lower P f hinv
  rw [hE, mul_zero] at hlower
  have hc : (0 : ℝ) ≤ (lam.contentSum : ℝ) := by exact_mod_cast hcontent
  have hnorm : 0 ≤ normSq f := by
    unfold normSq
    exact Finset.sum_nonneg fun g _ => mul_self_nonneg (f g)
  have hnormzero : normSq f = 0 := by nlinarith
  funext g
  change f g = 0
  have hterm : f g * f g = 0 := by
    apply (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => mul_self_nonneg (f x))).mp
      (show (∑ x, f x * f x) = 0 by exact hnormzero)
    exact Finset.mem_univ g
  exact mul_self_eq_zero.mp hterm

theorem orderedSetPartition_ext {n : ℕ} {lam : PartitionShape n}
    {P Q : OrderedSetPartition lam} (h : ∀ i, P.block i = Q.block i) : P = Q := by
  cases P with
  | mk pb pc pd pu =>
    cases Q with
    | mk qb qc qd qu =>
      have hpq : pb = qb := funext h
      subst qb
      rfl

local instance orderedSetPartitionFintype {n : ℕ} (lam : PartitionShape n) :
    Fintype (OrderedSetPartition lam) :=
  Fintype.ofInjective (fun P : OrderedSetPartition lam => P.block) fun P Q h => by
    apply orderedSetPartition_ext
    exact congrFun h

def actPartition {n : ℕ} {lam : PartitionShape n} (σ : Equiv.Perm (Fin n))
    (P : OrderedSetPartition lam) : OrderedSetPartition lam where
  block i := (P.block i).image σ
  card_block i := by rw [Finset.card_image_of_injective _ σ.injective, P.card_block]
  pairwise_disjoint i j hij := by
    change Disjoint ((P.block i).image σ) ((P.block j).image σ)
    rw [Finset.disjoint_left]
    intro x hxi hxj
    obtain ⟨xi, hxi_mem, hxi_eq⟩ := Finset.mem_image.mp hxi
    obtain ⟨xj, hxj_mem, hxj_eq⟩ := Finset.mem_image.mp hxj
    have : xi = xj := σ.injective (hxi_eq.trans hxj_eq.symm)
    subst xj
    exact (Finset.disjoint_left.mp (P.pairwise_disjoint hij)) hxi_mem hxj_mem
  union_eq_univ := by
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, hx⟩
      trivial
    · intro _
      have hx : σ.symm x ∈ Finset.univ.biUnion P.block := by
        rw [P.union_eq_univ]
        exact Finset.mem_univ _
      obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hx
      refine ⟨i, Finset.mem_image.mpr ⟨σ.symm x, hi, ?_⟩⟩
      simp

@[simp] theorem actPartition_block {n : ℕ} {lam : PartitionShape n}
    (σ : Equiv.Perm (Fin n)) (P : OrderedSetPartition lam)
    (i : Fin lam.parts.length) :
    (actPartition σ P).block i = (P.block i).image σ := rfl

@[simp] theorem actPartition_one {n : ℕ} {lam : PartitionShape n}
    (P : OrderedSetPartition lam) : actPartition 1 P = P := by
  apply orderedSetPartition_ext
  intro i
  simp [actPartition]

@[simp] theorem actPartition_mul {n : ℕ} {lam : PartitionShape n}
    (σ τ : Equiv.Perm (Fin n)) (P : OrderedSetPartition lam) :
    actPartition (σ * τ) P = actPartition σ (actPartition τ P) := by
  apply orderedSetPartition_ext
  intro i
  simp [actPartition, Finset.image_image, Function.comp_def, Equiv.Perm.coe_mul]

@[simp] theorem actPartition_inv_actPartition {n : ℕ} {lam : PartitionShape n}
    (σ : Equiv.Perm (Fin n)) (P : OrderedSetPartition lam) :
    actPartition σ⁻¹ (actPartition σ P) = P := by
  rw [← actPartition_mul]
  simp

@[simp] theorem actPartition_actPartition_inv {n : ℕ} {lam : PartitionShape n}
    (σ : Equiv.Perm (Fin n)) (P : OrderedSetPartition lam) :
    actPartition σ (actPartition σ⁻¹ P) = P := by
  rw [← actPartition_mul]
  simp

theorem sendsPartition_iff {n : ℕ} {lam : PartitionShape n}
    (σ : Equiv.Perm (Fin n)) (P Q : OrderedSetPartition lam) :
    SendsPartition σ P Q ↔ actPartition σ P = Q := by
  constructor
  · intro h
    apply orderedSetPartition_ext
    intro i
    exact h i
  · intro h i
    exact congrArg (fun R => R.block i) h

def tilingEquiv {G : Type*} [Group G] [Fintype G] {X Y : Set G}
    (h : IsTiling X Y) : X × Y ≃ G :=
  Equiv.ofBijective (fun p => (p.1 : G) * (p.2 : G)) <| by
    constructor
    · intro p q hpq
      obtain ⟨w, hw, huw⟩ := h ((p.1 : G) * (p.2 : G))
      exact (huw p rfl).trans (huw q hpq.symm).symm
    · intro g
      obtain ⟨p, hp, _⟩ := h g
      exact ⟨p, hp⟩

def blockPoint {n : ℕ} {lam : PartitionShape n} (P : OrderedSetPartition lam) :
    (Σ i, ↥(P.block i)) → Fin n := fun x => x.2

theorem blockPoint_bijective {n : ℕ} {lam : PartitionShape n}
    (P : OrderedSetPartition lam) : Function.Bijective (blockPoint P) := by
  constructor
  · rintro ⟨i, x⟩ ⟨j, y⟩ hxy
    have hval : (x : Fin n) = (y : Fin n) := hxy
    have hij : i = j := by
      by_contra hij
      have hd := P.pairwise_disjoint hij
      change Disjoint (P.block i) (P.block j) at hd
      rw [Finset.disjoint_left] at hd
      exact hd x.property (by simp [hval, y.property])
    subst j
    have hsub : x = y := Subtype.ext hval
    subst y
    rfl
  · intro x
    have hx : x ∈ Finset.univ.biUnion P.block := by
      rw [P.union_eq_univ]
      exact Finset.mem_univ x
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hx
    exact ⟨⟨i, ⟨x, hi⟩⟩, rfl⟩

def rawBlockEquiv {n : ℕ} {lam : PartitionShape n} (P : OrderedSetPartition lam) :
    Fin n ≃ Σ i, ↥(P.block i) :=
  (Equiv.ofBijective (blockPoint P) (blockPoint_bijective P)).symm

@[simp] theorem rawBlockEquiv_symm_apply {n : ℕ} {lam : PartitionShape n}
    (P : OrderedSetPartition lam) (x : Σ i, ↥(P.block i)) :
    (rawBlockEquiv P).symm x = x.2 := rfl

def blockEquiv {n : ℕ} {lam : PartitionShape n} (P : OrderedSetPartition lam) :
    Fin n ≃ Σ i, Fin (lam.parts.get i) :=
  (rawBlockEquiv P).trans <|
    Equiv.sigmaCongrRight fun i => (P.block i).equivFinOfCardEq (P.card_block i)

theorem blockEquiv_fst_eq_iff {n : ℕ} {lam : PartitionShape n}
    (P : OrderedSetPartition lam) (x : Fin n) (i : Fin lam.parts.length) :
    (blockEquiv P x).1 = i ↔ x ∈ P.block i := by
  change (rawBlockEquiv P x).1 = i ↔ x ∈ P.block i
  constructor
  · intro hi
    have hx : ((rawBlockEquiv P x).2 : Fin n) = x := by
      have hx' := (rawBlockEquiv P).symm_apply_apply x
      change blockPoint P (rawBlockEquiv P x) = x at hx'
      exact hx'
    simpa [← hi, hx] using (rawBlockEquiv P x).2.property
  · intro hx
    have heq : rawBlockEquiv P x = ⟨i, ⟨x, hx⟩⟩ := by
      apply (blockPoint_bijective P).1
      have hleft := (rawBlockEquiv P).symm_apply_apply x
      change blockPoint P (rawBlockEquiv P x) = x at hleft
      simpa [blockPoint] using hleft
    exact congrArg Sigma.fst heq

def partitionPerm {n : ℕ} {lam : PartitionShape n}
    (P Q : OrderedSetPartition lam) : Equiv.Perm (Fin n) :=
  (blockEquiv P).trans (blockEquiv Q).symm

theorem partitionPerm_sends {n : ℕ} {lam : PartitionShape n}
    (P Q : OrderedSetPartition lam) : SendsPartition (partitionPerm P Q) P Q := by
  rw [sendsPartition_iff]
  apply orderedSetPartition_ext
  intro i
  ext x
  simp only [actPartition_block, Finset.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [← blockEquiv_fst_eq_iff] at hy ⊢
    simpa [partitionPerm] using hy
  · intro hx
    refine ⟨(partitionPerm P Q).symm x, ?_, by simp⟩
    rw [← blockEquiv_fst_eq_iff] at hx ⊢
    simpa [partitionPerm] using hx

theorem swap_mem_iff {α : Type*} [DecidableEq α] (S : Finset α)
    {a b : α} (hab : a ∈ S ↔ b ∈ S) (x : α) :
    Equiv.swap a b x ∈ S ↔ x ∈ S := by
  by_cases hab' : a = b
  · subst b
    simp
  by_cases hxa : x = a
  · subst x
    simpa using hab.symm
  by_cases hxb : x = b
  · subst x
    simpa using hab
  simp [Equiv.swap_apply_of_ne_of_ne hxa hxb]

theorem actPartition_swap_same_block {n : ℕ} {lam : PartitionShape n}
    (P : OrderedSetPartition lam) (i : Fin lam.parts.length) {a b : Fin n}
    (ha : a ∈ P.block i) (hb : b ∈ P.block i) :
    actPartition (Equiv.swap a b) P = P := by
  apply orderedSetPartition_ext
  intro j
  have hab : a ∈ P.block j ↔ b ∈ P.block j := by
    by_cases hji : j = i
    · subst j
      exact iff_of_true ha hb
    · have hd : Disjoint (P.block j) (P.block i) := P.pairwise_disjoint hji
      have hna : a ∉ P.block j := fun haj => (Finset.disjoint_left.mp hd) haj ha
      have hnb : b ∉ P.block j := fun hbj => (Finset.disjoint_left.mp hd) hbj hb
      exact iff_of_false hna hnb
  ext x
  simp only [actPartition_block, Finset.mem_image]
  constructor
  · rintro ⟨y, hy, hxy⟩
    have hyx : y = Equiv.swap a b x := Equiv.swap_apply_eq_iff.mp hxy
    rw [hyx] at hy
    exact (swap_mem_iff (P.block j) hab x).mp hy
  · intro hx
    refine ⟨Equiv.swap a b x, (swap_mem_iff (P.block j) hab x).mpr hx, ?_⟩
    simp

theorem sends_mul_iff {n : ℕ} {lam : PartitionShape n}
    (σ τ : Equiv.Perm (Fin n)) (P Q : OrderedSetPartition lam) :
    SendsPartition (σ * τ) P Q ↔ SendsPartition τ P (actPartition σ⁻¹ Q) := by
  rw [sendsPartition_iff, sendsPartition_iff, actPartition_mul]
  constructor
  · intro h
    calc
      actPartition τ P =
          actPartition σ⁻¹ (actPartition σ (actPartition τ P)) := by simp
      _ = actPartition σ⁻¹ Q := congrArg (actPartition σ⁻¹) h
  · intro h
    calc
      actPartition σ (actPartition τ P) =
          actPartition σ (actPartition σ⁻¹ Q) := congrArg (actPartition σ) h
      _ = Q := by simp

def yCount {n : ℕ} {lam : PartitionShape n} (Y : Set (Equiv.Perm (Fin n)))
    (P Q : OrderedSetPartition lam) : ℝ :=
  ∑ y : Y, propIndicator (SendsPartition (y : Equiv.Perm (Fin n)) P Q)

def fullCount {n : ℕ} {lam : PartitionShape n} (P Q : OrderedSetPartition lam) : ℝ :=
  ∑ g : Equiv.Perm (Fin n), propIndicator (SendsPartition g P Q)

theorem sends_partitionPerm_mul_iff {n : ℕ} {lam : PartitionShape n}
    (P Q R : OrderedSetPartition lam) (g : Equiv.Perm (Fin n)) :
    SendsPartition g P Q ↔ SendsPartition (partitionPerm Q R * g) P R := by
  have hk : actPartition (partitionPerm Q R) Q = R :=
    (sendsPartition_iff (partitionPerm Q R) Q R).mp (partitionPerm_sends Q R)
  have hki : actPartition (partitionPerm Q R)⁻¹ R = Q := by
    calc
      actPartition (partitionPerm Q R)⁻¹ R =
          actPartition (partitionPerm Q R)⁻¹
            (actPartition (partitionPerm Q R) Q) := congrArg _ hk.symm
      _ = Q := by simp
  rw [sendsPartition_iff, sendsPartition_iff, actPartition_mul]
  constructor
  · intro h
    rw [h, hk]
  · intro h
    have h' := congrArg (actPartition (partitionPerm Q R)⁻¹) h
    simpa [actPartition_mul, hki] using h'

theorem fullCount_eq {n : ℕ} {lam : PartitionShape n}
    (P Q R : OrderedSetPartition lam) : fullCount P Q = fullCount P R := by
  unfold fullCount
  calc
    _ = ∑ g : Equiv.Perm (Fin n),
        propIndicator (SendsPartition (partitionPerm Q R * g) P R) := by
      apply Finset.sum_congr rfl
      intro g _
      rw [sends_partitionPerm_mul_iff]
    _ = _ := Fintype.sum_equiv (Equiv.mulLeft (partitionPerm Q R)) _ _ fun g => rfl

set_option maxHeartbeats 800000 in
theorem tiling_convolution {n : ℕ} {Y : Set (Equiv.Perm (Fin n))}
    (h : IsTiling (transpositionsWithOne n) Y) {lam : PartitionShape n}
    (P Q : OrderedSetPartition lam) :
    (∑ t : {σ // σ ∈ transpositionsWithOne n},
      yCount Y P (actPartition (t : Equiv.Perm (Fin n))⁻¹ Q)) = fullCount P Q := by
  unfold yCount fullCount
  calc
    _ = ∑ t : {σ // σ ∈ transpositionsWithOne n}, ∑ y : Y,
        propIndicator
          (SendsPartition ((t : Equiv.Perm (Fin n)) * (y : Equiv.Perm (Fin n))) P Q) := by
      apply Finset.sum_congr rfl
      intro t _
      apply Finset.sum_congr rfl
      intro y _
      rw [sends_mul_iff]
    _ = ∑ p : {σ // σ ∈ transpositionsWithOne n} × Y,
        propIndicator (SendsPartition ((p.1 : Equiv.Perm (Fin n)) *
          (p.2 : Equiv.Perm (Fin n))) P Q) :=
      (Fintype.sum_prod_type (fun p :
        {σ // σ ∈ transpositionsWithOne n} × Y =>
          propIndicator (SendsPartition ((p.1 : Equiv.Perm (Fin n)) *
            (p.2 : Equiv.Perm (Fin n))) P Q))).symm
    _ = _ := (tilingEquiv h).sum_comp fun g =>
      propIndicator (SendsPartition g P Q)

theorem transpositions_conj_inv_mem {n : ℕ} (g σ : Equiv.Perm (Fin n))
    (hσ : σ ∈ transpositionsWithOne n) : g * σ⁻¹ * g⁻¹ ∈ transpositionsWithOne n := by
  rcases hσ with rfl | ⟨i, j, hij, rfl⟩
  · simp [transpositionsWithOne]
  · refine Or.inr ⟨g i, g j, g.injective.ne hij, ?_⟩
    rw [Equiv.swap_inv, Equiv.mul_swap_eq_swap_mul]
    group

def conjugateInvTranspositionEquiv {n : ℕ} (g : Equiv.Perm (Fin n)) :
    {σ // σ ∈ transpositionsWithOne n} ≃ {σ // σ ∈ transpositionsWithOne n} where
  toFun σ := ⟨g * (σ : Equiv.Perm (Fin n))⁻¹ * g⁻¹,
    transpositions_conj_inv_mem g σ σ.property⟩
  invFun σ := ⟨g⁻¹ * (σ : Equiv.Perm (Fin n))⁻¹ * g,
    by simpa using transpositions_conj_inv_mem g⁻¹ σ σ.property⟩
  left_inv σ := by
    apply Subtype.ext
    simp only [mul_inv_rev, inv_inv]
    group
  right_inv σ := by
    apply Subtype.ext
    simp only [mul_inv_rev, inv_inv]
    group

@[simp] theorem conjugateInvTranspositionEquiv_inv_mul {n : ℕ}
    (g : Equiv.Perm (Fin n)) (σ : {τ // τ ∈ transpositionsWithOne n}) :
    ((conjugateInvTranspositionEquiv g σ : Equiv.Perm (Fin n))⁻¹ * g) =
      g * (σ : Equiv.Perm (Fin n)) := by
  simp [conjugateInvTranspositionEquiv]
  group

def liftedCount {n : ℕ} {Y : Set (Equiv.Perm (Fin n))} {lam : PartitionShape n}
    (P : OrderedSetPartition lam) (g : Equiv.Perm (Fin n)) : ℝ :=
  yCount Y P (actPartition g P)

theorem tileSum_liftedCount {n : ℕ} {Y : Set (Equiv.Perm (Fin n))}
    (h : IsTiling (transpositionsWithOne n) Y) {lam : PartitionShape n}
    (P : OrderedSetPartition lam) (g : Equiv.Perm (Fin n)) :
    tileSum n (liftedCount (Y := Y) P) g = fullCount P (actPartition g P) := by
  unfold tileSum liftedCount
  calc
    _ = ∑ σ : {τ // τ ∈ transpositionsWithOne n},
        yCount Y P (actPartition
          ((conjugateInvTranspositionEquiv g σ : Equiv.Perm (Fin n))⁻¹ * g) P) := by
      apply Finset.sum_congr rfl
      intro σ _
      rw [conjugateInvTranspositionEquiv_inv_mul]
    _ = ∑ τ : {σ // σ ∈ transpositionsWithOne n},
        yCount Y P (actPartition ((τ : Equiv.Perm (Fin n))⁻¹ * g) P) :=
      Fintype.sum_equiv (conjugateInvTranspositionEquiv g) _ _ fun σ => rfl
    _ = ∑ τ : {σ // σ ∈ transpositionsWithOne n},
        yCount Y P (actPartition (τ : Equiv.Perm (Fin n))⁻¹
          (actPartition g P)) := by
      simp_rw [actPartition_mul]
    _ = _ := tiling_convolution h P (actPartition g P)

theorem tileSum_liftedCount_const {n : ℕ} {Y : Set (Equiv.Perm (Fin n))}
    (h : IsTiling (transpositionsWithOne n) Y) {lam : PartitionShape n}
    (P : OrderedSetPartition lam) (g : Equiv.Perm (Fin n)) :
    tileSum n (liftedCount (Y := Y) P) g = fullCount P P := by
  rw [tileSum_liftedCount h]
  exact fullCount_eq P (actPartition g P) P

theorem yCount_target_eq {n : ℕ} {Y : Set (Equiv.Perm (Fin n))}
    (h : IsTiling (transpositionsWithOne n) Y) {lam : PartitionShape n}
    (hcontent : 0 ≤ lam.contentSum) (P Q : OrderedSetPartition lam) :
    yCount Y P Q = yCount Y P P := by
  let k := partitionPerm P Q
  let f : Equiv.Perm (Fin n) → ℝ := fun g =>
    liftedCount (Y := Y) P (k * g) - liftedCount (Y := Y) P g
  have hinv : ∀ (g : Equiv.Perm (Fin n)) (i : Fin lam.parts.length) (a b : Fin n),
      a ∈ P.block i → b ∈ P.block i → f (g * Equiv.swap a b) = f g := by
    intro g i a b ha hb
    have hs := actPartition_swap_same_block P i ha hb
    simp [f, liftedCount, actPartition_mul, hs]
  have hzero : ∀ g, tileSum n f g = 0 := by
    intro g
    change tileSum n (fun x =>
      liftedCount (Y := Y) P (k * x) - liftedCount (Y := Y) P x) g = 0
    rw [tileSum_sub]
    have htranslate :
        tileSum n (fun x => liftedCount (Y := Y) P (k * x)) g =
          tileSum n (liftedCount (Y := Y) P) (k * g) := by
      simp [tileSum, mul_assoc]
    rw [htranslate, tileSum_liftedCount_const h, tileSum_liftedCount_const h, sub_self]
  have hf := tileSum_eq_zero_imp P hcontent f hinv hzero
  have h1 := congrFun hf 1
  have hk : actPartition k P = Q :=
    (sendsPartition_iff k P Q).mp (partitionPerm_sends P Q)
  have hsub : yCount Y P Q - yCount Y P P = 0 := by
    simpa [f, liftedCount, k, hk] using h1
  exact sub_eq_zero.mp hsub

theorem sum_yCount {n : ℕ} (Y : Set (Equiv.Perm (Fin n)))
    {lam : PartitionShape n} (P : OrderedSetPartition lam) :
    (∑ Q : OrderedSetPartition lam, yCount Y P Q) = (Fintype.card Y : ℝ) := by
  unfold yCount
  rw [Finset.sum_comm]
  calc
    _ = ∑ _y : Y, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro y _
      simp only [sendsPartition_iff]
      letI : DecidableEq (OrderedSetPartition lam) := Classical.decEq _
      calc
        (∑ Q : OrderedSetPartition lam,
            propIndicator (actPartition (y : Equiv.Perm (Fin n)) P = Q)) =
            ∑ Q : OrderedSetPartition lam,
              if actPartition (y : Equiv.Perm (Fin n)) P = Q then (1 : ℝ) else 0 := by
          apply Finset.sum_congr rfl
          intro Q _
          by_cases hQ : actPartition (y : Equiv.Perm (Fin n)) P = Q <;>
            simp [propIndicator, hQ]
        _ = 1 := Fintype.sum_ite_eq
          (actPartition (y : Equiv.Perm (Fin n)) P) (fun _ => (1 : ℝ))
    _ = _ := by simp

theorem yCount_source_eq {n : ℕ} {Y : Set (Equiv.Perm (Fin n))}
    (h : IsTiling (transpositionsWithOne n) Y) {lam : PartitionShape n}
    (hcontent : 0 ≤ lam.contentSum) (P R : OrderedSetPartition lam) :
    yCount Y P P = yCount Y R R := by
  have hp : (Fintype.card (OrderedSetPartition lam) : ℝ) * yCount Y P P =
      (Fintype.card Y : ℝ) := by
    calc
      _ = ∑ _Q : OrderedSetPartition lam, yCount Y P P := by simp
      _ = ∑ Q : OrderedSetPartition lam, yCount Y P Q := by
        apply Finset.sum_congr rfl
        intro Q _
        exact (yCount_target_eq h hcontent P Q).symm
      _ = _ := sum_yCount Y P
  have hr : (Fintype.card (OrderedSetPartition lam) : ℝ) * yCount Y R R =
      (Fintype.card Y : ℝ) := by
    calc
      _ = ∑ _Q : OrderedSetPartition lam, yCount Y R R := by simp
      _ = ∑ Q : OrderedSetPartition lam, yCount Y R Q := by
        apply Finset.sum_congr rfl
        intro Q _
        exact (yCount_target_eq h hcontent R Q).symm
      _ = _ := sum_yCount Y R
  have hcardNat : 0 < Fintype.card (OrderedSetPartition lam) :=
    Fintype.card_pos_iff.mpr ⟨P⟩
  have hcard : (0 : ℝ) < Fintype.card (OrderedSetPartition lam) := by
    exact_mod_cast hcardNat
  nlinarith

theorem yCount_uniform {n : ℕ} {Y : Set (Equiv.Perm (Fin n))}
    (h : IsTiling (transpositionsWithOne n) Y) {lam : PartitionShape n}
    (hcontent : 0 ≤ lam.contentSum) (P Q R S : OrderedSetPartition lam) :
    yCount Y P Q = yCount Y R S := by
  calc
    yCount Y P Q = yCount Y P P := yCount_target_eq h hcontent P Q
    _ = yCount Y R R := yCount_source_eq h hcontent P R
    _ = yCount Y R S := (yCount_target_eq h hcontent R S).symm

theorem yCount_eq_ncard {n : ℕ} (Y : Set (Equiv.Perm (Fin n)))
    {lam : PartitionShape n} (P Q : OrderedSetPartition lam) :
    yCount Y P Q =
      ({σ : Equiv.Perm (Fin n) | σ ∈ Y ∧ SendsPartition σ P Q}.ncard : ℝ) := by
  let A : Set (Equiv.Perm (Fin n)) :=
    {σ : Equiv.Perm (Fin n) | σ ∈ Y ∧ SendsPartition σ P Q}
  let B : Set Y := {y : Y | SendsPartition (y : Equiv.Perm (Fin n)) P Q}
  have hBA : B.ncard = A.ncard := by
    have h := Set.ncard_subtype (fun σ : Equiv.Perm (Fin n) => σ ∈ Y)
      {σ : Equiv.Perm (Fin n) | SendsPartition σ P Q}
    calc
      B.ncard =
          ({σ : Equiv.Perm (Fin n) | SendsPartition σ P Q} ∩ Y).ncard := by
        simpa [B] using h
      _ = A.ncard := by
        congr 1
        ext σ
        simp [A, and_comm]
  calc
    yCount Y P Q = (B.ncard : ℝ) := by
      unfold yCount
      unfold propIndicator
      rw [Finset.sum_boole]
      congr 1
      rw [Set.ncard_eq_toFinset_card]
      congr 1
      ext y
      simp [B]
    _ = (A.ncard : ℝ) := by rw [hBA]
    _ = _ := rfl

end

end Submission.Helpers
