import ChallengeDeps

open LeanEval.Algebra
open Polynomial
open scoped Classical

namespace Submission.Helpers

/-- The possible zero pattern of the values of a Sturm sequence at one
point.  The first value is nonzero, and every zero after it is isolated
between values of opposite signs. -/
inductive EvalGood : List ℝ → Prop
  | single (x : ℝ) (hx : x ≠ 0) : EvalGood [x]
  | next {x y : ℝ} {xs : List ℝ} (hx : x ≠ 0) (hy : y ≠ 0)
      (tail : EvalGood (y :: xs)) : EvalGood (x :: y :: xs)
  | skip {x z : ℝ} {xs : List ℝ} (hx : x ≠ 0) (hz : z ≠ 0)
      (hxz : x * z < 0) (tail : EvalGood (z :: xs)) :
      EvalGood (x :: 0 :: z :: xs)

/-- `ys` is a nonvanishing perturbation of `xs`: corresponding nonzero
entries have the same sign. -/
inductive Perturbs : List ℝ → List ℝ → Prop
  | nil : Perturbs [] []
  | cons {x y : ℝ} {xs ys : List ℝ} (hy : y ≠ 0)
      (hxy : x ≠ 0 → 0 < x * y) (tail : Perturbs xs ys) :
      Perturbs (x :: xs) (y :: ys)

private lemma mul_neg_iff_of_same_sign {a b c d : ℝ}
    (hac : 0 < a * c) (hbd : 0 < b * d) :
    a * b < 0 ↔ c * d < 0 := by
  rcases (mul_pos_iff.mp hac) with hac | hac
  · rcases (mul_pos_iff.mp hbd) with hbd | hbd
    · constructor
      · exact fun h => (not_lt_of_ge (mul_nonneg hac.1.le hbd.1.le) h).elim
      · exact fun h => (not_lt_of_ge (mul_nonneg hac.2.le hbd.2.le) h).elim
    · constructor
      · exact fun _ => mul_neg_of_pos_of_neg hac.2 hbd.2
      · exact fun _ => mul_neg_of_pos_of_neg hac.1 hbd.1
  · rcases (mul_pos_iff.mp hbd) with hbd | hbd
    · constructor
      · exact fun _ => mul_neg_of_neg_of_pos hac.2 hbd.2
      · exact fun _ => mul_neg_of_neg_of_pos hac.1 hbd.1
    · constructor
      · exact fun h =>
          (not_lt_of_ge (mul_nonneg_of_nonpos_of_nonpos hac.1.le hbd.1.le) h).elim
      · exact fun h =>
          (not_lt_of_ge (mul_nonneg_of_nonpos_of_nonpos hac.2.le hbd.2.le) h).elim

private lemma opposite_edge_count {a b c : ℝ} (hac : a * c < 0) (hb : b ≠ 0) :
    (if a * b < 0 then 1 else 0) + (if b * c < 0 then 1 else 0) = 1 := by
  rcases (mul_neg_iff.mp hac) with ⟨ha, hc⟩ | ⟨ha, hc⟩
  · rcases lt_or_gt_of_ne hb with hb | hb
    · have hab : a * b < 0 := mul_neg_of_pos_of_neg ha hb
      have hbc : ¬b * c < 0 :=
        not_lt_of_ge (mul_nonneg_of_nonpos_of_nonpos hb.le hc.le)
      simp [hab, hbc]
    · have hab : ¬a * b < 0 := not_lt_of_ge (mul_nonneg ha.le hb.le)
      have hbc : b * c < 0 := mul_neg_of_pos_of_neg hb hc
      simp [hab, hbc]
  · rcases lt_or_gt_of_ne hb with hb | hb
    · have hab : ¬a * b < 0 :=
        not_lt_of_ge (mul_nonneg_of_nonpos_of_nonpos ha.le hb.le)
      have hbc : b * c < 0 := mul_neg_of_neg_of_pos hb hc
      simp [hab, hbc]
    · have hab : a * b < 0 := mul_neg_of_neg_of_pos ha hb
      have hbc : ¬b * c < 0 := not_lt_of_ge (mul_nonneg hb.le hc.le)
      simp [hab, hbc]

private lemma signChanges_cons_cons {x y : ℝ} {xs : List ℝ}
    (hx : x ≠ 0) (hy : y ≠ 0) :
    signChanges (x :: y :: xs) =
      (if x * y < 0 then 1 else 0) + signChanges (y :: xs) := by
  by_cases hxy : x * y < 0 <;>
    simp [signChanges, hx, hy, hxy, Nat.add_comm]

private lemma signChanges_skip {x z : ℝ} {xs : List ℝ}
    (hx : x ≠ 0) (hz : z ≠ 0) (hxz : x * z < 0) :
    signChanges (x :: 0 :: z :: xs) = 1 + signChanges (z :: xs) := by
  simp [signChanges, hx, hz, hxz, Nat.add_comm]

theorem EvalGood.signChanges_eq_of_perturbs {xs ys : List ℝ}
    (hxs : EvalGood xs) (hxy : Perturbs xs ys) :
    signChanges xs = signChanges ys := by
  induction hxs generalizing ys with
  | single x hx =>
      cases hxy with
      | cons hy _ tail =>
          cases tail
          simp [signChanges, hx, hy]
  | @next x y xs hx hy tail ih =>
      cases hxy with
      | cons hx' hxx' htail =>
          cases htail with
          | cons hy' hyy' hrest =>
              rw [signChanges_cons_cons hx hy, signChanges_cons_cons hx' hy']
              rw [ih (Perturbs.cons hy' hyy' hrest)]
              simp only [mul_neg_iff_of_same_sign (hxx' hx) (hyy' hy)]
  | @skip x z xs hx hz hxz tail ih =>
      cases hxy with
      | cons hx' hxx' htail =>
          cases htail with
          | cons hzero' _ htail' =>
              cases htail' with
              | cons hz' hzz' hrest =>
                  rw [signChanges_skip hx hz hxz]
                  rw [signChanges_cons_cons hx' hzero',
                    signChanges_cons_cons hzero' hz']
                  rw [ih (Perturbs.cons hz' hzz' hrest)]
                  have hxz' : _ * _ < (0 : ℝ) :=
                    (mul_neg_iff_of_same_sign (hxx' hx) (hzz' hz)).mp hxz
                  have hedges := opposite_edge_count hxz' hzero'
                  omega

/-- Structural invariant of a coprime polynomial remainder sequence. -/
def PRS : List ℝ[X] → Prop
  | [] => False
  | [p] => IsUnit p
  | p :: q :: qs =>
      p ≠ 0 ∧ IsCoprime p q ∧ PRS (q :: qs) ∧
        match qs with
        | [] => True
        | r :: _ => r = -(p % q)

private lemma isCoprime_mod_neg {p q : ℝ[X]} (h : IsCoprime p q) :
    IsCoprime q (-(p % q)) := by
  apply IsCoprime.neg_right
  apply IsCoprime.symm
  simpa only [EuclideanDomain.mod_eq_sub_mul_div] using
    (show IsCoprime (p - q * (p / q)) q from
      (IsCoprime.sub_mul_left_left_iff (x := p) (y := q) (z := p / q)).mpr h)

private lemma natDegree_neg_mod_lt {p q : ℝ[X]} (hq : q ≠ 0)
    (hmod : -(p % q) ≠ 0) :
    (-(p % q)).natDegree < q.natDegree := by
  apply (natDegree_lt_iff_degree_lt hmod).mpr
  simpa [degree_eq_natDegree hq] using degree_mod_lt p hq

theorem prs_sturmAux {p q : ℝ[X]} {n : ℕ} (hpq : IsCoprime p q)
    (hdeg : q = 0 ∨ q.natDegree < p.natDegree)
    (hfuel : p.natDegree < n) :
    PRS (sturmAux p q n) := by
  induction n using Nat.strong_induction_on generalizing p q with
  | h n ih =>
      cases n with
      | zero => omega
      | succ k =>
          by_cases hq : q = 0
          · have hpunit : IsUnit p := by
              rw [hq] at hpq
              exact isCoprime_zero_right.mp hpq
            simp [sturmAux, hq, PRS, hpunit]
          · have hqdeg : q.natDegree < p.natDegree := hdeg.resolve_left hq
            have hp0 : p ≠ 0 := by
              intro hp
              subst p
              simp at hqdeg
            have hqfuel : q.natDegree < k := by omega
            let r : ℝ[X] := -(p % q)
            have hqr : IsCoprime q r := by
              simpa [r] using isCoprime_mod_neg hpq
            have hrdeg : r = 0 ∨ r.natDegree < q.natDegree := by
              by_cases hr : r = 0
              · exact Or.inl hr
              · exact Or.inr (natDegree_neg_mod_lt hq hr)
            have htail : PRS (sturmAux q r k) :=
              ih k (Nat.lt_succ_self k) hqr hrdeg hqfuel
            have hk : k ≠ 0 := by omega
            obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
            rw [sturmAux, if_neg hq]
            change PRS (p :: sturmAux q r (Nat.succ l))
            by_cases hr : r = 0
            · rw [sturmAux, if_pos hr]
              exact ⟨hp0, hpq, by simpa [sturmAux, hr] using htail, trivial⟩
            · rw [sturmAux, if_neg hr] at htail ⊢
              refine ⟨hp0, hpq, htail, ?_⟩
              cases l with
              | zero => rfl
              | succ l =>
                  by_cases hs : -(q % r) = 0
                  · simp [sturmAux, hs, r]
                  · simp [sturmAux, hs, r]

theorem prs_sturmChain {p : ℝ[X]} (hp : Squarefree p) :
    PRS (sturmChain p) := by
  have hsep : p.Separable := PerfectField.separable_iff_squarefree.mpr hp
  have hdeg : p.derivative = 0 ∨ p.derivative.natDegree < p.natDegree := by
    by_cases hd : p.derivative = 0
    · exact Or.inl hd
    · exact Or.inr (natDegree_derivative_lt (Polynomial.derivative_ne_zero.mp hd))
  exact prs_sturmAux hsep hdeg (by omega)

theorem PRS.evalGood {ps : List ℝ[X]} (hps : PRS ps) {p : ℝ[X]}
    {rest : List ℝ[X]} (hshape : ps = p :: rest) {x : ℝ}
    (hpx : p.eval x ≠ 0) :
    EvalGood (ps.map fun q => q.eval x) := by
  subst ps
  induction rest using List.twoStepInduction generalizing p with
  | nil =>
      exact EvalGood.single _ hpx
  | singleton q =>
      have hqunit : IsUnit q := by
        simpa [PRS] using hps.2.2.1
      have hqx : q.eval x ≠ 0 :=
        (hqunit.map (evalRingHom x)).ne_zero
      exact EvalGood.next hpx hqx (EvalGood.single _ hqx)
  | cons_cons q r rs ih0 ih1 =>
      have hpq : IsCoprime p q := hps.2.1
      have htail : PRS (q :: r :: rs) := hps.2.2.1
      have hr : r = -(p % q) := by
        simpa [PRS] using hps.2.2.2
      by_cases hqx : q.eval x = 0
      · have hmod : (p % q).eval x = p.eval x := by
          rw [EuclideanDomain.mod_eq_sub_mul_div, eval_sub, eval_mul, hqx,
            zero_mul, sub_zero]
        have hrx : r.eval x = -p.eval x := by
          rw [hr, eval_neg, hmod]
        have hrx0 : r.eval x ≠ 0 := by
          rw [hrx]
          exact neg_ne_zero.mpr hpx
        have hpr : p.eval x * r.eval x < 0 := by
          rw [hrx]
          rw [mul_neg, neg_lt_zero]
          simpa [pow_two] using sq_pos_of_ne_zero hpx
        have hrrs : PRS (r :: rs) := by
          simpa [PRS] using htail.2.2.1
        simpa only [List.map_cons, hqx] using
          EvalGood.skip hpx hrx0 hpr (ih0 hrx0 hrrs)
      · exact EvalGood.next hpx hqx
          (ih1 r hqx htail)

theorem sturmChain_evalGood {p : ℝ[X]} (hp : Squarefree p) {x : ℝ}
    (hpx : p.eval x ≠ 0) :
    EvalGood ((sturmChain p).map fun q => q.eval x) := by
  have hshape : ∃ rest, sturmChain p = p :: rest := by
    unfold sturmChain
    rw [show p.natDegree + 2 = Nat.succ (p.natDegree + 1) by omega, sturmAux]
    split
    · exact ⟨[], rfl⟩
    · exact ⟨_, rfl⟩
  obtain ⟨rest, hshape⟩ := hshape
  exact (prs_sturmChain hp).evalGood hshape hpx

theorem PRS.forall_ne_zero {ps : List ℝ[X]} (hps : PRS ps) :
    ps.Forall (· ≠ 0) := by
  induction ps using List.twoStepInduction with
  | nil => simp [PRS] at hps
  | singleton p =>
      simpa using (IsUnit.ne_zero hps)
  | cons_cons p q qs _ ih =>
      simpa only [List.forall_cons] using And.intro hps.1 (ih q hps.2.2.1)

/-- The finite set of all real roots occurring in a polynomial list. -/
noncomputable def rootsOfList : List ℝ[X] → Finset ℝ
  | [] => ∅
  | p :: ps => p.roots.toFinset ∪ rootsOfList ps

theorem mem_rootsOfList_iff {ps : List ℝ[X]} (hps : ps.Forall (· ≠ 0))
    {x : ℝ} :
    x ∈ rootsOfList ps ↔ ∃ p ∈ ps, p.eval x = 0 := by
  induction ps with
  | nil => simp [rootsOfList]
  | cons p ps ih =>
      rw [List.forall_cons] at hps
      have hp0 : p ≠ 0 := hps.1
      have ht := hps.2
      simp only [rootsOfList, Finset.mem_union, Multiset.mem_toFinset,
        Polynomial.mem_roots hp0, Polynomial.IsRoot, List.mem_cons]
      rw [ih ht]
      aesop

private lemma eval_mul_pos_of_no_root {p : ℝ[X]} {x y : ℝ}
    (hxy : x < y) (hx : p.eval x ≠ 0) (hy : p.eval y ≠ 0)
    (hno : ∀ z, x < z → z < y → p.eval z ≠ 0) :
    0 < p.eval x * p.eval y := by
  by_contra h
  have hmul : p.eval x * p.eval y ≤ 0 := le_of_not_gt h
  have hz : (0 : ℝ) ∈ Set.uIcc (p.eval x) (p.eval y) := by
    rw [Set.mem_uIcc]
    rcases (mul_nonpos_iff.mp hmul) with h | h
    · exact Or.inr ⟨h.2, h.1⟩
    · exact Or.inl h
  obtain ⟨z, hzxy, hz0⟩ :=
    (intermediate_value_uIcc p.continuous.continuousOn) hz
  have hzmem : z ∈ Set.Icc x y := by
    simpa [Set.uIcc_of_le hxy.le] using hzxy
  have hzx : x < z := by
    refine lt_of_le_of_ne hzmem.1 ?_
    intro hzx
    apply hx
    simpa [hzx] using hz0
  have hzy : z < y := by
    refine lt_of_le_of_ne hzmem.2 ?_
    intro hzy
    apply hy
    simpa [hzy] using hz0
  exact hno z hzx hzy hz0

theorem perturbs_eval_of_no_roots {ps : List ℝ[X]} {x y : ℝ}
    (hxy : x < y)
    (hy : ∀ p ∈ ps, p.eval y ≠ 0)
    (hno : ∀ p ∈ ps, ∀ z, x < z → z < y → p.eval z ≠ 0) :
    Perturbs (ps.map fun p => p.eval x) (ps.map fun p => p.eval y) := by
  induction ps with
  | nil => exact Perturbs.nil
  | cons p ps ih =>
      apply Perturbs.cons (hy p (by simp))
      · intro hx
        exact eval_mul_pos_of_no_root hxy hx (hy p (by simp))
          (hno p (by simp))
      · exact ih (fun q hq => hy q (by simp [hq]))
          (fun q hq => hno q (by simp [hq]))

theorem perturbs_eval_of_no_roots_rev {ps : List ℝ[X]} {x y : ℝ}
    (hxy : x < y)
    (hx : ∀ p ∈ ps, p.eval x ≠ 0)
    (hno : ∀ p ∈ ps, ∀ z, x < z → z < y → p.eval z ≠ 0) :
    Perturbs (ps.map fun p => p.eval y) (ps.map fun p => p.eval x) := by
  induction ps with
  | nil => exact Perturbs.nil
  | cons p ps ih =>
      apply Perturbs.cons (hx p (by simp))
      · intro hy
        rw [mul_comm]
        exact eval_mul_pos_of_no_root hxy (hx p (by simp)) hy
          (hno p (by simp))
      · exact ih (fun q hq => hx q (by simp [hq]))
          (fun q hq => hno q (by simp [hq]))

private lemma same_sign_trans {a b c : ℝ} (hab : 0 < a * b)
    (hbc : 0 < b * c) : 0 < a * c := by
  rcases (mul_pos_iff.mp hab) with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;>
    rcases (mul_pos_iff.mp hbc) with ⟨_, hc⟩ | ⟨_, hc⟩
  · exact mul_pos ha hc
  · linarith
  · linarith
  · exact mul_pos_of_neg_of_neg ha hc

private lemma factor_at_root {p : ℝ[X]} {r : ℝ} (hr : p.eval r = 0) :
    (X - C r) * (p /ₘ (X - C r)) = p := by
  rw [X_sub_C_mul_divByMonic_eq_sub_modByMonic,
    modByMonic_X_sub_C_eq_C_eval, hr, C_0, sub_zero]

private lemma quotient_eval_root_eq_derivative {p : ℝ[X]} (r : ℝ) :
    (p /ₘ (X - C r)).eval r = p.derivative.eval r := by
  have h := congrArg (fun q : ℝ[X] => q.eval r)
    (divByMonic_add_X_sub_C_mul_derivative_divByMonic_eq_derivative p r)
  simpa using h

private lemma root_crossing_right {p : ℝ[X]} {r y : ℝ}
    (hry : r < y) (hr : p.eval r = 0) (hder : p.derivative.eval r ≠ 0)
    (hy : p.eval y ≠ 0)
    (hno : ∀ z, r < z → z < y → p.eval z ≠ 0) :
    0 < p.eval y * p.derivative.eval r := by
  let q : ℝ[X] := p /ₘ (X - C r)
  have hfac := factor_at_root hr
  have hqr : q.eval r = p.derivative.eval r := by
    simpa [q] using quotient_eval_root_eq_derivative (p := p) r
  have hqr0 : q.eval r ≠ 0 := hqr.symm ▸ hder
  have hqy0 : q.eval y ≠ 0 := by
    intro hqy
    have := congrArg (fun s : ℝ[X] => s.eval y) hfac
    apply hy
    simpa [q, hqy] using this.symm
  have hqno : ∀ z, r < z → z < y → q.eval z ≠ 0 := by
    intro z hrz hzy hqz
    have h := congrArg (fun s : ℝ[X] => s.eval z) hfac
    apply hno z hrz hzy
    simpa [q, hqz] using h.symm
  have hsame : 0 < q.eval r * q.eval y :=
    eval_mul_pos_of_no_root hry hqr0 hqy0 hqno
  have hpy : p.eval y = (y - r) * q.eval y := by
    have h := congrArg (fun s : ℝ[X] => s.eval y) hfac
    simpa [q] using h.symm
  rw [hpy, ← hqr]
  rw [mul_assoc, mul_comm (q.eval y) (q.eval r)]
  exact mul_pos (sub_pos.mpr hry) hsame

private lemma root_crossing_left {p : ℝ[X]} {x r : ℝ}
    (hxr : x < r) (hr : p.eval r = 0) (hder : p.derivative.eval r ≠ 0)
    (hx : p.eval x ≠ 0)
    (hno : ∀ z, x < z → z < r → p.eval z ≠ 0) :
    p.eval x * p.derivative.eval r < 0 := by
  let q : ℝ[X] := p /ₘ (X - C r)
  have hfac := factor_at_root hr
  have hqr : q.eval r = p.derivative.eval r := by
    simpa [q] using quotient_eval_root_eq_derivative (p := p) r
  have hqr0 : q.eval r ≠ 0 := hqr.symm ▸ hder
  have hqx0 : q.eval x ≠ 0 := by
    intro hqx
    have := congrArg (fun s : ℝ[X] => s.eval x) hfac
    apply hx
    simpa [q, hqx] using this.symm
  have hqno : ∀ z, x < z → z < r → q.eval z ≠ 0 := by
    intro z hxz hzr hqz
    have h := congrArg (fun s : ℝ[X] => s.eval z) hfac
    apply hno z hxz hzr
    simpa [q, hqz] using h.symm
  have hsame : 0 < q.eval x * q.eval r :=
    eval_mul_pos_of_no_root hxr hqx0 hqr0 hqno
  have hpx : p.eval x = (x - r) * q.eval x := by
    have h := congrArg (fun s : ℝ[X] => s.eval x) hfac
    simpa [q] using h.symm
  rw [hpx, ← hqr, mul_assoc]
  exact mul_neg_of_neg_of_pos (sub_neg.mpr hxr) hsame

theorem sturmChain_root_tail {p : ℝ[X]} (hp : Squarefree p) {x : ℝ}
    (hpx : p.eval x = 0) :
    ∃ qs : List ℝ[X],
      sturmChain p = p :: p.derivative :: qs ∧
      EvalGood ((p.derivative :: qs).map fun q => q.eval x) := by
  have hsep : p.Separable := PerfectField.separable_iff_squarefree.mpr hp
  have hdx : p.derivative.eval x ≠ 0 :=
    by simpa using hsep.aeval_derivative_ne_zero hpx
  have hd0 : p.derivative ≠ 0 := fun h => hdx (by simp [h])
  let r : ℝ[X] := -(p % p.derivative)
  let tail : List ℝ[X] :=
    sturmAux p.derivative r (p.natDegree + 1)
  have hchain : sturmChain p = p :: tail := by
    simp [sturmChain, sturmAux, hd0, tail, r]
  have htailshape : ∃ qs, tail = p.derivative :: qs := by
    unfold tail
    rw [show p.natDegree + 1 = Nat.succ p.natDegree by omega, sturmAux]
    split
    · exact ⟨[], rfl⟩
    · exact ⟨_, rfl⟩
  obtain ⟨qs, htail⟩ := htailshape
  have htailPRS : PRS (p.derivative :: qs) := by
    have hprs := prs_sturmChain hp
    rw [hchain, htail] at hprs
    exact hprs.2.2.1
  refine ⟨qs, by simp [hchain, htail], ?_⟩
  exact htailPRS.evalGood rfl hdx

theorem sigma_eq_of_no_chain_roots_right {p : ℝ[X]} (hp : Squarefree p)
    {x y : ℝ} (hxy : x < y)
    (hy : ∀ q ∈ sturmChain p, q.eval y ≠ 0)
    (hno : ∀ q ∈ sturmChain p, ∀ z, x < z → z < y → q.eval z ≠ 0) :
    sigma p x = sigma p y := by
  by_cases hpx : p.eval x = 0
  · obtain ⟨qs, hshape, hgood⟩ := sturmChain_root_tail hp hpx
    let tail := p.derivative :: qs
    have htailmem : ∀ q ∈ tail, q ∈ sturmChain p := by
      intro q hq
      rw [hshape]
      simp [tail, hq]
    have hpert :
        Perturbs (tail.map fun q => q.eval x) (tail.map fun q => q.eval y) :=
      perturbs_eval_of_no_roots hxy
        (fun q hq => hy q (htailmem q hq))
        (fun q hq => hno q (htailmem q hq))
    have htail :
        signChanges (tail.map fun q => q.eval x) =
          signChanges (tail.map fun q => q.eval y) :=
      hgood.signChanges_eq_of_perturbs hpert
    have hpy : p.eval y ≠ 0 := hy p (by rw [hshape]; simp)
    have hdx : p.derivative.eval x ≠ 0 := by
      have hsep : p.Separable := PerfectField.separable_iff_squarefree.mpr hp
      simpa using hsep.aeval_derivative_ne_zero hpx
    have hdy : p.derivative.eval y ≠ 0 :=
      hy p.derivative (by rw [hshape]; simp)
    have hcross : 0 < p.eval y * p.derivative.eval x :=
      root_crossing_right hxy hpx hdx hpy
        (fun z hxz hzy => hno p (by rw [hshape]; simp) z hxz hzy)
    have hder : 0 < p.derivative.eval x * p.derivative.eval y :=
      eval_mul_pos_of_no_root hxy hdx hdy
        (fun z hxz hzy => hno p.derivative (by rw [hshape]; simp) z hxz hzy)
    have hfirst : 0 < p.eval y * p.derivative.eval y :=
      same_sign_trans hcross hder
    unfold sigma
    rw [hshape]
    simp only [List.map_cons]
    rw [hpx]
    have hzero :
        signChanges (0 :: tail.map fun q => q.eval x) =
          signChanges (tail.map fun q => q.eval x) := by
      simp [signChanges]
    dsimp [tail] at hzero htail
    rw [hzero, signChanges_cons_cons hpy hdy]
    simp only [not_lt_of_ge hfirst.le, ↓reduceIte, zero_add]
    exact htail
  · unfold sigma
    exact (sturmChain_evalGood hp hpx).signChanges_eq_of_perturbs
      (perturbs_eval_of_no_roots hxy hy hno)

theorem sigma_eq_add_root_of_no_chain_roots_left {p : ℝ[X]}
    (hp : Squarefree p) {x y : ℝ} (hxy : x < y)
    (hx : ∀ q ∈ sturmChain p, q.eval x ≠ 0)
    (hno : ∀ q ∈ sturmChain p, ∀ z, x < z → z < y → q.eval z ≠ 0) :
    sigma p x = sigma p y + if p.eval y = 0 then 1 else 0 := by
  by_cases hpy : p.eval y = 0
  · obtain ⟨qs, hshape, hgood⟩ := sturmChain_root_tail hp hpy
    let tail := p.derivative :: qs
    have htailmem : ∀ q ∈ tail, q ∈ sturmChain p := by
      intro q hq
      rw [hshape]
      simp [tail, hq]
    have hpert :
        Perturbs (tail.map fun q => q.eval y) (tail.map fun q => q.eval x) :=
      perturbs_eval_of_no_roots_rev hxy
        (fun q hq => hx q (htailmem q hq))
        (fun q hq => hno q (htailmem q hq))
    have htail :
        signChanges (tail.map fun q => q.eval y) =
          signChanges (tail.map fun q => q.eval x) :=
      hgood.signChanges_eq_of_perturbs hpert
    have hpx : p.eval x ≠ 0 := hx p (by rw [hshape]; simp)
    have hdx : p.derivative.eval x ≠ 0 :=
      hx p.derivative (by rw [hshape]; simp)
    have hdy : p.derivative.eval y ≠ 0 := by
      have hsep : p.Separable := PerfectField.separable_iff_squarefree.mpr hp
      simpa using hsep.aeval_derivative_ne_zero hpy
    have hcross : p.eval x * p.derivative.eval y < 0 :=
      root_crossing_left hxy hpy hdy hpx
        (fun z hxz hzy => hno p (by rw [hshape]; simp) z hxz hzy)
    have hder : 0 < p.derivative.eval x * p.derivative.eval y :=
      eval_mul_pos_of_no_root hxy hdx hdy
        (fun z hxz hzy => hno p.derivative (by rw [hshape]; simp) z hxz hzy)
    have hsq : 0 < p.eval x * p.eval x := by
      simpa [pow_two] using sq_pos_of_ne_zero hpx
    have hfirst : p.eval x * p.derivative.eval x < 0 := by
      apply (mul_neg_iff_of_same_sign hsq ?_).mpr hcross
      simpa [mul_comm] using hder
    unfold sigma
    rw [hshape]
    simp only [List.map_cons]
    rw [hpy]
    have hzero :
        signChanges (0 :: tail.map fun q => q.eval y) =
          signChanges (tail.map fun q => q.eval y) := by
      simp [signChanges]
    dsimp [tail] at hzero htail
    rw [hzero, signChanges_cons_cons hpx hdx, if_pos hfirst, htail]
    simp [add_comm]
  · have hpert :=
        perturbs_eval_of_no_roots_rev (ps := sturmChain p) hxy hx hno
    have heq :
        signChanges ((sturmChain p).map fun q => q.eval y) =
          signChanges ((sturmChain p).map fun q => q.eval x) :=
      (sturmChain_evalGood hp hpy).signChanges_eq_of_perturbs hpert
    unfold sigma
    simpa [hpy] using heq.symm

theorem sigma_segment {p : ℝ[X]} (hp : Squarefree p) {x y : ℝ}
    (hxy : x < y)
    (hno : ∀ z, x < z → z < y → z ∉ rootsOfList (sturmChain p)) :
    sigma p x = sigma p y + if p.eval y = 0 then 1 else 0 := by
  let m : ℝ := (x + y) / 2
  have hxm : x < m := by
    dsimp [m]
    linarith
  have hmy : m < y := by
    dsimp [m]
    linarith
  have hall : (sturmChain p).Forall (· ≠ 0) :=
    (prs_sturmChain hp).forall_ne_zero
  have hm : ∀ q ∈ sturmChain p, q.eval m ≠ 0 := by
    intro q hq hqm
    apply hno m hxm hmy
    exact (mem_rootsOfList_iff hall).mpr ⟨q, hq, hqm⟩
  have hleft :
      sigma p x = sigma p m :=
    sigma_eq_of_no_chain_roots_right hp hxm hm
      (fun q hq z hxz hzm hqz =>
        hno z hxz (hzm.trans hmy)
          ((mem_rootsOfList_iff hall).mpr ⟨q, hq, hqz⟩))
  have hright :
      sigma p m = sigma p y + if p.eval y = 0 then 1 else 0 :=
    sigma_eq_add_root_of_no_chain_roots_left hp hmy hm
      (fun q hq z hmz hzy hqz =>
        hno z (hxm.trans hmz) hzy
          ((mem_rootsOfList_iff hall).mpr ⟨q, hq, hqz⟩))
  exact hleft.trans hright

private theorem self_mem_sturmChain (p : ℝ[X]) : p ∈ sturmChain p := by
  unfold sturmChain
  rw [show p.natDegree + 2 = Nat.succ (p.natDegree + 1) by omega, sturmAux]
  split <;> simp

private theorem squarefree_ne_zero {p : ℝ[X]} (hp : Squarefree p) : p ≠ 0 := by
  have hsep : p.Separable := PerfectField.separable_iff_squarefree.mpr hp
  intro hp0
  subst p
  exact Polynomial.not_separable_zero hsep

noncomputable def chainEvents (p : ℝ[X]) (x y : ℝ) : Finset ℝ :=
  (rootsOfList (sturmChain p)).filter fun z => x < z ∧ z ≤ y

noncomputable def rootsIoc (p : ℝ[X]) (x y : ℝ) : Finset ℝ :=
  p.roots.toFinset.filter fun z => x < z ∧ z ≤ y

theorem sigma_eq_add_card_rootsIoc {p : ℝ[X]} (hp : Squarefree p)
    {x y : ℝ} (hxy : x < y) :
    sigma p x = sigma p y + (rootsIoc p x y).card := by
  classical
  have hp0 : p ≠ 0 := squarefree_ne_zero hp
  have hall : (sturmChain p).Forall (· ≠ 0) :=
    (prs_sturmChain hp).forall_ne_zero
  have hp_mem : p ∈ sturmChain p := self_mem_sturmChain p
  have root_mem_event {u v z : ℝ} (hz : p.eval z = 0)
      (hu : u < z) (hv : z ≤ v) :
      z ∈ chainEvents p u v := by
    apply Finset.mem_filter.mpr
    refine ⟨(mem_rootsOfList_iff hall).mpr ⟨p, hp_mem, hz⟩, hu, hv⟩
  let statement := fun (n : ℕ) =>
    ∀ x y : ℝ, x < y → (chainEvents p x y).card = n →
      sigma p x = sigma p y + (rootsIoc p x y).card
  have main : ∀ n, statement n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro x y hxy hcard
        let E := chainEvents p x y
        by_cases hE : E = ∅
        · have hno : ∀ z, x < z → z < y →
              z ∉ rootsOfList (sturmChain p) := by
            intro z hxz hzy hz
            have : z ∈ E := Finset.mem_filter.mpr ⟨hz, hxz, hzy.le⟩
            simp [hE] at this
          have hseg := sigma_segment hp hxy hno
          have hroots :
              (rootsIoc p x y).card =
                if p.eval y = 0 then 1 else 0 := by
            by_cases hy : p.eval y = 0
            · have hyroots : y ∈ rootsIoc p x y := by
                exact Finset.mem_filter.mpr
                  ⟨by simpa [Polynomial.mem_roots hp0, Polynomial.IsRoot] using hy,
                    hxy, le_rfl⟩
              have herase : (rootsIoc p x y).erase y = ∅ := by
                apply Finset.eq_empty_iff_forall_notMem.mpr
                intro z hz
                have hz' := Finset.mem_erase.mp hz
                have hzroot := (Finset.mem_filter.mp hz'.2)
                have hzeval : p.eval z = 0 := by
                  simpa [Polynomial.mem_roots hp0, Polynomial.IsRoot] using hzroot.1
                have hzy : z < y := lt_of_le_of_ne hzroot.2.2 hz'.1
                exact hno z hzroot.2.1 hzy
                  ((mem_rootsOfList_iff hall).mpr ⟨p, hp_mem, hzeval⟩)
              rw [← Finset.card_erase_add_one hyroots, herase]
              simp [hy]
            · have hempty : rootsIoc p x y = ∅ := by
                apply Finset.eq_empty_iff_forall_notMem.mpr
                intro z hz
                have hzroot := Finset.mem_filter.mp hz
                have hzeval : p.eval z = 0 := by
                  simpa [Polynomial.mem_roots hp0, Polynomial.IsRoot] using hzroot.1
                by_cases hzy : z = y
                · exact hy (hzy ▸ hzeval)
                · have hzlt : z < y := lt_of_le_of_ne hzroot.2.2 hzy
                  exact hno z hzroot.2.1 hzlt
                    ((mem_rootsOfList_iff hall).mpr ⟨p, hp_mem, hzeval⟩)
              simp [hempty, hy]
          simpa [hroots] using hseg
        · have hEnon : E.Nonempty := Finset.nonempty_iff_ne_empty.mpr hE
          let r : ℝ := E.min' hEnon
          have hrE : r ∈ E := Finset.min'_mem E hEnon
          have hrange : x < r ∧ r ≤ y := (Finset.mem_filter.mp hrE).2
          have hno : ∀ z, x < z → z < r →
              z ∉ rootsOfList (sturmChain p) := by
            intro z hxz hzr hz
            have hzE : z ∈ E :=
              Finset.mem_filter.mpr ⟨hz, hxz, hzr.le.trans hrange.2⟩
            exact (not_le_of_gt hzr) (Finset.min'_le E z hzE)
          have hseg :
              sigma p x = sigma p r + if p.eval r = 0 then 1 else 0 :=
            sigma_segment hp hrange.1 hno
          let Er := chainEvents p r y
          let R := rootsIoc p x y
          let Rr := rootsIoc p r y
          have hEsub : Er ⊂ E := by
            constructor
            · intro z hz
              have hz' := Finset.mem_filter.mp hz
              exact Finset.mem_filter.mpr
                ⟨hz'.1, hrange.1.trans hz'.2.1, hz'.2.2⟩
            · intro hsub
              have : r ∈ Er := hsub hrE
              exact (Finset.mem_filter.mp this).2.1.false
          have hEcard : Er.card < n := by
            rw [← hcard]
            exact Finset.card_lt_card hEsub
          have hrec :
              sigma p r = sigma p y + Rr.card := by
            rcases hrange.2.eq_or_lt with hry | hry
            · have hsigma : sigma p r = sigma p y :=
                congrArg (sigma p) hry
              have hRrempty : Rr = ∅ := by
                apply Finset.eq_empty_iff_forall_notMem.mpr
                intro z hz
                have hz' := Finset.mem_filter.mp hz
                exact (not_lt_of_ge (hry.symm ▸ hz'.2.2)) hz'.2.1
              simpa [hRrempty] using hsigma
            · exact ih Er.card hEcard r y hry rfl
          have hRcard :
              R.card = Rr.card + if p.eval r = 0 then 1 else 0 := by
            by_cases hpr : p.eval r = 0
            · have hrR : r ∈ R := by
                exact Finset.mem_filter.mpr
                  ⟨by simpa [Polynomial.mem_roots hp0, Polynomial.IsRoot] using hpr,
                    hrange⟩
              have herase : R.erase r = Rr := by
                ext z
                constructor
                · intro hz
                  have hz' := Finset.mem_erase.mp hz
                  have hzR := Finset.mem_filter.mp hz'.2
                  have hzeval : p.eval z = 0 := by
                    simpa [Polynomial.mem_roots hp0, Polynomial.IsRoot] using hzR.1
                  have hzE : z ∈ E := root_mem_event hzeval hzR.2.1 hzR.2.2
                  have hrz : r < z :=
                    lt_of_le_of_ne (Finset.min'_le E z hzE) (Ne.symm hz'.1)
                  exact Finset.mem_filter.mpr ⟨hzR.1, hrz, hzR.2.2⟩
                · intro hz
                  have hzR := Finset.mem_filter.mp hz
                  apply Finset.mem_erase.mpr
                  exact ⟨(ne_of_lt hzR.2.1).symm, Finset.mem_filter.mpr
                    ⟨hzR.1, hrange.1.trans hzR.2.1, hzR.2.2⟩⟩
              rw [← Finset.card_erase_add_one hrR, herase]
              simp [hpr, Rr]
            · have hEq : R = Rr := by
                ext z
                constructor
                · intro hz
                  have hzR := Finset.mem_filter.mp hz
                  have hzeval : p.eval z = 0 := by
                    simpa [Polynomial.mem_roots hp0, Polynomial.IsRoot] using hzR.1
                  have hzE : z ∈ E := root_mem_event hzeval hzR.2.1 hzR.2.2
                  have hrzle : r ≤ z := Finset.min'_le E z hzE
                  have hrz : r < z := lt_of_le_of_ne hrzle fun h =>
                    hpr (h.symm ▸ hzeval)
                  exact Finset.mem_filter.mpr ⟨hzR.1, hrz, hzR.2.2⟩
                · intro hz
                  have hzR := Finset.mem_filter.mp hz
                  exact Finset.mem_filter.mpr
                    ⟨hzR.1, hrange.1.trans hzR.2.1, hzR.2.2⟩
              simp [hEq, hpr]
          rw [hseg, hrec, hRcard]
          omega
  exact main (chainEvents p x y).card x y hxy rfl

end Submission.Helpers
