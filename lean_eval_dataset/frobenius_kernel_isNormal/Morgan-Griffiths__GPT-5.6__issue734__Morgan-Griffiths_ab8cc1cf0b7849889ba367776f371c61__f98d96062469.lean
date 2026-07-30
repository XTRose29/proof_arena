import Mathlib

-- BEGIN INLINED FILE: Mathlib/Support/frobenius_kernel_isNormal_bde655671f/Basic.lean

open Set

/-!
Elementary bookkeeping for the set which occurs in the Frobenius kernel
problem.  None of the group theoretic (hard) closure assertion is used here.
It is useful to keep these lemmas separate: inverse closure and conjugation
invariance of this set do *not* require Frobenius' theorem.
-/

namespace FrobeniusKernel

variable (G X : Type*) [Group G] [MulAction G X]

/-- The set consisting of the identity and of the fixed-point free elements
of an action.  This is the prospective Frobenius kernel; it makes sense for
any action. -/
def kerSet : Set G := {1} ∪ {g : G | ∀ x : X, g • x ≠ x}

@[simp] lemma mem_kerSet (g : G) :
    g ∈ kerSet G X ↔ g = 1 ∨ ∀ x : X, g • x ≠ x := by
  constructor
  · intro h
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr h
  · intro h
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr h

@[simp] lemma one_mem_kerSet : (1 : G) ∈ kerSet G X := by
  exact (mem_kerSet G X 1).2 (Or.inl rfl)

/-- An inverse has exactly the same fixed points. -/
lemma inv_fixes_iff (g : G) (x : X) :
    g⁻¹ • x = x ↔ g • x = x := by
  constructor
  · intro h
    calc
      g • x = g • (g⁻¹ • x) := by rw [h]
      _ = x := by simp [smul_smul]
  · intro h
    calc
      g⁻¹ • x = g⁻¹ • (g • x) := by rw [h]
      _ = x := by simp [smul_smul]

lemma inv_mem_kerSet {g : G} (h : g ∈ kerSet G X) :
    g⁻¹ ∈ kerSet G X := by
  rcases (mem_kerSet G X g).1 h with h1 | hfree
  · subst g
    simpa using (one_mem_kerSet G X)
  · apply (mem_kerSet G X g⁻¹).2
    refine Or.inr ?_
    intro x hx
    exact hfree x ((inv_fixes_iff G X g x).1 hx)

@[simp] lemma inv_mem_kerSet_iff (g : G) :
    g⁻¹ ∈ kerSet G X ↔ g ∈ kerSet G X := by
  constructor
  · intro h
    have h' := inv_mem_kerSet G X h
    simpa using h'
  · exact inv_mem_kerSet G X

/-- Fixed-point freeness is unchanged by conjugation.  This is the easy
`Normal` part of the Frobenius kernel; it holds without any hypotheses on
point stabilizers. -/
lemma conj_mem_kerSet {a : G} (ha : a ∈ kerSet G X) (c : G) :
    c * a * c⁻¹ ∈ kerSet G X := by
  rcases (mem_kerSet G X a).1 ha with ha1 | hfree
  · subst a
    simpa using (one_mem_kerSet G X)
  · apply (mem_kerSet G X (c * a * c⁻¹)).2
    refine Or.inr ?_
    intro x hx
    have hx' : a • (c⁻¹ • x) = (c⁻¹ • x) := by
      have := congrArg (fun z : X => c⁻¹ • z) hx
      -- associativity of the action makes the conjugates cancel
      simpa [smul_smul, mul_assoc] using this
    exact hfree (c⁻¹ • x) hx'

/-- If the one genuinely difficult multiplication-closure assertion holds,
the Frobenius set is a subgroup.  Inverse closure is automatic. -/
def kerSubgroup
    (hmul : ∀ a b : G, a ∈ kerSet G X → b ∈ kerSet G X →
      a * b ∈ kerSet G X) : Subgroup G where
  carrier := kerSet G X
  one_mem' := one_mem_kerSet G X
  mul_mem' := by
    intro a b ha hb
    exact hmul a b ha hb
  inv_mem' := by
    intro a ha
    exact inv_mem_kerSet G X ha

@[simp] lemma mem_kerSubgroup
    (hmul : ∀ a b : G, a ∈ kerSet G X → b ∈ kerSet G X →
      a * b ∈ kerSet G X) (g : G) :
    g ∈ kerSubgroup G X hmul ↔ g ∈ kerSet G X := Iff.rfl

/-- Normality follows formally from conjugation invariance, once closure
has been established. -/
lemma kerSubgroup_normal
    (hmul : ∀ a b : G, a ∈ kerSet G X → b ∈ kerSet G X →
      a * b ∈ kerSet G X) :
    (kerSubgroup G X hmul).Normal := by
  constructor
  intro n hn g
  exact conj_mem_kerSet G X hn g

/-- A convenient reduction of the desired existence statement. -/
lemma exists_normal_of_mul_closed
    (hmul : ∀ a b : G, a ∈ kerSet G X → b ∈ kerSet G X →
      a * b ∈ kerSet G X) :
    ∃ N : Subgroup G, N.Normal ∧
      (N : Set G) = ({1} ∪ {g : G | ∀ x : X, g • x ≠ x}) := by
  refine ⟨kerSubgroup G X hmul, kerSubgroup_normal G X hmul, ?_⟩
  rfl

end FrobeniusKernel

-- END INLINED FILE: Mathlib/Support/frobenius_kernel_isNormal_bde655671f/Basic.lean

-- BEGIN INLINED FILE: Mathlib/Support/frobenius_kernel_isNormal_bde655671f/Trace.lean
open scoped BigOperators Classical
open Module Polynomial
noncomputable section
namespace FrobeniusKernel
-- two analytic observations used in converting equality of a character value
-- into membership of the kernel.  They are independent of any chosen basis.
lemma root_re_le_one {z : ℂ} {n : ℕ} (hn : n ≠ 0) (hz : z ^ n = 1) :
    z.re ≤ 1 := by
  have hnorm : ‖z‖ = (1:ℝ) := Complex.norm_eq_one_of_pow_eq_one hz hn
  simpa [hnorm] using Complex.re_le_norm z

lemma root_eq_one_of_re {z : ℂ} {n : ℕ} (hn : n ≠ 0)
    (hz : z ^ n = 1) (hre : z.re = 1) : z = 1 := by
  have hnorm : ‖z‖ = (1:ℝ) := Complex.norm_eq_one_of_pow_eq_one hz hn
  have hsq : Complex.normSq z = (1:ℝ) := by
    rw [← Complex.sq_norm, hnorm]
    norm_num
  have him : z.im = 0 := by
    rw [Complex.normSq_apply] at hsq
    nlinarith [sq_nonneg z.im]
  apply Complex.ext
  · simpa using hre
  · simpa using him

-- In finite dimension, every root of the characteristic polynomial of a
-- finite-order endomorphism is a root of unity. This is the algebraic half
-- of the usual trace argument and avoids any inner-product choices.
lemma charpoly_root_pow_one {W : Type*} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W]
    (A : Module.End ℂ W) {n : ℕ}
    (hpow : A ^ n = 1) {z : ℂ}
    (hz : z ∈ A.charpoly.roots) : z ^ n = 1 := by
  have hz' : A.charpoly.IsRoot z := (Polynomial.mem_roots (by
    exact A.charpoly_monic.ne_zero)).1 hz
  have heig : A.HasEigenvalue z :=
    (Module.End.hasEigenvalue_iff_isRoot_charpoly A z).2 hz'
  obtain ⟨v,hv⟩ := heig.exists_hasEigenvector
  have hcalc := hv.pow_apply n
  rw [hpow] at hcalc
  have hnz : v ≠ 0 := hv.2
  -- `(1) v = v`, so the scalar has to be one
  have hs : (z ^ n - 1) • v = 0 := by
    rw [sub_smul]
    have hvone : (1 : Module.End ℂ W) v = v := by simp
    rw [one_smul]
    -- after `hpow`, `hcalc` says precisely that the other scalar fixes `v`
    have hc : (z ^ n) • v = v := by simpa using hcalc.symm
    rw [hc]
    exact sub_self _
  exact sub_eq_zero.mp ((smul_eq_zero.mp hs).resolve_right hnz)
end FrobeniusKernel

end

-- END INLINED FILE: Mathlib/Support/frobenius_kernel_isNormal_bde655671f/Trace.lean

-- BEGIN INLINED FILE: Mathlib/Support/frobenius_kernel_isNormal_bde655671f/Virtual.lean
/-! Elementary bookkeeping for the unnormalised character pairing.  The pairing
used by `FDRep.char_orthonormal` in this development is bilinear, not sesquilinear:
`∑ f(g) q(g⁻¹)`.  Its symmetry is a *reindexing by inverse*, not a hidden
complex-conjugation theorem.  Recording this removes a surprisingly error-prone
shortcut in the virtual-character reduction. -/
open scoped BigOperators Classical
noncomputable section
namespace FrobeniusKernel
variable (L : Type) [Group L] [Fintype L]

def charPair (f q : L → ℂ) : ℂ := ∑ g : L, f g * q (g⁻¹)

lemma charPair_symm (f q : L → ℂ) : charPair L f q = charPair L q f := by
  classical
  -- reindex (and nothing else) by the involution `g ↦ g⁻¹`
  classical
  let e : L ≃ L := (Equiv.inv L)
  unfold charPair
  rw [← e.sum_comp]
  simp [e, mul_comm]

lemma charPair_add_left (f q r : L → ℂ) :
    charPair L (fun t => f t + q t) r = charPair L f r + charPair L q r := by
  classical
  unfold charPair
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib]

end FrobeniusKernel

end

-- END INLINED FILE: Mathlib/Support/frobenius_kernel_isNormal_bde655671f/Virtual.lean

-- BEGIN INLINED FILE: Mathlib/Support/frobenius_kernel_isNormal_bde655671f/Action.lean

namespace FrobeniusKernel

variable (G X : Type*) [Group G] [MulAction G X]

/-- Convenient contrapositive form of the Frobenius fixed-point hypothesis. -/
lemma eq_one_of_fixes_of_ne
    (hf : ∀ g : G, g ≠ 1 → ∀ x y : X,
      g • x = x → g • y = y → x = y)
    {g : G} {x y : X} (hxy : x ≠ y)
    (hx : g • x = x) (hy : g • y = y) :
    g = 1 := by
  by_contra h
  exact hxy (hf g h x y hx hy)

/-- Stabilizers of two different points intersect trivially.  This often
is a more useful local form of the Frobenius condition. -/
lemma stabilizer_inf_eq_bot_of_ne
    (hf : ∀ g : G, g ≠ 1 → ∀ x y : X,
      g • x = x → g • y = y → x = y)
    {x y : X} (hxy : x ≠ y) :
    MulAction.stabilizer G x ⊓ MulAction.stabilizer G y = ⊥ := by
  apply Subgroup.ext
  intro a
  constructor
  · intro ha
    have hx : a • x = x :=
      (MulAction.mem_stabilizer_iff).1 ha.1
    have hy : a • y = y :=
      (MulAction.mem_stabilizer_iff).1 ha.2
    exact (Subgroup.mem_bot).2
      (eq_one_of_fixes_of_ne G X hf hxy hx hy)
  · intro ha
    have ha' : a = 1 := (Subgroup.mem_bot).1 ha
    subst a
    simp

/-- If `d` fixes `x`, its `g`-conjugate fixes `g • x`. -/
lemma conj_fixes_smul {g d : G} {x : X}
    (hd : d • x = x) :
    (g * d * g⁻¹) • (g • x) = g • x := by
  -- the computation is worth having as a lemma; avoiding rewriting point
  -- stabilizers as mapped subgroups keeps later uses simple.
  -- first reassociate the scalar products, then cancel `g⁻¹ * g`.
  calc
    (g * d * g⁻¹) • (g • x) = g • (d • x) := by
      -- `simp` knows the cancellation in a group action
      simp [smul_smul, mul_assoc]
    _ = g • x := by rw [hd]

/-- A point stabilizer is a TI subgroup: its intersection with a conjugate
by an element moving the point is trivial. -/
lemma stabilizer_inf_map_conj_eq_bot
    (hf : ∀ a : G, a ≠ 1 → ∀ x y : X,
      a • x = x → a • y = y → x = y)
    (x : X) {g : G} (hg : g • x ≠ x) :
    MulAction.stabilizer G x ⊓
        (MulAction.stabilizer G x).map (MulAut.conj g).toMonoidHom = ⊥ := by
  apply Subgroup.ext
  intro a
  constructor
  · intro ha
    rcases (Subgroup.mem_map).1 ha.2 with ⟨d, hdH, hdval⟩
    have hdx : d • x = x :=
      (MulAction.mem_stabilizer_iff).1 hdH
    have hax : a • x = x :=
      (MulAction.mem_stabilizer_iff).1 ha.1
    have hagx : a • (g • x) = g • x := by
      rw [← hdval]
      -- evaluate the automorphism
      simpa using (conj_fixes_smul G X (g := g) hdx)
    have hxne : x ≠ g • x := Ne.symm hg
    exact (Subgroup.mem_bot).2
      (eq_one_of_fixes_of_ne G X hf hxne hax hagx)
  · intro ha
    have ha' : a = 1 := (Subgroup.mem_bot).1 ha
    subst a
    simp

/-- In a Frobenius action with a nontrivial point stabilizer, that
stabilizer is self-normalizing.  This is a purely elementary consequence
of the TI calculation. -/
lemma normalizer_stabilizer_le
    (hf : ∀ a : G, a ≠ 1 → ∀ x y : X,
      a • x = x → a • y = y → x = y)
    (x : X) (hH : MulAction.stabilizer G x ≠ ⊥) :
    Subgroup.normalizer (MulAction.stabilizer G x : Set G) ≤
      MulAction.stabilizer G x := by
  intro g hg
  -- Suppose the point is moved.  A nonidentity element of its stabilizer
  -- and its conjugate give a forbidden second fixed point.
  by_contra hng
  have hmove : g • x ≠ x := by
    intro hx
    exact hng ((MulAction.mem_stabilizer_iff).2 hx)
  obtain ⟨d, hd⟩ :=
    (Subgroup.ne_bot_iff_exists_ne_one.mp hH)
  -- `d` is a subtype element.
  have hdne : (d : G) ≠ 1 := by
    intro h
    apply hd
    apply Subtype.ext
    simpa using h
  have hdx : (d : G) • x = x :=
    (MulAction.mem_stabilizer_iff).1 d.property
  have hconjmem : g * (d : G) * g⁻¹ ∈ MulAction.stabilizer G x :=
    ((Subgroup.mem_normalizer_iff).1 hg (d : G)).1 d.property
  have hcx : (g * (d : G) * g⁻¹) • x = x :=
    (MulAction.mem_stabilizer_iff).1 hconjmem
  have hcgx : (g * (d : G) * g⁻¹) • (g • x) = g • x :=
    conj_fixes_smul G X (g := g) hdx
  have hc_one : g * (d : G) * g⁻¹ = 1 :=
    eq_one_of_fixes_of_ne G X hf (Ne.symm hmove) hcx hcgx
  have hd_one : (d : G) = 1 := by
    -- conjugation is injective
    have : (MulAut.conj g) (d : G) = (MulAut.conj g) (1 : G) := by
      simpa using hc_one
    exact (MulAut.conj g).injective this
  exact hdne hd_one

end FrobeniusKernel

namespace FrobeniusKernel
variable (G X : Type*) [Group G] [MulAction G X]

/-- Centralizers of a nonidentity element of a point stabilizer are in the
same point stabilizer.  In character-theoretic proofs this is the reason
induction from the stabilizer has the simple value formula away from `1`. -/
lemma commutant_mem_stabilizer
    (hf : ∀ a : G, a ≠ 1 → ∀ x y : X,
      a • x = x → a • y = y → x = y)
    {a : G} {x : X} (ha1 : a ≠ 1) (hax : a • x = x)
    {c : G} (hc : c * a = a * c) :
    c ∈ MulAction.stabilizer G x := by
  apply (MulAction.mem_stabilizer_iff).2
  have hacy : a • (c • x) = c • x := by
    calc
      a • (c • x) = (a * c) • x := by rw [smul_smul]
      _ = (c * a) • x := by rw [hc]
      _ = c • (a • x) := by rw [mul_smul]
      _ = c • x := by rw [hax]
  exact (hf a ha1 x (c • x) hax hacy).symm

end FrobeniusKernel

-- END INLINED FILE: Mathlib/Support/frobenius_kernel_isNormal_bde655671f/Action.lean

-- BEGIN INLINED FILE: Mathlib/Support/frobenius_kernel_isNormal_bde655671f/Counting.lean

namespace FrobeniusKernel

open scoped BigOperators Classical

/-- Nonidentity elements fixing some point.  We keep this as a subtype in
order to use finite-cardinality lemmas without decidability bookkeeping on
sets. -/
def NontrivFix (G X : Type*) [Group G] [MulAction G X] :=
  {g : G // g ≠ 1 ∧ ∃ x : X, g • x = x}

/-- A fixed point together with its nonidentity stabilizer element. -/
def FixPair (G X : Type*) [Group G] [MulAction G X] :=
  {p : X × G // p.2 ≠ 1 ∧ p.2 • p.1 = p.1}

-- These subtypes have obvious finite structures.  Giving the instances
-- explicitly avoids elaboration surprises through the abbreviations above.
noncomputable instance nontrivFixFintype (G X : Type*) [Group G]
    [MulAction G X] [Fintype G] [Fintype X] : Fintype (NontrivFix G X) := by
  unfold NontrivFix
  infer_instance
noncomputable instance fixPairFintype (G X : Type*) [Group G]
    [MulAction G X] [Fintype G] [Fintype X] : Fintype (FixPair G X) := by
  unfold FixPair
  infer_instance

section
variable (G X : Type*) [Group G] [MulAction G X]
  [Fintype G] [Fintype X]

noncomputable def pairToElement : FixPair G X → NontrivFix G X :=
  fun p => ⟨p.1.2, p.2.1, p.1.1, p.2.2⟩

/-- Under the Frobenius condition, forgetting the point from a nontrivial
fixed pair is a bijection: such an element has a *unique* fixed point. -/
lemma pairToElement_bijective
    (hf : ∀ a : G, a ≠ 1 → ∀ x y : X,
      a • x = x → a • y = y → x = y) :
    Function.Bijective (pairToElement G X) := by
  classical
  constructor
  · intro p q heq
    -- equality of images first identifies the group element, then the
    -- Frobenius hypothesis identifies the points.
    have hg : p.1.2 = q.1.2 :=
      congrArg (fun r : NontrivFix G X => r.val) heq
    have hpfix : p.1.2 • p.1.1 = p.1.1 := p.2.2
    have hqfix : p.1.2 • q.1.1 = q.1.1 := by simpa [hg] using q.2.2
    have hx : p.1.1 = q.1.1 :=
      hf (p.1.2) p.2.1 _ _ hpfix hqfix
    -- subtypes of a product have proof-irrelevant second fields
    apply Subtype.ext
    apply Prod.ext hx hg
  · intro a
    rcases a.2.2 with ⟨x, hx⟩
    exact ⟨⟨(x, a.val), a.2.1, hx⟩, Subtype.ext rfl⟩

noncomputable def fixPairEquiv
    (hf : ∀ a : G, a ≠ 1 → ∀ x y : X,
      a • x = x → a • y = y → x = y) :
    FixPair G X ≃ NontrivFix G X :=
  Equiv.ofBijective (pairToElement G X) (pairToElement_bijective G X hf)

/-- A version of the elementary `|H \ {1}| = |H|-1` which works for any
finite subtype group. -/
lemma card_ne_one_subtype (H : Subgroup G) :
    Fintype.card {h : H // h ≠ 1} = Fintype.card H - 1 := by
  classical
  -- use the complement of the singleton `1`
  have hc := Fintype.card_subtype_compl (α := H) (fun h : H => h = 1)
  have hone : Fintype.card {h : H // h = 1} = 1 := by
    classical
    -- it is a subsingleton with the evident inhabitant
    let u : {h : H // h = 1} := ⟨1, rfl⟩
    haveI : Subsingleton {h : H // h = 1} :=
      ⟨by
        intro a b
        apply Subtype.ext
        exact a.2.trans b.2.symm⟩
    simpa using (Fintype.card_ofSubsingleton u)
  -- the complement predicate is definitionally `¬ h = 1`
  simpa [hone] using hc

/-- For a fixed point, the possible partners in a `FixPair` are the
nonidentity elements of its stabilizer. -/
noncomputable def atPointEquiv (x : X) :
    {a : G // a ≠ 1 ∧ a • x = x} ≃
      {h : MulAction.stabilizer G x // h ≠ 1} := by
  classical
  let f : {a : G // a ≠ 1 ∧ a • x = x} →
      {h : MulAction.stabilizer G x // h ≠ 1} := fun a =>
        ⟨⟨a.1, (MulAction.mem_stabilizer_iff).2 a.2.2⟩,
          by
            intro h
            apply a.2.1
            have h' := congrArg (fun z : MulAction.stabilizer G x => (z : G)) h
            simpa using h'⟩
  apply Equiv.ofBijective f
  constructor
  · intro a b hab
    apply Subtype.ext
    have h := congrArg
      (fun z : {h : MulAction.stabilizer G x // h ≠ 1} => (z.1 : G)) hab
    exact h
  · intro h
    refine ⟨⟨(h.1 : G), ?_, (MulAction.mem_stabilizer_iff).1 h.1.2⟩, ?_⟩
    · intro he
      apply h.2
      apply Subtype.ext
      simpa using he
    · apply Subtype.ext
      apply Subtype.ext
      rfl

/-- Decomposing a fixed pair by its first coordinate. -/
noncomputable def fixPairSigmaEquiv :
    FixPair G X ≃ (x : X) × {a : G // a ≠ 1 ∧ a • x = x} := by
  classical
  -- `Equiv.subtypeProdEquivSigmaSubtype` has just the right shape.
  let e := Equiv.subtypeProdEquivSigmaSubtype
      (fun x : X => fun a : G => a ≠ 1 ∧ a • x = x)
  exact e

lemma card_fixPair :
    Fintype.card (FixPair G X) =
      ∑ x : X, (Fintype.card (MulAction.stabilizer G x) - 1) := by
  classical
  calc
    Fintype.card (FixPair G X) =
        Fintype.card ((x : X) × {a : G // a ≠ 1 ∧ a • x = x}) :=
          Fintype.card_congr (fixPairSigmaEquiv G X)
    _ = ∑ x : X, Fintype.card {a : G // a ≠ 1 ∧ a • x = x} :=
          Fintype.card_sigma
    _ = ∑ x : X, (Fintype.card (MulAction.stabilizer G x) - 1) := by
          apply Finset.sum_congr rfl
          intro x _
          calc
            Fintype.card {a : G // a ≠ 1 ∧ a • x = x} =
                Fintype.card {h : MulAction.stabilizer G x // h ≠ 1} :=
                  Fintype.card_congr (atPointEquiv G X x)
            _ = _ := card_ne_one_subtype (G := G) _

lemma card_nontrivFix
    (hf : ∀ a : G, a ≠ 1 → ∀ x y : X,
      a • x = x → a • y = y → x = y) :
    Fintype.card (NontrivFix G X) =
      ∑ x : X, (Fintype.card (MulAction.stabilizer G x) - 1) := by
  classical
  calc
    Fintype.card (NontrivFix G X) = Fintype.card (FixPair G X) :=
      (Fintype.card_congr (fixPairEquiv G X hf)).symm
    _ = _ := card_fixPair G X

end

end FrobeniusKernel

namespace FrobeniusKernel
open scoped BigOperators Classical

/-- The subtype corresponding to `kerSet`. -/
def KerElem (G X : Type*) [Group G] [MulAction G X] :=
  {g : G // g ∈ kerSet G X}

noncomputable instance kerElemFintype (G X : Type*) [Group G]
    [MulAction G X] [Fintype G] [Fintype X] : Fintype (KerElem G X) := by
  unfold KerElem kerSet
  infer_instance

variable (G X : Type*) [Group G] [MulAction G X]
  [Fintype G] [Fintype X]

lemma mem_kerSet_iff_not_nontrivfix (g : G) :
    g ∈ kerSet G X ↔ ¬ (g ≠ 1 ∧ ∃ x : X, g • x = x) := by
  classical
  rw [mem_kerSet]
  constructor
  · intro h hbad
    rcases h with h | h
    · exact hbad.1 h
    · rcases hbad.2 with ⟨x, hx⟩
      exact h x hx
  · intro h
    by_cases h1 : g = 1
    · exact Or.inl h1
    · right
      intro x hx
      exact h ⟨h1, ⟨x, hx⟩⟩

noncomputable def kerElemEquivCompl :
    KerElem G X ≃ {g : G // ¬ (g ≠ 1 ∧ ∃ x : X, g • x = x)} :=
  Equiv.subtypeEquivRight (mem_kerSet_iff_not_nontrivfix G X)

lemma card_kerElem :
    Fintype.card (KerElem G X) =
      Fintype.card G - Fintype.card (NontrivFix G X) := by
  classical
  calc
    Fintype.card (KerElem G X) =
        Fintype.card {g : G // ¬ (g ≠ 1 ∧ ∃ x : X, g • x = x)} :=
      Fintype.card_congr (kerElemEquivCompl G X)
    _ = Fintype.card G - Fintype.card {g : G // (g ≠ 1 ∧ ∃ x : X, g • x = x)} :=
      Fintype.card_subtype_compl _
    _ = _ := rfl

/-- Conjugation gives an equivalence of stabilizers of points in the same
orbit. -/
noncomputable def stabilizerEquivSends (g : G) (x y : X) (hg : g • x = y) :
    MulAction.stabilizer G x ≃ MulAction.stabilizer G y := by
  classical
  let f : MulAction.stabilizer G x → MulAction.stabilizer G y := fun d =>
    ⟨g * (d : G) * g⁻¹,
      (MulAction.mem_stabilizer_iff).2 (by
        -- use the elementary conjugation computation
        simpa [hg] using (conj_fixes_smul G X (g := g)
          ((MulAction.mem_stabilizer_iff).1 d.property)))⟩
  apply Equiv.ofBijective f
  constructor
  · intro a b hab
    apply Subtype.ext
    have h := congrArg (fun d : MulAction.stabilizer G y => (d : G)) hab
    -- cancel the conjugation
    have h' : (MulAut.conj g) (a : G) =
        (MulAut.conj g) (b : G) := by simpa [f] using h
    exact (MulAut.conj g).injective h'
  · intro d
    -- conjugate in the other direction
    let e : G := g⁻¹ * (d : G) * g
    have hefix : e • x = x := by
      have hd : (d : G) • y = y :=
        (MulAction.mem_stabilizer_iff).1 d.property
      -- rewrite `y` as `g • x`
      have hd' : (d : G) • (g • x) = g • x := by simpa [hg] using hd
      have := congrArg (fun z : X => g⁻¹ • z) hd'
      -- associativity cancels the outer `g`
      simpa [e, smul_smul, mul_assoc] using this
    let e' : MulAction.stabilizer G x :=
      ⟨e, (MulAction.mem_stabilizer_iff).2 hefix⟩
    refine ⟨e', ?_⟩
    apply Subtype.ext
    dsimp [f, e', e]
    simp [mul_assoc]

lemma card_stabilizer_eq_of_sends (g : G) (x y : X) (hg : g • x = y) :
    Fintype.card (MulAction.stabilizer G x) =
      Fintype.card (MulAction.stabilizer G y) := by
  classical
  exact Fintype.card_congr (stabilizerEquivSends G X g x y hg)

lemma orbit_eq_univ_of_transitive
    (ht : ∀ x y : X, ∃ g : G, g • x = y) (x : X) :
    MulAction.orbit G x = (Set.univ : Set X) := by
  classical
  apply Set.eq_univ_of_forall
  intro y
  rcases ht x y with ⟨g, hg⟩
  exact (MulAction.mem_orbit_iff).2 ⟨g, hg⟩

lemma card_mul_stabilizer_of_transitive
    (ht : ∀ x y : X, ∃ g : G, g • x = y) (x : X) :
    Fintype.card X * Fintype.card (MulAction.stabilizer G x) = Fintype.card G := by
  classical
  -- orbit-stabilizer and the orbit is all of `X`
  have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group G x
  have ho := orbit_eq_univ_of_transitive G X ht x
  -- replace the orbit subtype by the universe
  have horbcard : Fintype.card (MulAction.orbit G x) = Fintype.card X := by
    let e : (MulAction.orbit G x) ≃ X :=
      { toFun := fun z => z.1
        invFun := fun y => ⟨y, by rw [ho]; trivial⟩
        left_inv := by intro z; apply Subtype.ext; rfl
        right_inv := by intro y; rfl }
    exact Fintype.card_congr e
  rwa [horbcard] at h

lemma card_stabilizer_const
    (ht : ∀ x y : X, ∃ g : G, g • x = y) (x0 z : X) :
    Fintype.card (MulAction.stabilizer G z) =
      Fintype.card (MulAction.stabilizer G x0) := by
  classical
  rcases ht z x0 with ⟨g, hg⟩
  exact card_stabilizer_eq_of_sends G X g z x0 hg

lemma card_nontrivFix_of_transitive
    (hf : ∀ a : G, a ≠ 1 → ∀ x y : X,
      a • x = x → a • y = y → x = y)
    (ht : ∀ x y : X, ∃ g : G, g • x = y) (x0 : X) :
    Fintype.card (NontrivFix G X) =
      Fintype.card X * (Fintype.card (MulAction.stabilizer G x0) - 1) := by
  classical
  rw [card_nontrivFix G X hf]
  apply Finset.sum_const_nat
  intro z _
  rw [card_stabilizer_const G X ht x0 z]

/-- Pure counting already gives the expected order of the Frobenius
kernel *as a set*: it has as many elements as there are points.  No closure
is used here, and none follows just by taking cardinalities. -/
lemma card_kerElem_of_transitive
    (hf : ∀ a : G, a ≠ 1 → ∀ x y : X,
      a • x = x → a • y = y → x = y)
    (ht : ∀ x y : X, ∃ g : G, g • x = y)
    (hx0 : Nonempty X) :
    Fintype.card (KerElem G X) = Fintype.card X := by
  classical
  let x0 : X := Classical.choice hx0
  let n : ℕ := Fintype.card X
  let m : ℕ := Fintype.card (MulAction.stabilizer G x0)
  have hmul : n * m = Fintype.card G :=
    card_mul_stabilizer_of_transitive G X ht x0
  have hbad : Fintype.card (NontrivFix G X) = n * (m - 1) :=
    card_nontrivFix_of_transitive G X hf ht x0
  have hmpos : 0 < m := Fintype.card_pos_iff.mpr ⟨(1 : MulAction.stabilizer G x0)⟩
  calc
    Fintype.card (KerElem G X) = Fintype.card G - Fintype.card (NontrivFix G X) :=
      card_kerElem G X
    _ = n * m - n * (m - 1) := by rw [← hmul, hbad]
    _ = n * (m - (m - 1)) := by
      exact (Nat.mul_sub_left_distrib n m (m-1)).symm
    _ = n := by
      have hm : m - (m - 1) = 1 := by omega
      simp [hm]
    _ = Fintype.card X := rfl

end FrobeniusKernel

-- END INLINED FILE: Mathlib/Support/frobenius_kernel_isNormal_bde655671f/Counting.lean

-- BEGIN INLINED FILE: Mathlib/Support/frobenius_kernel_isNormal_bde655671f/Induction.lean
open scoped BigOperators Classical
namespace FrobeniusKernel
variable (G X : Type*) [Group G] [MulAction G X] [Fintype G] [Fintype X]
lemma test_conj_mem (hf : ∀ a : G, a ≠ 1 → ∀ x y : X,
      a • x = x → a • y = y → x = y)
    {a : G} (ha1 : a ≠ 1) {x : X} (hax : a • x = x) (t : G) :
    t⁻¹ * a * t ∈ MulAction.stabilizer G x ↔
      t ∈ MulAction.stabilizer G x := by
  classical
  constructor
  · intro ht
    have hx' : (t⁻¹ * a * t) • x = x :=
      (MulAction.mem_stabilizer_iff).1 ht
    have hay : a • (t • x) = t • x := by
      -- conjugating the equality by `t`
      have h' := congrArg (fun z : X => t • z) hx'
      simpa [smul_smul, mul_assoc] using h'
    have heq : x = t • x := hf a ha1 x (t • x) hax hay
    exact (MulAction.mem_stabilizer_iff).2 heq.symm
  · intro ht
    have htx : t • x = x := (MulAction.mem_stabilizer_iff).1 ht
    apply (MulAction.mem_stabilizer_iff).2
    -- evaluate directly
    calc
      (t⁻¹ * a * t) • x = t⁻¹ • (a • (t • x)) := by simp [smul_smul,mul_assoc]
      _ = t⁻¹ • (a • x) := by rw [htx]
      _ = t⁻¹ • x := by rw [hax]
      _ = x := by
        -- since `t` fixes, so does inverse
        exact (FrobeniusKernel.inv_fixes_iff G X t x).2 htx

lemma test_conj_no (g:G) (x:X) (hfree : ∀ y:X, g • y ≠ y) (t:G) :
  ¬ (t⁻¹ * g * t ∈ MulAction.stabilizer G x) := by
  intro ht
  have hx' : (t⁻¹ * g * t) • x = x :=
    (MulAction.mem_stabilizer_iff).1 ht
  have hg : g • (t • x) = t • x := by
    have h' := congrArg (fun z:X => t • z) hx'
    simpa [smul_smul, mul_assoc] using h'
  exact hfree (t • x) hg

-- sum indicator
variable {α : Type*} [Fintype α]
lemma sum_if_mem_subtype {p : α → Prop} [DecidablePred p]
    (C : ℂ) :
    (∑ t : α, if p t then C else 0) =
        (Fintype.card {t : α // p t} : ℕ) • C := by
  classical
  -- work with the filtered univ
  have hfilter :
      (∑ t ∈ (Finset.univ.filter p), C) =
        ∑ t ∈ (Finset.univ : Finset α), (if p t then C else 0) := by
    simpa using (Finset.sum_filter p (fun _ : α => C) : _)
  -- now evaluate the constant sum
  -- nested sums notation simplifies differently
  calc
    (∑ t : α, if p t then C else 0) =
        ∑ t ∈ (Finset.univ.filter p), C := by
          simpa using hfilter.symm
    _ = (Finset.univ.filter p).card • C := by simp
    _ = (Fintype.card {t : α // p t} : ℕ) • C := by
          congr 1
          -- card subtype
          symm
          simpa using (Fintype.card_subtype p)
end FrobeniusKernel
namespace FrobeniusKernel
open scoped BigOperators Classical
variable (G X : Type*) [Group G] [MulAction G X] [Fintype G] [Fintype X]

noncomputable def indSum (x:X)
    (φ : MulAction.stabilizer G x → ℂ) (g:G) : ℂ :=
  ∑ t : G,
    if ht : t⁻¹ * g * t ∈ MulAction.stabilizer G x then
      φ ⟨t⁻¹ * g * t, ht⟩
    else 0

def ClassOnStab (x:X)
    (φ : MulAction.stabilizer G x → ℂ) : Prop :=
  ∀ u v : MulAction.stabilizer G x, φ (u⁻¹ * v * u) = φ v

lemma indSum_free (x:X) (φ : MulAction.stabilizer G x → ℂ)
    {g:G} (hg : ∀ y:X, g • y ≠ y) :
    indSum G X x φ g = 0 := by
  classical
  unfold indSum
  -- each summand has false predicate
  have hnone : ∀ t:G, ¬ (t⁻¹ * g * t ∈ MulAction.stabilizer G x) :=
    fun t => FrobeniusKernel.test_conj_no G X g x hg t
  classical
  simp_rw [dif_neg (hnone _)]
  simp

lemma indSum_stab
    (hf : ∀ a : G, a ≠ 1 → ∀ z y : X,
      a • z = z → a • y = y → z = y)
    (x:X) (φ : MulAction.stabilizer G x → ℂ)
    (hclass : ClassOnStab G X x φ)
    {a:G} (ha1 : a ≠ 1) (hax : a • x = x) :
    indSum G X x φ a =
      (Fintype.card (MulAction.stabilizer G x) : ℕ) •
        φ ⟨a, (MulAction.mem_stabilizer_iff).2 hax⟩ := by
  classical
  unfold indSum
  let A : MulAction.stabilizer G x :=
    ⟨a, (MulAction.mem_stabilizer_iff).2 hax⟩
  -- for each t the membership iff t in stabilizer
  have hp (t:G) :
      t⁻¹ * a * t ∈ MulAction.stabilizer G x ↔
        t ∈ MulAction.stabilizer G x :=
    FrobeniusKernel.test_conj_mem G X hf ha1 hax t
  -- class invariance turns a true summand into a constant
  have heach (t:G) :
      (if ht : t⁻¹ * a * t ∈ MulAction.stabilizer G x then
         φ ⟨t⁻¹ * a * t, ht⟩ else 0) =
        if ht : t ∈ MulAction.stabilizer G x then φ A else 0 := by
    classical
    by_cases h : t ∈ MulAction.stabilizer G x
    · have h' : t⁻¹ * a * t ∈ MulAction.stabilizer G x := (hp t).2 h
      simp [h,h']
      -- after simp need equality of values
      have hv := hclass (⟨t,h⟩ : MulAction.stabilizer G x) A
      -- simplify cast
      -- hv : φ (↑? * ...) = _
      have heq :
          (⟨t⁻¹ * a * t, h'⟩ : MulAction.stabilizer G x) =
            (⟨t,h⟩ : MulAction.stabilizer G x)⁻¹ * A * ⟨t,h⟩ := by
          ext
          rfl
      -- dependent proofs inconsequential
      simpa [heq] using hv
    · have h' : ¬ (t⁻¹ * a * t ∈ MulAction.stabilizer G x) :=
        fun ht => h ((hp t).1 ht)
      simp [h,h']
  simp_rw [heach]
  -- sum of indicator over t in stabilizer
  have hh := FrobeniusKernel.sum_if_mem_subtype (α:=G)
      (p:= fun t:G => t ∈ MulAction.stabilizer G x) (φ A)
  -- subtype card is card of subgroup subtype (same definitional?)
  simpa using hh

lemma indSum_one (x:X) (φ : MulAction.stabilizer G x → ℂ) :
    indSum G X x φ (1:G) = (Fintype.card G : ℕ) • φ 1 := by
  classical
  unfold indSum
  -- conjugating the identity contributes the same summand for every transporter
  have hv : (fun (_ : G) => φ (1 : MulAction.stabilizer G x)) =
      (fun (_ : G) => φ (1 : MulAction.stabilizer G x)) := rfl
  -- eliminate the dependent membership tests
  classical
  have heach (t:G) :
      (if ht : t⁻¹ * (1:G) * t ∈ MulAction.stabilizer G x then
        φ ⟨t⁻¹ * (1:G) * t, ht⟩ else 0) =
          φ (1 : MulAction.stabilizer G x) := by
        have ht : t⁻¹ * (1:G) * t ∈ MulAction.stabilizer G x := by simp
        rw [dif_pos ht]
        congr 1
        ext
        simp
  simp_rw [heach]
  simp [nsmul_eq_mul]
end FrobeniusKernel
namespace FrobeniusKernel
open scoped BigOperators Classical
variable (G X : Type*) [Group G] [MulAction G X] [Fintype G] [Fintype X]
noncomputable def inducedStab (x:X)
    (φ : MulAction.stabilizer G x → ℂ) (g:G) : ℂ :=
  ((Fintype.card (MulAction.stabilizer G x) : ℂ)⁻¹) *
     indSum G X x φ g

noncomputable def tilde (x:X) (φ : MulAction.stabilizer G x → ℂ)
    (n:ℂ) (g:G) : ℂ :=
  inducedStab G X x (fun h => φ h - n) g + n

lemma tilde_free (x:X) (φ : MulAction.stabilizer G x → ℂ)
    (n:ℂ) {g:G} (hg: ∀ y:X, g • y ≠ y) :
    tilde G X x φ n g = n := by
  classical
  unfold tilde inducedStab
  rw [indSum_free G X x (fun h => φ h - n) hg]
  simp

lemma class_sub (x:X) (φ : MulAction.stabilizer G x → ℂ) (n:ℂ)
    (hc : ClassOnStab G X x φ) :
    ClassOnStab G X x (fun h => φ h - n) := by
  intro u v
  dsimp
  rw [hc u v]

lemma card_stab_nezero (x:X) :
   (Fintype.card (MulAction.stabilizer G x) : ℂ) ≠ 0 := by
  exact_mod_cast (Fintype.card_ne_zero :
    Fintype.card (MulAction.stabilizer G x) ≠ 0)

lemma tilde_stab
    (hf : ∀ a : G, a ≠ 1 → ∀ z y : X,
      a • z = z → a • y = y → z = y)
    (x:X) (φ : MulAction.stabilizer G x → ℂ)
    (n:ℂ) (hclass : ClassOnStab G X x φ)
    {a:G} (ha1 : a ≠ 1) (hax : a • x = x) :
    tilde G X x φ n a = φ ⟨a, (MulAction.mem_stabilizer_iff).2 hax⟩ := by
  classical
  unfold tilde inducedStab
  rw [indSum_stab G X hf x (fun h => φ h - n)
        (class_sub G X x φ n hclass) ha1 hax]
  -- normalize the nonzero scalar
  -- nsmul = cast mul
  rw [nsmul_eq_mul]
  have hcard := card_stab_nezero G X x
  -- in a field inv * (c * d) = d
  field_simp
  ring

lemma tilde_one
    (x:X) (φ : MulAction.stabilizer G x → ℂ) (n:ℂ)
    (hval : φ 1 = n) :
      tilde G X x φ n (1:G) = n := by
  classical
  unfold tilde inducedStab
  rw [indSum_one G X x (fun h => φ h - n)]
  rw [nsmul_eq_mul]
  simp [hval]
end FrobeniusKernel
namespace FrobeniusKernel
open scoped BigOperators Classical
variable (G X : Type*) [Group G] [MulAction G X] [Fintype G] [Fintype X]
lemma indSum_conj (x:X) (φ : MulAction.stabilizer G x → ℂ)
    (g c : G) :
    indSum G X x φ (c * g * c⁻¹) = indSum G X x φ g := by
  classical
  unfold indSum
  let e : G ≃ G := Equiv.mulLeft c
  have hsum := (Equiv.sum_comp e
    (fun t : G =>
      if ht : t⁻¹ * (c * g * c⁻¹) * t ∈ MulAction.stabilizer G x then
        φ ⟨t⁻¹ * (c * g * c⁻¹) * t, ht⟩ else 0))
  -- put the left hand sum in the order t=c*u
  rw [← hsum]
  apply Finset.sum_congr rfl
  intro t htT
  -- a group calculation identifies the conjugates
  have he : (c * t)⁻¹ * (c * g * c⁻¹) * (c * t) = t⁻¹ * g * t := by
     simp [mul_assoc]
  change
    (if ht : (c * t)⁻¹ * (c * g * c⁻¹) * (c * t) ∈
            MulAction.stabilizer G x then
       φ ⟨(c*t)⁻¹ * (c * g * c⁻¹) * (c*t), ht⟩ else 0) =
    (if ht : t⁻¹ * g * t ∈ MulAction.stabilizer G x then
       φ ⟨t⁻¹ * g * t, ht⟩ else 0)
  -- rewriting before simplifying the dependent if keeps the witnesses aligned
  rw [he]
end FrobeniusKernel
namespace FrobeniusKernel
open scoped BigOperators Classical
variable (G X : Type*) [Group G] [MulAction G X] [Fintype G] [Fintype X]

/-- The transporter formula is a class function on `G`.  At this point no
    assertion about integrality/virtual characters is made. -/
lemma inducedStab_conj (x:X) (φ : MulAction.stabilizer G x → ℂ)
    (g c : G) :
    inducedStab G X x φ (c * g * c⁻¹) = inducedStab G X x φ g := by
  classical
  unfold inducedStab
  rw [indSum_conj G X x φ g c]

lemma tilde_conj (x:X) (φ : MulAction.stabilizer G x → ℂ)
    (n:ℂ) (g c : G) :
    tilde G X x φ n (c * g * c⁻¹) = tilde G X x φ n g := by
  classical
  unfold tilde
  rw [inducedStab_conj G X x (fun h => φ h - n) g c]

end FrobeniusKernel
namespace FrobeniusKernel
open scoped BigOperators Classical
variable (G X : Type*) [Group G] [MulAction G X] [Fintype G] [Fintype X]

/-- Character of the regular representation of the point stabilizer, as a
    function.  Using this single class function would already suffice for the
    separating-kernel step of Frobenius' character argument. -/
noncomputable def regularStab (x:X) :
    MulAction.stabilizer G x → ℂ := fun h =>
      if h = 1 then (Fintype.card (MulAction.stabilizer G x) : ℂ) else 0

@[simp] lemma regularStab_one (x:X) :
    regularStab G X x (1 : MulAction.stabilizer G x) =
       (Fintype.card (MulAction.stabilizer G x) : ℂ) := by
  classical
  simp [regularStab]

lemma regularStab_ne (x:X) {h : MulAction.stabilizer G x}
    (hh : h ≠ 1) : regularStab G X x h = 0 := by
  classical
  simp [regularStab, hh]

lemma regularStab_class (x:X) :
    ClassOnStab G X x (regularStab G X x) := by
  classical
  intro u v
  by_cases hv : v = 1
  · subst v
    simp [regularStab]
  · have hcv : u⁻¹ * v * u ≠ (1 : MulAction.stabilizer G x) := by
      intro hz
      -- conjugation by u is injective in the subgroup just as in a group
      have eqv : v = (1 : MulAction.stabilizer G x) := by
        -- cancel explicitly using the group laws
        calc
          v = u * (u⁻¹ * v * u) * u⁻¹ := by simp [mul_assoc]
          _ = 1 := by simp [hz]
      exact hv eqv
    simp [regularStab, hv, hcv]
end FrobeniusKernel

-- END INLINED FILE: Mathlib/Support/frobenius_kernel_isNormal_bde655671f/Induction.lean

-- BEGIN INLINED FILE: Mathlib/Support/frobenius_kernel_isNormal_bde655671f/Inner.lean
namespace FrobeniusKernel
open scoped BigOperators Classical
variable (G X : Type*) [Group G] [MulAction G X] [Fintype G] [Fintype X]

lemma sum_into_stab (x:X) (f : MulAction.stabilizer G x → ℂ) :
    (∑ g:G, if hg : g ∈ MulAction.stabilizer G x then f ⟨g,hg⟩ else 0) =
      ∑ h : MulAction.stabilizer G x, f h := by
  classical
  let p : G → Prop := fun g => g ∈ MulAction.stabilizer G x
  let F : G → ℂ := fun g => if hg : p g then f ⟨g,hg⟩ else 0
  change (∑ g:G, F g) = _
  calc
    (∑ g:G, F g) = ∑ g ∈ (Finset.univ.filter p), F g := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro a ha
      by_cases h : p a
      · simp [F, h, p, MulAction.mem_stabilizer_iff]
      · have hh : a • x ≠ x := by
          simpa [p, MulAction.mem_stabilizer_iff] using h
        simp [F, h, hh]
    _ = ∑ h : {g:G // p g}, F h := by
      apply Finset.sum_subtype
      intro g
      simp [p, MulAction.mem_stabilizer_iff]
    _ = ∑ h : MulAction.stabilizer G x, f h := by
      -- the subtype is definitionally the subgroup; all its members satisfy the test
      apply Finset.sum_congr rfl
      intro h _
      simp [F, p, (MulAction.mem_stabilizer_iff).1 h.property]

lemma sum_conj_into_stab (x:X) (f : MulAction.stabilizer G x → ℂ)
    (t:G) :
    (∑ g:G, if hg : t⁻¹ * g * t ∈ MulAction.stabilizer G x
       then f ⟨t⁻¹*g*t,hg⟩ else 0) =
      ∑ h : MulAction.stabilizer G x, f h := by
  classical
  let F : G → ℂ := fun g =>
    if hg : t⁻¹ * g * t ∈ MulAction.stabilizer G x
       then f ⟨t⁻¹*g*t,hg⟩ else 0
  let D : G → ℂ := fun u =>
    if hu : u ∈ MulAction.stabilizer G x then f ⟨u,hu⟩ else 0
  let e : G ≃ G := (MulAut.conj t).toEquiv
  have he (u:G) : t⁻¹ * (e u) * t = u := by
    change t⁻¹ * (t*u*t⁻¹) * t = u
    simp [mul_assoc]
  have hF (u:G) : F (e u) = D u := by
    dsimp [F, D]
    rw [he]
  calc
    (∑ g:G, if hg : t⁻¹ * g * t ∈ MulAction.stabilizer G x
       then f ⟨t⁻¹*g*t,hg⟩ else 0) = ∑ g:G, F g := rfl
    _ = ∑ u:G, F (e u) := (Equiv.sum_comp e F).symm
    _ = ∑ u:G, D u := by simp_rw [hF]
    _ = ∑ h : MulAction.stabilizer G x, f h :=
      sum_into_stab G X x f

lemma sum_indSum (x:X) (f : MulAction.stabilizer G x → ℂ) :
    (∑ g:G, indSum G X x f g) =
       (Fintype.card G : ℂ) * ∑ h : MulAction.stabilizer G x, f h := by
  classical
  unfold indSum
  rw [Finset.sum_comm]
  -- every transporter gives the same subgroup sum
  simp_rw [sum_conj_into_stab G X x f]
  simp

lemma sum_inducedStab (x:X) (f : MulAction.stabilizer G x → ℂ) :
    (∑ g:G, inducedStab G X x f g) =
       (Fintype.card G : ℂ) * ((Fintype.card (MulAction.stabilizer G x) : ℂ))⁻¹ *
          ∑ h : MulAction.stabilizer G x, f h := by
  classical
  unfold inducedStab
  rw [← Finset.mul_sum]
  rw [sum_indSum G X x f]
  ring

lemma indSum_inv_stab_ne (hf : ∀ a : G, a ≠ 1 → ∀ z y : X,
      a • z = z → a • y = y → z = y)
    (x:X) (q : MulAction.stabilizer G x → ℂ)
    (hq : ClassOnStab G X x q)
    (h : MulAction.stabilizer G x) (hh : h ≠ 1) :
    indSum G X x q ((h:G)⁻¹) =
       (Fintype.card (MulAction.stabilizer G x) : ℕ) • q (h⁻¹) := by
  classical
  have hn : (h:G)⁻¹ ≠ 1 := by
    intro hz; apply hh
    apply Subtype.ext
    have hz' : (h:G) = 1 := by
      have := congrArg Inv.inv hz
      simpa using this
    exact hz'
  have hx : ((h:G)⁻¹) • x = x :=
    (MulAction.mem_stabilizer_iff).1 ((h⁻¹).property)
  have hv := indSum_stab G X hf x q hq hn hx
  have he : (⟨(h:G)⁻¹, (MulAction.mem_stabilizer_iff).2 hx⟩ :
       MulAction.stabilizer G x) = h⁻¹ := by
       ext; rfl
  simpa [he] using hv

lemma sum_one_transport_mul_indSum (hf : ∀ a : G, a ≠ 1 → ∀ z y : X,
      a • z = z → a • y = y → z = y)
    (x:X) (f q : MulAction.stabilizer G x → ℂ)
    (hf0 : f 1 = 0) (hq : ClassOnStab G X x q) (t:G) :
    (∑ g:G, (if hg : t⁻¹ * g * t ∈ MulAction.stabilizer G x then
                  f ⟨t⁻¹*g*t,hg⟩ else 0) * indSum G X x q g⁻¹) =
       (Fintype.card (MulAction.stabilizer G x) : ℂ) *
         ∑ h : MulAction.stabilizer G x, f h * q (h⁻¹) := by
  classical
  let H := MulAction.stabilizer G x
  let e : G ≃ G := (MulAut.conj t).toEquiv
  have he (u:G) : t⁻¹ * (e u) * t = u := by
    change t⁻¹ * (t*u*t⁻¹) * t = u
    simp [mul_assoc]
  have hinv (u:G) : (e u)⁻¹ = t * u⁻¹ * t⁻¹ := by
    change (t*u*t⁻¹)⁻¹ = _
    simp [mul_assoc]
  let F : G → ℂ := fun g =>
    (if hg : t⁻¹ * g * t ∈ H then f ⟨t⁻¹*g*t,hg⟩ else 0) *
       indSum G X x q g⁻¹
  let D : G → ℂ := fun u =>
    if hu : u ∈ H then f ⟨u,hu⟩ * indSum G X x q u⁻¹ else 0
  have hFD (u:G) : F (e u) = D u := by
    dsimp [F, D]
    rw [he]
    rw [hinv]
    rw [indSum_conj G X x q (u⁻¹) t]
    by_cases hu : u ∈ H
    · simp [hu]
    · simp [hu]
  have hDsum : (∑ u:G, D u) =
      ∑ h : H, f h * indSum G X x q ((h:G)⁻¹) := by
    -- reuse subtype-filter summation, for a function of a stabilizer value
    simpa [D, H] using (sum_into_stab G X x
      (fun h : MulAction.stabilizer G x => f h * indSum G X x q ((h:G)⁻¹)))
  have hone (h : H) :
      f h * indSum G X x q ((h:G)⁻¹) =
        (Fintype.card H : ℂ) * (f h * q (h⁻¹)) := by
    by_cases hz : h = 1
    · subst h
      simp [hf0]
    · rw [indSum_inv_stab_ne G X hf x q hq h hz]
      rw [nsmul_eq_mul]
      ring
  calc
    (∑ g:G, (if hg : t⁻¹ * g * t ∈ MulAction.stabilizer G x then
                  f ⟨t⁻¹*g*t,hg⟩ else 0) * indSum G X x q g⁻¹)
       = ∑ g:G, F g := rfl
    _ = ∑ u:G, F (e u) := (Equiv.sum_comp e F).symm
    _ = ∑ u:G, D u := by simp_rw [hFD]
    _ = ∑ h : H, f h * indSum G X x q ((h:G)⁻¹) := hDsum
    _ = ∑ h : H, (Fintype.card H : ℂ) * (f h * q (h⁻¹)) := by
      apply Finset.sum_congr rfl
      intro h hh
      exact hone h
    _ = _ := by rw [← Finset.mul_sum]

lemma sum_indSum_mul_indSum (hf : ∀ a : G, a ≠ 1 → ∀ z y : X,
      a • z = z → a • y = y → z = y)
    (x:X) (f q : MulAction.stabilizer G x → ℂ)
    (hf0 : f 1 = 0) (hq : ClassOnStab G X x q) :
    (∑ g:G, indSum G X x f g * indSum G X x q g⁻¹) =
       (Fintype.card G : ℂ) * (Fintype.card (MulAction.stabilizer G x) : ℂ) *
         ∑ h : MulAction.stabilizer G x, f h * q (h⁻¹) := by
  classical
  -- expand the first transporter sum and interchange the two summations
  have hexp (g:G) :
      indSum G X x f g * indSum G X x q g⁻¹ =
        ∑ t:G, (if ht : t⁻¹ * g * t ∈ MulAction.stabilizer G x then
                    f ⟨t⁻¹*g*t,ht⟩ else 0) * indSum G X x q g⁻¹ := by
    unfold indSum
    rw [Finset.sum_mul]
  calc
    (∑ g:G, indSum G X x f g * indSum G X x q g⁻¹) =
       ∑ g:G, ∑ t:G, (if ht : t⁻¹ * g * t ∈ MulAction.stabilizer G x then
                    f ⟨t⁻¹*g*t,ht⟩ else 0) * indSum G X x q g⁻¹ := by
         apply Finset.sum_congr rfl
         intro g hg
         exact hexp g
    _ = ∑ t:G, ∑ g:G, (if ht : t⁻¹ * g * t ∈ MulAction.stabilizer G x then
                    f ⟨t⁻¹*g*t,ht⟩ else 0) * indSum G X x q g⁻¹ := by
          rw [Finset.sum_comm]
    _ = ∑ t:G, (Fintype.card (MulAction.stabilizer G x) : ℂ) *
           ∑ h : MulAction.stabilizer G x, f h * q (h⁻¹) := by
          apply Finset.sum_congr rfl
          intro t ht
          exact sum_one_transport_mul_indSum G X hf x f q hf0 hq t
    _ = _ := by simp; ring

lemma sum_induced_mul_induced (hf : ∀ a : G, a ≠ 1 → ∀ z y : X,
      a • z = z → a • y = y → z = y)
    (x:X) (f q : MulAction.stabilizer G x → ℂ)
    (hf0 : f 1 = 0) (hq : ClassOnStab G X x q) :
    (∑ g:G, inducedStab G X x f g * inducedStab G X x q g⁻¹) =
       (Fintype.card G : ℂ) * ((Fintype.card (MulAction.stabilizer G x) : ℂ))⁻¹ *
         ∑ h : MulAction.stabilizer G x, f h * q (h⁻¹) := by
  classical
  let c : ℂ := (Fintype.card (MulAction.stabilizer G x) : ℂ)
  change (∑ g:G, (c⁻¹ * indSum G X x f g) *
                       (c⁻¹ * indSum G X x q g⁻¹)) = _
  have hp (g:G) : (c⁻¹ * indSum G X x f g) *
                       (c⁻¹ * indSum G X x q g⁻¹) =
           (c⁻¹ * c⁻¹) * (indSum G X x f g * indSum G X x q g⁻¹) := by ring
  simp_rw [hp]
  rw [← Finset.mul_sum]
  rw [sum_indSum_mul_indSum G X hf x f q hf0 hq]
  have hc : c ≠ 0 := card_stab_nezero G X x
  let D : ℂ := (Fintype.card G : ℂ)
  let S : ℂ := ∑ h : MulAction.stabilizer G x, f h * q h⁻¹
  change c⁻¹ * c⁻¹ * (D * c * S) = D * c⁻¹ * S
  have hi : c⁻¹ * c = (1:ℂ) := inv_mul_cancel₀ hc
  calc
    c⁻¹ * c⁻¹ * (D * c * S) = (c⁻¹ * c) * (D * c⁻¹ * S) := by ring
    _ = D * c⁻¹ * S := by rw [hi]; ring

lemma sum_tilde_mul_tilde (hf : ∀ a : G, a ≠ 1 → ∀ z y : X,
      a • z = z → a • y = y → z = y)
    (x:X) (φ ψ : MulAction.stabilizer G x → ℂ)
    (hψ : ClassOnStab G X x ψ) :
    (∑ g:G, tilde G X x φ (φ 1) g * tilde G X x ψ (ψ 1) g⁻¹) =
       (Fintype.card G : ℂ) * ((Fintype.card (MulAction.stabilizer G x) : ℂ))⁻¹ *
         ∑ h : MulAction.stabilizer G x, φ h * ψ (h⁻¹) := by
  classical
  let H := MulAction.stabilizer G x
  let c : ℂ := (Fintype.card H : ℂ)
  let D : ℂ := (Fintype.card G : ℂ)
  let n : ℂ := φ 1
  let m : ℂ := ψ 1
  let f : H → ℂ := fun h => φ h - n
  let q : H → ℂ := fun h => ψ h - m
  have f0 : f 1 = 0 := by simp [f,n]
  have qc : ClassOnStab G X x q := class_sub G X x ψ m hψ
  have prodEq :
    (∑ g:G, inducedStab G X x f g * inducedStab G X x q g⁻¹) =
       D * c⁻¹ * ∑ h:H, f h * q (h⁻¹) := by
    simpa [D,c,H] using sum_induced_mul_induced G X hf x f q f0 qc
  have fsum : (∑ g:G, inducedStab G X x f g) =
        D * c⁻¹ * ∑ h:H, f h := by
    simpa [D,c,H] using sum_inducedStab G X x f
  have qsum0 : (∑ g:G, inducedStab G X x q g) =
        D * c⁻¹ * ∑ h:H, q h := by
    simpa [D,c,H] using sum_inducedStab G X x q
  have qsum : (∑ g:G, inducedStab G X x q g⁻¹) =
        D * c⁻¹ * ∑ h:H, q h := by
    let e : G ≃ G := Equiv.inv G
    have he := Equiv.sum_comp e (fun z:G => inducedStab G X x q z)
    exact he.trans qsum0
  -- First expand the pointwise product. Pull all four sums out.
  have expand :
    (∑ g:G, (inducedStab G X x f g + n) *
                (inducedStab G X x q g⁻¹ + m)) =
       (∑ g:G, inducedStab G X x f g * inducedStab G X x q g⁻¹) +
          m * (∑ g:G, inducedStab G X x f g) +
          n * (∑ g:G, inducedStab G X x q g⁻¹) + D*(n*m) := by
    -- all terms live in a commutative ring; distribute sums
    simp only [mul_add, add_mul, Finset.sum_add_distrib]
    -- sum of constants
    simp [D, ← Finset.mul_sum, ← Finset.sum_mul]
    ring
  have eqmid :
    (∑ g:G, (inducedStab G X x f g + n) *
                (inducedStab G X x q g⁻¹ + m)) =
      D * c⁻¹ * (∑ h:H, f h * q (h⁻¹)) +
        m * (D*c⁻¹ * ∑ h:H, f h) +
        n * (D*c⁻¹ * ∑ h:H, q h) + D*(n*m) := by
    rw [expand, prodEq, fsum, qsum]
  -- inside the subgroup the displayed expression is just (f+n)(q+m)
  have combine :
      D * c⁻¹ * (∑ h:H, f h * q (h⁻¹)) +
        m * (D*c⁻¹ * ∑ h:H, f h) +
        n * (D*c⁻¹ * ∑ h:H, q h) + D*(n*m)
       = D*c⁻¹ * (∑ h:H, φ h * ψ (h⁻¹)) := by
    -- replace the last term by `c` copies: the subgroup is nonempty
    have hc0 : c ≠ 0 := by simpa [c,H] using card_stab_nezero G X x
    -- sums of constants in H
    have hconst : (∑ _h:H, (n*m)) = c*(n*m) := by simp [c]
    -- sums of `q h⁻¹` reindex the subgroup by inverse
    have qinv : (∑ h:H, q (h⁻¹)) = ∑ h:H, q h := by
      have he := Equiv.sum_comp (Equiv.inv H) q
      exact he
    -- pointwise identity, then distribute it over the finite sum
    have one (h:H) : φ h * ψ (h⁻¹) =
         f h * q (h⁻¹) + m * f h + n * q (h⁻¹) + n*m := by
      simp [f,q,n,m]
      ring
    have totals : (∑ h:H, φ h * ψ (h⁻¹)) =
        (∑ h:H, f h * q (h⁻¹)) +
        m * (∑ h:H, f h) +
        n * (∑ h:H, q h) + c*(n*m) := by
      simp_rw [one]
      simp only [Finset.sum_add_distrib]
      simp only [← Finset.mul_sum]
      rw [qinv]
      simp [c]
      ring
    rw [totals]
    -- cancel `c` against its inverse in the last term
    have hc : c⁻¹ * c = (1:ℂ) := inv_mul_cancel₀ hc0
    -- ring, with that single relation
    let A : ℂ := ∑ h:H, f h * q (h⁻¹)
    let B : ℂ := ∑ h:H, f h
    let C : ℂ := ∑ h:H, q h
    change D*c⁻¹*A + m*(D*c⁻¹*B) + n*(D*c⁻¹*C) + D*(n*m) =
       D*c⁻¹*(A + m*B + n*C + c*(n*m))
    calc
      D*c⁻¹*A + m*(D*c⁻¹*B) + n*(D*c⁻¹*C) + D*(n*m)
          = D*c⁻¹*(A + m*B + n*C) + D*(n*m) := by ring
      _ = D*c⁻¹*(A + m*B + n*C) + (c⁻¹*c)*(D*(n*m)) := by rw [hc]; ring
      _ = D*c⁻¹*(A + m*B + n*C + c*(n*m)) := by ring

  change (∑ g:G, (inducedStab G X x f g + n) *
                (inducedStab G X x q g⁻¹ + m)) = _
  simpa [D,c,H] using eqmid.trans combine

lemma char_class_stab (x:X) (V : FDRep ℂ (MulAction.stabilizer G x)) :
    ClassOnStab G X x V.character := by
  intro u v
  -- representation characters are invariant under conjugacy
  simpa using (FDRep.char_conj V v u⁻¹)

lemma tilde_simple_inner (hf : ∀ a : G, a ≠ 1 → ∀ z y : X,
      a • z = z → a • y = y → z = y)
    (x:X)
    (V W : FDRep ℂ (MulAction.stabilizer G x)) [CategoryTheory.Simple V] [CategoryTheory.Simple W] :
    (∑ g:G,
       tilde G X x V.character (V.character 1) g *
       tilde G X x W.character (W.character 1) g⁻¹) =
       if Nonempty (V ≅ W) then (Fintype.card G : ℂ) else 0 := by
  classical
  let H := MulAction.stabilizer G x
  let c : ℂ := (Fintype.card H : ℂ)
  have hc : c ≠ 0 := by simpa [c,H] using card_stab_nezero G X x
  letI : Invertible (Fintype.card H : ℂ) := invertibleOfNonzero hc
  have orth := FDRep.char_orthonormal V W
  -- `⅟` agrees with inverse in a field
  have hs : (∑ h:H, V.character h * W.character h⁻¹) =
        c * (if Nonempty (V ≅ W) then (1:ℂ) else 0) := by
    -- solve from orthogonality
    -- its scalar notation is `⅟ c • sum`
    change ⅟(c) • (∑ h:H, V.character h * W.character h⁻¹) =
       (if Nonempty (V ≅ W) then (1:ℂ) else 0) at orth
    -- turn scalar inverse into ordinary inverse
    rw [invOf_eq_inv, smul_eq_mul] at orth
    have : c⁻¹ * c = (1:ℂ) := inv_mul_cancel₀ hc
    calc
      (∑ h:H, V.character h * W.character h⁻¹)
          = c * (c⁻¹ * (∑ h:H, V.character h * W.character h⁻¹)) := by field_simp
      _ = _ := by rw [orth]
  rw [sum_tilde_mul_tilde G X hf x V.character W.character
        (char_class_stab G X x W)]
  rw [hs]
  have hi : c⁻¹ * c = (1:ℂ) := inv_mul_cancel₀ hc
  change (Fintype.card G : ℂ) * c⁻¹ *
      (c * (if Nonempty (V ≅ W) then (1:ℂ) else 0)) = _
  split_ifs
  · calc
      (Fintype.card G : ℂ) * c⁻¹ * (c * 1) =
        (Fintype.card G : ℂ) * (c⁻¹*c) := by ring
      _ = _ := by rw [hi]; ring
  · ring

end FrobeniusKernel

-- END INLINED FILE: Mathlib/Support/frobenius_kernel_isNormal_bde655671f/Inner.lean

-- BEGIN INLINED FILE: Mathlib/Support/frobenius_kernel_isNormal_bde655671f/Integrality.lean
namespace FrobeniusKernel
open scoped BigOperators Classical
variable (G X : Type*) [Group G] [MulAction G X] [Fintype G] [Fintype X]

lemma one_transport_mul_char (x:X)
    (f : MulAction.stabilizer G x → ℂ) (T : FDRep ℂ G) (t:G) :
    (∑ g:G, (if hg : t⁻¹ * g * t ∈ MulAction.stabilizer G x
        then f ⟨t⁻¹*g*t,hg⟩ else 0) * T.character g⁻¹) =
      ∑ h : MulAction.stabilizer G x, f h * T.character ((h:G)⁻¹) := by
  classical
  let H := MulAction.stabilizer G x
  let e : G ≃ G := (MulAut.conj t).toEquiv
  have he (u:G) : t⁻¹ * (e u) * t = u := by
    change t⁻¹ * (t*u*t⁻¹) * t = u
    simp [mul_assoc]
  have hinv (u:G) : (e u)⁻¹ = t * u⁻¹ * t⁻¹ := by
    change (t*u*t⁻¹)⁻¹ = _
    simp [mul_assoc]
  let F : G → ℂ := fun g =>
    (if hg : t⁻¹ * g * t ∈ MulAction.stabilizer G x
        then f ⟨t⁻¹*g*t,hg⟩ else 0) * T.character g⁻¹
  let D : G → ℂ := fun u =>
    if hu : u ∈ MulAction.stabilizer G x then
       f ⟨u,hu⟩ * T.character (u⁻¹) else 0
  have hFD (u:G) : F (e u) = D u := by
    dsimp [F, D]
    rw [he, hinv]
    rw [FDRep.char_conj T (u⁻¹) t]
    by_cases h : u ∈ MulAction.stabilizer G x <;> simp [h]
  calc
    (∑ g:G, (if hg : t⁻¹ * g * t ∈ MulAction.stabilizer G x
        then f ⟨t⁻¹*g*t,hg⟩ else 0) * T.character g⁻¹) = ∑ g:G, F g := rfl
    _ = ∑ u:G, F (e u) := (Equiv.sum_comp e F).symm
    _ = ∑ u:G, D u := by simp_rw [hFD]
    _ = ∑ h : MulAction.stabilizer G x, f h * T.character ((h:G)⁻¹) := by
      simpa [D] using (sum_into_stab G X x
        (fun h : MulAction.stabilizer G x => f h * T.character ((h:G)⁻¹)))

lemma indSum_mul_char (x:X)
    (f : MulAction.stabilizer G x → ℂ) (T: FDRep ℂ G) :
    (∑ g:G, indSum G X x f g * T.character g⁻¹) =
      (Fintype.card G : ℂ) *
        ∑ h : MulAction.stabilizer G x, f h * T.character ((h:G)⁻¹) := by
  classical
  unfold indSum
  -- distribute product into transporter sum
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [one_transport_mul_char G X x f T]
  simp

lemma induced_mul_char (x:X)
    (f : MulAction.stabilizer G x → ℂ) (T: FDRep ℂ G) :
    (∑ g:G, inducedStab G X x f g * T.character g⁻¹) =
      (Fintype.card G : ℂ) *
        ((Fintype.card (MulAction.stabilizer G x) : ℂ))⁻¹ *
        ∑ h : MulAction.stabilizer G x, f h * T.character ((h:G)⁻¹) := by
  classical
  unfold inducedStab
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  rw [indSum_mul_char G X x f T]
  ring

lemma tilde_mul_char (x:X)
    (φ : MulAction.stabilizer G x → ℂ) (n:ℂ) (T: FDRep ℂ G) :
    (∑ g:G, tilde G X x φ n g * T.character g⁻¹) =
      (Fintype.card G : ℂ) *
        ((Fintype.card (MulAction.stabilizer G x) : ℂ))⁻¹ *
        ∑ h : MulAction.stabilizer G x, (φ h - n) * T.character ((h:G)⁻¹)
        + n * (∑ g:G, T.character g) := by
  classical
  unfold tilde
  simp only [add_mul, Finset.sum_add_distrib]
  -- second summand inverses reindex
  have hinv : (∑ g:G, T.character g⁻¹) = ∑ g:G, T.character g :=
    Equiv.sum_comp (Equiv.inv G) T.character
  rw [← Finset.mul_sum]
  rw [hinv]
  rw [induced_mul_char G X x (fun h => φ h - n) T]

noncomputable abbrev resStab (x:X) (T: FDRep ℂ G) :
    FDRep ℂ (MulAction.stabilizer G x) :=
  FDRep.of (T.ρ.comp (MulAction.stabilizer G x).subtype)

@[simp] lemma resStab_char (x:X) (T: FDRep ℂ G)
    (h : MulAction.stabilizer G x) :
    (resStab G X x T).character h = T.character (h:G) := rfl

-- the subgroup scalar product, without invertible notation
lemma sum_char_hom (x:X) (V : FDRep ℂ (MulAction.stabilizer G x))
    (T: FDRep ℂ G) :
    (∑ h : MulAction.stabilizer G x,
       V.character h * T.character ((h:G)⁻¹)) =
      (Fintype.card (MulAction.stabilizer G x) : ℂ) *
        (Module.finrank ℂ ((resStab G X x T) ⟶ V) : ℂ) := by
  classical
  let H := MulAction.stabilizer G x
  let c : ℂ := (Fintype.card H : ℂ)
  have hc : c ≠ 0 := by simpa [c,H] using card_stab_nezero G X x
  letI : Invertible (Fintype.card H : ℂ) := invertibleOfNonzero hc
  have e := FDRep.scalar_product_char_eq_finrank_equivariant
      (resStab G X x T) V
  have e' : c⁻¹ *
       (∑ h : H, V.character h * (resStab G X x T).character h⁻¹) =
         (Module.finrank ℂ ((resStab G X x T) ⟶ V) : ℂ) := by
    simpa [c, H, invOf_eq_inv, smul_eq_mul] using e
  change (∑ h:H, V.character h * T.character ((h:G)⁻¹)) = _
  have rewrite :
      (∑ h:H, V.character h * (resStab G X x T).character h⁻¹) =
         ∑ h:H, V.character h * T.character ((h:G)⁻¹) := by rfl
  rw [rewrite] at e'
  change _ = c * _
  calc
    (∑ h:H, V.character h * T.character ((h:G)⁻¹)) =
       c * (c⁻¹ * (∑ h:H, V.character h * T.character ((h:G)⁻¹))) := by
         field_simp
    _ = _ := by rw [e']

noncomputable abbrev trivRep (L:Type*) [Group L] : FDRep ℂ L :=
  FDRep.of (Representation.trivial ℂ L ℂ)

@[simp] lemma trivRep_char (L:Type*) [Group L] (h:L) :
    (trivRep L).character h = 1 := by
  change LinearMap.trace ℂ ℂ _ = _
  change LinearMap.trace ℂ ℂ 1 = _
  simp

@[simp] lemma trivRep_finrank (L:Type*) [Group L] :
    Module.finrank ℂ (trivRep L) = 1 := by
  change Module.finrank ℂ ℂ = 1
  simp

lemma sum_char_all (T: FDRep ℂ G) :
    (∑ g:G, T.character g) = (Fintype.card G : ℂ) *
        (Module.finrank ℂ (T ⟶ trivRep G) : ℂ) := by
  classical
  let c : ℂ := (Fintype.card G : ℂ)
  have hc : c ≠ 0 := by dsimp [c]; exact_mod_cast (Fintype.card_ne_zero : Fintype.card G ≠ 0)
  letI : Invertible (Fintype.card G : ℂ) := invertibleOfNonzero hc
  have e := FDRep.scalar_product_char_eq_finrank_equivariant T (trivRep G)
  have ev : c⁻¹ * (∑ g:G, T.character g⁻¹) =
       (Module.finrank ℂ (T ⟶ trivRep G) : ℂ) := by
    simpa [c, invOf_eq_inv, smul_eq_mul, trivRep_char] using e
  have hinv : (∑ g:G, T.character g⁻¹) = ∑ g:G, T.character g :=
    Equiv.sum_comp (Equiv.inv G) T.character
  rw [hinv] at ev
  change _ = c * _
  calc
    (∑ g:G, T.character g) = c * (c⁻¹ * (∑ g:G, T.character g)) := by field_simp
    _ = _ := by rw [ev]

lemma sum_plain_stab_char (x:X) (T: FDRep ℂ G) :
    (∑ h : MulAction.stabilizer G x, T.character ((h:G)⁻¹)) =
      (Fintype.card (MulAction.stabilizer G x) : ℂ) *
       (Module.finrank ℂ ((resStab G X x T) ⟶ trivRep (MulAction.stabilizer G x)) : ℂ) := by
  have e := sum_char_hom G X x (trivRep (MulAction.stabilizer G x)) T
  simpa [trivRep_char] using e

-- integral scalar product of tilde with any character, written without division
lemma tilde_char_integer (x:X)
    (V : FDRep ℂ (MulAction.stabilizer G x)) (T: FDRep ℂ G) :
    (∑ g:G, tilde G X x V.character (V.character 1) g * T.character g⁻¹) =
      (Fintype.card G : ℂ) *
       ((Module.finrank ℂ ((resStab G X x T) ⟶ V) : ℂ)
        - (Module.finrank ℂ V : ℂ) *
           (Module.finrank ℂ ((resStab G X x T) ⟶ trivRep (MulAction.stabilizer G x)) : ℂ)
        + (Module.finrank ℂ V : ℂ) *
           (Module.finrank ℂ ( T ⟶ trivRep G) : ℂ)) := by
  classical
  let H := MulAction.stabilizer G x
  let c : ℂ := (Fintype.card H : ℂ)
  let D : ℂ := (Fintype.card G : ℂ)
  let d : ℂ := (Module.finrank ℂ V : ℂ)
  let m : ℂ := (Module.finrank ℂ ((resStab G X x T) ⟶ V) : ℂ)
  let b : ℂ :=
    (Module.finrank ℂ ((resStab G X x T) ⟶ trivRep H) : ℂ)
  let q : ℂ := (Module.finrank ℂ (T ⟶ trivRep G) : ℂ)
  have hc : c ≠ 0 := by simpa [c,H] using card_stab_nezero G X x
  have hval : V.character 1 = d := by
    simpa [d] using (FDRep.char_one V)
  have hA : (∑ h:H, V.character h * T.character ((h:G)⁻¹)) = c*m := by
    simpa [c,m,H] using (sum_char_hom G X x V T)
  have hB : (∑ h:H, T.character ((h:G)⁻¹)) = c*b := by
    simpa [c,b,H] using (sum_plain_stab_char G X x T)
  have hQ : (∑ g:G, T.character g) = D*q := by
    simpa [D,q] using (sum_char_all (G:=G) T)
  have hdiff :
      (∑ h:H, (V.character h - V.character 1) *
          T.character ((h:G)⁻¹)) = c*m - d*(c*b) := by
    -- split into two sums; all other quantities are scalars
    simp only [sub_mul, Finset.sum_sub_distrib]
    rw [hA]
    rw [← Finset.mul_sum]
    rw [hval, hB]
  rw [tilde_mul_char G X x V.character (V.character 1) T]
  -- use the three subgroup/full sums
  change D * c⁻¹ *
      (∑ h:H, (V.character h - V.character 1) * T.character ((h:G)⁻¹))
      + V.character 1 * (∑ g:G, T.character g) = _
  rw [hdiff, hval, hQ]
  change D * c⁻¹ * (c*m - d*(c*b)) + d*(D*q) =
       D * (m - d*b + d*q)
  have hi : c⁻¹ * c = (1:ℂ) := inv_mul_cancel₀ hc
  calc
    D * c⁻¹ * (c*m - d*(c*b)) + d*(D*q)
       = D * (c⁻¹*c) * (m - d*b) + d*(D*q) := by ring
    _ = D * (m - d*b) + d*(D*q) := by rw [hi]; ring
    _ = D * (m - d*b + d*q) := by ring


/-- The unnormalised scalar product is actually an integer multiple of the
order of the group. Notice that this uses an arbitrary representation of `G`,
not just a simple one; no decomposition theorem is being smuggled in here. -/
lemma tilde_char_integer_int (x:X)
    (V : FDRep ℂ (MulAction.stabilizer G x)) (T: FDRep ℂ G) :
    ∃ z : ℤ,
      (∑ g:G, tilde G X x V.character (V.character 1) g * T.character g⁻¹) =
         (Fintype.card G : ℂ) * (z : ℂ) := by
  classical
  let m : ℕ := Module.finrank ℂ ((resStab G X x T) ⟶ V)
  let d : ℕ := Module.finrank ℂ V
  let b : ℕ := Module.finrank ℂ
       ((resStab G X x T) ⟶ trivRep (MulAction.stabilizer G x))
  let q : ℕ := Module.finrank ℂ (T ⟶ trivRep G)
  refine ⟨(m:ℤ) - (d:ℤ)*(b:ℤ) + (d:ℤ)*(q:ℤ), ?_⟩
  rw [tilde_char_integer G X x V T]
  -- casting a difference is done in `ℤ`, not in `ℕ`; this is why the
  -- preceding lemma was stated over `ℂ` first.
  push_cast
  rfl

end FrobeniusKernel

-- END INLINED FILE: Mathlib/Support/frobenius_kernel_isNormal_bde655671f/Integrality.lean

-- BEGIN INLINED FILE: Mathlib/Support/frobenius_kernel_isNormal_bde655671f/Lift.lean

namespace FrobeniusKernel
open scoped BigOperators Classical
open CategoryTheory
variable (L : Type*) [Group L] [Fintype L]

/-- Conjugation-invariant complex functions; cheaper than bundled class functions. -/
def CentralFun (f : L → ℂ) : Prop :=
  ∀ (c g : L), f (c * g * c⁻¹) = f g

/-- The element of the group algebra given by a function acts on a representation. We use
 the inverse in the matrix because the scalar product in Character.lean is `χ g⁻¹`. -/
noncomputable def centralOperator (f : L → ℂ) (T : FDRep ℂ L) : Module.End ℂ T :=
  ∑ g : L, f g • T.ρ (g⁻¹)

lemma centralOperator_trace (f : L → ℂ) (T : FDRep ℂ L) :
    LinearMap.trace ℂ T (centralOperator L f T) =
      ∑ g : L, f g * T.character (g⁻¹) := by
  classical
  unfold centralOperator FDRep.character
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro g hg
  rw [LinearMap.map_smul]
  simp [smul_eq_mul]

/-- A class sum commutes with every matrix of a representation.  This elementary change of
variables is useful because it only needs a finite group. -/
lemma centralOperator_comm (f : L → ℂ) (hf : CentralFun L f)
    (T : FDRep ℂ L) (t : L) :
    (T.ρ t).comp (centralOperator L f T) =
       (centralOperator L f T).comp (T.ρ t) := by
  classical
  let e : L ≃ L := (MulAut.conj t).toEquiv
  have he (g : L) : (e g)⁻¹ = t * g⁻¹ * t⁻¹ := by
    change (t * g * t⁻¹)⁻¹ = _
    simp [mul_assoc]
  have hf' (g : L) : f (e g) = f g := by
    simpa [e] using hf t g
  -- rewrite the right hand conjugation index and compare on vectors
  ext v
  -- composition on a sum can be evaluated pointwise
  simp only [centralOperator, LinearMap.comp_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, map_sum, LinearMap.map_smul]
  -- reindex the right-hand sum
  have hr :
      (∑ h : L, f h • (T.ρ h⁻¹) ((T.ρ t) v)) =
        ∑ g : L, f (e g) • (T.ρ (e g)⁻¹) ((T.ρ t) v) :=
    (Equiv.sum_comp e (fun h : L => f h • (T.ρ h⁻¹) ((T.ρ t) v))).symm
  rw [hr]
  apply Finset.sum_congr rfl
  intro g hg
  rw [hf' g, he]
  -- multiplicativity of rho
  simp only [map_mul]
  change _ = _
  -- `mul_apply` for endomorphism algebra is composition, simp finds it by `rfl`/simp
  -- use module scalar commutation and group cancellation
  -- after simp of the inverse group products both sides coincide
  simp [mul_assoc]

/-- The central operator as an equivariant endomorphism. -/
noncomputable def centralHom (f : L → ℂ) (hf : CentralFun L f)
    (T : FDRep ℂ L) : T ⟶ T where
  hom := InducedCategory.homMk (ModuleCat.ofHom (centralOperator L f T))
  comm t := by
    -- commutative-square orientation in Action
    apply InducedCategory.hom_ext
    apply ModuleCat.hom_ext
    simp only [FGModuleCat.hom_hom_comp, FDRep.hom_hom_action_ρ]
    ext v
    dsimp
    change (centralOperator L f T) ((T.ρ t) v) = (T.ρ t) ((centralOperator L f T) v)
    have h := congrArg (fun A : Module.End ℂ T => A v) (centralOperator_comm L f hf T t)
    exact h.symm

@[simp] lemma centralHom_linear (f : L → ℂ) (hf : CentralFun L f) (T : FDRep ℂ L) :
    (centralHom L f hf T).hom.hom.hom = centralOperator L f T := rfl

/-- On a simple module a central class sum with zero trace vanishes. This is the small
`Schur` step in the completeness argument for characters. -/
lemma centralOperator_eq_zero_of_simple (f : L → ℂ) (hf : CentralFun L f)
    (T : FDRep ℂ L) [CategoryTheory.Simple T]
    (hz : (∑ g : L, f g * T.character g⁻¹) = 0) :
    centralOperator L f T = 0 := by
  classical
  obtain ⟨c, hc⟩ :=
    CategoryTheory.endomorphism_simple_eq_smul_id ℂ (centralHom L f hf T)
  -- compare underlying linear maps
  have lin : c • (1 : Module.End ℂ T) = centralOperator L f T := by
    have h := congrArg (fun u : T ⟶ T => u.hom.hom.hom) hc
    -- identity and scalar structures are pointwise
    change c • (1 : Module.End ℂ T) = centralOperator L f T at h
    exact h
  have dpos : (Module.finrank ℂ T : ℂ) ≠ 0 := by
    have hn : ¬ Module.finrank ℂ T = 0 := by
      intro h0
      have ss : Subsingleton T := (Module.finrank_zero_iff).1 h0
      have eqid : (𝟙 T : T ⟶ T) = 0 := by
        ext v
        change v = 0
        exact @Subsingleton.elim T ss _ _
      exact CategoryTheory.id_nonzero T eqid
    exact_mod_cast hn
  have trlin := congrArg (LinearMap.trace ℂ T) lin
  have ctr : c * (Module.finrank ℂ T : ℂ) = 0 := by
    -- trace c id = c*d, RHS is `hz`
    simpa [LinearMap.map_smul, centralOperator_trace L f T, hz] using trlin
  have cz : c = 0 := (mul_eq_zero.mp ctr).resolve_right dpos
  rw [← lin, cz, zero_smul]

end FrobeniusKernel

-- END INLINED FILE: Mathlib/Support/frobenius_kernel_isNormal_bde655671f/Lift.lean

-- BEGIN INLINED FILE: Mathlib/Support/frobenius_kernel_isNormal_bde655671f/Separation.lean

namespace FrobeniusKernel
open scoped BigOperators Classical

/-- A concrete regular object of `FDRep`.  We use the left action on the
finitely supported functions on the group.  Keeping this as an abbreviation
makes the underlying space (`L →₀ ℂ`) reducible; this is quite convenient when
one wants to evaluate a vector at one group element. -/
noncomputable abbrev leftRegularObj (L : Type) [Group L] [Fintype L] : FDRep ℂ L :=
  FDRep.of (Representation.ofMulAction ℂ L L)

variable (L : Type) [Group L] [Fintype L]

/-- One column of the left regular matrix.  Notice the inverse in `ρ g⁻¹`:
the coefficient is at `g⁻¹`.  This is the elementary faithful-regular-action
calculation used when turning character separation into equality of class
functions. -/
lemma leftRegularObj_column (g t : L) :
    (((leftRegularObj L).ρ (g⁻¹)) (Finsupp.single 1 (1:ℂ)) : (L →₀ ℂ)) t =
       (if g*t = (1:L) then 1 else 0) := by
  change (Representation.ofMulAction ℂ L L (g⁻¹)
      (Finsupp.single 1 (1:ℂ))) t = _
  -- Multiplying on the left by `g` sends the basis vector at `1` to the
  -- basis vector at `g⁻¹` for this convention.
  by_cases h : g*t = (1:L)
  · have ht : t = g⁻¹ := by
      calc
        t = g⁻¹ * (g*t) := by simp [mul_assoc]
        _ = g⁻¹ := by rw [h]; simp
    simp [h, ht]
  · have ht : t ≠ g⁻¹ := by
      intro e
      apply h
      rw [e]
      simp
    simp [h, ht]

/-- Acting with a group-algebra element `∑ f g • g⁻¹` on the delta vector of
the regular object recovers `f`, with its index reversed.  No centrality of
`f` is needed here. -/
lemma centralOperator_leftRegular_apply (f : L → ℂ) (t : L) :
    (((centralOperator L f (leftRegularObj L))
       (Finsupp.single 1 (1:ℂ)) : (L →₀ ℂ)) t) = f (t⁻¹) := by
  classical
  unfold centralOperator
  simp only [LinearMap.sum_apply, LinearMap.smul_apply]
  -- Push evaluation through the finite sum, regarding it first as an
  -- additive map on finsupps.  `Finset.sum_apply` is the lemma for functions,
  -- not for `Finsupp`, so `applyAddHom` is important here.
  change (Finset.univ.sum (fun x : L =>
      f x • (((leftRegularObj L).ρ x⁻¹)
          (Finsupp.single 1 (1:ℂ)) : (L →₀ ℂ)))) t = _
  change Finsupp.applyAddHom t (Finset.univ.sum _) = _
  rw [map_sum]
  change (∑ x : L, f x *
       ((((leftRegularObj L).ρ x⁻¹)
          (Finsupp.single 1 (1:ℂ)) : (L →₀ ℂ)) t)) = _
  simp_rw [leftRegularObj_column L]
  have hx : (t⁻¹) * t = (1:L) := by simp
  have hzero (u:L) (hu:u ≠ t⁻¹) :
      f u * (if u*t = (1:L) then 1 else 0) = 0 := by
    have hn : u*t ≠ (1:L) := by
      intro e
      apply hu
      exact (mul_eq_one_iff_eq_inv).1 e
    simp [hn]
  rw [Finset.sum_eq_single (t⁻¹)]
  · simp [hx]
  · intro u hu hne
    exact hzero u hne
  · simp

/-- The regular object is faithful for these class-sum operators.  In fact
this is true for *all* functions on the group, not just class functions. This
is often the last, purely algebraic, step in a character-separation proof:
once the central operator is known to vanish on a decomposition of the
regular object, the function itself is zero. -/
lemma centralOperator_leftRegular_injective (f : L → ℂ)
    (hz : centralOperator L f (leftRegularObj L) = 0) : f = 0 := by
  classical
  funext g
  have hv := congrArg (fun (A : Module.End ℂ (leftRegularObj L)) =>
      (((A (Finsupp.single 1 (1:ℂ))) : (L →₀ ℂ)) (g⁻¹))) hz
  have hval :
      (((centralOperator L f (leftRegularObj L))
          (Finsupp.single 1 (1:ℂ)) : (L →₀ ℂ)) (g⁻¹)) = f g := by
    simpa using (centralOperator_leftRegular_apply L f (g⁻¹))
  -- The right hand side of `hv` is the value of the zero linear map on a
  -- vector, hence zero.
  simpa [hval] using hv

/-- A convenient pointwise formulation. -/
lemma centralOperator_leftRegular_eq_zero_iff (f : L → ℂ) :
    centralOperator L f (leftRegularObj L) = 0 ↔ f = 0 := by
  constructor
  · exact centralOperator_leftRegular_injective L f
  · intro e; simpa [e, centralOperator]


noncomputable def orbitIndicator (a : L) (u : L) : ℂ :=
  if ∃ c : L, c * a * c⁻¹ = u then 1 else 0
lemma orbitIndicator_central (a : L) : CentralFun L (orbitIndicator L a) := by
  intro c g
  classical
  unfold orbitIndicator
  split_ifs with h1 h2
  · rfl
  · exfalso
    apply h2
    obtain ⟨d, hd⟩ := h1
    refine ⟨c⁻¹ * d, ?_⟩
    -- Need solve (c⁻¹*d)*a*(c⁻¹*d)⁻¹ = g
    -- from d*a*d⁻¹ = c*g*c⁻¹
    have he := congrArg (fun t : L => c⁻¹ * t * c) hd
    simpa [mul_assoc] using he
  · exfalso
    apply h1
    obtain ⟨d, hd⟩ := ‹∃ _ : L, _›
    refine ⟨c*d, ?_⟩
    -- hd: d*a*d^-1 = g
    rw [mul_inv_rev]
    simpa [mul_assoc] using congrArg (fun t : L => c * t * c⁻¹) hd
  · rfl

/- Unnormalised pairing of `f` with the inverse orbit-indicator for `a`. -/
lemma mul_orbitIndicator_inv_sum (f : L → ℂ) (hf : CentralFun L f) (a : L) :
    (∑ g:L, f g * orbitIndicator L (a⁻¹) (g⁻¹)) =
      ((Finset.univ.filter (fun g : L => ∃ c : L, c*a*c⁻¹ = g)).card : ℂ) * f a := by
  classical
  let p : L → Prop := fun g => ∃ c : L, c*a*c⁻¹=g
  have hp (g:L) : (∃ c:L, c*(a⁻¹)*c⁻¹ = g⁻¹) ↔ p g := by
    constructor
    · rintro ⟨c,hc⟩
      refine ⟨c, ?_⟩
      -- invert hc
      have := congrArg Inv.inv hc
      -- (c*a^-1*c^-1)^-1 = c*a*c^-1
      simpa [mul_assoc] using this
    · rintro ⟨c,hc⟩
      refine ⟨c, ?_⟩
      have := congrArg Inv.inv hc
      simpa [mul_assoc] using this
  have hfval {g:L} (hg:p g) : f g = f a := by
    obtain ⟨c,rfl⟩ := hg
    exact hf c a
  calc
   (∑ g:L, f g * orbitIndicator L (a⁻¹) (g⁻¹)) =
      ∑ g ∈ Finset.univ.filter p, f g * orbitIndicator L (a⁻¹) (g⁻¹) := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro u hu
        by_cases h:p u
        · change (∃ c : L, c*a*c⁻¹ = u) at h
          simp [h]
        · have hn : ¬ ∃ c:L, c*(a⁻¹)*c⁻¹ = u⁻¹ := not_congr (hp u) |>.mpr h
          -- term is zero off the orbit
          simp [h, orbitIndicator, hn]
   _ = ∑ g ∈ Finset.univ.filter p, f a := by
        apply Finset.sum_congr rfl
        intro u hu
        have hmem : p u := (Finset.mem_filter.mp hu).2
        have hind : orbitIndicator L (a⁻¹) (u⁻¹) = 1 := by
          have h := (hp u).2 hmem
          simp [orbitIndicator, h]
        -- on that orbit `f` is constant
        simp [hind, hfval hmem]
   _ = ((Finset.univ.filter p).card : ℂ) * f a := by simp
   _ = _ := rfl

lemma centralPairing_nondegenerate (f : L → ℂ) (hf : CentralFun L f)
    (hz : ∀ q : L → ℂ, CentralFun L q →
       (∑ g:L, f g * q (g⁻¹)) = 0) : f = 0 := by
  classical
  funext a
  have hsum := hz (orbitIndicator L (a⁻¹))
      (orbitIndicator_central L (a⁻¹))
  rw [mul_orbitIndicator_inv_sum L f hf a] at hsum
  let s := Finset.univ.filter (fun g : L => ∃ c : L, c*a*c⁻¹ = g)
  have hamem : a ∈ s := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    exact ⟨1, by simp⟩
  have hcard : s.card ≠ 0 := by
    intro h
    exact (Finset.card_ne_zero.mpr ⟨a, hamem⟩) h
  have hcast : (s.card : ℂ) ≠ 0 := by exact_mod_cast hcard
  -- `hsum` is a nonzero natural scalar times the desired value.
  exact (mul_eq_zero.mp hsum).resolve_left hcast


end FrobeniusKernel

-- END INLINED FILE: Mathlib/Support/frobenius_kernel_isNormal_bde655671f/Separation.lean

-- BEGIN INLINED FILE: Mathlib/Support/frobenius_kernel_isNormal_bde655671f/Detection.lean
namespace FrobeniusKernel
open scoped BigOperators Classical
open CategoryTheory
variable (L : Type*) [Group L] [Fintype L]
/-- The group-algebra operator is natural with respect to intertwining maps, without
any centrality assumption. This is useful when cutting the regular object into
Maschke summands. -/
lemma centralOperator_map (f : L → ℂ) {S T : FDRep ℂ L} (u : S ⟶ T) (v : S) :
    u.hom.hom.hom (centralOperator L f S v) =
      centralOperator L f T (u.hom.hom.hom v) := by
  classical
  unfold centralOperator
  simp only [LinearMap.sum_apply, LinearMap.smul_apply]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro g hg
  rw [map_smul]
  -- the morphism intertwines the action
  have h := u.comm (g⁻¹)
  have hu := ConcreteCategory.congr_hom h v
  have hu' : (u.hom.hom.hom) ((S.ρ (g⁻¹)) v) =
      (T.ρ (g⁻¹)) ((u.hom.hom.hom) v) := by
    exact hu
  exact congrArg (fun w : T => f g • w) hu'
end FrobeniusKernel
namespace FrobeniusKernel
open scoped BigOperators Classical
open CategoryTheory
variable (L : Type*) [Group L] [Fintype L]
lemma centralOperator_range_le (f : L → ℂ) {S T : FDRep ℂ L} (u : S ⟶ T)
    (hz : centralOperator L f S = 0) :
    LinearMap.range (u.hom.hom.hom : S →ₗ[ℂ] T) ≤
       LinearMap.ker (centralOperator L f T) := by
  intro w hw
  rcases hw with ⟨v,rfl⟩
  have h := centralOperator_map L f u v
  rw [hz] at h
  simpa using h.symm

/-- A family of summands whose underlying ranges span detects zero class-sum
operators. The hypothesis is deliberately in the underlying vector space; no
choice of biproducts in `FDRep` is required. In applications Maschke supplies such
a family of simple summands of the regular module. -/
lemma centralOperator_eq_zero_of_ranges (f : L → ℂ) (T : FDRep ℂ L)
    {ι : Sort*} (S : ι → FDRep ℂ L) (incl : ∀ i, S i ⟶ T)
    (hgen : (⨆ i, LinearMap.range ((incl i).hom.hom.hom : S i →ₗ[ℂ] T)) = ⊤)
    (hz : ∀ i, centralOperator L f (S i) = 0) :
    centralOperator L f T = 0 := by
  classical
  have leker : (⊤ : Submodule ℂ T) ≤ LinearMap.ker (centralOperator L f T) := by
    rw [← hgen]
    exact iSup_le (fun i => centralOperator_range_le L f (incl i) (hz i))
  have hker : LinearMap.ker (centralOperator L f T) = ⊤ := top_unique leker
  ext v
  have hv : v ∈ LinearMap.ker (centralOperator L f T) := hker.symm ▸ trivial
  exact hv
end FrobeniusKernel
namespace FrobeniusKernel
open scoped BigOperators Classical
open CategoryTheory
variable (L : Type*) [Group L] [Fintype L]
/-- Vanishing transports across an equivariant isomorphism. -/
lemma centralOperator_eq_zero_of_iso (f : L → ℂ) {S T : FDRep ℂ L}
    (e : S ≅ T) (hz : centralOperator L f S = 0) :
    centralOperator L f T = 0 := by
  ext v
  obtain ⟨w, rfl⟩ := (FDRep.isoToLinearEquiv e).surjective v
  have h := centralOperator_map L f e.hom w
  rw [hz] at h
  have heq : (FDRep.isoToLinearEquiv e) w = e.hom.hom.hom.hom w := rfl
  rw [heq]
  simpa using h.symm
end FrobeniusKernel

-- END INLINED FILE: Mathlib/Support/frobenius_kernel_isNormal_bde655671f/Detection.lean

-- BEGIN INLINED FILE: Mathlib/Support/frobenius_kernel_isNormal_bde655671f/KernelChar.lean
open scoped Classical BigOperators
open Module Polynomial
noncomputable section
namespace FrobeniusKernel
/-- If all elements of a finite multiset of real numbers are at most one,
and its sum is its cardinality, all the elements are one. -/
lemma multiset_all_one_of_le {s : Multiset ℝ}
    (hle : ∀ x ∈ s, x ≤ (1:ℝ)) (hs : s.sum = (s.card : ℝ)) :
    ∀ x ∈ s, x = (1:ℝ) := by
  classical
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a t ih =>
    have ha : a ≤ (1:ℝ) := hle a (by simp)
    have ht : ∀ y ∈ t, y ≤ (1:ℝ) := by
      intro y hy
      exact hle y (by simp [hy])
    have htle : t.sum ≤ (t.card : ℝ) := by
      have h := Multiset.sum_le_card_nsmul t (1:ℝ) ht
      simpa using h
    have hsum : a + t.sum = (t.card : ℝ) + 1 := by
      simpa [add_comm, add_left_comm, add_assoc] using hs
    have ha1 : a = (1:ℝ) := by linarith
    have hts : t.sum = (t.card : ℝ) := by linarith
    have hi := ih ht hts
    intro z hz
    have : z = a ∨ z ∈ t := (Multiset.mem_cons.mp hz)
    rcases this with rfl | hz'
    · exact ha1
    · exact hi _ hz'

lemma end_eq_one_of_trace_eq_finrank_of_pow
    {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (A : Module.End ℂ W) {n : ℕ} (hn : n ≠ 0)
    (hpow : A ^ n = 1)
    (htr : LinearMap.trace ℂ W A = (Module.finrank ℂ W : ℂ)) :
    A = 1 := by
  classical
  let r : Multiset ℂ := A.charpoly.roots
  have hsplit : A.charpoly.Splits := IsAlgClosed.splits _
  have hcard : r.card = Module.finrank ℂ W := by
    change A.charpoly.roots.card = _
    rw [← Polynomial.natDegree_eq_card_roots hsplit]
    exact A.charpoly_natDegree
  have hsum : r.sum = (Module.finrank ℂ W : ℂ) := by
    have ht := Module.End.trace_eq_sum_roots_charpoly_of_splits (f:=A) hsplit
    -- trace = sum
    exact ht.symm.trans htr
  --Real parts sum to their cardinality.
  have hsumre : (Multiset.map (fun z : ℂ => z.re) r).sum = (r.card : ℝ) := by
    have hm : (r.sum).re = (Multiset.map (fun z : ℂ => z.re) r).sum := by
      simpa using (map_multiset_sum (Complex.reCLM.toAddMonoidHom) r)
    have hre : (r.sum).re = (Module.finrank ℂ W : ℝ) := by
      rw [hsum]
      simp
    rw [← hm]
    rw [hre, hcard]
  have hle : ∀ y ∈ Multiset.map (fun z : ℂ => z.re) r, y ≤ (1:ℝ) := by
    intro y hy
    rcases Multiset.mem_map.mp hy with ⟨z,hz,rfl⟩
    apply root_re_le_one hn
    apply charpoly_root_pow_one A hpow hz
  have hallre : ∀ y ∈ Multiset.map (fun z : ℂ => z.re) r, y = (1:ℝ) :=
    multiset_all_one_of_le hle (by simpa using hsumre)
  have hroot : ∀ z : ℂ, z ∈ r → z = 1 := by
    intro z hz
    apply root_eq_one_of_re hn (charpoly_root_pow_one A hpow hz)
    exact hallre z.re (Multiset.mem_map_of_mem _ hz)
  have heigen : ∀ z : ℂ, A.HasEigenvalue z → z = 1 := by
    intro z hz
    apply hroot z
    exact (Polynomial.mem_roots (A.charpoly_monic.ne_zero)).2
      ((Module.End.hasEigenvalue_iff_isRoot_charpoly A z).1 hz)
  -- `A` is semisimple since it is annihilated by the separable polynomial
  -- `X^n-1` in characteristic zero.
  have hsep : (Polynomial.X ^ n - Polynomial.C (1:ℂ)).Separable :=
    Polynomial.separable_X_pow_sub_C (1:ℂ) (by exact_mod_cast hn) one_ne_zero
  have hpzero : Polynomial.aeval A (Polynomial.X ^ n - Polynomial.C (1:ℂ)) = 0 := by
    simp [map_sub, map_pow, hpow]
  have hsemi : A.IsSemisimple :=
    Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsep.squarefree hpzero
  have heigTop : A.eigenspace (1:ℂ) = ⊤ := by
    rw [← hsemi.iSup_eigenspace_eq_top]
    apply le_antisymm
    · exact le_iSup (fun μ : ℂ => A.eigenspace μ) 1
    · exact iSup_le (fun μ => by
        classical
        by_cases hμ : μ = (1:ℂ)
        · simpa [hμ]
        · have hm : ¬ A.HasEigenvalue μ := by
            intro hh
            exact hμ (heigen μ hh)
          have hb : A.eigenspace μ = ⊥ := by
            exact not_not.mp (Module.End.hasEigenvalue_iff.not.mp hm)
          simp [hb])
  ext w
  have hw : w ∈ A.eigenspace (1:ℂ) := heigTop.symm ▸ (show w ∈ (⊤ : Submodule ℂ W) from trivial)
  simpa [Module.End.mem_eigenspace_iff] using (Module.End.mem_eigenspace_iff.mp hw)

lemma rho_eq_one_of_character_eq_one (L : Type) [Group L] [Fintype L]
    (T : FDRep ℂ L) (g : L)
    (hc : T.character g = T.character 1) :
    T.ρ g = 1 := by
  classical
  have hn : Fintype.card L ≠ 0 := Fintype.card_ne_zero
  have hp : (T.ρ g : Module.End ℂ T) ^ (Fintype.card L) = 1 := by
    rw [← map_pow]
    rw [pow_card_eq_one]
    simp
  apply end_eq_one_of_trace_eq_finrank_of_pow (T.ρ g) hn hp
  simpa [FDRep.character] using hc.trans (FDRep.char_one T)
end FrobeniusKernel
namespace FrobeniusKernel
open CategoryTheory
lemma rho_eq_one_of_ranges (L : Type) [Group L]
    (g : L) (T : FDRep ℂ L) {ι : Sort*} (S : ι → FDRep ℂ L)
    (u : ∀ i, S i ⟶ T)
    (hspan : (⨆ i, LinearMap.range ((u i).hom.hom.hom : S i →ₗ[ℂ] T)) = ⊤)
    (hone : ∀ i, (S i).ρ g = 1) : T.ρ g = 1 := by
  classical
  -- subtract the identity and annihilate each spanning range
  let A : Module.End ℂ T := T.ρ g - 1
  have hr : ∀ i, LinearMap.range ((u i).hom.hom.hom : S i →ₗ[ℂ] T) ≤
      LinearMap.ker A := by
    intro i w hw
    rcases hw with ⟨v,rfl⟩
    change A ((u i).hom.hom.hom v) = 0
    change T.ρ g ((u i).hom.hom.hom v) - (u i).hom.hom.hom v = 0
    have hc := ConcreteCategory.congr_hom ((u i).comm g) v
    have hc' : (T.ρ g) ((u i).hom.hom.hom v) =
        (u i).hom.hom.hom ((S i).ρ g v) := by
      exact hc.symm
    -- equivariance and the hypothesis on this source
    rw [hc', hone i]
    simp
  have ht : (⊤ : Submodule ℂ T) ≤ LinearMap.ker A := by
    rw [← hspan]
    exact iSup_le hr
  have hk : LinearMap.ker A = ⊤ := top_unique ht
  have hz : A = 0 := LinearMap.ker_eq_top.mp hk
  dsimp [A] at hz
  exact sub_eq_zero.mp hz
end FrobeniusKernel
namespace FrobeniusKernel
lemma leftRegular_rho_injective_one (L : Type) [Group L] [Fintype L]
    (g : L) (h : (leftRegularObj L).ρ g = 1) : g = 1 := by
  classical
  have hv := congrArg (fun A : Module.End ℂ (leftRegularObj L) =>
      (A (Finsupp.single 1 (1:ℂ)) : (L →₀ ℂ)) (1:L)) h
  have hc := leftRegularObj_column L (g⁻¹) (1:L)
  have hif : (if g⁻¹ * (1:L) = (1:L) then (1:ℂ) else 0) = 1 := by
    calc
      (if g⁻¹ * (1:L) = (1:L) then (1:ℂ) else 0) =
          (((leftRegularObj L).ρ ((g⁻¹)⁻¹))
            (Finsupp.single 1 (1:ℂ)) : (L →₀ ℂ)) (1:L) := hc.symm
      _ = (((leftRegularObj L).ρ g)
            (Finsupp.single 1 (1:ℂ)) : (L →₀ ℂ)) (1:L) := by simp
      _ = 1 := by simpa using hv
  by_cases he : g⁻¹ * (1:L) = (1:L)
  · simpa using (inv_eq_one.mp (by simpa using he) : g = 1)
  · simpa using hif
end FrobeniusKernel

end

-- END INLINED FILE: Mathlib/Support/frobenius_kernel_isNormal_bde655671f/KernelChar.lean

-- BEGIN INLINED FILE: Mathlib/Support/frobenius_kernel_isNormal_bde655671f/Semisimple.lean
/-! A little finiteness lemma for the Maschke step.

`IsSemisimpleRepresentation` by itself only gives an *arbitrary* independent
family of submodules.  In applications to characters it is easy to get stuck
at this point: detectability on simple objects wants a **finite** family.  The
underlying vector space of an object of `FDRep` is finite-dimensional, and the
following lemma records the finite version on the group-algebra module.
-/
open scoped MonoidAlgebra
open Representation
noncomputable section
namespace FrobeniusKernel
variable (L Y : Type) [Group L] [Fintype L] [AddCommGroup Y] [Module ℂ Y]

/-- The `ℂ[L]`-module underlying a finite dimensional representation has a
finite Maschke decomposition into simple (actual sub-)modules.  We keep the
linear equivalence: throwing it away and retaining just existence of one atom
is not enough for the separation argument. -/
lemma finite_simple_submodules (ρ : Representation ℂ L Y)
    [FiniteDimensional ℂ Y] :
    ∃ (n : ℕ) (S : Fin n → Submodule ℂ[L] ρ.asModule),
      Nonempty (ρ.asModule ≃ₗ[ℂ[L]] Π₀ i : Fin n, S i) ∧
        ∀ i, IsSimpleModule ℂ[L] (S i) := by
  -- Maschke over `ℂ` needs `Nat.card`, rather than `Fintype.card`.
  letI : NeZero (Nat.card L : ℂ) :=
    ⟨by
      exact_mod_cast
        (Nat.card_ne_zero.mpr ⟨⟨(1 : L)⟩, inferInstance⟩)⟩
  -- There is no type-class loop from the finite-dimensional `ℂ` vector
  -- space here: `of_restrictScalars_finite` is deliberately in the
  -- *easy* direction.  A vector-space basis generates the same module
  -- over the larger scalar ring.
  letI : Module.Finite ℂ[L] ρ.asModule := by
    haveI : Module.Finite ℂ ρ.asModule := Module.Finite.equiv ρ.asModuleEquiv.symm
    exact Module.Finite.of_restrictScalars_finite ℂ ℂ[L] ρ.asModule
  obtain ⟨n, S, e, hs⟩ :=
    IsSemisimpleModule.exists_linearEquiv_fin_dfinsupp ℂ[L] ρ.asModule
  exact ⟨n, S, ⟨e⟩, hs⟩

end FrobeniusKernel

end

-- END INLINED FILE: Mathlib/Support/frobenius_kernel_isNormal_bde655671f/Semisimple.lean

-- BEGIN INLINED FILE: Mathlib/Support/frobenius_kernel_isNormal_bde655671f/FiniteSpan.lean
open scoped MonoidAlgebra
open Representation
noncomputable section
namespace FrobeniusKernel
variable (L Y : Type) [Group L] [Fintype L] [AddCommGroup Y] [Module ℂ Y]
lemma finite_simple_submodules_span (ρ : Representation ℂ L Y)
    [FiniteDimensional ℂ Y] :
    ∃ (n : ℕ) (P : Fin n → Submodule ℂ[L] ρ.asModule),
       (∀ j, IsSimpleModule ℂ[L] (P j)) ∧ (⨆ j, P j) = ⊤ := by
  -- Maschke as in the preceding lemma
  letI : NeZero (Nat.card L : ℂ) :=
    ⟨by
      exact_mod_cast
        (Nat.card_ne_zero.mpr ⟨⟨(1 : L)⟩, inferInstance⟩)⟩
  letI : Module.Finite ℂ[L] ρ.asModule := by
    haveI : Module.Finite ℂ ρ.asModule := Module.Finite.equiv ρ.asModuleEquiv.symm
    exact Module.Finite.of_restrictScalars_finite ℂ ℂ[L] ρ.asModule
  obtain ⟨s, ind, hs, simple⟩ :=
    IsSemisimpleModule.exists_sSupIndep_sSup_simples_eq_top ℂ[L] ρ.asModule
  -- only finitely many summands occur in a finite module
  letI : Finite s :=
    WellFoundedGT.finite_of_iSupIndep ((sSupIndep_iff _).mp ind)
      (fun S => by
        letI : IsSimpleModule ℂ[L] S.1 := simple _ S.2
        exact (S.1.nontrivial_iff_ne_bot).mp
          (IsSimpleModule.nontrivial ℂ[L] S.1))
  let e := Finite.equivFin s
  let P : Fin (Nat.card s) → Submodule ℂ[L] ρ.asModule := fun j => (e.symm j).1
  refine ⟨Nat.card s, P, ?_, ?_⟩
  · intro j
    exact simple _ (e.symm j).2
  · -- the supremum is just the old `sSup`, after reindexing its subtype
    rw [sSup_eq_iSup'] at hs
    -- `⨆ (u : s), (u : Submodule ..)` reindex by e
    have eqsup : (⨆ j : Fin (Nat.card s), P j) =
        (⨆ u : s, (u.1 : Submodule ℂ[L] ρ.asModule)) := by
      apply le_antisymm
      · refine iSup_le ?_
        intro j
        exact le_iSup (fun u : s => (u.1 : Submodule ℂ[L] ρ.asModule)) (e.symm j)
      · refine iSup_le ?_
        intro u
        have h := le_iSup (fun j : Fin (Nat.card s) => P j) (e u)
        change (e.symm (e u)).1 ≤ _ at h
        simp only [Equiv.symm_apply_apply] at h
        exact h
    rw [eqsup]
    exact hs
end FrobeniusKernel

end

-- END INLINED FILE: Mathlib/Support/frobenius_kernel_isNormal_bde655671f/FiniteSpan.lean

-- BEGIN INLINED FILE: Mathlib/Support/frobenius_kernel_isNormal_bde655671f/Summands.lean
open scoped MonoidAlgebra BigOperators Classical
open Representation CategoryTheory
noncomputable section
namespace FrobeniusKernel
variable (L : Type) [Group L] [Fintype L]

-- convert a group algebra submodule of a representation to a small FDRep object
noncomputable def subFD (T : FDRep ℂ L)
    (P : Submodule ℂ[L] (Representation.asModule T.ρ)) : FDRep ℂ L :=
  FDRep.of ((Subrepresentation.ofSubmodule' (ρ:=T.ρ) P).toRepresentation)

noncomputable def subIncl (T : FDRep ℂ L)
    (P : Submodule ℂ[L] (Representation.asModule T.ρ)) : subFD L T P ⟶ T where
  hom := InducedCategory.homMk (ModuleCat.ofHom (Submodule.subtype _))
  comm g := by
    apply InducedCategory.hom_ext
    apply ModuleCat.hom_ext
    -- show subtype map commutes
    ext v
    rfl

@[simp] lemma subIncl_linear (T : FDRep ℂ L)
    (P : Submodule ℂ[L] (Representation.asModule T.ρ)) :
    (subIncl L T P).hom.hom.hom = (Submodule.subtype _ :
      (Subrepresentation.ofSubmodule' (ρ:=T.ρ) P).toSubmodule →ₗ[ℂ] T) := rfl

-- test simplicity conversion
lemma subFD_simple (T : FDRep ℂ L)
    (P : Submodule ℂ[L] (Representation.asModule T.ρ)) [IsSimpleModule ℂ[L] P] :
    CategoryTheory.Simple (subFD L T P) := by
  -- the group order is nonzero over the complex numbers
  letI : NeZero (Nat.card L : ℂ) :=
    ⟨by exact_mod_cast (Nat.card_ne_zero.mpr ⟨⟨(1:L)⟩, inferInstance⟩)⟩
  -- use endomorphism rank criterion
  apply (FDRep.simple_iff_end_is_rank_one (subFD L T P)).2
  let τ : Representation ℂ L ((Subrepresentation.ofSubmodule' (ρ:=T.ρ) P).toSubmodule) :=
    (Subrepresentation.ofSubmodule' (ρ:=T.ρ) P).toRepresentation
  -- irreducibility of tau via equality of the group algebra actions on the subtype
  let e : τ.asModule ≃ₗ[ℂ[L]] P :=
    { toFun := fun w => ⟨w.1, w.2⟩
      invFun := fun w => ⟨w.1, w.2⟩
      left_inv := fun w => by cases w; rfl
      right_inv := fun w => by cases w; rfl
      map_add' := fun u v => by rfl
      map_smul' := by
        intro c w
        induction c using MonoidAlgebra.induction_linear with
        | zero =>
          ext
          rfl
        | add a b ha hb =>
          change (⟨((a + b) • (w : τ.asModule)).1, _⟩ : P) =
            (a+b) • (⟨w.1,w.2⟩ : P)
          calc
            ⟨((a+b) • w : τ.asModule).1, _⟩ =
                ⟨(a • w : τ.asModule).1, _⟩ + ⟨(b • w : τ.asModule).1, _⟩ := by
                    ext; exact congrArg Subtype.val (add_smul a b w)
            _ = a • (⟨w.1,w.2⟩ : P) + b • (⟨w.1,w.2⟩ : P) :=
               congrArg₂ (fun u v : P => u + v) (by simpa using ha) (by simpa using hb)
            _ = (a+b) • (⟨w.1,w.2⟩ : P) := by rw [add_smul]
        | single g a =>
          ext
          let ρT : Representation ℂ L T := T.ρ
          change (((MonoidAlgebra.single g a) • (w : τ.asModule)) : τ.asModule).1 =
            (((MonoidAlgebra.single g a) •
               (show ρT.asModule from w.1)) : ρT.asModule)
          rw [Representation.single_smul (ρ:=τ),
              Representation.single_smul (ρ:=ρT)]
          rfl

    }
  have hsimpM : IsSimpleModule ℂ[L] τ.asModule := by
    exact (LinearEquiv.isSimpleModule_iff e).2
      (inferInstance : IsSimpleModule ℂ[L] P)
  letI : Representation.IsIrreducible τ :=
    (Representation.irreducible_iff_isSimpleModule_asModule τ).2 hsimpM
  -- compare endomorphisms linear equivalences
  calc
    Module.finrank ℂ ((subFD L T P) ⟶ (subFD L T P)) =
        Module.finrank ℂ
          ((((forget₂ (FDRep ℂ L) (Rep ℂ L)).obj (subFD L T P)) ⟶
            ((forget₂ (FDRep ℂ L) (Rep ℂ L)).obj (subFD L T P)))) := by
              -- equivalence is opposite direction
              symm
              exact LinearEquiv.finrank_eq (FDRep.forget₂HomLinearEquiv (subFD L T P) (subFD L T P))
    _ = Module.finrank ℂ (τ.IntertwiningMap τ) := by
          -- rep hom linear equivalence
          exact LinearEquiv.finrank_eq (Rep.homLinearEquiv ((forget₂ (FDRep ℂ L) (Rep ℂ L)).obj (subFD L T P)) _)
    _ = 1 := by
      exact Representation.IsIrreducible.finrank_intertwiningMap_self τ

lemma finite_simple_fdrep_ranges (T : FDRep ℂ L) :
    ∃ (n : ℕ) (S : Fin n → FDRep ℂ L)
       (simpS : ∀ i, CategoryTheory.Simple (S i))
       (incl : ∀ i, S i ⟶ T),
       (⨆ i, LinearMap.range ((incl i).hom.hom.hom : S i →ₗ[ℂ] T)) = ⊤ := by
  obtain ⟨n,P,hP,hspan⟩ := finite_simple_submodules_span (L:=L) (Y:=T) T.ρ
  let S : Fin n → FDRep ℂ L := fun j => subFD L T (P j)
  let inc : ∀ j : Fin n, S j ⟶ T := fun j => subIncl L T (P j)
  have si : ∀ j, CategoryTheory.Simple (S j) := by
    intro j
    letI : IsSimpleModule ℂ[L] (P j) := hP j
    exact subFD_simple L T (P j)
  refine ⟨n, S, si, inc, ?_⟩
  -- the ranges of the subtype maps just are the scalar-restricted submodules
  -- use hspan after comparing lattices via membership
  have eqj : ∀ j,
      LinearMap.range ((inc j).hom.hom.hom : S j →ₗ[ℂ] T) =
        (P j).restrictScalars ℂ := by
    intro j
    -- ext by elements
    ext v
    constructor
    · rintro ⟨w, hw⟩
      change (v : T) ∈ (P j)
      change (v : T) ∈ (P j) -- maybe change
      change w.1 = v at hw
      subst v
      exact w.property
    · intro hv
      change (v : T) ∈ (P j) at hv
      refine ⟨(⟨v, hv⟩ : S j), ?_⟩
      rfl
  -- show iSup = top using hspan and order relation between module submodules
  calc
    (⨆ i, LinearMap.range ((inc i).hom.hom.hom : S i →ₗ[ℂ] T)) =
        (⨆ i, (P i).restrictScalars ℂ) := iSup_congr eqj
    _ = (⨆ i, P i).restrictScalars ℂ :=
      (Submodule.restrictScalars_iSup (S:=ℂ) P).symm
    _ = ⊤ := by rw [hspan, Submodule.restrictScalars_top]
end FrobeniusKernel

end

-- END INLINED FILE: Mathlib/Support/frobenius_kernel_isNormal_bde655671f/Summands.lean

-- BEGIN INLINED FILE: Mathlib/Support/frobenius_kernel_isNormal_bde655671f/Basis.lean
open scoped BigOperators Classical MonoidAlgebra
open CategoryTheory
noncomputable section
namespace FrobeniusKernel
variable (L : Type) [Group L] [Fintype L]

lemma eq_zero_of_simple_pairs
    {ι : Sort*} (S : ι → FDRep ℂ L)
    (simpleS : ∀ i, CategoryTheory.Simple (S i))
    (incl : ∀ i, S i ⟶ leftRegularObj L)
    (hspan : (⨆ i, LinearMap.range
      ((incl i).hom.hom.hom : S i →ₗ[ℂ] leftRegularObj L)) = ⊤)
    (f : L → ℂ) (hf : CentralFun L f)
    (hz : ∀ i, charPair L f (S i).character = 0) : f = 0 := by
  have hz' : ∀ i, centralOperator L f (S i) = 0 := by
    intro i
    letI : CategoryTheory.Simple (S i) := simpleS i
    exact centralOperator_eq_zero_of_simple L f hf (S i) (hz i)
  exact centralOperator_leftRegular_injective L f <|
    centralOperator_eq_zero_of_ranges L f (leftRegularObj L) S incl hspan hz'

lemma char_central (T : FDRep ℂ L) : CentralFun L T.character := by
  intro c g
  -- character of conjugates
  simp

lemma charPair_simple (A B : FDRep ℂ L)
    [CategoryTheory.Simple A] [CategoryTheory.Simple B] :
    charPair L A.character B.character =
      if Nonempty (A ≅ B) then (Fintype.card L : ℂ) else 0 := by
  classical
  letI : Invertible (Fintype.card L : ℂ) :=
    invertibleOfNonzero (by exact_mod_cast (Fintype.card_ne_zero : Fintype.card L ≠ 0))
  have h := FDRep.char_orthonormal A B
  -- cancel inverse
  rw [smul_eq_mul] at h
  -- inverse scalar unit
  by_cases e : Nonempty (A ≅ B)
  · simp [e] at h ⊢
    have hc : (Fintype.card L : ℂ) ≠ 0 := by exact_mod_cast (Fintype.card_ne_zero : Fintype.card L ≠ 0)
    -- h : ⅟ ... * sum = 1
    have hi : (⅟(Fintype.card L : ℂ)) = ((Fintype.card L : ℂ)⁻¹) :=
      invOf_eq_inv _
    have := h
    have := congrArg (fun z : ℂ => (Fintype.card L : ℂ) * z) this
    -- field simplification
    -- left side reduces to the original unnormalised sum
    simpa [charPair, hc] using this
  · simp [e] at h ⊢
    have hi : (⅟(Fintype.card L : ℂ)) = ((Fintype.card L : ℂ)⁻¹) := invOf_eq_inv _
    have hc : ((Fintype.card L : ℂ)⁻¹) ≠ 0 := by
      have : (Fintype.card L : ℂ) ≠ 0 := by exact_mod_cast (Fintype.card_ne_zero : Fintype.card L ≠ 0)
      exact inv_ne_zero this
    -- h product zero
    simpa [charPair] using h

lemma charPair_sub_left (f q r : L → ℂ) :
    charPair L (fun g => f g - q g) r = charPair L f r - charPair L q r := by
  classical
  unfold charPair
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]

lemma charPair_smul_left (z : ℂ) (f q : L → ℂ) :
    charPair L (fun g => z * f g) q = z * charPair L f q := by
  classical
  unfold charPair
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma central_sub (f q : L → ℂ) (hf : CentralFun L f) (hq : CentralFun L q) :
    CentralFun L (fun g => f g - q g) := by
  intro c g
  simp [hf c g, hq c g]

lemma central_smul (z : ℂ) (f : L → ℂ) (hf : CentralFun L f) :
    CentralFun L (fun g => z * f g) := by
  intro c g
  simp [hf c g]
end FrobeniusKernel

namespace FrobeniusKernel
open scoped BigOperators Classical MonoidAlgebra
open CategoryTheory
noncomputable section
variable (L : Type) [Group L] [Fintype L]

lemma eq_smul_char_of_simple_pairs
    {ι : Sort*} (S : ι → FDRep ℂ L)
    (simpleS : ∀ i, CategoryTheory.Simple (S i))
    (incl : ∀ i, S i ⟶ leftRegularObj L)
    (hspan : (⨆ i, LinearMap.range
      ((incl i).hom.hom.hom : S i →ₗ[ℂ] leftRegularObj L)) = ⊤)
    (i : ι) (c : ℂ) (f : L → ℂ) (hf : CentralFun L f)
    (hp : ∀ j, charPair L f (S j).character =
      if Nonempty (S i ≅ S j) then c * (Fintype.card L : ℂ) else 0) :
    f = (fun g => c * (S i).character g) := by
  letI : CategoryTheory.Simple (S i) := simpleS i
  -- subtract the single character and use detection by the regular object
  have hz : ∀ j,
      charPair L (fun g => f g - c * (S i).character g) (S j).character = 0 := by
    intro j
    letI : CategoryTheory.Simple (S j) := simpleS j
    rw [charPair_sub_left]
    rw [charPair_smul_left]
    rw [charPair_simple L (S i) (S j)]
    rw [hp j]
    split_ifs with h
    · ring
    · simp
  have hc' : CentralFun L (fun g => c * (S i).character g) :=
    central_smul L c _ (char_central L (S i))
  have h0 := eq_zero_of_simple_pairs L S simpleS incl hspan
      (fun g => f g - c * (S i).character g) (central_sub L f _ hf hc') hz
  funext g
  have := congrFun h0 g
  simp at this
  exact sub_eq_zero.mp this
end
end FrobeniusKernel

end

-- END INLINED FILE: Mathlib/Support/frobenius_kernel_isNormal_bde655671f/Basis.lean

-- BEGIN INLINED FILE: Mathlib/Support/frobenius_kernel_isNormal_bde655671f/Positive.lean
open scoped BigOperators Classical
open CategoryTheory
noncomputable section
namespace FrobeniusKernel
variable (L : Type) [Group L] [Fintype L]
/-- The sign in a norm-one virtual row is positive as soon as its value at one
is the (positive) dimension.  All inner products here are the bilinear,
unnormalised ones. -/
lemma scalar_eq_one_of_row (T : FDRep ℂ L) [CategoryTheory.Simple T]
    (d : ℕ) (hd : d ≠ 0) (f : L → ℂ) (c : ℂ)
    (hone : f 1 = (d : ℂ))
    (hnorm : charPair L f f = (Fintype.card L : ℂ))
    (hrow : f = fun g => c * T.character g) : c = 1 := by
  have ht : T.character 1 = (Module.finrank ℂ T : ℂ) := by simp
  have ht0nat : Module.finrank ℂ T ≠ 0 := by
    intro h
    have ss : Subsingleton T := (Module.finrank_zero_iff).1 h
    have hi : (CategoryTheory.CategoryStruct.id T : T ⟶ T) = 0 := by
      ext v
      change v = 0
      exact @Subsingleton.elim T ss _ _
    exact CategoryTheory.id_nonzero T hi
  have ht0 : (Module.finrank ℂ T : ℂ) ≠ 0 := by exact_mod_cast ht0nat
  have hcval : c * (Module.finrank ℂ T : ℂ) = (d : ℂ) := by
    simpa [hrow, ht] using hone
  have hcard : (Fintype.card L : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card L ≠ 0)
  have hcc : c * c = (1 : ℂ) := by
    have hTpair : charPair L T.character T.character = (Fintype.card L : ℂ) := by
      simpa [Nonempty.intro (Iso.refl T)] using (charPair_simple L T T)
    have hfcalc : charPair L f f = (c*c) * charPair L T.character T.character := by
      classical
      subst f
      unfold charPair
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro g _
      ring
    rw [hfcalc, hTpair] at hnorm
    exact (mul_right_cancel₀ hcard (by simpa using hnorm))
  rcases (mul_self_eq_one_iff.mp hcc) with hp | hm
  · exact hp
  · exfalso
    rw [hm] at hcval
    have hcastpos : (0:ℝ) < d := by exact_mod_cast (Nat.pos_of_ne_zero hd)
    have htpos : (0:ℝ) < Module.finrank ℂ T := by exact_mod_cast (Nat.pos_of_ne_zero ht0nat)
    -- equality `-(finrank)=d` is impossible by real parts
    have hz := congrArg Complex.re hcval
    norm_num at hz
    norm_num at hz
    have : ¬ (-(Module.finrank ℂ T : ℝ) = (d:ℝ)) := by linarith
    exact this (by exact_mod_cast hz)
end FrobeniusKernel

end

-- END INLINED FILE: Mathlib/Support/frobenius_kernel_isNormal_bde655671f/Positive.lean

-- BEGIN INLINED FILE: Mathlib/Support/frobenius_kernel_isNormal_bde655671f/Row.lean
open scoped BigOperators Classical MonoidAlgebra
open CategoryTheory
noncomputable section
namespace FrobeniusKernel
variable (L : Type) [Group L] [Fintype L]

-- A finite spanning list of simple objects is already a full character table.
-- A central function of norm one-sized group with integral coefficients on that
-- table has a single row, up to a sign.  We keep repeated isomorphic summands
-- in the list; the proof passes to their quotient.
lemma single_row_of_integer_norm
    (n : ℕ) (S : Fin n → FDRep ℂ L)
    (simpleS : ∀ i, CategoryTheory.Simple (S i))
    (incl : ∀ i, S i ⟶ leftRegularObj L)
    (hspan : (⨆ i, LinearMap.range
      ((incl i).hom.hom.hom : S i →ₗ[ℂ] leftRegularObj L)) = ⊤)
    (f : L → ℂ) (hf : CentralFun L f)
    (hnorm : charPair L f f = (Fintype.card L : ℂ))
    (hint : ∀ j : Fin n, ∃ z : ℤ,
       charPair L f (S j).character = (Fintype.card L : ℂ) * (z : ℂ)) :
    ∃ (i : Fin n) (z : ℤ), (z = 1 ∨ z = -1) ∧
      ∀ j : Fin n, charPair L f (S j).character =
        if Nonempty (S i ≅ S j) then (z : ℂ) * (Fintype.card L : ℂ) else 0 := by
  classical
  let D : ℂ := (Fintype.card L : ℂ)
  have hD : D ≠ 0 := by
    dsimp [D]
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card L ≠ 0)
  -- chosen integral coefficients, one for each occurrence
  choose zfun hzfun using hint
  -- package isomorphism classes of the (possibly repeated) finite list
  let r : Setoid (Fin n) :=
    { r := fun i j => Nonempty (S i ≅ S j)
      iseqv :=
        { refl := fun i => ⟨Iso.refl _⟩
          symm := fun {i j} h => ⟨(Classical.choice h).symm⟩
          trans := fun {i j k} h h' =>
            ⟨(Classical.choice h).trans (Classical.choice h')⟩ } }
  let Q := Quotient r
  letI : Fintype Q := Fintype.ofFinite Q
  let rep : Q → Fin n := fun q => Quotient.out q
  have rep_mk (j : Fin n) : r (rep (Quotient.mk r j)) j := by
    -- `out` is related to the element it represents
    exact Quotient.mk_out j
  have mk_rep (q : Q) : Quotient.mk r (rep q) = q := by
    -- quotient induction avoids any reference to a chosen order
    refine Quotient.inductionOn q ?_
    intro j
    exact Quotient.sound (rep_mk j)
  have rel_iff (q : Q) (j : Fin n) :
      Nonempty (S (rep q) ≅ S j) ↔ q = Quotient.mk r j := by
    constructor
    · intro h
      have hr : r (rep q) j := h
      have e : Quotient.mk r (rep q) = Quotient.mk r j := Quotient.sound hr
      simpa [mk_rep q] using e
    · intro e
      have e' : Quotient.mk r (rep q) = Quotient.mk r j := by simpa [mk_rep q] using e
      exact (Quotient.eq).1 e'
  -- coefficients are constant on each isomorphism class
  have z_eq {i j : Fin n} (h : Nonempty (S i ≅ S j)) : zfun i = zfun j := by
    have hc : (S i).character = (S j).character := FDRep.char_iso (Classical.choice h)
    have hp : charPair L f (S i).character = charPair L f (S j).character := by rw [hc]
    have he : D * (zfun i : ℂ) = D * (zfun j : ℂ) := by
      simpa [D, hzfun i, hzfun j] using hp
    have he' : (zfun i : ℂ) = (zfun j : ℂ) := by
      exact (mul_left_cancel₀ hD he)
    exact_mod_cast he'
  let zq : Q → ℤ := fun q => zfun (rep q)
  -- Pairing an explicit sum with a table row picks just its class coefficient.
  let rows : L → ℂ := fun g =>
    ∑ q : Q, (zq q : ℂ) * (S (rep q)).character g
  have pair_rows (j : Fin n) :
      charPair L rows (S j).character = D * (zfun j : ℂ) := by
    -- distribute the finite sum through the left slot
    have expand : charPair L rows (S j).character =
        ∑ q : Q, (zq q : ℂ) *
          charPair L (S (rep q)).character (S j).character := by
      unfold charPair
      dsimp [rows]
      -- exchange the two finite sums
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      -- pull the scalar out
      apply Finset.sum_congr rfl
      intro q hq
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro g hg
      ring
    rw [expand]
    -- orthogonality of simple rows; all but the represented class vanish
    have ev (q : Q) :
        (zq q : ℂ) * charPair L (S (rep q)).character (S j).character =
          if h : q = Quotient.mk r j then
            (zq q : ℂ) * D else 0 := by
      letI : CategoryTheory.Simple (S (rep q)) := simpleS (rep q)
      letI : CategoryTheory.Simple (S j) := simpleS j
      rw [charPair_simple L (S (rep q)) (S j)]
      by_cases hrel : Nonempty (S (rep q) ≅ S j)
      · have hqj : q = Quotient.mk r j := (rel_iff q j).1 hrel
        have hrel' : Nonempty (S (rep (Quotient.mk r j)) ≅ S j) :=
          (rel_iff (Quotient.mk r j) j).2 rfl
        simp [hrel', hqj, D]
      · have hqj : q ≠ Quotient.mk r j := by
          intro e
          exact hrel ((rel_iff q j).2 e)
        simp [hrel, hqj]
    simp_rw [ev]
    -- the single surviving representative is the class of `j`
    classical
    have hmem : (Quotient.mk r j : Q) ∈ (Finset.univ : Finset Q) := Finset.mem_univ _
    have sone : (∑ q : Q, if h : q = Quotient.mk r j then
              (zq q : ℂ) * D else 0) =
          (zq (Quotient.mk r j) : ℂ) * D := by
      classical
      -- select the single member of `univ`
      simpa using
        (Finset.sum_ite_eq' (Finset.univ : Finset Q)
          (Quotient.mk r j) (fun q : Q => (zq q : ℂ) * D))
    rw [sone]
    have hzrep : zq (Quotient.mk r j) = zfun j := by
      apply z_eq
      exact rep_mk j
    simp [hzrep, mul_comm]
  -- detection on the left regular object identifies the central function
  have frows : f = rows := by
    have zer : ∀ j : Fin n,
        charPair L (fun g => f g - rows g) (S j).character = 0 := by
      intro j
      rw [charPair_sub_left]
      rw [pair_rows j]
      rw [hzfun j]
      simp [D]
    have hcrows : CentralFun L rows := by
      intro c g
      dsimp [rows]
      apply Finset.sum_congr rfl
      intro q hq
      -- character is central
      have hh := char_central L (S (rep q)) c g
      simp [hh]
    have hzero := eq_zero_of_simple_pairs L S simpleS incl hspan
        (fun g => f g - rows g) (central_sub L f rows hf hcrows) zer
    funext g
    have e := congrFun hzero g
    exact sub_eq_zero.mp e
  -- compute the norm through the expansion, using the coefficients themselves.
  have norm_coeff :
      (∑ q : Q, (zq q : ℂ) * (zq q : ℂ)) = (1 : ℂ) := by
    -- pair f with the displayed expansion on the right
    have ex : charPair L f rows =
          ∑ q : Q, (zq q : ℂ) *
             charPair L f (S (rep q)).character := by
      -- use symmetry to use the left-linearity already established
      -- direct computation is short
      unfold charPair
      dsimp [rows]
      -- rows at inverse
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro q hq
      apply Finset.sum_congr rfl
      intro g hg
      ring
    have hn : charPair L f rows = D := by simpa [frows] using hnorm
    rw [ex] at hn
    -- substitute the known coefficient for each representative
    have hv (q : Q) :
        charPair L f (S (rep q)).character = D * (zq q : ℂ) := by
      simpa [D, zq] using hzfun (rep q)
    simp_rw [hv] at hn
    -- divide by the nonzero group order
    -- all terms are `(zq)^2 * D`
    have : D * (∑ q : Q, (zq q : ℂ) * (zq q : ℂ)) = D * 1 := by
      simp only [mul_one]
      rw [Finset.mul_sum]
      -- both sides are the same finite sum, just associated differently
      calc
        (∑ q : Q, D * ((zq q : ℂ) * (zq q : ℂ))) =
            ∑ q : Q, (zq q : ℂ) * (D * (zq q : ℂ)) := by
              apply Finset.sum_congr rfl
              intro q hq
              ring
        _ = D := hn
    exact mul_left_cancel₀ hD this
  have norm_int : (∑ q : Q, zq q * zq q) = (1 : ℤ) := by
    have hcast : ((∑ q : Q, zq q * zq q : ℤ) : ℂ) = (1 : ℂ) := by
      -- sum and products commute with the cast
      simpa using norm_coeff
    exact_mod_cast hcast
  -- a finite sum of integral squares equal to one has a single nonzero term
  have existsq : ∃ q : Q, zq q ≠ 0 := by
    by_contra h
    push_neg at h
    have hs : (∑ q : Q, zq q * zq q) = (0 : ℤ) := by simp [h]
    rw [hs] at norm_int
    norm_num at norm_int
  obtain ⟨q0, hq0⟩ := existsq
  have nonneg (q : Q) : 0 ≤ zq q * zq q := mul_self_nonneg _
  have split : (∑ q : Q, zq q * zq q) =
       zq q0 * zq q0 + ∑ q ∈ (Finset.univ.erase q0), zq q * zq q := by
    classical
    have hmem : q0 ∈ (Finset.univ : Finset Q) := Finset.mem_univ _
    have := (Finset.add_sum_erase (Finset.univ : Finset Q)
      (fun q => zq q * zq q) hmem)
    -- `add_sum_erase` puts the distinguished term first
    simpa using this.symm
  have hle : zq q0 * zq q0 ≤ (1 : ℤ) := by
    rw [split] at norm_int
    have hother : 0 ≤ ∑ q ∈ (Finset.univ.erase q0), zq q * zq q := by
      exact Finset.sum_nonneg (by
        intro i hi; exact nonneg i)
    omega
  have hge : (1 : ℤ) ≤ zq q0 * zq q0 := by
    have hn0 : zq q0 * zq q0 ≠ 0 := (mul_self_ne_zero.mpr hq0)
    have hz0 := nonneg q0
    omega
  have hone0 : zq q0 * zq q0 = (1 : ℤ) := le_antisymm hle hge
  have hsgn : zq q0 = (1 : ℤ) ∨ zq q0 = (-1 : ℤ) := (mul_self_eq_one_iff).1 hone0
  have hrest : ∀ q : Q, q ≠ q0 → zq q = 0 := by
    intro q hneq
    have hmemq : q ∈ (Finset.univ.erase q0 : Finset Q) :=
      Finset.mem_erase.mpr ⟨hneq, Finset.mem_univ _⟩
    have hrzero : (∑ p ∈ (Finset.univ.erase q0), zq p * zq p) = (0 : ℤ) := by
      rw [split] at norm_int
      rw [hone0] at norm_int
      omega
    have each : zq q * zq q = 0 := by
      have : ∀ i ∈ (Finset.univ.erase q0 : Finset Q), zq i * zq i = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (by
          intro i hi; exact nonneg i)).1 hrzero
      exact this q hmemq
    exact (mul_self_eq_zero.mp each)
  -- return the chosen occurrence and its sign-profile
  refine ⟨rep q0, zq q0, hsgn, ?_⟩
  intro j
  have hj :
      charPair L f (S j).character = D * (zfun j : ℂ) := by
    simpa [D] using hzfun j
  by_cases hrel : Nonempty (S (rep q0) ≅ S j)
  · have eqq : (Quotient.mk r j : Q) = q0 := (rel_iff q0 j).1 hrel |>.symm
    have zjeq : zfun j = zq q0 := by
      -- compare with the representative of this class
      have hr : Nonempty (S (rep q0) ≅ S j) := hrel
      have := z_eq hr
      simpa [zq] using this.symm
    simp [hrel, hj, zjeq, D, mul_comm]
  · have neq : (Quotient.mk r j : Q) ≠ q0 := by
      intro e
      exact hrel ((rel_iff q0 j).2 e.symm)
    have hzj0 : zfun j = 0 := by
      have hr := hrest (Quotient.mk r j) neq
      -- its representative has the same coefficient
      have ze : zq (Quotient.mk r j) = zfun j := z_eq (rep_mk j)
      rw [ze] at hr
      exact hr
    simp [hrel, hj, hzj0]
end FrobeniusKernel

end

-- END INLINED FILE: Mathlib/Support/frobenius_kernel_isNormal_bde655671f/Row.lean

namespace Submission

-- BEGIN INLINED FILE: Main.lean
open scoped MonoidAlgebra
/-ResultDefinitionsBegin-/
/-ResultProofDefinitionsBegin-/
/-ResultProofDefinitionsEnd-/
/-ResultDefinitionsEnd-/

/-ResultBegin-/

theorem frobenius_kernel_isNormal (G X : Type) [Group G] [Fintype G] [Fintype X]
    [MulAction G X] [FaithfulSMul G X]
    (hcard : 2 ≤ Fintype.card X)
    (htrans : ∀ x y : X, ∃ g : G, g • x = y)
    (hstab : ∀ x : X, MulAction.stabilizer G x ≠ ⊥)
    (hfrob : ∀ g : G, g ≠ 1 → ∀ x y : X, g • x = x → g • y = y → x = y) :
    ∃ N : Subgroup G, N.Normal ∧
      (N : Set G) = {1} ∪ {g : G | ∀ x : X, g • x ≠ x} :=
/-ResultProofBegin-/by
  classical
  -- Inverses and conjugates of the prospective Frobenius kernel cause no
  -- difficulty.  We isolate the genuine content as multiplication-closure.
  -- This way the normality part of the goal does not get mixed up with it.
  apply FrobeniusKernel.exists_normal_of_mul_closed (G := G) (X := X)
  intro a b ha hb
  rcases (FrobeniusKernel.mem_kerSet (G := G) (X := X) a).1 ha with h1 | ha_free
  · subst a
    simpa using hb
  · rcases (FrobeniusKernel.mem_kerSet (G := G) (X := X) b).1 hb with h1 | hb_free
    · subst b
      simpa using ha
    · apply (FrobeniusKernel.mem_kerSet (G := G) (X := X) (a * b)).2
      by_cases hab : a * b = 1
      · exact Or.inl hab
      · refine Or.inr ?_
        intro x hx
        -- We can make the local TI/normalizer consequences completely
        -- explicit.  They do not use a closure assertion about the kernel.
        have huniq : ∀ y : X, (a * b) • y = y → y = x := by
          intro y hy
          exact (hfrob (a*b) hab y x hy hx)
        have hnormal :
            Subgroup.normalizer (MulAction.stabilizer G x : Set G) ≤
              MulAction.stabilizer G x :=
          FrobeniusKernel.normalizer_stabilizer_le G X hfrob x (hstab x)
        have han : a ∉ Subgroup.normalizer (MulAction.stabilizer G x : Set G) := by
          intro ha
          exact ha_free x ((MulAction.mem_stabilizer_iff).1 (hnormal ha))
        have hbn : b ∉ Subgroup.normalizer (MulAction.stabilizer G x : Set G) := by
          intro hb
          exact hb_free x ((MulAction.mem_stabilizer_iff).1 (hnormal hb))
        have hnon : Nonempty X :=
          Fintype.card_pos_iff.mp
            (lt_of_lt_of_le (by decide : 0 < (2:ℕ)) hcard)
        have hkernel_card :
            Fintype.card (FrobeniusKernel.KerElem G X) = Fintype.card X :=
          FrobeniusKernel.card_kerElem_of_transitive G X hfrob htrans hnon
        -- We can at least carry out, in the kernel, the *class-function* part
        -- of the character-theoretic argument.  The `tilde` below is the
        -- usual extension
        --   Ind_H^G (φ-φ(1)) + φ(1)·1
        -- at the level of functions.  `indSum` is the transporter sum, so no
        -- assertion about representations is hidden in these equalities.
        -- The TI computation above is precisely what makes the two value
        -- formulae true.
        let H := MulAction.stabilizer G x
        have habx : a * b ∈ H :=
          (MulAction.mem_stabilizer_iff).2 hx
        have htable_stab :
            ∀ (φ : (MulAction.stabilizer G x) → ℂ)
              (hc : FrobeniusKernel.ClassOnStab G X x φ),
            FrobeniusKernel.tilde G X x φ (φ 1) (a*b) =
                φ ⟨a*b, habx⟩ := by
          intro φ hc
          simpa using
            (FrobeniusKernel.tilde_stab G X hfrob x φ (φ 1) hc hab hx)
        have htable_a :
            ∀ (φ : (MulAction.stabilizer G x) → ℂ),
              FrobeniusKernel.tilde G X x φ (φ 1) a = φ 1 := by
          intro φ
          exact FrobeniusKernel.tilde_free G X x φ (φ 1) ha_free
        have htable_b :
            ∀ (φ : (MulAction.stabilizer G x) → ℂ),
              FrobeniusKernel.tilde G X x φ (φ 1) b = φ 1 := by
          intro φ
          exact FrobeniusKernel.tilde_free G X x φ (φ 1) hb_free
        have htable_one :
            ∀ (φ : (MulAction.stabilizer G x) → ℂ),
              FrobeniusKernel.tilde G X x φ (φ 1) (1:G) = φ 1 := by
          intro φ
          exact FrobeniusKernel.tilde_one G X x φ (φ 1) rfl
        -- The regular character of the stabilizer is a concrete single
        -- class function that would suffice.  Its extension takes the common
        -- degree on both derangements but vanishes at our putative product.
        have habH : (⟨a*b, habx⟩ : MulAction.stabilizer G x) ≠ 1 := by
          intro hz
          apply hab
          have hz' := congrArg
            (fun u : MulAction.stabilizer G x => (u : G)) hz
          simpa using hz'
        have hreg_prod :
            FrobeniusKernel.tilde G X x
              (FrobeniusKernel.regularStab G X x)
              ((Fintype.card (MulAction.stabilizer G x) : ℂ)) (a*b) = 0 := by
          have hv := htable_stab (FrobeniusKernel.regularStab G X x)
              (FrobeniusKernel.regularStab_class G X x)
          -- its value on a nonidentity stabilizer element is zero
          simpa [FrobeniusKernel.regularStab, habH] using hv
        have hreg_a :
            FrobeniusKernel.tilde G X x
              (FrobeniusKernel.regularStab G X x)
              ((Fintype.card (MulAction.stabilizer G x) : ℂ)) a =
                (Fintype.card (MulAction.stabilizer G x) : ℂ) := by
          have hv := htable_a (FrobeniusKernel.regularStab G X x)
          simpa using hv
        have hreg_b :
            FrobeniusKernel.tilde G X x
              (FrobeniusKernel.regularStab G X x)
              ((Fintype.card (MulAction.stabilizer G x) : ℂ)) b =
                (Fintype.card (MulAction.stabilizer G x) : ℂ) := by
          have hv := htable_b (FrobeniusKernel.regularStab G X x)
          simpa using hv
        -- These equalities isolate the remaining prerequisite very tightly.
        -- One must show that, for irreducible characters `φ` of `H`, this
        -- class function is an *ordinary* character of `G`.  Its kernel
        -- would contain `a` and `b` by the second and third equations and
        -- exclude the nonidentity stabilizer elements by the first equation;
        -- closure of the kernel would contradict `hx`.  Proving ordinariness
        -- (not the table itself) is Frobenius' integral lifting theorem.
        -- A useful next portion of the character argument is already formal at
        -- the level of scalar products: the extension is an isometry on
        -- irreducible characters.  This uses the double transporter sum; a
        -- tempting but incorrect shortcut is to treat the regular table as
        -- a representation.  In particular the still-missing assertion below
        -- is at least the *integrality/positivity* assertion, not orthogonality.
        have hsimplenorm (V W : FDRep ℂ (MulAction.stabilizer G x))
            [CategoryTheory.Simple V] [CategoryTheory.Simple W] :
            (∑ g:G,
              FrobeniusKernel.tilde G X x V.character (V.character 1) g *
              FrobeniusKernel.tilde G X x W.character (W.character 1) g⁻¹) =
                 if Nonempty (V ≅ W) then (Fintype.card G : ℂ) else 0 :=
          FrobeniusKernel.tilde_simple_inner G X hfrob x V W
        -- Reciprocity/integrality is a separate issue from the norm
        -- computation above.  Unfolding the transporter and restricting an
        -- arbitrary representation of `G` to the point stabilizer gives the
        -- following completely integral scalar product.  This is the usual
        -- "generalised character" half of the extension argument.
        have hgeneralized (V : FDRep ℂ (MulAction.stabilizer G x))
            (T : FDRep ℂ G) :
            (∑ g:G,
              FrobeniusKernel.tilde G X x V.character (V.character 1) g *
                T.character g⁻¹) =
             (Fintype.card G : ℂ) *
               ((Module.finrank ℂ ((FrobeniusKernel.resStab G X x T) ⟶ V) : ℂ)
                - (Module.finrank ℂ V : ℂ) *
                   (Module.finrank ℂ
                     ((FrobeniusKernel.resStab G X x T) ⟶
                       FrobeniusKernel.trivRep (MulAction.stabilizer G x)) : ℂ)
                + (Module.finrank ℂ V : ℂ) *
                   (Module.finrank ℂ
                     (T ⟶ FrobeniusKernel.trivRep G) : ℂ)) :=
          FrobeniusKernel.tilde_char_integer G X x V T
        have hintercoeff (V : FDRep ℂ (MulAction.stabilizer G x))
            (T : FDRep ℂ G) :
            ∃ z : ℤ,
              (∑ g:G,
                FrobeniusKernel.tilde G X x V.character (V.character 1) g *
                  T.character g⁻¹) = (Fintype.card G : ℂ) * (z : ℂ) :=
          FrobeniusKernel.tilde_char_integer_int G X x V T

        -- The next obstruction in making the generalized character ordinary is
        -- *separation*: irreducible characters of `G` must span its class
        -- functions.  A useful way to state the exact half of this which uses
        -- no character-table assertion is in terms of central class sums.  The
        -- tilde functions really are central on all of `G`, not just the three
        -- values above.
        have htildeCentral (V : FDRep ℂ (MulAction.stabilizer G x)) :
            FrobeniusKernel.CentralFun G
              (FrobeniusKernel.tilde G X x V.character (V.character 1)) := by
          intro c g
          exact FrobeniusKernel.tilde_conj G X x V.character (V.character 1) g c
        -- Thus if the coefficient against a simple character vanishes, the
        -- corresponding central element acts as zero on that simple.  This is
        -- the Schur-lemma step of the missing separation argument.  Notice the
        -- index is inverted in `centralOperator`: this is exactly why our
        -- integral scalar product above is the right one; no complex conjugate
        -- or positivity assertion is being snuck in here.
        have hzeroOnSimple
            (V : FDRep ℂ (MulAction.stabilizer G x))
            (T : FDRep ℂ G) [CategoryTheory.Simple T]
            (hz : (∑ g:G,
              FrobeniusKernel.tilde G X x V.character (V.character 1) g *
                T.character g⁻¹) = 0) :
            FrobeniusKernel.centralOperator G
              (FrobeniusKernel.tilde G X x V.character (V.character 1)) T = 0 :=
          FrobeniusKernel.centralOperator_eq_zero_of_simple G _
             (htildeCentral V) T hz
        have hfaithfulClass
            (f : G → ℂ) (hf : FrobeniusKernel.CentralFun G f)
            (hz : FrobeniusKernel.centralOperator G f
              (FrobeniusKernel.leftRegularObj G) = 0) :
              f = 0 :=
          FrobeniusKernel.centralOperator_leftRegular_injective G f hz
        have hpairSeparation
            (f : G → ℂ) (hc : FrobeniusKernel.CentralFun G f)
            (hz : ∀ q : G → ℂ, FrobeniusKernel.CentralFun G q →
                (∑ g:G, f g * q (g⁻¹)) = 0) : f = 0 :=
          FrobeniusKernel.centralPairing_nondegenerate G f hc hz
        -- In particular the class sum attached to a simple stabilizer
        -- character cannot vanish on the regular object. What remains is
        -- to decompose that object (or its centre) into simple constituents.
        have hregularWitness (V : FDRep ℂ (MulAction.stabilizer G x))
            [CategoryTheory.Simple V] :
            FrobeniusKernel.centralOperator G
              (FrobeniusKernel.tilde G X x V.character (V.character 1))
              (FrobeniusKernel.leftRegularObj G) ≠ 0 := by
          intro hz
          have fz := FrobeniusKernel.centralOperator_leftRegular_injective G
              (FrobeniusKernel.tilde G X x V.character (V.character 1)) hz
          have hv := congrFun fz (1:G)
          have hdim : (Module.finrank ℂ V : ℂ) ≠ 0 := by
            have hn : ¬ Module.finrank ℂ V = 0 := by
              intro h0
              have ss : Subsingleton V := (Module.finrank_zero_iff).1 h0
              have eqid : (CategoryTheory.CategoryStruct.id V : V ⟶ V) = 0 := by
                ext v
                change v = 0
                exact @Subsingleton.elim V ss _ _
              exact CategoryTheory.id_nonzero V eqid
            exact_mod_cast hn
          have hone :
              FrobeniusKernel.tilde G X x V.character (V.character 1)
                  (1:G) = V.character 1 :=
            FrobeniusKernel.tilde_one G X x V.character (V.character 1) rfl
          have hzero :
              FrobeniusKernel.tilde G X x V.character (V.character 1)
                  (1:G) = 0 := by simpa using hv
          have hcharzero : V.character 1 = 0 := by
            calc
              V.character 1 = FrobeniusKernel.tilde G X x V.character (V.character 1) (1:G) := hone.symm
              _ = 0 := hzero
          have : V.character 1 = 0 := hcharzero
          exact hdim (by simpa using this)
        -- A precise formulation of the reduction to Maschke summands: any
        -- list of simple summands whose ranges span the regular object must
        -- contain a nonzero character-pairing coefficient.  The hypotheses
        -- here only mention the underlying ranges, so that a later
        -- decomposition proof need not construct categorical biproducts.
        have hcoefficientDetected
            (V : FDRep ℂ (MulAction.stabilizer G x)) [CategoryTheory.Simple V]
            (n : ℕ) (S : Fin n → FDRep ℂ G)
            (simpleS : ∀ i, CategoryTheory.Simple (S i))
            (incl : ∀ i, S i ⟶ FrobeniusKernel.leftRegularObj G)
            (hspan : (⨆ i, LinearMap.range
              ((incl i).hom.hom.hom : S i →ₗ[ℂ]
                FrobeniusKernel.leftRegularObj G)) = ⊤) :
            ∃ i, (∑ g:G,
              FrobeniusKernel.tilde G X x V.character (V.character 1) g *
                (S i).character g⁻¹) ≠ 0 := by
          classical
          by_contra hh
          push_neg at hh
          let f : G → ℂ :=
            FrobeniusKernel.tilde G X x V.character (V.character 1)
          have hzS : ∀ i, FrobeniusKernel.centralOperator G f (S i) = 0 := by
            intro i
            letI : CategoryTheory.Simple (S i) := simpleS i
            exact hzeroOnSimple V (S i) (by
              exact hh i)
          have hzreg : FrobeniusKernel.centralOperator G f
                (FrobeniusKernel.leftRegularObj G) = 0 := by
            exact FrobeniusKernel.centralOperator_eq_zero_of_ranges G f
              (FrobeniusKernel.leftRegularObj G) S incl hspan hzS
          exact hregularWitness V hzreg
        have hintegerDetected
            (V : FDRep ℂ (MulAction.stabilizer G x)) [CategoryTheory.Simple V]
            (n : ℕ) (S : Fin n → FDRep ℂ G)
            (simpleS : ∀ i, CategoryTheory.Simple (S i))
            (incl : ∀ i, S i ⟶ FrobeniusKernel.leftRegularObj G)
            (hspan : (⨆ i, LinearMap.range
              ((incl i).hom.hom.hom : S i →ₗ[ℂ]
                FrobeniusKernel.leftRegularObj G)) = ⊤) :
            ∃ (i : Fin n) (z : ℤ), z ≠ 0 ∧
              (∑ g:G,
               FrobeniusKernel.tilde G X x V.character (V.character 1) g *
                 (S i).character g⁻¹) = (Fintype.card G : ℂ) * (z : ℂ) := by
          obtain ⟨i, hi⟩ := hcoefficientDetected V n S simpleS incl hspan
          obtain ⟨z,hz⟩ := hintercoeff V (S i)
          have zn : z ≠ 0 := by
            intro e
            subst z
            simp at hz
            exact hi (by simpa using hz)
          exact ⟨i,z,zn,hz⟩
        -- Maschke really gives a finite family here.  It is important to take
        -- the module on the regular object (not just an arbitrary class
        -- function): finite-dimensionality upgrades the generally infinite
        -- semisimple decomposition to finitely many honest simple
        -- ℂ[G]-submodules.
        let ρregular : Representation ℂ G (FrobeniusKernel.leftRegularObj G) :=
          (FrobeniusKernel.leftRegularObj G).ρ
        have hmoduleFinite :
            ∃ (m : ℕ) (P : Fin m → Submodule ℂ[G] ρregular.asModule),
              Nonempty (ρregular.asModule ≃ₗ[ℂ[G]] Π₀ j : Fin m, P j) ∧
                ∀ j, IsSimpleModule ℂ[G] (P j) := by
          exact FrobeniusKernel.finite_simple_submodules G
            (FrobeniusKernel.leftRegularObj G) ρregular
        -- Retaining only that equivalence loses the fact that its summands are the
        -- *displayed* submodules.  The strengthened finite Maschke form keeps
        -- their supremum; this is the input needed to manufacture inclusions.
        have hmoduleSpan :
            ∃ (m : ℕ) (P : Fin m → Submodule ℂ[G] ρregular.asModule),
               (∀ j, IsSimpleModule ℂ[G] (P j)) ∧ (⨆ j, P j) = ⊤ := by
          exact FrobeniusKernel.finite_simple_submodules_span G
            (FrobeniusKernel.leftRegularObj G) ρregular
        -- Turn the spanning algebra submodules into honest objects of `FDRep`.
        -- The subtle point is that the group-algebra action on a subtype really
        -- is the subrepresentation action; `finite_simple_fdrep_ranges`
        -- installs this equivalence and the `Simple` instances.
        have hsummands :
            ∃ (m : ℕ) (S : Fin m → FDRep ℂ G)
              (_ : ∀ j, CategoryTheory.Simple (S j))
              (incl : ∀ j, S j ⟶ FrobeniusKernel.leftRegularObj G),
              (⨆ j, LinearMap.range
                ((incl j).hom.hom.hom : S j →ₗ[ℂ]
                  FrobeniusKernel.leftRegularObj G)) = ⊤ := by
          exact FrobeniusKernel.finite_simple_fdrep_ranges G
            (FrobeniusKernel.leftRegularObj G)
        obtain ⟨m,S,sS,incS,spanS⟩ := hsummands
        have hdetectedFinite
            (V : FDRep ℂ (MulAction.stabilizer G x)) [CategoryTheory.Simple V] :
            ∃ (i : Fin m) (z : ℤ), z ≠ 0 ∧
              (∑ g:G,
               FrobeniusKernel.tilde G X x V.character (V.character 1) g *
                 (S i).character g⁻¹) = (Fintype.card G : ℂ) * (z : ℂ) := by
          exact hintegerDetected V m S sS incS spanS
        -- Completeness can now be used entirely on this finite family.  In
        -- particular a central class function whose pairings with these
        -- objects vanish is zero; no choice of all simple objects is needed.
        have hfiniteSeparation
            (f : G → ℂ) (hc : FrobeniusKernel.CentralFun G f)
            (hz : ∀ j : Fin m,
                FrobeniusKernel.charPair G f (S j).character = 0) : f = 0 :=
          FrobeniusKernel.eq_zero_of_simple_pairs G S sS incS spanS f hc hz
        have hcharacterTableRow
            (i : Fin m) (c : ℂ) (f : G → ℂ)
            (hc : FrobeniusKernel.CentralFun G f)
            (hp : ∀ j : Fin m,
              FrobeniusKernel.charPair G f (S j).character =
                if Nonempty (S i ≅ S j) then
                  c * (Fintype.card G : ℂ) else 0) :
            f = (fun g => c * (S i).character g) :=
          FrobeniusKernel.eq_smul_char_of_simple_pairs G S sS incS spanS i c f hc hp
        -- Once a profile has just one nonzero isomorphism class, this is an
        -- *ordinary* row, not its negative.  This small sign point is often
        -- obscured by changing to Hermitian products; the following argument
        -- only uses the bilinear norm and the value at one.
        have hrowPositive
            (V : FDRep ℂ (MulAction.stabilizer G x)) [CategoryTheory.Simple V]
            (i : Fin m) (c : ℂ)
            (hp : ∀ j : Fin m,
              FrobeniusKernel.charPair G
                (FrobeniusKernel.tilde G X x V.character (V.character 1))
                (S j).character =
                 if Nonempty (S i ≅ S j) then
                   c * (Fintype.card G : ℂ) else 0) :
            c = 1 ∧
              FrobeniusKernel.tilde G X x V.character (V.character 1) =
                (S i).character := by
          let f : G → ℂ :=
            FrobeniusKernel.tilde G X x V.character (V.character 1)
          have eqr : f = fun g => c * (S i).character g :=
            hcharacterTableRow i c f (htildeCentral V) hp
          have hd : Module.finrank ℂ V ≠ 0 := by
            intro h0
            have ss : Subsingleton V := (Module.finrank_zero_iff).1 h0
            have hi : (CategoryTheory.CategoryStruct.id V : V ⟶ V) = 0 := by
              ext v
              change v = 0
              exact @Subsingleton.elim V ss _ _
            exact CategoryTheory.id_nonzero V hi
          have onef : f 1 = (Module.finrank ℂ V : ℂ) := by
            change FrobeniusKernel.tilde G X x V.character (V.character 1) 1 = _
            have := FrobeniusKernel.tilde_one G X x V.character (V.character 1) rfl
            simpa using this
          have normf : FrobeniusKernel.charPair G f f = (Fintype.card G : ℂ) := by
            have hh := hsimplenorm V V
            simpa [FrobeniusKernel.charPair, f, Nonempty.intro (CategoryTheory.Iso.refl V)] using hh
          have ce : c = 1 := by
            letI : CategoryTheory.Simple (S i) := sS i
            exact FrobeniusKernel.scalar_eq_one_of_row G (S i)
              (Module.finrank ℂ V) hd f c onef normf eqr
          refine ⟨ce, ?_⟩
          simpa [f, ce] using eqr
        -- Thus the virtual norm-one row really is an ordinary simple
        -- character.  `single_row_of_integer_norm` is careful to quotient
        -- the finite Maschke list by repeated isomorphic summands.
        have hord
            (V : FDRep ℂ (MulAction.stabilizer G x)) [CategoryTheory.Simple V] :
            ∃ i : Fin m,
              FrobeniusKernel.tilde G X x V.character (V.character 1) =
                (S i).character := by
          let f : G → ℂ :=
            FrobeniusKernel.tilde G X x V.character (V.character 1)
          have hn : FrobeniusKernel.charPair G f f = (Fintype.card G : ℂ) := by
            have h := hsimplenorm V V
            simpa [f, FrobeniusKernel.charPair,
              Nonempty.intro (CategoryTheory.Iso.refl V)] using h
          have hi : ∀ j : Fin m, ∃ z : ℤ,
                FrobeniusKernel.charPair G f (S j).character =
                  (Fintype.card G : ℂ) * (z : ℂ) := by
            intro j
            have := hintercoeff V (S j)
            simpa [FrobeniusKernel.charPair, f] using this
          obtain ⟨i,z,hz,hp⟩ :=
            FrobeniusKernel.single_row_of_integer_norm G m S sS incS spanS
              f (htildeCentral V) hn hi
          let c : ℂ := (z : ℂ)
          have hp' : ∀ j : Fin m,
                FrobeniusKernel.charPair G
                  (FrobeniusKernel.tilde G X x V.character (V.character 1))
                  (S j).character =
                    if Nonempty (S i ≅ S j) then
                       c * (Fintype.card G : ℂ) else 0 := by
            intro j
            simpa [c, f] using hp j
          exact ⟨i, (hrowPositive V i c hp').2⟩
        have hordinary
            (V : FDRep ℂ (MulAction.stabilizer G x)) [CategoryTheory.Simple V] :
            ∃ T : FDRep ℂ G, ∀ g : G,
                T.character g =
                  FrobeniusKernel.tilde G X x V.character (V.character 1) g := by
          obtain ⟨i, hi⟩ := hord V
          exact ⟨S i, fun g => (congrFun hi g).symm⟩
        have hsimpleTables
            (V : FDRep ℂ (MulAction.stabilizer G x)) [CategoryTheory.Simple V] :
            ∃ i : Fin m,
              (S i).character a = V.character 1 ∧
              (S i).character b = V.character 1 ∧
              (S i).character (1:G) = V.character 1 ∧
              (S i).character (a*b) = V.character ⟨a*b, habx⟩ := by
          obtain ⟨i, hi⟩ := hord V
          refine ⟨i, ?_, ?_, ?_, ?_⟩
          · rw [← congrFun hi a]
            exact htable_a V.character
          · rw [← congrFun hi b]
            exact htable_b V.character
          · rw [← congrFun hi (1:G)]
            exact htable_one V.character
          · rw [← congrFun hi (a*b)]
            have hv : FrobeniusKernel.ClassOnStab G X x V.character := by
              intro c t
              -- this is the usual class property of a character
              simpa using (FDRep.char_conj V t c⁻¹)
            exact htable_stab V.character hv
        -- Equality of a character value with its degree forces a group
        -- element to act as the identity: finite order makes the operator
        -- semisimple, and all its eigenvalues have real part at most one.
        -- (The analytic/algebraic lemma is in `KernelChar`.)  Applying it
        -- twice to the simple row above shows that the stabilizer element
        -- `⟨a*b,_⟩` is invisible in every simple stabilizer representation.
        let d : MulAction.stabilizer G x := ⟨a*b, habx⟩
        have hsimpleFix
            (V : FDRep ℂ (MulAction.stabilizer G x))
            [CategoryTheory.Simple V] : V.ρ d = 1 := by
          obtain ⟨i, hia, hib, hi1, hid⟩ := hsimpleTables V
          have ha' : (S i).character a = (S i).character (1:G) :=
            hia.trans hi1.symm
          have hb' : (S i).character b = (S i).character (1:G) :=
            hib.trans hi1.symm
          have ra : (S i).ρ a = 1 :=
            FrobeniusKernel.rho_eq_one_of_character_eq_one G (S i) a ha'
          have rb : (S i).ρ b = 1 :=
            FrobeniusKernel.rho_eq_one_of_character_eq_one G (S i) b hb'
          have rab : (S i).ρ (a*b) = 1 := by
            rw [map_mul, ra, rb]
            simp
          have habchar : (S i).character (a*b) = (S i).character (1:G) := by
            simp [FDRep.character, rab]
          have hvchar : V.character d = V.character 1 := by
            exact hid.symm.trans (habchar.trans hi1)
          exact FrobeniusKernel.rho_eq_one_of_character_eq_one
            (MulAction.stabilizer G x) V d hvchar
        -- The Maschke summands of the stabilizer *regular* object span it.
        -- Consequently an element acting as one on every simple acts as
        -- one on that faithful regular object.
        let RH : FDRep ℂ (MulAction.stabilizer G x) :=
          FrobeniusKernel.leftRegularObj (MulAction.stabilizer G x)
        obtain ⟨q, Q, sQ, uQ, spQ⟩ :=
          (FrobeniusKernel.finite_simple_fdrep_ranges
            (MulAction.stabilizer G x) RH)
        have hQR : RH.ρ d = 1 := by
          apply FrobeniusKernel.rho_eq_one_of_ranges
            (MulAction.stabilizer G x) d RH Q uQ spQ
          intro j
          letI : CategoryTheory.Simple (Q j) := sQ j
          exact hsimpleFix (Q j)
        have hd1 : d = 1 :=
          FrobeniusKernel.leftRegular_rho_injective_one
            (MulAction.stabilizer G x) d hQR
        exact habH hd1
/-ResultProofEnd-/
/-ResultEnd-/
-- END INLINED FILE: Main.lean

end Submission
