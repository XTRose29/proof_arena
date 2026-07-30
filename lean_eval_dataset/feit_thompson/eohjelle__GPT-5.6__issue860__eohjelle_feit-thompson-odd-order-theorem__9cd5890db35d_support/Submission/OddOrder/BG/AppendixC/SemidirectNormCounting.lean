import Submission.OddOrder.BG.AppendixC.FiniteFieldNormCocycle
import Submission.OddOrder.BG.AppendixC.NormEquationCharacterBranch
import Submission.OddOrder.BG.AppendixC.NormEquationCubic
import Submission.OddOrder.BG.AppendixC.SemidirectTIIntersection

/-!
# The norm-counting conclusion of Bender--Glauberman Appendix C

This file ports the logical end of `BGappendixC.v`, lines 569--762.  The
long group calculation in Lemma C.3, Step 4 ends at the source assertion
`EpsiV`: the pullback of the two-norm equation set is preserved by
`a ↦ (a⁻¹) ^ t³`.  The short odd-order iteration from `EpsiV` to plain
inversion is formalized here.  `NormPairInverseClosed` names the resulting
field-valued endpoint, and `BGappendixC3_Ediv` uses it to prove the inversion
stability needed by Lemma C.1.

The rest of the file combines the two already formalized branches of Lemma
C.2 and performs the concluding count.  The source-facing theorem is
currently conditional on two explicitly named obligations:

* `BGappendixC3Step4Obligation`, the remaining semidirect-product word
  calculation after the Step 3 TI-intersection theorem;
* `LargeDegreeCharacterObligation`, the identification and estimate of the
  class-product coefficient in the `4 < q` branch.

These are propositions, not axioms.  Keeping them visible makes the exact
remaining work explicit while the independently useful counting theorem is
available to downstream files.
-/

namespace Submission.OddOrder.BG.AppendixC

noncomputable section

open Submission.OddOrder.MathlibSupport
open scoped commutatorElement

universe u v w

variable {G : Type u} [Group G]

/-! ### The odd-order iteration in Step 4 -/

/-- Inversion, regarded only as a permutation.  It need not be a group
automorphism because the ambient group need not be abelian. -/
def inversionPerm (A : Type w) [Group A] : Equiv.Perm A :=
  inv_involutive.toPerm Inv.inv

/-- The permutation occurring in the `EpsiV` iteration in the source:
first invert, then apply the third power of an automorphism. -/
def inverseTwistPerm {A : Type w} [Group A]
    (phi : MulAut A) : Equiv.Perm A :=
  ((MulAut.toPerm A) phi) ^ 3 * inversionPerm A

/-- If `phi` has odd period `n`, then the `n`th power of the inverse twist
is plain inversion.  This isolates the short odd-order iteration at the
start of Step 4 from the long semidirect-product word calculation. -/
theorem inverseTwistPerm_pow_of_odd
    {A : Type w} [Group A] (phi : MulAut A) {n : ℕ}
    (hn : Odd n) (hphi : phi ^ n = 1) :
    (inverseTwistPerm phi) ^ n = inversionPerm A := by
  have hcomm : Commute ((MulAut.toPerm A) phi) (inversionPerm A) := by
    change ((MulAut.toPerm A) phi) * inversionPerm A =
      inversionPerm A * (MulAut.toPerm A) phi
    ext a
    change phi (a⁻¹) = (phi a)⁻¹
    exact map_inv phi a
  have hphiPerm : ((MulAut.toPerm A) phi) ^ n = 1 := by
    calc
      ((MulAut.toPerm A) phi) ^ n = (MulAut.toPerm A) (phi ^ n) :=
        ((MulAut.toPerm A).map_pow phi n).symm
      _ = 1 := by rw [hphi]; rfl
  have hphiThree : (((MulAut.toPerm A) phi) ^ 3) ^ n = 1 := by
    calc
      (((MulAut.toPerm A) phi) ^ 3) ^ n =
          ((MulAut.toPerm A) phi) ^ (3 * n) :=
        (pow_mul ((MulAut.toPerm A) phi) 3 n).symm
      _ = ((MulAut.toPerm A) phi) ^ (n * 3) := by rw [Nat.mul_comm]
      _ = (((MulAut.toPerm A) phi) ^ n) ^ 3 :=
        pow_mul ((MulAut.toPerm A) phi) n 3
      _ = 1 := by rw [hphiPerm, one_pow]
  have hinvTwo : inversionPerm A ^ 2 = 1 := by
    ext a
    simp [pow_two, Equiv.Perm.mul_apply, inversionPerm]
  have hinvOdd : inversionPerm A ^ n = inversionPerm A := by
    obtain ⟨k, rfl⟩ := hn
    rw [pow_add, pow_mul, hinvTwo, one_pow, one_mul, pow_one]
  rw [inverseTwistPerm, (hcomm.pow_left 3).mul_pow,
    hphiThree, hinvOdd, one_mul]

/-- Function-iterate form of `inverseTwistPerm_pow_of_odd`. -/
theorem inverseTwistPerm_iterate_of_odd
    {A : Type w} [Group A] (phi : MulAut A) {n : ℕ}
    (hn : Odd n) (hphi : phi ^ n = 1) (a : A) :
    (⇑(inverseTwistPerm phi))^[n] a = a⁻¹ := by
  calc
    (⇑(inverseTwistPerm phi))^[n] a =
        ((inverseTwistPerm phi) ^ n) a :=
      (congrFun (Equiv.Perm.coe_pow (inverseTwistPerm phi) n) a).symm
    _ = a⁻¹ := by
      rw [inverseTwistPerm_pow_of_odd phi hn hphi]
      rfl

namespace FiniteFieldImage

variable {P P0 U : Subgroup G} (h : FiniteFieldImage P P0 U)

/-- The field-valued endpoint of the group calculation in Lemma C.3,
Step 4.  If `x = ψ(a)` and `2 - x = ψ(b)`, it supplies an element whose
value is `2 - x⁻¹`. -/
def NormPairInverseClosed : Prop :=
  ∀ a b : U, h.psiValue a + h.psiValue b = 2 →
    ∃ c : U, h.psiValue c = 2 - (h.psiValue a)⁻¹

/-- The pullback of the two-norm equation set along the faithful unit
action.  This is the predicate written `psi a \in E` in the Coq proof. -/
def normEquationPreimage
    (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) h.F] : Set U :=
  {a : U | h.psiValue a ∈ normEquationSet (ZMod p) h.F}

/-- The exact one-step endpoint `EpsiV` of the long word calculation in
Step 4: the indicated permutation carries the pullback of `E` into itself.
The odd-order iteration turning this into inversion closure is proved
separately below. -/
def NormEquationOneStepClosed
    (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) h.F]
    (tau : Equiv.Perm U) : Prop :=
  Set.MapsTo tau (h.normEquationPreimage p) (h.normEquationPreimage p)

/-- Once the source's one-step closure and odd-period identity are known,
the field-valued endpoint `NormPairInverseClosed` follows. -/
theorem normPairInverseClosed_of_oneStep
    {p q : ℕ} [Fact p.Prime]
    [Algebra (ZMod p) h.F]
    (hcardP : Nat.card P = p ^ q)
    (hcardU : Nat.card U = nU p q)
    (tau : Equiv.Perm U)
    (htau : tau ^ Nat.card P = inversionPerm U)
    (hone : h.NormEquationOneStepClosed p tau) :
    h.NormPairInverseClosed := by
  intro a b hab
  have haNorm : Algebra.norm (ZMod p) (h.psiValue a) = 1 :=
    (h.im_psi hcardP hcardU (h.psiValue a)).1 ⟨a, rfl⟩
  have hbNorm : Algebra.norm (ZMod p) (h.psiValue b) = 1 :=
    (h.im_psi hcardP hcardU (h.psiValue b)).1 ⟨b, rfl⟩
  have haE : h.psiValue a ∈ normEquationSet (ZMod p) h.F := by
    refine ⟨haNorm, ?_⟩
    have htwo : 2 - h.psiValue a = h.psiValue b := by
      rw [← hab]
      ring
    rwa [htwo]
  have hiterate := hone.iterate (Nat.card P) (show
    a ∈ h.normEquationPreimage p from haE)
  have htauApply : (⇑tau)^[Nat.card P] a = a⁻¹ := by
    calc
      (⇑tau)^[Nat.card P] a = (tau ^ Nat.card P) a :=
        (congrFun (Equiv.Perm.coe_pow tau (Nat.card P)) a).symm
      _ = a⁻¹ := by rw [htau]; rfl
  have hainvE : h.psiValue a⁻¹ ∈ normEquationSet (ZMod p) h.F := by
    change h.psiValue ((⇑tau)^[Nat.card P] a) ∈
      normEquationSet (ZMod p) h.F at hiterate
    rwa [htauApply] at hiterate
  have htargetNorm :
      Algebra.norm (ZMod p) (2 - (h.psiValue a)⁻¹) = 1 := by
    simpa only [h.psiValue_inv] using hainvE.2
  exact (h.im_psi hcardP hcardU
    (2 - (h.psiValue a)⁻¹)).2 htargetNorm

/-! ### The cardinality of the distinguished prime line -/

/-- The finite-field realization identifies `P₀` with the additive line
generated by `1`. -/
noncomputable def p0EquivPrimeAdditiveLine :
    P0 ≃ primeAdditiveLine h.F where
  toFun x :=
    let xP : P := ⟨(x : G), h.p0_le x.property⟩
    ⟨h.sigma (Additive.ofMul xP),
      (h.mem_p0_iff_sigma_mem_primeAdditiveLine xP).1 x.property⟩
  invFun z :=
    let xP : P := Additive.toMul (h.sigma.symm (z : h.F))
    ⟨(xP : G), (h.mem_p0_iff_sigma_mem_primeAdditiveLine xP).2 (by
      simpa [xP] using z.property)⟩
  left_inv x := by
    apply Subtype.ext
    simp
  right_inv z := by
    apply Subtype.ext
    simp

/-- The cardinality of `P₀` is the characteristic prime.  In the Coq
proof this is `oP0`; here it follows directly from `primeLine_comap`. -/
theorem natCard_p0_eq_prime
    {p : ℕ} [Fact p.Prime] [Algebra (ZMod p) h.F] :
    Nat.card P0 = p := by
  have hchar : CharP h.F p := by
    rw [← Algebra.charP_iff (ZMod p) h.F p]
    exact ZMod.charP p
  calc
    Nat.card P0 = Nat.card (primeAdditiveLine h.F) :=
      Nat.card_congr h.p0EquivPrimeAdditiveLine
    _ = Nat.card (AddSubgroup.zmultiples (1 : h.F)) := rfl
    _ = addOrderOf (1 : h.F) := Nat.card_zmultiples (1 : h.F)
    _ = p := CharP.eq h.F (CharP.addOrderOf_one h.F) hchar

/-! ### The concrete Step-4 permutation -/

/-- The source element `t = s ^ y`, with right-conjugation convention
`s ^ y = y⁻¹ s y`. -/
def appendixCStep4Conjugator (y : G) : G :=
  y⁻¹ * (h.onePreimage : G) * y

theorem appendixCStep4Conjugator_mem (y : G) :
    h.appendixCStep4Conjugator y ∈ appendixCP1 P0 y := by
  rw [appendixCP1]
  refine ⟨h.onePreimage, h.onePreimage_mem_p0, ?_⟩
  simp [appendixCStep4Conjugator, MulAut.conj_apply]

/-- The conjugator `t`, packaged as an element of the normalizer of `U`. -/
def appendixCStep4Normalizer
    (y : G)
    (hP1normU : appendixCP1 P0 y ≤
      Subgroup.normalizer (U : Set G)) :
    Subgroup.normalizer (U : Set G) :=
  ⟨h.appendixCStep4Conjugator y,
    hP1normU (h.appendixCStep4Conjugator_mem y)⟩

/-- The automorphism of `U` given by source-style right conjugation by
`t`.  Mathlib's normalizer action is left conjugation, hence the inverse. -/
def appendixCStep4Action
    (y : G)
    (hP1normU : appendixCP1 P0 y ≤
      Subgroup.normalizer (U : Set G)) : MulAut U :=
  U.normalizerMonoidHom (h.appendixCStep4Normalizer y hP1normU)⁻¹

@[simp]
theorem appendixCStep4Action_apply_coe
    (y : G)
    (hP1normU : appendixCP1 P0 y ≤
      Subgroup.normalizer (U : Set G)) (a : U) :
    ((h.appendixCStep4Action y hP1normU a : U) : G) =
      (h.appendixCStep4Conjugator y)⁻¹ * (a : G) *
        h.appendixCStep4Conjugator y := by
  simp [appendixCStep4Action, appendixCStep4Normalizer,
    Subgroup.normalizerMonoidHom, HSMul.hSMul]

/-- The exact transformation in `EpsiV`, namely
`a ↦ (a⁻¹) ^ (t ^ 3)`. -/
def appendixCStep4Transform
    (y : G)
    (hP1normU : appendixCP1 P0 y ≤
      Subgroup.normalizer (U : Set G)) : Equiv.Perm U :=
  inverseTwistPerm (h.appendixCStep4Action y hP1normU)

@[simp]
theorem appendixCStep4Transform_apply
    (y : G)
    (hP1normU : appendixCP1 P0 y ≤
      Subgroup.normalizer (U : Set G)) (a : U) :
    h.appendixCStep4Transform y hP1normU a =
      ((h.appendixCStep4Action y hP1normU) ^ 3) (a⁻¹) := by
  change
    (((MulAut.toPerm U) (h.appendixCStep4Action y hP1normU)) ^ 3) (a⁻¹) =
      ((MulAut.toPerm U)
        ((h.appendixCStep4Action y hP1normU) ^ 3)) (a⁻¹)
  exact congrArg (fun tau : Equiv.Perm U ↦ tau (a⁻¹))
    (((MulAut.toPerm U).map_pow
      (h.appendixCStep4Action y hP1normU) 3).symm)

/-- The normalizer action by `t⁻¹` has period dividing `|P|`, because
`t` is conjugate to the distinguished element `s ∈ P`. -/
theorem appendixCStep4Action_pow_card
    (y : G)
    (hP1normU : appendixCP1 P0 y ≤
      Subgroup.normalizer (U : Set G)) :
    (h.appendixCStep4Action y hP1normU) ^ Nat.card P = 1 := by
  let tN : Subgroup.normalizer (U : Set G) :=
    h.appendixCStep4Normalizer y hP1normU
  have hsPow : h.onePreimage ^ Nat.card P = 1 :=
    pow_card_eq_one'
  have hsPowG : P.subtype h.onePreimage ^ Nat.card P = 1 := by
    calc
      P.subtype h.onePreimage ^ Nat.card P =
          P.subtype (h.onePreimage ^ Nat.card P) :=
        (map_pow P.subtype h.onePreimage (Nat.card P)).symm
      _ = P.subtype 1 := congrArg P.subtype hsPow
      _ = 1 := map_one P.subtype
  have htPow : tN ^ Nat.card P = 1 := by
    apply Subtype.ext
    change (h.appendixCStep4Conjugator y) ^ Nat.card P = 1
    calc
      (h.appendixCStep4Conjugator y) ^ Nat.card P =
          (MulAut.conj y⁻¹)
            (P.subtype h.onePreimage ^ Nat.card P) := by
        rw [map_pow]
        simp [appendixCStep4Conjugator, MulAut.conj_apply]
      _ = 1 := by rw [hsPowG]; simp
  have htInvPow : tN⁻¹ ^ Nat.card P = 1 := by
    rw [inv_pow, htPow, inv_one]
  change (U.normalizerMonoidHom tN⁻¹) ^ Nat.card P = 1
  calc
    (U.normalizerMonoidHom tN⁻¹) ^ Nat.card P =
        U.normalizerMonoidHom (tN⁻¹ ^ Nat.card P) :=
      ((U.normalizerMonoidHom).map_pow tN⁻¹ (Nat.card P)).symm
    _ = 1 := by rw [htInvPow, map_one]

/-- The whole short iteration surrounding the hard word identity in Step
4.  Its only group-calculation input is the one-step `EpsiV` closure. -/
theorem normPairInverseClosed_of_appendixC3_oneStep
    {p q : ℕ} [Fact p.Prime]
    [Algebra (ZMod p) h.F]
    (hcardP : Nat.card P = p ^ q)
    (hcardU : Nat.card U = nU p q)
    (hoddP : Odd (Nat.card P))
    (y : G)
    (hP1normU : appendixCP1 P0 y ≤
      Subgroup.normalizer (U : Set G))
    (hone : h.NormEquationOneStepClosed p
      (h.appendixCStep4Transform y hP1normU)) :
    h.NormPairInverseClosed := by
  apply h.normPairInverseClosed_of_oneStep hcardP hcardU
    (h.appendixCStep4Transform y hP1normU)
  · exact inverseTwistPerm_pow_of_odd
      (h.appendixCStep4Action y hP1normU) hoddP
      (h.appendixCStep4Action_pow_card y hP1normU)
  · exact hone

/-- Bender--Glauberman Appendix C, Lemma C.3, Step 4
(`BGappendixC.v: BGappendixC3_Ediv`), factored after the odd-order
iteration surrounding the semidirect-product word calculation.

The proof below contains the complete norm/image argument; the
source-facing theorem later obtains its `NormPairInverseClosed` argument
from the narrower `BGappendixC3Step4Obligation`.
-/
theorem BGappendixC3_Ediv
    {p q : ℕ} [Fact p.Prime]
    [Algebra (ZMod p) h.F]
    (hcardP : Nat.card P = p ^ q)
    (hcardU : Nat.card U = nU p q)
    (hstep4 : h.NormPairInverseClosed) :
    normEquationSet (ZMod p) h.F =
      (fun x : h.F ↦ x⁻¹) '' normEquationSet (ZMod p) h.F := by
  let E := normEquationSet (ZMod p) h.F
  have hmap : Set.MapsTo (fun x : h.F ↦ x⁻¹) E E := by
    intro x hx
    have hxNorm : Algebra.norm (ZMod p) x = 1 := hx.1
    have htwoNorm : Algebra.norm (ZMod p) (2 - x) = 1 := hx.2
    obtain ⟨a, ha⟩ := (h.im_psi hcardP hcardU x).2 hxNorm
    obtain ⟨b, hb⟩ := (h.im_psi hcardP hcardU (2 - x)).2 htwoNorm
    have hab : h.psiValue a + h.psiValue b = 2 := by
      rw [ha, hb]
      ring
    obtain ⟨c, hc⟩ := hstep4 a b hab
    constructor
    · rw [Algebra.norm_inv, hxNorm, inv_one]
    · apply (h.im_psi hcardP hcardU (2 - x⁻¹)).1
      refine ⟨c, ?_⟩
      rw [hc, ha]
  apply Set.Subset.antisymm
  · intro x hx
    refine ⟨x⁻¹, hmap hx, ?_⟩
    simp
  · rintro _ ⟨x, hx, rfl⟩
    exact hmap hx

end FiniteFieldImage

/-! ### The two branches of Lemma C.2 -/

/-- The exact remaining class-product obligation in the `4 < q` branch.
It packages the natural-number coefficient, its identification with the
norm-equation set, and the analytic estimate proved from character theory
in the source. -/
def LargeDegreeCharacterObligation
    {p q : ℕ} (F : Type v) [Field F] [Finite F]
    [Algebra (ZMod p) F] : Prop :=
  ∃ e : ℕ,
    (normEquationSet (ZMod p) F).ncard = e ∧
      ‖(((p ^ q) * e : ℕ) : ℂ) - ((nU p q : ℂ) ^ 2)‖ ≤
        (p ^ q : ℝ) * Real.sqrt (p ^ q : ℝ)

/-- Lemma C.2 in the form needed by the final count, combining the
character-theoretic `4 < q` result and the cubic small-degree result. -/
theorem one_lt_normEquationSet_ncard_of_appendixC_branches
    {p q : ℕ} [Fact p.Prime]
    (F : Type v) [Field F] [Finite F]
    [Algebra (ZMod p) F] [FiniteDimensional (ZMod p) F]
    (hqp : q < p) (hpodd : Odd p) (hqodd : Odd q) (htwo : 2 < q)
    (hfinrank : Module.finrank (ZMod p) F = q)
    (hlarge : 4 < q → LargeDegreeCharacterObligation (p := p) (q := q) F) :
    1 < (normEquationSet (ZMod p) F).ncard := by
  by_cases hq4 : 4 < q
  · obtain ⟨e, hcard, hdist⟩ := hlarge hq4
    exact one_lt_normEquationSet_ncard_of_q_gt_four
      F hqp hq4 hcard hdist
  · have hfour : q ≤ 4 := Nat.le_of_not_gt hq4
    obtain ⟨a, ha1, haE⟩ :=
      exists_nontrivial_mem_normEquationSet_of_small_odd_degree
        F hpodd hqodd htwo hfour hfinrank
    exact (Set.one_lt_ncard).2
      ⟨1, one_mem_normEquationSet (ZMod p) F,
        a, haE, ha1.symm⟩

/-! ### The concluding count -/

/-- Bender--Glauberman's `BGappendixC_inner_subproof`: once Step 4 gives
inversion stability and the large-degree character obligation is
available, Lemmas C.1 and C.2 contradict `q < p`. -/
theorem BGappendixC_inner_subproof
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (F : Type v) [Field F] [Finite F]
    [Algebra (ZMod p) F] [FiniteDimensional (ZMod p) F]
    (hcop : (nU p q).Coprime (p - 1))
    (hqp : q < p)
    (hfinrank : Module.finrank (ZMod p) F = q)
    (hinv : normEquationSet (ZMod p) F =
      (fun x : F ↦ x⁻¹) '' normEquationSet (ZMod p) F)
    (hlarge : 4 < q → LargeDegreeCharacterObligation (p := p) (q := q) F) :
    p ≤ q := by
  have hpodd : Odd p := odd_p Fact.out Fact.out hqp
  have hqodd : Odd q := odd_q Fact.out Fact.out hcop hqp
  have htwo : 2 < q := two_lt_q Fact.out Fact.out hcop hqp
  have hcard : 1 < (normEquationSet (ZMod p) F).ncard :=
    one_lt_normEquationSet_ncard_of_appendixC_branches
      F hqp hpodd hqodd htwo hfinrank hlarge
  exact prime_le_of_normEquationSet_eq_image_inv
    F hfinrank hinv hcard

/-! ### Conditional source-facing theorem -/

/-- The exact remaining Step-4 word obligation, parameterized by the
adjusted conjugator produced by Remark XI and by the Step-3 TI-intersection
family.  Its conclusion is precisely the source assertion `EpsiV`, not the
final inversion closure: the odd-order iteration from `EpsiV` to
`NormPairInverseClosed` is proved above. -/
def BGappendixC3Step4Obligation
    {p : ℕ} [Fact p.Prime]
    {H P P0 U Q : Subgroup G}
    (hfield : FiniteFieldImage P P0 U)
    [Algebra (ZMod p) hfield.F] : Prop :=
  ∀ (y : G) (_ : y ∈ ⁅Q, P0⁆)
    (hP1normU : appendixCP1 P0 y ≤
      Subgroup.normalizer (U : Set G)),
    (∀ {t1 : G}, t1 ∈ appendixCP1 P0 y → t1 ≠ 1 →
      H ⊓ H.map (MulAut.conj t1⁻¹).toMonoidHom = U) →
    hfield.NormEquationOneStepClosed p
      (hfield.appendixCStep4Transform y hP1normU)

/-- The source-facing Appendix C theorem, conditional only on the two
named obligations above.  All arithmetic, finite-field, norm-equation,
and final counting steps are discharged here; future files can remove the
two obligation arguments without changing the counting API. -/
theorem prime_dim_normed_finField
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    [Finite G]
    {H P P0 U Q : Subgroup G}
    (hfield : FiniteFieldImage P P0 U)
    [Algebra (ZMod p) hfield.F]
    (hPH : P ≤ H) (hUH : U ≤ H)
    (hsemi : (P.subgroupOf H).IsComplement' (U.subgroupOf H))
    (hUP : U ≤ Subgroup.normalizer (P : Set G))
    (hcardP : Nat.card P = p ^ q)
    (hcardU : Nat.card U = nU p q)
    (hcop : (nU p q).Coprime (p - 1))
    (hQ : IsElementaryAbelianGroup q Q)
    (hnormQ : P0 ≤ Subgroup.normalizer (Q : Set G))
    (hconj : ∃ y : G, y ∈ Q ∧
      appendixCP1 P0 y ≤ Subgroup.normalizer (U : Set G))
    (hstep4 : BGappendixC3Step4Obligation
      (p := p) (H := H) (Q := Q) hfield)
    (hlarge : 4 < q →
      LargeDegreeCharacterObligation (p := p) (q := q) hfield.F) :
    p ≤ q := by
  by_contra hpq
  have hqp : q < p := Nat.lt_of_not_ge hpq
  have hP : IsPGroup p P := pP hcardP
  have hqne : q ≠ p := q_ne_p hqp
  have hpodd : Odd p := odd_p Fact.out Fact.out hqp
  have hcardP0 : Nat.card P0 = p :=
    hfield.natCard_p0_eq_prime
  obtain ⟨y, hyComm, hyNorm⟩ :=
    nU_P0QP0_of_isPGroup
      (P := P) (P0 := P0) (U := U) (Q := Q)
      hQ hP hqne hfield.p0_le hnormQ (by
        simpa only [appendixCP1] using hconj)
  have hyNorm' : appendixCP1 P0 y ≤
      Subgroup.normalizer (U : Set G) := by
    simpa only [appendixCP1] using hyNorm
  have hyQ : y ∈ Q := (sQP0Q hnormQ) hyComm
  have hti : ∀ {t1 : G}, t1 ∈ appendixCP1 P0 y → t1 ≠ 1 →
      H ⊓ H.map (MulAut.conj t1⁻¹).toMonoidHom = U := by
    intro t1 ht1 ht1ne
    exact hfield.tiH_P1 hPH hUH hsemi hUP
      (hfield.natCard_P_eq_field.symm.trans hcardP)
      hcardU hcop hQ hqne hnormQ hcardP0 y hyQ hyNorm' ht1 ht1ne
  have hone : hfield.NormEquationOneStepClosed p
      (hfield.appendixCStep4Transform y hyNorm') :=
    hstep4 y hyComm hyNorm' hti
  have hcardPodd : Odd (Nat.card P) := by
    rw [hcardP]
    exact hpodd.pow
  have hclosure : hfield.NormPairInverseClosed :=
    hfield.normPairInverseClosed_of_appendixC3_oneStep
      hcardP hcardU hcardPodd y hyNorm' hone
  have hinv : normEquationSet (ZMod p) hfield.F =
      (fun x : hfield.F ↦ x⁻¹) ''
        normEquationSet (ZMod p) hfield.F :=
    hfield.BGappendixC3_Ediv hcardP hcardU hclosure
  have hfinrank : Module.finrank (ZMod p) hfield.F = q := by
    apply Nat.pow_right_injective (Fact.out : p.Prime).two_le
    calc
      p ^ Module.finrank (ZMod p) hfield.F = Nat.card hfield.F :=
        FiniteField.pow_finrank_eq_natCard p hfield.F
      _ = Nat.card P := hfield.natCard_P_eq_field.symm
      _ = p ^ q := hcardP
  exact hpq (BGappendixC_inner_subproof
    hfield.F hcop hqp hfinrank hinv hlarge)

end

end Submission.OddOrder.BG.AppendixC
