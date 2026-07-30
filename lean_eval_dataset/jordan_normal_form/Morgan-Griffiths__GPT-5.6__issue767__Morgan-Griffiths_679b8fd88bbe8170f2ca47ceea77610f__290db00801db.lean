import ChallengeDeps
import Mathlib

-- BEGIN INLINED FILE: Mathlib/Support/jordan_normal_form_5debc30dcb/Blocks.lean
section

/- Some elementary blocks. -/
open Polynomial
noncomputable section
namespace JordanSupport

variable (K : Type*) [Field K]

/-- The reverse-of-power basis in the truncated polynomial algebra.  In this
orientation multiplication by `X` is the backwards shift. -/
def nilBlockBasis (e : ℕ) :
    Module.Basis (Fin e) K (AdjoinRoot (X ^ e : K[X])) :=
  (AdjoinRoot.powerBasis' (monic_X_pow e : (X ^ e : K[X]).Monic)).basis.reindex
    ((finCongr (by simp : (X ^ e : K[X]).natDegree = e)).trans Fin.revPerm)

@[simp] lemma nilBlockBasis_apply (e : ℕ) (j : Fin e) :
    nilBlockBasis K e j =
      (AdjoinRoot.root (X ^ e : K[X])) ^ (e - (j:ℕ) - 1) := by
  classical
  unfold nilBlockBasis
  rw [Module.Basis.reindex_apply]
  rw [(AdjoinRoot.powerBasis' (monic_X_pow e : (X^e : K[X]).Monic)).basis_eq_pow]
  rw [AdjoinRoot.powerBasis'_gen]
  congr 1
  -- the index was reversed
  -- simp

@[simp] lemma nilBlock_root_pow_dim (e : ℕ) :
    (AdjoinRoot.root (X ^ e : K[X])) ^ e = 0 := by
  -- the defining relation
  rw [← AdjoinRoot.mk_X]
  rw [← map_pow]
  exact AdjoinRoot.mk_self

theorem nilBlockBasis_chain (e : ℕ) (j : Fin e) :
    let b := nilBlockBasis K e
    (AdjoinRoot.root (X ^ e : K[X])) * b j =
      if j.val = 0 then 0 else
        b ⟨j.val - 1, lt_of_le_of_lt (Nat.sub_le j.val 1) j.isLt⟩ := by
  dsimp
  rw [nilBlockBasis_apply]
  split_ifs with h
  · -- the top vector is root^(e-1)
    have hj : (j:ℕ) = 0 := h
    simp only [hj, Nat.sub_zero]
    -- root * root^(e-1) = root^e
    have he : 0 < e := lt_of_le_of_lt (Nat.zero_le _) j.isLt
    -- rearrange exponents
    rw [← pow_succ']
    have : e - 1 + 1 = e := Nat.sub_add_cancel he
    rw [this, nilBlock_root_pow_dim]
  · rw [nilBlockBasis_apply]
    -- if j>0, multiplication increments exponent by one
    rw [← pow_succ']
    congr 1
    -- exponents
    simp only []
    have hj : 1 ≤ (j:ℕ) := (Nat.one_le_iff_ne_zero).2 h
    omega

end JordanSupport

namespace JordanSupport
open Polynomial
variable (K : Type*) [Field K]

lemma subRoot_pow_zero (a : K) (e : ℕ) :
    (AdjoinRoot.root ((X - C a)^e : K[X]) -
       algebraMap K (AdjoinRoot ((X-C a)^e : K[X])) a)^e = 0 := by
  have h := AdjoinRoot.eval₂_root ((X-C a)^e : K[X])
  rw [eval₂_pow, eval₂_sub, eval₂_X, eval₂_C] at h
  exact h

-- Translation identifies a translated truncated polynomial algebra with the ordinary one.
noncomputable def translateNilEquiv (a : K) (e : ℕ) :
    AdjoinRoot (X^e : K[X]) ≃ₐ[K] AdjoinRoot ((X-C a)^e : K[X]) := by
  let ra : AdjoinRoot ((X-C a)^e : K[X]) := AdjoinRoot.root _
  let r0 : AdjoinRoot (X^e : K[X]) := AdjoinRoot.root _
  have hsub : (ra - algebraMap K _ a)^e = 0 := subRoot_pow_zero K a e
  have hadd : (r0 + algebraMap K _ a - algebraMap K _ a)^e = 0 := by
    rw [add_sub_cancel_right]
    exact nilBlock_root_pow_dim K e
  have h0eval : Polynomial.eval₂ (algebraMap K (AdjoinRoot ((X-C a)^e : K[X])))
        (ra - algebraMap K _ a) (X^e : K[X]) = 0 := by
    simpa using hsub
  have haeval : Polynomial.eval₂ (algebraMap K (AdjoinRoot (X^e : K[X])))
        (r0 + algebraMap K _ a) ((X-C a)^e : K[X]) = 0 := by
    simpa [eval₂_pow, eval₂_sub] using hadd
  let F : AdjoinRoot (X^e : K[X]) →ₐ[K] AdjoinRoot ((X-C a)^e : K[X]) :=
    AdjoinRoot.liftAlgHom _ (Algebra.ofId K (AdjoinRoot ((X-C a)^e : K[X])))
      (ra - algebraMap K _ a) h0eval
  let G : AdjoinRoot ((X-C a)^e : K[X]) →ₐ[K] AdjoinRoot (X^e : K[X]) :=
    AdjoinRoot.liftAlgHom _ (Algebra.ofId K (AdjoinRoot (X^e : K[X])))
      (r0 + algebraMap K _ a) haeval
  have Froot : F r0 = ra - algebraMap K _ a := by
    exact AdjoinRoot.liftAlgHom_root _ _ _ _
  have Groot : G ra = r0 + algebraMap K _ a := by
    exact AdjoinRoot.liftAlgHom_root _ _ _ _
  have FG : F.comp G = AlgHom.id K _ := by
    apply AdjoinRoot.algHom_ext
    change F (G _) = _
    rw [Groot, map_add, Froot, F.commutes]
    simp; rfl
  have GF : G.comp F = AlgHom.id K _ := by
    apply AdjoinRoot.algHom_ext
    change G (F _) = _
    rw [Froot, map_sub, Groot, G.commutes]
    simp; rfl

  exact AlgEquiv.ofAlgHom F G FG GF

@[simp] lemma translateNilEquiv_gen (a : K) (e : ℕ) :
    translateNilEquiv K a e (AdjoinRoot.root (X^e : K[X])) =
      AdjoinRoot.root ((X-C a)^e : K[X]) - algebraMap K _ a := by
  classical
  unfold translateNilEquiv
  dsimp
  rw [AlgEquiv.ofAlgHom_apply]
  apply AdjoinRoot.liftAlgHom_root


end JordanSupport

namespace JordanSupport
open Polynomial
variable (K : Type*) [Field K]

noncomputable def primaryBlockBasis (a : K) (e : ℕ) :
    Module.Basis (Fin e) K (AdjoinRoot ((X-C a)^e : K[X])) :=
  (nilBlockBasis K e).map (translateNilEquiv K a e).toLinearEquiv

@[simp] lemma primaryBlockBasis_apply (a : K) (e : ℕ) (j : Fin e) :
    primaryBlockBasis K a e j =
      (AdjoinRoot.root ((X-C a)^e : K[X]) - algebraMap K _ a)
        ^ (e - (j:ℕ) - 1) := by
  classical
  change translateNilEquiv K a e (nilBlockBasis K e j) = _
  rw [nilBlockBasis_apply]
  rw [map_pow, translateNilEquiv_gen]

theorem primaryBlockBasis_chain (a : K) (e : ℕ) (j : Fin e) :
    let b := primaryBlockBasis K a e
    (AdjoinRoot.root ((X-C a)^e : K[X])) * b j =
      a • b j + if j.val = 0 then 0 else
        b ⟨j.val - 1, lt_of_le_of_lt (Nat.sub_le j.val 1) j.isLt⟩ := by
  classical
  dsimp
  -- compare with the untranslated, nilpotent block
  let E := translateNilEquiv K a e
  let r := AdjoinRoot.root ((X-C a)^e : K[X])
  let x := nilBlockBasis K e j
  have hb : primaryBlockBasis K a e j = E x := rfl
  have hn := nilBlockBasis_chain K e j
  have hr : E (AdjoinRoot.root (X^e : K[X])) = r - algebraMap K _ a :=
    translateNilEquiv_gen K a e
  -- the generator splits as its nilpotent part and scalar part
  have key (y : AdjoinRoot (X^e : K[X])) :
       r * E y = a • E y + E (AdjoinRoot.root (X^e : K[X]) * y) := by
    calc
      r * E y = ((r - algebraMap K _ a) + algebraMap K _ a) * E y := by rw [sub_add_cancel]
      _ = (r - algebraMap K _ a) * E y + (algebraMap K _ a) * E y := by rw [add_mul]
      _ = E (AdjoinRoot.root (X^e : K[X])) * E y + a • E y := by
        rw [hr]
        simp [Algebra.smul_def]
      _ = a • E y + E (AdjoinRoot.root (X^e : K[X]) * y) := by
        rw [map_mul]
        ac_rfl
  rw [hb, key]
  rw [hn]
  split_ifs with h
  · simp [h]
  · -- maps send other basis entries to the new basis entries
    have hb' :
        primaryBlockBasis K a e
          (⟨j.val - 1, lt_of_le_of_lt (Nat.sub_le j.val 1) j.isLt⟩) =
          E (nilBlockBasis K e
          (⟨j.val - 1, lt_of_le_of_lt (Nat.sub_le j.val 1) j.isLt⟩)) := rfl
    simp [h, hb']

end JordanSupport

end

end
-- END INLINED FILE: Mathlib/Support/jordan_normal_form_5debc30dcb/Blocks.lean

-- BEGIN INLINED FILE: Mathlib/Support/jordan_normal_form_5debc30dcb/Irred.lean
section
open Polynomial
noncomputable section
namespace JordanSupport
variable (K : Type*) [Field K] [IsAlgClosed K]
lemma irred_linear {p : K[X]} (hp : Irreducible p) :
    ∃ (a c : K), c ≠ 0 ∧ p = C c * (X - C a) := by
  have hd : p.natDegree = 1 := by
    have h := IsAlgClosed.degree_eq_one_of_irreducible K hp
    rw [degree_eq_natDegree hp.ne_zero] at h
    exact_mod_cast h
  have hform := Polynomial.exists_eq_X_add_C_of_natDegree_le_one (p := p) hd.le
  obtain ⟨c,b,eqp⟩ := hform
  have hc : c ≠ 0 := by
    intro h
    have : p.natDegree = 0 := by
      rw [eqp, h]
      simp
    omega
  refine ⟨-(c⁻¹*b), c, hc, ?_⟩
  rw [eqp]
  -- expand; use `C` arithmetic
  rw [mul_sub, mul_comm (C c) X, ← C_mul]
  congr 1
  -- constant coefficients
  -- the two scalar terms coincide
  rw [← map_neg]
  apply congrArg C
    (by field_simp : b = -(c * -(c⁻¹ * b)))


lemma irred_span_pow_eq {p : K[X]} (hp : Irreducible p) (e : ℕ) :
    ∃ a : K, K[X] ∙ p^e = K[X] ∙ (X-C a)^e := by
  obtain ⟨a,c,hc,rfl⟩ := irred_linear K hp
  refine ⟨a, ?_⟩
  -- submodule generated by an invertible scalar multiple
  apply (Submodule.span_singleton_eq_span_singleton).2
  let u0 : Kˣ := Units.mk0 c hc
  let u : K[X]ˣ := Units.map (Polynomial.C : K →+* K[X]).toMonoidHom u0
  refine ⟨u⁻¹ ^ e, ?_⟩
  simp only [Units.smul_def]
  have hu : (↑u : K[X]) = C c := rfl
  -- cancellation of the constant unit
  rw [mul_pow]
  change (↑(u⁻¹ ^ e) : K[X]) * ((C c)^e * (X-C a)^e) = _
  rw [hu.symm]
  push_cast
  rw [← mul_assoc, ← mul_pow]
  simp

end JordanSupport

end

end
-- END INLINED FILE: Mathlib/Support/jordan_normal_form_5debc30dcb/Irred.lean

-- BEGIN INLINED FILE: Mathlib/Support/jordan_normal_form_5debc30dcb/Cyclic.lean
section
noncomputable section
open Polynomial
open scoped DirectSum
namespace JordanSupport
universe u v
variable (K : Type u) [Field K]

/- The module attached to an endomorphism is torsion; this is the point at
which finite dimensionality enters the elementary-divisor argument. -/
lemma ae_torsion {V : Type v} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) :
    Module.IsTorsion K[X] (Module.AEval' T) := by
  -- the algebra of endomorphisms is finite dimensional
  exact Module.AEval.isTorsion_of_finiteDimensional K V T

-- test raw elementary divisor theorem
lemma cyclic_decomp_raw {V : Type v} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) :
    ∃ (ι : Type u) (_ : Fintype ι) (p : ι → K[X]) (_ : ∀ i, Irreducible (p i))
      (e : ι → ℕ),
      Nonempty ((Module.AEval' T) ≃ₗ[K[X]] ⨁ i : ι, K[X] ⧸ K[X] ∙ (p i) ^ (e i)) := by
  exact Module.equiv_directSum_of_isTorsion (R:=K[X]) (M:=Module.AEval' T)
    (ae_torsion K T)

variable [IsAlgClosed K]
-- replace each irreducible by the linear primary polynomial, at the level of quotients
lemma cyclic_decomp_linear_raw {V : Type v} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) :
    ∃ (ι : Type u) (_ : Fintype ι) (a : ι → K) (e : ι → ℕ),
      Nonempty ((Module.AEval' T) ≃ₗ[K[X]] ⨁ i : ι,
        K[X] ⧸ K[X] ∙ ((X - C (a i))^(e i) : K[X])) := by
  classical
  obtain ⟨ι, hι, p, hp, e, ⟨E⟩⟩ := cyclic_decomp_raw K T
  let a : ι → K := fun i => Classical.choose (irred_span_pow_eq K (hp i) (e i))
  have H (i : ι) : K[X] ∙ (p i)^(e i) = K[X] ∙ (X-C (a i))^(e i) :=
    Classical.choose_spec (irred_span_pow_eq K (hp i) (e i))
  let Q (i : ι) :
      (K[X] ⧸ K[X] ∙ (p i)^(e i)) ≃ₗ[K[X]]
        (K[X] ⧸ K[X] ∙ (X-C (a i))^(e i)) :=
    Submodule.quotEquivOfEq _ _ (H i)
  exact ⟨ι, hι, a, e, ⟨E.trans (DFinsupp.mapRange.linearEquiv Q)⟩⟩


/-- Trivial power quotients (exponent zero) carry no summand in a direct sum.  This
small lemma is useful to erase them without choices of generators. -/
lemma zeroBlockSubsingleton (a : K) :
    Subsingleton (K[X] ⧸ K[X] ∙ ((X-C a)^0 : K[X])) := by
  apply Submodule.Quotient.subsingleton_iff.mpr
  simp

/-- Restrict a (finite) product of power quotients to the nonzero powers. Written
out for Pi first; this avoids support choices for `DFinsupp`. -/
lemma restrictPiPower
    {ι : Type u} [Fintype ι] (a : ι → K) (e : ι → ℕ) :
    Nonempty
      (((i : ι) → (K[X] ⧸ K[X] ∙ ((X-C (a i))^(e i) : K[X])))
        ≃ₗ[K[X]]
       ((i : {i : ι // 0 < e i}) →
          (K[X] ⧸ K[X] ∙ ((X-C (a i.1))^(e i.1) : K[X])))) := by
  classical
  let M (i : ι) := (K[X] ⧸ K[X] ∙ ((X-C (a i))^(e i) : K[X]))
  have hz (i : ι) (hi : ¬ 0 < e i) : Subsingleton (M i) := by
    have he : e i = 0 := Nat.eq_zero_of_not_pos hi
    -- rewriting the exponent turns it into the quotient by the span of one
    dsimp [M]
    rw [he]
    exact zeroBlockSubsingleton K (a i)
  let down : ((i : ι) → M i) →ₗ[K[X]] ((i : {i : ι // 0 < e i}) → M i.1) :=
    { toFun := fun x i => x i.1
      map_add' := by intro x y; rfl
      map_smul' := by intro c x; rfl }
  let up : ((i : {i : ι // 0 < e i}) → M i.1) → ((i : ι) → M i) :=
    fun y i => dite (0 < e i) (fun h => y ⟨i,h⟩) (fun _ => 0)
  refine ⟨{
    __ := down
    invFun := up
    left_inv := ?_
    right_inv := ?_ }⟩
  · intro x
    funext i
    by_cases h : 0 < e i
    · simp [down, up, h]
    · have : x i = 0 := @Subsingleton.elim (M i) (hz i h) (x i) 0
      simp [down, up, h, this]
  · intro y
    funext i
    simp [down, up, i.2]

/-- Elementary divisors for the polynomial module, keeping only nonzero powers.
The index has exactly one nontrivial cyclic summand for each primary block. -/
lemma cyclic_decomp_linear {V : Type v} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) :
    ∃ (ι : Type u) (_ : Fintype ι) (a : ι → K) (e : ι → ℕ),
      (∀ i, 0 < e i) ∧
      Nonempty ((Module.AEval' T) ≃ₗ[K[X]]
        ⨁ i : ι, K[X] ⧸ K[X] ∙ ((X-C (a i))^(e i) : K[X])) := by
  classical
  obtain ⟨ι, hi, a, e, ⟨E⟩⟩ := cyclic_decomp_linear_raw K T
  letI : Fintype ι := hi
  let j := {i : ι // 0 < e i}
  haveI : Fintype j := inferInstance
  let a' : j → K := fun i => a i.1
  let e' : j → ℕ := fun i => e i.1
  obtain ⟨P⟩ := restrictPiPower K a e
  -- on a finite index a direct sum is the same as the product
  let F := (DFinsupp.linearEquivFunOnFintype (R:=K[X])
      (M:=fun i : ι => K[X] ⧸ K[X] ∙ ((X-C (a i))^(e i) : K[X]))).trans
        (P.trans (DFinsupp.linearEquivFunOnFintype (R:=K[X])
          (M:=fun t : j => K[X] ⧸ K[X] ∙ ((X-C (a t.1))^(e t.1) : K[X]))).symm)
  exact ⟨j, inferInstance, a', e', (fun i => i.2), ⟨E.trans F⟩⟩

end JordanSupport

end

end
-- END INLINED FILE: Mathlib/Support/jordan_normal_form_5debc30dcb/Cyclic.lean

-- BEGIN INLINED FILE: Mathlib/Support/jordan_normal_form_5debc30dcb/Assemble.lean
section
noncomputable section
open Polynomial
open scoped DirectSum
namespace JordanSupport
universe u v
variable (K : Type u) [Field K]

/-- Identifying the `Submodule` and `Ideal` presentations of a principal quotient,
at the level of `K` vector spaces. -/
def quotAdjoinRootEquiv (a : K) (e : ℕ) :
    (K[X] ⧸ K[X] ∙ ((X-C a)^e : K[X])) ≃ₗ[K]
      AdjoinRoot ((X-C a)^e : K[X]) := by
  rw [Ideal.submodule_span_eq]
  exact LinearEquiv.refl K _

@[simp] lemma quotAdjoinRoot_mk (a : K) (e : ℕ) (p : K[X]) :
    quotAdjoinRootEquiv K a e (Submodule.Quotient.mk p) =
      AdjoinRoot.mk ((X-C a)^e : K[X]) p := by
  rfl

/-- Reverse-power block basis written in the submodule quotient. -/
def quotBlockBasis (a : K) (e : ℕ) :
    Module.Basis (Fin e) K (K[X] ⧸ K[X] ∙ ((X-C a)^e : K[X])) :=
  (primaryBlockBasis K a e).map (quotAdjoinRootEquiv K a e).symm

@[simp] lemma quotBlockBasis_map (a : K) (e : ℕ) (j : Fin e) :
    quotAdjoinRootEquiv K a e (quotBlockBasis K a e j) =
      primaryBlockBasis K a e j := by
  classical
  simp [quotBlockBasis]

lemma quot_X_map (a : K) (e : ℕ)
    (q : K[X] ⧸ K[X] ∙ ((X-C a)^e : K[X])) :
    quotAdjoinRootEquiv K a e ((X : K[X]) • q) =
      AdjoinRoot.root ((X-C a)^e : K[X]) * quotAdjoinRootEquiv K a e q := by
  induction q using Quotient.inductionOn' with
  | _ p =>
    change AdjoinRoot.mk ((X-C a)^e : K[X]) (X*p) = _
    rw [← AdjoinRoot.mk_X]
    rw [map_mul]
    rfl

lemma quotBlockBasis_chain (a : K) (e : ℕ) (j : Fin e) :
    let b := quotBlockBasis K a e
    (X : K[X]) • b j =
      a • b j + if j.val = 0 then 0 else
        b ⟨j.val - 1, lt_of_le_of_lt (Nat.sub_le j.val 1) j.isLt⟩ := by
  classical
  dsimp
  -- inject to the adjoin-root block
  apply (quotAdjoinRootEquiv K a e).injective
  rw [quot_X_map]
  rw [quotBlockBasis_map]
  rw [map_add]
  -- linearity + the possibly zero last term
  simp only [map_smul]
  split_ifs with h
  · rw [primaryBlockBasis_chain K a e j]
    simp [h, quotBlockBasis_map]
  · rw [primaryBlockBasis_chain K a e j]
    simp [h, quotBlockBasis_map]

end JordanSupport

namespace JordanSupport
open Polynomial
open scoped DirectSum
universe u
variable {K : Type u} [Field K]
@[simp] lemma dfbasis_apply
    {ι : Type*} [DecidableEq ι]
    {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module K (M i)]
    {η : ι → Type*} (b : ∀ i, Module.Basis (η i) K (M i))
    (i : ι) (j : η i) :
    DFinsupp.basis b ⟨i,j⟩ = DFinsupp.single i (b i j) := by
  -- should be a general description of this basis
  apply (DFinsupp.basis b).repr.injective
  ext k
  rcases k with ⟨t,z⟩
  change _ = _
  by_cases h : i = t
  · subst t
    -- coordinates in the ith factor
    simp [DFinsupp.basis, DFinsupp.single]
  · simp [DFinsupp.basis, DFinsupp.single, h]
end JordanSupport
namespace JordanSupport
open Polynomial
open scoped DirectSum
universe u
variable {K : Type u} [Field K]
@[simp] lemma directBlock_chain
    {ι : Type*} [DecidableEq ι]
    (a : ι → K) (e : ι → ℕ) (i : ι) (j : Fin (e i)) :
    let b : ∀ t, Module.Basis (Fin (e t)) K
       (K[X] ⧸ K[X] ∙ ((X-C (a t))^(e t) : K[X])) := fun t => quotBlockBasis K (a t) (e t)
    (X : K[X]) • (DFinsupp.basis b ⟨i,j⟩) =
       a i • (DFinsupp.basis b ⟨i,j⟩) +
         if j.val = 0 then 0 else
           DFinsupp.basis b ⟨i, ⟨j.val-1, lt_of_le_of_lt (Nat.sub_le j.val 1) j.isLt⟩⟩ := by
  classical
  dsimp
  simp only [dfbasis_apply]
  have h := quotBlockBasis_chain K (a i) (e i) j
  dsimp at h
  by_cases z : j.val = 0
  · -- functoriality of a single
    -- h says local X action
    rw [← DFinsupp.single_smul]
    rw [h]
    simp [z, DFinsupp.single_smul, DFinsupp.single_add]
  · rw [← DFinsupp.single_smul]
    rw [h]
    rw [if_neg z]
    -- distribute single and scalar
    rw [DFinsupp.single_add]
    rw [DFinsupp.single_smul]
    simp [z]
end JordanSupport

end

end
-- END INLINED FILE: Mathlib/Support/jordan_normal_form_5debc30dcb/Assemble.lean

-- BEGIN INLINED MAIN PRELUDE

open LeanEval.LinearAlgebra.JordanNormalForm
open scoped DirectSum
open Polynomial
/-ResultDefinitionsBegin-/
/-ResultProofDefinitionsBegin-/
/-ResultProofDefinitionsEnd-/
/-ResultDefinitionsEnd-/


-- END INLINED MAIN PRELUDE

namespace Submission

/-ResultBegin-/

theorem jordan_normal_form {K : Type*} [Field K] [IsAlgClosed K] (n : ℕ)
    (f : Module.End K (StdSpace K n)) :
    Nonempty (JordanChainBasis f) :=
/-ResultProofBegin-/ by
  classical

  -- regard the operator as a polynomial module and use elementary divisors
  letI : FiniteDimensional K (StdSpace K n) := by infer_instance
  obtain ⟨ι, hi, a, e, he, ⟨P⟩⟩ :=
    JordanSupport.cyclic_decomp_linear K f
  letI : Fintype ι := hi
  letI : DecidableEq ι := Classical.decEq _
  let small (t : ι) :=
    JordanSupport.quotBlockBasis K (a t) (e t)
  let W := (⨁ t : ι,
      K[X] ⧸ K[X] ∙ ((Polynomial.X - Polynomial.C (a t))^(e t) : K[X]))
  let wb : Module.Basis (Σ t : ι, Fin (e t)) K W :=
    DFinsupp.basis small
  -- forget polynomial scalars, and the harmless synonym AEval
  let L : (StdSpace K n) ≃ₗ[K] W :=
    (Module.AEval'.of f).trans (P.restrictScalars K)
  let vb : Module.Basis (Σ t : ι, Fin (e t)) K (StdSpace K n) := wb.map L.symm
  let d := Fintype.card ι
  let q : Fin d → ι := (Fintype.equivFin ι).symm
  let ee : Fin d → ℕ := fun r => e (q r)
  let aa : Fin d → K := fun r => a (q r)
  -- The sigma equivalence that sends a new (`Fin d`) label to the old summand.
  -- Keep its inverse separately as the direction expected by `Basis.reindex`.
  let ix₀ : (Σ r : Fin d, Fin (ee r)) ≃ (Σ t : ι, Fin (e t)) :=
    Equiv.sigmaCongr (Fintype.equivFin ι).symm (fun r => Equiv.refl _)
  let ix : (Σ t : ι, Fin (e t)) ≃ (Σ r : Fin d, Fin (ee r)) := ix₀.symm
  let vb' : Module.Basis (Σ r : Fin d, Fin (ee r)) K (StdSpace K n) :=
    vb.reindex ix
  refine ⟨{
    ι := Fin d
    size := ee
    positive_size := fun r => he _
    eigenvalue := aa
    basis := vb'
    chain := ?_ }⟩
  intro r j
  let i : ι := q r
  change f (vb' ⟨r,j⟩) = _

  have b_eq (r : Fin d) (k : Fin (ee r)) : vb' ⟨r,k⟩ = vb ⟨q r,k⟩ := by
    rw [Module.Basis.reindex_apply]
    -- compute the sigma reindex on a pair
    -- `reindex` takes an equivalence from old to new; its value at a new
    -- label is the old basis at `ix.symm`, namely `ix₀` on this pair.
    change vb (ix₀ ⟨r,k⟩) = _
    rfl
  simp only [b_eq]
  -- transport
  apply L.injective
  have hx (x : StdSpace K n) : L (f x) = (Polynomial.X : K[X]) • L x := by
    change P (Module.AEval'.of f (f x)) = _
    rw [← Module.AEval'.X_smul_of]
    rw [map_smul]
    rfl
  have Lv (t : ι) (k : Fin (e t)) :
       L (vb ⟨t,k⟩) = wb ⟨t,k⟩ := by
    simp [vb, wb, L]
  rw [hx]
  rw [Lv]
  rw [map_add, map_smul, Lv]
  split_ifs with z
  · simp
    -- unfold goal
    have h := JordanSupport.directBlock_chain (K:=K) a e (q r) j
    dsimp at h
    rw [if_pos z, add_zero] at h
    exact h
  · rw [Lv]
    have h := JordanSupport.directBlock_chain (K:=K) a e (q r) j
    dsimp at h
    rw [if_neg z] at h
    exact h
/-ResultProofEnd-/
/-ResultEnd-/

end Submission
