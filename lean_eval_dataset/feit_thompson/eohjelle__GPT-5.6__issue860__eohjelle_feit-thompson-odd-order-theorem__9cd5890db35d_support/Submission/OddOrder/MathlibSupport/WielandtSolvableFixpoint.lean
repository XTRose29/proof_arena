import Submission.OddOrder.MathlibSupport.WielandtQuotientHomocyclic
import Submission.OddOrder.MathlibSupport.SolvableComplementActorConjugacy
import Submission.OddOrder.MathlibSupport.SolvableComplementConjugacy
import Submission.OddOrder.MathlibSupport.MinimalNormalExistence
import Submission.OddOrder.MathlibSupport.MinimalNormalElementaryAbelian
import Submission.OddOrder.MathlibSupport.SubgroupCardinality
import Submission.OddOrder.BG.Section03.FrobeniusPartitionSum
import Mathlib.Algebra.Module.ZMod
import Mathlib.FieldTheory.Finiteness
import Mathlib.RepresentationTheory.Invariants
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.LocalRing.Module

/-!
# The solvable Wielandt fixed-point formula

This is the Lean port of the final theorem of `wielandt_fixpoint.v`.  The
preceding module constructs the homocyclic covers of an elementary abelian
minimal normal subgroup.  Here we apply the norm/averaging operator to those
covers, compare its trace with the rank of its fixed summand, and finish by
induction through a solvable kernel.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped Classical IsMulCommutative

universe u v

set_option maxHeartbeats 1000000

/-! ### Finite-free averaging over a prime-power residue ring -/

/-- `ZMod (p ^ e)` is local when `p` is prime and `e` is positive. -/
private theorem zmod_primePower_isLocalRing
    {p e : ℕ} (hp : p.Prime) (he : 0 < e) :
    IsLocalRing (ZMod (p ^ e)) := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fact (1 < p ^ e) :=
    ⟨one_lt_pow₀ hp.one_lt (Nat.ne_of_gt he)⟩
  apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
  intro a
  by_cases ha : p ∣ a.val
  · right
    rw [← ZMod.natCast_zmod_val (1 - a)]
    apply (ZMod.isUnit_natCast_iff_not_dvd_pow hp he).2
    intro hpa
    have hpq : p ∣ p ^ e := dvd_pow_self p (Nat.ne_of_gt he)
    let c : ZMod (p ^ e) →+* ZMod p := ZMod.castHom hpq (ZMod p)
    have hac : c a = 0 := by
      rw [← ZMod.natCast_zmod_val a, map_natCast]
      exact (ZMod.natCast_eq_zero_iff _ _).mpr ha
    have hbc : c (1 - a) = 0 := by
      rw [← ZMod.natCast_zmod_val (1 - a), map_natCast]
      exact (ZMod.natCast_eq_zero_iff _ _).mpr hpa
    have hone : (1 : ZMod p) = 0 := by
      calc
        (1 : ZMod p) = 1 - c a := by rw [hac, sub_zero]
        _ = c (1 - a) := by rw [map_sub, map_one]
        _ = 0 := hbc
    exact one_ne_zero hone
  · left
    rw [← ZMod.natCast_zmod_val a]
    exact (ZMod.isUnit_natCast_iff_not_dvd_pow hp he).2 ha

section Projection

variable {R M : Type*} [CommRing R] [IsLocalRing R]
variable [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Free R M]

/-- The canonical retraction onto the range of a projection. -/
def isProjRangeRetraction
    {P : Submodule R M} {f : M →ₗ[R] M} (hf : LinearMap.IsProj P f) :
    M →ₗ[R] P :=
  f.codRestrict P hf.map_mem

theorem isProjRangeRetraction_comp_subtype
    {P : Submodule R M} {f : M →ₗ[R] M} (hf : LinearMap.IsProj P f) :
    (isProjRangeRetraction hf).comp P.subtype = LinearMap.id := by
  ext x
  change f (x : M) = x
  exact hf.map_id x x.property

theorem isProjRangeRetraction_surjective
    {P : Submodule R M} {f : M →ₗ[R] M} (hf : LinearMap.IsProj P f) :
    Function.Surjective (isProjRangeRetraction hf) := by
  intro x
  exact ⟨x, Subtype.ext (hf.map_id x x.property)⟩

/-- The complementary retraction onto the kernel of a projection. -/
def isProjKerRetraction
    {P : Submodule R M} {f : M →ₗ[R] M} (hf : LinearMap.IsProj P f) :
    M →ₗ[R] LinearMap.ker f :=
  (LinearMap.id - f).codRestrict (LinearMap.ker f) (by
    intro x
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply]
    rw [map_sub, hf.map_id (f x) (hf.map_mem x), sub_self])

theorem isProjKerRetraction_comp_subtype
    {P : Submodule R M} {f : M →ₗ[R] M} (hf : LinearMap.IsProj P f) :
    (isProjKerRetraction hf).comp (LinearMap.ker f).subtype = LinearMap.id := by
  ext x
  change (x : M) - f x = x
  rw [LinearMap.mem_ker.mp x.property]
  simp

theorem isProjKerRetraction_surjective
    {P : Submodule R M} {f : M →ₗ[R] M} (hf : LinearMap.IsProj P f) :
    Function.Surjective (isProjKerRetraction hf) := by
  intro x
  exact ⟨x, LinearMap.congr_fun
    (isProjKerRetraction_comp_subtype hf) x⟩

/-- Over a local ring, the two summands of a projection of a finite free
module are finite free. -/
theorem isProjTrace_eq_finrank
    {P : Submodule R M} {f : M →ₗ[R] M} (hf : LinearMap.IsProj P f) :
    LinearMap.trace R M f = (Module.finrank R P : R) := by
  letI : Module.Finite R P :=
    Module.Finite.of_surjective (isProjRangeRetraction hf)
      (isProjRangeRetraction_surjective hf)
  letI : Module.Flat R P :=
    Module.Flat.of_retract P.subtype (isProjRangeRetraction hf)
      (isProjRangeRetraction_comp_subtype hf)
  letI : Module.Free R P := Module.free_of_flat_of_isLocalRing
  let K := LinearMap.ker f
  letI : Module.Finite R K :=
    Module.Finite.of_surjective (isProjKerRetraction hf)
      (isProjKerRetraction_surjective hf)
  letI : Module.Flat R K :=
    Module.Flat.of_retract K.subtype (isProjKerRetraction hf)
      (isProjKerRetraction_comp_subtype hf)
  letI : Module.Free R K := Module.free_of_flat_of_isLocalRing
  exact hf.trace

/-- The range of a projection of a finite free module over a local ring is
itself finite free.  This separate form is used to count its reduction
modulo `p`. -/
theorem isProjRange_finite
    {P : Submodule R M} {f : M →ₗ[R] M} (hf : LinearMap.IsProj P f) :
    Module.Finite R P :=
  Module.Finite.of_surjective (isProjRangeRetraction hf)
    (isProjRangeRetraction_surjective hf)

theorem isProjRange_free
    {P : Submodule R M} {f : M →ₗ[R] M} (hf : LinearMap.IsProj P f)
    [Module.Finite R P] : Module.Free R P := by
  letI : Module.Flat R P :=
    Module.Flat.of_retract P.subtype (isProjRangeRetraction hf)
      (isProjRangeRetraction_comp_subtype hf)
  exact Module.free_of_flat_of_isLocalRing

end Projection

section PrimeReduction

variable {p e : ℕ} (hp : p.Prime) (he : 0 < e)
variable {M : Type*} [AddCommGroup M]
variable [Module (ZMod (p ^ e)) M]
variable [Module.Finite (ZMod (p ^ e)) M]
variable [Module.Free (ZMod (p ^ e)) M]

/-- Coordinatewise reduction of a finite free `ZMod (p^e)`-module modulo
`p`, using its canonical finite basis. -/
private noncomputable def zmodPrimeReduction :
    M →+ (Fin (Module.finrank (ZMod (p ^ e)) M) → ZMod p) := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fact (1 < p ^ e) :=
    ⟨one_lt_pow₀ hp.one_lt (Nat.ne_of_gt he)⟩
  let b := Module.finBasis (ZMod (p ^ e)) M
  have hpq : p ∣ p ^ e := dvd_pow_self p (Nat.ne_of_gt he)
  let c : ZMod (p ^ e) →+* ZMod p := ZMod.castHom hpq (ZMod p)
  exact
    { toFun := fun x i ↦ c (b.equivFun x i)
      map_zero' := by ext; simp
      map_add' := by intro x y; ext; simp }

private theorem zmodPrimeReduction_surjective :
    Function.Surjective (zmodPrimeReduction hp he (M := M)) := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fact (1 < p ^ e) :=
    ⟨one_lt_pow₀ hp.one_lt (Nat.ne_of_gt he)⟩
  let b := Module.finBasis (ZMod (p ^ e)) M
  have hpq : p ∣ p ^ e := dvd_pow_self p (Nat.ne_of_gt he)
  let c : ZMod (p ^ e) →+* ZMod p := ZMod.castHom hpq (ZMod p)
  intro y
  choose x hx using fun i ↦ ZMod.castHom_surjective hpq (y i)
  refine ⟨b.equivFun.symm x, ?_⟩
  ext i
  change c (b.equivFun (b.equivFun.symm x) i) = y i
  rw [b.equivFun.apply_symm_apply]
  exact hx i

private theorem zmodPrimeReduction_eq_zero_iff (x : M) :
    zmodPrimeReduction hp he x = 0 ↔
      ∃ y : M, ((p : ℕ) : ZMod (p ^ e)) • y = x := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fact (1 < p ^ e) :=
    ⟨one_lt_pow₀ hp.one_lt (Nat.ne_of_gt he)⟩
  let b := Module.finBasis (ZMod (p ^ e)) M
  have hpq : p ∣ p ^ e := dvd_pow_self p (Nat.ne_of_gt he)
  let c : ZMod (p ^ e) →+* ZMod p := ZMod.castHom hpq (ZMod p)
  constructor
  · intro hx
    have hcoord : ∀ i, c (b.equivFun x i) = 0 := by
      intro i
      exact congrFun hx i
    have hdiv : ∀ i, p ∣ (b.equivFun x i).val := by
      intro i
      have hi := hcoord i
      rw [← ZMod.natCast_zmod_val (b.equivFun x i), map_natCast] at hi
      exact (ZMod.natCast_eq_zero_iff _ _).mp hi
    let z : Fin (Module.finrank (ZMod (p ^ e)) M) → ZMod (p ^ e) :=
      fun i ↦ ((b.equivFun x i).val / p : ℕ)
    refine ⟨b.equivFun.symm z, ?_⟩
    apply b.equivFun.injective
    ext i
    simp only [map_smul, LinearEquiv.apply_symm_apply, Pi.smul_apply, z]
    change (p : ZMod (p ^ e)) *
        ((b.equivFun x i).val / p : ZMod (p ^ e)) = b.equivFun x i
    rw [← Nat.cast_mul]
    have hi := Nat.mul_div_cancel' (hdiv i)
    rw [hi, ZMod.natCast_zmod_val]
  · rintro ⟨y, rfl⟩
    ext i
    change c (b.equivFun
      (((p : ℕ) : ZMod (p ^ e)) • y) i) = 0
    rw [map_smul]
    change c (((p : ℕ) : ZMod (p ^ e)) * b.equivFun y i) = 0
    rw [map_mul]
    have hpzero : c ((p : ℕ) : ZMod (p ^ e)) = 0 := by
      rw [map_natCast]
      exact (ZMod.natCast_eq_zero_iff _ _).mpr dvd_rfl
    rw [hpzero, zero_mul]

/-- The index of the `p`-multiple submodule in a finite free
`ZMod (p^e)`-module is `p` to the module rank. -/
private theorem zmodPrimeMultiple_index :
    (zmodPrimeReduction hp he (M := M)).ker.index =
      p ^ Module.finrank (ZMod (p ^ e)) M := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fact (1 < p ^ e) :=
    ⟨one_lt_pow₀ hp.one_lt (Nat.ne_of_gt he)⟩
  rw [AddSubgroup.index_ker]
  have hrange : Nat.card (zmodPrimeReduction hp he (M := M)).range =
      Nat.card (Fin (Module.finrank (ZMod (p ^ e)) M) → ZMod p) := by
    rw [AddMonoidHom.range_eq_top.mpr
      (zmodPrimeReduction_surjective hp he (M := M))]
    simp
  rw [hrange, Nat.card_fun, Nat.card_fin, Nat.card_zmod]

include hp he

/-- A surjective additive quotient of a finite free prime-power module whose
kernel is precisely the `p`-multiple subgroup has cardinality `p ^ rank`.
This is the counting bridge between the fixed summand of the homocyclic
cover and the fixed subgroup of its elementary-abelian quotient. -/
private theorem natCard_eq_prime_pow_finrank_of_ker_eq_primeMultiple
    {N : Type*} [AddCommGroup N] (q : M →+ N)
    (hq : Function.Surjective q)
    (hker : ∀ x : M, q x = 0 ↔
      ∃ y : M, ((p : ℕ) : ZMod (p ^ e)) • y = x) :
    Nat.card N = p ^ Module.finrank (ZMod (p ^ e)) M := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fact (1 < p ^ e) :=
    ⟨one_lt_pow₀ hp.one_lt (Nat.ne_of_gt he)⟩
  have hkerEq : q.ker = (zmodPrimeReduction hp he (M := M)).ker := by
    ext x
    rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_ker,
      hker, zmodPrimeReduction_eq_zero_iff hp he]
  calc
    Nat.card N = Nat.card q.range := by
      rw [AddMonoidHom.range_eq_top.mpr hq]
      simp
    _ = q.ker.index := (AddSubgroup.index_ker q).symm
    _ = (zmodPrimeReduction hp he (M := M)).ker.index := by rw [hkerEq]
    _ = p ^ Module.finrank (ZMod (p ^ e)) M :=
      zmodPrimeMultiple_index hp he

/-- Rank recovery from the cardinality of a prime-field quotient. -/
private theorem finrank_eq_of_surjective_prime_quotient
    {N : Type*} [AddCommGroup N] (q : M →+ N)
    (hq : Function.Surjective q)
    (hker : ∀ x : M, q x = 0 ↔
      ∃ y : M, ((p : ℕ) : ZMod (p ^ e)) • y = x)
    {r : ℕ} (hcard : Nat.card N = p ^ r) :
    Module.finrank (ZMod (p ^ e)) M = r := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fact (1 < p ^ e) :=
    ⟨one_lt_pow₀ hp.one_lt (Nat.ne_of_gt he)⟩
  apply Nat.pow_right_injective hp.two_le
  exact (natCard_eq_prime_pow_finrank_of_ker_eq_primeMultiple
    hp he q hq hker).symm.trans hcard

end PrimeReduction

section AveragingTrace

variable {R H M : Type*} [CommRing R] [IsLocalRing R]
variable [Group H] [Fintype H]
variable [AddCommGroup M] [Module R M]
variable [Module.Finite R M] [Module.Free R M]

/-- Averaging written directly in terms of the representation norm.  This
form is convenient over `ZMod (p ^ e)`, where invertibility of the actor's
order follows from the coprimality hypothesis. -/
noncomputable def normAverageMap
    (rho : Representation R H M) [Invertible (Fintype.card H : R)] :
    M →ₗ[R] M :=
  ⅟(Fintype.card H : R) • rho.norm

theorem normAverageMap_invariant
    (rho : Representation R H M) [Invertible (Fintype.card H : R)]
    (x : M) :
    normAverageMap rho x ∈ rho.invariants := by
  rw [Representation.mem_invariants]
  intro h
  simp only [normAverageMap, LinearMap.smul_apply,
    map_smul, Representation.self_norm_apply]

theorem normAverageMap_id
    (rho : Representation R H M) [Invertible (Fintype.card H : R)]
    (x : M) (hx : x ∈ rho.invariants) :
    normAverageMap rho x = x := by
  have hnorm : rho.norm x = (Fintype.card H : R) • x := by
    simp only [Representation.norm, LinearMap.sum_apply]
    rw [Fintype.sum_congr _ _ (fun h ↦ hx h), Finset.sum_const,
      Finset.card_univ, ← Nat.cast_smul_eq_nsmul R]
  rw [normAverageMap, LinearMap.smul_apply, hnorm,
    smul_smul, invOf_mul_self, one_smul]

theorem isProj_normAverageMap
    (rho : Representation R H M) [Invertible (Fintype.card H : R)] :
    LinearMap.IsProj rho.invariants (normAverageMap rho) :=
  ⟨normAverageMap_invariant rho, normAverageMap_id rho⟩

theorem card_smul_normAverageMap
    (rho : Representation R H M) [Invertible (Fintype.card H : R)] :
    (Fintype.card H : R) • normAverageMap rho = rho.norm := by
  ext x
  simp only [normAverageMap, LinearMap.smul_apply, smul_smul,
    mul_invOf_self, one_smul]

/-- The trace of a group norm is the actor order times the rank of the fixed
summand.  No field hypothesis is needed: the fixed summand is a retract of a
finite free module, hence free over the local coefficient ring. -/
theorem trace_norm_eq_card_mul_finrank
    (rho : Representation R H M) [Invertible (Fintype.card H : R)] :
    LinearMap.trace R M rho.norm =
      (Fintype.card H : R) * Module.finrank R rho.invariants := by
  calc
    LinearMap.trace R M rho.norm =
        LinearMap.trace R M ((Fintype.card H : R) • normAverageMap rho) := by
      rw [card_smul_normAverageMap rho]
    _ = (Fintype.card H : R) *
        LinearMap.trace R M (normAverageMap rho) := by
      simp only [map_smul, smul_eq_mul]
    _ = (Fintype.card H : R) * Module.finrank R rho.invariants := by
      rw [isProjTrace_eq_finrank (isProj_normAverageMap rho)]

end AveragingTrace

section FixedQuotientRank

variable {p e : ℕ} (hp : p.Prime) (he : 0 < e)
variable {H M N : Type*} [Group H] [Fintype H]
variable [AddCommGroup M] [Module (ZMod (p ^ e)) M]
variable [Module.Finite (ZMod (p ^ e)) M]
variable [Module.Free (ZMod (p ^ e)) M]
variable [AddCommGroup N] [Module (ZMod p) N]

/-- Restrict an equivariant additive quotient to the two fixed submodules. -/
private def fixedQuotientAdd
    (rho : Representation (ZMod (p ^ e)) H M)
    (sigma : Representation (ZMod p) H N)
    (q : M →+ N)
    (hequiv : ∀ h x, q (rho h x) = sigma h (q x)) :
    rho.invariants →+ sigma.invariants where
  toFun x := ⟨q x, fun h ↦ by
    rw [← hequiv]
    exact congrArg q (x.property h)⟩
  map_zero' := by ext; exact q.map_zero
  map_add' x y := by ext; exact q.map_add x y

include hp he

/-- Fixed points commute with a coprime prime-power quotient.  The proof is
the usual averaging argument: average a lift to obtain a fixed lift, and
average a preimage in the kernel to show that the fixed kernel consists
exactly of `p`-multiples of fixed vectors. -/
private theorem finrank_invariants_eq_of_prime_quotient
    (rho : Representation (ZMod (p ^ e)) H M)
    (sigma : Representation (ZMod p) H N)
    (c : ZMod (p ^ e) →+* ZMod p)
    (q : M →+ N)
    (hscalar : ∀ r x, q (r • x) = c r • q x)
    (hequiv : ∀ h x, q (rho h x) = sigma h (q x))
    (hq : Function.Surjective q)
    (hker : ∀ x : M, q x = 0 ↔
      ∃ y : M, ((p : ℕ) : ZMod (p ^ e)) • y = x)
    (hcp : c ((p : ℕ) : ZMod (p ^ e)) = 0)
    [Invertible (Fintype.card H : ZMod (p ^ e))]
    {r : ℕ} (hcard : Nat.card ↥sigma.invariants = p ^ r) :
    Module.finrank (ZMod (p ^ e)) rho.invariants = r := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fact (1 < p ^ e) :=
    ⟨one_lt_pow₀ hp.one_lt (Nat.ne_of_gt he)⟩
  letI : IsLocalRing (ZMod (p ^ e)) := zmod_primePower_isLocalRing hp he
  letI : Module.Finite (ZMod (p ^ e)) rho.invariants :=
    isProjRange_finite (isProj_normAverageMap rho)
  letI : Module.Free (ZMod (p ^ e)) rho.invariants :=
    isProjRange_free (isProj_normAverageMap rho)
  let qfix : rho.invariants →+ sigma.invariants :=
    fixedQuotientAdd rho sigma q hequiv
  have hqfix : Function.Surjective qfix := by
    intro v
    obtain ⟨x, hx⟩ := hq v
    let y : M := normAverageMap rho x
    have hy : y ∈ rho.invariants := normAverageMap_invariant rho x
    refine ⟨⟨y, hy⟩, ?_⟩
    apply Subtype.ext
    change q y = v
    have hnorm : q (rho.norm x) =
        (Fintype.card H : ZMod p) • v := by
      calc
        q (rho.norm x) = ∑ h : H, q (rho h x) := by
          simp only [Representation.norm, LinearMap.sum_apply, map_sum]
        _ = ∑ h : H, sigma h (q x) := by
          apply Fintype.sum_congr
          intro h
          exact hequiv h x
        _ = ∑ _h : H, (v : N) := by
          apply Fintype.sum_congr
          intro h
          rw [hx]
          exact v.property h
        _ = (Fintype.card H : ZMod p) • v := by
          rw [Finset.sum_const, Finset.card_univ,
            ← Nat.cast_smul_eq_nsmul (ZMod p)]
    have hcast : c (Fintype.card H : ZMod (p ^ e)) =
        (Fintype.card H : ZMod p) := map_natCast c (Fintype.card H)
    have hcoeff :
        c (⅟(Fintype.card H : ZMod (p ^ e))) *
            (Fintype.card H : ZMod p) = 1 := by
      rw [← hcast, ← map_mul, invOf_mul_self, map_one]
    dsimp [y]
    rw [normAverageMap, LinearMap.smul_apply,
      hscalar, hnorm, smul_smul, hcoeff, one_smul]
  have hqfixKer : ∀ x : rho.invariants, qfix x = 0 ↔
      ∃ y : rho.invariants,
        ((p : ℕ) : ZMod (p ^ e)) • y = x := by
    intro x
    constructor
    · intro hx
      have hxq : q (x : M) = 0 := congrArg Subtype.val hx
      obtain ⟨y, hy⟩ := (hker x).mp hxq
      let z : M := normAverageMap rho y
      have hz : z ∈ rho.invariants := normAverageMap_invariant rho y
      refine ⟨⟨z, hz⟩, ?_⟩
      apply Subtype.ext
      change ((p : ℕ) : ZMod (p ^ e)) • z = (x : M)
      calc
        ((p : ℕ) : ZMod (p ^ e)) • z =
            normAverageMap rho
              (((p : ℕ) : ZMod (p ^ e)) • y) := by
          rw [map_smul]
        _ = normAverageMap rho x := by rw [hy]
        _ = x := normAverageMap_id rho x x.property
    · rintro ⟨y, rfl⟩
      apply Subtype.ext
      change q (((p : ℕ) : ZMod (p ^ e)) • (y : M)) = 0
      rw [hscalar, hcp, zero_smul]
  apply finrank_eq_of_surjective_prime_quotient hp he qfix hqfix hqfixKer hcard

end FixedQuotientRank

/-! ### Fixed cosets modulo a solvable normal Hall subgroup -/

/-- Solvable-left form of coprime fixed-coset lifting.  The existing support
library contains the ambient-solvable and actor-solvable variants; the
Wielandt induction needs the third Schur--Zassenhaus branch, where only the
normal quotient kernel is solvable. -/
private theorem map_centralizer_quotient_eq_of_coprime_of_solvable_left
    {K : Type u} [Group K] [Finite K]
    {N R : Subgroup K} [N.Normal] [IsSolvable N]
    (hcop : Nat.Coprime (Nat.card N) (Nat.card R)) :
    (Subgroup.centralizer (R : Set K)).map (QuotientGroup.mk' N) =
      Subgroup.centralizer
        (R.map (QuotientGroup.mk' N) : Set (K ⧸ N)) := by
  classical
  let q : K →* K ⧸ N := QuotientGroup.mk' N
  apply le_antisymm
  · rintro _ ⟨c, hc, rfl⟩
    apply Subgroup.mem_centralizer_iff.mpr
    rintro _ ⟨r, hr, rfl⟩
    exact congrArg q (Subgroup.mem_centralizer_iff.mp hc r hr)
  · intro z hz
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N z
    let Rg : Subgroup K := R.map (MulAut.conj g).toMonoidHom
    have hRgL : Rg ≤ N ⊔ R := by
      rintro _ ⟨r, hr, rfl⟩
      have hcomm := Subgroup.mem_centralizer_iff.mp hz (q r)
        (Subgroup.mem_map_of_mem q hr)
      change q r * q g = q g * q r at hcomm
      have hqeq : q (g * r * g⁻¹) = q r := by
        change q g * q r * (q g)⁻¹ = q r
        rw [← hcomm]
        group
      have hker : (g * r * g⁻¹)⁻¹ * r ∈ N := QuotientGroup.eq.mp hqeq
      change g * r * g⁻¹ ∈ N ⊔ R
      rw [show g * r * g⁻¹ = r * ((g * r * g⁻¹)⁻¹ * r)⁻¹ by group]
      exact (N ⊔ R).mul_mem
        ((show R ≤ N ⊔ R from le_sup_right) hr)
        ((show N ≤ N ⊔ R from le_sup_left) (N.inv_mem hker))
    let L : Subgroup K := N ⊔ R
    let NL : Subgroup L := N.subgroupOf L
    let RL : Subgroup L := R.subgroupOf L
    let RgL : Subgroup L := Rg.subgroupOf L
    letI : NL.Normal := by
      dsimp [NL]
      exact Subgroup.Normal.subgroupOf (inferInstance : N.Normal) L
    letI : IsSolvable NL :=
      solvable_of_solvable_injective
        (f := (Subgroup.subgroupOfEquivOfLe
          (show N ≤ L from le_sup_left)).toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe
          (show N ≤ L from le_sup_left)).injective
    have hcardNL : Nat.card NL = Nat.card N :=
      natCard_subgroupOf_eq le_sup_left
    have hcardRL : Nat.card RL = Nat.card R :=
      natCard_subgroupOf_eq le_sup_right
    have hdisNR : Disjoint N R := Subgroup.disjoint_of_coprime_natCard hcop
    have hdisNLRL : Disjoint NL RL := by
      rw [disjoint_iff]
      apply le_antisymm _ bot_le
      intro x hx
      apply Subgroup.mem_bot.mpr
      apply Subtype.ext
      apply Subgroup.mem_bot.mp
      rw [← disjoint_iff.mp hdisNR]
      exact hx
    have hsupNLRL : NL ⊔ RL = ⊤ := by
      change N.subgroupOf L ⊔ R.subgroupOf L = ⊤
      rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right]
      exact Subgroup.subgroupOf_self L
    have hcompRL : NL.IsComplement' RL := by
      apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisNLRL
      rw [← Subgroup.normal_mul NL RL, hsupNLRL]
      rfl
    have hcardRg : Nat.card Rg = Nat.card R := by
      dsimp [Rg]
      exact Subgroup.card_map_of_injective (MulAut.conj g).injective
    have hcardRgL : Nat.card RgL = Nat.card RL := by
      rw [natCard_subgroupOf_eq hRgL, hcardRg,
        natCard_subgroupOf_eq le_sup_right]
    have hcompRgL : NL.IsComplement' RgL := by
      apply Subgroup.isComplement'_of_coprime
      · rw [hcardRgL]
        exact hcompRL.card_mul
      · rw [hcardNL, hcardRgL, hcardRL]
        exact hcop
    have hcopNLindex : Nat.Coprime (Nat.card NL) NL.index := by
      rw [hcompRL.symm.index_eq_card, hcardNL, hcardRL]
      exact hcop
    obtain ⟨n, hn⟩ :=
      Subgroup.solvable_complement_conjugacy
        hcopNLindex hcompRL hcompRgL
    let nK : K := ((n : NL) : L)
    have hnN : nK ∈ N := n.property
    let c : K := nK⁻¹ * g
    have hconjR (r : K) (hr : r ∈ R) : c * r * c⁻¹ ∈ R := by
      have hxRg : g * r * g⁻¹ ∈ Rg := ⟨r, hr, rfl⟩
      let xL : L := ⟨g * r * g⁻¹, hRgL hxRg⟩
      have hxRgL : xL ∈ RgL := hxRg
      rw [hn] at hxRgL
      rcases hxRgL with ⟨s, hs, hns⟩
      have hnsK : nK * (s : K) * nK⁻¹ = g * r * g⁻¹ :=
        congrArg (fun y : L ↦ (y : K)) hns
      rw [show c * r * c⁻¹ = (s : K) by
        dsimp [c]
        calc
          nK⁻¹ * g * r * (nK⁻¹ * g)⁻¹ =
              nK⁻¹ * (g * r * g⁻¹) * nK := by group
          _ = nK⁻¹ * (nK * (s : K) * nK⁻¹) * nK := by rw [← hnsK]
          _ = (s : K) := by group]
      exact hs
    have hqn : q nK = 1 := QuotientGroup.eq_one_iff nK |>.mpr hnN
    have hqc : q c = q g := by simp [c, hqn]
    refine ⟨c, ?_, hqc⟩
    apply Subgroup.mem_centralizer_iff.mpr
    intro r hr
    have hcr : c * r * c⁻¹ ∈ R := hconjR r hr
    have hcomm := Subgroup.mem_centralizer_iff.mp hz (q r)
      (Subgroup.mem_map_of_mem q hr)
    change q r * q g = q g * q r at hcomm
    have hqeq : q (c * r * c⁻¹) = q r := by
      change q c * q r * (q c)⁻¹ = q r
      rw [hqc, ← hcomm]
      group
    have hdiffN : (c * r * c⁻¹)⁻¹ * r ∈ N := QuotientGroup.eq.mp hqeq
    have hdiffR : (c * r * c⁻¹)⁻¹ * r ∈ R :=
      R.mul_mem (R.inv_mem hcr) hr
    have hdiffOne : (c * r * c⁻¹)⁻¹ * r = 1 := by
      apply Subgroup.mem_bot.mp
      rw [← disjoint_iff.mp hdisNR]
      exact ⟨hdiffN, hdiffR⟩
    have hconjEq : c * r * c⁻¹ = r := inv_mul_eq_one.mp hdiffOne
    symm
    calc
      c * r = (c * r * c⁻¹) * c := by group
      _ = r * c := by rw [hconjEq]

/-- Internal-centralizer form of the solvable-left fixed-coset lemma. -/
private theorem map_centralizerWithin_quotient_eq_of_coprime_of_solvable_left
    {K : Type u} [Group K] [Finite K]
    {N Y R : Subgroup K} [N.Normal] [IsSolvable N]
    (hNY : N ≤ Y)
    (hcop : Nat.Coprime (Nat.card N) (Nat.card R)) :
    (centralizerWithin Y R).map (QuotientGroup.mk' N) =
      centralizerWithin (Y.map (QuotientGroup.mk' N))
        (R.map (QuotientGroup.mk' N)) := by
  classical
  let q : K →* K ⧸ N := QuotientGroup.mk' N
  have hcent :=
    map_centralizer_quotient_eq_of_coprime_of_solvable_left hcop
  apply le_antisymm
  · rintro _ ⟨c, hc, rfl⟩
    refine ⟨⟨c, hc.1, rfl⟩, ?_⟩
    have hcmap : q c ∈
        (Subgroup.centralizer (R : Set K)).map q :=
      ⟨c, hc.2, rfl⟩
    rwa [hcent] at hcmap
  · intro z hz
    have hzCent : z ∈
        (Subgroup.centralizer (R : Set K)).map q := by
      rw [hcent]
      exact hz.2
    rcases hzCent with ⟨c, hcCent, hcz⟩
    rcases hz.1 with ⟨y, hy, hyz⟩
    have hqeq : q c = q y := hcz.trans hyz.symm
    have hdiff : c⁻¹ * y ∈ N := QuotientGroup.eq.mp hqeq
    have hcY : c ∈ Y := by
      rw [show c = y * (c⁻¹ * y)⁻¹ by group]
      exact Y.mul_mem hy (Y.inv_mem (hNY hdiff))
    exact ⟨c, ⟨hcY, hcCent⟩, hcz⟩

/-! ### Conjugation invariants and internal centralizers -/

/-- A subgroup known to normalize `V`, regarded as a subgroup of the full
normalizer. -/
private def subgroupToNormalizer
    {E : Type*} [Group E] (V A : Subgroup E)
    (hA : A ≤ Subgroup.normalizer (V : Set E)) :
    A →* Subgroup.normalizer (V : Set E) where
  toFun a := ⟨a, hA a.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Conjugation by a normalizing subgroup on an elementary-abelian module. -/
private def subgroupConjugationRepresentation
    {E : Type*} [Group E] (V A : Subgroup E) (p : ℕ)
    [IsMulCommutative V] [Module (ZMod p) (Additive V)]
    (hA : A ≤ Subgroup.normalizer (V : Set E)) :
    Representation (ZMod p) A (Additive V) :=
  (normalizerConjugationRepresentation V p).comp
    (subgroupToNormalizer V A hA)

@[simp]
private theorem subgroupConjugationRepresentation_apply
    {E : Type*} [Group E] (V A : Subgroup E) (p : ℕ)
    [IsMulCommutative V] [Module (ZMod p) (Additive V)]
    (hA : A ≤ Subgroup.normalizer (V : Set E))
    (a : A) (x : Additive V) :
    subgroupConjugationRepresentation V A p hA a x =
      Additive.ofMul
        ((⟨a, hA a.2⟩ : Subgroup.normalizer (V : Set E)) • x.toMul) :=
  rfl

/-- The fixed vectors of the conjugation representation are precisely the
elements of the internal centralizer. -/
private noncomputable def conjugationInvariantsEquivCentralizer
    {E : Type*} [Group E] (V A : Subgroup E) (p : ℕ)
    [IsMulCommutative V] [Module (ZMod p) (Additive V)]
    (hA : A ≤ Subgroup.normalizer (V : Set E)) :
    (subgroupConjugationRepresentation V A p hA).invariants ≃
      Additive (centralizerWithin V A) where
  toFun x := Additive.ofMul ⟨(x : Additive V).toMul, ⟨x.val.toMul.2, by
    intro a ha
    let aA : A := ⟨a, ha⟩
    have hx := x.property aA
    have hxE : a * (x.val.toMul : E) * a⁻¹ = (x.val.toMul : E) := by
      exact congrArg (fun y : Additive V ↦ (y.toMul : E)) hx
    calc
      a * (x.val.toMul : E) =
          (a * (x.val.toMul : E) * a⁻¹) * a := by group
      _ = (x.val.toMul : E) * a := by rw [hxE]⟩⟩
  invFun z := ⟨Additive.ofMul ⟨(z.toMul : E), z.toMul.2.1⟩, by
    intro a
    apply Additive.toMul.injective
    apply Subtype.ext
    change (a : E) * (z.toMul : E) * (a : E)⁻¹ = (z.toMul : E)
    have hcomm := z.toMul.2.2 (a : E) a.2
    rw [hcomm]
    group⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv z := by apply Additive.toMul.injective; apply Subtype.ext; rfl

private theorem natCard_conjugation_invariants
    {E : Type*} [Group E] (V A : Subgroup E) (p : ℕ)
    [IsMulCommutative V] [Module (ZMod p) (Additive V)]
    (hA : A ≤ Subgroup.normalizer (V : Set E)) :
    Nat.card ↥((subgroupConjugationRepresentation V A p hA).invariants) =
      Nat.card (centralizerWithin V A) := by
  calc
    Nat.card ↥((subgroupConjugationRepresentation V A p hA).invariants) =
        Nat.card (Additive (centralizerWithin V A)) :=
      Nat.card_congr (conjugationInvariantsEquivCentralizer V A p hA)
    _ = Nat.card (centralizerWithin V A) := Nat.card_congr Additive.toMul

/-- Restriction along a surjective group homomorphism does not change the
fixed submodule. -/
private theorem Representation.invariants_comp_eq_of_surjective
    {k H A M : Type*} [CommRing k] [Group H] [Group A]
    [AddCommGroup M] [Module k M]
    (rho : Representation k A M) (f : H →* A)
    (hf : Function.Surjective f) :
    Representation.invariants (rho.comp f) = rho.invariants := by
  ext x
  constructor
  · intro hx a
    obtain ⟨h, rfl⟩ := hf a
    exact hx h
  · intro hx h
    exact hx (f h)

/-! ### Cardinal factorization through a solvable normal kernel -/

/-- The centralizer cardinal factors into the fixed points in a solvable
normal kernel and the fixed points in the quotient. -/
private theorem natCard_centralizerWithin_eq_mul_quotient
    {K : Type u} [Group K] [Finite K]
    {B V A : Subgroup K} [B.Normal] [IsSolvable B]
    (hBV : B ≤ V)
    (hcop : Nat.Coprime (Nat.card B) (Nat.card A)) :
    Nat.card (centralizerWithin V A) =
      Nat.card (centralizerWithin B A) *
        Nat.card (centralizerWithin
          (V.map (QuotientGroup.mk' B))
          (A.map (QuotientGroup.mk' B))) := by
  classical
  let q : K →* K ⧸ B := QuotientGroup.mk' B
  let C : Subgroup K := centralizerWithin V A
  let CB : Subgroup K := centralizerWithin B A
  have hCBC : CB ≤ C := centralizerWithin_mono_left hBV
  let fC : C →* C.map q := q.subgroupMap C
  have hker : fC.ker = CB.subgroupOf C := by
    ext x
    constructor
    · intro hx
      have hxq : q (x : K) = 1 := by
        exact congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
      have hxB : (x : K) ∈ B := QuotientGroup.eq_one_iff (x : K) |>.mp hxq
      exact ⟨hxB, x.2.2⟩
    · intro hx
      apply MonoidHom.mem_ker.mpr
      apply Subtype.ext
      exact QuotientGroup.eq_one_iff (x : K) |>.mpr hx.1
  have hmap : C.map q = centralizerWithin (V.map q) (A.map q) := by
    dsimp [C, q]
    exact map_centralizerWithin_quotient_eq_of_coprime_of_solvable_left
      hBV hcop
  calc
    Nat.card C = Nat.card fC.ker * fC.ker.index :=
      fC.ker.card_mul_index.symm
    _ = Nat.card CB * fC.ker.index := by
      rw [hker, natCard_subgroupOf_eq hCBC]
    _ = Nat.card CB * Nat.card (C.map q) := by
      rw [Subgroup.index_ker]
      have hrange : fC.range = ⊤ := MonoidHom.range_eq_top.mpr
        (q.subgroupMap_surjective C)
      rw [hrange]
      simp
    _ = Nat.card CB * Nat.card
        (centralizerWithin (V.map q) (A.map q)) := by rw [hmap]

/-- When the quotient kernel is disjoint from `G`, quotienting does not
change membership in a subgroup of `G`. -/
private theorem mem_map_quotient_iff_of_le_of_coprime
    {K : Type u} [Group K] [Finite K]
    {B A G : Subgroup K} [B.Normal]
    (hAG : A ≤ G)
    (hcop : Nat.Coprime (Nat.card B) (Nat.card G))
    (a : G) :
    QuotientGroup.mk' B (a : K) ∈ A.map (QuotientGroup.mk' B) ↔
      (a : K) ∈ A := by
  let q : K →* K ⧸ B := QuotientGroup.mk' B
  have hdis : Disjoint B G := Subgroup.disjoint_of_coprime_natCard hcop
  constructor
  · rintro ⟨x, hxA, hxa⟩
    have hdiffB : x⁻¹ * (a : K) ∈ B := QuotientGroup.eq.mp hxa
    have hdiffG : x⁻¹ * (a : K) ∈ G :=
      G.mul_mem (G.inv_mem (hAG hxA)) a.2
    have hdiff : x⁻¹ * (a : K) = 1 := by
      apply Subgroup.mem_bot.mp
      rw [← disjoint_iff.mp hdis]
      exact ⟨hdiffB, hdiffG⟩
    have hxa' : x = (a : K) := inv_mul_eq_one.mp hdiff
    rwa [← hxa']
  · intro ha
    exact ⟨a, ha, rfl⟩

private theorem natCard_map_quotient_lt_of_ne_bot_of_le
    {K : Type u} [Group K] [Finite K]
    {B V : Subgroup K} [B.Normal]
    (hBV : B ≤ V) (hB : B ≠ ⊥) :
    Nat.card (V.map (QuotientGroup.mk' B)) < Nat.card V := by
  let q : K →* K ⧸ B := QuotientGroup.mk' B
  let f : V →* V.map q := q.subgroupMap V
  letI : Fintype V := Fintype.ofFinite V
  letI : Fintype (V.map q) := Fintype.ofFinite (V.map q)
  have hsurj : Function.Surjective f := q.subgroupMap_surjective V
  have hnotinj : ¬ Function.Injective f := by
    intro hinj
    obtain ⟨b, hb⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hB
    have hfb : f ⟨b, hBV b.2⟩ = f 1 := by
      apply Subtype.ext
      change q (b : K) = q 1
      rw [map_one]
      exact QuotientGroup.eq_one_iff (b : K) |>.mpr b.2
    have hbOne : (⟨b, hBV b.2⟩ : V) = 1 := hinj hfb
    apply hb
    apply Subtype.ext
    exact congrArg (fun x : V ↦ (x : K)) hbOne
  simpa only [Nat.card_eq_fintype_card] using
    Fintype.card_lt_of_surjective_not_injective f hsurj hnotinj

/-! ### Passing to the subgroup generated by kernel and actor -/

private theorem map_centralizerWithin_subgroupOf
    {K : Type u} [Group K]
    {J V A : Subgroup K} (hVJ : V ≤ J) (hAJ : A ≤ J) :
    (centralizerWithin (V.subgroupOf J) (A.subgroupOf J)).map J.subtype =
      centralizerWithin V A := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨hy.1, ?_⟩
    intro a ha
    let aJ : J := ⟨a, hAJ ha⟩
    exact congrArg Subtype.val (hy.2 aJ ha)
  · intro hx
    let xJ : J := ⟨x, hVJ hx.1⟩
    refine ⟨xJ, ?_, rfl⟩
    refine ⟨hx.1, ?_⟩
    intro a ha
    apply Subtype.ext
    exact hx.2 a ha

private theorem natCard_centralizerWithin_subgroupOf
    {K : Type u} [Group K] [Finite K]
    {J V A : Subgroup K} (hVJ : V ≤ J) (hAJ : A ≤ J) :
    Nat.card (centralizerWithin (V.subgroupOf J) (A.subgroupOf J)) =
      Nat.card (centralizerWithin V A) := by
  rw [← map_centralizerWithin_subgroupOf hVJ hAJ]
  exact (Subgroup.card_map_of_injective J.subtype_injective).symm

/-! ### Reindexing the weighted subgroup norms -/

/-- Incidences may be indexed either by a subgroup followed by one of its
elements, or by a group element followed by a subgroup containing it. -/
private def subgroupIncidenceEquiv
    {H ι : Type*} [Group H] (A : ι → Subgroup H) :
    (Σ i, A i) ≃ (Σ h : H, {i : ι // h ∈ A i}) where
  toFun z := ⟨z.2, ⟨z.1, z.2.2⟩⟩
  invFun z := ⟨z.2, ⟨z.1, z.2.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem sum_subtype_mem_eq_filter
    {ι H : Type*} [Fintype ι] [Group H]
    (A : ι → Subgroup H) (w : ι → ℕ) (h : H) :
    (∑ i : {i : ι // h ∈ A i}, w i) =
      ∑ i with h ∈ A i, w i := by
  symm
  apply Finset.sum_subtype
  intro i
  simp

/-- Equality of the pointwise membership sums is exactly equality of the
corresponding weighted sums of representation norms. -/
private theorem weighted_norm_eq_of_membership_sums
    {R H M ι : Type*} [CommRing R] [Group H] [Fintype H]
    [AddCommGroup M] [Module R M] [Fintype ι]
    (rho : Representation R H M) (A : ι → Subgroup H)
    (m n : ι → ℕ)
    (hpart : ∀ h : H,
      (∑ i with h ∈ A i, m i) = ∑ i with h ∈ A i, n i) :
    (∑ i, (m i : R) •
        Representation.norm (rho.comp (A i).subtype)) =
      ∑ i, (n i : R) •
        Representation.norm (rho.comp (A i).subtype) := by
  classical
  ext x
  simp only [LinearMap.sum_apply, LinearMap.smul_apply,
    Representation.norm]
  calc
    (∑ i, (m i : R) •
        ∑ a : A i, rho ((A i).subtype a) x) =
        ∑ z : Σ i, A i, (m z.1 : R) • rho z.2 x := by
      rw [Fintype.sum_sigma]
      apply Fintype.sum_congr
      intro i
      rw [Finset.smul_sum]
      apply Fintype.sum_congr
      intro a
      rfl
    _ = ∑ z : Σ h : H, {i : ι // h ∈ A i},
        (m z.2.1 : R) • rho z.1 x := by
      apply Fintype.sum_equiv (subgroupIncidenceEquiv A)
      intro z
      rfl
    _ = ∑ h : H, ∑ i : {i : ι // h ∈ A i},
        (m i : R) • rho h x := Fintype.sum_sigma _
    _ = ∑ h : H, ∑ i : {i : ι // h ∈ A i},
        (n i : R) • rho h x := by
      apply Fintype.sum_congr
      intro h
      have hw : (∑ i : {i : ι // h ∈ A i}, m i) =
          ∑ i : {i : ι // h ∈ A i}, n i := by
        rw [sum_subtype_mem_eq_filter A m h,
          sum_subtype_mem_eq_filter A n h, hpart h]
      calc
        (∑ i : {i : ι // h ∈ A i},
            (m i : R) • rho h x) =
            (∑ i : {i : ι // h ∈ A i}, (m i : R)) • rho h x := by
          rw [Finset.sum_smul]
        _ = ((∑ i : {i : ι // h ∈ A i}, m i : ℕ) : R) •
            rho h x := by rw [Nat.cast_sum]
        _ = ((∑ i : {i : ι // h ∈ A i}, n i : ℕ) : R) •
            rho h x := by rw [hw]
        _ = (∑ i : {i : ι // h ∈ A i}, (n i : R)) • rho h x := by
          rw [Nat.cast_sum]
        _ = ∑ i : {i : ι // h ∈ A i},
            (n i : R) • rho h x := by rw [Finset.sum_smul]
    _ = ∑ z : Σ h : H, {i : ι // h ∈ A i},
        (n z.2.1 : R) • rho z.1 x :=
      (Fintype.sum_sigma (fun z : Σ h : H, {i : ι // h ∈ A i} ↦
        (n z.2.1 : R) • rho z.1 x)).symm
    _ = ∑ z : Σ i, A i, (n z.1 : R) • rho z.2 x := by
      apply Fintype.sum_equiv (subgroupIncidenceEquiv A).symm
      intro z
      rfl
    _ = ∑ i, (n i : R) •
        ∑ a : A i, rho ((A i).subtype a) x := by
      rw [Fintype.sum_sigma]
      apply Fintype.sum_congr
      intro i
      rw [Finset.smul_sum]
      apply Fintype.sum_congr
      intro a
      rfl

/-! ### The trace calculation on a homocyclic cover -/

namespace IsoQuotientHomocyclicSdprod

variable {E : Type u} [Group E] {p e : ℕ} {V G : Subgroup E}

/-- The pulled-back actor subgroup maps onto the corresponding ambient
subgroup, not merely onto its subtype inside `G`. -/
private noncomputable def pullbackActorToAmbientSubgroup
    (X : IsoQuotientHomocyclicSdprod p e V G)
    (A : Subgroup E) (hAG : A ≤ G) :
    X.pullbackActorSubgroup (A.subgroupOf G) →* A where
  toFun g := ⟨G.subtype (X.actorEquiv g), g.2⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' x y := by apply Subtype.ext; simp

private theorem pullbackActorToAmbientSubgroup_surjective
    (X : IsoQuotientHomocyclicSdprod p e V G)
    (A : Subgroup E) (hAG : A ≤ G) :
    Function.Surjective (X.pullbackActorToAmbientSubgroup A hAG) := by
  intro a
  let aG : G := ⟨a, hAG a.2⟩
  let g : X.G₁ := X.actorEquiv.symm aG
  have hg : g ∈ X.pullbackActorSubgroup (A.subgroupOf G) := by
    change X.actorEquiv g ∈ A.subgroupOf G
    rw [show X.actorEquiv g = aG by simp [g]]
    exact a.2
  refine ⟨⟨g, hg⟩, ?_⟩
  apply Subtype.ext
  simp [pullbackActorToAmbientSubgroup, g, aG]

end IsoQuotientHomocyclicSdprod

private theorem trace_cover_norm_eq
    {E : Type u} [Group E] [Finite E]
    {p e : ℕ} (hp : p.Prime) (he : 0 < e)
    {V G : Subgroup E}
    (hV : IsElementaryAbelianGroup p V)
    (hGnorm : G ≤ Subgroup.normalizer (V : Set E))
    (X : IsoQuotientHomocyclicSdprod p e V G)
    (A : Subgroup E) (hAG : A ≤ G)
    (hcopA : Nat.Coprime p (Nat.card A))
    {r : ℕ} (hcard : Nat.card (centralizerWithin V A) = p ^ r) :
    let _ : Fintype X.G₁ := Fintype.ofFinite X.G₁
    let H := X.pullbackActorSubgroup (A.subgroupOf G)
    let _ : Fintype H := inferInstance
    let rho := X.actorRepresentation.comp H.subtype
    LinearMap.trace (ZMod (p ^ e)) X.ZModModel
      (Representation.norm rho) =
      ((Nat.card A * r : ℕ) : ZMod (p ^ e)) := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fact (1 < p ^ e) :=
    ⟨one_lt_pow₀ hp.one_lt (Nat.ne_of_gt he)⟩
  letI : IsMulCommutative V := hV.commutative
  letI : Module (ZMod p) (Additive V) :=
    elementaryAbelianZModModule V p hV.pow_eq_one
  letI : Fintype X.G₁ := Fintype.ofFinite X.G₁
  let H := X.pullbackActorSubgroup (A.subgroupOf G)
  letI : Fintype H := inferInstance
  have hcardH : Nat.card H = Nat.card A := by
    calc
      Nat.card H = Nat.card (A.subgroupOf G) :=
        X.natCard_pullbackActorSubgroup (A.subgroupOf G)
      _ = Nat.card A := natCard_subgroupOf_eq hAG
  have hunit : IsUnit (Fintype.card H : ZMod (p ^ e)) := by
    rw [Fintype.card_eq_nat_card, hcardH]
    apply (ZMod.isUnit_natCast_iff_not_dvd_pow hp he).2
    intro hpdvd
    exact (Nat.not_coprime_of_dvd_of_dvd hp.one_lt dvd_rfl hpdvd) hcopA
  letI : Invertible (Fintype.card H : ZMod (p ^ e)) := hunit.invertible
  let alpha : H →* A := X.pullbackActorToAmbientSubgroup A hAG
  have halpha : Function.Surjective alpha :=
    X.pullbackActorToAmbientSubgroup_surjective A hAG
  have hAnorm : A ≤ Subgroup.normalizer (V : Set E) := hAG.trans hGnorm
  let endMonoid : Monoid (Module.End (ZMod p) (Additive V)) :=
    Module.End.instMonoid
  letI : MulOne (Module.End (ZMod p) (Additive V)) := endMonoid.toMulOne
  let sigmaA : Representation (ZMod p) A (Additive V) :=
    subgroupConjugationRepresentation V A p hAnorm
  let sigma : H →* (Additive V →ₗ[ZMod p] Additive V) :=
    @MonoidHom.comp H A (Module.End (ZMod p) (Additive V))
      _ _ inferInstance sigmaA alpha
  let rho : Representation (ZMod (p ^ e)) H X.ZModModel :=
    X.actorRepresentation.comp H.subtype
  have hcardSigma :
      Nat.card {x : Additive V //
        (Representation.invariants sigma).carrier x} =
        p ^ r := by
    dsimp [sigma, sigmaA]
    rw [Representation.invariants_comp_eq_of_surjective _ _ halpha]
    calc
      Nat.card {x : Additive V //
          (Representation.invariants
            (subgroupConjugationRepresentation V A p hAnorm)).carrier x} =
          Nat.card (Additive (centralizerWithin V A)) :=
        Nat.card_congr
          (conjugationInvariantsEquivCentralizer V A p hAnorm)
      _ = Nat.card (centralizerWithin V A) := Nat.card_congr Additive.toMul
      _ = p ^ r := hcard
  let c : ZMod (p ^ e) →+* ZMod p :=
    PrimePowerCoordinateLift.residueHom (p := p) he
  have hcP : c ((p : ℕ) : ZMod (p ^ e)) = 0 := by
    rw [map_natCast]
    exact (ZMod.natCast_eq_zero_iff _ _).mpr dvd_rfl
  have hequiv : ∀ h x,
      X.quotientAdd (rho h x) = (sigma h).toFun (X.quotientAdd x) := by
    intro h x
    apply Additive.toMul.injective
    apply Subtype.ext
    exact X.quotientHom_actor (h : X.G₁) x.toMul
  have hrank : Module.finrank (ZMod (p ^ e)) rho.invariants = r := by
    apply finrank_invariants_eq_of_prime_quotient hp he rho sigma c
      X.quotientAdd
    · exact X.quotientAdd_smul_residue he
    · exact hequiv
    · exact X.quotientAdd_surjective
    · exact X.quotientAdd_eq_zero_iff_prime_smul
    · exact hcP
    · exact hcardSigma
  letI : IsLocalRing (ZMod (p ^ e)) := zmod_primePower_isLocalRing hp he
  calc
    LinearMap.trace (ZMod (p ^ e)) X.ZModModel
        (Representation.norm rho) =
        (Fintype.card H : ZMod (p ^ e)) *
          Module.finrank (ZMod (p ^ e)) rho.invariants :=
      trace_norm_eq_card_mul_finrank rho
    _ = ((Nat.card A * r : ℕ) : ZMod (p ^ e)) := by
      rw [Fintype.card_eq_nat_card, hcardH, hrank, Nat.cast_mul]

/-! ### The elementary-abelian minimal case -/

private theorem wielandt_fixpoint_of_minimal
    {E : Type u} [Group E] [Finite E]
    {ι : Type v} [Fintype ι]
    (A : ι → Subgroup E) (m n : ι → ℕ)
    (G V : Subgroup E)
    (hAG : ∀ i, A i ≤ G)
    (hmin : IsMinimalNormalUnder V G)
    (hcop : Nat.Coprime (Nat.card V) (Nat.card G))
    {p : ℕ} (hp : p.Prime)
    (hV : IsElementaryAbelianGroup p V)
    (hpart : ∀ a : E, a ∈ G →
      (∑ i with a ∈ A i, m i) = ∑ i with a ∈ A i, n i) :
    (∏ i, Nat.card (centralizerWithin V (A i)) ^
        (m i * Nat.card (A i))) =
      ∏ i, Nat.card (centralizerWithin V (A i)) ^
        (n i * Nat.card (A i)) := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  have hpV : p ∣ Nat.card V := by
    obtain ⟨d, hd⟩ := hV.isPGroup.exists_card_eq
    have hd0 : d ≠ 0 := by
      intro hd0
      rw [hd0, pow_zero] at hd
      exact (Nat.ne_of_gt (V.one_lt_card_iff_ne_bot.mpr hmin.ne_bot)) hd
    rw [hd]
    exact dvd_pow_self p hd0
  have hcopPG : Nat.Coprime p (Nat.card G) :=
    hcop.coprime_dvd_left hpV
  have hCp : ∀ i, IsPGroup p (centralizerWithin V (A i)) := by
    intro i
    let C := centralizerWithin V (A i)
    have hCV : C ≤ V := centralizerWithin_le_left V (A i)
    exact (hV.isPGroup.to_subgroup (C.subgroupOf V)).of_equiv
      (Subgroup.subgroupOfEquivOfLe hCV)
  choose r hr using fun i ↦ (hCp i).exists_card_eq
  let x : ℕ := ∑ i, r i * m i * Nat.card (A i)
  let y : ℕ := ∑ i, r i * n i * Nat.card (A i)
  let e : ℕ := max x y + 1
  have he : 0 < e := Nat.succ_pos _
  letI : Fact (1 < p ^ e) :=
    ⟨one_lt_pow₀ hp.one_lt (Nat.ne_of_gt he)⟩
  let X : IsoQuotientHomocyclicSdprod p e V G :=
    iso_quotient_homocyclic_sdprod V G p e hmin hcopPG hV he
  letI : Fintype X.G₁ := Fintype.ofFinite X.G₁
  let B : ι → Subgroup X.G₁ := fun i ↦
    X.pullbackActorSubgroup ((A i).subgroupOf G)
  have hpartX : ∀ g : X.G₁,
      (∑ i with g ∈ B i, m i) = ∑ i with g ∈ B i, n i := by
    intro g
    change (∑ i with (G.subtype (X.actorEquiv g) : E) ∈ A i, m i) =
      ∑ i with (G.subtype (X.actorEquiv g) : E) ∈ A i, n i
    exact hpart (G.subtype (X.actorEquiv g)) (X.actorEquiv g).2
  let normB : ι → Module.End (ZMod (p ^ e)) X.ZModModel := fun i ↦
    Representation.norm
      (X.actorRepresentation.comp (B i).subtype :
        Representation (ZMod (p ^ e)) (B i) X.ZModModel)
  have hnormEq :
      (∑ i, HSMul.hSMul
        (α := ZMod (p ^ e))
        (β := Module.End (ZMod (p ^ e)) X.ZModModel)
        (γ := Module.End (ZMod (p ^ e)) X.ZModModel)
        (m i : ZMod (p ^ e)) (normB i)) =
        ∑ i, HSMul.hSMul
          (α := ZMod (p ^ e))
          (β := Module.End (ZMod (p ^ e)) X.ZModModel)
          (γ := Module.End (ZMod (p ^ e)) X.ZModModel)
          (n i : ZMod (p ^ e)) (normB i) := by
    simpa only [normB] using
      weighted_norm_eq_of_membership_sums X.actorRepresentation B m n hpartX
  have htraceEq := congrArg
    (LinearMap.trace (ZMod (p ^ e)) X.ZModModel) hnormEq
  simp only [map_sum, map_smul, smul_eq_mul] at htraceEq
  have htrace (i : ι) :
      LinearMap.trace (ZMod (p ^ e)) X.ZModModel
          (normB i) =
        ((Nat.card (A i) * r i : ℕ) : ZMod (p ^ e)) := by
    have hcopA : Nat.Coprime p (Nat.card (A i)) :=
      hcopPG.coprime_dvd_right (Subgroup.card_dvd_of_le (hAG i))
    simpa [normB, B] using trace_cover_norm_eq hp he hV hmin.le_normalizer
      X (A i) (hAG i) hcopA (hr i)
  have hcast : (x : ZMod (p ^ e)) = (y : ZMod (p ^ e)) := by
    calc
      (x : ZMod (p ^ e)) =
          ∑ i, (m i : ZMod (p ^ e)) *
            ((Nat.card (A i) * r i : ℕ) : ZMod (p ^ e)) := by
        dsimp [x]
        push_cast
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = ∑ i, (n i : ZMod (p ^ e)) *
            ((Nat.card (A i) * r i : ℕ) : ZMod (p ^ e)) := by
        simpa only [htrace] using htraceEq
      _ = (y : ZMod (p ^ e)) := by
        dsimp [y]
        push_cast
        apply Finset.sum_congr rfl
        intro i _
        ring
  have hmaxlt : max x y < p ^ e := by
    dsimp [e]
    exact (Nat.lt_pow_self hp.one_lt).trans
      (Nat.pow_lt_pow_succ hp.one_lt)
  have hxlt : x < p ^ e := (le_max_left x y).trans_lt hmaxlt
  have hylt : y < p ^ e := (le_max_right x y).trans_lt hmaxlt
  have hxy : x = y := by
    have := congrArg ZMod.val hcast
    rwa [ZMod.val_natCast_of_lt hxlt, ZMod.val_natCast_of_lt hylt] at this
  calc
    (∏ i, Nat.card (centralizerWithin V (A i)) ^
        (m i * Nat.card (A i))) =
        ∏ i, p ^ (r i * (m i * Nat.card (A i))) := by
      apply Finset.prod_congr rfl
      intro i _
      rw [hr i, ← pow_mul]
    _ = p ^ x := by
      rw [Finset.prod_pow_eq_pow_sum]
      simp only [x, Nat.mul_assoc]
    _ = p ^ y := by rw [hxy]
    _ = ∏ i, p ^ (r i * (n i * Nat.card (A i))) := by
      rw [Finset.prod_pow_eq_pow_sum]
      simp only [y, Nat.mul_assoc]
    _ = ∏ i, Nat.card (centralizerWithin V (A i)) ^
        (n i * Nat.card (A i)) := by
      apply Finset.prod_congr rfl
      intro i _
      rw [hr i, ← pow_mul]

/-! ### Solvable minimal normal subgroups -/

/-- Prime-power order for a global minimal normal subgroup, assuming only
that the subgroup itself (rather than the whole ambient group) is solvable. -/
private theorem IsMinimalNormal.exists_prime_isPGroup_of_isSolvable
    {E : Type u} [Group E] [Finite E] {M : Subgroup E}
    [IsSolvable M] (hM : IsMinimalNormal M) :
    ∃ p : ℕ, p.Prime ∧ IsPGroup p M := by
  classical
  letI : M.Normal := hM.normal
  letI : IsMulCommutative M := hM.isMulCommutative_of_isSolvable
  have hcard : 1 < Nat.card M := M.one_lt_card_iff_ne_bot.mpr hM.ne_bot
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (ne_of_gt hcard)
  letI : Fact p.Prime := ⟨hp⟩
  let S : Sylow p M := Classical.choice inferInstance
  have hSnon : (S : Subgroup M) ≠ ⊥ := S.ne_bot_of_dvd_card hpdvd
  have hScore : (S : Subgroup M) ≤ pCore p M :=
    le_pCore S.isPGroup' (by infer_instance)
  have hcoreNon : pCore p M ≠ ⊥ := by
    intro hcore
    apply hSnon
    rw [hcore] at hScore
    exact le_bot_iff.mp hScore
  let K : Subgroup E := (pCore p M).map M.subtype
  have hKnormal : K.Normal := by dsimp [K]; infer_instance
  have hKle : K ≤ M := by dsimp [K]; exact Subgroup.map_subtype_le _
  have hKnon : K ≠ ⊥ := by
    dsimp [K]
    intro hK
    apply hcoreNon
    exact (Subgroup.map_eq_bot_iff_of_injective
      (pCore p M) M.subtype_injective).mp hK
  have hKM : K = M := hM.eq_of_normal_le hKnormal hKle hKnon
  refine ⟨p, hp, ?_⟩
  rw [← hKM]
  exact pCore_isPGroup.map M.subtype

/-! ### Induction through the solvable kernel -/

private def WielandtGeneratedStatement (c : ℕ) : Prop :=
  ∀ (E : Type u) [Group E] [Finite E]
    (ι : Type v) [Fintype ι]
    (A : ι → Subgroup E) (m n : ι → ℕ)
    (G V : Subgroup E),
    V.Normal → Nat.card V = c → V ⊔ G = ⊤ →
    (∀ i, A i ≤ G) →
    Nat.Coprime (Nat.card V) (Nat.card G) →
    IsSolvable V →
    (∀ a : E, a ∈ G →
      (∑ i with a ∈ A i, m i) = ∑ i with a ∈ A i, n i) →
    (∏ i, Nat.card (centralizerWithin V (A i)) ^
        (m i * Nat.card (A i))) =
      ∏ i, Nat.card (centralizerWithin V (A i)) ^
        (n i * Nat.card (A i))

private def WielandtGeneralStatement (c : ℕ) : Prop :=
  ∀ (E : Type u) [Group E] [Finite E]
    (ι : Type v) [Fintype ι]
    (A : ι → Subgroup E) (m n : ι → ℕ)
    (G V : Subgroup E),
    Nat.card V = c →
    (∀ i, A i ≤ G) →
    G ≤ Subgroup.normalizer (V : Set E) →
    Nat.Coprime (Nat.card V) (Nat.card G) →
    IsSolvable V →
    (∀ a : E, a ∈ G →
      (∑ i with a ∈ A i, m i) = ∑ i with a ∈ A i, n i) →
    (∏ i, Nat.card (centralizerWithin V (A i)) ^
        (m i * Nat.card (A i))) =
      ∏ i, Nat.card (centralizerWithin V (A i)) ^
        (n i * Nat.card (A i))

/-- Restrict the ambient group to `V ⊔ G`, turning normalization into a
global normality hypothesis. -/
private theorem wielandtGeneral_of_generated
    {c : ℕ} (hgen : WielandtGeneratedStatement.{u, v} c) :
    WielandtGeneralStatement.{u, v} c := by
  set_option maxHeartbeats 1000000 in
  intro E _ _ ι _ A m n G V hcard hAG hGV hcop hsol hpart
  letI : IsSolvable V := hsol
  let J : Subgroup E := V ⊔ G
  let VJ : Subgroup J := V.subgroupOf J
  let GJ : Subgroup J := G.subgroupOf J
  let AJ : ι → Subgroup J := fun i ↦ (A i).subgroupOf J
  have hVJnormal : VJ.Normal := by
    dsimp [VJ, J]
    have hnormal : (V.subgroupOf (G ⊔ V)).Normal :=
      Subgroup.normal_subgroupOf_sup_of_le_normalizer hGV
    rw [sup_comm G V] at hnormal
    exact hnormal
  have hcardVJ : Nat.card VJ = c := by
    rw [natCard_subgroupOf_eq (show V ≤ J from le_sup_left)]
    exact hcard
  have hgenJ : VJ ⊔ GJ = ⊤ := by
    change V.subgroupOf J ⊔ G.subgroupOf J = ⊤
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right]
    exact Subgroup.subgroupOf_self J
  have hAJGJ : ∀ i, AJ i ≤ GJ := by
    intro i
    exact Subgroup.subgroupOf_mono J (hAG i)
  have hcopJ : Nat.Coprime (Nat.card VJ) (Nat.card GJ) := by
    simpa [VJ, GJ, J, natCard_subgroupOf_eq le_sup_left,
      natCard_subgroupOf_eq le_sup_right] using hcop
  have hsolJ : IsSolvable VJ :=
    solvable_of_solvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe
        (show V ≤ J from le_sup_left)).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe
        (show V ≤ J from le_sup_left)).injective
  have hpartJ : ∀ a : J, a ∈ GJ →
      (∑ i with a ∈ AJ i, m i) = ∑ i with a ∈ AJ i, n i := by
    intro a ha
    change (∑ i with (a : E) ∈ A i, m i) =
      ∑ i with (a : E) ∈ A i, n i
    exact hpart (a : E) ha
  have hresult := hgen J ι AJ m n GJ VJ hVJnormal hcardVJ hgenJ
    hAJGJ hcopJ hsolJ hpartJ
  simpa only [AJ, VJ, GJ,
    natCard_centralizerWithin_subgroupOf
      (show V ≤ J from le_sup_left)
      (hAG _ |>.trans (show G ≤ J from le_sup_right)),
    natCard_subgroupOf_eq
      (hAG _ |>.trans (show G ≤ J from le_sup_right))] using hresult

/-! The recursive generated statement follows below. -/

private theorem wielandtGeneratedStatement_all (c : ℕ) :
    WielandtGeneratedStatement.{u, v} c := by
  set_option maxHeartbeats 1000000 in
  induction c using Nat.strong_induction_on with
  | h c ih =>
    intro E _ _ ι _ A m n G V hVnormal hcard hgen hAG hcop hsol hpart
    classical
    letI : V.Normal := hVnormal
    letI : IsSolvable V := hsol
    by_cases hVbot : V = ⊥
    · subst V
      simp [centralizerWithin]
    · obtain ⟨B, hBmin, hBV⟩ := exists_minimalNormal_le hVnormal hVbot
      letI : B.Normal := hBmin.normal
      have hBsol : IsSolvable B :=
        solvable_of_solvable_injective
          (f := Subgroup.inclusion hBV)
          (Subgroup.inclusion_injective hBV)
      letI : IsSolvable B := hBsol
      by_cases hBVeq : B = V
      · subst B
        obtain ⟨p, hp, hVp⟩ :=
          hBmin.exists_prime_isPGroup_of_isSolvable
        letI : Fact p.Prime := ⟨hp⟩
        have hVabel := hBmin.isElementaryAbelian_of_isPGroup hVp
        letI : IsMulCommutative V := hVabel.1
        let hElem : IsElementaryAbelianGroup p V :=
          ⟨hVp, hVabel.1, hVabel.2⟩
        have hminG : IsMinimalNormalUnder V G := by
          refine ⟨hBmin.ne_bot, Subgroup.le_normalizer_of_normal, ?_⟩
          intro D hDV hD hDinv
          have hVD : V ≤ Subgroup.normalizer (D : Set E) := by
            rw [Subgroup.le_normalizer_iff]
            intro x hx d hd
            have hcomm : x * d = d * x := by
              exact congrArg Subtype.val
                (mul_comm (⟨x, hx⟩ : V) (⟨d, hDV hd⟩ : V))
            have heq : x * d * x⁻¹ = d := by
              calc
                x * d * x⁻¹ = d * x * x⁻¹ := by rw [hcomm]
                _ = d := by simp
            rw [heq]
            exact hd
          have hGD : G ≤ Subgroup.normalizer (D : Set E) :=
            Subgroup.le_normalizer_iff.mpr hDinv
          have hDtop : Subgroup.normalizer (D : Set E) = ⊤ := by
            apply top_unique
            rw [← hgen]
            exact sup_le hVD hGD
          have hDnormal : D.Normal :=
            Subgroup.normalizer_eq_top_iff.mp hDtop
          exact (hBmin.eq_of_normal_le hDnormal hDV hD).ge
        exact wielandt_fixpoint_of_minimal A m n G V hAG hminG hcop
          hp hElem hpart
      · have hBltV : B < V := lt_of_le_of_ne hBV hBVeq
        have hBlt : Nat.card B < c := by
          rw [← hcard]
          exact natCard_subgroup_lt_of_lt hBltV
        have hcopBG : Nat.Coprime (Nat.card B) (Nat.card G) :=
          hcop.coprime_dvd_left (Subgroup.card_dvd_of_le hBV)
        have hrecB :
            (∏ i, Nat.card (centralizerWithin B (A i)) ^
                (m i * Nat.card (A i))) =
              ∏ i, Nat.card (centralizerWithin B (A i)) ^
                (n i * Nat.card (A i)) :=
          (wielandtGeneral_of_generated (ih (Nat.card B) hBlt))
            E ι A m n G B rfl hAG Subgroup.le_normalizer_of_normal
              hcopBG hBsol hpart

        let q : E →* E ⧸ B := QuotientGroup.mk' B
        let Aq : ι → Subgroup (E ⧸ B) := fun i ↦ (A i).map q
        let Gq : Subgroup (E ⧸ B) := G.map q
        let Vq : Subgroup (E ⧸ B) := V.map q
        letI : Vq.Normal :=
          Subgroup.Normal.map hVnormal q (QuotientGroup.mk'_surjective B)
        have hAGq : ∀ i, Aq i ≤ Gq := fun i ↦
          Subgroup.map_mono (hAG i)
        have hcopq : Nat.Coprime (Nat.card Vq) (Nat.card Gq) :=
          (hcop.coprime_dvd_left (Subgroup.card_map_dvd V q)).coprime_dvd_right
            (Subgroup.card_map_dvd G q)
        have hsolq : IsSolvable Vq :=
          solvable_of_surjective (f := q.subgroupMap V)
            (q.subgroupMap_surjective V)
        have hdisBG : Disjoint B G :=
          Subgroup.disjoint_of_coprime_natCard hcopBG
        have hqAinj (i : ι) : Function.Injective (q.subgroupMap (A i)) := by
          rw [← MonoidHom.ker_eq_bot_iff, Subgroup.ker_subgroupMap,
            show q.ker = B by exact QuotientGroup.ker_mk' B,
            Subgroup.subgroupOf_eq_bot]
          exact hdisBG.mono_right (hAG i)
        have hcardAq (i : ι) : Nat.card (Aq i) = Nat.card (A i) := by
          let eAq : A i ≃* Aq i :=
            MulEquiv.ofBijective (q.subgroupMap (A i))
              ⟨hqAinj i, q.subgroupMap_surjective (A i)⟩
          exact (Nat.card_congr eAq.toEquiv).symm
        have hpartq : ∀ a : E ⧸ B, a ∈ Gq →
            (∑ i with a ∈ Aq i, m i) = ∑ i with a ∈ Aq i, n i := by
          rintro a ⟨g, hg, rfl⟩
          have hmem (i : ι) : q g ∈ Aq i ↔ g ∈ A i := by
            exact mem_map_quotient_iff_of_le_of_coprime
              (hAG i) hcopBG ⟨g, hg⟩
          simpa only [hmem] using hpart g hg
        have hVqlt : Nat.card Vq < c := by
          rw [← hcard]
          exact natCard_map_quotient_lt_of_ne_bot_of_le hBV hBmin.ne_bot
        have hrecq :
            (∏ i, Nat.card (centralizerWithin Vq (Aq i)) ^
                (m i * Nat.card (Aq i))) =
              ∏ i, Nat.card (centralizerWithin Vq (Aq i)) ^
                (n i * Nat.card (Aq i)) :=
          (wielandtGeneral_of_generated (ih (Nat.card Vq) hVqlt))
            (E ⧸ B) ι Aq m n Gq Vq rfl hAGq
              Subgroup.le_normalizer_of_normal hcopq hsolq hpartq
        have hcopBA (i : ι) :
            Nat.Coprime (Nat.card B) (Nat.card (A i)) :=
          hcopBG.coprime_dvd_right (Subgroup.card_dvd_of_le (hAG i))
        have hfactor (w : ι → ℕ) :
            (∏ i, Nat.card (centralizerWithin V (A i)) ^
                (w i * Nat.card (A i))) =
              (∏ i, Nat.card (centralizerWithin B (A i)) ^
                  (w i * Nat.card (A i))) *
                ∏ i, Nat.card (centralizerWithin Vq (Aq i)) ^
                  (w i * Nat.card (Aq i)) := by
          rw [← Finset.prod_mul_distrib]
          apply Finset.prod_congr rfl
          intro i _
          rw [hcardAq i, ← mul_pow]
          exact congrArg (fun z : ℕ ↦ z ^ (w i * Nat.card (A i)))
            (natCard_centralizerWithin_eq_mul_quotient hBV (hcopBA i))
        rw [hfactor m, hfactor n, hrecB, hrecq]

private theorem solvable_Wielandt_fixpoint_all_subgroups
    {T : Type u} [Group T] [Finite T]
    {ι : Type v} [Fintype ι]
    (A : ι → Subgroup T) (m n : ι → ℕ)
    (G V : Subgroup T)
    (hAG : ∀ i, A i ≤ G)
    (hGV : G ≤ Subgroup.normalizer (V : Set T))
    (hcop : Nat.Coprime (Nat.card V) (Nat.card G))
    (hsol : IsSolvable V)
    (hpart : ∀ a : T, a ∈ G →
      (∑ i with a ∈ A i, m i) = ∑ i with a ∈ A i, n i) :
    (∏ i, Nat.card (centralizerWithin V (A i)) ^
        (m i * Nat.card (A i))) =
      ∏ i, Nat.card (centralizerWithin V (A i)) ^
        (n i * Nat.card (A i)) := by
  exact (wielandtGeneral_of_generated
    (wielandtGeneratedStatement_all (Nat.card V)))
      T ι A m n G V rfl hAG hGV hcop hsol hpart

/-! ### The solvable Wielandt fixed-point theorem -/

/-- The final fixed-point product identity from `wielandt_fixpoint.v`.

Only subgroups carrying a nonzero weight need to lie in the acting subgroup;
the proof discards the zero-weight terms before applying the induction above.
-/
theorem solvable_Wielandt_fixpoint
    {T : Type u} [Group T] [Finite T]
    {ι : Type v} [Fintype ι]
    (A : ι → Subgroup T) (m n : ι → ℕ)
    (G V : Subgroup T)
    (hAG : ∀ i, 0 < m i + n i → A i ≤ G)
    (hGV : G ≤ Subgroup.normalizer (V : Set T))
    (hcop : Nat.Coprime (Nat.card V) (Nat.card G))
    (hsol : IsSolvable V)
    (hpart : ∀ a : T, a ∈ G →
      (∑ i with a ∈ A i, m i) = ∑ i with a ∈ A i, n i) :
    (∏ i, Nat.card (centralizerWithin V (A i)) ^
        (m i * Nat.card (A i))) =
      ∏ i, Nat.card (centralizerWithin V (A i)) ^
        (n i * Nat.card (A i)) := by
  classical
  let A' : ι → Subgroup T := fun i ↦
    if 0 < m i + n i then A i else ⊥
  have hA'G (i : ι) : A' i ≤ G := by
    by_cases hi : 0 < m i + n i
    · change (if 0 < m i + n i then A i else ⊥) ≤ G
      rw [if_pos hi]
      exact hAG i hi
    · change (if 0 < m i + n i then A i else ⊥) ≤ G
      rw [if_neg hi]
      exact bot_le
  have hA'A (i : ι) : A' i ≤ A i := by
    by_cases hi : 0 < m i + n i
    · change (if 0 < m i + n i then A i else ⊥) ≤ A i
      rw [if_pos hi]
    · change (if 0 < m i + n i then A i else ⊥) ≤ A i
      rw [if_neg hi]
      exact bot_le
  have hzero (i : ι) (hi : ¬ 0 < m i + n i) :
      m i = 0 ∧ n i = 0 :=
    Nat.add_eq_zero.mp (Nat.eq_zero_of_not_pos hi)
  have hsum (w : ι → ℕ)
      (hw : ∀ i, ¬ 0 < m i + n i → w i = 0) (a : T) :
      (∑ i with a ∈ A' i, w i) = ∑ i with a ∈ A i, w i := by
    apply Finset.sum_subset
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      exact hA'A i hi
    · intro i hiA hiA'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hiA hiA'
      apply hw i
      intro hi
      apply hiA'
      change a ∈ if 0 < m i + n i then A i else ⊥
      rw [if_pos hi]
      exact hiA
  have hpart' : ∀ a : T, a ∈ G →
      (∑ i with a ∈ A' i, m i) = ∑ i with a ∈ A' i, n i := by
    intro a ha
    rw [hsum m (fun i hi ↦ (hzero i hi).1) a,
      hsum n (fun i hi ↦ (hzero i hi).2) a]
    exact hpart a ha
  have hresult := solvable_Wielandt_fixpoint_all_subgroups
    A' m n G V hA'G hGV hcop hsol hpart'
  have hprod (w : ι → ℕ)
      (hw : ∀ i, ¬ 0 < m i + n i → w i = 0) :
      (∏ i, Nat.card (centralizerWithin V (A' i)) ^
          (w i * Nat.card (A' i))) =
        ∏ i, Nat.card (centralizerWithin V (A i)) ^
          (w i * Nat.card (A i)) := by
    apply Finset.prod_congr rfl
    intro i _
    by_cases hi : 0 < m i + n i
    · have hAi : A' i = A i := by
        change (if 0 < m i + n i then A i else ⊥) = A i
        rw [if_pos hi]
      rw [hAi]
    · rw [hw i hi]
      simp
  rw [hprod m (fun i hi ↦ (hzero i hi).1),
    hprod n (fun i hi ↦ (hzero i hi).2)] at hresult
  exact hresult

/-! ### The Frobenius--Wielandt specialization -/

open Submission.OddOrder.BG.Section03

/-- Centralizers commute with transport by an ambient group equivalence. -/
private theorem centralizerWithin_map_mulEquiv_wielandt
    {T : Type*} [Group T] (D A : Subgroup T) (e : T ≃* T) :
    (centralizerWithin D A).map e.toMonoidHom =
      centralizerWithin (D.map e.toMonoidHom) (A.map e.toMonoidHom) := by
  ext y
  rw [Subgroup.mem_map_equiv]
  constructor
  · intro hy
    refine ⟨Subgroup.mem_map_equiv.mpr hy.1, ?_⟩
    intro a ha
    have ha' : e.symm a ∈ A := Subgroup.mem_map_equiv.mp ha
    simpa using congrArg e (hy.2 (e.symm a) ha')
  · intro hy
    refine ⟨Subgroup.mem_map_equiv.mp hy.1, ?_⟩
    intro a ha
    have ha' : e a ∈ A.map e.toMonoidHom :=
      Subgroup.mem_map_equiv.mpr (by simpa using ha)
    simpa using congrArg e.symm (hy.2 (e a) ha')

/-- `BGsection3.v: Frobenius_Wielandt_fixpoint`.

The source theorem is stated for a Frobenius kernel and complement acting
coprimely on a solvable normalized subgroup.  The Frobenius decomposition is
formed in `K ⊔ R`; this avoids requiring irrelevant ambient-membership
hypotheses when the theorem is applied to subgroups of a larger group. -/
theorem Frobenius_Wielandt_fixpoint
    {T : Type u} [Group T] [Finite T]
    {K R M : Subgroup T}
    (hFrob : IsFrobeniusDecomposition
      (K.subgroupOf (K ⊔ R)) (R.subgroupOf (K ⊔ R)))
    (hNorm : K ⊔ R ≤ Subgroup.normalizer (M : Set T))
    (hcop : Nat.Coprime (Nat.card M) (Nat.card ↥(K ⊔ R)))
    (hsol : IsSolvable M) :
    Nat.card (centralizerWithin M (K ⊔ R)) ^ Nat.card R * Nat.card M =
          Nat.card (centralizerWithin M R) ^ Nat.card R *
            Nat.card (centralizerWithin M K) ∧
      (centralizerWithin M R = ⊥ →
        K ≤ Subgroup.centralizer (M : Set T)) ∧
      (centralizerWithin M K = ⊥ →
        Nat.card M = Nat.card (centralizerWithin M R) ^ Nat.card R) := by
  classical
  letI : Fintype T := Fintype.ofFinite T
  let J : Subgroup T := K ⊔ R
  let KJ : Subgroup J := K.subgroupOf J
  let RJ : Subgroup J := R.subgroupOf J
  have hFrobJ : IsFrobeniusDecomposition KJ RJ := by
    simpa [J, KJ, RJ] using hFrob
  let conjR : KJ → Subgroup T := fun x ↦
    R.map (MulAut.conj (((x : J) : T))).toMonoidHom
  let ι := Unit ⊕ (Unit ⊕ (Unit ⊕ KJ))
  let A : ι → Subgroup T
    | Sum.inl _ => J
    | Sum.inr (Sum.inl _) => ⊥
    | Sum.inr (Sum.inr (Sum.inl _)) => K
    | Sum.inr (Sum.inr (Sum.inr x)) => conjR x
  let m : ι → ℕ
    | Sum.inl _ => 1
    | Sum.inr (Sum.inl _) => Nat.card KJ
    | _ => 0
  let n : ι → ℕ
    | Sum.inr (Sum.inr (Sum.inl _)) => 1
    | Sum.inr (Sum.inr (Sum.inr _)) => 1
    | _ => 0

  have hAJ (i : ι) : A i ≤ J := by
    rcases i with (_ | (_ | (_ | x)))
    · exact le_rfl
    · exact bot_le
    · exact le_sup_left
    · rintro y ⟨r, hr, rfl⟩
      have hrJ : r ∈ J := by
        change r ∈ K ⊔ R
        exact (le_sup_right : R ≤ K ⊔ R) hr
      exact J.mul_mem (J.mul_mem (x : J).property hrJ)
        (J.inv_mem (x : J).property)

  have sum_indicator_of_injective
      {X : Type u} [Fintype X] (f : X → J)
      (hf : Function.Injective f) (a : J) :
      (∑ x : X, if f x = a then 1 else 0) =
        if a ∈ Set.range f then 1 else 0 := by
    by_cases ha : a ∈ Set.range f
    · obtain ⟨x, rfl⟩ := ha
      rw [if_pos ⟨x, rfl⟩]
      simp [hf.eq_iff]
    · rw [if_neg ha]
      apply Finset.sum_eq_zero
      intro x _
      rw [if_neg]
      exact fun hx ↦ ha ⟨x, hx⟩

  have hpart : ∀ a : T, a ∈ J →
      (∑ i with a ∈ A i, m i) = ∑ i with a ∈ A i, n i := by
    intro a ha
    let aJ : J := ⟨a, ha⟩
    let f : J → ℕ := fun y ↦ if y = aJ then 1 else 0
    have hsumJ : (∑ y : J, f y) = 1 := by
      simpa [f] using
        (sum_indicator_of_injective (fun y : J ↦ y)
          Function.injective_id aJ)
    have hRangeK :
        aJ ∈ Set.range (fun x : KJ ↦ (x : J)) ↔ a ∈ K := by
      constructor
      · rintro ⟨x, hx⟩
        have hxK : ((x : J) : T) ∈ K := x.property
        have hxT : ((x : J) : T) = a :=
          congrArg (fun y : J ↦ (y : T)) hx
        rw [hxT] at hxK
        exact hxK
      · intro haK
        exact ⟨⟨aJ, haK⟩, rfl⟩
    have hsumK : (∑ x : KJ, f (x : J)) =
        if a ∈ K then 1 else 0 := by
      have hs := sum_indicator_of_injective
        (fun x : KJ ↦ (x : J)) Subtype.val_injective aJ
      simp only [hRangeK] at hs
      simpa only [f] using hs
    have hRangeR (x : KJ) :
        aJ ∈ Set.range
            (fun r : RJ ↦ (x : J) * (r : J) * (x : J)⁻¹) ↔
          a ∈ conjR x := by
      constructor
      · rintro ⟨r, hr⟩
        refine ⟨((r : J) : T), r.property, ?_⟩
        exact congrArg Subtype.val hr
      · rintro ⟨r, hrR, hr⟩
        have hrJ : r ∈ J := by
          change r ∈ K ⊔ R
          exact (le_sup_right : R ≤ K ⊔ R) hrR
        let rJ : RJ := ⟨⟨r, hrJ⟩, hrR⟩
        refine ⟨rJ, Subtype.ext ?_⟩
        exact hr
    have hsumR (x : KJ) :
        (∑ r : RJ, f ((x : J) * (r : J) * (x : J)⁻¹)) =
          if a ∈ conjR x then 1 else 0 := by
      have hinj : Function.Injective
          (fun r : RJ ↦ (x : J) * (r : J) * (x : J)⁻¹) := by
        intro r s hrs
        apply Subtype.ext
        have hrs' := congrArg
          (fun y : J ↦ (x : J)⁻¹ * y * (x : J)) hrs
        simpa [mul_assoc] using hrs'
      simpa [f, hRangeR x] using
        (sum_indicator_of_injective
          (fun r : RJ ↦ (x : J) * (r : J) * (x : J)⁻¹)
          hinj aJ)
    have hp := hFrobJ.sum_add_card_nsmul_one_eq_kernel_add_conjugates f
    rw [hsumJ, hsumK] at hp
    simp_rw [hsumR] at hp
    have hm : (∑ i with a ∈ A i, m i) =
        1 + if a = 1 then Nat.card KJ else 0 := by
      rw [Finset.sum_filter]
      simp [ι, A, m, ha]
    have hn : (∑ i with a ∈ A i, n i) =
        (if a ∈ K then 1 else 0) +
          ∑ x : KJ, if a ∈ conjR x then 1 else 0 := by
      rw [Finset.sum_filter]
      simp [ι, A, n]
    rw [hm, hn]
    have hone : (1 : J) = aJ ↔ a = 1 := by
      constructor
      · intro h
        exact (congrArg (fun y : J ↦ (y : T)) h).symm
      · intro h
        apply Subtype.ext
        exact h.symm
    simpa [f, hone, Nat.card_eq_fintype_card, nsmul_eq_mul] using hp

  have hresult := solvable_Wielandt_fixpoint
    A m n J M (fun i _ ↦ hAJ i) hNorm hcop hsol hpart

  have hMconj (x : KJ) :
      M.map (MulAut.conj (((x : J) : T))).toMonoidHom = M :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hNorm ((x : J).property))
  have hcardConjR (x : KJ) : Nat.card (conjR x) = Nat.card R := by
    exact Subgroup.card_map_of_injective
      (MulAut.conj (((x : J) : T))).injective
  have hcardCentConjR (x : KJ) :
      Nat.card (centralizerWithin M (conjR x)) =
        Nat.card (centralizerWithin M R) := by
    let e : T ≃* T := MulAut.conj (((x : J) : T))
    have hmap := centralizerWithin_map_mulEquiv_wielandt M R e
    rw [hMconj x] at hmap
    calc
      Nat.card (centralizerWithin M (conjR x)) =
          Nat.card ((centralizerWithin M R).map e.toMonoidHom) := by
            rw [hmap]
      _ = Nat.card (centralizerWithin M R) :=
        Subgroup.card_map_of_injective e.injective
  have hcardKJ : Nat.card KJ = Nat.card K :=
    natCard_subgroupOf_eq le_sup_left
  have hcardRJ : Nat.card RJ = Nat.card R :=
    natCard_subgroupOf_eq le_sup_right
  have hcardJ : Nat.card J = Nat.card R * Nat.card K := by
    rw [← hcardKJ, ← hcardRJ]
    simpa [mul_comm] using hFrobJ.card_mul_card.symm
  have hcentBot : centralizerWithin M (⊥ : Subgroup T) = M := by
    apply le_antisymm (centralizerWithin_le_left M ⊥)
    intro x hx
    refine mem_centralizerWithin.mpr ⟨hx, ?_⟩
    intro y hy
    rw [Subgroup.mem_bot.mp hy]
    simp
  have hleft :
      (∏ i, Nat.card (centralizerWithin M (A i)) ^
          (m i * Nat.card (A i))) =
        Nat.card (centralizerWithin M J) ^ Nat.card J *
          Nat.card M ^ Nat.card KJ := by
    simp [ι, A, m, hcentBot, mul_comm, mul_left_comm, mul_assoc]
  have hprodConjR :
      (∏ x : KJ, Nat.card (centralizerWithin M (conjR x)) ^
          Nat.card (conjR x)) =
        (Nat.card (centralizerWithin M R) ^ Nat.card R) ^
          Nat.card KJ := by
    simp_rw [hcardConjR, hcardCentConjR]
    simp [Nat.card_eq_fintype_card]
  have hright :
      (∏ i, Nat.card (centralizerWithin M (A i)) ^
          (n i * Nat.card (A i))) =
        Nat.card (centralizerWithin M K) ^ Nat.card K *
          (Nat.card (centralizerWithin M R) ^ Nat.card R) ^
            Nat.card KJ := by
    calc
      _ = Nat.card (centralizerWithin M K) ^ Nat.card K *
          (∏ x : KJ, Nat.card (centralizerWithin M (conjR x)) ^
            Nat.card (conjR x)) := by
              simp [ι, A, n]
      _ = _ := by rw [hprodConjR]
  rw [hleft, hright] at hresult
  have hidentity :
      Nat.card (centralizerWithin M J) ^ Nat.card R * Nat.card M =
        Nat.card (centralizerWithin M R) ^ Nat.card R *
          Nat.card (centralizerWithin M K) := by
    rw [hcardJ, hcardKJ] at hresult
    have hresult' :
        Nat.card (centralizerWithin M J) ^
              (Nat.card R * Nat.card K) * Nat.card M ^ Nat.card K =
            (Nat.card (centralizerWithin M R) ^ Nat.card R) ^
                Nat.card K *
              Nat.card (centralizerWithin M K) ^ Nat.card K := by
      calc
        _ = Nat.card (centralizerWithin M K) ^ Nat.card K *
              (Nat.card (centralizerWithin M R) ^ Nat.card R) ^
                Nat.card K := hresult
        _ = _ := Nat.mul_comm _ _
    apply Nat.pow_left_injective (Nat.card_pos (α := K)).ne'
    simpa only [mul_pow, pow_mul] using hresult'
  refine ⟨hidentity, ?_, ?_⟩
  · intro hCR
    have hCG : centralizerWithin M J = ⊥ := by
      apply le_antisymm _ bot_le
      exact (centralizerWithin_antitone_right le_sup_right).trans_eq hCR
    have hcard : Nat.card M = Nat.card (centralizerWithin M K) := by
      simpa [hCR, hCG] using hidentity
    have hCK : centralizerWithin M K = M :=
      Subgroup.eq_of_le_of_card_ge (centralizerWithin_le_left M K)
        hcard.symm.ge
    rw [Subgroup.le_centralizer_iff]
    intro x hx
    exact (mem_centralizerWithin.mp (hCK.symm ▸ hx)).2
  · intro hCK
    have hCG : centralizerWithin M J = ⊥ := by
      apply le_antisymm _ bot_le
      exact (centralizerWithin_antitone_right le_sup_left).trans_eq hCK
    simpa [hCK, hCG] using hidentity

end Submission.OddOrder.MathlibSupport
