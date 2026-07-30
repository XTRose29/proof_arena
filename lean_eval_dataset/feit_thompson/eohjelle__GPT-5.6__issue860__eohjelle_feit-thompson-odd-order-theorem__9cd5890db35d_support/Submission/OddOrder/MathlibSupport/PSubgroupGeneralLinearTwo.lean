import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.GroupTheory.PGroup
import Mathlib.RepresentationTheory.Basic

/-!
The `p`-part of the two-dimensional general linear group in characteristic
`p`.  This is the cardinal estimate used in Bender--Glauberman Proposition
4.8(a): a `p`-subgroup of `GL₂(p)` has order at most `p`.
-/

namespace Submission.OddOrder.MathlibSupport

/-- The only factor of `p` in the order
`(p² - 1) * (p² - p)` of `GL₂(p)` is the displayed factor `p`. -/
theorem prime_pow_dvd_card_GL_two_factor_le_one
    {p n : ℕ} (hp : p.Prime)
    (hdvd : p ^ n ∣ (p ^ 2 - 1) * (p ^ 2 - p)) :
    n ≤ 1 := by
  have hpPow : p ∣ p ^ 2 := dvd_pow_self p (by decide : (2 : ℕ) ≠ 0)
  have hnot₁ : ¬ p ∣ p ^ 2 - 1 := by
    intro h
    have hd := Nat.dvd_sub hpPow h
    have hone : p ^ 2 - (p ^ 2 - 1) = 1 := by
      have : 1 ≤ p ^ 2 := one_le_pow₀ hp.pos
      omega
    rw [hone] at hd
    exact hp.not_dvd_one hd
  have hnot₂ : ¬ p ∣ p - 1 := by
    intro h
    have hd := Nat.dvd_sub (dvd_refl p) h
    have hone : p - (p - 1) = 1 := by
      have : 1 ≤ p := hp.pos
      omega
    rw [hone] at hd
    exact hp.not_dvd_one hd
  have hcop : (p ^ n).Coprime ((p ^ 2 - 1) * (p - 1)) :=
    ((hp.coprime_iff_not_dvd.mpr hnot₁).mul_right
      (hp.coprime_iff_not_dvd.mpr hnot₂)).pow_left n
  have hfactor :
      (p ^ 2 - 1) * (p ^ 2 - p) =
        p * ((p ^ 2 - 1) * (p - 1)) := by
    have hsecond : p ^ 2 - p = p * (p - 1) := by
      rw [Nat.mul_sub_left_distrib, pow_two, mul_one]
    rw [hsecond]
    ac_rfl
  have hpowDvdP : p ^ n ∣ p := by
    apply hcop.dvd_of_dvd_mul_right
    rwa [hfactor] at hdvd
  have hpowLe : p ^ n ≤ p ^ 1 := by
    simpa using Nat.le_of_dvd hp.pos hpowDvdP
  exact (Nat.pow_le_pow_iff_right hp.one_lt).mp hpowLe

/-- Every `p`-subgroup of `GL₂(ZMod p)` has cardinality at most `p`. -/
theorem natCard_le_prime_of_isPGroup_subgroup_GL_two
    {p : ℕ} [Fact p.Prime]
    (P : Subgroup (GL (Fin 2) (ZMod p)))
    (hP : IsPGroup p P) :
    Nat.card P ≤ p := by
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have hcardGL :
      Nat.card (GL (Fin 2) (ZMod p)) =
        (p ^ 2 - 1) * (p ^ 2 - p) := by
    have h := Matrix.card_GL_field (𝔽 := ZMod p) 2
    simpa [Fin.prod_univ_succ] using h
  have hdvd : p ^ n ∣ (p ^ 2 - 1) * (p ^ 2 - p) := by
    rw [← hcardGL, ← hn]
    exact P.card_subgroup_dvd_card
  have hnle : n ≤ 1 :=
    prime_pow_dvd_card_GL_two_factor_le_one Fact.out hdvd
  calc
    Nat.card P = p ^ n := hn
    _ ≤ p ^ 1 := Nat.pow_le_pow_right (Fact.out : p.Prime).pos hnle
    _ = p := pow_one p

/-- Uniform version in dimensions at most two. -/
theorem natCard_le_prime_of_isPGroup_subgroup_GL_fin_le_two
    {p m : ℕ} [Fact p.Prime] (hm : m ≤ 2)
    (P : Subgroup (GL (Fin m) (ZMod p)))
    (hP : IsPGroup p P) :
    Nat.card P ≤ p := by
  have hmCases : m = 0 ∨ m = 1 ∨ m = 2 := by omega
  rcases hmCases with rfl | rfl | rfl
  · have hcard : Nat.card (GL (Fin 0) (ZMod p)) = 1 := by
      simpa using (Matrix.card_GL_field (𝔽 := ZMod p) 0)
    calc
      Nat.card P ≤ Nat.card (GL (Fin 0) (ZMod p)) :=
        Nat.le_of_dvd (Nat.card_pos (α := GL (Fin 0) (ZMod p)))
          P.card_subgroup_dvd_card
      _ = 1 := hcard
      _ ≤ p := (Fact.out : p.Prime).pos
  · have hcard : Nat.card (GL (Fin 1) (ZMod p)) = p - 1 := by
      simpa [Fin.prod_univ_succ] using
        (Matrix.card_GL_field (𝔽 := ZMod p) 1)
    calc
      Nat.card P ≤ Nat.card (GL (Fin 1) (ZMod p)) :=
        Nat.le_of_dvd (Nat.card_pos (α := GL (Fin 1) (ZMod p)))
          P.card_subgroup_dvd_card
      _ = p - 1 := hcard
      _ ≤ p := Nat.sub_le p 1
  · exact natCard_le_prime_of_isPGroup_subgroup_GL_two P hP

/-- A finite `p`-group acting faithfully on a vector space of dimension at
most two over `ZMod p` has order at most `p`.

This is the representation-theoretic form of the estimate used for the
quotient by a self-centralizing elementary abelian subgroup. -/
theorem natCard_le_prime_of_isPGroup_of_faithful_representation_finrank_le_two
    {p : ℕ} [Fact p.Prime]
    {Q V : Type*} [Group Q]
    [AddCommGroup V] [Finite V] [Module (ZMod p) V]
    (hQ : IsPGroup p Q) (rho : Representation (ZMod p) Q V)
    (hrho : Function.Injective rho)
    (hdim : Module.finrank (ZMod p) V ≤ 2) :
    Nat.card Q ≤ p := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  letI : Module.Finite (ZMod p) V := by infer_instance
  let n := Module.finrank (ZMod p) V
  let b : Module.Basis (Fin n) (ZMod p) V :=
    Module.finBasisOfFinrankEq (ZMod p) V rfl
  let e : GL (Fin n) (ZMod p) ≃* LinearMap.GeneralLinearGroup (ZMod p) V :=
    Matrix.GeneralLinearGroup.toLin' b
  let rhoGL : Q →* GL (Fin n) (ZMod p) :=
    e.symm.toMonoidHom.comp rho.asGroupHom
  have hrhoGL : Function.Injective rhoGL := by
    intro x y hxy
    apply hrho
    have hxy' : rho.asGroupHom x = rho.asGroupHom y := by
      exact e.symm.injective hxy
    exact Units.ext_iff.mp hxy'
  let P : Subgroup (GL (Fin n) (ZMod p)) := rhoGL.range
  have hP : IsPGroup p P := by
    change IsPGroup p rhoGL.range
    rw [rhoGL.range_eq_map]
    exact (hQ.to_subgroup (⊤ : Subgroup Q)).map rhoGL
  have hPcard : Nat.card P = Nat.card Q := by
    symm
    exact Nat.card_congr (Equiv.ofInjective rhoGL hrhoGL)
  calc
    Nat.card Q = Nat.card P := hPcard.symm
    _ ≤ p := natCard_le_prime_of_isPGroup_subgroup_GL_fin_le_two hdim P hP

/-- Cardinal form of the faithful two-dimensional representation estimate.
It is convenient when the module comes from a finite elementary abelian
group whose order has already been bounded. -/
theorem natCard_le_prime_of_isPGroup_of_faithful_representation_card_le_sq
    {p : ℕ} [Fact p.Prime]
    {Q V : Type*} [Group Q]
    [AddCommGroup V] [Finite V] [Module (ZMod p) V]
    (hQ : IsPGroup p Q) (rho : Representation (ZMod p) Q V)
    (hrho : Function.Injective rho)
    (hVcard : Nat.card V ≤ p ^ 2) :
    Nat.card Q ≤ p := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  letI : Module.Finite (ZMod p) V := by infer_instance
  have hcard : Nat.card V = p ^ Module.finrank (ZMod p) V := by
    simpa only [Nat.card_zmod] using
      (Module.natCard_eq_pow_finrank (K := ZMod p) (V := V))
  have hdim : Module.finrank (ZMod p) V ≤ 2 := by
    by_contra hnot
    have hthree : 3 ≤ Module.finrank (ZMod p) V := by omega
    have hpows : p ^ 3 ≤ p ^ Module.finrank (ZMod p) V :=
      Nat.pow_le_pow_right (Fact.out : p.Prime).pos hthree
    have : p ^ 3 ≤ p ^ 2 := by
      calc
        p ^ 3 ≤ p ^ Module.finrank (ZMod p) V := hpows
        _ = Nat.card V := hcard.symm
        _ ≤ p ^ 2 := hVcard
    have hstrict : p ^ 2 < p ^ 3 :=
      Nat.pow_lt_pow_right (Fact.out : p.Prime).one_lt (by omega)
    exact (not_lt_of_ge this) hstrict
  exact
    natCard_le_prime_of_isPGroup_of_faithful_representation_finrank_le_two
      hQ rho hrho hdim

/-- A `p`-subgroup of the linear automorphism group of a finite
`ZMod p`-module of cardinality at most `p²` has order at most `p`. -/
theorem natCard_le_prime_of_isPGroup_subgroup_linearGL_card_le_sq
    {p : ℕ} [Fact p.Prime]
    {V : Type*} [AddCommGroup V] [Finite V] [Module (ZMod p) V]
    (P : Subgroup (LinearMap.GeneralLinearGroup (ZMod p) V))
    (hP : IsPGroup p P) (hVcard : Nat.card V ≤ p ^ 2) :
    Nat.card P ≤ p := by
  let rho : Representation (ZMod p) P V :=
    (Units.coeHom (Module.End (ZMod p) V)).comp P.subtype
  have hrho : Function.Injective rho := by
    intro x y hxy
    apply Subtype.ext
    apply Units.ext
    exact hxy
  exact
    natCard_le_prime_of_isPGroup_of_faithful_representation_card_le_sq
      hP rho hrho hVcard

end Submission.OddOrder.MathlibSupport
