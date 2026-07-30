import Submission.OddOrder.MathlibSupport.PSubgroupGeneralLinearTwo
import Mathlib.Algebra.Module.ZMod
import Mathlib.RepresentationTheory.Basic

/-!
Prime-order faithful actions on elementary-abelian groups of rank at most two.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped IsMulCommutative

noncomputable section

universe u v

variable {p q : ℕ} [Fact p.Prime]
variable {A : Type u} {E : Type v}
variable [Group A] [Finite A] [Group E] [Finite E]

/-- Multiplicative automorphisms of an abelian group of exponent `p`,
linearized on its additive `ZMod p` form. -/
private def elementaryAbelianMulAutRepresentation
    [IsMulCommutative E] [Module (ZMod p) (Additive E)] :
    Representation (ZMod p) (MulAut E) (Additive E) where
  toFun f := (MonoidHom.toAdditive f.toMonoidHom).toZModLinearMap p
  map_one' := by
    apply LinearMap.ext
    intro x
    change Additive.ofMul ((1 : MulAut E) x.toMul) = x
    simp
  map_mul' := by
    intro f g
    apply LinearMap.ext
    intro x
    change Additive.ofMul ((f * g) x.toMul) =
      Additive.ofMul (f (g x.toMul))
    rfl

omit [Finite E] in
private theorem elementaryAbelianMulAutRepresentation_injective
    [IsMulCommutative E] [Module (ZMod p) (Additive E)] :
    Function.Injective
      (elementaryAbelianMulAutRepresentation (p := p) (E := E)).asGroupHom := by
  intro f g hfg
  apply MulEquiv.ext
  intro x
  have hx := LinearMap.congr_fun (Units.ext_iff.mp hfg) (Additive.ofMul x)
  exact congrArg Additive.toMul hx

/-- If a group of prime cardinality `q` acts faithfully on an
elementary-abelian `p`-group of cardinality at most `p²`, then
`q ∣ p² - 1` (provided `q ≠ p`). -/
theorem prime_dvd_sq_sub_one_of_faithful_elementaryAbelian_action
    (hq : q.Prime) (hqp : q ≠ p) (hAcard : Nat.card A = q)
    (hcomm : IsMulCommutative E) (hpow : ∀ x : E, x ^ p = 1)
    (hEcard : Nat.card E ≤ p ^ 2)
    (rho : A →* MulAut E) (hrho : Function.Injective rho) :
    q ∣ p ^ 2 - 1 := by
  classical
  letI : IsMulCommutative E := hcomm
  letI : AddCommGroup (Additive E) := inferInstance
  letI : Module (ZMod p) (Additive E) :=
    AddCommGroup.zmodModule fun x ↦ by
      change x.toMul ^ p = 1
      exact hpow x.toMul
  letI : Fintype (Additive E) := Fintype.ofFinite (Additive E)
  letI hfinite : Module.Finite (ZMod p) (Additive E) :=
    Module.Finite.of_fg_top (by
      rw [← Submodule.span_univ]
      exact Submodule.fg_span Set.finite_univ)
  let hfree : Module.Free (ZMod p) (Additive E) :=
    @Module.Free.of_divisionRing (ZMod p) (Additive E)
      inferInstance inferInstance inferInstance
  let linearize :
      MulAut E →* LinearMap.GeneralLinearGroup (ZMod p) (Additive E) :=
    (elementaryAbelianMulAutRepresentation (p := p) (E := E)).asGroupHom
  let rhoGL :
      A →* LinearMap.GeneralLinearGroup (ZMod p) (Additive E) :=
    linearize.comp rho
  have hrhoGL : Function.Injective rhoGL :=
    (elementaryAbelianMulAutRepresentation_injective (p := p) (E := E)).comp hrho
  let n : ℕ := Module.finrank (ZMod p) (Additive E)
  let b : Module.Basis (Fin n) (ZMod p) (Additive E) :=
    @Module.finBasisOfFinrankEq (ZMod p) (Additive E)
      inferInstance inferInstance inferInstance hfree
      inferInstance hfinite n rfl
  let e : GL (Fin n) (ZMod p) ≃*
      LinearMap.GeneralLinearGroup (ZMod p) (Additive E) :=
    Matrix.GeneralLinearGroup.toLin' b
  let rhoM : A →* GL (Fin n) (ZMod p) :=
    e.symm.toMonoidHom.comp rhoGL
  have hrhoM : Function.Injective rhoM := e.symm.injective.comp hrhoGL
  let Q : Subgroup (GL (Fin n) (ZMod p)) := rhoM.range
  have hQcard : Nat.card Q = q := by
    calc
      Nat.card Q = Nat.card A := by
        symm
        exact Nat.card_congr (Equiv.ofInjective rhoM hrhoM)
      _ = q := hAcard
  have hqGL : q ∣ Nat.card (GL (Fin n) (ZMod p)) := by
    rw [← hQcard]
    exact Q.card_subgroup_dvd_card
  have hcardE : Nat.card E = p ^ n := by
    calc
      Nat.card E = Nat.card (Additive E) := Nat.card_congr Additive.ofMul
      _ = p ^ n := by
        simpa only [Nat.card_zmod] using
          (Module.natCard_eq_pow_finrank
            (K := ZMod p) (V := Additive E))
  have hn : n ≤ 2 := by
    by_contra hnle
    have hthree : 3 ≤ n := by omega
    have hpowle : p ^ 3 ≤ p ^ n :=
      Nat.pow_le_pow_right (Fact.out : p.Prime).pos hthree
    have hbad : p ^ 3 ≤ p ^ 2 := by
      calc
        p ^ 3 ≤ p ^ n := hpowle
        _ = Nat.card E := hcardE.symm
        _ ≤ p ^ 2 := hEcard
    exact (not_lt_of_ge hbad)
      (Nat.pow_lt_pow_right (Fact.out : p.Prime).one_lt (by omega))
  have hfactor : p ^ 2 - 1 = (p + 1) * (p - 1) := by
    simpa using (Nat.sq_sub_sq p 1)
  have hminus_dvd (hminus : q ∣ p - 1) : q ∣ p ^ 2 - 1 := by
    rw [hfactor]
    exact dvd_mul_of_dvd_right hminus (p + 1)
  have hqnotp : ¬ q ∣ p := by
    intro hdiv
    have hcases := (Nat.dvd_prime (Fact.out : p.Prime)).mp hdiv
    exact hqp (hcases.resolve_left hq.ne_one)
  have hnCases : n = 0 ∨ n = 1 ∨ n = 2 := by omega
  rcases hnCases with hn0 | hn1 | hn2
  · rw [hn0] at hqGL
    have hcardGL : Nat.card (GL (Fin 0) (ZMod p)) = 1 := by
      simp
    rw [hcardGL] at hqGL
    exact (hq.not_dvd_one hqGL).elim
  · rw [hn1] at hqGL
    have hcardGL : Nat.card (GL (Fin 1) (ZMod p)) = p - 1 := by
      simpa [Fin.prod_univ_succ] using
        (Matrix.card_GL_field (𝔽 := ZMod p) 1)
    rw [hcardGL] at hqGL
    exact hminus_dvd hqGL
  · rw [hn2] at hqGL
    have hcardGL : Nat.card (GL (Fin 2) (ZMod p)) =
        (p ^ 2 - 1) * (p ^ 2 - p) := by
      simpa [Fin.prod_univ_succ] using
        (Matrix.card_GL_field (𝔽 := ZMod p) 2)
    rw [hcardGL] at hqGL
    rcases hq.dvd_or_dvd hqGL with hfirst | hsecond
    · exact hfirst
    · have hsecondFactor : p ^ 2 - p = p * (p - 1) := by
        rw [Nat.mul_sub_left_distrib, pow_two, mul_one]
      rw [hsecondFactor] at hsecond
      exact hminus_dvd ((hq.dvd_or_dvd hsecond).resolve_left hqnotp)

end

end Submission.OddOrder.MathlibSupport
