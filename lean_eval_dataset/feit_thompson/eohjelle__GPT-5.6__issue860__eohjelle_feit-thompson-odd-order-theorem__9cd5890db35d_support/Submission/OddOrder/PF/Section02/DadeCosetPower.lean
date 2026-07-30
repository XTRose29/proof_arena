import Submission.OddOrder.PF.Section02.DadeSignalizer

/-!
# Recovering the Dade-coset factor by a coprime power

MathComp uses the canonical `pi`-part of an element in the proof of
Peterfalvi 2.4.  Here a Chinese-remainder exponent kills the two signalizer
factors while fixing the two centralizer factors.
-/

namespace Submission.OddOrder.PF

open Submission.OddOrder.MathlibSupport
open scoped Pointwise

universe u

/-- Conjugate elements of two Dade right cosets have conjugate right
factors.  This is the coprime-power extraction used in Peterfalvi 2.4(b)
and in the strengthened normalized-TI form of 2.4(c). -/
theorem dade_coset_conj_right_factor
    {Γ : Type u} [Group Γ] [Finite Γ]
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A)
    {a b u v g : Γ}
    (ha : a ∈ A) (hb : b ∈ A)
    (hu :
      u ∈ (DadeSignalizer ddA a : Set Γ) * ({a} : Set Γ))
    (hv :
      v ∈ (DadeSignalizer ddA b : Set Γ) * ({b} : Set Γ))
    (hconj : g⁻¹ * u * g = v) :
    g⁻¹ * a * g = b := by
  rcases Set.mem_mul.mp hu with ⟨x, hx, a', ha', rfl⟩
  rw [Set.mem_singleton_iff] at ha'
  subst a'
  rcases Set.mem_mul.mp hv with ⟨y, hy, b', hb', rfl⟩
  rw [Set.mem_singleton_iff] at hb'
  subst b'

  let Ha : Subgroup Γ := DadeSignalizer ddA a
  let Hb : Subgroup Γ := DadeSignalizer ddA b
  let Ca : Subgroup Γ :=
    centralizerWithin L (Subgroup.zpowers a)
  let Cb : Subgroup Γ :=
    centralizerWithin L (Subgroup.zpowers b)
  let m := Nat.card Ha * Nat.card Hb
  let n := Nat.card Ca * Nat.card Cb

  have hHaCa : Nat.Coprime (Nat.card Ha) (Nat.card Ca) := by
    simpa [Ha, Ca] using Dade_coprime ddA ha ha
  have hHaCb : Nat.Coprime (Nat.card Ha) (Nat.card Cb) := by
    simpa [Ha, Cb] using Dade_coprime ddA ha hb
  have hHbCa : Nat.Coprime (Nat.card Hb) (Nat.card Ca) := by
    simpa [Hb, Ca] using Dade_coprime ddA hb ha
  have hHbCb : Nat.Coprime (Nat.card Hb) (Nat.card Cb) := by
    simpa [Hb, Cb] using Dade_coprime ddA hb hb
  have hcop : Nat.Coprime m n := by
    dsimp [m, n]
    exact Nat.Coprime.mul_left
      (Nat.Coprime.mul_right hHaCa hHaCb)
      (Nat.Coprime.mul_right hHbCa hHbCb)

  let e0 := Nat.chineseRemainder hcop 0 1
  let e : ℕ := e0
  have hem : e ≡ 0 [MOD m] := e0.property.1
  have hen : e ≡ 1 [MOD n] := e0.property.2

  have hxa : Commute x a :=
    (Dade_signalizer_cent ddA a hx a
      (Subgroup.mem_zpowers a)).symm
  have hyb : Commute y b :=
    (Dade_signalizer_cent ddA b hy b
      (Subgroup.mem_zpowers b)).symm

  have haCa : a ∈ Ca := by
    refine ⟨ddA.1.1 ha, ?_⟩
    intro z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact ((Commute.refl a).zpow_left k).eq
  have hbCb : b ∈ Cb := by
    refine ⟨ddA.1.1 hb, ?_⟩
    intro z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact ((Commute.refl b).zpow_left k).eq

  have hxpow : x ^ e = 1 := by
    apply pow_eq_one_iff_modEq.mpr
    apply hem.of_dvd
    exact (Ha.orderOf_dvd_natCard hx).trans
      (by
        dsimp [m]
        exact dvd_mul_right (Nat.card Ha) (Nat.card Hb))
  have hypow : y ^ e = 1 := by
    apply pow_eq_one_iff_modEq.mpr
    apply hem.of_dvd
    exact (Hb.orderOf_dvd_natCard hy).trans
      (by
        dsimp [m]
        exact dvd_mul_left (Nat.card Hb) (Nat.card Ha))
  have hapow : a ^ e = a := by
    have hmod : e ≡ 1 [MOD orderOf a] := by
      apply hen.of_dvd
      exact (Ca.orderOf_dvd_natCard haCa).trans
        (by
          dsimp [n]
          exact dvd_mul_right (Nat.card Ca) (Nat.card Cb))
    simpa using (pow_eq_pow_iff_modEq.mpr hmod : a ^ e = a ^ 1)
  have hbpow : b ^ e = b := by
    have hmod : e ≡ 1 [MOD orderOf b] := by
      apply hen.of_dvd
      exact (Cb.orderOf_dvd_natCard hbCb).trans
        (by
          dsimp [n]
          exact dvd_mul_left (Nat.card Cb) (Nat.card Ca))
    simpa using (pow_eq_pow_iff_modEq.mpr hmod : b ^ e = b ^ 1)

  have hxapow : (x * a) ^ e = a := by
    rw [hxa.mul_pow, hxpow, hapow, one_mul]
  have hybpow : (y * b) ^ e = b := by
    rw [hyb.mul_pow, hypow, hbpow, one_mul]

  calc
    g⁻¹ * a * g = g⁻¹ * ((x * a) ^ e) * g := by rw [hxapow]
    _ = (g⁻¹ * (x * a) * g) ^ e := by
      simpa [MulAut.conj_apply] using
        (map_pow (MulAut.conj g⁻¹) (x * a) e)
    _ = (y * b) ^ e := congrArg (fun z : Γ ↦ z ^ e) hconj
    _ = b := hybpow

end Submission.OddOrder.PF
