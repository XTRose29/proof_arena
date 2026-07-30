import Submission.OddOrder.PF.Section02.DadeSignalizer

/-!
# Peterfalvi 2.4(a): conjugation invariance of the first Dade support

The support is expressed using explicit right-conjugacy witnesses, matching
the convention `g⁻¹ * y * g` used throughout the Peterfalvi port.
-/

namespace Submission.OddOrder.PF

open Submission.OddOrder.MathlibSupport
open scoped Pointwise

universe u

variable {Γ : Type u} [Group Γ]

/-- The union of the `G`-conjugacy classes meeting `S`. -/
def classSupportWithin (G : Subgroup Γ) (S : Set Γ) : Set Γ :=
  {y | ∃ x ∈ S, y ∈ conjugacyClassWithin G x}

/-- The first support associated with a Dade signalizer. -/
def Dade_support1
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) (a : Γ) : Set Γ :=
  classSupportWithin G
    ((DadeSignalizer ddA a : Set Γ) * ({a} : Set Γ))

/-- Every product `x * a` with `x` in the signalizer at `a` belongs to the
first Dade support. -/
theorem mem_Dade_support1
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) {a x : Γ}
    (ha : a ∈ A) (hx : x ∈ DadeSignalizer ddA a) :
    x * a ∈ Dade_support1 ddA a := by
  have hxG : x ∈ G := Dade_signalizer_sub ddA a hx
  have haG : a ∈ G := ddA.2.1 (ddA.1.1 ha)
  have hxaG : x * a ∈ G := G.mul_mem hxG haG
  refine ⟨x * a, ?_, x * a, hxaG, ?_⟩
  · exact ⟨x, hx, a, by simp, rfl⟩
  · group

private theorem centralizerWithin_map_equiv
    {D S : Subgroup Γ} (e : Γ ≃* Γ)
    (hD : D.map e.toMonoidHom = D) :
    (centralizerWithin D S).map e.toMonoidHom =
      centralizerWithin D (S.map e.toMonoidHom) := by
  ext y
  rw [Subgroup.mem_map_equiv]
  constructor
  · intro hy
    refine ⟨?_, ?_⟩
    · have hyMap : y ∈ D.map e.toMonoidHom :=
        Subgroup.mem_map_equiv.mpr hy.1
      rwa [hD] at hyMap
    · intro z hz
      have hz' : e.symm z ∈ S := Subgroup.mem_map_equiv.mp hz
      have hcomm := hy.2 (e.symm z) hz'
      simpa using congrArg e hcomm
  · intro hy
    refine ⟨?_, ?_⟩
    · have hyMap : y ∈ D.map e.toMonoidHom := by
        rw [hD]
        exact hy.1
      exact Subgroup.mem_map_equiv.mp hyMap
    · intro z hz
      have hzMap : e z ∈ S.map e.toMonoidHom :=
        (Subgroup.mem_map_iff_mem e.injective).mpr hz
      have hcomm := hy.2 (e z) hzMap
      simpa using congrArg e.symm hcomm

/-- Conjugation by an element of `L` transports Dade signalizers. -/
theorem DadeJ
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) (a x : Γ) (hx : x ∈ L) :
    DadeSignalizer ddA (x⁻¹ * a * x) =
      (DadeSignalizer ddA a).map
        (MulAut.conj x⁻¹).toMonoidHom := by
  let e : Γ ≃* Γ := MulAut.conj x⁻¹
  have hxG : x ∈ G := ddA.2.1 hx
  have hGmap : G.map e.toMonoidHom = G := by
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mp
    exact Subgroup.le_normalizer (G.inv_mem hxG)
  have hCGmap :
      (centralizerWithin G (Subgroup.zpowers a)).map e.toMonoidHom =
        centralizerWithin G
          (Subgroup.zpowers (x⁻¹ * a * x)) := by
    have hmap := centralizerWithin_map_equiv
      (S := Subgroup.zpowers a) e hGmap
    simpa [MonoidHom.map_zpowers, e] using hmap
  change
    piPrimeCore (dadePrimeSet L A)
        (centralizerWithin G (Subgroup.zpowers (x⁻¹ * a * x))) =
      (piPrimeCore (dadePrimeSet L A)
        (centralizerWithin G (Subgroup.zpowers a))).map
          e.toMonoidHom
  calc
    piPrimeCore (dadePrimeSet L A)
        (centralizerWithin G (Subgroup.zpowers (x⁻¹ * a * x))) =
      piPrimeCore (dadePrimeSet L A)
        ((centralizerWithin G (Subgroup.zpowers a)).map
          e.toMonoidHom) := congrArg (piPrimeCore (dadePrimeSet L A))
            hCGmap.symm
    _ = (piPrimeCore (dadePrimeSet L A)
          (centralizerWithin G (Subgroup.zpowers a))).map
            e.toMonoidHom :=
      (piPrimeCore_map_equiv (dadePrimeSet L A)
        (centralizerWithin G (Subgroup.zpowers a)) e).symm

/-- The first Dade support is invariant under conjugating its argument by
an element of `L`. -/
theorem Dade_support1_id
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) (a x : Γ) (hx : x ∈ L) :
    Dade_support1 ddA (x⁻¹ * a * x) = Dade_support1 ddA a := by
  let b : Γ := x⁻¹ * a * x
  let e : Γ ≃* Γ := MulAut.conj x⁻¹
  have hxG : x ∈ G := ddA.2.1 hx
  have hJ : DadeSignalizer ddA b =
      (DadeSignalizer ddA a).map e.toMonoidHom := by
    simpa [b, e] using DadeJ ddA a x hx
  ext y
  change
    (∃ z ∈ ((DadeSignalizer ddA b : Set Γ) * ({b} : Set Γ)),
      ∃ g ∈ G, g⁻¹ * z * g = y) ↔
    (∃ z ∈ ((DadeSignalizer ddA a : Set Γ) * ({a} : Set Γ)),
      ∃ g ∈ G, g⁻¹ * z * g = y)
  constructor
  · rintro ⟨z, hz, g, hg, rfl⟩
    rcases Set.mem_mul.mp hz with ⟨h, hh, t, ht, rfl⟩
    have htEq : t = b := Set.mem_singleton_iff.mp ht
    subst t
    rw [hJ] at hh
    rcases hh with ⟨h₀, hh₀, rfl⟩
    refine ⟨h₀ * a, ?_, x * g, G.mul_mem hxG hg, ?_⟩
    · exact ⟨h₀, hh₀, a, by simp, rfl⟩
    · simp [e, b, mul_assoc]
  · rintro ⟨z, hz, g, hg, rfl⟩
    rcases Set.mem_mul.mp hz with ⟨h, hh, t, ht, rfl⟩
    have htEq : t = a := Set.mem_singleton_iff.mp ht
    subst t
    have heh : e h ∈ DadeSignalizer ddA b := by
      rw [hJ]
      exact (Subgroup.mem_map_iff_mem e.injective).mpr hh
    refine ⟨e h * b, ?_, x⁻¹ * g,
      G.mul_mem (G.inv_mem hxG) hg, ?_⟩
    · exact ⟨e h, heh, b, by simp, rfl⟩
    · simp [e, b, mul_assoc]

end Submission.OddOrder.PF
