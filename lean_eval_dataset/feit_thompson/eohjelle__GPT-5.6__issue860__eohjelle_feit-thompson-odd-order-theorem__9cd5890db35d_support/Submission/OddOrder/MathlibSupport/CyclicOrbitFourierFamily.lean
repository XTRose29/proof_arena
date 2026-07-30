import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Submission.OddOrder.MathlibSupport.IndependentConjugationBlockRankDrop

/-!
Fourier transforms of independent families of free finite cyclic orbits.
-/

namespace Submission.OddOrder.MathlibSupport

open Module
open scoped BigOperators

universe u v w

variable {k : Type u} {W : Type v} {J : Type w}
variable [Field k] [AddCommGroup W] [Module k W]

/-- Fourier transform every cyclic orbit, indexed first by weight and then by
the orbit label. -/
noncomputable def cyclicOrbitFourierFamily
    {h : Nat} [NeZero h] {omega : kˣ}
    (homega : IsPrimitiveRoot omega h)
    (v : J -> ZMod h -> W) (i : ZMod h) (j : J) : W :=
  ∑ t : ZMod h,
    (primitiveRootUnitWeight homega (-(i * t)) : k) • v j t

/-- On one orbit, the family-level Fourier transform agrees with the Fourier
vector constructed from the basis spanned by that orbit. -/
theorem cyclicOrbitFourierFamily_eq_cyclicOrbitFourierVector
    {h : Nat} [NeZero h] {omega : kˣ}
    (homega : IsPrimitiveRoot omega h) (v : ZMod h -> W)
    (hv : LinearIndependent k v) (i : ZMod h) :
    cyclicOrbitFourierFamily homega (fun _ : Unit => v) i () =
      Submodule.subtype (Submodule.span k (Set.range v))
        (cyclicOrbitFourierVector homega (Basis.span hv) i) := by
  simp [cyclicOrbitFourierFamily, cyclicOrbitFourierVector]

/-- Fourier transformation preserves linear independence on one free cyclic
orbit. -/
theorem cyclicOrbitFourierFamily_linearIndependent
    {h : Nat} [NeZero h] {omega : kˣ}
    (homega : IsPrimitiveRoot omega h) (v : ZMod h -> W)
    (hv : LinearIndependent k v) :
    LinearIndependent k
      (fun i => cyclicOrbitFourierFamily homega (fun _ : Unit => v) i ()) := by
  let S : Submodule k W := Submodule.span k (Set.range v)
  let b : Basis (ZMod h) k S := Basis.span hv
  let shift : S ≃ₗ[k] S := b.equiv b (Equiv.addRight (1 : ZMod h))
  have hshift (t : ZMod h) : shift (b t) = b (t + 1) := by
    simp [shift]
  have hfourier :
      LinearIndependent k (cyclicOrbitFourierVector homega b) :=
    cyclicOrbitFourierVector_linearIndependent homega b shift hshift
  have hmapped := hfourier.map' S.subtype (by simp)
  simpa [Function.comp_def, S, b,
    cyclicOrbitFourierFamily_eq_cyclicOrbitFourierVector homega v hv] using hmapped

/-- Fourier transformation preserves the span of one free cyclic orbit. -/
theorem span_cyclicOrbitFourierFamily_eq
    {h : Nat} [NeZero h] {omega : kˣ}
    (homega : IsPrimitiveRoot omega h) (v : ZMod h -> W)
    (hv : LinearIndependent k v) :
    Submodule.span k
        (Set.range
          (fun i => cyclicOrbitFourierFamily homega (fun _ : Unit => v) i ())) =
      Submodule.span k (Set.range v) := by
  let S : Submodule k W := Submodule.span k (Set.range v)
  letI : FiniteDimensional k S := (Basis.span hv).finiteDimensional_of_finite
  apply Submodule.eq_of_le_of_finrank_eq
  · rw [Submodule.span_le]
    rintro x ⟨i, rfl⟩
    unfold cyclicOrbitFourierFamily
    exact Submodule.sum_mem _ fun t _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨t, rfl⟩)
  · rw [finrank_span_eq_card
      (cyclicOrbitFourierFamily_linearIndependent homega v hv),
      finrank_span_eq_card hv]

/-- Fourier transformation preserves global independence across any finite
family of independent cyclic orbits. -/
theorem cyclicOrbitFourierFamily_global_linearIndependent
    {h : Nat} [NeZero h] {omega : kˣ}
    (homega : IsPrimitiveRoot omega h) [Fintype J]
    (v : J -> ZMod h -> W)
    (hv : LinearIndependent k (fun p : J × ZMod h => v p.1 p.2)) :
    LinearIndependent k
      (fun p : ZMod h × J =>
        cyclicOrbitFourierFamily homega v p.1 p.2) := by
  rw [linearIndependent_iff_card_eq_finrank_span]
  have hslice (j : J) : LinearIndependent k (v j) :=
    linearIndependent_weight_slice v hv j
  have hlocal (j : J) :
      indexedWeightBlock (k := k)
          (fun j i => cyclicOrbitFourierFamily homega v i j) j =
        indexedWeightBlock (k := k) v j := by
    exact span_cyclicOrbitFourierFamily_eq homega (v j) (hslice j)
  have hrange :
      Set.range (fun p : ZMod h × J =>
          cyclicOrbitFourierFamily homega v p.1 p.2) =
        Set.range (fun p : J × ZMod h =>
          cyclicOrbitFourierFamily homega v p.2 p.1) := by
    ext x
    constructor
    · rintro ⟨⟨i, j⟩, rfl⟩
      exact ⟨(j, i), rfl⟩
    · rintro ⟨⟨j, i⟩, rfl⟩
      exact ⟨(i, j), rfl⟩
  change Fintype.card (ZMod h × J) =
    Module.finrank k (Submodule.span k
      (Set.range (fun p : ZMod h × J =>
        cyclicOrbitFourierFamily homega v p.1 p.2)))
  rw [hrange,
    ← iSup_indexedWeightBlock (k := k)
      (fun j : J => fun i : ZMod h => cyclicOrbitFourierFamily homega v i j),
    show (⨆ j, indexedWeightBlock (k := k)
      (fun j i => cyclicOrbitFourierFamily homega v i j) j) =
        ⨆ j, indexedWeightBlock (k := k) v j by
      exact iSup_congr hlocal,
    iSup_indexedWeightBlock (k := k) v]
  have hvcard := (linearIndependent_iff_card_eq_finrank_span.mp hv)
  change Fintype.card (J × ZMod h) =
    Module.finrank k (Submodule.span k
      (Set.range (fun p : J × ZMod h => v p.1 p.2))) at hvcard
  simpa [Fintype.card_prod, Nat.mul_comm] using hvcard

/-- A linear equivalence shifting every orbit by one acts on the transformed
family through the corresponding primitive-root eigenvalue. -/
theorem linearEquiv_apply_cyclicOrbitFourierFamily
    {h : Nat} [NeZero h] {omega : kˣ}
    (homega : IsPrimitiveRoot omega h)
    (v : J -> ZMod h -> W) (f : W ≃ₗ[k] W)
    (hshift : ∀ j t, f (v j t) = v j (t + 1))
    (i : ZMod h) (j : J) :
    f (cyclicOrbitFourierFamily homega v i j) =
      (primitiveRootUnitWeight homega i : k) •
        cyclicOrbitFourierFamily homega v i j := by
  rw [cyclicOrbitFourierFamily, map_sum]
  simp_rw [map_smul, hshift]
  rw [Finset.smul_sum]
  apply Fintype.sum_equiv (Equiv.addRight (1 : ZMod h))
  intro t
  rw [smul_smul]
  have hweight :
      primitiveRootUnitWeight homega (-(i * t)) =
        primitiveRootUnitWeight homega i *
          primitiveRootUnitWeight homega (-(i * (t + 1))) := by
    rw [← primitiveRootUnitWeight_add]
    congr 1
    ring
  rw [hweight]
  simp

end Submission.OddOrder.MathlibSupport
