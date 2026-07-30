import Submission.Helpers

open LeanEval.KnotTheory
open Complex Set
open scoped ComplexConjugate

namespace Submission.Detector

noncomputable section

structure KnotDetector (K : Knot) where
  map : R3 → ℂ
  smooth : ContDiff ℝ (⊤ : ℕ∞) map
  zero_iff : ∀ p, map p = 0 ↔ p ∈ Set.range K.curve

def along {K : Knot} (D : KnotDetector K) (L : Knot) : ℝ → ℂ :=
  D.map ∘ L.curve

theorem along_smooth {K : Knot} (D : KnotDetector K) (L : Knot) :
    ContDiff ℝ (⊤ : ℕ∞) (along D L) :=
  D.smooth.comp L.smooth

theorem along_periodic {K : Knot} (D : KnotDetector K) (L : Knot) (t : ℝ) :
    along D L (t + 2 * Real.pi) = along D L t := by
  simp [along, L.periodic]

theorem along_ne_zero {K : Knot} (D : KnotDetector K) (L : Knot)
    (hdisjoint : Disjoint (Set.range K.curve) (Set.range L.curve)) (t : ℝ) :
    along D L t ≠ 0 := by
  intro hzero
  have hK : L.curve t ∈ Set.range K.curve :=
    (D.zero_iff (L.curve t)).mp hzero
  have hL : L.curve t ∈ Set.range L.curve := ⟨t, rfl⟩
  exact Set.disjoint_left.mp hdisjoint hK hL

def linkingValue {K : Knot} (D : KnotDetector K) (L : Knot) : ℝ :=
  Linking.windingValue (along D L) (along_smooth D L) (along_periodic D L)

def mirror {K : Knot} (D : KnotDetector K) : KnotDetector (Helpers.mirrorKnot K) where
  map p := conj (D.map (reflectZ p))
  smooth := by
    change ContDiff ℝ (⊤ : ℕ∞)
      (Complex.conjCLE ∘ D.map ∘ Helpers.reflectZContinuousLinearEquiv)
    exact Complex.conjCLE.contDiff.comp
      (D.smooth.comp Helpers.reflectZContinuousLinearEquiv.contDiff)
  zero_iff := by
    intro p
    constructor
    · intro hzero
      have hreflect : reflectZ p ∈ Set.range K.curve := by
        apply (D.zero_iff (reflectZ p)).mp
        simpa using congrArg conj hzero
      rcases hreflect with ⟨t, ht⟩
      refine ⟨t, ?_⟩
      change reflectZ (K.curve t) = p
      rw [ht, Helpers.reflectZ_involutive]
    · rintro ⟨t, rfl⟩
      change conj (D.map (reflectZ (reflectZ (K.curve t)))) = 0
      rw [Helpers.reflectZ_involutive]
      simp [(D.zero_iff (K.curve t)).2 ⟨t, rfl⟩]

theorem mirror_along {K : Knot} (D : KnotDetector K) (L : Knot) (t : ℝ) :
    along (mirror D) (Helpers.mirrorKnot L) t = conj (along D L t) := by
  simp [along, mirror, Helpers.mirrorKnot, Helpers.reflectZ_involutive]

theorem linkingValue_mirror {K : Knot} (D : KnotDetector K) (L : Knot) :
    linkingValue (mirror D) (Helpers.mirrorKnot L) = -linkingValue D L := by
  have hcurve : along (mirror D) (Helpers.mirrorKnot L) =
      fun t => conj (along D L t) := by
    funext t
    exact mirror_along D L t
  unfold linkingValue
  calc
    Linking.windingValue (along (mirror D) (Helpers.mirrorKnot L))
        (along_smooth (mirror D) (Helpers.mirrorKnot L))
        (along_periodic (mirror D) (Helpers.mirrorKnot L)) =
      Linking.windingValue (fun t => conj (along D L t))
        (Complex.conjCLE.contDiff.comp (along_smooth D L))
        (fun t => congrArg conj (along_periodic D L t)) :=
      Linking.windingValue_congr hcurve _ _ _ _
    _ = -Linking.windingValue (along D L) (along_smooth D L) (along_periodic D L) :=
      Linking.windingValue_conj (along D L) (along_smooth D L) (along_periodic D L)

def transport {K1 K2 : Knot} (D : KnotDetector K1)
    (Phi : AmbientIsotopy) (sigma : CircleReparam)
    (hendpoint : ∀ t, Phi.H 1 (K1.curve t) = K2.curve (sigma.f t)) :
    KnotDetector K2 where
  map p := D.map (Phi.Hinv 1 p)
  smooth := D.smooth.comp (Orientation.slice_inv_contDiff Phi 1)
  zero_iff := by
    intro p
    constructor
    · intro hzero
      have hpre : Phi.Hinv 1 p ∈ Set.range K1.curve :=
        (D.zero_iff (Phi.Hinv 1 p)).mp hzero
      rcases hpre with ⟨t, ht⟩
      refine ⟨sigma.f t, ?_⟩
      calc
        K2.curve (sigma.f t) = Phi.H 1 (K1.curve t) := (hendpoint t).symm
        _ = Phi.H 1 (Phi.Hinv 1 p) := by rw [ht]
        _ = p := Phi.inv_right 1 p
    · rintro ⟨t, rfl⟩
      apply (D.zero_iff (Phi.Hinv 1 (K2.curve t))).2
      refine ⟨sigma.finv t, ?_⟩
      have h := congrArg (Phi.Hinv 1) (hendpoint (sigma.finv t))
      rw [sigma.right_inv, Phi.inv_left] at h
      exact h

theorem disjoint_of_transport
    {K1 K2 L1 L2 : Knot} (Phi : AmbientIsotopy)
    (sigma tau : CircleReparam)
    (hK : ∀ t, Phi.H 1 (K1.curve t) = K2.curve (sigma.f t))
    (hL : ∀ t, Phi.H 1 (L1.curve t) = L2.curve (tau.f t))
    (hdisjoint : Disjoint (Set.range K1.curve) (Set.range L1.curve)) :
    Disjoint (Set.range K2.curve) (Set.range L2.curve) := by
  rw [Set.disjoint_left]
  intro p hpK hpL
  rcases hpK with ⟨s, hs⟩
  rcases hpL with ⟨t, ht⟩
  have hKs := hK (sigma.finv s)
  have hLt := hL (tau.finv t)
  rw [sigma.right_inv] at hKs
  rw [tau.right_inv] at hLt
  have hforward :
      Phi.H 1 (K1.curve (sigma.finv s)) = Phi.H 1 (L1.curve (tau.finv t)) :=
    hKs.trans (hs.trans (ht.symm.trans hLt.symm))
  have hpre := congrArg (Phi.Hinv 1) hforward
  simp only [Phi.inv_left] at hpre
  exact Set.disjoint_left.mp hdisjoint ⟨sigma.finv s, rfl⟩
    ⟨tau.finv t, hpre.symm⟩

theorem transport_along
    {K1 K2 L1 L2 : Knot} (D : KnotDetector K1)
    (Phi : AmbientIsotopy) (sigma tau : CircleReparam)
    (hK : ∀ t, Phi.H 1 (K1.curve t) = K2.curve (sigma.f t))
    (hL : ∀ t, Phi.H 1 (L1.curve t) = L2.curve (tau.f t)) (t : ℝ) :
    along (transport D Phi sigma hK) L2 (tau.f t) = along D L1 t := by
  change D.map (Phi.Hinv 1 (L2.curve (tau.f t))) = D.map (L1.curve t)
  rw [← hL t, Phi.inv_left]

theorem linkingValue_transport
    {K1 K2 L1 L2 : Knot} (D : KnotDetector K1)
    (Phi : AmbientIsotopy) (sigma tau : CircleReparam)
    (hK : ∀ t, Phi.H 1 (K1.curve t) = K2.curve (sigma.f t))
    (hL : ∀ t, Phi.H 1 (L1.curve t) = L2.curve (tau.f t))
    (hdisjoint : Disjoint (Set.range K1.curve) (Set.range L1.curve)) :
    linkingValue (transport D Phi sigma hK) L2 = linkingValue D L1 := by
  unfold linkingValue
  exact Linking.windingValue_eq_of_reparam
    (along D L1) (along (transport D Phi sigma hK) L2)
    (along_smooth D L1) (along_smooth (transport D Phi sigma hK) L2)
    (along_periodic D L1) (along_periodic (transport D Phi sigma hK) L2)
    (along_ne_zero (transport D Phi sigma hK) L2
      (disjoint_of_transport Phi sigma tau hK hL hdisjoint)) tau
    (transport_along D Phi sigma tau hK hL)

end

end Submission.Detector
