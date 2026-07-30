import Submission.OddOrder.BG.AppendixAB.PuigCentralizer
import Submission.OddOrder.BG.Section01.PuigFunctorial

/-!
Injective functoriality of the Puig series.

The general homomorphism API gives only a forward inclusion.  Appendix B.4
uses equality for a quotient map whose restriction to a Sylow subgroup is
injective.  This file proves the globally injective statements first and then
packages the exact, more general, injective-on-a-subgroup form.
-/

namespace Submission.OddOrder.BG.AppendixAB

open Submission.OddOrder.BG.Section01
open Submission.OddOrder.MathlibSupport

variable {G K : Type*} [Group G] [Group K]

/-- One Puig step commutes with an injective homomorphism. -/
theorem map_puigSucc_eq_of_injective (f : G →* K) (hf : Function.Injective f)
    (D E : Subgroup G) :
    (puigSucc D E).map f = puigSucc (D.map f) (E.map f) := by
  apply le_antisymm (map_puigSucc_le f)
  rw [puigSucc]
  apply sSup_le
  intro A hA
  have hArange : A ≤ f.range := hA.1.trans (D.map_le_range f)
  have hA0D : A.comap f ≤ D := by
    have h : A.comap f ≤ (D.map f).comap f :=
      Subgroup.comap_mono (f := f) hA.1
    rwa [Subgroup.comap_map_eq_self_of_injective hf D] at h
  have hA0norm : E ≤ Subgroup.normalizer (A.comap f : Set G) := by
    have hE : E ≤ (E.map f).comap f := by
      rw [Subgroup.comap_map_eq_self_of_injective hf E]
    exact hE.trans ((Subgroup.comap_mono (f := f) hA.2.1).trans
      (Subgroup.le_normalizer_comap f))
  have hA0abelian : IsAbelianSubgroup (A.comap f) := by
    intro x y
    apply Subtype.ext
    apply hf
    simpa using congrArg Subtype.val
      (hA.2.2 ⟨f x, x.property⟩ ⟨f y, y.property⟩)
  have hA0 : A.comap f ≤ puigSucc D E := by
    apply le_sSup
    exact ⟨hA0D, hA0norm, hA0abelian⟩
  calc
    A = (A.comap f).map f := (Subgroup.map_comap_eq_self hArange).symm
    _ ≤ (puigSucc D E).map f := Subgroup.map_mono hA0

/-- Every finite Puig stage commutes with an injective homomorphism. -/
theorem map_puigAt_eq_of_injective (f : G →* K) (hf : Function.Injective f)
    (n : ℕ) (D : Subgroup G) :
    (puigAt n D).map f = puigAt n (D.map f) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [puigAt_succ, puigAt_succ, map_puigSucc_eq_of_injective f hf, ih]

/-- The terminal lower Puig term commutes with an injective homomorphism. -/
theorem map_puigInf_eq_of_injective (f : G →* K) (hf : Function.Injective f)
    (D : Subgroup G) :
    (puigInf D).map f = puigInf (D.map f) := by
  rw [puigInf, puigInf, Subgroup.card_map_of_injective (K := D) hf]
  exact map_puigAt_eq_of_injective f hf _ D

/-- The terminal Puig subgroup commutes with an injective homomorphism. -/
theorem map_puig_eq_of_injective (f : G →* K) (hf : Function.Injective f)
    (D : Subgroup G) :
    (puig D).map f = puig (D.map f) := by
  rw [puig, puig, Subgroup.card_map_of_injective (K := D) hf]
  exact map_puigAt_eq_of_injective f hf _ D

/-- `centerWithin` commutes with a homomorphism that is injective on the
subgroup being centralized. -/
theorem map_centerWithin_eq_of_injective_on (f : G →* K) (D : Subgroup G)
    (hf : Function.Injective fun x : D ↦ f x) :
    (centerWithin D).map f = centerWithin (D.map f) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨x, hx.1, rfl⟩, ?_⟩
    rintro _ ⟨d, hd, rfl⟩
    simpa using congrArg f (hx.2 d hd)
  · rintro ⟨hyD, hycentral⟩
    obtain ⟨x, hxD, rfl⟩ := hyD
    refine ⟨x, ⟨hxD, ?_⟩, rfl⟩
    intro d hd
    have hsubtype :
        (⟨d * x, D.mul_mem hd hxD⟩ : D) =
          ⟨x * d, D.mul_mem hxD hd⟩ := by
      apply hf
      change f (d * x) = f (x * d)
      simpa using hycentral (f d) ⟨d, hd, rfl⟩
    exact congrArg (fun z : D => (z : G)) hsubtype

/-- The Puig subgroup commutes with a homomorphism whose restriction to the
ambient subgroup is injective. -/
theorem map_puig_eq_of_injective_on (f : G →* K) (D : Subgroup G)
    (hf : Function.Injective fun x : D ↦ f x) :
    (puig D).map f = puig (D.map f) := by
  let i : D →* G := D.subtype
  let fD : D →* K := f.comp i
  have hi : Function.Injective i := D.subtype_injective
  have hfD : Function.Injective fD := hf
  have htopi : (⊤ : Subgroup D).map i = D := by
    dsimp [i]
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have htopfD : (⊤ : Subgroup D).map fD = D.map f := by
    dsimp [fD]
    rw [← Subgroup.map_map, htopi]
  have hpuigi : (puig (⊤ : Subgroup D)).map i = puig D := by
    rw [map_puig_eq_of_injective i hi, htopi]
  calc
    (puig D).map f =
        ((puig (⊤ : Subgroup D)).map i).map f := by rw [hpuigi]
    _ = (puig (⊤ : Subgroup D)).map fD := by
      rw [Subgroup.map_map]
    _ = puig ((⊤ : Subgroup D).map fD) :=
      map_puig_eq_of_injective fD hfD _
    _ = puig (D.map f) := congrArg puig htopfD

/-- The center of the Puig subgroup commutes with a homomorphism whose
restriction to the ambient subgroup is injective. -/
theorem map_centerWithin_puig_eq_of_injective_on (f : G →* K)
    (D : Subgroup G) (hf : Function.Injective fun x : D ↦ f x) :
    (centerWithin (puig D)).map f = centerWithin (puig (D.map f)) := by
  have hfPuig : Function.Injective fun x : puig D ↦ f x := by
    intro x y hxy
    apply Subtype.ext
    have hxyD :
        f (⟨x, puig_le D x.property⟩ : D) =
          f (⟨y, puig_le D y.property⟩ : D) := hxy
    have hsubtype :
        (⟨x, puig_le D x.property⟩ : D) =
          ⟨y, puig_le D y.property⟩ := hf hxyD
    exact congrArg (fun z : D => (z : G)) hsubtype
  calc
    (centerWithin (puig D)).map f = centerWithin ((puig D).map f) :=
      map_centerWithin_eq_of_injective_on f (puig D) hfPuig
    _ = centerWithin (puig (D.map f)) := by
      rw [map_puig_eq_of_injective_on f D hf]

end Submission.OddOrder.BG.AppendixAB
