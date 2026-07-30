import Submission.OddOrder.BG.Section01.Puig

/-!
Functoriality of the elementary Puig-series construction.

This is the mathlib-facing counterpart of `Puig_at_cont`, `Puig_inf_cont`, and
`Puig_cont` at the end of `BGsection1.v`.  General homomorphisms give the
forward inclusion; multiplicative equivalences give the equalities used by the
later local-analysis sections.
-/

namespace Submission.OddOrder.BG.Section01

variable {G K : Type*} [Group G] [Group K]
variable {D E A : Subgroup G} {p : ℕ}

theorem isAbelianSubgroup_map (f : G →* K) (hA : IsAbelianSubgroup A) :
    IsAbelianSubgroup (A.map f) := by
  letI : IsMulCommutative A := isMulCommutative_iff.mpr hA
  letI : IsMulCommutative (A.map f) := Subgroup.map_isMulCommutative A f
  exact isMulCommutative_iff.mp inferInstance

theorem normalizedAbelian_map (f : G →* K) (hA : NormalizedAbelian D A) :
    NormalizedAbelian (D.map f) (A.map f) :=
  ⟨(Subgroup.map_mono hA.1).trans (Subgroup.le_normalizer_map (H := A) f),
    isAbelianSubgroup_map f hA.2⟩

theorem pNormalizedAbelian_map (f : G →* K) (hA : PNormalizedAbelian p D A) :
    PNormalizedAbelian p (D.map f) (A.map f) :=
  ⟨hA.1.map f, normalizedAbelian_map f hA.2⟩

theorem map_puigSucc_le (f : G →* K) :
    (puigSucc D E).map f ≤ puigSucc (D.map f) (E.map f) := by
  rw [puigSucc, Subgroup.map_le_iff_le_comap]
  apply sSup_le
  intro A hA
  rw [← Subgroup.map_le_iff_le_comap]
  apply le_sSup
  exact ⟨Subgroup.map_mono hA.1, normalizedAbelian_map f hA.2⟩

theorem map_puigSucc_equiv (e : G ≃* K) :
    (puigSucc D E).map e.toMonoidHom =
      puigSucc (D.map e.toMonoidHom) (E.map e.toMonoidHom) := by
  apply le_antisymm (map_puigSucc_le e.toMonoidHom)
  rw [← Subgroup.map_le_map_iff_of_injective
    (f := e.symm.toMonoidHom) e.symm.injective]
  have h := map_puigSucc_le (D := D.map e.toMonoidHom)
    (E := E.map e.toMonoidHom) e.symm.toMonoidHom
  simpa [Subgroup.map_map] using h

theorem map_puigAt_equiv (e : G ≃* K) (n : ℕ) (D : Subgroup G) :
    (puigAt n D).map e.toMonoidHom = puigAt n (D.map e.toMonoidHom) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [puigAt_succ, puigAt_succ, map_puigSucc_equiv, ih]

theorem natCard_map_equiv (e : G ≃* K) (D : Subgroup G) :
    Nat.card (D.map e.toMonoidHom) = Nat.card D :=
  (Nat.card_congr (e.subgroupMap D).toEquiv).symm

theorem map_puigInf_equiv (e : G ≃* K) (D : Subgroup G) :
    (puigInf D).map e.toMonoidHom = puigInf (D.map e.toMonoidHom) := by
  rw [puigInf, puigInf, natCard_map_equiv]
  exact map_puigAt_equiv e _ D

theorem map_puig_equiv (e : G ≃* K) (D : Subgroup G) :
    (puig D).map e.toMonoidHom = puig (D.map e.toMonoidHom) := by
  rw [puig, puig, natCard_map_equiv]
  exact map_puigAt_equiv e _ D

end Submission.OddOrder.BG.Section01
