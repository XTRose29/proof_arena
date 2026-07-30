import Mathlib
import Submission.Helpers

open Polynomial IntermediateField

namespace Submission

theorem solvable_iff_solvableByRad (F : Type*) [Field F] [CharZero F]
    (p : F[X]) (_hp : p ≠ 0) :
    (∀ x : AlgebraicClosure F, aeval x p = 0 →
        x ∈ solvableByRad F (AlgebraicClosure F)) ↔ IsSolvable p.Gal := by
  let A := AlgebraicClosure F
  let S : IntermediateField F A := solvableByRad F A
  constructor
  · let P : F[X] → Prop := fun q ↦
      (∀ x : A, aeval x q = 0 → x ∈ S) → IsSolvable q.Gal
    change P p
    induction p using WfDvdMonoid.induction_on_irreducible with
    | zero =>
        intro _
        exact gal_zero_isSolvable
    | unit q hq =>
        intro _
        letI : Fact q.Splits := ⟨hq.splits⟩
        infer_instance
    | mul q r hq hr hir =>
        intro hall
        have hqall : ∀ x : A, aeval x q = 0 → x ∈ S := by
          intro x hx
          exact hall x (by simp [hx])
        have hrall : ∀ x : A, aeval x r = 0 → x ∈ S := by
          intro x hx
          exact hall x (by simp [hx])
        have hr_degree : r.degree ≠ 0 := fun hdegree ↦
          hr.not_isUnit (Polynomial.isUnit_iff_degree_eq_zero.mpr hdegree)
        obtain ⟨x, hx⟩ := Splits.exists_eval_eq_zero
          (IsAlgClosed.splits (r.map (algebraMap F A))) (by rwa [degree_map])
        rw [eval_map_algebraMap] at hx
        exact gal_mul_isSolvable
          (isSolvable_gal_of_irreducible (hrall x hx) hr hx) (hir hq hqall)
  · intro hsolv
    letI : IsSolvable p.Gal := hsolv
    have hp_splits : (p.map (algebraMap F A)).Splits := IsAlgClosed.splits _
    let K : IntermediateField F A := IntermediateField.adjoin F (p.rootSet A)
    letI : p.IsSplittingField F K :=
      IntermediateField.adjoin_rootSet_isSplittingField hp_splits
    letI : FiniteDimensional F K :=
      Polynomial.IsSplittingField.finiteDimensional K p
    letI : Normal F K := Normal.of_isSplittingField p
    letI : IsGalois F K := {}
    let eKp : Gal(K/F) ≃* p.Gal := (IsSplittingField.algEquiv K p).autCongr
    letI : IsSolvable Gal(K/F) :=
      solvable_of_solvable_injective (f := eKp.toMonoidHom) eKp.injective
    let T : IntermediateField F A := K ⊔ S
    have hKT : K ≤ T := le_sup_left
    have hST : S ≤ T := le_sup_right
    let K' : IntermediateField F T := K.restrict hKT
    let S' : IntermediateField F T := S.restrict hST
    have hsup : K' ⊔ S' = ⊤ := by
      rw [← IntermediateField.lift_inj, IntermediateField.lift_top,
        IntermediateField.lift_sup, IntermediateField.lift_restrict hKT,
        IntermediateField.lift_restrict hST]
    let eKK' : K ≃ₐ[F] K' := IntermediateField.restrict_algEquiv hKT
    letI : FiniteDimensional F K' := eKK'.toLinearEquiv.finiteDimensional
    letI : IsGalois F K' := IsGalois.of_algEquiv eKK'
    letI : IsSolvable Gal(K'/F) :=
      solvable_of_surjective (f := eKK'.autCongr.toMonoidHom) eKK'.autCongr.surjective
    letI : IsGalois S' T := IsGalois.sup_right K' S' hsup
    letI : p.IsSplittingField F K' :=
      Polynomial.IsSplittingField.of_algEquiv K' p eKK'
    let p' : S'[X] := p.map (algebraMap F S')
    have hpK' : p.IsSplittingField F K' := inferInstance
    have hpT : p'.IsSplittingField S' T := by
      rw [isSplittingField_iff_intermediateField] at hpK' ⊢
      constructor
      · rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
        exact Polynomial.Splits.of_algHom hpK'.1 (IsScalarTower.toAlgHom _ _ _)
      · have hroots : p'.rootSet T = p.rootSet T := by
          simp [Set.ext_iff, Polynomial.mem_rootSet', p']
        rw [← IntermediateField.lift_inj, IntermediateField.lift_adjoin,
          ← IntermediateField.coe_val, hpK'.1.image_rootSet] at hpK'
        rw [← IntermediateField.restrictScalars_eq_top_iff (K := F),
          IntermediateField.restrictScalars_adjoin, IntermediateField.adjoin_union,
          IntermediateField.adjoin_self, hroots, hpK'.2, IntermediateField.lift_top,
          sup_comm, hsup]
    letI : p'.IsSplittingField S' T := hpT
    letI : FiniteDimensional S' T :=
      Polynomial.IsSplittingField.finiteDimensional T p'
    letI : IsSolvable Gal(T/S') :=
      solvable_of_solvable_injective
        (IntermediateField.restrictRestrictAlgEquivMapHom_injective K' S' hsup)
    have hrad : Helpers.RadicallyClosed (K := S') (E := T) := by
      intro y n hn hy
      rw [IntermediateField.mem_bot] at hy ⊢
      obtain ⟨s, hs⟩ := hy
      have hsS : ((s : T) : A) ∈ S :=
        (IntermediateField.mem_restrict hST (s : T)).mp s.2
      have hyS : ((y : T) : A) ^ n ∈ S := by
        have heq : ((s : T) : A) = ((y : T) : A) ^ n := by
          simpa using congrArg (fun z : T ↦ (z : A)) hs
        rw [← heq]
        exact hsS
      have hyS' : y ∈ S' :=
        (IntermediateField.mem_restrict hST y).mpr
          (solvableByRad.rad_mem hn hyS)
      exact ⟨⟨y, hyS'⟩, rfl⟩
    have hroots : ∀ n : ℕ, n ≠ 0 → (primitiveRoots n S').Nonempty := by
      intro n hn
      letI : NeZero n := ⟨hn⟩
      obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot A n
      have hζS : ζ ∈ S := solvableByRad.rad_mem hn <| by
        rw [hζ.pow_eq_one]
        exact one_mem S
      let ζT : T := ⟨ζ, hST hζS⟩
      let ζS' : S' :=
        ⟨ζT, (IntermediateField.mem_restrict hST ζT).mpr hζS⟩
      have hζT : IsPrimitiveRoot ζT n :=
        hζ.of_map_of_injective T.val.injective
      have hζS' : IsPrimitiveRoot ζS' n :=
        hζT.of_map_of_injective S'.val.injective
      exact ⟨ζS', (mem_primitiveRoots (Nat.pos_of_ne_zero hn)).mpr hζS'⟩
    have htriv : (⊥ : IntermediateField S' T) = ⊤ :=
      Helpers.bot_eq_top_of_isSolvable hrad hroots
    intro x hx
    have hxroot : x ∈ p.rootSet A := (mem_rootSet_of_ne _hp).mpr hx
    let xT : T := ⟨x, hKT (subset_adjoin F (p.rootSet A) hxroot)⟩
    have hxbot : xT ∈ (⊥ : IntermediateField S' T) := by
      rw [htriv]
      trivial
    obtain ⟨s, hs⟩ := IntermediateField.mem_bot.mp hxbot
    have hsS : ((s : T) : A) ∈ S :=
      (IntermediateField.mem_restrict hST (s : T)).mp s.2
    have hsx : ((s : T) : A) = x :=
      congrArg (fun z : T ↦ (z : A)) hs
    rwa [hsx] at hsS

end Submission
