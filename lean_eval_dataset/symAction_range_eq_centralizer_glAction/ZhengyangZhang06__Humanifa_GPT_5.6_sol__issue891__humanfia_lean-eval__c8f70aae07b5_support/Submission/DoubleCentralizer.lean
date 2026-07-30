import ChallengeDeps
import Mathlib.RepresentationTheory.Maschke
import Mathlib.RepresentationTheory.Intertwining
import Mathlib.RingTheory.Finiteness.Basic

open scoped MonoidAlgebra TensorProduct

namespace Submission.DoubleCentralizer

open Function

private theorem asAlgebraHom_mem_adjoin
    {K G V : Type*} [Field K] [Group G] [AddCommGroup V] [Module K V]
    (ρ : Representation K G V) (a : MonoidAlgebra K G) :
    ρ.asAlgebraHom a ∈ Algebra.adjoin K (Set.range ρ) := by
  apply MonoidAlgebra.induction_on a
  · intro g
    apply Algebra.subset_adjoin
    exact ⟨g, by simp⟩
  · intro x y hx hy
    simpa only [map_add] using
      (Algebra.adjoin K (Set.range ρ)).add_mem hx hy
  · intro r x hx
    simpa only [map_smul] using
      (Algebra.adjoin K (Set.range ρ)).smul_mem hx r

/-- Finite-dimensional Maschke modules satisfy the double-centralizer theorem. -/
theorem adjoin_range_eq_doubleCentralizer
    {K G V : Type*} [Field K] [Group G] [Finite G]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [NeZero (Nat.card G : K)] (ρ : Representation K G V) :
    Algebra.adjoin K (Set.range ρ) =
      Subalgebra.centralizer K
        (Subalgebra.centralizer K (Set.range ρ) :
          Set (Module.End K V)) := by
  apply le_antisymm
  · exact Algebra.adjoin_le_centralizer_centralizer K (Set.range ρ)
  · intro z hz
    let W := ρ.asModule
    let B := Module.End K[G] W
    let e : W ≃ₗ[K] V := ρ.asModuleEquiv
    haveI : Module.Finite B W :=
      Module.Finite.of_restrictScalars_finite K B W
    let F : Module.End B W :=
      { toFun := fun x ↦ e.symm (z (e x))
        map_add' := by
          intro x y
          simp
        map_smul' := by
          intro b x
          let bV : Module.End K V :=
            { toFun := fun v ↦ e (b (e.symm v))
              map_add' := by intro u v; simp
              map_smul' := by
                intro r v
                calc
                  e (b (r • e.symm v)) =
                      e (b (algebraMap K K[G] r • e.symm v)) := by
                        rw [algebraMap_smul]
                  _ = e (algebraMap K K[G] r • b (e.symm v)) := by
                        rw [b.map_smul]
                  _ = e (r • b (e.symm v)) := by
                        rw [algebraMap_smul]
                  _ = r • e (b (e.symm v)) := by
                        rw [map_smul] }
          have hbV :
              bV ∈ Subalgebra.centralizer K (Set.range ρ) := by
            rw [Subalgebra.mem_centralizer_iff]
            rintro _ ⟨g, rfl⟩
            ext v
            apply e.symm.injective
            change ρ.asModuleEquiv.symm
                (ρ g (ρ.asModuleEquiv (b (ρ.asModuleEquiv.symm v)))) =
              ρ.asModuleEquiv.symm
                (ρ.asModuleEquiv (b (ρ.asModuleEquiv.symm (ρ g v))))
            simpa only [LinearEquiv.symm_apply_apply,
              Representation.asModuleEquiv_symm_map_rho] using
              (b.map_smul (MonoidAlgebra.of K G g) (e.symm v)).symm
          have hcomm : bV * z = z * bV :=
            (Subalgebra.mem_centralizer_iff K).mp hz bV hbV
          apply e.injective
          change z (e (b x)) = e (b (e.symm (z (e x))))
          calc
            z (e (b x)) = z (bV (e x)) := by
              congr 1
            _ = bV (z (e x)) := by
              simpa only [Module.End.mul_apply] using
                congrArg (fun q : Module.End K V ↦ q (e x)) hcomm.symm
            _ = e (b (e.symm (z (e x)))) := rfl }
    obtain ⟨a, ha⟩ :=
      Module.Finite.toModuleEnd_moduleEnd_surjective (R := K[G]) (M := W) F
    have hza : z = ρ.asAlgebraHom a := by
      ext v
      have hav :=
        LinearMap.congr_fun ha (e.symm v)
      change a • ρ.asModuleEquiv.symm v =
        ρ.asModuleEquiv.symm
          (z (ρ.asModuleEquiv (ρ.asModuleEquiv.symm v))) at hav
      have hev := congrArg ρ.asModuleEquiv hav
      simpa only [LinearEquiv.apply_symm_apply,
        Representation.asModuleEquiv_map_smul] using hev.symm
    rw [hza]
    exact asAlgebraHom_mem_adjoin ρ a

end Submission.DoubleCentralizer
