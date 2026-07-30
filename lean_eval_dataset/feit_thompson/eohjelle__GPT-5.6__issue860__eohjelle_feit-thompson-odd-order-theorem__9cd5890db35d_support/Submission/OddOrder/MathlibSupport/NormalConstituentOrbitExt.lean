import Submission.OddOrder.MathlibSupport.NormalConstituentOrbit

/-!
Linear-map extensionality on the ambient orbit of a normal constituent.
-/

namespace Submission.OddOrder.MathlibSupport

universe u v w x

variable {k : Type u} {G : Type v} {V : Type w} {W : Type x}
variable [Field k] [Group G] [Finite G]
variable [AddCommGroup V] [Module k V]
variable [AddCommGroup W] [Module k W]

/-- In an irreducible ambient representation, two linear maps are equal if
they agree on every ambient translate of one nonzero normal constituent. -/
theorem LinearMap.eq_of_eqOn_normalConstituentOrbit
    (rho : Representation k G V) [Representation.IsIrreducible rho]
    (N : Subgroup G) [N.Normal]
    (U : Subrepresentation (rho.comp N.subtype)) (hU : U ≠ ⊥)
    (f g : V →ₗ[k] W)
    (hfg : ∀ z : G,
      ∀ u : (conjugateNormalSubrepresentation rho N z U).toSubmodule,
        f u = g u) :
    f = g := by
  classical
  letI := Fintype.ofFinite G
  have htranslate (z : G) :
      (conjugateNormalSubrepresentation rho N z U).toSubmodule ≤
        LinearMap.ker (f - g) := by
    intro v hv
    rw [LinearMap.mem_ker]
    simp only [LinearMap.sub_apply, sub_eq_zero]
    exact hfg z ⟨v, hv⟩
  have hfinset (s : Finset G) :
      (s.sup fun z ↦ conjugateNormalSubrepresentation rho N z U).toSubmodule ≤
        LinearMap.ker (f - g) := by
    induction s using Finset.induction_on with
    | empty => exact bot_le
    | insert z s hz ih =>
        simp only [Finset.sup_insert, Subrepresentation.toSubmodule_sup]
        exact sup_le (htranslate z) ih
  have horbit_ker :
      (normalConstituentOrbitSup rho N U).toSubmodule ≤
        LinearMap.ker (f - g) := by
    rw [normalConstituentOrbitSup]
    exact hfinset Finset.univ
  rw [normalConstituentOrbitSup_eq_top rho N U hU] at horbit_ker
  ext v
  have hv := horbit_ker (Submodule.mem_top : v ∈ (⊤ : Submodule k V))
  rw [LinearMap.mem_ker] at hv
  exact sub_eq_zero.mp hv

end Submission.OddOrder.MathlibSupport
