import Submission.OddOrder.MathlibSupport.SubgroupConjugationQuotientAction
import Mathlib.GroupTheory.Commutator.Basic

/-!
Conjugation actions on subgroup factors and their kernels.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped commutatorElement

variable {G : Type*} [Group G]

/-- If `H` normalizes both `E` and `M`, its conjugation action on `E`
descends to the quotient by `M ∩ E`. -/
theorem subgroupConjugationFactorQuotientAction
    (M E H : Subgroup G)
    (hHE : H ≤ Subgroup.normalizer (E : Set G))
    (hHM : H ≤ Subgroup.normalizer (M : Set G)) :
    letI := subgroupConjugationAction E H hHE
    MulAction.QuotientAction H (M.subgroupOf E) := by
  letI := subgroupConjugationAction E H hHE
  refine ⟨?_⟩
  intro g e e' hee'
  change (e : G)⁻¹ * (e' : G) ∈ M at hee'
  change ((((g • e)⁻¹ * g • e' : E) : G)) ∈ M
  have hcoe : ((((g • e)⁻¹ * g • e' : E) : G)) =
      (g : G) * ((e : G)⁻¹ * (e' : G)) * (g : G)⁻¹ := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv,
      coe_subgroupConjugationAction_smul E H hHE,
      coe_subgroupConjugationAction_smul E H hHE]
    group
  rw [hcoe]
  exact (hHM g.property ((e : G)⁻¹ * (e' : G))).mp hee'

/-- The conjugation homomorphism induced by `H` on the factor `E/(M ∩ E)`. -/
noncomputable def subgroupConjugationFactorHom
    (M E H : Subgroup G) [(M.subgroupOf E).Normal]
    (hHE : H ≤ Subgroup.normalizer (E : Set G))
    (hHM : H ≤ Subgroup.normalizer (M : Set G)) :
    H →* MulAut (E ⧸ M.subgroupOf E) := by
  letI := subgroupConjugationAction E H hHE
  letI : MulAction.QuotientAction H (M.subgroupOf E) :=
    subgroupConjugationFactorQuotientAction M E H hHE hHM
  letI : MulDistribMulAction H (E ⧸ M.subgroupOf E) :=
    (QuotientGroup.mk'_surjective (M.subgroupOf E)).mulDistribMulAction
      (QuotientGroup.mk' (M.subgroupOf E)) (fun _ _ ↦ rfl)
  exact MulDistribMulAction.toMulAut H (E ⧸ M.subgroupOf E)

@[simp]
theorem subgroupConjugationFactorHom_apply_mk
    (M E H : Subgroup G) [(M.subgroupOf E).Normal]
    (hHE : H ≤ Subgroup.normalizer (E : Set G))
    (hHM : H ≤ Subgroup.normalizer (M : Set G))
    (g : H) (e : E) :
    subgroupConjugationFactorHom M E H hHE hHM g
        (QuotientGroup.mk' (M.subgroupOf E) e) =
      QuotientGroup.mk' (M.subgroupOf E)
        ⟨(g : G) * (e : G) * (g : G)⁻¹,
          (hHE g.property e).mp e.property⟩ :=
  rfl

/-- An element is in the kernel of the factor action exactly when all of its
commutators with `E` lie in `M`. -/
theorem mem_ker_subgroupConjugationFactorHom_iff
    (M E H : Subgroup G) [(M.subgroupOf E).Normal]
    (hHE : H ≤ Subgroup.normalizer (E : Set G))
    (hHM : H ≤ Subgroup.normalizer (M : Set G))
    (g : H) :
    g ∈ (subgroupConjugationFactorHom M E H hHE hHM).ker ↔
      ∀ e : G, e ∈ E → ⁅(g : G), e⁆ ∈ M := by
  constructor
  · intro hg e he
    let eE : E := ⟨e, he⟩
    have haction := DFunLike.congr_fun (MonoidHom.mem_ker.mp hg)
      (QuotientGroup.mk' (M.subgroupOf E) eE)
    have hcommE : ⁅(g : G), e⁆ ∈ E := by
      exact E.mul_mem ((hHE g.property e).mp he) (E.inv_mem he)
    have hcommOne :
        QuotientGroup.mk' (M.subgroupOf E) ⟨⁅(g : G), e⁆, hcommE⟩ = 1 := by
      calc
        QuotientGroup.mk' (M.subgroupOf E) ⟨⁅(g : G), e⁆, hcommE⟩ =
            QuotientGroup.mk' (M.subgroupOf E)
                ⟨(g : G) * e * (g : G)⁻¹,
                  (hHE g.property e).mp he⟩ *
              (QuotientGroup.mk' (M.subgroupOf E) eE)⁻¹ := by
                rw [← map_inv, ← map_mul]
                congr 1
        _ = 1 := by
          rw [← subgroupConjugationFactorHom_apply_mk
            M E H hHE hHM g eE, haction]
          simp
    exact (QuotientGroup.eq_one_iff
      (N := M.subgroupOf E) (⟨⁅(g : G), e⁆, hcommE⟩ : E)).mp hcommOne
  · intro hcomm
    rw [MonoidHom.mem_ker]
    ext z
    obtain ⟨e, rfl⟩ := QuotientGroup.mk'_surjective (M.subgroupOf E) z
    have hcommE : ⁅(g : G), (e : G)⁆ ∈ E := by
      exact E.mul_mem ((hHE g.property (e : G)).mp e.property)
        (E.inv_mem e.property)
    have hcommOne :
        QuotientGroup.mk' (M.subgroupOf E)
          ⟨⁅(g : G), (e : G)⁆, hcommE⟩ = 1 :=
      (QuotientGroup.eq_one_iff
        (N := M.subgroupOf E)
        (⟨⁅(g : G), (e : G)⁆, hcommE⟩ : E)).mpr
          (hcomm e e.property)
    calc
      subgroupConjugationFactorHom M E H hHE hHM g
          (QuotientGroup.mk' (M.subgroupOf E) e) =
          QuotientGroup.mk' (M.subgroupOf E)
            ⟨(g : G) * (e : G) * (g : G)⁻¹,
              (hHE g.property e).mp e.property⟩ :=
        subgroupConjugationFactorHom_apply_mk M E H hHE hHM g e
      _ = QuotientGroup.mk' (M.subgroupOf E)
            ⟨⁅(g : G), (e : G)⁆, hcommE⟩ *
          QuotientGroup.mk' (M.subgroupOf E) e := by
            rw [← map_mul]
            congr 1
            apply Subtype.ext
            change (g : G) * (e : G) * (g : G)⁻¹ =
              ((g : G) * (e : G) * (g : G)⁻¹ * (e : G)⁻¹) * (e : G)
            group
      _ = QuotientGroup.mk' (M.subgroupOf E) e := by rw [hcommOne]; simp
      _ = (1 : MulAut (E ⧸ M.subgroupOf E))
          (QuotientGroup.mk' (M.subgroupOf E) e) := by simp

/-- The factor action is trivial precisely when the acting subgroup
centralizes `E` modulo `M`. -/
theorem subgroupConjugationFactorHom_ker_eq_top_iff
    (M E H : Subgroup G) [(M.subgroupOf E).Normal]
    (hHE : H ≤ Subgroup.normalizer (E : Set G))
    (hHM : H ≤ Subgroup.normalizer (M : Set G)) :
    (subgroupConjugationFactorHom M E H hHE hHM).ker = ⊤ ↔
      ⁅H, E⁆ ≤ M := by
  rw [Subgroup.eq_top_iff']
  constructor
  · intro hker
    apply Subgroup.commutator_le.mpr
    intro g hg e he
    exact (mem_ker_subgroupConjugationFactorHom_iff
      M E H hHE hHM ⟨g, hg⟩).mp (hker ⟨g, hg⟩) e he
  · intro hcomm g
    apply (mem_ker_subgroupConjugationFactorHom_iff
      M E H hHE hHM g).mpr
    intro e he
    exact Subgroup.commutator_le.mp hcomm (g : G) g.property e he

end Submission.OddOrder.MathlibSupport
