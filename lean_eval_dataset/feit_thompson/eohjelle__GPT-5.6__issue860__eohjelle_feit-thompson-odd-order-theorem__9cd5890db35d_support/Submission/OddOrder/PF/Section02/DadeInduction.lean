import Submission.OddOrder.PF.Section02.DadeBasicProperties
import Submission.OddOrder.PF.Section01.InductionTransitivity

/-!
# Peterfalvi 2.5: Dade induction on normalized TI sets

For a normalized trivial-intersection set, the Dade extension of a class
function supported on that set is ordinary class-function induction.  The
proof compares the two functions pointwise and evaluates the induction sum
directly.
-/

namespace Submission.OddOrder.PF

noncomputable section

open Submission.OddOrder.MathlibSupport
open scoped BigOperators Classical Pointwise

universe u v

/-- Coq `Dade_Ind`: on a normalized TI set, the Dade map agrees with
class-function induction. -/
theorem Dade_Ind
    {Γ : Type u} [Group Γ] [Fintype Γ]
    {k : Type v} [Field k] [CharZero k]
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A)
    (hTI : IsNormalizedTI A G L)
    (alpha : ClassFunction L k)
    (halpha : alpha ∈
      ClassFunction.supportedOn {x : L | (x : Γ) ∈ A}) :
    Dade ddA alpha =
      ClassFunction.induce (L.subgroupOf G)
        (ClassFunction.toSubgroupOf L G ddA.2.1 alpha) := by
  classical
  apply ClassFunction.ext
  intro g
  let H : Subgroup G := L.subgroupOf G
  let beta : ClassFunction H k :=
    ClassFunction.toSubgroupOf L G ddA.2.1 alpha
  change Dade ddA alpha g = ClassFunction.induce H beta g
  have hsignal : ∀ ⦃a : Γ⦄, a ∈ A → DadeSignalizer ddA a = ⊥ :=
    ((Dade_normedTI_P ddA).mp hTI).2
  by_cases hex :
      ∃ x : G, (x : Γ)⁻¹ * (g : Γ) * (x : Γ) ∈ A
  · rcases hex with ⟨x₀, hx₀⟩
    let a : Γ := (x₀ : Γ)⁻¹ * (g : Γ) * (x₀ : Γ)
    have ha : a ∈ A := hx₀
    let aL : L := ⟨a, ddA.1.1 ha⟩
    have hgSupport1 : (g : Γ) ∈ Dade_support1 ddA a := by
      change ∃ z ∈
          ((DadeSignalizer ddA a : Set Γ) * ({a} : Set Γ)),
        ∃ x ∈ G, x⁻¹ * z * x = (g : Γ)
      refine ⟨a, ?_, (x₀ : Γ)⁻¹, G.inv_mem x₀.property, ?_⟩
      · exact ⟨1, (DadeSignalizer ddA a).one_mem,
          a, Set.mem_singleton a, one_mul a⟩
      · dsimp [a]
        group
    have hDade : Dade ddA alpha g = alpha aL := by
      simpa [aL] using DadeE ddA alpha ha g hgSupport1
    have hconj (y : G) :
        ((((x₀ * y)⁻¹ * g * (x₀ * y) : G) : Γ)) =
          (y : Γ)⁻¹ * a * (y : Γ) := by
      dsimp [a]
      group
    have hTI_mem (y : G) :
        ((y : Γ)⁻¹ * a * (y : Γ) ∈ A ↔ (y : Γ) ∈ L) :=
      (isNormalizedTI_iff_mem_conj.mp hTI).2.2 ha y.property
    have hsumReindexed :
        (∑ y : G,
            ClassFunction.inductionKernel H beta (x₀ * y) g) =
          ∑ _y : H, alpha aL := by
      apply Finset.sum_congr_set (H : Set G)
        (fun y : G ↦
          ClassFunction.inductionKernel H beta (x₀ * y) g)
        (fun _y : H ↦ alpha aL)
      · intro y hy
        have hyL : (y : Γ) ∈ L := by
          change (y : Γ) ∈ L at hy
          exact hy
        have hmem : (x₀ * y)⁻¹ * g * (x₀ * y) ∈ H := by
          change ((((x₀ * y)⁻¹ * g * (x₀ * y) : G) : Γ)) ∈ L
          rw [hconj y]
          exact L.mul_mem (L.mul_mem (L.inv_mem hyL) (ddA.1.1 ha)) hyL
        rw [ClassFunction.inductionKernel_of_mem H beta
          (x₀ * y) g hmem]
        rw [ClassFunction.toSubgroupOf_apply]
        let yL : L := ⟨(y : Γ), hyL⟩
        have harg :
            Subgroup.subgroupOfEquivOfLe ddA.2.1
                (⟨(x₀ * y)⁻¹ * g * (x₀ * y), hmem⟩ : H) =
              yL⁻¹ * aL * yL := by
          apply Subtype.ext
          exact hconj y
        rw [harg]
        simpa using ClassFunction.conj_apply alpha yL⁻¹ aL
      · intro y hy
        by_cases hmem : (x₀ * y)⁻¹ * g * (x₀ * y) ∈ H
        · rw [ClassFunction.inductionKernel_of_mem H beta
            (x₀ * y) g hmem]
          rw [ClassFunction.toSubgroupOf_apply]
          apply ClassFunction.eq_zero_of_mem_supportedOn halpha
          change ((((x₀ * y)⁻¹ * g * (x₀ * y) : G) : Γ)) ∉ A
          rw [hconj y]
          intro hya
          apply hy
          change (y : Γ) ∈ L
          exact (hTI_mem y).mp hya
        · exact ClassFunction.inductionKernel_of_notMem H beta
            (x₀ * y) g hmem
    have hreindex :
        (∑ x : G, ClassFunction.inductionKernel H beta x g) =
          ∑ y : G,
            ClassFunction.inductionKernel H beta (x₀ * y) g := by
      symm
      exact Fintype.sum_equiv (Equiv.mulLeft x₀)
        (fun y : G ↦ ClassFunction.inductionKernel H beta (x₀ * y) g)
        (fun x : G ↦ ClassFunction.inductionKernel H beta x g)
        (fun _ ↦ rfl)
    have hsum :
        (∑ x : G, ClassFunction.inductionKernel H beta x g) =
          Nat.card H • alpha aL := by
      rw [hreindex, hsumReindexed, Finset.sum_const, Finset.card_univ,
        ← Nat.card_eq_fintype_card]
    rw [hDade]
    change alpha aL =
      (Nat.card H : k)⁻¹ *
        ∑ x : G, ClassFunction.inductionKernel H beta x g
    rw [hsum,
      ← Nat.cast_smul_eq_nsmul k, smul_eq_mul, ← mul_assoc,
      inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Nat.card_pos.ne'), one_mul]
  · have hgSupport : (g : Γ) ∉ Dade_support ddA := by
      rintro ⟨a, ha, hga⟩
      change ∃ z ∈
          ((DadeSignalizer ddA a : Set Γ) * ({a} : Set Γ)),
        ∃ x ∈ G, x⁻¹ * z * x = (g : Γ) at hga
      rcases hga with ⟨z, hz, x, hxG, hxz⟩
      rcases Set.mem_mul.mp hz with ⟨s, hs, b, hb, hsb⟩
      have hsOne : s = 1 := by
        rw [hsignal ha] at hs
        simpa using hs
      have hbA : b = a := Set.mem_singleton_iff.mp hb
      subst s
      subst b
      simp only [one_mul] at hsb
      subst z
      have hback : x * (g : Γ) * x⁻¹ = a := by
        rw [← hxz]
        group
      apply hex
      refine ⟨⟨x⁻¹, G.inv_mem hxG⟩, ?_⟩
      simpa only [Subgroup.coe_mk, inv_inv] using (hback.symm ▸ ha)
    have hsumZero :
        (∑ x : G, ClassFunction.inductionKernel H beta x g) = 0 := by
      apply Finset.sum_eq_zero
      intro x _hx
      by_cases hxH : x⁻¹ * g * x ∈ H
      · rw [ClassFunction.inductionKernel_of_mem H beta x g hxH]
        rw [ClassFunction.toSubgroupOf_apply]
        apply ClassFunction.eq_zero_of_mem_supportedOn halpha
        change (x : Γ)⁻¹ * (g : Γ) * (x : Γ) ∉ A
        exact fun hxA ↦ hex ⟨x, hxA⟩
      · exact ClassFunction.inductionKernel_of_notMem H beta x g hxH
    rw [Dade_eq_zero_of_not_mem ddA alpha g hgSupport]
    change 0 = (Nat.card H : k)⁻¹ *
      ∑ x : G, ClassFunction.inductionKernel H beta x g
    rw [hsumZero, mul_zero]

end

end Submission.OddOrder.PF
