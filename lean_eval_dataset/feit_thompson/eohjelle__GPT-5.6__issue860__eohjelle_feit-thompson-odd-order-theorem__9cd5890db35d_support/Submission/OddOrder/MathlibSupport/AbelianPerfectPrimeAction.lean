import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Submission.OddOrder.MathlibSupport.PrimeOrderCentralizer
import Submission.OddOrder.MathlibSupport.SubgroupConjugationQuotientAction

/-!
An abelian kernel with perfect prime-order coprime action is fixed-point-free.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped commutatorElement Pointwise

universe u

variable {G : Type u} [Group G] [Finite G]
variable {K R : Subgroup G}

/-- If an abelian normal factor satisfies `[R,K] = K` for a prime-order
complement, every nonidentity element of the complement fixes only the
identity in `K`. -/
theorem fixed_eq_one_of_abelian_perfect_prime_action
    [IsMulCommutative K]
    (hnormK : R ≤ Subgroup.normalizer (K : Set G))
    (hRprime : (Nat.card R).Prime)
    (hperfect : ⁅R, K⁆ = K)
    (r : R) (hr : r ≠ 1) (k : K)
    (hfix : (r : G) * (k : G) * (r : G)⁻¹ = (k : G)) :
    k = 1 := by
  classical
  letI : MulDistribMulAction R K :=
    subgroupConjugationAction K R hnormK
  let phi : K →* K := MulDistribMulAction.toMonoidHom K r
  let delta : K →* K :=
    { toFun := fun x ↦ x / phi x
      map_one' := by simp
      map_mul' := by
        intro x y
        simp only [map_mul, div_eq_mul_inv, mul_inv_rev]
        ac_rfl }
  let D : Subgroup G := delta.range.map K.subtype
  have hphi (x : K) :
      ((phi x : K) : G) = (r : G) * (x : G) * (r : G)⁻¹ := by
    exact coe_subgroupConjugationAction_smul K R hnormK r x
  have hdelta (x : K) :
      ((delta x : K) : G) = ⁅(x : G), (r : G)⁆ := by
    dsimp [delta]
    rw [hphi]
    simp [div_eq_mul_inv, commutatorElement_def, mul_assoc]
  have hdelta_mem (x : K) : ((delta x : K) : G) ∈ D :=
    ⟨delta x, ⟨x, rfl⟩, rfl⟩
  have hmapD : D.map (MulAut.conj (r : G)) ≤ D := by
    intro z hz
    rcases hz with ⟨d, hd, rfl⟩
    rcases hd with ⟨dK, ⟨x, hx⟩, hdK⟩
    subst dK
    subst d
    refine ⟨delta (phi x), ⟨phi x, rfl⟩, ?_⟩
    change ((delta (phi x) : K) : G) =
      (r : G) * ((delta x : K) : G) * (r : G)⁻¹
    rw [hdelta, hdelta, conjugate_commutatorElement, hphi]
    simp
  have hrnormD : (r : G) ∈ Subgroup.normalizer (D : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    apply Subgroup.eq_of_le_of_card_ge hmapD
    have hc : Nat.card (D.map (MulAut.conj (r : G)).toMonoidHom) = Nat.card D := by
      exact Subgroup.card_map_of_injective
        (f := (MulAut.conj (r : G)).toMonoidHom)
        (MulAut.conj (r : G)).injective
    exact hc.ge
  have hbasic (x : K) : ⁅(r : G), (x : G)⁆ ∈ D := by
    have hx := D.inv_mem (hdelta_mem x)
    rw [hdelta, commutatorElement_inv] at hx
    exact hx
  have hbasicInv (x : K) : ⁅(r : G)⁻¹, (x : G)⁆ ∈ D := by
    rw [commutatorElement_inv_left]
    have hx : ⁅(x : G), (r : G)⁆ ∈ D := by
      rw [← hdelta]
      exact hdelta_mem x
    simpa only [inv_inv] using (Subgroup.mem_normalizer_iff.mp
      ((Subgroup.normalizer (D : Set G)).inv_mem hrnormD) _).mp hx
  have hpow (z : ℤ) (x : K) :
      ⁅(r : G) ^ z, (x : G)⁆ ∈ D := by
    induction z using Int.induction_on with
    | zero => simp
    | succ n ih =>
        rw [zpow_add_one, commutatorElement_mul_left_eq_conj_mul]
        apply D.mul_mem
        · exact (Subgroup.mem_normalizer_iff.mp
            ((Subgroup.normalizer (D : Set G)).zpow_mem hrnormD n) _).mp
              (hbasic x)
        · exact ih
    | pred n ih =>
        rw [sub_eq_add_neg, zpow_add, zpow_neg_one]
        rw [commutatorElement_mul_left_eq_conj_mul]
        apply D.mul_mem
        · exact (Subgroup.mem_normalizer_iff.mp
            ((Subgroup.normalizer (D : Set G)).zpow_mem hrnormD (-(n : ℤ))) _).mp
              (hbasicInv x)
        · exact ih
  have hRz : Subgroup.zpowers (r : G) = R :=
    zpowers_eq_of_mem_subgroup_prime_card R hRprime r.property (by
      intro h
      apply hr
      exact Subtype.ext h)
  have hcomm_le : ⁅R, K⁆ ≤ D := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [← hRz] at ha
    rcases ha with ⟨z, rfl⟩
    exact hpow z ⟨b, hb⟩
  have hD_le : D ≤ ⁅R, K⁆ := by
    rintro d ⟨dK, ⟨x, hx⟩, rfl⟩
    subst dK
    change ((delta x : K) : G) ∈ ⁅R, K⁆
    rw [hdelta, Subgroup.commutator_comm R K]
    exact Subgroup.commutator_mem_commutator x.property r.property
  have hDK : D = K := by
    calc
      D = ⁅R, K⁆ := le_antisymm hD_le hcomm_le
      _ = K := hperfect
  have hrange : delta.range = ⊤ := by
    apply Subgroup.map_injective K.subtype_injective
    calc
      delta.range.map K.subtype = K := by simpa [D] using hDK
      _ = K.subtype.range := K.range_subtype.symm
      _ = (⊤ : Subgroup K).map K.subtype := by
        ext g
        simp
  have hdeltaSurj : Function.Surjective delta :=
    MonoidHom.range_eq_top.mp hrange
  have hdeltaInj : Function.Injective delta :=
    Finite.injective_iff_surjective.mpr hdeltaSurj
  apply hdeltaInj
  have hfixK : r • k = k := Subtype.ext hfix
  have hk : delta k = 1 := by
    change k / (r • k) = 1
    rw [hfixK]
    simp
  simpa using hk

end Submission.OddOrder.MathlibSupport
