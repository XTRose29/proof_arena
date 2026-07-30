import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.CharP.Algebra
import Mathlib.RepresentationTheory.Invariants
import Submission.OddOrder.MathlibSupport.PGroupCenter

/-!
Nonzero invariant vectors for finite `p`-groups in characteristic `p`.
-/

namespace Submission.OddOrder.MathlibSupport

universe u v w

variable {F : Type v} {G : Type u} {V : Type w}
  [Field F] [Group G] [Finite G]
  [AddCommGroup V] [Module F V] [FiniteDimensional F V] [Nontrivial V]

/-- A finite `p`-group acting on a nonzero finite-dimensional vector space in
characteristic `p` has a nonzero common fixed vector. -/
theorem invariants_ne_bot_of_isPGroup_charP
    {p : ℕ} [CharP F p] [Fact p.Prime]
    (rho : Representation F G V) (hG : IsPGroup p G) :
    rho.invariants ≠ ⊥ := by
  classical
  let P : ℕ → Prop := fun n ↦
    ∀ (K : Type u) [Group K] [Finite K], Nat.card K = n →
      ∀ (W : Type w) [AddCommGroup W] [Module F W]
        [FiniteDimensional F W] [Nontrivial W],
        (sigma : Representation F K W) → IsPGroup p K →
          sigma.invariants ≠ ⊥
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        dsimp only [P]
        intro K _ _ hcard W _ _ _ _ sigma hK
        by_cases hnontriv : Nontrivial K
        · letI : Nontrivial K := hnontriv
          have hcenterP : IsPGroup p (Subgroup.center K) :=
            hK.to_subgroup (Subgroup.center K)
          letI : Nontrivial (Subgroup.center K) := hK.center_nontrivial
          obtain ⟨m, hm, hcenterCard⟩ :=
            hcenterP.nontrivial_iff_card.mp inferInstance
          have hpcenter : p ∣ Nat.card (Subgroup.center K) := by
            rw [hcenterCard]
            exact dvd_pow_self p hm.ne'
          obtain ⟨z, hzorder⟩ :=
            exists_prime_orderOf_dvd_card'
              (G := Subgroup.center K) p hpcenter
          let zK : K := z
          have hzorderK : orderOf zK = p :=
            (Subgroup.orderOf_coe z).trans hzorder
          have hzpow : zK ^ p = 1 :=
            (congrArg (fun r : ℕ ↦ zK ^ r) hzorderK).symm.trans
              (pow_orderOf_eq_one zK)
          have hzne : zK ≠ 1 := by
            intro hz
            apply (Fact.out : p.Prime).ne_one
            rw [← hzorderK, hz, orderOf_one]
          let C : Subgroup K := Subgroup.zpowers zK
          have hCcenter : C ≤ Subgroup.center K :=
            Subgroup.zpowers_le.mpr z.property
          have hCne : C ≠ ⊥ := by
            simpa [C, Subgroup.zpowers_eq_bot] using hzne
          letI : C.Normal := by
            constructor
            intro c hc k
            have hck := Subgroup.mem_center_iff.mp (hCcenter hc) k
            simpa [hck] using hc
          letI : CharP (Module.End F W) p :=
            charP_of_injective_algebraMap
              (FaithfulSMul.algebraMap_injective F (Module.End F W)) p
          let T : Module.End F W := sigma zK - 1
          have hTpow : T ^ p = 0 := by
            dsimp only [T]
            rw [sub_pow_char_of_commute, one_pow, ← map_pow, hzpow,
              map_one, sub_self]
            exact Commute.one_right (sigma zK)
          have hker : LinearMap.ker T ≠ ⊥ := by
            intro hker
            have hTin : Function.Injective T :=
              LinearMap.ker_eq_bot.mp hker
            have hpowInj : ∀ r : ℕ, Function.Injective (T ^ r) := by
              intro r
              induction r with
              | zero =>
                  intro a b hab
                  simpa using hab
              | succ r ihr =>
                  rw [pow_succ]
                  exact ihr.comp hTin
            have hzero : Function.Injective (0 : Module.End F W) := by
              simpa [hTpow] using hpowInj p
            obtain ⟨w, hw⟩ := exists_ne (0 : W)
            apply hw
            apply hzero
            simp
          let zC : C := ⟨zK, Subgroup.mem_zpowers zK⟩
          have hCcyclic : ∀ c : C, c ∈ Subgroup.zpowers zC := by
            intro c
            rcases c.property with ⟨r, hr⟩
            exact ⟨r, Subtype.ext hr⟩
          let sigmaC : Representation F C W := sigma.comp C.subtype
          have hker_le : LinearMap.ker T ≤ sigmaC.invariants := by
            intro w hw
            rw [Representation.mem_invariants_iff_of_forall_mem_zpowers
              sigmaC zC hCcyclic w]
            have hw0 := LinearMap.mem_ker.mp hw
            change (sigma zK - 1) w = 0 at hw0
            simpa [sigmaC, zC, sub_eq_zero] using hw0
          have hfixedC : sigmaC.invariants ≠ ⊥ := by
            intro hbot
            apply hker
            apply le_antisymm
            · intro w hw
              have hwC := hker_le hw
              rw [hbot] at hwC
              simpa using hwC
            · exact bot_le
          letI : Nontrivial sigmaC.invariants :=
            Submodule.nontrivial_iff_ne_bot.mpr hfixedC
          let tau := sigma.quotientToInvariants C
          have hquotP : IsPGroup p (K ⧸ C) := hK.to_quotient C
          have hquotlt : Nat.card (K ⧸ C) < n := by
            rw [← hcard]
            have hCcard : 1 < Nat.card C :=
              (Subgroup.one_lt_card_iff_ne_bot C).mpr hCne
            calc
              Nat.card (K ⧸ C) < Nat.card (K ⧸ C) * Nat.card C :=
                lt_mul_of_one_lt_right
                  (Nat.card_pos : 0 < Nat.card (K ⧸ C)) hCcard
              _ = Nat.card K :=
                (Subgroup.card_eq_card_quotient_mul_card_subgroup C).symm
          have htau : tau.invariants ≠ ⊥ :=
            ih (Nat.card (K ⧸ C)) hquotlt (K ⧸ C) rfl
              sigmaC.invariants tau hquotP
          letI : Nontrivial tau.invariants :=
            Submodule.nontrivial_iff_ne_bot.mpr htau
          obtain ⟨x, hx⟩ := exists_ne (0 : tau.invariants)
          let y : sigma.invariants := ⟨x.1.1, fun k ↦ by
            have hxk := x.2 (QuotientGroup.mk' C k)
            change sigma.toInvariants C k x.1 = x.1 at hxk
            exact congrArg Subtype.val hxk⟩
          have hy : y ≠ 0 := by
            intro hy0
            apply hx
            have hyW : x.1.1 = 0 := by
              change (y : W) = 0
              exact congrArg Subtype.val hy0
            exact Subtype.ext (Subtype.ext hyW)
          exact Submodule.nontrivial_iff_ne_bot.mp ⟨⟨y, 0, hy⟩⟩
        · haveI : Subsingleton K := not_nontrivial_iff_subsingleton.mp hnontriv
          letI : sigma.IsTrivial := ⟨fun k ↦ by
            ext w
            simp [Subsingleton.elim k 1]⟩
          rw [sigma.invariants_eq_top]
          exact top_ne_bot
  exact hP (Nat.card G) G rfl V rho hG

end Submission.OddOrder.MathlibSupport
