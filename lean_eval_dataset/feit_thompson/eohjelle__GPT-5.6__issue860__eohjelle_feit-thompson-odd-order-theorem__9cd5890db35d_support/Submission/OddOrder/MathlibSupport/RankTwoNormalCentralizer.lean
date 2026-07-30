import Submission.OddOrder.BG.Section04.RankTwoChiefFactorCentralizer
import Submission.OddOrder.MathlibSupport.MinimalNormalExistence
import Submission.OddOrder.MathlibSupport.StableFactor

/-!
# Rank-two normal subgroups and coprime centralization

If a normal subgroup has no elementary-abelian subgroup of rank three at
any prime, the ambient derived subgroup centralizes all of its chief
factors.  A subgroup of the derived subgroup whose order is coprime to the
normal subgroup therefore centralizes the normal subgroup itself.
-/

namespace Submission.OddOrder.MathlibSupport

open Submission.OddOrder.BG.Section04

universe u

/-- A coprime subgroup of the ambient derived group centralizes a normal
subgroup having no elementary-abelian subgroup of rank three at any prime.

This is the chief-series/stable-factor step used in `BGsection9.v`, in the
proof of Bender--Glauberman Lemma 9.5. -/
theorem le_centralizer_of_le_commutator_of_no_rank_three
    {X : Type u} [Group X] [Finite X]
    (hodd : Odd (Nat.card X)) (hsol : IsSolvable X)
    {N K : Subgroup X} (hNnormal : N.Normal)
    (hRank : ∀ q : ℕ, q.Prime →
      ¬ ∃ E : Subgroup N, IsElementaryAbelianOfRank q 3 E)
    (hKder : K ≤ _root_.commutator X)
    (hcop : Nat.Coprime (Nat.card N) (Nat.card K)) :
    K ≤ Subgroup.centralizer (N : Set X) := by
  classical
  letI : IsSolvable X := hsol
  let Good : Subgroup X → Prop := fun V ↦
    V.Normal ∧ V ≤ N ∧ K ≤ Subgroup.centralizer (V : Set X)
  have hbot : Good (⊥ : Subgroup X) := by
    refine ⟨by infer_instance, bot_le, ?_⟩
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [Subgroup.mem_bot.mp hx]
    exact Commute.one_left k
  obtain ⟨V, _hbotV, hVgood, hVmax⟩ :=
    Finite.exists_le_maximal (p := Good) hbot
  letI : V.Normal := hVgood.1
  have hVN : V = N := by
    apply le_antisymm hVgood.2.1
    by_contra hNV
    have hVltN : V < N :=
      lt_of_le_of_ne hVgood.2.1 (fun hEq ↦ hNV hEq.ge)
    obtain ⟨W, hchief, hWN⟩ :=
      exists_chiefFactor_le hVltN hNnormal
    obtain ⟨q, hq, hfactor, _hpow⟩ :=
      hchief.exists_prime_isPGroup_pow_eq_one
    letI : Fact q.Prime := ⟨hq⟩
    have hderW :
        ⁅(_root_.commutator X), W⁆ ≤ V :=
      rank2_der1_cent_chief
        (G := X) (p := q) (Gs := N) (U := W) (V := V)
        hodd hsol hNnormal (hRank q hq) hchief hfactor hWN
    have hKW : ⁅K, W⁆ ≤ V :=
      (Subgroup.commutator_mono hKder le_rfl).trans hderW
    have hcopW : Nat.Coprime (Nat.card W) (Nat.card K) :=
      hcop.coprime_dvd_left (Subgroup.card_dvd_of_le hWN)
    have hKcentW : K ≤ Subgroup.centralizer (W : Set X) :=
      stableFactor_centralizes hVgood.2.2 hchief.le hKW hcopW
    have hWgood : Good W :=
      ⟨hchief.upper_normal, hWN, hKcentW⟩
    have hWV : W ≤ V := hVmax hWgood hchief.le
    exact (not_le_of_gt hchief.lt) hWV
  simpa [hVN] using hVgood.2.2

end Submission.OddOrder.MathlibSupport
