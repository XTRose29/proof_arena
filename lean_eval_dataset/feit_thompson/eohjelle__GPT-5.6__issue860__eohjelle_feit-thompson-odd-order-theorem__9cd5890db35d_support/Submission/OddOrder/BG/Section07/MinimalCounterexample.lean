import Submission.OddOrder.Bridge

/-!
# Bender--Glauberman, Section 7: the minimal odd counterexample

This is the opening block of `BGsection7.v`.  It packages a hypothetical
minimal counterexample to the odd-order theorem and proves the standard
strong-induction reduction to that setting.  The remaining lemmas are the
elementary consequences used before maximal subgroups are introduced.
-/

namespace Submission.OddOrder.BG.Section07

open Submission.OddOrder
open Submission.OddOrder.MathlibSupport

universe u

/-- A finite simple odd-order group which is not solvable, while all of its
proper subgroups are solvable.  This is `IsMinSimpleOddGroup` in
`BGsection7.v`. -/
class IsMinSimpleOddGroup (G : Type u) [Group G] [Finite G] : Prop
    extends IsSimpleGroup G where
  odd_card : Odd (Nat.card G)
  not_isSolvable : ¬ IsSolvable G
  proper_isSolvable : ∀ H : Subgroup G, H < ⊤ → IsSolvable H

/-- The initial reduction in `BGsection7.v`: if a minimal simple odd-order
counterexample cannot exist, then every finite group of odd order is
solvable. -/
theorem minSimpleOdd_ind
    (noCounterexample :
      ∀ (G : Type u) [Group G] [Finite G] [IsMinSimpleOddGroup G], False)
    {G : Type u} [Group G] [Finite G] (hodd : Odd (Nat.card G)) :
    IsSolvable G := by
  classical
  let P : ℕ → Prop := fun n =>
    ∀ {K : Type u} [Group K] [Finite K],
      Nat.card K = n → Odd (Nat.card K) → IsSolvable K
  suffices hP : P (Nat.card G) from hP rfl hodd
  exact Nat.strong_induction_on (p := P) (Nat.card G) fun n ih => by
    intro K _ _ hcard hoddK
    by_cases hsub : Subsingleton K
    · haveI : Subsingleton K := hsub
      infer_instance
    · haveI : Nontrivial K := not_subsingleton_iff_nontrivial.mp hsub
      by_cases hsimp : IsSimpleGroup K
      · haveI : IsSimpleGroup K := hsimp
        by_cases hsol : IsSolvable K
        · exact hsol
        · have hproper : ∀ H : Subgroup K, H < ⊤ → IsSolvable H := by
            intro H hH
            have hHlt : Nat.card H < n := by
              rw [← hcard]
              exact natCard_subgroup_lt_natCard_of_ne_top H hH.ne
            exact ih (Nat.card H) hHlt rfl (odd_natCard_subgroup H hoddK)
          letI : IsMinSimpleOddGroup K :=
            { odd_card := hoddK
              not_isSolvable := hsol
              proper_isSolvable := hproper }
          exact (noCounterexample K).elim
      · obtain ⟨N, hNnormal, hNnebot, hNnetop⟩ :=
          exists_proper_nontrivial_normal_of_not_isSimpleGroup (G := K) hsimp
        haveI : N.Normal := hNnormal
        have hNlt : Nat.card N < n := by
          rw [← hcard]
          exact natCard_subgroup_lt_natCard_of_ne_top N hNnetop
        have hQlt : Nat.card (K ⧸ N) < n := by
          rw [← hcard]
          exact natCard_quotient_lt_natCard_of_ne_bot N hNnebot
        haveI : IsSolvable N :=
          ih (Nat.card N) hNlt rfl (odd_natCard_subgroup N hoddK)
        haveI : IsSolvable (K ⧸ N) :=
          ih (Nat.card (K ⧸ N)) hQlt rfl (odd_natCard_quotient N hoddK)
        exact isSolvable_of_normal_subgroup_and_quotient N

/-- A simple odd-order group has prime order once the minimal-counterexample
case has been eliminated. -/
theorem minSimpleOdd_prime
    (noCounterexample :
      ∀ (K : Type u) [Group K] [Finite K] [IsMinSimpleOddGroup K], False)
    {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]
    (hodd : Odd (Nat.card G)) :
    (Nat.card G).Prime := by
  haveI : IsSolvable G := minSimpleOdd_ind noCounterexample hodd
  letI : CommGroup G :=
    { ‹Group G› with
      mul_comm := IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance }
  exact IsSimpleGroup.prime_card

section Elementary

variable {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]

/-- Every subgroup of the minimal counterexample has odd order. -/
theorem mFT_odd (H : Subgroup G) : Odd (Nat.card H) :=
  odd_natCard_subgroup H IsMinSimpleOddGroup.odd_card

/-- Every proper subgroup of the minimal counterexample is solvable. -/
theorem mFT_sol {H : Subgroup G} (hH : H < ⊤) : IsSolvable H :=
  IsMinSimpleOddGroup.proper_isSolvable H hH

/-- The minimal counterexample is nonabelian. -/
theorem mFT_nonAbelian : ¬ ∀ a b : G, a * b = b * a := by
  intro hcomm
  exact IsMinSimpleOddGroup.not_isSolvable (G := G) (_root_.isSolvable_of_comm hcomm)

/-- The trivial subgroup is proper in the minimal counterexample. -/
theorem mFT_gt1 : (⊥ : Subgroup G) < ⊤ :=
  bot_lt_iff_ne_bot.mpr top_ne_bot

/-- The minimal counterexample is nontrivial.  This is the proposition-valued
counterpart of MathComp's `mFT_neq1`. -/
theorem mFT_neq1 : (⊥ : Subgroup G) ≠ ⊤ :=
  (mFT_gt1 (G := G)).ne

/-- Quotients of the minimal counterexample inherit odd order. -/
theorem mFT_quo_odd (H : Subgroup G) : Odd (Nat.card (G ⧸ H)) :=
  odd_natCard_quotient H IsMinSimpleOddGroup.odd_card

/-- The quotient of a subgroup by one of its normal subgroups has odd order.
This is the full two-subgroup form of MathComp's `mFT_quo_odd`. -/
theorem mFT_quo_odd_subgroup (M : Subgroup G) (H : Subgroup M) :
    Odd (Nat.card (M ⧸ H)) :=
  odd_natCard_quotient H (mFT_odd M)

/-- In the minimal counterexample, a subgroup is proper exactly when it is
solvable. -/
theorem mFT_sol_proper (H : Subgroup G) : H < ⊤ ↔ IsSolvable H := by
  constructor
  · exact mFT_sol
  · intro hsol
    rw [lt_top_iff_ne_top]
    intro htop
    letI : IsSolvable H := hsol
    apply IsMinSimpleOddGroup.not_isSolvable (G := G)
    exact _root_.solvable_of_surjective (f := H.subtype) (by
      intro g
      exact ⟨⟨g, by simp [htop]⟩, rfl⟩)

/-- Every finite `p`-subgroup of the minimal counterexample is proper. -/
theorem mFT_pgroup_proper {p : ℕ} [Fact p.Prime]
    (P : Subgroup G) (hP : IsPGroup p P) : P < ⊤ := by
  have hnil : Group.IsNilpotent P := IsPGroup.isNilpotent hP
  letI : Group.IsNilpotent P := hnil
  exact (mFT_sol_proper P).mpr inferInstance

/-- A nontrivial proper subgroup has proper normalizer. -/
theorem mFT_norm_proper (H : Subgroup G) (hHne : H ≠ ⊥) (hH : H < ⊤) :
    Subgroup.normalizer (H : Set G) < ⊤ := by
  rw [lt_top_iff_ne_top]
  intro hnorm
  have hHnormal : H.Normal := Subgroup.normalizer_eq_top_iff.mp hnorm
  rcases hHnormal.eq_bot_or_eq_top with hbot | htop
  · exact hHne hbot
  · exact hH.ne htop

/-- The center of the minimal counterexample is trivial. -/
theorem cent_mFT_trivial : Subgroup.center G = ⊥ := by
  rcases ((inferInstance : (Subgroup.center G).Normal).eq_bot_or_eq_top) with hbot | htop
  · exact hbot
  · exact False.elim
      (mFT_nonAbelian (isMulCommutative_iff.mp (Subgroup.center_eq_top_iff.mp htop)))

/-- The centralizer of every nontrivial subgroup is proper. -/
theorem mFT_cent_proper (H : Subgroup G) (hHne : H ≠ ⊥) :
    Subgroup.centralizer (H : Set G) < ⊤ := by
  by_cases hHtop : H = ⊤
  · subst H
    change Subgroup.centralizer (Set.univ : Set G) < ⊤
    rw [Subgroup.centralizer_univ, cent_mFT_trivial]
    exact mFT_gt1 (G := G)
  · exact lt_of_le_of_lt (Subgroup.centralizer_le_normalizer (H : Set G))
      (mFT_norm_proper H hHne (lt_top_iff_ne_top.mpr hHtop))

/-- The centralizer of a nonidentity element is proper. -/
theorem mFT_cent1_proper {x : G} (hx : x ≠ 1) :
    Subgroup.centralizer ({x} : Set G) < ⊤ := by
  rw [← Subgroup.centralizer_closure, ← Subgroup.zpowers_eq_closure]
  exact mFT_cent_proper (Subgroup.zpowers x) (Subgroup.zpowers_ne_bot.mpr hx)

/-- If a nontrivial subgroup is normal in `M`, then the quotient `M / H` is
solvable.  When `M` is proper this follows from minimality; when `M = G`,
simplicity forces `H = G`.  This ports MathComp's `mFT_quo_sol`. -/
theorem mFT_quo_sol (M : Subgroup G) (H : Subgroup M) [H.Normal]
    (hHne : H ≠ ⊥) : IsSolvable (M ⧸ H) := by
  by_cases hM : M = ⊤
  · subst M
    let e : (⊤ : Subgroup G) ≃* G := Subgroup.topEquiv
    let K : Subgroup G := H.map e
    haveI : K.Normal := Subgroup.Normal.map (inferInstance : H.Normal)
      e.toMonoidHom e.surjective
    have hKne : K ≠ ⊥ := by
      intro hK
      apply hHne
      apply (Subgroup.map_injective (f := e.toMonoidHom) e.injective)
      simpa [K] using hK
    have hKtop : K = ⊤ :=
      ((inferInstance : K.Normal).eq_bot_or_eq_top).resolve_left hKne
    have hHtop : H = ⊤ := by
      apply (Subgroup.map_injective (f := e.toMonoidHom) e.injective)
      simpa [K] using hKtop
    haveI : Subsingleton ((⊤ : Subgroup G) ⧸ H) := by
      rw [hHtop]
      exact QuotientGroup.subsingleton_quotient_top
    infer_instance
  · letI : IsSolvable M := mFT_sol (lt_top_iff_ne_top.mpr hM)
    infer_instance

end Elementary

end Submission.OddOrder.BG.Section07
