import Submission.OddOrder.BG.Section07.MinimalCounterexample
import Submission.OddOrder.MathlibSupport.PGroupNormalizer
import Submission.OddOrder.MathlibSupport.SCNCentralizer

/-!
# Bender--Glauberman, Section 7: maximal subgroups

This file ports the block of `BGsection7.v` that introduces the families
`'M`, `'M(H)`, `'U`, and `'SCN_n[p]`, then establishes the elementary
maximal-subgroup facts through self-normality of maximal subgroups.
-/

namespace Submission.OddOrder.BG.Section07

open Submission.OddOrder
open Submission.OddOrder.MathlibSupport

universe u

variable {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]

/-- The maximal proper subgroups of the minimal counterexample. -/
def minSimple_max_groups : Set (Subgroup G) :=
  {M | IsCoatom M}

/-- The maximal subgroups which contain a prescribed set. -/
def minSimple_max_groups_of (H : Set G) : Set (Subgroup G) :=
  {M | M ∈ minSimple_max_groups (G := G) ∧ H ⊆ M}

/-- The subgroups contained in a unique maximal subgroup. -/
def minSimple_uniq_max_groups : Set (Subgroup G) :=
  {U | (minSimple_max_groups_of (G := G) (U : Set G)).ncard = 1}

/-- SCN subgroups of rank at least `n`, as the Sylow subgroup varies. -/
def minSimple_SCN_at (n p : ℕ) [Fact p.Prime] : Set (Subgroup G) :=
  {A | ∃ P : Sylow p G,
    IsSCN (P : Subgroup G) A ∧ n ≤ Group.rank A}

/-- Every proper subgroup is contained in a maximal subgroup. -/
theorem mmax_exists (H : Subgroup G) (hH : H < ⊤) :
    ∃ M : Subgroup G,
      M ∈ minSimple_max_groups (G := G) ∧ H ≤ M := by
  rcases (eq_top_or_exists_le_coatom H).resolve_left hH.ne with ⟨M, hM, hHM⟩
  exact ⟨M, hM, hHM⟩

/-- The minimal counterexample has a maximal subgroup. -/
theorem any_mmax :
    ∃ M : Subgroup G, M ∈ minSimple_max_groups (G := G) := by
  rcases mmax_exists (⊥ : Subgroup G) (mFT_gt1 (G := G)) with ⟨M, hM, -⟩
  exact ⟨M, hM⟩

/-- A member of `'M` is proper. -/
theorem mmax_proper {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G)) : M < ⊤ :=
  hM.lt_top

/-- A member of `'M` is solvable. -/
theorem mmax_sol {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G)) : IsSolvable M :=
  mFT_sol (mmax_proper hM)

/-- A proper subgroup above a maximal subgroup is that maximal subgroup. -/
theorem mmax_max {M H : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hH : H < ⊤) (hMH : M ≤ H) : H = M :=
  hM.le_iff_eq hH.ne |>.mp hMH

/-- Maximal subgroups are an antichain. -/
theorem eq_mmax {M H : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hH : H ∈ minSimple_max_groups (G := G))
    (hMH : M ≤ H) : M = H :=
  (mmax_max hM (mmax_proper hH) hMH).symm

/-- Every subgroup of a maximal subgroup is proper in `G`. -/
theorem sub_mmax_proper {M H : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hHM : H ≤ M) : H < ⊤ :=
  lt_of_le_of_lt hHM (mmax_proper hM)

/-- If a maximal subgroup lies in the normalizer of a nontrivial proper
subgroup, it is the whole normalizer. -/
theorem mmax_norm {M X : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hXne : X ≠ ⊥) (hX : X < ⊤)
    (hMN : M ≤ Subgroup.normalizer (X : Set G)) :
    Subgroup.normalizer (X : Set G) = M :=
  mmax_max hM (mFT_norm_proper X hXne hX) hMN

/-- Set-valued form of `mmax_normal`: a nontrivial set normalized by a
maximal subgroup has that maximal subgroup as its full normalizer.  This is
MathComp's `mmax_normal_subset`. -/
theorem mmax_normal_subset {M : Subgroup G} {A : Set G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hAM : A ⊆ M) (hMN : M ≤ Subgroup.normalizer A)
    (hAne : ¬ A ⊆ {1}) :
    Subgroup.normalizer A = M := by
  have hclosureNe : Subgroup.closure A ≠ ⊥ := by
    exact fun hbot => hAne (Subgroup.closure_eq_bot_iff.mp hbot)
  have hclosureM : Subgroup.closure A ≤ M :=
    (Subgroup.closure_le M).mpr hAM
  have hclosureProper : Subgroup.closure A < ⊤ :=
    sub_mmax_proper hM hclosureM
  have hnormalizerClosureProper :
      Subgroup.normalizer (Subgroup.closure A : Set G) < ⊤ :=
    mFT_norm_proper (Subgroup.closure A) hclosureNe hclosureProper
  have hnormalizerProper : Subgroup.normalizer A < ⊤ :=
    lt_of_le_of_lt (Subgroup.normalizer_le_normalizer_closure A)
      hnormalizerClosureProper
  exact mmax_max hM hnormalizerProper hMN

/-- A nontrivial subgroup normal in a maximal subgroup has that maximal
subgroup as its full normalizer. -/
theorem mmax_normal {M H : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hHM : H ≤ M) (hHnormal : (H.subgroupOf M).Normal)
    (hHne : H ≠ ⊥) :
    Subgroup.normalizer (H : Set G) = M := by
  apply mmax_norm hM hHne (sub_mmax_proper hM hHM)
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hHM).mp hHnormal

/-- A Sylow subgroup of a maximal subgroup is ambient Sylow when its ambient
normalizer is already contained in that maximal subgroup. -/
theorem mmax_sigma_Sylow {p : ℕ} [Fact p.Prime]
    {M : Subgroup G} (hM : M ∈ minSimple_max_groups (G := G))
    (P : Sylow p M)
    (hNP : Subgroup.normalizer
      ((P : Subgroup M).map M.subtype : Set G) ≤ M) :
    ∃ Q : Sylow p G,
      (Q : Subgroup G) = (P : Subgroup M).map M.subtype := by
  let PG : Subgroup G := (P : Subgroup M).map M.subtype
  have hPGp : IsPGroup p PG := P.isPGroup'.map M.subtype
  rcases hPGp.exists_le_sylow with ⟨Q, hPGQ⟩
  have hQeq : (Q : Subgroup G) = PG := by
    by_contra hne
    have hPGltQ : PG < (Q : Subgroup G) :=
      lt_of_le_of_ne hPGQ (Ne.symm hne)
    let R : Subgroup G := (Q : Subgroup G) ⊓ Subgroup.normalizer (PG : Set G)
    have hPGltR : PG < R := by
      exact lt_inf_normalizer_of_isPGroup Q.isPGroup' hPGltQ
    have hRM : R ≤ M := by
      exact inf_le_right.trans hNP
    let RM : Subgroup M := R.subgroupOf M
    have hRMp : IsPGroup p RM := by
      exact (Q.isPGroup'.to_le inf_le_left).of_equiv
        (Subgroup.subgroupOfEquivOfLe hRM).symm
    have hPRM : (P : Subgroup M) ≤ RM := by
      intro x hx
      change (x : G) ∈ R
      exact hPGltR.le (Subgroup.mem_map_of_mem M.subtype hx)
    have hRMeq : RM = (P : Subgroup M) :=
      P.is_maximal' hRMp hPRM
    have hReq : R = PG := by
      rw [← Subgroup.map_subgroupOf_eq_of_le hRM]
      change RM.map M.subtype = PG
      rw [hRMeq]
    exact hPGltR.ne hReq.symm
  exact ⟨Q, hQeq⟩

/-- A maximal subgroup of the minimal counterexample is nontrivial. -/
theorem mmax_neq1 {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G)) : M ≠ ⊥ := by
  intro hMbot
  obtain ⟨x : G, hx⟩ := exists_ne (1 : G)
  have hzx : Subgroup.zpowers x ≠ ⊥ :=
    Subgroup.zpowers_ne_bot.mpr hx
  have hzle : (⊥ : Subgroup G) ≤ Subgroup.zpowers x := bot_le
  have hcoatomBot : IsCoatom (⊥ : Subgroup G) := hMbot ▸ hM
  have hztop : Subgroup.zpowers x = ⊤ := by
    rcases hcoatomBot.le_iff.mp hzle with htop | hbot
    · exact htop
    · exact (hzx hbot).elim
  letI : IsCyclic G :=
    isCyclic_iff_exists_zpowers_eq_top.mpr ⟨x, hztop⟩
  exact mFT_nonAbelian (G := G)
    (isMulCommutative_iff.mp (inferInstance : IsMulCommutative G))

/-- Maximal subgroups are self-normalizing. -/
theorem norm_mmax {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G)) :
    Subgroup.normalizer (M : Set G) = M := by
  apply mmax_norm hM (mmax_neq1 hM) (mmax_proper hM)
  exact Subgroup.le_normalizer

end Submission.OddOrder.BG.Section07
