import Submission.OddOrder.MathlibSupport.FittingNilpotent
import Submission.OddOrder.MathlibSupport.MinimalNormalExistence

/-!
The chief-factor stabilizer criterion for the Fitting subgroup.

This is the subgroup form of the nontrivial inclusion in
`BGsection1.chief_stab_sub_Fitting`.  The proof follows Hall's minimal
counterexample argument: a minimal normal counterexample has a top chief
factor with abelian quotient, while all lower chief factors lie in the
Fitting subgroup and are centralized successively.  Its lower central
series therefore terminates.
-/

namespace Submission.OddOrder.MathlibSupport

universe u

variable {G : Type u} [Group G] [Finite G]

/-- Every nontrivial normal subgroup of a finite group is the upper term of
some chief factor. -/
private theorem exists_chiefFactor_eq_upper {U : Subgroup G}
    (hUnormal : U.Normal) (hU : U ≠ ⊥) :
    ∃ (V : Subgroup G) (hVnormal : V.Normal),
      @IsChiefFactor G _ V U hVnormal := by
  let Good : Subgroup G → Prop := fun V ↦ V.Normal ∧ V < U
  have hbot : Good (⊥ : Subgroup G) :=
    ⟨by infer_instance, bot_lt_iff_ne_bot.mpr hU⟩
  obtain ⟨V, _hbotV, hVgood, hVmax⟩ :=
    Finite.exists_le_maximal (p := Good) hbot
  letI : V.Normal := hVgood.1
  let q : G →* G ⧸ V := QuotientGroup.mk' V
  have hqsurj : Function.Surjective q := QuotientGroup.mk'_surjective V
  refine ⟨V, hVgood.1, hVgood.2.le, hUnormal, ?_⟩
  refine ⟨?_, Subgroup.Normal.map hUnormal q hqsurj, ?_⟩
  · intro hmap
    have hUV : U ≤ V := by
      have hker : U ≤ q.ker := (Subgroup.map_eq_bot_iff U).mp hmap
      simpa [q, QuotientGroup.ker_mk'] using hker
    exact (not_le_of_gt hVgood.2) hUV
  · intro N hNnormal hNU hN
    let W : Subgroup G := N.comap q
    have hWnormal : W.Normal := by
      dsimp [W]
      exact Subgroup.Normal.comap hNnormal q
    have hVW : V ≤ W := by
      dsimp [W, q]
      exact QuotientGroup.le_comap_mk' V N
    have hWU : W ≤ U := by
      have hkerU : q.ker ≤ U := by
        simpa [q, QuotientGroup.ker_mk'] using hVgood.2.le
      calc
        W ≤ (U.map q).comap q := Subgroup.comap_mono hNU
        _ = U := Subgroup.comap_map_eq_self hkerU
    by_contra hUN
    have hnUW : ¬ U ≤ W := by
      intro hUW
      apply hUN
      exact Subgroup.map_le_iff_le_comap.mpr hUW
    have hWltU : W < U :=
      lt_of_le_of_ne hWU (fun hWUeq ↦ hnUW hWUeq.ge)
    have hWV : W ≤ V := hVmax ⟨hWnormal, hWltU⟩ hVW
    have hWVeq : W = V := le_antisymm hWV hVW
    apply hN
    calc
      N = W.map q :=
        (Subgroup.map_comap_eq_self_of_surjective hqsurj N).symm
      _ = V.map q := congrArg (fun X : Subgroup G ↦ X.map q) hWVeq
      _ = ⊥ := QuotientGroup.map_mk'_self V

/-- A chief factor at the top of a normal subgroup of a solvable group has
abelian quotient, so the derived subgroup lies below the lower term. -/
private theorem commutator_le_lower_of_chiefFactor
    {X : Type u} [Group X] [IsSolvable X]
    {V U : Subgroup X} [V.Normal]
    (hChief : IsChiefFactor V U) :
    ⁅U, U⁆ ≤ V := by
  let q : X →* X ⧸ V := QuotientGroup.mk' V
  let M : Subgroup (X ⧸ V) := U.map q
  have hMcomm : IsMulCommutative M := by
    exact hChief.quotient_minimal_normal.isMulCommutative
  have hMM : ⁅M, M⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact Subgroup.le_centralizer_iff_isMulCommutative.mpr hMcomm
  have hmap : ⁅U, U⁆.map q = ⊥ := by
    rw [Subgroup.map_commutator]
    exact hMM
  have hker : ⁅U, U⁆ ≤ q.ker := (Subgroup.map_eq_bot_iff _).mp hmap
  simpa [q, QuotientGroup.ker_mk'] using hker

/-- If `H` stabilizes every chief factor below the Fitting subgroup, then
every nontrivial normal subgroup below the Fitting subgroup has strictly
descending commutator with `H`. -/
private theorem commutator_lt_of_stabilizes_chiefFactors
    [IsSolvable G] {H K U : Subgroup G}
    (hKH : K ≤ H)
    (hU : U.Normal) (hUne : U ≠ ⊥)
    (hUF : U ≤ fittingCore G)
    (hstab :
      ∀ (V W : Subgroup G) [V.Normal],
        IsChiefFactor V W →
        W ≤ fittingCore G →
        ⁅H, W⁆ ≤ V) :
    ⁅U, K⁆ < U := by
  obtain ⟨V, hVnormal, hChief⟩ :=
    exists_chiefFactor_eq_upper hU hUne
  letI : V.Normal := hVnormal
  have hUK : ⁅U, K⁆ ≤ ⁅U, H⁆ :=
    Subgroup.commutator_mono le_rfl hKH
  have hUH : ⁅U, H⁆ ≤ ⁅H, U⁆ := Subgroup.commutator_comm_le U H
  exact lt_of_le_of_lt (hUK.trans (hUH.trans (hstab V U hChief hUF)))
    hChief.lt

/-- `BGsection1.chief_stab_sub_Fitting`, specialized to a normal acting
subgroup.  A normal subgroup which stabilizes every chief factor whose upper
term is contained in the Fitting subgroup is itself contained in the Fitting
subgroup. -/
theorem normal_le_fittingCore_of_stabilizes_chiefFactors
    [IsSolvable G]
    {H : Subgroup G}
    (hHnormal : H.Normal)
    (hstab :
      ∀ (V U : Subgroup G) [V.Normal],
        IsChiefFactor V U →
        U ≤ fittingCore G →
        ⁅H, U⁆ ≤ V) :
    H ≤ fittingCore G := by
  by_contra hHF
  let Bad : Subgroup G → Prop := fun K ↦
    K.Normal ∧ K ≤ H ∧ ¬ K ≤ fittingCore G
  have hHbad : Bad H := ⟨hHnormal, le_rfl, hHF⟩
  obtain ⟨K, _hKH, hKmin⟩ := Finite.exists_le_minimal hHbad
  have hKnormal : K.Normal := hKmin.1.1
  have hKH : K ≤ H := hKmin.1.2.1
  have hKF : ¬ K ≤ fittingCore G := hKmin.1.2.2
  have hKne : K ≠ ⊥ := by
    intro hK
    apply hKF
    rw [hK]
    exact bot_le
  obtain ⟨V, hVnormal, hChief⟩ :=
    exists_chiefFactor_eq_upper hKnormal hKne
  letI : V.Normal := hVnormal
  have hVF : V ≤ fittingCore G := by
    by_contra hVF
    have hVbad : Bad V :=
      ⟨by infer_instance, hChief.le.trans hKH, hVF⟩
    have hKV : K ≤ V := hKmin.eq_of_ge hVbad hChief.le |>.le
    exact (not_le_of_gt hChief.lt) hKV
  have hderived : ⁅K, K⁆ ≤ V :=
    commutator_le_lower_of_chiefFactor hChief
  have hseriesOne : K.lowerCentralSeries 1 ≤ V := by
    simpa [Subgroup.lowerCentralSeries_succ] using hderived
  have hseriesF : ∀ n : ℕ, K.lowerCentralSeries (n + 1) ≤ fittingCore G := by
    intro n
    exact (K.lowerCentralSeries_antitone (Nat.succ_le_succ (Nat.zero_le n))).trans
      (hseriesOne.trans hVF)
  have hseriesTerminates : ∃ n : ℕ, K.lowerCentralSeries n = ⊥ := by
    by_contra hnone
    have hnonzero : ∀ n : ℕ, K.lowerCentralSeries n ≠ ⊥ := by
      intro n hn
      exact hnone ⟨n, hn⟩
    let L : ℕ → Subgroup G := fun n ↦ K.lowerCentralSeries (n + 1)
    have hLstrict : ∀ n : ℕ, L (n + 1) < L n := by
      intro n
      have hnormal : (L n).Normal := by
        dsimp [L]
        exact Subgroup.lowerCentralSeries_normal K (n + 1)
      have hne : L n ≠ ⊥ := hnonzero (n + 1)
      have hdesc := commutator_lt_of_stabilizes_chiefFactors
        (H := H) (K := K) hKH hnormal hne (hseriesF n) hstab
      simpa [L, Subgroup.lowerCentralSeries_succ, Nat.add_assoc] using hdesc
    have hinj : Function.Injective L :=
      (strictAnti_nat_of_succ_lt hLstrict).injective
    exact (Finite.of_injective L hinj).false
  have hKnil : Group.IsNilpotent K :=
    (Subgroup.isNilpotent_iff_lowerCentralSeries K).mpr hseriesTerminates
  exact hKF (nilpotent_normal_le_fittingCore hKnormal hKnil)

end Submission.OddOrder.MathlibSupport
