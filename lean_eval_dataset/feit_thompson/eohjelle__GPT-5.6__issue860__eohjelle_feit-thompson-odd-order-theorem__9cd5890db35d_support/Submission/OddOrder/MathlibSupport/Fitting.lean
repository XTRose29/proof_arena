import Submission.OddOrder.MathlibSupport.PPrimeCore

/-!
The p-core decomposition of the finite Fitting subgroup.

The supremum of all normal p-cores is characteristic and contains every
normal nilpotent subgroup.  The remaining half of finite Fitting's theorem,
that this supremum is itself nilpotent, is kept separate because it is the
normal-nilpotent product theorem missing from mathlib.
-/

namespace Submission.OddOrder.MathlibSupport

variable {G : Type*} [Group G]

/-- One chosen Sylow subgroup for every prime, joined inside `G`. -/
noncomputable def sylowSup (G : Type*) [Group G] : Subgroup G :=
  ⨆ p : {p : ℕ // p.Prime},
    (Classical.choice (Sylow.nonempty (p := (p : ℕ)) (G := G)) : Sylow p G)

theorem sylowSup_eq_top [Finite G] : sylowSup G = ⊤ := by
  apply Subgroup.index_eq_one.mp
  rw [Nat.eq_one_iff_not_exists_prime_dvd]
  intro p hp hpindex
  letI : Fact p.Prime := ⟨hp⟩
  let P : Sylow p G := Classical.choice Sylow.nonempty
  have hP : (P : Subgroup G) ≤ sylowSup G := by
    exact le_iSup (fun q : {q : ℕ // q.Prime} ↦
      ((Classical.choice (Sylow.nonempty (p := (q : ℕ)) (G := G)) :
        Sylow q G) : Subgroup G)) ⟨p, hp⟩
  exact P.not_dvd_index (hpindex.trans (Subgroup.index_dvd_of_le hP))

/-- The p-core supremum form of the finite Fitting subgroup. -/
def fittingCore (G : Type*) [Group G] : Subgroup G :=
  ⨆ p : {p : ℕ // p.Prime}, pCore (p : ℕ) G

instance fittingCore_normal : (fittingCore G).Normal := by
  dsimp [fittingCore]
  infer_instance

instance fittingCore_characteristic : (fittingCore G).Characteristic := by
  rw [Subgroup.characteristic_iff_map_eq]
  intro e
  rw [fittingCore, Subgroup.map_iSup]
  apply iSup_congr
  intro p
  exact Subgroup.characteristic_iff_map_eq.mp (by infer_instance) e

theorem pCore_le_fittingCore (p : ℕ) [Fact p.Prime] :
    pCore p G ≤ fittingCore G :=
  le_iSup (fun q : {q : ℕ // q.Prime} ↦ pCore (q : ℕ) G)
    ⟨p, Fact.out⟩

theorem pCore_le_pPrimeCore_of_ne [Finite G] {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q) :
    pCore q G ≤ pPrimeCore p G := by
  apply le_pPrimeCore (hPnormal := by infer_instance)
  obtain ⟨n, hcard⟩ := (pCore_isPGroup (p := q) (G := G)).exists_card_eq
  rw [IsPPrimeSubgroup, hcard]
  exact ((Nat.coprime_primes Fact.out Fact.out).mpr hpq).pow_right n

/-- If the `p'`-core is trivial, the Fitting p-core supremum consists only of
the `p`-core. -/
theorem fittingCore_eq_pCore_of_pPrimeCore_eq_bot [Finite G] (p : ℕ)
    [Fact p.Prime] (hprimeCore : pPrimeCore p G = ⊥) :
    fittingCore G = pCore p G := by
  apply le_antisymm
  · rw [fittingCore]
    apply iSup_le
    intro q
    by_cases hqp : (q : ℕ) = p
    · exact (congrArg (fun r : ℕ ↦ pCore r G) hqp).le
    · haveI : Fact (q : ℕ).Prime := ⟨q.property⟩
      have hle := pCore_le_pPrimeCore_of_ne (G := G) (p := p)
        (q := (q : ℕ)) (fun h ↦ hqp h.symm)
      have hleBot : pCore (q : ℕ) G ≤ ⊥ := by
        simpa [hprimeCore] using hle
      exact hleBot.trans bot_le
  · exact pCore_le_fittingCore p

/-- Every normal nilpotent subgroup lies in the p-core supremum. -/
theorem nilpotent_normal_le_fittingCore [Finite G] {H : Subgroup G}
    (hHnormal : H.Normal) (hHnil : Group.IsNilpotent H) :
    H ≤ fittingCore G := by
  letI : H.Normal := hHnormal
  letI : Group.IsNilpotent H := hHnil
  calc
    H = (⊤ : Subgroup H).map H.subtype := by
      calc
        H = H.subtype.range := H.range_subtype.symm
        _ = (⊤ : Subgroup H).map H.subtype :=
          MonoidHom.range_eq_map H.subtype
    _ = (sylowSup H).map H.subtype := by rw [sylowSup_eq_top]
    _ = ⨆ p : {p : ℕ // p.Prime},
        ((Classical.choice
          (Sylow.nonempty (p := (p : ℕ)) (G := H)) : Sylow p H) :
          Subgroup H).map H.subtype := by
      rw [sylowSup, Subgroup.map_iSup]
    _ ≤ fittingCore G := by
      apply iSup_le
      intro p
      letI : Fact (p : ℕ).Prime := ⟨p.property⟩
      let P : Sylow (p : ℕ) H := Classical.choice Sylow.nonempty
      have hPnormal : (P : Subgroup H).Normal := by infer_instance
      letI : (P : Subgroup H).Characteristic :=
        P.characteristic_of_normal hPnormal
      have hPimageNormal : ((P : Subgroup H).map H.subtype).Normal := by
        infer_instance
      exact (le_pCore (P.isPGroup'.map H.subtype) hPimageNormal).trans
        (pCore_le_fittingCore (G := G) (p : ℕ))

end Submission.OddOrder.MathlibSupport
