import Submission.OddOrder.MathlibSupport.PCore

/-!
The largest normal subgroup of order coprime to `p`.

This is the mathlib-shaped version of MathComp's `'O_p^'(G)`.  In a finite
group, normal subgroups of order coprime to `p` are closed under joins, so a
maximal one is automatically greatest.
-/

namespace Submission.OddOrder.MathlibSupport

variable {G : Type*} [Group G] {p : ℕ}

/-- A subgroup whose cardinality is coprime to `p`. -/
def IsPPrimeSubgroup (p : ℕ) (H : Subgroup G) : Prop :=
  Nat.Coprime p (Nat.card H)

/-- A normal subgroup whose cardinality is coprime to `p`. -/
def IsNormalPPrime (p : ℕ) (H : Subgroup G) : Prop :=
  IsPPrimeSubgroup p H ∧ H.Normal

theorem isPPrimeSubgroup_bot : IsPPrimeSubgroup p (⊥ : Subgroup G) := by
  simp [IsPPrimeSubgroup]

theorem isNormalPPrime_bot : IsNormalPPrime p (⊥ : Subgroup G) :=
  ⟨isPPrimeSubgroup_bot, inferInstance⟩

theorem isPPrimeSubgroup_sup [Finite G] {H K : Subgroup G}
    (hHnormal : H.Normal)
    (hH : IsPPrimeSubgroup p H) (hK : IsPPrimeSubgroup p K) :
    IsPPrimeSubgroup p (H ⊔ K) := by
  letI : H.Normal := hHnormal
  have hrel : H.relIndex (H ⊔ K) = H.relIndex K := by
    exact Subgroup.relIndex_sup_left K H
  have hsubcard : Nat.card (H.subgroupOf (H ⊔ K)) = Nat.card H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv
  rw [IsPPrimeSubgroup, ← (H.subgroupOf (H ⊔ K)).card_mul_index, hsubcard]
  change Nat.Coprime p (Nat.card H * H.relIndex (H ⊔ K))
  rw [hrel, Nat.coprime_mul_iff_right]
  exact ⟨hH, hK.coprime_dvd_right (Subgroup.relIndex_dvd_card H K)⟩

theorem exists_greatest_isNormalPPrime [Finite G] :
    ∃ M : Subgroup G, IsNormalPPrime p M ∧
      ∀ P : Subgroup G, IsNormalPPrime p P → P ≤ M := by
  classical
  obtain ⟨M, _, hM, hMmax⟩ :=
    Finite.exists_le_maximal (p := fun P : Subgroup G => IsNormalPPrime p P)
      isNormalPPrime_bot
  refine ⟨M, hM, ?_⟩
  intro P hP
  have hsup : IsNormalPPrime p (M ⊔ P) := by
    refine ⟨isPPrimeSubgroup_sup hM.2 hM.1 hP.1, ?_⟩
    letI : M.Normal := hM.2
    letI : P.Normal := hP.2
    infer_instance
  exact le_sup_right.trans (hMmax hsup le_sup_left)

/-- The `p'`-core, i.e. the greatest normal subgroup of order coprime to `p`. -/
noncomputable def pPrimeCore (p : ℕ) (G : Type*) [Group G] [Finite G] : Subgroup G :=
  (exists_greatest_isNormalPPrime (G := G) (p := p)).choose

theorem pPrimeCore_isNormalPPrime [Finite G] :
    IsNormalPPrime p (pPrimeCore p G) :=
  (exists_greatest_isNormalPPrime (G := G) (p := p)).choose_spec.1

theorem le_pPrimeCore [Finite G] {P : Subgroup G}
    (hP : IsPPrimeSubgroup p P) (hPnormal : P.Normal) : P ≤ pPrimeCore p G :=
  (exists_greatest_isNormalPPrime (G := G) (p := p)).choose_spec.2 P ⟨hP, hPnormal⟩

theorem pPrimeCore_coprime_card [Finite G] :
    Nat.Coprime p (Nat.card (pPrimeCore p G)) :=
  pPrimeCore_isNormalPPrime.1

instance pPrimeCore_normal [Finite G] : (pPrimeCore p G).Normal :=
  pPrimeCore_isNormalPPrime.2

theorem map_pPrimeCore_le_equiv [Finite G] (e : G ≃* G) :
    (pPrimeCore p G).map e.toMonoidHom ≤ pPrimeCore p G := by
  apply le_pPrimeCore
  · rw [IsPPrimeSubgroup]
    have hcard : Nat.card ((pPrimeCore p G).map e.toMonoidHom) =
        Nat.card (pPrimeCore p G) :=
      (Nat.card_congr (e.subgroupMap (pPrimeCore p G)).toEquiv).symm
    rw [hcard]
    exact pPrimeCore_coprime_card
  · exact Subgroup.Normal.map (by infer_instance) e.toMonoidHom e.surjective

instance pPrimeCore_characteristic [Finite G] : (pPrimeCore p G).Characteristic := by
  rw [Subgroup.characteristic_iff_map_eq]
  intro e
  apply le_antisymm (map_pPrimeCore_le_equiv e)
  rw [← Subgroup.map_le_map_iff_of_injective
    (f := e.symm.toMonoidHom) e.symm.injective]
  have h := map_pPrimeCore_le_equiv (p := p) e.symm
  simpa [Subgroup.map_map] using h

theorem disjoint_pPrimeCore_of_isPGroup [Finite G] [Fact p.Prime]
    {P : Subgroup G} (hP : IsPGroup p P) : Disjoint P (pPrimeCore p G) := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP
  apply Subgroup.disjoint_of_coprime_natCard
  rw [hn]
  exact (pPrimeCore_coprime_card (G := G) (p := p)).pow_left n

theorem disjoint_pCore_pPrimeCore [Finite G] [Fact p.Prime] :
    Disjoint (pCore p G) (pPrimeCore p G) :=
  disjoint_pPrimeCore_of_isPGroup pCore_isPGroup

end Submission.OddOrder.MathlibSupport
