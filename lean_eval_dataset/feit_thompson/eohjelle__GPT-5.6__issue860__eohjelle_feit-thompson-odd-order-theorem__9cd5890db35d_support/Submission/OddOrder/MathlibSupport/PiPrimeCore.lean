import Submission.OddOrder.MathlibSupport.Hall

/-!
# Prime-complement cores inside ambient subgroups

This file supplies the prime-set analogue of MathComp's `O_pi^'(X)`: the
largest subgroup of `X` that is normal in `X` and whose order has no prime
divisor in `pi`.
-/

namespace Submission.OddOrder.MathlibSupport

universe u

/-- The `pi`-prime core of `X`, viewed as a subgroup of the ambient group. -/
def piPrimeCore
    {G : Type u} [Group G]
    (pi : Set ℕ) (X : Subgroup G) : Subgroup G :=
  sSup {K : Subgroup G |
    K ≤ X ∧ (K.subgroupOf X).Normal ∧
      IsPiNumber piᶜ (Nat.card K)}

private theorem le_piPrimeCore
    {G : Type u} [Group G] {pi : Set ℕ} {K X : Subgroup G}
    (hKX : K ≤ X) (hKnormal : (K.subgroupOf X).Normal)
    (hKpi : IsPiNumber piᶜ (Nat.card K)) :
    K ≤ piPrimeCore pi X := by
  rw [piPrimeCore]
  exact le_sSup ⟨hKX, hKnormal, hKpi⟩

/-- The prime-complement core is contained in its ambient subgroup. -/
theorem piPrimeCore_le
    {G : Type u} [Group G]
    (pi : Set ℕ) (X : Subgroup G) :
    piPrimeCore pi X ≤ X := by
  rw [piPrimeCore]
  exact sSup_le fun _ hK => hK.1

/-- The prime-complement core is normal in its ambient subgroup. -/
theorem piPrimeCore_normal
    {G : Type u} [Group G]
    (pi : Set ℕ) (X : Subgroup G) :
    ((piPrimeCore pi X).subgroupOf X).Normal := by
  have hcoreX : piPrimeCore pi X ≤ X := piPrimeCore_le pi X
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hcoreX]
  rw [piPrimeCore, sSup_eq_iSup']
  let S : Set (Subgroup G) :=
    {K : Subgroup G |
      K ≤ X ∧ (K.subgroupOf X).Normal ∧
        IsPiNumber piᶜ (Nat.card K)}
  change X ≤ Subgroup.normalizer
    ((⨆ K : S, (K : Subgroup G) : Subgroup G) : Set G)
  refine (show X ≤ ⨅ K : S, Subgroup.normalizer (K : Subgroup G) by
    intro x hx
    rw [Subgroup.mem_iInf]
    intro K
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer K.property.1).mp
      K.property.2.1 hx) |>.trans
        (Subgroup.iInf_normalizer_le_normalizer_iSup
          (fun K : S => (K : Subgroup G)))

private theorem isPiNumber_card_sup_of_normal_left
    {G : Type u} [Group G] [Finite G] {rho : Set ℕ}
    {H K : Subgroup G} (hHnormal : H.Normal)
    (hH : IsPiNumber rho (Nat.card H))
    (hK : IsPiNumber rho (Nat.card K)) :
    IsPiNumber rho (Nat.card (H ⊔ K : Subgroup G)) := by
  letI : H.Normal := hHnormal
  have hrel : H.relIndex (H ⊔ K) = H.relIndex K :=
    Subgroup.relIndex_sup_left K H
  have hsubcard : Nat.card (H.subgroupOf (H ⊔ K)) = Nat.card H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv
  rw [← (H.subgroupOf (H ⊔ K)).card_mul_index, hsubcard]
  change IsPiNumber rho (Nat.card H * H.relIndex (H ⊔ K))
  rw [hrel]
  exact hH.mul (hK.of_dvd (Subgroup.relIndex_dvd_card H K))

/-- The prime-complement core has `pi`-prime cardinality. -/
theorem piPrimeCore_isPiNumber
    {G : Type u} [Group G] [Finite G]
    (pi : Set ℕ) (X : Subgroup G) :
    IsPiNumber piᶜ (Nat.card (piPrimeCore pi X)) := by
  classical
  let Good : Subgroup G → Prop := fun K =>
    K ≤ X ∧ (K.subgroupOf X).Normal ∧
      IsPiNumber piᶜ (Nat.card K)
  have hbot : Good (⊥ : Subgroup G) := by
    refine ⟨bot_le, ?_, ?_⟩
    · simp
    · simpa using (IsPiNumber.one (pi := piᶜ))
  obtain ⟨M, _, hM, hMmax⟩ :=
    Finite.exists_le_maximal (p := Good) hbot
  have hgreatest : ∀ P : Subgroup G, Good P → P ≤ M := by
    intro P hP
    have hsupLe : M ⊔ P ≤ X := sup_le hM.1 hP.1
    have hsupNormal : ((M ⊔ P).subgroupOf X).Normal := by
      rw [Subgroup.subgroupOf_sup hM.1 hP.1]
      letI : (M.subgroupOf X).Normal := hM.2.1
      letI : (P.subgroupOf X).Normal := hP.2.1
      infer_instance
    have hMsubcard : Nat.card (M.subgroupOf X) = Nat.card M :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hM.1).toEquiv
    have hPsubcard : Nat.card (P.subgroupOf X) = Nat.card P :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP.1).toEquiv
    have hMsubPi : IsPiNumber piᶜ (Nat.card (M.subgroupOf X)) := by
      rw [hMsubcard]
      exact hM.2.2
    have hPsubPi : IsPiNumber piᶜ (Nat.card (P.subgroupOf X)) := by
      rw [hPsubcard]
      exact hP.2.2
    have hsupPi : IsPiNumber piᶜ (Nat.card (M ⊔ P : Subgroup G)) := by
      have h := isPiNumber_card_sup_of_normal_left
        (G := X) hM.2.1 hMsubPi hPsubPi
      rw [← Subgroup.subgroupOf_sup hM.1 hP.1] at h
      have hsupCard : Nat.card ((M ⊔ P).subgroupOf X) =
          Nat.card (M ⊔ P : Subgroup G) :=
        Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe hsupLe).toEquiv
      rw [hsupCard] at h
      exact h
    have hGoodSup : Good (M ⊔ P) :=
      ⟨hsupLe, hsupNormal, hsupPi⟩
    exact le_sup_right.trans (hMmax hGoodSup le_sup_left)
  have hcoreEq : piPrimeCore pi X = M := by
    apply le_antisymm
    · rw [piPrimeCore]
      exact sSup_le fun P hP => hgreatest P hP
    · exact le_piPrimeCore hM.1 hM.2.1 hM.2.2
  rw [hcoreEq]
  exact hM.2.2

private theorem le_normal_isHall_of_isPiNumber
    {G : Type u} [Group G] [Finite G]
    {rho : Set ℕ} {C K L : Subgroup G}
    (hKnormal : (K.subgroupOf C).Normal)
    (hKHall : IsHall rho (K.subgroupOf C))
    (hLC : L ≤ C) (hLpi : IsPiNumber rho (Nat.card L)) :
    L ≤ K := by
  let KC : Subgroup C := K.subgroupOf C
  letI : KC.Normal := by simpa [KC] using hKnormal
  have hcop : (Nat.card L).Coprime KC.index := by
    apply Nat.coprime_of_dvd
    intro p hp hpL hpIndex
    have hpPi : p ∈ rho := hLpi hp hpL
    have hpNotPi : p ∈ rhoᶜ := hKHall.isPiNumber_index hp hpIndex
    exact hpNotPi hpPi
  intro x hxL
  let xC : C := ⟨x, hLC hxL⟩
  let qC : C →* C ⧸ KC := QuotientGroup.mk' KC
  have horderL : orderOf (qC xC) ∣ Nat.card L := by
    exact (orderOf_map_dvd qC xC).trans (by
      simpa [xC] using L.orderOf_dvd_natCard hxL)
  have horderIndex : orderOf (qC xC) ∣ KC.index := by
    simpa only [KC.index_eq_card] using orderOf_dvd_natCard (qC xC)
  have horderOne : orderOf (qC xC) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop horderL horderIndex
  have hqOne : qC xC = 1 := orderOf_eq_one_iff.mp horderOne
  have hxKC : xC ∈ KC :=
    (QuotientGroup.eq_one_iff xC).mp (by simpa [qC] using hqOne)
  exact hxKC

/-- A normal `pi`-complement in `X` is its prime-complement core. -/
theorem piPrimeCore_eq_of_normal_isComplement
    {G : Type u} [Group G] [Finite G]
    (pi : Set ℕ) {X K H : Subgroup G}
    (hKX : K ≤ X) (hHX : H ≤ X)
    (hKnormal : (K.subgroupOf X).Normal)
    (hKpi : IsPiNumber piᶜ (Nat.card K))
    (hHpi : IsPiNumber pi (Nat.card H))
    (hcomp :
      (K.subgroupOf X).IsComplement' (H.subgroupOf X)) :
    piPrimeCore pi X = K := by
  have hKsubcard : Nat.card (K.subgroupOf X) = Nat.card K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKX).toEquiv
  have hHsubcard : Nat.card (H.subgroupOf X) = Nat.card H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHX).toEquiv
  have hKHall : IsHall piᶜ (K.subgroupOf X) := by
    constructor
    · rw [hKsubcard]
      exact hKpi
    · rw [hcomp.symm.index_eq_card, hHsubcard]
      simpa only [compl_compl] using hHpi
  apply le_antisymm
  · exact le_normal_isHall_of_isPiNumber hKnormal hKHall
      (piPrimeCore_le pi X) (piPrimeCore_isPiNumber pi X)
  · exact le_piPrimeCore hKX hKnormal hKpi

/-- Ambient automorphisms transport the prime-complement core. -/
theorem piPrimeCore_map_equiv
    {G : Type u} [Group G]
    (pi : Set ℕ) (X : Subgroup G) (e : G ≃* G) :
    (piPrimeCore pi X).map e.toMonoidHom =
      piPrimeCore pi (X.map e.toMonoidHom) := by
  have map_le (f : G ≃* G) (Y : Subgroup G) :
      (piPrimeCore pi Y).map f.toMonoidHom ≤
        piPrimeCore pi (Y.map f.toMonoidHom) := by
    let S : Set (Subgroup G) :=
      {K | K ≤ Y ∧ (K.subgroupOf Y).Normal ∧
        IsPiNumber piᶜ (Nat.card K)}
    change (sSup S).map f.toMonoidHom ≤
      piPrimeCore pi (Y.map f.toMonoidHom)
    rw [Subgroup.map_le_iff_le_comap]
    apply sSup_le
    intro K hK
    change K ≤ (piPrimeCore pi (Y.map f.toMonoidHom)).comap
      f.toMonoidHom
    rw [← Subgroup.map_le_iff_le_comap]
    have hKS : K ≤ Y ∧ (K.subgroupOf Y).Normal ∧
        IsPiNumber piᶜ (Nat.card K) := hK
    have hmapY : K.map f.toMonoidHom ≤ Y.map f.toMonoidHom :=
      Subgroup.map_mono hKS.1
    have hYnormK : Y ≤ Subgroup.normalizer (K : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hKS.1).mp hKS.2.1
    have hmapYnormMap :
        Y.map f.toMonoidHom ≤
          Subgroup.normalizer (K.map f.toMonoidHom : Set G) :=
      (Subgroup.map_mono hYnormK).trans
        (K.le_normalizer_map f.toMonoidHom)
    have hmapNormal :
        ((K.map f.toMonoidHom).subgroupOf
          (Y.map f.toMonoidHom)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hmapY).mpr
        hmapYnormMap
    have hmapPi :
        IsPiNumber piᶜ (Nat.card (K.map f.toMonoidHom)) := by
      rw [Subgroup.card_map_of_injective f.injective]
      exact hKS.2.2
    exact le_piPrimeCore hmapY hmapNormal hmapPi
  apply le_antisymm (map_le e X)
  have hback := map_le e.symm (X.map e.toMonoidHom)
  have hmapped :
      ((piPrimeCore pi (X.map e.toMonoidHom)).map
        e.symm.toMonoidHom).map e.toMonoidHom ≤
      (piPrimeCore pi
        ((X.map e.toMonoidHom).map e.symm.toMonoidHom)).map
          e.toMonoidHom :=
    Subgroup.map_mono hback
  simpa [Subgroup.map_map] using hmapped

end Submission.OddOrder.MathlibSupport
