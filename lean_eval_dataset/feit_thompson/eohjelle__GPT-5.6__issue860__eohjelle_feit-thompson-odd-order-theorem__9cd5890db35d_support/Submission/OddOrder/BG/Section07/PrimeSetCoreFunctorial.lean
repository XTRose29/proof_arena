import Submission.OddOrder.BG.Section07.NormedConstrainedHall

/-!
# Functoriality of the prime-set core

The prime-set core is preserved by ambient automorphisms preserving its
ambient subgroup.  The resulting normalizer control supplies the two core
identifications used in Bender--Glauberman Theorem 7.4.
-/

namespace Submission.OddOrder.BG.Section07

open Submission.OddOrder.MathlibSupport

universe u

private theorem le_primeSetCore
    {G : Type u} [Group G] {pi : Set ℕ} {K X : Subgroup G}
    (hKX : K ≤ X) (hKnormal : (K.subgroupOf X).Normal)
    (hKpi : IsPiNumber pi (Nat.card K)) :
    K ≤ primeSetCore pi X := by
  rw [primeSetCore]
  exact le_sSup ⟨hKX, hKnormal, hKpi⟩

private theorem primeSetCore_le'
    {G : Type u} [Group G] (pi : Set ℕ) (X : Subgroup G) :
    primeSetCore pi X ≤ X := by
  rw [primeSetCore]
  exact sSup_le fun _ hK => hK.1

/-- An ambient automorphism preserving `X` also preserves its prime-set
core. -/
theorem primeSetCore_map_equiv_of_map_eq
    {G : Type u} [Group G]
    (pi : Set ℕ) (X : Subgroup G) (e : G ≃* G)
    (hX : X.map e.toMonoidHom = X) :
    (primeSetCore pi X).map e.toMonoidHom = primeSetCore pi X := by
  have map_le (f : G ≃* G) (hXf : X.map f.toMonoidHom = X) :
      (primeSetCore pi X).map f.toMonoidHom ≤ primeSetCore pi X := by
    let S : Set (Subgroup G) :=
      {K | K ≤ X ∧ (K.subgroupOf X).Normal ∧
        IsPiNumber pi (Nat.card K)}
    change (sSup S).map f.toMonoidHom ≤ primeSetCore pi X
    rw [Subgroup.map_le_iff_le_comap]
    apply sSup_le
    intro K hK
    change K ≤ (primeSetCore pi X).comap f.toMonoidHom
    rw [← Subgroup.map_le_iff_le_comap]
    have hKS :
        K ≤ X ∧ (K.subgroupOf X).Normal ∧
          IsPiNumber pi (Nat.card K) := hK
    have hKX : K ≤ X := hKS.1
    have hmapX : K.map f.toMonoidHom ≤ X := by
      calc
        K.map f.toMonoidHom ≤ X.map f.toMonoidHom :=
          Subgroup.map_mono hKX
        _ = X := hXf
    have hXnormK : X ≤ Subgroup.normalizer (K : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hKX).mp
        hKS.2.1
    have hXnormMap :
        X ≤ Subgroup.normalizer
          (K.map f.toMonoidHom : Set G) := by
      have hmapped :
          X.map f.toMonoidHom ≤
            (Subgroup.normalizer (K : Set G)).map f.toMonoidHom :=
        Subgroup.map_mono hXnormK
      rw [hXf] at hmapped
      exact hmapped.trans (K.le_normalizer_map f.toMonoidHom)
    have hmapNormal :
        ((K.map f.toMonoidHom).subgroupOf X).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hmapX).mpr hXnormMap
    have hmapPi :
        IsPiNumber pi (Nat.card (K.map f.toMonoidHom)) := by
      rw [Subgroup.card_map_of_injective f.injective]
      exact hKS.2.2
    exact le_primeSetCore (pi := pi) (K := K.map f.toMonoidHom)
      (X := X) hmapX hmapNormal hmapPi
  apply le_antisymm (map_le e hX)
  have hXsymm : X.map e.symm.toMonoidHom = X := by
    have h := congrArg
      (fun Y : Subgroup G => Y.map e.symm.toMonoidHom) hX
    simpa [Subgroup.map_map] using h.symm
  have hback := map_le e.symm hXsymm
  have hmapped :
    ((primeSetCore pi X).map e.symm.toMonoidHom).map e.toMonoidHom ≤
      (primeSetCore pi X).map e.toMonoidHom :=
    Subgroup.map_mono hback
  simpa [Subgroup.map_map] using hmapped

/-- A subgroup normalizing `X` also normalizes its prime-set core. -/
theorem le_normalizer_primeSetCore_of_le_normalizer
    {G : Type u} [Group G]
    (pi : Set ℕ) {X N : Subgroup G}
    (hNX : N ≤ Subgroup.normalizer (X : Set G)) :
    N ≤ Subgroup.normalizer ((primeSetCore pi X : Subgroup G) : Set G) := by
  intro n hn
  have hnX := hNX hn
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hnX ⊢
  exact primeSetCore_map_equiv_of_map_eq pi X (MulAut.conj n) hnX

/-- The prime-set core of `C_G(P)` is normal in `N_G(P)`. -/
theorem primeSetCore_centralizer_normal_in_normalizer
    {G : Type u} [Group G]
    (pi : Set ℕ) (P : Subgroup G) :
    ((primeSetCore pi (Subgroup.centralizer (P : Set G))).subgroupOf
      (Subgroup.normalizer (P : Set G))).Normal := by
  let C : Subgroup G := Subgroup.centralizer (P : Set G)
  let N : Subgroup G := Subgroup.normalizer (P : Set G)
  let K : Subgroup G := primeSetCore pi C
  have hCN : C ≤ N := by
    simpa [C, N] using Subgroup.centralizer_le_normalizer (P : Set G)
  have hNnormC : N ≤ Subgroup.normalizer (C : Set G) := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hCN).mp
    simpa [C, N] using
      Subgroup.normal_subgroupOf_centralizer_normalizer (P : Set G)
  have hKN : K ≤ N :=
    (primeSetCore_le' pi C).trans hCN
  apply (Subgroup.normal_subgroupOf_iff_le_normalizer hKN).mpr
  exact le_normalizer_primeSetCore_of_le_normalizer pi hNnormC

private theorem le_normal_isHall_of_isPiNumber
    {G : Type u} [Group G] [Finite G]
    {pi : Set ℕ} {C K L : Subgroup G}
    (hKnormal : (K.subgroupOf C).Normal)
    (hKHall : IsHall pi (K.subgroupOf C))
    (hLC : L ≤ C) (hLpi : IsPiNumber pi (Nat.card L)) :
    L ≤ K := by
  let KC : Subgroup C := K.subgroupOf C
  letI : KC.Normal := by simpa [KC] using hKnormal
  have hcop : (Nat.card L).Coprime KC.index := by
    apply Nat.coprime_of_dvd
    intro p hp hpL hpIndex
    have hpPi : p ∈ pi := hLpi hp hpL
    have hpNotPi : p ∈ piᶜ := hKHall.isPiNumber_index hp hpIndex
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

/-- If `A ≤ B`, then the elements of the prime-complement core of
`C_G(A)` centralizing `B` form the prime-complement core of `C_G(B)`.
This is the local identity `defK` in Bender--Glauberman Theorem 7.4. -/
theorem centralizerWithin_centralPrimeComplementCore_eq_primeSetCore
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    (A B : Subgroup G)
    (cstrA : NormedConstrained A)
    (hAB : A ≤ B) :
    centralizerWithin (centralPrimeComplementCore A) B =
      primeSetCore (primeSupport (Nat.card A))ᶜ
        (Subgroup.centralizer (B : Set G)) := by
  let pi : Set ℕ := primeSupport (Nat.card A)
  let CA : Subgroup G := Subgroup.centralizer (A : Set G)
  let CB : Subgroup G := Subgroup.centralizer (B : Set G)
  let K : Subgroup G := centralPrimeComplementCore A
  let L : Subgroup G := primeSetCore piᶜ CB
  change K ⊓ CB = L
  have hCBCA : CB ≤ CA := by
    simpa [CB, CA] using Subgroup.centralizer_le hAB
  have hKCA : K ≤ CA := by
    simpa [K, CA, pi, centralPrimeComplementCore] using
      (primeSetCore_le piᶜ CA)
  have hKHall : IsHall piᶜ (K.subgroupOf CA) := by
    simpa [K, CA, pi] using normed_constrained_Hall A cstrA
  have hKpi : IsPiNumber piᶜ (Nat.card K) := by
    have h := hKHall.isPiNumber_card
    rw [natCard_subgroupOf_eq hKCA] at h
    exact h
  have hCAnormK : CA ≤ Subgroup.normalizer (K : Set G) := by
    simpa [K, CA, pi, centralPrimeComplementCore] using
      (le_normalizer_primeSetCore_of_le_normalizer
        (G := G) piᶜ (X := CA) (N := CA) Subgroup.le_normalizer)
  have hCBnormK : CB ≤ Subgroup.normalizer (K : Set G) :=
    hCBCA.trans hCAnormK
  have hDnormal : ((K ⊓ CB).subgroupOf CB).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr
    exact (le_inf hCBnormK Subgroup.le_normalizer).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hDpi : IsPiNumber piᶜ (Nat.card (K ⊓ CB : Subgroup G)) :=
    hKpi.of_dvd (Subgroup.card_dvd_of_le inf_le_left)
  have hleft : K ⊓ CB ≤ L := by
    dsimp [L]
    exact le_primeSetCore inf_le_right hDnormal hDpi
  have hLCB : L ≤ CB := by
    dsimp [L]
    exact primeSetCore_le piᶜ CB
  have hLCA : L ≤ CA := hLCB.trans hCBCA
  have hLpi : IsPiNumber piᶜ (Nat.card L) := by
    dsimp [L]
    exact primeSetCore_isPiNumber piᶜ CB
  have hLleK : L ≤ K :=
    le_normal_isHall_of_isPiNumber
      (by simpa [K, CA] using centralPrimeComplementCore_normal A)
      hKHall hLCA hLpi
  exact le_antisymm hleft (le_inf hLleK hLCB)

end Submission.OddOrder.BG.Section07
