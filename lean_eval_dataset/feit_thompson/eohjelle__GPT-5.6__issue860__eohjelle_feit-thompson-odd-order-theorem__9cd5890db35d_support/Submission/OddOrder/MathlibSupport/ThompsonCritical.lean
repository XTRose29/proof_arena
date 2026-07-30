import Submission.OddOrder.MathlibSupport.CommutatorSup
import Submission.OddOrder.MathlibSupport.Critical
import Submission.OddOrder.MathlibSupport.FrattiniPGroup
import Submission.OddOrder.MathlibSupport.PGroupCenter

/-!
Thompson's critical subgroup theorem.

The proof follows MathComp's `Thompson_critical`: choose a maximal
characteristic subgroup satisfying the two centrality conditions.  If it is
not self-centralizing, enlarge it using the first omega subgroup of the
center after quotienting by its center.  The Frattini condition for the
enlargement is recovered from the resulting elementary-abelian quotient.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped commutatorElement IsMulCommutative

universe u

variable {G : Type u} [Group G]

private structure IsCriticalCandidate (H : Subgroup G) : Prop where
  characteristic : H.Characteristic
  frattini_le_center : frattini H ≤ Subgroup.center H
  commutator_le_center : ⁅(⊤ : Subgroup G), H⁆ ≤ centerWithin H

private theorem isCriticalCandidate_bot :
    IsCriticalCandidate (⊥ : Subgroup G) := by
  refine ⟨inferInstance, ?_, ?_⟩
  · simp
  · simp [centerWithin, centralizerWithin]

private theorem exists_maximal_isCriticalCandidate [Finite G] :
    ∃ K : Subgroup G, IsCriticalCandidate K ∧
      ∀ {L : Subgroup G}, IsCriticalCandidate L → K ≤ L → L ≤ K := by
  classical
  let s : Set (Subgroup G) := {H | IsCriticalCandidate H}
  have hs : s.Nonempty := ⟨⊥, isCriticalCandidate_bot⟩
  obtain ⟨K, hK, hKmax⟩ := s.toFinite.exists_maximal hs
  exact ⟨K, hK, fun hL hKL ↦ hKmax hL hKL⟩

/-- MathComp's `Thompson_critical`: every finite `p`-group has a critical
subgroup. -/
theorem thompson_critical [Finite G] {p : ℕ} [Fact p.Prime]
    (hG : IsPGroup p G) :
    ∃ H : Subgroup G, IsCritical H := by
  classical
  obtain ⟨K, hK, hKmax⟩ := exists_maximal_isCriticalCandidate (G := G)
  letI : K.Characteristic := hK.characteristic
  let Z : Subgroup G := centerWithin K
  letI : Z.Characteristic := by
    dsimp [Z]
    infer_instance
  let C : Subgroup G := Subgroup.centralizer (K : Set G)
  letI : C.Characteristic := by
    dsimp [C]
    infer_instance
  have hZC : Z ≤ C := by
    dsimp [Z, C, centerWithin, centralizerWithin]
    exact inf_le_right
  have hCZ : C ≤ Z := by
    by_contra hCZ
    let q : G →* G ⧸ Z := QuotientGroup.mk' Z
    let Cbar : Subgroup (G ⧸ Z) := C.map q
    have hCbarNormal : Cbar.Normal := by
      dsimp [Cbar]
      exact Subgroup.Normal.map (show C.Normal from inferInstance) q
        (QuotientGroup.mk'_surjective Z)
    letI : Cbar.Normal := hCbarNormal
    have hCbarNe : Cbar ≠ ⊥ := by
      intro hbot
      apply hCZ
      have hCker : C ≤ q.ker := (Subgroup.map_eq_bot_iff C).mp hbot
      simpa [q, QuotientGroup.ker_mk'] using hCker
    have hQp : IsPGroup p (G ⧸ Z) := hG.to_quotient Z
    let M : Subgroup (G ⧸ Z) := Cbar ⊓ Subgroup.center (G ⧸ Z)
    have hMne : M ≠ ⊥ := by
      dsimp [M]
      exact normal_inf_center_ne_bot hQp Cbar hCbarNe
    have hMp : IsPGroup p M := hQp.to_subgroup M
    have hMcard : Nat.card M ≠ 1 :=
      (M.one_lt_card_iff_ne_bot.mpr hMne).ne'
    have hOmegaMne : omegaOne p M ≠ ⊥ :=
      omegaOne_ne_bot_of_isPGroup hMp hMcard
    obtain ⟨w, hwne⟩ :=
      Subgroup.ne_bot_iff_exists_ne_one.mp hOmegaMne
    have hwQne : (((w : M) : G ⧸ Z)) ≠ 1 := by
      intro hw
      apply hwne
      apply Subtype.ext
      apply Subtype.ext
      exact hw

    let W : Subgroup (G ⧸ Z) :=
      (omegaOne p (Subgroup.center (G ⧸ Z))).map
        (Subgroup.center (G ⧸ Z)).subtype
    have hWchar : W.Characteristic := by
      dsimp [W]
      infer_instance
    letI : W.Characteristic := hWchar
    have hWleCenter : W ≤ Subgroup.center (G ⧸ Z) := by
      dsimp [W]
      exact Subgroup.map_subtype_le _
    have hWpow : ∀ z : W, z ^ p = 1 := by
      rintro ⟨_, z, hzOmega, rfl⟩
      apply Subtype.ext
      change (z : G ⧸ Z) ^ p = 1
      simpa using congrArg Subtype.val
        (omegaOne_pow_eq_one_of_mul_closed p
          (fun a b ha hb ↦ by
            have hab : Commute a b := Std.Commutative.comm a b
            simpa [ha, hb] using hab.mul_pow p) hzOmega)

    let mCenter : M →* Subgroup.center (G ⧸ Z) :=
      M.subtype.codRestrict (Subgroup.center (G ⧸ Z)) fun m ↦ m.property.2
    have hwOmegaCenter :
        mCenter (w : M) ∈ omegaOne p (Subgroup.center (G ⧸ Z)) :=
      map_omegaOne_le p mCenter
        (Subgroup.mem_map_of_mem mCenter w.property)
    have hwW : (((w : M) : G ⧸ Z)) ∈ W :=
      ⟨mCenter (w : M), hwOmegaCenter, rfl⟩
    have hwCbar : (((w : M) : G ⧸ Z)) ∈ Cbar :=
      w.val.property.1
    obtain ⟨c, hcC, hqc⟩ := hwCbar

    let X : Subgroup G := C ⊓ W.comap q
    have hXchar : X.Characteristic := by
      dsimp [X]
      haveI : (W.comap q).Characteristic :=
        Subgroup.Characteristic.comap_quotient_mk hWchar
      infer_instance
    letI : X.Characteristic := hXchar
    have hXleC : X ≤ C := by
      dsimp [X]
      exact inf_le_left
    have hXleW : X ≤ W.comap q := by
      dsimp [X]
      exact inf_le_right
    have hZX : Z ≤ X := by
      intro z hz
      refine ⟨hZC hz, ?_⟩
      change q z ∈ W
      have hqz : q z = 1 := (QuotientGroup.eq_one_iff z).mpr hz
      rw [hqz]
      exact W.one_mem
    have hcX : c ∈ X := by
      refine ⟨hcC, ?_⟩
      change q c ∈ W
      rw [hqc]
      exact hwW
    have hcNotZ : c ∉ Z := by
      intro hcZ
      apply hwQne
      rw [← hqc]
      exact (QuotientGroup.eq_one_iff c).mpr hcZ
    have hXnotleZ : ¬ X ≤ Z := fun hXZ ↦ hcNotZ (hXZ hcX)

    have hXmapCenter : X.map q ≤ Subgroup.center (G ⧸ Z) := by
      rintro _ ⟨x, hx, rfl⟩
      exact hWleCenter (hXleW hx)
    have hXcomm : ⁅(⊤ : Subgroup G), X⁆ ≤ Z := by
      have hmapComm :
          ⁅(⊤ : Subgroup G).map q, X.map q⁆ = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro g _
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        exact (Subgroup.mem_center_iff.mp (hXmapCenter hx) g).symm
      have hmapBot : (⁅(⊤ : Subgroup G), X⁆).map q = ⊥ := by
        rw [Subgroup.map_commutator]
        exact hmapComm
      have hker : ⁅(⊤ : Subgroup G), X⁆ ≤ q.ker :=
        (Subgroup.map_eq_bot_iff _).mp hmapBot
      simpa [q, QuotientGroup.ker_mk'] using hker

    let L : Subgroup G := K ⊔ X
    have hLchar : L.Characteristic := by
      dsimp [L]
      infer_instance
    letI : L.Characteristic := hLchar
    have hZcenterL : Z ≤ centerWithin L := by
      intro z hz
      refine ⟨?_, ?_⟩
      · change z ∈ K ⊔ X
        exact Subgroup.mem_sup_left hz.1
      · change z ∈ Subgroup.centralizer (L : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have hy' : y ∈ K ⊔ X := hy
        rw [Subgroup.mem_sup_of_normal_right] at hy'
        obtain ⟨k, hk, x, hx, rfl⟩ := hy'
        have hkz : k * z = z * k := hz.2 k hk
        have hzx : z * x = x * z :=
          Subgroup.mem_centralizer_iff.mp (hXleC hx) z hz.1
        rw [mul_assoc, ← hzx, ← mul_assoc, hkz, mul_assoc]
    have hLcomm : ⁅(⊤ : Subgroup G), L⁆ ≤ centerWithin L := by
      have hcommZ : ⁅(⊤ : Subgroup G), K ⊔ X⁆ ≤ Z :=
        commutator_sup_le_of_normal hK.commutator_le_center hXcomm
      exact hcommZ.trans hZcenterL

    have hKmapCenter : K.map q ≤ Subgroup.center (G ⧸ Z) := by
      rintro _ ⟨k, hk, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective Z y
      rw [← commutatorElement_eq_one_iff_mul_comm,
        ← map_commutatorElement]
      exact (QuotientGroup.eq_one_iff _).mpr
        (hK.commutator_le_center
          (Subgroup.commutator_mem_commutator trivial hk))
    have hLmapCenter : L.map q ≤ Subgroup.center (G ⧸ Z) := by
      simpa [L, Subgroup.map_sup] using sup_le hKmapCenter hXmapCenter

    let Lbar : Subgroup (G ⧸ Z) := L.map q
    have hLbarComm : IsMulCommutative Lbar := by
      apply isMulCommutative_iff.mpr
      intro a b
      apply Subtype.ext
      exact
        (Subgroup.mem_center_iff.mp (hLmapCenter a.property) (b : G ⧸ Z)).symm
    letI : IsMulCommutative Lbar := hLbarComm
    have hXmapNormal : (X.map q).Normal :=
      Subgroup.Normal.map (show X.Normal from inferInstance) q
        (QuotientGroup.mk'_surjective Z)
    letI : (X.map q).Normal := hXmapNormal
    have hLbarPow : ∀ y : Lbar, y ^ p = 1 := by
      intro y
      have hySup : (y : G ⧸ Z) ∈ K.map q ⊔ X.map q := by
        simpa [Lbar, L, Subgroup.map_sup] using y.property
      rw [Subgroup.mem_sup_of_normal_right] at hySup
      obtain ⟨k, hk, x, hx, hkxy⟩ := hySup
      have hkpow : k ^ p = 1 := by
        obtain ⟨k, hkK, rfl⟩ := hk
        let kK : K := ⟨k, hkK⟩
        have hkFrattini : kK ^ p ∈ frattini K :=
          IsPGroup.pow_prime_mem_frattini (hG.to_subgroup K) kK
        have hkZ : k ^ p ∈ Z := by
          change k ^ p ∈ centerWithin K
          rw [← map_center_eq_centerWithin K]
          exact ⟨kK ^ p, hK.frattini_le_center hkFrattini, rfl⟩
        rw [← map_pow]
        exact (QuotientGroup.eq_one_iff _).mpr hkZ
      have hxpow : x ^ p = 1 := by
        obtain ⟨x, hxX, rfl⟩ := hx
        have hxW : q x ∈ W := hXleW hxX
        exact congrArg Subtype.val (hWpow ⟨q x, hxW⟩)
      apply Subtype.ext
      change (y : G ⧸ Z) ^ p = 1
      rw [← hkxy]
      have hkx : Commute k x := by
        exact (Subgroup.mem_center_iff.mp (hKmapCenter hk) x).symm
      rw [hkx.mul_pow, hkpow, hxpow, mul_one]

    let f : L →* Lbar :=
      (q.comp L.subtype).codRestrict Lbar fun l ↦
        Subgroup.mem_map_of_mem q l.property
    have hfSurj : Function.Surjective f := by
      rintro ⟨y, hy⟩
      obtain ⟨x, hx, hxy⟩ := hy
      refine ⟨⟨x, hx⟩, ?_⟩
      apply Subtype.ext
      exact hxy
    have hFrattiniL : frattini L ≤ Subgroup.center L := by
      have hFrattiniMap : frattini L ≤ (frattini Lbar).comap f :=
        frattini_le_comap_frattini_of_surjective hfSurj
      have hFrattiniBot : frattini Lbar = ⊥ :=
        IsPGroup.frattini_eq_bot_of_isMulCommutative_of_pow_prime hLbarPow
      intro a ha
      have hfa : f a = 1 := by
        have := hFrattiniMap ha
        rw [hFrattiniBot] at this
        exact Subgroup.mem_bot.mp this
      have haZ : (a : G) ∈ Z := by
        apply (QuotientGroup.eq_one_iff (a : G)).mp
        exact congrArg Subtype.val hfa
      rw [Subgroup.mem_center_iff]
      intro l
      apply Subtype.ext
      exact (mem_centerWithin.mp (hZcenterL haZ)).2 (l : G) l.property

    have hLcandidate : IsCriticalCandidate L :=
      ⟨hLchar, hFrattiniL, hLcomm⟩
    have hLleK : L ≤ K := hKmax hLcandidate le_sup_left
    have hXleK : X ≤ K := le_sup_right.trans hLleK
    apply hXnotleZ
    intro x hx
    exact ⟨hXleK hx, hXleC hx⟩

  exact ⟨K,
    { characteristic := hK.characteristic
      frattini_le_center := hK.frattini_le_center
      commutator_le_center := hK.commutator_le_center
      centralizer_eq_center := le_antisymm hCZ hZC }⟩

end Submission.OddOrder.MathlibSupport
