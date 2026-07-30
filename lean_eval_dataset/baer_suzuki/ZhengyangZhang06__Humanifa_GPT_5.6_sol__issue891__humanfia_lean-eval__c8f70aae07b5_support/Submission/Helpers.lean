import ChallengeDeps

open LeanEval.GroupTheory
open LeanEval.GroupTheory.Defs
open scoped Pointwise

namespace Submission.Helpers

universe u

theorem pCore_normal {G : Type*} [Group G] (p : ℕ) : (pCore p G).Normal := by
  rw [pCore]
  exact Subgroup.sSup_normal _ fun N hN => hN.1

theorem pCore_isPGroup {G : Type*} [Group G] {p : ℕ} [Fact p.Prime] :
    IsPGroup p (pCore p G) := by
  rw [pCore]
  exact Sylow.sSup_of_normal _ (fun N hN => hN.2) (fun N hN => hN.1)

theorem le_pCore {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    {P : Subgroup G} (hP : P.Normal) (hpP : IsPGroup p P) :
    P ≤ pCore p G := by
  rw [pCore]
  exact le_sSup ⟨hP, hpP⟩

theorem pCore_eq_top_of_isPGroup {G : Type*} [Group G]
    {p : ℕ} [Fact p.Prime] (hG : IsPGroup p G) :
    pCore p G = ⊤ := by
  apply top_unique
  exact le_pCore Subgroup.normal_top (hG.to_subgroup ⊤)

theorem pCore_characteristic {G : Type*} [Group G]
    {p : ℕ} [Fact p.Prime] :
    (pCore p G).Characteristic := by
  rw [Subgroup.characteristic_iff_map_le]
  intro e
  exact le_pCore ((pCore_normal p).map e.toMonoidHom e.surjective)
    (pCore_isPGroup.map e.toMonoidHom)

theorem map_pCore_equiv {G K : Type*} [Group G] [Group K]
    {p : ℕ} [Fact p.Prime] (e : G ≃* K) :
    (pCore p G).map e.toMonoidHom = pCore p K := by
  apply le_antisymm
  · exact le_pCore ((pCore_normal p).map e.toMonoidHom e.surjective)
      (pCore_isPGroup.map e.toMonoidHom)
  · intro y hy
    have hsymm : (pCore p K).map e.symm.toMonoidHom ≤ pCore p G :=
      le_pCore ((pCore_normal p).map e.symm.toMonoidHom e.symm.surjective)
        (pCore_isPGroup.map e.symm.toMonoidHom)
    exact ⟨e.symm y, hsymm ⟨y, hy, rfl⟩, e.apply_symm_apply y⟩

theorem mem_pCore_of_mem_pCore_normal {G : Type*} [Group G]
    {H K : Subgroup G} (hHK : H ≤ K)
    (hN : (H.subgroupOf K).Normal) {p : ℕ} [Fact p.Prime]
    (x : H) (hx : x ∈ pCore p H) :
    (⟨x, hHK x.property⟩ : K) ∈ pCore p K := by
  let J : Subgroup K := H.subgroupOf K
  let e : H ≃* J := (Subgroup.subgroupOfEquivOfLe hHK).symm
  have hxe : e x ∈ pCore p J := by
    rw [← map_pCore_equiv e]
    exact ⟨x, hx, rfl⟩
  letI : J.Normal := hN
  letI : (pCore p J).Characteristic := pCore_characteristic
  have hnormal : ((pCore p J).map J.subtype).Normal := inferInstance
  apply le_pCore hnormal (pCore_isPGroup.map J.subtype)
  exact ⟨e x, hxe, rfl⟩

theorem baerSuzuki_forward {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    (x : G) (hx : x ∈ pCore p G) (g : G) :
    IsPGroup p (Subgroup.closure ({x, g * x * g⁻¹} : Set G)) := by
  apply pCore_isPGroup.to_le
  rw [Subgroup.closure_le]
  intro y hy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  rcases hy with rfl | rfl
  · exact hx
  · exact (pCore_normal p).conj_mem x hx g

theorem singletonClosure_isPGroup_of_pairwise {G : Type*} [Group G]
    {p : ℕ} [Fact p.Prime] (x : G)
    (h : ∀ g : G, IsPGroup p
      (Subgroup.closure ({x, g * x * g⁻¹} : Set G))) :
    IsPGroup p (Subgroup.closure ({x} : Set G)) := by
  have h1 := h 1
  have hs : ({x, (1 : G) * x * 1⁻¹} : Set G) = {x} := by
    ext y
    simp
  rw [hs] at h1
  exact h1

theorem singletonClosure_sup_conjugate {G : Type*} [Group G] (x g : G) :
    Subgroup.closure ({x} : Set G) ⊔
        (Subgroup.closure ({x} : Set G)).map (MulAut.conj g).toMonoidHom =
      Subgroup.closure ({x, g * x * g⁻¹} : Set G) := by
  apply le_antisymm
  · apply sup_le
    · rw [Subgroup.closure_le]
      intro y hy
      simp only [Set.mem_singleton_iff] at hy
      subst y
      exact Subgroup.subset_closure (by simp)
    · change (Subgroup.closure ({x} : Set G)).map
          (MulAut.conj g).toMonoidHom ≤ _
      rw [MonoidHom.map_closure, Subgroup.closure_le]
      rintro y ⟨z, hz, rfl⟩
      simp only [Set.mem_singleton_iff] at hz
      subst z
      exact Subgroup.subset_closure (by simp)
  · rw [Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with hy | hy
    · rw [hy]
      exact (show Subgroup.closure ({x} : Set G) ≤ _ from le_sup_left)
        (Subgroup.subset_closure (Set.mem_singleton x))
    · rw [hy]
      apply (show (Subgroup.closure ({x} : Set G)).map
          (MulAut.conj g).toMonoidHom ≤ _ from le_sup_right)
      exact ⟨x, Subgroup.subset_closure (Set.mem_singleton x), rfl⟩

theorem subgroup_isSubnormal_of_isPGroup {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (hG : IsPGroup p G) (H : Subgroup G) :
    H.IsSubnormal := by
  classical
  letI : Group.IsNilpotent G := hG.isNilpotent
  induction H using WellFoundedGT.induction with
  | ind H ih =>
      by_cases hH : H = ⊤
      · subst H
        exact Subgroup.IsSubnormal.top
      · have hlt : H < Subgroup.normalizer H :=
          Group.normalizerCondition_of_isNilpotent H (lt_top_iff_ne_top.mpr hH)
        exact Subgroup.IsSubnormal.step H (Subgroup.normalizer H) hlt.le
          (ih _ hlt) inferInstance

theorem singletonClosure_subnormal_in_conjugate_join
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (x g : G)
    (hp : IsPGroup p (Subgroup.closure ({x, g * x * g⁻¹} : Set G))) :
    (Subgroup.closure ({x} : Set G)).subgroupOf
      (Subgroup.closure ({x} : Set G) ⊔
        (Subgroup.closure ({x} : Set G)).map
          (MulAut.conj g).toMonoidHom) |>.IsSubnormal := by
  have hpK : IsPGroup p
      ((Subgroup.closure ({x} : Set G) ⊔
        (Subgroup.closure ({x} : Set G)).map
          (MulAut.conj g).toMonoidHom : Subgroup G)) := by
    rw [singletonClosure_sup_conjugate x g]
    exact hp
  exact subgroup_isSubnormal_of_isPGroup hpK
    ((Subgroup.closure ({x} : Set G)).subgroupOf
      (Subgroup.closure ({x} : Set G) ⊔
        (Subgroup.closure ({x} : Set G)).map
          (MulAut.conj g).toMonoidHom))

theorem singletonClosure_locally_subnormal_of_pairwise
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (x : G)
    (h : ∀ g : G, IsPGroup p
      (Subgroup.closure ({x, g * x * g⁻¹} : Set G))) :
    ∀ g : G,
      (Subgroup.closure ({x} : Set G)).subgroupOf
        (Subgroup.closure ({x} : Set G) ⊔
          (Subgroup.closure ({x} : Set G)).map
            (MulAut.conj g).toMonoidHom) |>.IsSubnormal := by
  intro g
  exact singletonClosure_subnormal_in_conjugate_join x g (h g)

theorem conjugatePair_isPGroup_of_pairwise {G : Type*} [Group G]
    {p : ℕ} [Fact p.Prime] (x : G)
    (h : ∀ g : G, IsPGroup p
      (Subgroup.closure ({x, g * x * g⁻¹} : Set G)))
    (a b : G) :
    IsPGroup p (Subgroup.closure
      ({a * x * a⁻¹, b * x * b⁻¹} : Set G)) := by
  have hp := (h (a⁻¹ * b)).map (MulAut.conj a).toMonoidHom
  rw [MonoidHom.map_closure] at hp
  have hs : (MulAut.conj a).toMonoidHom ''
      ({x, (a⁻¹ * b) * x * (a⁻¹ * b)⁻¹} : Set G) =
      ({a * x * a⁻¹, b * x * b⁻¹} : Set G) := by
    ext y
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨z, (rfl | rfl), rfl⟩
      · exact Or.inl (by simp)
      · exact Or.inr (by simp [mul_assoc])
    · rintro (rfl | rfl)
      · exact ⟨x, Or.inl rfl, by simp⟩
      · exact ⟨a⁻¹ * b * x * (a⁻¹ * b)⁻¹, Or.inr rfl,
          by simp [mul_assoc]⟩
  rw [hs] at hp
  exact hp

theorem pairwise_restrict
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (x : G) (K : Subgroup G) (hx : x ∈ K)
    (h : ∀ g : G, IsPGroup p
      (Subgroup.closure ({x, g * x * g⁻¹} : Set G))) :
    ∀ g : K, IsPGroup p
      (Subgroup.closure
        ({(⟨x, hx⟩ : K), g * (⟨x, hx⟩ : K) * g⁻¹} : Set K)) := by
  intro g
  let L : Subgroup K := Subgroup.closure
    ({(⟨x, hx⟩ : K), g * (⟨x, hx⟩ : K) * g⁻¹} : Set K)
  have himage : K.subtype ''
      ({(⟨x, hx⟩ : K), g * (⟨x, hx⟩ : K) * g⁻¹} : Set K) =
      ({x, (g : G) * x * (g : G)⁻¹} : Set G) := by
    ext y
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨z, (rfl | rfl), rfl⟩
      · exact Or.inl rfl
      · exact Or.inr rfl
    · intro hy
      rcases hy with hy | hy
      · exact ⟨⟨x, hx⟩, Or.inl rfl, hy.symm⟩
      · exact ⟨g * (⟨x, hx⟩ : K) * g⁻¹, Or.inr rfl, hy.symm⟩
  have hmap : L.map K.subtype =
      Subgroup.closure ({x, (g : G) * x * (g : G)⁻¹} : Set G) := by
    change (Subgroup.closure
      ({(⟨x, hx⟩ : K), g * (⟨x, hx⟩ : K) * g⁻¹} : Set K)).map
        K.subtype = _
    rw [MonoidHom.map_closure, himage]
  have hpmap : IsPGroup p (L.map K.subtype) := by
    rw [hmap]
    exact h g
  exact hpmap.of_equiv
    (L.equivMapOfInjective K.subtype K.subtype_injective).symm

theorem subgroup_card_lt
    {G : Type*} [Group G] [Finite G] {K : Subgroup G} (hK : K < ⊤) :
    Nat.card K < Nat.card G := by
  change Nat.card (K : Set G) < Nat.card G
  rw [Nat.card_coe_set_eq]
  apply Set.ncard_lt_card
  intro h
  apply hK.ne
  ext y
  simp only [Subgroup.mem_top, iff_true]
  change y ∈ (K : Set G)
  rw [h]
  exact Set.mem_univ y

theorem mem_pCore_proper_subgroup_of_induction
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hind : ∀ {K : Type u} [Group K] [Finite K],
      Nat.card K < Nat.card G → ∀ y : K,
        y ∈ pCore p K ↔
          ∀ k : K, IsPGroup p
            (Subgroup.closure ({y, k * y * k⁻¹} : Set K)))
    (x : G) (K : Subgroup G) (hx : x ∈ K) (hK : K < ⊤)
    (h : ∀ g : G, IsPGroup p
      (Subgroup.closure ({x, g * x * g⁻¹} : Set G))) :
    (⟨x, hx⟩ : K) ∈ pCore p K := by
  apply (hind (subgroup_card_lt hK) (⟨x, hx⟩ : K)).2
  exact pairwise_restrict x K hx h

theorem normalClosure_singleton_isPGroup_proper_subgroup
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hind : ∀ {K : Type u} [Group K] [Finite K],
      Nat.card K < Nat.card G → ∀ y : K,
        y ∈ pCore p K ↔
          ∀ k : K, IsPGroup p
            (Subgroup.closure ({y, k * y * k⁻¹} : Set K)))
    (x : G) (K : Subgroup G) (hx : x ∈ K) (hK : K < ⊤)
    (h : ∀ g : G, IsPGroup p
      (Subgroup.closure ({x, g * x * g⁻¹} : Set G))) :
    IsPGroup p
      (Subgroup.normalClosure ({(⟨x, hx⟩ : K)} : Set K)) := by
  apply pCore_isPGroup.to_le
  letI : (pCore p K).Normal := pCore_normal p
  apply Subgroup.normalClosure_le_normal
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst y
  exact mem_pCore_proper_subgroup_of_induction hind x K hx hK h

theorem singletonClosure_subnormal_proper_subgroup_of_induction
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hind : ∀ {K : Type u} [Group K] [Finite K],
      Nat.card K < Nat.card G → ∀ y : K,
        y ∈ pCore p K ↔
          ∀ k : K, IsPGroup p
            (Subgroup.closure ({y, k * y * k⁻¹} : Set K)))
    (x : G) (K : Subgroup G) (hx : x ∈ K) (hK : K < ⊤)
    (h : ∀ g : G, IsPGroup p
      (Subgroup.closure ({x, g * x * g⁻¹} : Set G))) :
    (Subgroup.closure ({(⟨x, hx⟩ : K)} : Set K)).IsSubnormal := by
  let H : Subgroup K := Subgroup.closure ({(⟨x, hx⟩ : K)} : Set K)
  have hxcore : (⟨x, hx⟩ : K) ∈ pCore p K :=
    mem_pCore_proper_subgroup_of_induction hind x K hx hK h
  have hle : H ≤ pCore p K := by
    change Subgroup.closure ({(⟨x, hx⟩ : K)} : Set K) ≤ pCore p K
    rw [Subgroup.closure_le]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    simpa [hy] using hxcore
  apply Subgroup.IsSubnormal.trans hle
  · exact subgroup_isSubnormal_of_isPGroup pCore_isPGroup
      (H.subgroupOf (pCore p K))
  · exact (pCore_normal p).isSubnormal

theorem isPGroup_closure_pair_iff_exists_sylow
    {G : Type*} [Group G] {p : ℕ} [Fact p.Prime] (a b : G) :
    IsPGroup p (Subgroup.closure ({a, b} : Set G)) ↔
      ∃ P : Sylow p G, a ∈ P ∧ b ∈ P := by
  constructor
  · intro hp
    obtain ⟨P, hP⟩ := hp.exists_le_sylow
    exact ⟨P, hP (Subgroup.subset_closure (by simp)),
      hP (Subgroup.subset_closure (by simp))⟩
  · rintro ⟨P, ha, hb⟩
    apply P.isPGroup'.to_le
    rw [Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact ha
    · exact hb

theorem mem_pCore_iff_mem_all_sylow
    {G : Type*} [Group G] {p : ℕ} [Fact p.Prime] (x : G) :
    x ∈ pCore p G ↔ ∀ P : Sylow p G, x ∈ P := by
  constructor
  · intro hx P
    letI : (pCore p G).Normal := pCore_normal p
    exact (pCore_isPGroup.le_sylow_of_normal P) hx
  · intro hx
    let P : Sylow p G := Classical.arbitrary (Sylow p G)
    apply le_pCore P.normalCore_normal
      (P.isPGroup'.to_le P.normalCore_le)
    intro g
    have hxg := hx (g⁻¹ • P)
    change x ∈ (MulAut.conj g⁻¹) • (P : Subgroup G) at hxg
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hxg
    simpa [MulAut.inv_def, MulAut.conj_apply] using hxg

theorem mem_pCore_iff_exists_sylow_containing_conjugates
    {G : Type*} [Group G] {p : ℕ} [Fact p.Prime] (x : G) :
    x ∈ pCore p G ↔
      ∃ P : Sylow p G, Group.conjugatesOfSet ({x} : Set G) ⊆ P := by
  constructor
  · intro hx
    let P : Sylow p G := Classical.arbitrary (Sylow p G)
    letI : (pCore p G).Normal := pCore_normal p
    refine ⟨P, (Group.conjugatesOfSet_subset ?_).trans
      (pCore_isPGroup.le_sylow_of_normal P)⟩
    simpa using hx
  · rintro ⟨P, hP⟩
    have hpN : IsPGroup p (Subgroup.normalClosure ({x} : Set G)) := by
      rw [Subgroup.normalClosure]
      apply P.isPGroup'.to_le
      rwa [Subgroup.closure_le]
    apply le_pCore Subgroup.normalClosure_normal hpN
    exact Subgroup.subset_normalClosure (Set.mem_singleton x)

theorem isPGroup_le_pCore_of_isSubnormal {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {H : Subgroup G} (hH : IsPGroup p H)
    (hS : H.IsSubnormal) :
    H ≤ pCore p G := by
  intro x hx
  obtain ⟨n, f, hf, hnormal, f0, fn⟩ := hS.exists_chain
  have hxmem (i : ℕ) : x ∈ f i := by
    apply hf (Nat.zero_le i)
    rw [f0]
    exact hx
  have hxcore : ∀ i : ℕ, (⟨x, hxmem i⟩ : f i) ∈ pCore p (f i) := by
    intro i
    induction i with
    | zero =>
        have hf0 : IsPGroup p (f 0) := by
          rw [f0]
          exact hH
        rw [pCore_eq_top_of_isPGroup hf0]
        exact Subgroup.mem_top _
    | succ i ih =>
        exact mem_pCore_of_mem_pCore_normal (hf (Nat.le_succ i)) (hnormal i)
          ⟨x, hxmem i⟩ ih
  have hn := hxcore n
  letI : (f n).Normal := fn ▸ Subgroup.normal_top
  letI : (pCore p (f n)).Characteristic := pCore_characteristic
  have hnormal : ((pCore p (f n)).map (f n).subtype).Normal := inferInstance
  apply le_pCore hnormal (pCore_isPGroup.map (f n).subtype)
  exact ⟨⟨x, hxmem n⟩, hn, rfl⟩

theorem mem_pCore_of_singletonClosure_isSubnormal
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (x : G)
    (h : ∀ g : G, IsPGroup p
      (Subgroup.closure ({x, g * x * g⁻¹} : Set G)))
    (hS : (Subgroup.closure ({x} : Set G)).IsSubnormal) :
    x ∈ pCore p G := by
  apply isPGroup_le_pCore_of_isSubnormal
    (singletonClosure_isPGroup_of_pairwise x h) hS
  exact Subgroup.subset_closure (Set.mem_singleton x)

end Submission.Helpers
