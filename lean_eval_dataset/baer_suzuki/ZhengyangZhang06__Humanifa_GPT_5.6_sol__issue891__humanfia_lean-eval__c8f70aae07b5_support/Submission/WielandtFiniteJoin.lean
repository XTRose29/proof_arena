import Submission.WielandtJoin

open scoped Pointwise

namespace Submission.Helpers

universe u

/-- The join of two subnormal subgroups of a finite group is subnormal. -/
theorem isSubnormal_sup_finite
    {G : Type u} [Group G] [Finite G] (A B : Subgroup G)
    (hA : A.IsSubnormal) (hB : B.IsSubnormal) :
    (A ⊔ B).IsSubnormal := by
  classical
  induction hcard : Nat.card G using Nat.strong_induction_on generalizing G with
  | h n ih =>
      by_contra hAB
      let Bad := fun X : Subgroup G =>
        X.IsSubnormal ∧ ¬(X ⊔ B).IsSubnormal
      obtain ⟨C, hAC, hCmax⟩ :=
        Finite.exists_le_maximal (p := Bad) (a := A) ⟨hA, hAB⟩
      have hC : C.IsSubnormal :=
        hCmax.prop.1
      have hCB : ¬(C ⊔ B).IsSubnormal :=
        hCmax.prop.2
      have hCnotNormal : ¬C.Normal := by
        intro hnormal
        exact hCB (isSubnormal_sup_of_normal_left hnormal hB)
      obtain hCtop | ⟨X, hCX, hX, hCnormalX⟩ :=
        Subgroup.IsSubnormal.iff_eq_top_or_exists.mp hC
      · subst C
        have htop : (⊤ : Subgroup G) ⊔ B = ⊤ :=
          top_unique le_sup_left
        rw [htop] at hCB
        exact hCB .top
      have hXtop : X ≠ ⊤ := by
        intro htop
        have hnormalizer :
            X ≤ Subgroup.normalizer (C : Set G) :=
          (Subgroup.normal_subgroupOf_iff_le_normalizer hCX.le).mp
            hCnormalX
        rw [htop, top_le_iff, Subgroup.normalizer_eq_top_iff] at hnormalizer
        exact hCnotNormal hnormalizer
      obtain ⟨G₁, hG₁normal, hXG₁, hG₁top⟩ :=
        hX.exists_normal_and_le_and_lt_top_of_ne hXtop
      letI : G₁.Normal := hG₁normal
      have hCG₁ : C ≤ G₁ :=
        hCX.le.trans hXG₁
      have hcardG₁ : Nat.card G₁ < n := by
        rw [← hcard]
        exact subgroup_card_lt hG₁top
      have hjoinG₁ :
          ∀ D E : Subgroup G₁,
            D.IsSubnormal → E.IsSubnormal →
              (D ⊔ E).IsSubnormal := by
        intro D E hD hE
        exact ih (Nat.card G₁) hcardG₁ D E hD hE rfl
      let F : Set (Subgroup G) :=
        {D | ∃ b : B, D = (MulAut.conj (b : G)) • C}
      let K : Subgroup G := sSup F
      have hFleG₁ : ∀ D ∈ F, D ≤ G₁ := by
        intro D hD
        obtain ⟨b, rfl⟩ := hD
        rintro y ⟨z, hz, rfl⟩
        exact hG₁normal.conj_mem z (hCG₁ hz) b
      have hFsubnormal :
          ∀ D ∈ F, (D.subgroupOf G₁).IsSubnormal := by
        intro D hD
        obtain ⟨b, rfl⟩ := hD
        exact (hC.smul (MulAut.conj (b : G))).subgroupOf
      have hfinset :
          ∀ s : Finset (Subgroup G),
            (∀ D ∈ s, D ≤ G₁) →
            (∀ D ∈ s, (D.subgroupOf G₁).IsSubnormal) →
            ((s.sup id).subgroupOf G₁).IsSubnormal := by
        intro s
        induction s using Finset.induction with
        | empty =>
            simp
        | @insert D s hDs hs =>
            intro hle hsubnormal
            have hDG₁ : D ≤ G₁ :=
              hle D (by simp)
            have hsG₁ : s.sup id ≤ G₁ :=
              Finset.sup_le fun E hE =>
                hle E (by simp [hE])
            rw [Finset.sup_insert]
            change ((D ⊔ s.sup id).subgroupOf G₁).IsSubnormal
            rw [Subgroup.subgroupOf_sup hDG₁ hsG₁]
            apply hjoinG₁
            · exact hsubnormal D (by simp)
            · apply hs
              · intro E hE
                exact hle E (by simp [hE])
              · intro E hE
                exact hsubnormal E (by simp [hE])
      let s : Finset (Subgroup G) := F.toFinite.toFinset
      have hsF : (s : Set (Subgroup G)) = F := by
        ext D
        simp [s]
      have hsup : s.sup id = K := by
        rw [Finset.sup_id_eq_sSup, hsF]
      have hKleG₁ : K ≤ G₁ := by
        change sSup F ≤ G₁
        exact sSup_le hFleG₁
      have hKsubnormalG₁ :
          (K.subgroupOf G₁).IsSubnormal := by
        rw [← hsup]
        apply hfinset s
        · intro D hD
          exact hFleG₁ D (hsF ▸ hD)
        · intro D hD
          exact hFsubnormal D (hsF ▸ hD)
      have hKsubnormal : K.IsSubnormal :=
        Subgroup.IsSubnormal.trans hKleG₁ hKsubnormalG₁
          hG₁normal.isSubnormal
      have hCK : C ≤ K := by
        change C ≤ sSup F
        apply le_sSup
        exact ⟨(1 : B), by simp⟩
      have hKleCB : K ≤ C ⊔ B := by
        change sSup F ≤ C ⊔ B
        apply sSup_le
        intro D hD
        obtain ⟨b, rfl⟩ := hD
        exact Subgroup.conj_smul_le_of_le le_sup_left
          (⟨(b : G),
            (show B ≤ C ⊔ B from le_sup_right) b.property⟩ :
            ↥(C ⊔ B))
      have hKsupB : K ⊔ B = C ⊔ B := by
        apply le_antisymm
        · exact sup_le hKleCB le_sup_right
        · exact sup_le (hCK.trans le_sup_left) le_sup_right
      have hKbad : Bad K := by
        refine ⟨hKsubnormal, ?_⟩
        rwa [hKsupB]
      have hKC : K ≤ C :=
        hCmax.2 hKbad hCK
      have hKCeq : K = C :=
        le_antisymm hKC hCK
      have hBnormalizesK :
          B ≤ Subgroup.normalizer (K : Set G) := by
        intro b hb
        rw [Subgroup.mem_normalizer_iff_map_conj_eq]
        change (MulAut.conj b) • K = K
        have hforward (a : B) :
            (MulAut.conj (a : G)) • C ≤ C := by
          calc
            (MulAut.conj (a : G)) • C ≤ K := by
              change (MulAut.conj (a : G)) • C ≤ sSup F
              apply le_sSup
              exact ⟨a, rfl⟩
            _ = C := hKCeq
        rw [hKCeq]
        apply le_antisymm (hforward ⟨b, hb⟩)
        apply (Subgroup.subset_pointwise_smul_iff).2
        simpa [MulAut.inv_def] using
          hforward (⟨b, hb⟩ : B)⁻¹
      have hBX : B ≤ Subgroup.normalizer (C : Set G) := by
        rwa [← hKCeq]
      have hXnormalizesC :
          X ≤ Subgroup.normalizer (C : Set G) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hCX.le).mp
          hCnormalX
      have hXBnormalizes :
          X ⊔ B ≤ Subgroup.normalizer (C : Set G) :=
        sup_le hXnormalizesC hBX
      have hXBsubnormal : (X ⊔ B).IsSubnormal := by
        by_contra hbad
        have hXleC : X ≤ C :=
          hCmax.2 ⟨hX, hbad⟩ hCX.le
        exact hCX.ne' (le_antisymm hXleC hCX.le)
      by_cases hXBtop : X ⊔ B = ⊤
      · rw [hXBtop, top_le_iff,
          Subgroup.normalizer_eq_top_iff] at hXBnormalizes
        exact hCnotNormal hXBnormalizes
      · let L : Subgroup G := X ⊔ B
        have hLtop : L < ⊤ :=
          lt_top_iff_ne_top.mpr hXBtop
        have hcardL : Nat.card L < n := by
          rw [← hcard]
          exact subgroup_card_lt hLtop
        have hCsubL :
            (C.subgroupOf L).IsSubnormal := by
          exact hC.subgroupOf
        have hBsubL :
            (B.subgroupOf L).IsSubnormal := by
          exact hB.subgroupOf
        have hjoinL :
            ((C.subgroupOf L) ⊔ (B.subgroupOf L)).IsSubnormal :=
          ih (Nat.card L) hcardL _ _ hCsubL hBsubL rfl
        have hCBsubL :
            ((C ⊔ B).subgroupOf L).IsSubnormal := by
          rw [Subgroup.subgroupOf_sup
            (hCX.le.trans le_sup_left) le_sup_right]
          exact hjoinL
        exact hCB
          (Subgroup.IsSubnormal.trans
            (sup_le (hCX.le.trans le_sup_left) le_sup_right)
            hCBsubL hXBsubnormal)

/-- In a finite group, the subgroup generated by any family of subnormal
subgroups is subnormal. -/
theorem isSubnormal_sSup_finite
    {G : Type u} [Group G] [Finite G] (S : Set (Subgroup G))
    (hS : ∀ H ∈ S, H.IsSubnormal) :
    (sSup S).IsSubnormal := by
  classical
  let s : Finset (Subgroup G) := S.toFinite.toFinset
  have hsS : (s : Set (Subgroup G)) = S := by
    ext H
    simp [s]
  have aux :
      ∀ t : Finset (Subgroup G),
        (∀ H ∈ t, H.IsSubnormal) →
          (t.sup id).IsSubnormal := by
    intro t
    induction t using Finset.induction with
    | empty =>
        simp
    | @insert H t hHt ih =>
        intro ht
        rw [Finset.sup_insert]
        apply isSubnormal_sup_finite
        · exact ht H (by simp)
        · apply ih
          intro K hK
          exact ht K (by simp [hK])
  have hfinset : (s.sup id).IsSubnormal := by
    apply aux s
    intro H hH
    exact hS H (hsS ▸ hH)
  rwa [Finset.sup_id_eq_sSup, hsS] at hfinset

end Submission.Helpers
