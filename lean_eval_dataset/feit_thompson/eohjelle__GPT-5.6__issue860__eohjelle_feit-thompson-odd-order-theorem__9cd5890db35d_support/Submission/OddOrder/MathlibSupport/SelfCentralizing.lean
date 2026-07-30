import Submission.OddOrder.MathlibSupport.NormalAbelian
import Submission.OddOrder.MathlibSupport.PGroupCenter

/-!
Self-centralizing normal abelian subgroups of finite `p`-groups.

This is the mathlib-shaped replacement for the `max_SCN`/`SCN_P` package used
by MathComp's proof of Bender--Glauberman Lemma B.1(f).
-/

namespace Submission.OddOrder.MathlibSupport

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- An inclusion-maximal normal abelian subgroup of a finite `p`-group is
self-centralizing. -/
theorem centralizer_eq_of_maximal_isNormalAbelian (hG : IsPGroup p G)
    {M : Subgroup G} (hM : IsNormalAbelian M)
    (hMmax : ∀ {A : Subgroup G}, IsNormalAbelian A → M ≤ A → A ≤ M) :
    Subgroup.centralizer (M : Set G) = M := by
  letI : M.Normal := hM.normal
  letI : IsMulCommutative M := hM.isMulCommutative
  let C : Subgroup G := Subgroup.centralizer (M : Set G)
  have hMC : M ≤ C := Subgroup.le_centralizer M
  apply le_antisymm ?_ hMC
  by_contra hCM
  letI : C.Normal := by
    dsimp [C]
    infer_instance
  let q : G →* G ⧸ M := QuotientGroup.mk' M
  let Cbar : Subgroup (G ⧸ M) := C.map q
  have hCbar : Cbar ≠ ⊥ := by
    intro hbot
    apply hCM
    have hCker : C ≤ q.ker := (Subgroup.map_eq_bot_iff C).mp hbot
    simpa [q, QuotientGroup.ker_mk'] using hCker
  letI : Cbar.Normal := by
    exact Subgroup.Normal.map (by infer_instance) q (QuotientGroup.mk'_surjective M)
  have hQ : IsPGroup p (G ⧸ M) := hG.to_quotient M
  have hmeet : Cbar ⊓ Subgroup.center (G ⧸ M) ≠ ⊥ :=
    normal_inf_center_ne_bot hQ Cbar hCbar
  have hmeetNontrivial : Nontrivial ↑(Cbar ⊓ Subgroup.center (G ⧸ M)) :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr hmeet
  obtain ⟨z, hz, hzOne⟩ :=
    (Subgroup.nontrivial_iff_exists_ne_one _).mp hmeetNontrivial
  let K : Subgroup (G ⧸ M) := Subgroup.zpowers z
  have hKCbar : K ≤ Cbar := Subgroup.zpowers_le.mpr hz.1
  have hKcenter : K ≤ Subgroup.center (G ⧸ M) :=
    Subgroup.zpowers_le.mpr hz.2
  have hKne : K ≠ ⊥ := by
    simpa [K, Subgroup.zpowers_eq_bot] using hzOne
  letI : K.Normal := by
    constructor
    intro k hk g
    have hkCenter := Subgroup.mem_center_iff.mp (hKcenter hk) g
    simpa [hkCenter] using hk
  let A : Subgroup G := K.comap q
  have hMA : M ≤ A := by
    exact QuotientGroup.le_comap_mk' M K
  have hAC : A ≤ C := by
    change K.comap q ≤ C
    apply (Subgroup.comap_mono hKCbar).trans_eq
    dsimp [Cbar]
    apply Subgroup.comap_map_eq_self
    simpa [q, QuotientGroup.ker_mk'] using hMC
  have hAnormal : A.Normal := by
    dsimp [A]
    infer_instance
  let f₀ : A →* (G ⧸ M) := q.comp A.subtype
  let f : A →* K := f₀.codRestrict K fun a => a.2
  have hfker : f.ker ≤ Subgroup.center A := by
    intro a ha
    apply Subgroup.mem_center_iff.mpr
    intro b
    apply Subtype.ext
    have hfa : f a = 1 := f.mem_ker.mp ha
    have hqa : q (a : G) = 1 := congrArg Subtype.val hfa
    have haM : (a : G) ∈ M := by
      exact QuotientGroup.eq_one_iff (a : G) |>.mp (by simpa [q] using hqa)
    have hbC : (b : G) ∈ C := hAC b.2
    exact (hbC (a : G) haM).symm
  have hAcomm : IsMulCommutative A :=
    f.isMulCommutative_of_isCyclic_of_ker_le_center hfker
  have hAnormAb : IsNormalAbelian A := ⟨hAnormal, hAcomm⟩
  have hAne : A ≠ M := by
    intro hAM
    apply hKne
    calc
      K = A.map q :=
        (Subgroup.map_comap_eq_self_of_surjective
          (QuotientGroup.mk'_surjective M) K).symm
      _ = M.map q := congrArg (fun H : Subgroup G => H.map q) hAM
      _ = ⊥ := by
        simp [q]
  exact hAne (le_antisymm (hMmax hAnormAb hMA) hMA)

/-- Every finite `p`-group has a self-centralizing normal abelian subgroup. -/
theorem exists_selfCentralizing_isNormalAbelian (hG : IsPGroup p G) :
    ∃ M : Subgroup G, IsNormalAbelian M ∧ Subgroup.centralizer (M : Set G) = M := by
  obtain ⟨M, hM, hMmax⟩ := exists_maximal_isNormalAbelian (G := G)
  exact ⟨M, hM, centralizer_eq_of_maximal_isNormalAbelian hG hM hMmax⟩

end Submission.OddOrder.MathlibSupport
