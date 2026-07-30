import Submission.OddOrder.MathlibSupport.ChiefFactor

/-!
Transport of chief factors through a quotient whose kernel meets the upper
group of the factor inside its lower group.
-/

namespace Submission.OddOrder.MathlibSupport

universe u

variable {G : Type u} [Group G]

private def factorQuotientHom
    {K V : Subgroup G} [K.Normal] [V.Normal] :
    G ⧸ V →* (G ⧸ K) ⧸ V.map (QuotientGroup.mk' K) :=
  QuotientGroup.lift V
    ((QuotientGroup.mk' (V.map (QuotientGroup.mk' K))).comp
      (QuotientGroup.mk' K)) <| by
    intro x hx
    change QuotientGroup.mk' (V.map (QuotientGroup.mk' K))
      (QuotientGroup.mk' K x) = 1
    apply QuotientGroup.eq_one_iff (QuotientGroup.mk' K x) |>.mpr
    exact Subgroup.mem_map_of_mem (QuotientGroup.mk' K) hx

@[simp]
private theorem factorQuotientHom_mk
    {K V : Subgroup G} [K.Normal] [V.Normal] (x : G) :
    factorQuotientHom (K := K) (V := V)
        (QuotientGroup.mk' V x) =
      QuotientGroup.mk' (V.map (QuotientGroup.mk' K))
        (QuotientGroup.mk' K x) :=
  QuotientGroup.lift_mk' V _ x

private theorem factorQuotientHom_surjective
    {K V : Subgroup G} [K.Normal] [V.Normal] :
    Function.Surjective (factorQuotientHom (K := K) (V := V)) := by
  intro y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective
    (V.map (QuotientGroup.mk' K)) y
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective K x
  exact ⟨QuotientGroup.mk' V g, factorQuotientHom_mk g⟩

private theorem factorQuotientHom_injective_on_factor
    {K V U : Subgroup G} [K.Normal] [V.Normal]
    (hVU : V ≤ U) (hKU : K ⊓ U ≤ V) :
    Function.Injective
      ((factorQuotientHom (K := K) (V := V)).subgroupMap
        (U.map (QuotientGroup.mk' V))) := by
  intro x y hxy
  have hxy' :
      factorQuotientHom (K := K) (V := V) (x : G ⧸ V) =
        factorQuotientHom (K := K) (V := V) (y : G ⧸ V) :=
    congrArg Subtype.val hxy
  have hzmem : (x : G ⧸ V) * (y : G ⧸ V)⁻¹ ∈
      U.map (QuotientGroup.mk' V) :=
    (U.map (QuotientGroup.mk' V)).mul_mem x.2
      ((U.map (QuotientGroup.mk' V)).inv_mem y.2)
  have hzker : factorQuotientHom (K := K) (V := V)
      ((x : G ⧸ V) * (y : G ⧸ V)⁻¹) = 1 := by
    rw [map_mul, map_inv, hxy']
    simp
  rcases hzmem with ⟨g, hgU, hg⟩
  have hgker : factorQuotientHom (K := K) (V := V)
      (QuotientGroup.mk' V g) = 1 := by
    rw [hg]
    exact hzker
  rw [factorQuotientHom_mk] at hgker
  have hgimage : QuotientGroup.mk' K g ∈
      V.map (QuotientGroup.mk' K) :=
    QuotientGroup.eq_one_iff (QuotientGroup.mk' K g) |>.mp hgker
  rcases hgimage with ⟨v, hvV, hvg⟩
  have hdK : v⁻¹ * g ∈ K := by
    apply QuotientGroup.eq_one_iff (v⁻¹ * g) |>.mp
    change QuotientGroup.mk' K (v⁻¹ * g) = 1
    calc
      QuotientGroup.mk' K (v⁻¹ * g) =
          (QuotientGroup.mk' K v)⁻¹ * QuotientGroup.mk' K g := by
        simp
      _ = 1 := by rw [hvg]; simp
  have hdU : v⁻¹ * g ∈ U :=
    U.mul_mem (U.inv_mem (hVU hvV)) hgU
  have hdV : v⁻¹ * g ∈ V := hKU ⟨hdK, hdU⟩
  have hgV : g ∈ V := by
    have hdecomp : g = v * (v⁻¹ * g) := by group
    rw [hdecomp]
    exact V.mul_mem hvV hdV
  have hzone : (x : G ⧸ V) * (y : G ⧸ V)⁻¹ = 1 := by
    rw [← hg]
    exact QuotientGroup.eq_one_iff g |>.mpr hgV
  apply Subtype.ext
  exact mul_inv_eq_one.mp hzone

private theorem map_factorQuotientHom
    {K V U : Subgroup G} [K.Normal] [V.Normal] :
    (U.map (QuotientGroup.mk' V)).map
        (factorQuotientHom (K := K) (V := V)) =
      (U.map (QuotientGroup.mk' K)).map
        (QuotientGroup.mk' (V.map (QuotientGroup.mk' K))) := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

private theorem IsMinimalNormal.map_of_surjective_of_ne_bot
    {A B : Type*} [Group A] [Group B]
    {M : Subgroup A} (hM : IsMinimalNormal M)
    (f : A →* B) (hf : Function.Surjective f)
    (hne : M.map f ≠ ⊥) :
    IsMinimalNormal (M.map f) := by
  refine ⟨hne, hM.normal.map f hf, ?_⟩
  intro L hLnormal hLM hLne
  let N : Subgroup A := L.comap f ⊓ M
  have hNnormal : N.Normal := by
    dsimp only [N]
    letI : L.Normal := hLnormal
    letI : M.Normal := hM.normal
    infer_instance
  have hLmapN : L ≤ N.map f := by
    intro y hy
    rcases hLM hy with ⟨x, hxM, hxy⟩
    refine ⟨x, ⟨?_, hxM⟩, hxy⟩
    change f x ∈ L
    rwa [hxy]
  have hNne : N ≠ ⊥ := by
    intro hN
    apply hLne
    apply le_antisymm _ bot_le
    intro y hy
    have hymap := hLmapN hy
    rw [hN] at hymap
    simpa using hymap
  have hMN : M ≤ N := hM.2.2 N hNnormal inf_le_right hNne
  intro y hy
  rcases hy with ⟨x, hxM, hxy⟩
  have hxN := hMN hxM
  have hfxL : f x ∈ L := hxN.1
  rwa [hxy] at hfxL

private theorem map_ne_bot_of_injective_on_subgroup
    {A B : Type*} [Group A] [Group B]
    {M : Subgroup A} {f : A →* B}
    (hM : M ≠ ⊥)
    (hinj : Function.Injective (f.subgroupMap M)) :
    M.map f ≠ ⊥ := by
  intro hmap
  apply hM
  apply le_antisymm _ bot_le
  intro x hx
  apply Subgroup.mem_bot.mpr
  have hfx : f.subgroupMap M ⟨x, hx⟩ =
      f.subgroupMap M (1 : M) := by
    apply Subtype.ext
    have hmem : f x ∈ (⊥ : Subgroup B) := by
      rw [← hmap]
      exact Subgroup.mem_map_of_mem f hx
    simpa using Subgroup.mem_bot.mp hmem
  exact congrArg Subtype.val (hinj hfx)

/-- The factor `U / V` is isomorphic to the factor formed by the images of
`U` and `V` modulo `K`, provided `K ∩ U ≤ V`. -/
noncomputable def chiefFactorQuotientMulEquiv
    {K V U : Subgroup G} [K.Normal] [V.Normal]
    (hVU : V ≤ U) (hKU : K ⊓ U ≤ V) :
    U.map (QuotientGroup.mk' V) ≃*
      (U.map (QuotientGroup.mk' K)).map
        (QuotientGroup.mk' (V.map (QuotientGroup.mk' K))) :=
  (MulEquiv.ofBijective
      ((factorQuotientHom (K := K) (V := V)).subgroupMap
        (U.map (QuotientGroup.mk' V)))
      ⟨factorQuotientHom_injective_on_factor hVU hKU,
        MonoidHom.subgroupMap_surjective _ _⟩).trans
    (MulEquiv.subgroupCongr map_factorQuotientHom)

/-- Prime-power structure transports across `chiefFactorQuotientMulEquiv`. -/
theorem isPGroup_map_quotient_factor_iff
    {K V U : Subgroup G} [K.Normal] [V.Normal]
    {p : ℕ} (hVU : V ≤ U) (hKU : K ⊓ U ≤ V) :
    IsPGroup p
        ((U.map (QuotientGroup.mk' K)).map
          (QuotientGroup.mk' (V.map (QuotientGroup.mk' K)))) ↔
      IsPGroup p (U.map (QuotientGroup.mk' V)) := by
  constructor
  · intro h
    exact h.of_equiv (chiefFactorQuotientMulEquiv hVU hKU).symm
  · intro h
    exact h.of_equiv (chiefFactorQuotientMulEquiv hVU hKU)

/-- A chief factor remains a chief factor after quotienting by a normal
subgroup whose intersection with the upper group lies in the lower group. -/
theorem IsChiefFactor.map_quotient_of_inf_le
    [Finite G]
    {K V U : Subgroup G} [K.Normal] [V.Normal]
    (hchief : IsChiefFactor V U)
    (hKU : K ⊓ U ≤ V) :
    IsChiefFactor
      (V.map (QuotientGroup.mk' K))
      (U.map (QuotientGroup.mk' K)) := by
  refine ⟨Subgroup.map_mono hchief.le,
    hchief.upper_normal.map _ (QuotientGroup.mk'_surjective K), ?_⟩
  let f := factorQuotientHom (K := K) (V := V)
  have hinj : Function.Injective
      (f.subgroupMap (U.map (QuotientGroup.mk' V))) :=
    factorQuotientHom_injective_on_factor hchief.le hKU
  have hne : (U.map (QuotientGroup.mk' V)).map f ≠ ⊥ :=
    map_ne_bot_of_injective_on_subgroup
      hchief.quotient_minimal_normal.ne_bot hinj
  have hminimal :=
    IsMinimalNormal.map_of_surjective_of_ne_bot
      hchief.quotient_minimal_normal f
      factorQuotientHom_surjective hne
  rw [map_factorQuotientHom] at hminimal
  exact hminimal

end Submission.OddOrder.MathlibSupport
