import Submission.OddOrder.BG.AppendixAB.QuadraticPairNormalQuotient

/-!
The invariant ambient quotient used in the odd quadratic-pair induction.
-/

namespace Submission.OddOrder.BG.AppendixAB

open Submission.OddOrder.MathlibSupport

variable {G K : Type*} [Group G] [Group K]

/-- Quadraticity can be reflected through an injective homomorphism. -/
theorem IsQuadraticPElement.of_map_of_injective
    {p : ℕ} {E : Subgroup G} {x : G} (f : G →* K)
    (hf : Function.Injective f)
    (hx : IsQuadraticPElement p (E.map f) (f x)) :
    IsQuadraticPElement p E x := by
  refine ⟨IsPElement.of_map_of_injective f hf hx.1, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  have hzmap : f z ∈ ⁅E.map f, Subgroup.zpowers (f x)⁆ := by
    rw [← MonoidHom.map_zpowers, ← Subgroup.map_commutator]
    exact ⟨z, hz, rfl⟩
  have hcomm := Subgroup.mem_centralizer_iff.mp hx.2 (f z) hzmap
  exact hf (by simpa using hcomm)

/-- The smallest ambient subgroup containing the acted-on subgroup and the
two acting elements. -/
def pairExtension (E : Subgroup G) (x y : G) : Subgroup G :=
  E ⊔ pairGenerated x y

theorem le_pairExtension (E : Subgroup G) (x y : G) :
    E ≤ pairExtension E x y :=
  le_sup_left

theorem pairGenerated_le_pairExtension (E : Subgroup G) (x y : G) :
    pairGenerated x y ≤ pairExtension E x y :=
  le_sup_right

def pairExtensionLeft (E : Subgroup G) (x y : G) : pairExtension E x y :=
  ⟨x, pairGenerated_le_pairExtension E x y (mem_pairGenerated_left x y)⟩

def pairExtensionRight (E : Subgroup G) (x y : G) : pairExtension E x y :=
  ⟨y, pairGenerated_le_pairExtension E x y (mem_pairGenerated_right x y)⟩

@[simp]
theorem pairExtensionLeft_coe (E : Subgroup G) (x y : G) :
    (pairExtensionLeft E x y : G) = x :=
  rfl

@[simp]
theorem pairExtensionRight_coe (E : Subgroup G) (x y : G) :
    (pairExtensionRight E x y : G) = y :=
  rfl

/-- A subgroup normalized by `E`, `x`, and `y` is normal inside their pair
extension. -/
theorem pairExtension_subgroupOf_normal
    {D E : Subgroup G} {x y : G}
    (hED : E ≤ Subgroup.normalizer (D : Set G))
    (hxND : x ∈ Subgroup.normalizer (D : Set G))
    (hyND : y ∈ Subgroup.normalizer (D : Set G)) :
    (D.subgroupOf (pairExtension E x y)).Normal := by
  apply Subgroup.normal_subgroupOf_of_le_normalizer
  exact sup_le hED (pairGenerated_le_normalizer hxND hyND)

section Finite

variable [Finite G]

/-- Passing to the quotient of `E ⊔ ⟨x,y⟩` by a nontrivial invariant
subgroup transports the full quadratic-pair hypothesis and strictly lowers
the cardinality of the acted-on subgroup. -/
theorem quadraticPair_invariantQuotient
    {p : ℕ} {D E : Subgroup G} {x y : G}
    (hDE : D ≤ E) (hD : D ≠ ⊥)
    (hED : E ≤ Subgroup.normalizer (D : Set G))
    (hxND : x ∈ Subgroup.normalizer (D : Set G))
    (hyND : y ∈ Subgroup.normalizer (D : Set G))
    (hxNE : x ∈ Subgroup.normalizer (E : Set G))
    (hyNE : y ∈ Subgroup.normalizer (E : Set G))
    (hodd : Odd (Nat.card (pairGenerated x y)))
    (hE : IsPGroup p E)
    (hx : IsQuadraticPElement p E x)
    (hy : IsQuadraticPElement p E y) :
    let J : Subgroup G := pairExtension E x y
    let DJ : Subgroup J := D.subgroupOf J
    letI : DJ.Normal := pairExtension_subgroupOf_normal hED hxND hyND
    let EJ : Subgroup J := E.subgroupOf J
    let q : J →* J ⧸ DJ := QuotientGroup.mk' DJ
    let Eq : Subgroup (J ⧸ DJ) := EJ.map q
    q (pairExtensionLeft E x y) ∈
        Subgroup.normalizer (Eq : Set (J ⧸ DJ)) ∧
      q (pairExtensionRight E x y) ∈
        Subgroup.normalizer (Eq : Set (J ⧸ DJ)) ∧
      Odd (Nat.card (pairGenerated
        (q (pairExtensionLeft E x y))
        (q (pairExtensionRight E x y)))) ∧
      IsPGroup p Eq ∧
      IsQuadraticPElement p Eq (q (pairExtensionLeft E x y)) ∧
      IsQuadraticPElement p Eq (q (pairExtensionRight E x y)) ∧
      Nat.card Eq < Nat.card E := by
  dsimp only
  let J : Subgroup G := pairExtension E x y
  let DJ : Subgroup J := D.subgroupOf J
  let EJ : Subgroup J := E.subgroupOf J
  let xJ : J := pairExtensionLeft E x y
  let yJ : J := pairExtensionRight E x y
  letI : DJ.Normal := pairExtension_subgroupOf_normal hED hxND hyND
  have hEJ : E ≤ J := le_pairExtension E x y
  have hDJ : D ≤ J := hDE.trans hEJ
  have hDJEJ : DJ ≤ EJ := Subgroup.subgroupOf_mono J hDE
  have hDJne : DJ ≠ ⊥ := by
    rw [Subgroup.ne_bot_iff_exists_ne_one]
    obtain ⟨d, hd⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hD
    refine ⟨⟨⟨(d : G), hDJ d.property⟩, d.property⟩, ?_⟩
    intro hdOne
    apply hd
    apply Subtype.ext
    exact congrArg (fun z : DJ ↦ ((z : J) : G)) hdOne
  have hxNEJ : xJ ∈ Subgroup.normalizer (EJ : Set J) := by
    rw [Subgroup.mem_normalizer_iff]
    intro e
    change (e : G) ∈ E ↔ x * (e : G) * x⁻¹ ∈ E
    exact hxNE e
  have hyNEJ : yJ ∈ Subgroup.normalizer (EJ : Set J) := by
    rw [Subgroup.mem_normalizer_iff]
    intro e
    change (e : G) ∈ E ↔ y * (e : G) * y⁻¹ ∈ E
    exact hyNE e
  have hEJmap : EJ.map J.subtype = E :=
    Subgroup.map_subgroupOf_eq_of_le hEJ
  have hEJp : IsPGroup p EJ :=
    hE.of_equiv (Subgroup.subgroupOfEquivOfLe hEJ).symm
  have hxJ : IsQuadraticPElement p EJ xJ := by
    apply IsQuadraticPElement.of_map_of_injective J.subtype J.subtype_injective
    simpa [hEJmap, xJ] using hx
  have hyJ : IsQuadraticPElement p EJ yJ := by
    apply IsQuadraticPElement.of_map_of_injective J.subtype J.subtype_injective
    simpa [hEJmap, yJ] using hy
  have hpairMap :
      (pairGenerated xJ yJ).map J.subtype = pairGenerated x y := by
    rw [← pairGenerated_map_eq]
    rfl
  have hoddJ : Odd (Nat.card (pairGenerated xJ yJ)) := by
    have hcardMap := Subgroup.card_map_of_injective
      (K := pairGenerated xJ yJ) J.subtype_injective
    rw [hpairMap] at hcardMap
    rwa [hcardMap] at hodd
  obtain ⟨hxNq, hyNq, hoddq, hEq, hxq, hyq, hcardq⟩ :=
    quadraticPair_normalQuotient hDJEJ hDJne
      hxNEJ hyNEJ hoddJ hEJp hxJ hyJ
  have hcardEJ : Nat.card EJ = Nat.card E :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEJ).toEquiv
  exact ⟨hxNq, hyNq, hoddq, hEq, hxq, hyq, hcardEJ ▸ hcardq⟩

end Finite

end Submission.OddOrder.BG.AppendixAB
