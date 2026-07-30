import Submission.OddOrder.BG.Section04.ExponentOmegaOneRankTwo
import Submission.OddOrder.BG.Section05.Definitions

/-!
Injective-image and isomorphism invariance of narrowness.

This is the mathlib-facing port of `injm_narrow`, `isog_narrow`, and
`narrowJ` from the opening of `BGsection5.v`.
-/

namespace Submission.OddOrder.BG.Section05

open Submission.OddOrder.MathlibSupport

universe u v

variable {G : Type u} {H : Type v} [Group G] [Group H]
variable {p : ℕ}

private theorem elementary_map_of_injective
    {A : Subgroup G} (hA : IsElementaryAbelianGroup p A)
    (f : G →* H) :
    IsElementaryAbelianGroup p (A.map f) := by
  letI : IsMulCommutative A := hA.commutative
  refine
    { isPGroup := hA.isPGroup.map f
      commutative := Subgroup.map_isMulCommutative A f
      pow_eq_one := ?_ }
  rintro ⟨x, hx⟩
  rcases hx with ⟨a, ha, hax⟩
  apply Subtype.ext
  change x ^ p = 1
  rw [← hax]
  have haPow := congrArg f
    (congrArg Subtype.val (hA.pow_eq_one ⟨a, ha⟩))
  simpa using haPow

private theorem elementary_comap_of_injective
    {A : Subgroup H} (hA : IsElementaryAbelianGroup p A)
    (f : G →* H) (hf : Function.Injective f) :
    IsElementaryAbelianGroup p (A.comap f) := by
  letI : IsMulCommutative A := hA.commutative
  refine
    { isPGroup := hA.isPGroup.comap_of_injective f hf
      commutative := A.comap_injective_isMulCommutative hf
      pow_eq_one := ?_ }
  intro x
  apply Subtype.ext
  apply hf
  have hx := congrArg Subtype.val
    (hA.pow_eq_one (⟨f x, x.property⟩ : A))
  simpa using hx

private theorem rank_comap_of_injective_of_le_range
    {n : ℕ} {A : Subgroup H} (hA : IsElementaryAbelianOfRank p n A)
    (f : G →* H) (hf : Function.Injective f) (hArange : A ≤ f.range) :
    IsElementaryAbelianOfRank p n (A.comap f) := by
  refine
    { toIsElementaryAbelianGroup :=
        elementary_comap_of_injective hA.toIsElementaryAbelianGroup f hf
      card_eq := ?_ }
  calc
    Nat.card (A.comap f) = Nat.card ((A.comap f).map f) :=
      (Subgroup.card_map_of_injective hf).symm
    _ = Nat.card A := by rw [Subgroup.map_comap_eq_self hArange]
    _ = p ^ n := hA.card_eq

private theorem pmax_map_of_injective
    {A E : Subgroup G} (hE : IsPMaxElem p A E)
    (f : G →* H) (hf : Function.Injective f) :
    IsPMaxElem p (A.map f) (E.map f) := by
  refine ⟨⟨Subgroup.map_mono hE.le,
    elementary_map_of_injective hE.elementary f⟩, ?_⟩
  intro F hF hEF
  have hFrange : F ≤ f.range :=
    hF.1.trans (Subgroup.map_le_range (f := f) A)
  let F' : Subgroup G := F.comap f
  have hF'A : F' ≤ A := by
    rw [← Subgroup.comap_map_eq_self_of_injective hf A]
    exact Subgroup.comap_mono hF.1
  have hF'elem : IsElementaryAbelianGroup p F' :=
    elementary_comap_of_injective hF.2 f hf
  have hEF' : E ≤ F' :=
    Subgroup.map_le_iff_le_comap.mp hEF
  have hF'E : F' = E := hE.2 F' ⟨hF'A, hF'elem⟩ hEF'
  calc
    F = F'.map f := (Subgroup.map_comap_eq_self hFrange).symm
    _ = E.map f := congrArg (fun K : Subgroup G ↦ K.map f) hF'E

private theorem pmax_comap_of_injective_of_le_range
    (f : G →* H) {A : Subgroup G} {E : Subgroup H}
    (hE : IsPMaxElem p (A.map f) E)
    (hf : Function.Injective f) (hErange : E ≤ f.range) :
    IsPMaxElem p A (E.comap f) := by
  have hEA : E.comap f ≤ A := by
    rw [← Subgroup.comap_map_eq_self_of_injective hf A]
    exact Subgroup.comap_mono hE.le
  refine ⟨⟨hEA, elementary_comap_of_injective hE.elementary f hf⟩, ?_⟩
  intro K hK hEK
  have hmapK : IsPElementaryIn p (A.map f) (K.map f) :=
    ⟨Subgroup.map_mono hK.1, elementary_map_of_injective hK.2 f⟩
  have hEmapK : E ≤ K.map f := by
    rw [← Subgroup.map_comap_eq_self hErange]
    exact Subgroup.map_mono hEK
  have hmapKE : K.map f = E := hE.2 (K.map f) hmapK hEmapK
  calc
    K = (K.map f).comap f :=
      (Subgroup.comap_map_eq_self_of_injective hf K).symm
    _ = E.comap f := congrArg (fun L : Subgroup H ↦ L.comap f) hmapKE

/-- `BGsection5.v: injm_narrow`.

Narrowness is preserved and reflected by an injective homomorphism. -/
theorem isNarrow_map_iff_of_injective
    [Fact p.Prime] (f : G →* H) (hf : Function.Injective f)
    (A : Subgroup G) :
    IsNarrow p (A.map f) ↔ IsNarrow p A := by
  constructor
  · intro hN hRank3
    have hRank3map :
        ∃ E : Subgroup H,
          E ≤ A.map f ∧ IsElementaryAbelianOfRank p 3 E := by
      obtain ⟨E, hEA, hE⟩ := hRank3
      exact ⟨E.map f, Subgroup.map_mono hEA,
        Submission.OddOrder.BG.Section04.isElementaryAbelianOfRank_map_of_injective
          hE f hf⟩
    obtain ⟨E, hErank, hEmax⟩ := hN hRank3map
    have hErange : E ≤ f.range :=
      hEmax.le.trans (Subgroup.map_le_range (f := f) A)
    exact ⟨E.comap f,
      rank_comap_of_injective_of_le_range hErank f hf hErange,
      pmax_comap_of_injective_of_le_range f hEmax hf hErange⟩
  · intro hN hRank3
    obtain ⟨E, hEAmap, hErank⟩ := hRank3
    have hErange : E ≤ f.range :=
      hEAmap.trans (Subgroup.map_le_range (f := f) A)
    have hRank3comap :
        ∃ F : Subgroup G, F ≤ A ∧ IsElementaryAbelianOfRank p 3 F := by
      refine ⟨E.comap f, ?_,
        rank_comap_of_injective_of_le_range hErank f hf hErange⟩
      rw [← Subgroup.comap_map_eq_self_of_injective hf A]
      exact Subgroup.comap_mono hEAmap
    obtain ⟨F, hFrank, hFmax⟩ := hN hRank3comap
    exact ⟨F.map f,
      Submission.OddOrder.BG.Section04.isElementaryAbelianOfRank_map_of_injective
        hFrank f hf,
      pmax_map_of_injective hFmax f hf⟩

/-- `BGsection5.v: isog_narrow`. -/
theorem isNarrow_map_mulEquiv_iff [Fact p.Prime]
    (e : G ≃* H) (A : Subgroup G) :
    IsNarrow p (A.map e.toMonoidHom) ↔ IsNarrow p A :=
  isNarrow_map_iff_of_injective e.toMonoidHom e.injective A

/-- `BGsection5.v: narrowJ`, expressed using the conjugation equivalence. -/
theorem isNarrow_conj_iff [Fact p.Prime] (A : Subgroup G) (g : G) :
    IsNarrow p (A.map (MulAut.conj g).toMonoidHom) ↔ IsNarrow p A :=
  isNarrow_map_mulEquiv_iff (MulAut.conj g) A

end Submission.OddOrder.BG.Section05
