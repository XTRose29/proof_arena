import Submission.OddOrder.BG.Section03.OddPrimeSemidirectTheorem
import Submission.OddOrder.MathlibSupport.Centralizer
import Submission.OddOrder.MathlibSupport.ElementaryAbelian
import Submission.OddOrder.MathlibSupport.ElementaryAbelianRepresentation
import Submission.OddOrder.MathlibSupport.RepresentationSubgroupRestriction
import Submission.OddOrder.MathlibSupport.SubgroupCardinality

/-!
# Prime complements acting fixed-point-freely on elementary abelian groups

This is the mathlib-facing form of Bender--Glauberman Theorem 3.4's
elementary-abelian-action corollary.
-/

namespace Submission.OddOrder.BG.Section03

open Submission.OddOrder.MathlibSupport
open scoped IsMulCommutative

noncomputable section

universe u

/-- `BGsection3.v: odd_prime_sdprod_abelem_cent1`.

If an odd solvable semidirect product `J = K ⋊ R`, with `R` of prime
order, acts coprimely and fixed-point-freely on an elementary abelian group
`V`, then the mixed commutator `[R,K]` centralizes `V`.
-/
theorem odd_prime_sdprod_abelem_cent1
    {A : Type u} [Group A] [Finite A]
    {q : ℕ} [Fact q.Prime]
    (J K R V : Subgroup A)
    [IsSolvable J] [(K.subgroupOf J).Normal]
    (hKJ : K ≤ J) (hRJ : R ≤ J)
    (hKR : (K.subgroupOf J).IsComplement' (R.subgroupOf J))
    (hcop : Nat.Coprime (Nat.card K) (Nat.card R))
    (hodd : Odd (Nat.card J))
    (hRprime : (Nat.card R).Prime)
    (hVelem : IsElementaryAbelianGroup q V)
    (hJV : J ≤ Subgroup.normalizer (V : Set A))
    (hJcard : (Nat.card J : ZMod q) ≠ 0)
    (hCVR : centralizerWithin V R = ⊥) :
    ⁅R, K⁆ ≤ centralizerWithin K V := by
  classical
  letI : Fintype J := Fintype.ofFinite J
  letI : IsMulCommutative V := hVelem.commutative
  letI : Module (ZMod q) (Additive V) :=
    elementaryAbelianZModModule V q hVelem.pow_eq_one
  let endMonoid : Monoid (Module.End (ZMod q) (Additive V)) :=
    Module.End.instMonoid
  letI : Monoid (Module.End (ZMod q) (Additive V)) := endMonoid
  letI : MulOne (Module.End (ZMod q) (Additive V)) :=
    endMonoid.toMulOne
  letI : MulOneClass (Module.End (ZMod q) (Additive V)) :=
    endMonoid.toMulOneClass
  let rhoN : Representation (ZMod q)
      (Subgroup.normalizer (V : Set A)) (Additive V) :=
    normalizerConjugationRepresentation V q
  let inclusion : J →* Subgroup.normalizer (V : Set A) :=
    Subgroup.inclusion hJV
  let rho : Representation (ZMod q) J (Additive V) :=
    rhoN.comp inclusion
  have hcopJ : Nat.Coprime
      (Nat.card (K.subgroupOf J)) (Nat.card (R.subgroupOf J)) := by
    rw [natCard_subgroupOf_eq hKJ, natCard_subgroupOf_eq hRJ]
    exact hcop
  have hRprimeJ : (Nat.card (R.subgroupOf J)).Prime := by
    rw [natCard_subgroupOf_eq hRJ]
    exact hRprime
  have hfix :=
      (Submodule.eq_bot_iff (Representation.invariants
        (rho.comp (R.subgroupOf J).subtype :
          Representation (ZMod q) (R.subgroupOf J) (Additive V)))).mpr (by
    intro x hx
    apply Additive.toMul.injective
    change x.toMul = 1
    have hxCent : (x.toMul : A) ∈ centralizerWithin V R := by
      refine ⟨x.toMul.property, ?_⟩
      intro r hr
      let rJ : J := ⟨r, hRJ hr⟩
      let rRJ : R.subgroupOf J := ⟨rJ, hr⟩
      have hxFix :=
        (Representation.mem_invariants _ x).mp hx rRJ
      have hxConj := congrArg
        (fun y : Additive V ↦ (y.toMul : A)) hxFix
      change r * (x.toMul : A) * r⁻¹ = (x.toMul : A) at hxConj
      calc
        r * (x.toMul : A) =
            (r * (x.toMul : A) * r⁻¹) * r := by group
        _ = (x.toMul : A) * r := by rw [hxConj]
    have hxBot : (x.toMul : A) ∈ (⊥ : Subgroup A) := by
      rw [← hCVR]
      exact hxCent
    exact Subtype.ext (Subgroup.mem_bot.mp hxBot))
  have hlocal :
      ⁅R.subgroupOf J, K.subgroupOf J⁆ ≤ rho.ker :=
    odd_prime_sdprod_rfix0 rho (K.subgroupOf J) (R.subgroupOf J)
      hKR hcopJ hodd hRprimeJ hJcard hfix
  intro x hx
  have hxMap :
      x ∈ ⁅R.subgroupOf J, K.subgroupOf J⁆.map J.subtype := by
    rw [map_subgroupOf_commutator hKJ hRJ]
    exact hx
  rcases hxMap with ⟨j, hj, rfl⟩
  refine ⟨(Subgroup.commutator_le_right
    (R.subgroupOf J) (K.subgroupOf J)) hj, ?_⟩
  intro v hv
  have hjrho := MonoidHom.mem_ker.mp (hlocal hj)
  have hfixed := LinearMap.congr_fun hjrho
    (Additive.ofMul (⟨v, hv⟩ : V))
  change
    Additive.ofMul
        ((Subgroup.inclusion hJV j) • (⟨v, hv⟩ : V)) =
      Additive.ofMul (⟨v, hv⟩ : V) at hfixed
  have hfixedV := congrArg Additive.toMul hfixed
  have hconj := congrArg Subtype.val hfixedV
  change (j : A) * v * (j : A)⁻¹ = v at hconj
  symm
  calc
    (j : A) * v =
        ((j : A) * v * (j : A)⁻¹) * (j : A) := by group
    _ = v * (j : A) := by rw [hconj]

end

end Submission.OddOrder.BG.Section03
