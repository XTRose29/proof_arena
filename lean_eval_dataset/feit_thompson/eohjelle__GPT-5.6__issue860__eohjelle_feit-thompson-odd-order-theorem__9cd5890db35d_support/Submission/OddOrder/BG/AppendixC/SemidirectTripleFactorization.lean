import Mathlib.Tactic.Group
import Submission.OddOrder.BG.AppendixC.FiniteFieldUnitDecomposition

/-!
# The opening factorization lemmas for Appendix C.3

This file ports Steps 1 and 2 of Bender--Glauberman Lemma C.3,
`BGappendixC.v`, lines 465--504.  The finite-field unit decomposition from
Remark VIII first refines the internal semidirect-product factorization
`H = P U` to `H = U P₀ U`.  The second theorem records the rigidity of a
word `s₁ u s₂` that falls back into `U`.
-/

namespace Submission.OddOrder.BG.AppendixC

noncomputable section

universe u v

variable {G : Type u} [Group G]

namespace FiniteFieldImage

variable {H P P0 U : Subgroup G} (h : FiniteFieldImage P P0 U)

private theorem sigma_ne_zero_iff (x : P) :
    h.sigma (Additive.ofMul x) ≠ 0 ↔ x ≠ 1 := by
  constructor
  · intro hx hx1
    apply hx
    simp [hx1]
  · intro hx hsigma
    apply hx
    have heq :
        h.sigma (Additive.ofMul x) =
          h.sigma (Additive.ofMul (1 : P)) := by
      simpa using hsigma
    exact congrArg Additive.toMul (h.sigma.injective heq)

/-- Bender--Glauberman Lemma C.3, Step 1 (`BGappendixC.v: splitH`).

Every element of the internal semidirect product `H = P U` is a product
of an element of `U`, an element of the distinguished prime-line subgroup
`P₀`, and another element of `U`. -/
theorem splitH
    {p q : ℕ} [Fact p.Prime] [Algebra (ZMod p) h.F]
    (hPH : P ≤ H) (hUH : U ≤ H)
    (hsemi : (P.subgroupOf H).IsComplement' (U.subgroupOf H))
    (hUP : U ≤ Subgroup.normalizer (P : Set G))
    (hcardF : Nat.card h.F = p ^ q)
    (hcardU : Nat.card U = nU p q)
    (hcop : (nU p q).Coprime (p - 1))
    {x : G} (hxH : x ∈ H) :
    ∃ u : G, u ∈ U ∧
      ∃ v : G, v ∈ U ∧
        ∃ s₁ : G, s₁ ∈ P0 ∧ x = u * s₁ * v := by
  let xH : H := ⟨x, hxH⟩
  obtain ⟨⟨zH, vH⟩, hzv⟩ := hsemi.2 xH
  let z : P := ⟨((zH : H) : G), zH.property⟩
  let v : U := ⟨((vH : H) : G), vH.property⟩
  have hx_zv : x = (z : G) * (v : G) := by
    exact (congrArg (fun a : H ↦ (a : G)) hzv).symm
  by_cases hz1 : z = 1
  · refine ⟨1, U.one_mem, v, v.property, 1, P0.one_mem, ?_⟩
    simpa [hz1] using hx_zv
  · have hz0 : h.sigma (Additive.ofMul z) ≠ 0 :=
      (h.sigma_ne_zero_iff z).2 hz1
    let wz : h.Fˣ := Units.mk0 (h.sigma (Additive.ofMul z)) hz0
    have hunits := h.defFU hcardF hcardU hcop
    obtain ⟨⟨a, b⟩, hab⟩ := hunits.2 wz
    rcases a.property with ⟨u, hu⟩
    let s₁ : P :=
      Additive.toMul (h.sigma.symm (((b : primeFieldUnitRange p h.F) : h.Fˣ) : h.F))
    have hsigma : h.sigma (Additive.ofMul s₁) =
        ((b : primeFieldUnitRange p h.F) : h.Fˣ) := by
      simp [s₁]
    have hs₁P0 : (s₁ : G) ∈ P0 := by
      apply (h.mem_p0_iff_sigma_mem_primeAdditiveLine s₁).2
      rw [hsigma]
      exact h.val_mem_primeAdditiveLine_of_mem_primeFieldUnitRange b.property
    have hua : h.psiValue u = ((a : h.psi.range) : h.Fˣ) := by
      simpa [psiValue] using congrArg Units.val hu
    have habval : (((a : h.psi.range) : h.Fˣ) : h.F) *
        (((b : primeFieldUnitRange p h.F) : h.Fˣ) : h.F) =
        h.sigma (Additive.ofMul z) := by
      simpa [wz] using congrArg Units.val hab
    have hfield : (((b : primeFieldUnitRange p h.F) : h.Fˣ) : h.F) *
        h.psiValue u =
        h.sigma (Additive.ofMul z) := by
      rw [hua, mul_comm]
      exact habval
    have hzconj : z = rightConjugate P U hUP s₁ u := by
      apply congrArg Additive.toMul
      apply h.sigma.injective
      calc
        h.sigma (Additive.ofMul z) =
            (((b : primeFieldUnitRange p h.F) : h.Fˣ) : h.F) *
              h.psiValue u := hfield.symm
        _ = h.sigma (Additive.ofMul s₁) * h.psiValue u := by rw [hsigma]
        _ = h.sigma (Additive.ofMul
              (rightConjugate P U hUP s₁ u)) :=
          (h.sigma_rightConjugate hUP s₁ u).symm
    refine ⟨(u : G)⁻¹, U.inv_mem u.property,
      (u : G) * (v : G), U.mul_mem u.property v.property,
      s₁, hs₁P0, ?_⟩
    calc
      x = (z : G) * (v : G) := hx_zv
      _ = ((rightConjugate P U hUP s₁ u : P) : G) * (v : G) := by
        rw [hzconj]
      _ = (u : G)⁻¹ * (s₁ : G) * ((u : G) * (v : G)) := by
        rw [coe_rightConjugate]
        group

/-- Bender--Glauberman Lemma C.3, Step 2
(`BGappendixC.v: not_splitU`). -/
theorem not_splitU
    {p q : ℕ} [Fact p.Prime] [Algebra (ZMod p) h.F]
    (hPH : P ≤ H) (hUH : U ≤ H)
    (hsemi : (P.subgroupOf H).IsComplement' (U.subgroupOf H))
    (hUP : U ≤ Subgroup.normalizer (P : Set G))
    (hcardF : Nat.card h.F = p ^ q)
    (hcardU : Nat.card U = nU p q)
    (hcop : (nU p q).Coprime (p - 1))
    {s₁ s₂ u : G}
    (hs₁P0 : s₁ ∈ P0) (hs₂P0 : s₂ ∈ P0) (huU : u ∈ U)
    (hsusU : s₁ * u * s₂ ∈ U) :
    (s₁ = 1 ∧ s₂ = 1) ∨ (u = 1 ∧ s₁ * s₂ = 1) := by
  let s₁P : P := ⟨s₁, h.p0_le hs₁P0⟩
  let s₂P : P := ⟨s₂, h.p0_le hs₂P0⟩
  let uU : U := ⟨u, huU⟩
  let c : P := rightConjugate P U hUP s₁P uU

  have hc_ambient : (c : G) = u⁻¹ * s₁ * u := by
    simpa only [c, s₁P, uU] using
      coe_rightConjugate P U hUP s₁P uU

  have trivial_of_mem_both :
      ∀ {g : G}, g ∈ P → g ∈ U → g = 1 := by
    intro g hgP hgU
    let gH : H := ⟨g, hPH hgP⟩
    have hgInf : gH ∈
        (P.subgroupOf H) ⊓ (U.subgroupOf H) := ⟨hgP, hgU⟩
    have hgBot : gH ∈ (⊥ : Subgroup H) := by
      rw [← disjoint_iff.mp hsemi.disjoint]
      exact hgInf
    exact congrArg (fun a : H ↦ (a : G)) (Subgroup.mem_bot.mp hgBot)

  have hcs₂U : (c : G) * (s₂P : G) ∈ U := by
    have hleft : u⁻¹ * (s₁ * u * s₂) ∈ U :=
      U.mul_mem (U.inv_mem huU) hsusU
    have heq : (c : G) * (s₂P : G) =
        u⁻¹ * (s₁ * u * s₂) := by
      rw [hc_ambient]
      change u⁻¹ * s₁ * u * s₂ = u⁻¹ * (s₁ * u * s₂)
      group
    rw [heq]
    exact hleft
  have hcs₂P : (c : G) * (s₂P : G) ∈ P :=
    P.mul_mem c.property s₂P.property
  have hcs₂_one_ambient : (c : G) * (s₂P : G) = 1 :=
    trivial_of_mem_both hcs₂P hcs₂U
  have hcs₂_one : c * s₂P = 1 := by
    apply Subtype.ext
    exact hcs₂_one_ambient

  by_cases hs₁1 : s₁ = 1
  · left
    refine ⟨hs₁1, ?_⟩
    have hc1 : c = 1 := by
      apply Subtype.ext
      rw [hc_ambient]
      simp [hs₁1]
    have hs₂1 : s₂P = 1 := by simpa [hc1] using hcs₂_one
    exact congrArg Subtype.val hs₂1
  by_cases hu1 : u = 1
  · right
    refine ⟨hu1, ?_⟩
    have hambient : (c : G) * (s₂P : G) = (1 : G) := by
      exact congrArg Subtype.val hcs₂_one
    rw [hc_ambient] at hambient
    simpa [hu1] using hambient

  have hs₁P1 : s₁P ≠ 1 := by
    intro hs
    apply hs₁1
    exact congrArg Subtype.val hs
  have hs₁0 : h.sigma (Additive.ofMul s₁P) ≠ 0 :=
    (h.sigma_ne_zero_iff s₁P).2 hs₁P1
  have hsum :
      h.sigma (Additive.ofMul s₁P) * h.psiValue uU +
        h.sigma (Additive.ofMul s₂P) = 0 := by
    calc
      h.sigma (Additive.ofMul s₁P) * h.psiValue uU +
          h.sigma (Additive.ofMul s₂P) =
          h.sigma (Additive.ofMul c) +
            h.sigma (Additive.ofMul s₂P) := by
              rw [h.sigma_rightConjugate hUP s₁P uU]
      _ = h.sigma (Additive.ofMul (c * s₂P)) :=
        (h.sigma_mul c s₂P).symm
      _ = 0 := by rw [hcs₂_one, h.sigma_one]
  have hs₂0 : h.sigma (Additive.ofMul s₂P) ≠ 0 := by
    intro hs₂zero
    have hprod :
        h.sigma (Additive.ofMul s₁P) * h.psiValue uU = 0 := by
      simpa [hs₂zero] using hsum
    exact (mul_ne_zero hs₁0 (h.psiValue_ne_zero uU)) hprod
  have hpsi : h.psiValue uU =
      (-h.sigma (Additive.ofMul s₂P)) *
        (h.sigma (Additive.ofMul s₁P))⁻¹ := by
    calc
      h.psiValue uU =
          (h.sigma (Additive.ofMul s₁P))⁻¹ *
            (h.sigma (Additive.ofMul s₁P) * h.psiValue uU) := by
              rw [← mul_assoc, inv_mul_cancel₀ hs₁0, one_mul]
      _ = (h.sigma (Additive.ofMul s₁P))⁻¹ *
          (-h.sigma (Additive.ofMul s₂P)) := by
            rw [eq_neg_of_add_eq_zero_left hsum]
      _ = (-h.sigma (Additive.ofMul s₂P)) *
          (h.sigma (Additive.ofMul s₁P))⁻¹ := mul_comm _ _

  have hs₁line : h.sigma (Additive.ofMul s₁P) ∈
      primeAdditiveLine h.F :=
    (h.mem_p0_iff_sigma_mem_primeAdditiveLine s₁P).1 hs₁P0
  have hs₂line : h.sigma (Additive.ofMul s₂P) ∈
      primeAdditiveLine h.F :=
    (h.mem_p0_iff_sigma_mem_primeAdditiveLine s₂P).1 hs₂P0
  let a₁ : h.Fˣ := Units.mk0 (h.sigma (Additive.ofMul s₁P)) hs₁0
  let a₂ : h.Fˣ := Units.mk0 (-h.sigma (Additive.ofMul s₂P))
    (neg_ne_zero.mpr hs₂0)
  have ha₁ : a₁ ∈ primeFieldUnitRange p h.F := by
    exact (h.mk0_mem_primeFieldUnitRange_iff
      (h.sigma (Additive.ofMul s₁P)) hs₁0).2 hs₁line
  have ha₂ : a₂ ∈ primeFieldUnitRange p h.F := by
    apply (h.mk0_mem_primeFieldUnitRange_iff
      (-h.sigma (Additive.ofMul s₂P)) (neg_ne_zero.mpr hs₂0)).2
    exact (primeAdditiveLine h.F).neg_mem hs₂line
  have hpsi_eq : h.psi uU = a₂ * a₁⁻¹ := by
    apply Units.ext
    simpa [a₁, a₂, psiValue] using hpsi
  have hpsi_prime : h.psi uU ∈ primeFieldUnitRange p h.F := by
    rw [hpsi_eq]
    exact (primeFieldUnitRange p h.F).mul_mem ha₂
      ((primeFieldUnitRange p h.F).inv_mem ha₁)
  have hunits := h.defFU hcardF hcardU hcop
  have hpsiBot : h.psi uU ∈ (⊥ : Subgroup h.Fˣ) := by
    rw [← disjoint_iff.mp hunits.disjoint]
    exact ⟨⟨uU, rfl⟩, hpsi_prime⟩
  have hpsi1 : h.psi uU = 1 := Subgroup.mem_bot.mp hpsiBot
  have huU1 : uU = 1 := by
    apply h.psi_injective
    simpa using hpsi1
  exact (hu1 (congrArg Subtype.val huU1)).elim

end FiniteFieldImage

end

end Submission.OddOrder.BG.AppendixC
