import Mathlib

namespace Submission

namespace LeanEval
namespace Combinatorics
namespace FraserKakeyaProblem

/-!
# Fraser: Fourier decay for finite-field Kakeya sets

For every dimension `d ≥ 2`, every finite-field Kakeya set
`K ⊆ F_q^d` supports a probability measure whose finite-field Fourier
transform is bounded by `q^{-1}` at every nonzero frequency, **and**
this exponent is sharp in every dimension (for sufficiently large
`q`). Jonathan M. Fraser, *Fourier analytic properties of Kakeya sets
in finite fields*, Bull. London Math. Soc. **58**(5) (2026); DOI
`10.1112/blms.70367`; arXiv:2505.09464.

A *finite-field Kakeya set* is a subset of `F_q^d` containing a line
in every direction. The theorem combines the upper Fourier-decay
bound with a matching sharpness construction valid in arbitrary
ambient dimension.
-/

open scoped BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The ambient finite vector space `F_q^d`. -/
abbrev Space (F : Type*) (d : ℕ) := Fin d → F

/-- Standard dot product on `F_q^d`. -/
def dot {d : ℕ} (x y : Space F d) : F :=
  ∑ i, x i * y i

/-- The affine line with base point `y` and direction `x`. -/
def affineLine {d : ℕ} (y x : Space F d) : Set (Space F d) :=
  {z | ∃ a : F, z = y + a • x}

/-- A **Kakeya set**: it contains a line in every direction. -/
def IsKakeya {d : ℕ} (K : Set (Space F d)) : Prop :=
  ∀ x : Space F d, ∃ y : Space F d, affineLine y x ⊆ K

/-- A real-valued probability measure on the finite vector space
whose support is contained in `K`. -/
def IsProbabilityMeasureOn {d : ℕ} (K : Set (Space F d))
    (μ : Space F d → ℝ) : Prop :=
  (∀ x, 0 ≤ μ x) ∧ (∑ x, μ x = 1) ∧ ∀ x, μ x ≠ 0 → x ∈ K

/-- The finite-field Fourier transform with respect to a nontrivial
additive character. -/
noncomputable def fourier {d : ℕ} (χ : AddChar F ℂ) (μ : Space F d → ℝ)
    (ξ : Space F d) : ℂ :=
  ∑ x, χ (-(dot ξ x)) * (μ x : ℂ)



end FraserKakeyaProblem
end Combinatorics
end LeanEval

open LeanEval.Combinatorics.FraserKakeyaProblem
open scoped BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
/-ResultDefinitionsBegin-/
/-ResultProofDefinitionsBegin-/

open scoped Classical

/-- elementary ``pairing'' estimate for the image of a finite map.  It is useful in
characteristic two as well as in odd characteristic. -/
private lemma image_involution_bound
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (f : α → β) (j : α → α)
    (hj : ∀ a, j (j a) = a) (hf : ∀ a, f (j a) = f a) :
    2 * (Finset.univ.image f).card ≤
      Fintype.card α + (Finset.univ.filter (fun a => j a = a)).card := by
  classical
  let A : Finset β := Finset.univ.image f
  let s : (↥A) → α := fun b =>
    Classical.choose (Finset.mem_image.mp b.property)
  have hs (b : ↥A) : f (s b) = (b : β) :=
    (Classical.choose_spec (Finset.mem_image.mp b.property)).2
  have sinj : Function.Injective s := by
    intro u v h
    apply Subtype.ext
    exact calc
      (u : β) = f (s u) := (hs u).symm
      _ = f (s v) := congrArg f h
      _ = (v : β) := hs v
  let G := {b : ↥A // j (s b) ≠ s b}
  let T : Finset α := Finset.univ.filter (fun a => j a = a)
  let X := ↥T
  -- A representative and, for a non-fixed fibre, its partner are disjoint.
  let e₁ : (↥A ⊕ G) → α := fun u =>
    Sum.elim s (fun b : G => j (s (b.1))) u
  have he₁ : Function.Injective e₁ := by
    intro u v h
    cases u with
    | inl u =>
      cases v with
      | inl v =>
        have h' : s u = s v := h
        have h'' : u = v := sinj h'
        simpa [h'']
      | inr v =>
        exfalso
        have huv : u = v.1 := by
          apply Subtype.ext
          calc
            (u : β) = f (s u) := (hs u).symm
            _ = f (j (s (v.1))) := congrArg f h
            _ = f (s (v.1)) := hf _
            _ = (v.1 : β) := hs _
        have hbad : s v.1 = j (s v.1) := by
          simpa [e₁, huv] using h
        exact v.2 hbad.symm
    | inr u =>
      cases v with
      | inl v =>
        exfalso
        have huv : u.1 = v := by
          apply Subtype.ext
          calc
            (u.1 : β) = f (s (u.1)) := (hs _).symm
            _ = f (j (s (u.1))) := (hf _).symm
            _ = f (s v) := congrArg f h
            _ = (v : β) := hs _
        have hbad : j (s u.1) = s u.1 := by
          simpa [e₁, huv] using h
        exact u.2 hbad
      | inr v =>
        have h' : s (u.1) = s (v.1) := by
          have hh := congrArg j h
          simpa [e₁, hj] using hh
        have huv : u.1 = v.1 := sinj h'
        cases u with
        | mk u hu =>
          cases v with
          | mk v hv =>
            dsimp at huv
            cases huv
            rfl
  have h₁ : Fintype.card (↥A ⊕ G) ≤ Fintype.card α :=
    Fintype.card_le_of_injective e₁ he₁
  -- Fixed representatives give all the possible exceptions to that pairing.
  let e₂ : (↥A) → (G ⊕ X) := fun b =>
    if h : j (s b) ≠ s b then
      Sum.inl ⟨b, h⟩
    else
      Sum.inr ⟨s b, by
        have h' : j (s b) = s b := not_ne_iff.mp h
        simp [T, h']⟩
  let r : (G ⊕ X) → β := fun w =>
    Sum.elim (fun g : G => (g.1 : β)) (fun a : X => f (a.1)) w
  have hr (b : ↥A) : r (e₂ b) = (b : β) := by
    classical
    by_cases h : j (s b) ≠ s b
    · simp [e₂, h, r]
    · dsimp [e₂, r]
      rw [dif_neg h]
      exact hs b
  have he₂ : Function.Injective e₂ := by
    intro u v h
    apply Subtype.ext
    exact calc
      (u : β) = r (e₂ u) := (hr u).symm
      _ = r (e₂ v) := congrArg r h
      _ = (v : β) := hr v
  have h₂ : Fintype.card (↥A) ≤ Fintype.card (G ⊕ X) :=
    Fintype.card_le_of_injective e₂ he₂
  change 2 * A.card ≤ Fintype.card α + (Finset.univ.filter (fun a => j a = a)).card
  change _ at h₁ h₂
  simp only [Fintype.card_sum, Fintype.card_coe] at h₁ h₂
  -- `card_subtype_...` reduces `X`
  have hx : Fintype.card X = (Finset.univ.filter (fun a => j a = a)).card := by
    classical
    change Fintype.card (↥T) = _
    simpa [T] using (Fintype.card_coe T)
  -- The subtype of the good representatives has the usual card; no need to compute it.
  rw [hx] at h₂
  omega



section Plane
open LeanEval.Combinatorics.FraserKakeyaProblem
variable (E : Type*) [Field E] [Fintype E] [DecidableEq E]

private def slopeMap (u : E × E) : Space E 2 :=
  ![u.2, u.1 * u.2 + u.1^2]

private def slopeSwap (u : E × E) : E × E :=
  (- u.2 - u.1, u.2)

private lemma slopeSwap_swap (u : E × E) : slopeSwap E (slopeSwap E u) = u := by
  rcases u with ⟨m,t⟩
  ext <;> simp [slopeSwap]

private lemma slopeMap_swap (u : E × E) :
    slopeMap E (slopeSwap E u) = slopeMap E u := by
  rcases u with ⟨m,t⟩
  ext i
  fin_cases i <;> dsimp [slopeMap, slopeSwap] <;> ring

private lemma slope_fixed_card :
    (Finset.univ.filter (fun u : E × E => slopeSwap E u = u)).card
       ≤ Fintype.card E := by
  classical
  let T : Finset (E × E) := Finset.univ.filter (fun u : E × E => slopeSwap E u = u)
  let proj : (↥T) → E := fun u => (u.1).1
  have hp : Function.Injective proj := by
    intro a b h
    apply Subtype.ext
    rcases a with ⟨⟨m,t⟩, ha⟩
    rcases b with ⟨⟨n,s⟩, hb⟩
    change m = n at h
    dsimp [T, slopeSwap] at ha hb
    have ha' : -t - m = m := by simpa using ha
    have hb' : -s - n = n := by simpa using hb
    cases h
    have : t = s := by
      linear_combination - ha' + hb' 
    cases this
    rfl
  change T.card ≤ Fintype.card E
  simpa using (Fintype.card_le_of_injective proj hp)

private def slopeFinset : Finset (Space E 2) :=
  Finset.univ.image (slopeMap E)

private def vertFinset : Finset (Space E 2) :=
  Finset.univ.image (fun t : E => ![0,t])

private def planeFinset : Finset (Space E 2) := slopeFinset E ∪ vertFinset E

private lemma slope_card_bound :
    2 * (slopeFinset E).card ≤ (Fintype.card E) * (Fintype.card E) + Fintype.card E := by
  classical
  have h := image_involution_bound (α := E × E) (β := Space E 2)
       (slopeMap E) (slopeSwap E) (slopeSwap_swap E) (slopeMap_swap E)
  have hf := slope_fixed_card E
  change 2 * (slopeFinset E).card ≤ _
  change 2 * (slopeFinset E).card ≤ Fintype.card (E × E) +
    (Finset.univ.filter (fun u : E × E => slopeSwap E u = u)).card at h
  simpa [Fintype.card_prod] using (le_trans h (Nat.add_le_add_left hf _))

private lemma plane_card_bound :
    2 * (planeFinset E).card ≤ (Fintype.card E) * (Fintype.card E) + 3 * Fintype.card E := by
  classical
  have h₁ := slope_card_bound E
  have hv : (vertFinset E).card ≤ Fintype.card E := by
    simpa [vertFinset] using
      (Finset.card_image_le (s := (Finset.univ : Finset E)) (f := fun t : E => ![0,t]))
  have hu := Finset.card_union_le (slopeFinset E) (vertFinset E)
  change (planeFinset E).card ≤ _ at hu
  omega


private lemma plane_kakeya :
    IsKakeya (F:=E) (d:=2) (↑(planeFinset E) : Set (Space E 2)) := by
  classical
  intro x
  by_cases hu : x 0 = 0
  · refine ⟨(0 : Space E 2), ?_⟩
    intro z hz
    rcases hz with ⟨a, rfl⟩
    have hmem : ( (0 : Space E 2) + a • x) ∈ vertFinset E := by
      change _ ∈ Finset.univ.image (fun t : E => ![0,t])
      apply Finset.mem_image.mpr
      refine ⟨a * x 1, Finset.mem_univ _, ?_⟩
      ext i
      fin_cases i
      · simp [hu]
      · simp
    change _ ∈ planeFinset E
    exact Finset.mem_union.mpr (Or.inr hmem)
  · let m : E := x 1 / x 0
    let y : Space E 2 := slopeMap E (m, 0)
    refine ⟨y, ?_⟩
    intro z hz
    rcases hz with ⟨a, rfl⟩
    have heq : y + a • x = slopeMap E (m, a * x 0) := by
      ext i
      fin_cases i
      · simp [y, slopeMap]
      · dsimp [y, slopeMap, m]
        field_simp
        ring
    have hmem : y + a • x ∈ slopeFinset E := by
      change _ ∈ Finset.univ.image (slopeMap E)
      apply Finset.mem_image.mpr
      exact ⟨(m, a * x 0), Finset.mem_univ _, heq.symm⟩
    change _ ∈ planeFinset E
    exact Finset.mem_union.mpr (Or.inl hmem)

end Plane

section FourierPlane
open LeanEval.Combinatorics.FraserKakeyaProblem
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E]

private lemma char_conj (ψ : AddChar E ℂ) (a : E) :
    (starRingEnd ℂ) (ψ a) = ψ (-a) := by
  rw [AddChar.map_neg_eq_inv]
  exact (Complex.inv_eq_conj (ψ.norm_apply _)).symm

private lemma orth_plane (ψ : AddChar E ℂ) (hp : ψ.IsPrimitive)
    (v : Space E 2) :
    (∑ w : Space E 2, ψ (dot w v)) =
      if v = 0 then (Fintype.card E : ℂ) ^ 2 else 0 := by
  classical
  have hcoord (a b : E) :
      dot (![a,b] : Space E 2) v = a * v 0 + b * v 1 := by
        simp [dot, Fin.sum_univ_two]
  rw [Fintype.sum_equiv (finTwoArrowEquiv E)
    (fun w : Space E 2 => ψ (dot w v))
    (fun p : E × E => ψ (dot (![p.1,p.2] : Space E 2) v))]
  · rw [Fintype.sum_prod_type]
    simp_rw [hcoord]
    simp_rw [AddChar.map_add_eq_mul]
    simp_rw [← Finset.mul_sum]
    -- factor the rectangular sum
    rw [← Finset.sum_mul]
    -- Now both one dimensional sums are the standard primitive sums.
    rw [AddChar.sum_mulShift (v 0) hp, AddChar.sum_mulShift (v 1) hp]
    by_cases h0 : v = 0
    · subst v
      simp [pow_two]
    · have hor : v 0 ≠ 0 ∨ v 1 ≠ 0 := by
        by_contra hn
        push_neg at hn
        apply h0
        funext i
        fin_cases i <;> simp [hn.1, hn.2]
      rcases hor with hor | hor
      · simp [h0, hor]
      · by_cases hz : v 0 = 0
        · simp [h0, hz, hor]
        · simp [h0, hz]
  · intro w
    rfl


private lemma dot_sub_vec (w : Space E 2) (x y : Space E 2) :
    dot w (x - y) = dot w x - dot w y := by
  simp [dot, Fin.sum_univ_two]
  ring

private lemma plane_parseval (ψ : AddChar E ℂ) (hp : ψ.IsPrimitive)
    (ν : Space E 2 → ℝ) :
    (∑ w : Space E 2, ‖fourier ψ ν w‖ ^ 2)
       = (Fintype.card E : ℝ)^2 * ∑ x, (ν x)^2 := by
  classical
  -- prove the identity after casting to `ℂ`; the computation is just
  -- character orthogonality.
  apply Complex.ofReal_injective
  -- cast the squares and open the two transforms
  push_cast
  have hn (z : ℂ) : ( (‖z‖ : ℂ))^2 = (Complex.normSq z : ℂ) := by
    norm_cast
    exact Complex.sq_norm z
  simp_rw [hn, Complex.normSq_eq_conj_mul_self]
  simp_rw [LeanEval.Combinatorics.FraserKakeyaProblem.fourier]
  simp_rw [map_sum, map_mul, char_conj]
  simp only [neg_neg, Complex.conj_ofReal]
  -- expand the product of the two sums
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  -- put the frequency sum on the inside
  rw [Finset.sum_comm]
  -- interchange the two inner sums as well
  have swap (y : Space E 2) :
      (∑ x : Space E 2, ∑ i : Space E 2,
        ψ (dot x y) * (ν y : ℂ) * (ψ (-dot x i) * (ν i : ℂ))) =
      (∑ i : Space E 2, ∑ x : Space E 2,
        ψ (dot x y) * (ν y : ℂ) * (ψ (-dot x i) * (ν i : ℂ))) := by
        exact Finset.sum_comm
  simp_rw [swap]
  have hre (w x y : Space E 2) :
      ψ (dot w x) * (ν x : ℂ) * (ψ (- dot w y) * (ν y : ℂ)) =
        ((ν x : ℂ) * (ν y : ℂ)) * ψ (dot w (x-y)) := by
    rw [dot_sub_vec]
    rw [sub_eq_add_neg, AddChar.map_add_eq_mul]
    ring
  simp_rw [hre]
  simp_rw [← Finset.mul_sum]
  simp_rw [orth_plane ψ hp]
  simp_rw [sub_eq_zero]
  -- only the diagonal survives
  simp_rw [mul_ite, mul_zero]
  simp_rw [Finset.sum_ite_eq]
  simp
  rw [← Finset.sum_mul]
  ring

end FourierPlane



section Upper
open LeanEval.Combinatorics.FraserKakeyaProblem
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E]

-- the useful, two-vector version
private lemma dot_line' {n} (u y v : Space E n) (a:E) :
  dot u (y + a • v) = dot u y + a * dot u v := by
    simp [dot, Finset.mul_sum, Finset.sum_add_distrib]
    -- pointwise distributivity is handled by `ring`
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib]
    simp
    apply Finset.sum_congr rfl
    intro i hi
    ring

private lemma kernel_le {n} (u : Space E n) (hu : u ≠ 0) :
  (Finset.univ.filter (fun x : Space E n => dot u x = 0)).card * Fintype.card E
      ≤ Fintype.card (Space E n) := by
  classical
  have hi : ∃ i : Fin n, u i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hu (funext h)
  choose i hi using hi
  let T : Finset (Space E n) := Finset.univ.filter (fun x : Space E n => dot u x = 0)
  let ei : Space E n := fun j => if j = i then 1 else 0
  have hei : dot u ei = u i := by
    simp [dot, ei]
  let inj : (↥T × E) → Space E n := fun p => p.1.1 + p.2 • ei
  have hinj : Function.Injective inj := by
    intro A B h
    rcases A with ⟨⟨v,hv⟩,a⟩
    rcases B with ⟨⟨w,hw⟩,b⟩
    have hv' : dot u v = 0 := (Finset.mem_filter.mp hv).2
    have hw' : dot u w = 0 := (Finset.mem_filter.mp hw).2
    have he : a = b := by
      have hdot := congrArg (dot u) h
      dsimp [inj] at hdot
      rw [dot_line', dot_line', hv', hw', hei] at hdot
      simp only [zero_add] at hdot
      exact (mul_right_cancel₀ hi hdot)
    subst b
    dsimp [inj] at h
    have : v = w := add_right_cancel h
    subst w
    rfl
  change T.card * Fintype.card E ≤ _
  simpa using (Fintype.card_le_of_injective inj hinj)

private lemma sum_line_char {n} (ψ : AddChar E ℂ) (hp : ψ.IsPrimitive)
    (u y v : Space E n) :
    (∑ a : E, ψ (- dot u (y + a • v))) =
       ψ (-(dot u y)) * (if dot u v = 0 then (Fintype.card E : ℂ) else 0) := by
  classical
  simp_rw [dot_line']
  have h (a : E) : -(dot u y + a * dot u v) =
      -(dot u y) + a * (-(dot u v)) := by ring
  simp_rw [h, AddChar.map_add_eq_mul, ← Finset.mul_sum]
  rw [AddChar.sum_mulShift (-(dot u v)) hp]
  by_cases hz : dot u v = 0 <;> simp [hz]


private lemma incidence_real_sum {n} (Y : Space E n → Space E n) :
    (∑ z : Space E n, ∑ v : Space E n, ∑ a : E,
      if Y v + a • v = z then (1:ℝ) else 0)
       = (Fintype.card (Space E n) : ℝ) * Fintype.card E := by
  classical
  rw [Finset.sum_comm]
  have sw (v : Space E n) :
    (∑ z : Space E n, ∑ a : E,
      if Y v + a • v = z then (1:ℝ) else 0) =
    (∑ a : E, ∑ z : Space E n,
      if Y v + a • v = z then (1:ℝ) else 0) := by exact Finset.sum_comm
  simp_rw [sw, Finset.sum_ite_eq]
  simp

private lemma incidence_complex_delta {n} (Y : Space E n → Space E n)
    (g : Space E n → ℂ) :
    (∑ z : Space E n, g z *
      (∑ v : Space E n, ∑ a : E,
        if Y v + a • v = z then (1:ℂ) else 0)) =
      ∑ v : Space E n, ∑ a : E, g (Y v + a • v) := by
  classical
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have sw (v : Space E n) :
    (∑ z : Space E n, ∑ a : E,
      g z * (if Y v + a • v = z then (1:ℂ) else 0)) =
    (∑ a : E, ∑ z : Space E n,
      g z * (if Y v + a • v = z then (1:ℂ) else 0)) := by exact Finset.sum_comm
  simp_rw [sw, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq]
  simp

private lemma kakeya_upper {n} {S : Set (Space E n)} (hS : IsKakeya S)
    (ψ : AddChar E ℂ) (hψ : ψ ≠ 1) :
    ∃ μ : Space E n → ℝ, IsProbabilityMeasureOn S μ ∧
      ∀ u, u ≠ 0 → ‖fourier ψ μ u‖ ≤ (Fintype.card E : ℝ)⁻¹ := by
  classical
  choose Y hY using hS
  let C : Space E n → ℝ := fun z =>
    ∑ v : Space E n, ∑ a : E,
      if Y v + a • v = z then (1:ℝ) else 0
  let D : ℝ := (Fintype.card (Space E n) : ℝ) * (Fintype.card E : ℝ)
  let μ : Space E n → ℝ := fun z => C z / D
  have hN : 0 < (Fintype.card (Space E n) : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr (inferInstance : Nonempty (Space E n)))
  have hq : 0 < (Fintype.card E : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr (inferInstance : Nonempty E))
  have hD : 0 < D := by
    dsimp [D]
    exact mul_pos hN hq
  have hC (z : Space E n) : 0 ≤ C z := by
    dsimp [C]
    apply Finset.sum_nonneg
    intro v hv
    apply Finset.sum_nonneg
    intro a ha
    by_cases h : Y v + a • v = z <;> simp [h]
  refine ⟨μ, ?_, ?_⟩
  · -- probability and support
    refine ⟨?_, ?_, ?_⟩
    · intro z
      exact div_nonneg (hC z) (le_of_lt hD)
    · change (∑ z : Space E n, C z / D) = 1
      rw [← Finset.sum_div]
      have htot : (∑ z : Space E n, C z) = D := by
        simpa [C, D] using (incidence_real_sum (E:=E) Y)
      rw [htot, div_self (ne_of_gt hD)]
    · intro z hz
      have hex : ∃ v : Space E n, ∃ a : E, Y v + a • v = z := by
        by_contra hn
        push_neg at hn
        have hz0 : C z = 0 := by
          dsimp [C]
          apply Finset.sum_eq_zero
          intro v hv
          apply Finset.sum_eq_zero
          intro a ha
          simp [hn v a]
        exact hz (by simp [μ, hz0])
      rcases hex with ⟨v,a,ha⟩
      apply hY v
      change ∃ b : E, z = Y v + b • v
      exact ⟨a, ha.symm⟩
  · -- Fourier estimate
    have hp : ψ.IsPrimitive := AddChar.IsPrimitive.of_ne_one hψ
    have castC (z : Space E n) : (C z : ℂ) =
        ∑ v : Space E n, ∑ a : E,
          if Y v + a • v = z then (1:ℂ) else 0 := by
      dsimp [C]
      push_cast
      apply Finset.sum_congr rfl
      intro v hv
      apply Finset.sum_congr rfl
      intro a ha
      by_cases h : Y v + a • v = z <;> simp [h]
    let A : Space E n → ℂ := fun u =>
      ∑ v : Space E n,
        ψ (-(dot u (Y v))) *
          (if dot u v = 0 then (Fintype.card E : ℂ) else 0)
    have hdelta (u : Space E n) :
        (∑ z : Space E n, ψ (-(dot u z)) * (C z : ℂ)) = A u := by
      simp_rw [castC]
      rw [incidence_complex_delta (E:=E) Y (fun z : Space E n => ψ (-(dot u z)))]
      dsimp [A]
      apply Finset.sum_congr rfl
      intro v hv
      exact sum_line_char (E:=E) ψ hp u (Y v) v
    have hF (u : Space E n) :
        fourier ψ μ u = (D : ℂ)⁻¹ * A u := by
      calc
        fourier ψ μ u =
            ∑ z : Space E n, ψ (-(dot u z)) * ((C z / D : ℝ) : ℂ) := by
              rfl
        _ = ∑ z : Space E n, (D : ℂ)⁻¹ *
              (ψ (-(dot u z)) * (C z : ℂ)) := by
              apply Finset.sum_congr rfl
              intro z hz
              push_cast
              -- commute the scalar to the front
              ring
        _ = (D : ℂ)⁻¹ *
              (∑ z : Space E n, ψ (-(dot u z)) * (C z : ℂ)) := by
                rw [Finset.mul_sum]
        _ = (D : ℂ)⁻¹ * A u := by rw [hdelta]
    have hAnorm (u : Space E n) :
        ‖A u‖ ≤
          ((Finset.univ.filter (fun v : Space E n => dot u v = 0)).card : ℝ)
             * (Fintype.card E : ℝ) := by
      dsimp [A]
      calc
        ‖∑ v : Space E n,
            ψ (-(dot u (Y v))) *
              (if dot u v = 0 then (Fintype.card E : ℂ) else 0)‖ ≤
          ∑ v : Space E n,
            ‖ψ (-(dot u (Y v))) *
              (if dot u v = 0 then (Fintype.card E : ℂ) else 0)‖ :=
                norm_sum_le _ _
        _ = ∑ v : Space E n,
              (if dot u v = 0 then (Fintype.card E : ℝ) else 0) := by
              apply Finset.sum_congr rfl
              intro v hv
              by_cases h : dot u v = 0
              · simp [h, norm_mul, AddChar.norm_apply, Complex.norm_natCast]
              · simp [h, norm_mul, AddChar.norm_apply]
        _ = ((Finset.univ.filter (fun v : Space E n => dot u v = 0)).card : ℝ)
                * (Fintype.card E : ℝ) := by
              -- a sum of a fixed constant over a filter
              symm
              -- turn it into `card • c`
              rw [← Finset.sum_filter]
              simp [Finset.sum_const, nsmul_eq_mul]
    intro u hu
    rw [hF]
    rw [norm_mul, norm_inv]
    have hnormD : ‖(D : ℂ)‖ = D := by
      rw [Complex.norm_real]
      exact abs_of_pos hD
    rw [hnormD]
    have hk := kernel_le (E:=E) u hu
    have hkR :
        ((Finset.univ.filter (fun v : Space E n => dot u v = 0)).card : ℝ)
              * (Fintype.card E : ℝ)
          ≤ (Fintype.card (Space E n) : ℝ) := by
      exact_mod_cast hk
    calc
      D⁻¹ * ‖A u‖ ≤ D⁻¹ *
            (((Finset.univ.filter (fun v : Space E n => dot u v = 0)).card : ℝ)
              * (Fintype.card E : ℝ)) := by
                exact mul_le_mul_of_nonneg_left (hAnorm u) (by positivity)
      _ ≤ D⁻¹ * (Fintype.card (Space E n) : ℝ) := by
                exact mul_le_mul_of_nonneg_left hkR (by positivity)
      _ = (Fintype.card E : ℝ)⁻¹ := by
            dsimp [D]
            field_simp

end Upper

section SharpHelpers
open LeanEval.Combinatorics.FraserKakeyaProblem
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E]

private def projTwo {d : ℕ} (hd : 2 ≤ d) (x : Space E d) : Space E 2 :=
  fun i => x (Fin.castLE hd i)

/-- Extend two coordinates by zero.  Writing the extension with a test on the
index makes summing the unused coordinates painless. -/
private def incTwo {d : ℕ} (hd : 2 ≤ d) (w : Space E 2) : Space E d :=
  fun j => if h : (j : ℕ) < 2 then w ⟨j, h⟩ else 0

private lemma projTwo_inc {d : ℕ} (hd : 2 ≤ d) (w : Space E 2) :
    projTwo (E:=E) hd (incTwo (E:=E) hd w) = w := by
  funext i
  change (dite _ _ _) = _
  have hi : ((Fin.castLE hd i : Fin d) : ℕ) < 2 := i.isLt
  rw [dif_pos hi]
  congr 1

private lemma projTwo_add_smul {d : ℕ} (hd : 2 ≤ d)
    (y x : Space E d) (a : E) :
    projTwo (E:=E) hd (y + a • x) =
       projTwo (E:=E) hd y + a • projTwo (E:=E) hd x := by
  rfl

-- Only the first two summands are left in a dot product with a zero extension.
private lemma dot_incTwo {d : ℕ} (hd : 2 ≤ d) (w : Space E 2)
    (x : Space E d) :
    dot (incTwo (E:=E) hd w) x = dot w (projTwo (E:=E) hd x) := by
  classical
  -- write the ambient dimension with its first two entries displayed
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 2 := by
    exact ⟨d-2, by omega⟩
  -- split the finite sums twice; what remains has zero left factor
  unfold LeanEval.Combinatorics.FraserKakeyaProblem.dot
  conv_lhs =>
    rw [Fin.sum_univ_succ]
    rw [Fin.sum_univ_succ]
  -- the two-dimensional sum on the other side
  conv_rhs => rw [Fin.sum_univ_two]
  simp [incTwo, projTwo]
  left
  congr 1

private def liftedPlane (d : ℕ) (hd : 2 ≤ d) : Set (Space E d) :=
  {x | projTwo (E:=E) hd x ∈ (↑(planeFinset E) : Set (Space E 2))}

private lemma liftedPlane_kakeya {d : ℕ} (hd : 2 ≤ d) :
    IsKakeya (F:=E) (d:=d) (liftedPlane (E:=E) d hd) := by
  classical
  intro x
  have hpl := plane_kakeya E (projTwo (E:=E) hd x)
  rcases hpl with ⟨y, hy⟩
  refine ⟨incTwo (E:=E) hd y, ?_⟩
  intro z hz
  rcases hz with ⟨a, rfl⟩
  change projTwo (E:=E) hd (incTwo (E:=E) hd y + a • x) ∈
    (↑(planeFinset E) : Set (Space E 2))
  rw [projTwo_add_smul, projTwo_inc]
  apply hy
  exact ⟨a, rfl⟩

-- push a mass down to the first two coordinates
private def pushPlane {d : ℕ} (hd : 2 ≤ d) (m : Space E d → ℝ) :
    Space E 2 → ℝ := fun t =>
  ∑ x : Space E d, if projTwo (E:=E) hd x = t then m x else 0

private lemma pushPlane_nonneg {d : ℕ} (hd : 2 ≤ d)
    {m : Space E d → ℝ} (hm : ∀ x, 0 ≤ m x) :
    ∀ t, 0 ≤ pushPlane (E:=E) hd m t := by
  classical
  intro t
  dsimp [pushPlane]
  apply Finset.sum_nonneg
  intro x hx
  split_ifs <;> simp [hm]

private lemma pushPlane_sum {d : ℕ} (hd : 2 ≤ d)
    (m : Space E d → ℝ) :
    (∑ t : Space E 2, pushPlane (E:=E) hd m t) = ∑ x, m x := by
  classical
  dsimp [pushPlane]
  rw [Finset.sum_comm]
  simp [Finset.sum_ite_eq']

-- a delta computation valid also with real masses cast to complex
private lemma pushPlane_complex {d : ℕ} (hd : 2 ≤ d)
    (m : Space E d → ℝ) (g : Space E 2 → ℂ) :
    (∑ t : Space E 2, g t * (pushPlane (E:=E) hd m t : ℂ)) =
      ∑ x : Space E d, g (projTwo (E:=E) hd x) * (m x : ℂ) := by
  classical
  simp_rw [pushPlane]
  push_cast
  -- move the casts through the delta
  -- it is a genuine push-forward, so change the order of the sums
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  -- exactly one target contributes
  classical
  -- the casted indicators can be simplified termwise
  have ht (t : Space E 2) :
      g t * ( (if projTwo (E:=E) hd x = t then m x else 0 : ℝ) : ℂ) =
        (if projTwo (E:=E) hd x = t
           then g t * (m x : ℂ) else 0) := by
      by_cases h : projTwo (E:=E) hd x = t <;> simp [h]
  simp_rw [ht]
  simp

private lemma pushPlane_support {d : ℕ} (hd : 2 ≤ d)
    {m : Space E d → ℝ}
    (hm : ∀ x, m x ≠ 0 → x ∈ liftedPlane (E:=E) d hd) :
    ∀ t, pushPlane (E:=E) hd m t ≠ 0 →
       t ∈ (↑(planeFinset E) : Set (Space E 2)) := by
  classical
  intro t ht
  by_contra hn
  have hzero : pushPlane (E:=E) hd m t = 0 := by
    dsimp [pushPlane]
    apply Finset.sum_eq_zero
    intro x hx
    by_cases hxt : projTwo (E:=E) hd x = t
    · have hx0 : m x = 0 := by
        by_contra hx0
        have hxS := hm x hx0
        change projTwo (E:=E) hd x ∈ (↑(planeFinset E) : Set (Space E 2)) at hxS
        exact hn (by simpa [hxt] using hxS)
      simp [hxt, hx0]
    · simp [hxt]
  exact ht hzero

private lemma pushPlane_fourier {d : ℕ} (hd : 2 ≤ d)
    (ψ : AddChar E ℂ) (m : Space E d → ℝ) (w : Space E 2) :
    fourier ψ (pushPlane (E:=E) hd m) w =
      fourier ψ m (incTwo (E:=E) hd w) := by
  classical
  unfold LeanEval.Combinatorics.FraserKakeyaProblem.fourier
  rw [pushPlane_complex (E:=E) hd m (fun t : Space E 2 => ψ (-(dot w t)))]
  apply Finset.sum_congr rfl
  intro x hx
  rw [dot_incTwo (E:=E) hd]

end SharpHelpers
/-ResultProofDefinitionsEnd-/
/-ResultDefinitionsEnd-/

/-ResultBegin-/

theorem fraser_kakeya_fourier_decay_and_sharp {d : ℕ} (_hd : 2 ≤ d) {K : Set (Space F d)} (_hK : IsKakeya K)
    (χ : AddChar F ℂ) (_hχ : χ ≠ 1) :
    (∃ μ : Space F d → ℝ, IsProbabilityMeasureOn K μ ∧
      ∀ ξ : Space F d, ξ ≠ 0 →
        ‖fourier χ μ ξ‖ ≤ (Fintype.card F : ℝ)⁻¹) ∧
    (∀ κ : ℝ, 0 < κ → κ < 1 →
      ∃ Q : ℕ, ∀ (F' : Type*) [Field F'] [Fintype F'] [DecidableEq F'],
        Q ≤ Fintype.card F' →
          ∃ K' : Set (Space F' d), IsKakeya K' ∧
            ∀ μ : Space F' d → ℝ, IsProbabilityMeasureOn K' μ →
              ∃ ξ : Space F' d, ξ ≠ 0 ∧
                κ * (Fintype.card F' : ℝ)⁻¹ ≤
                  ‖fourier (AddChar.FiniteField.primitiveChar_to_Complex F') μ ξ‖) :=
/-ResultProofBegin-/by
  classical
  constructor
  · exact kakeya_upper _hK χ _hχ
  · intro κ hκ hκ1
    have hgap : 0 < 1 - κ^2 := by nlinarith
    obtain ⟨Q, hQ⟩ := exists_nat_gt ( (3:ℝ) * (1 + κ^2) / (1-κ^2))
    refine ⟨Q, ?_⟩
    intro E hfield hfint hdec hlarge
    letI : Field E := hfield
    letI : Fintype E := hfint
    letI : DecidableEq E := hdec
    have hq : 0 < (Fintype.card E : ℝ) := by
      exact_mod_cast (Fintype.card_pos_iff.mpr (inferInstance : Nonempty E))
    have hlarge' : ((Q:ℕ):ℝ) ≤ (Fintype.card E : ℝ) := by
      exact_mod_cast hlarge
    have hthr : (3:ℝ) * (1 + κ^2) / (1-κ^2) < (Fintype.card E : ℝ) :=
      lt_of_lt_of_le hQ hlarge'
    refine ⟨liftedPlane (E:=E) d _hd, liftedPlane_kakeya (E:=E) _hd, ?_⟩
    intro m hm
    let ψ : AddChar E ℂ := AddChar.FiniteField.primitiveChar_to_Complex E
    let ν : Space E 2 → ℝ := pushPlane (E:=E) _hd m
    have hν0 : ∀ t, 0 ≤ ν t := pushPlane_nonneg (E:=E) _hd hm.1
    have hνsum : (∑ t : Space E 2, ν t) = 1 := by
      rw [pushPlane_sum (E:=E) _hd m]
      exact hm.2.1
    have hνsupp : ∀ t, ν t ≠ 0 →
        t ∈ (planeFinset E) := by
      exact pushPlane_support (E:=E) _hd hm.2.2
    -- it is easier to prove existence by contradiction, bounding all
    -- nontrivial coefficients and then using the planar energy identity.
    by_contra hn
    push_neg at hn
    have hsmall : ∀ w : Space E 2, w ≠ 0 →
        ‖fourier ψ ν w‖ < κ * (Fintype.card E : ℝ)⁻¹ := by
      intro w hw
      have he : incTwo (E:=E) _hd w ≠ 0 := by
        intro hh
        have := congrArg (projTwo (E:=E) _hd) hh
        have hz0 : projTwo (E:=E) _hd (0 : Space E d) = (0 : Space E 2) := rfl
        have hh' : w = 0 := by
          rw [projTwo_inc, hz0] at this
          exact this
        exact hw hh'
      have H := hn (incTwo (E:=E) _hd w) he
      simpa [ψ, pushPlane_fourier (E:=E) _hd ψ m w, ν] using H
    have hzero : fourier ψ ν (0 : Space E 2) = 1 := by
      unfold LeanEval.Combinatorics.FraserKakeyaProblem.fourier
      have hdot (x : Space E 2) : dot (0 : Space E 2) x = 0 := by
        simp [dot]
      simp_rw [hdot]
      simp
      -- casting the total mass
      exact_mod_cast hνsum
    let b : ℝ := κ * (Fintype.card E : ℝ)⁻¹
    have hb : 0 ≤ b := by dsimp [b]; positivity
    have hup : (∑ w : Space E 2, ‖fourier ψ ν w‖^2) ≤ 1 + κ^2 := by
      calc
        (∑ w : Space E 2, ‖fourier ψ ν w‖^2) ≤
            ∑ w : Space E 2,
              (b^2 + if w = 0 then (1:ℝ) else 0) := by
            apply Finset.sum_le_sum
            intro w hw
            by_cases hz : w = 0
            · subst w
              simp [hzero, sq_nonneg b]
            · have hh := (hsmall w hz).le
              have hs : ‖fourier ψ ν w‖ ^ 2 ≤ b^2 :=
                (sq_le_sq₀ (norm_nonneg _) hb).2 hh
              simpa [hz] using hs
        _ = (Fintype.card (Space E 2) : ℝ) * b^2 + 1 := by
              simp [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
        _ = 1 + κ^2 := by
              have hc : (Fintype.card (Space E 2) : ℝ) =
                    (Fintype.card E : ℝ)^2 := by
                norm_cast
                simp [Fintype.card_fun]
              rw [hc]
              dsimp [b]
              field_simp
              <;> ring
    let T : Finset (Space E 2) := planeFinset E
    have hout (t : Space E 2) (ht : t ∉ T) : ν t = 0 := by
      by_contra hn0
      exact ht (hνsupp t hn0)
    have hrest (f : Space E 2 → ℝ)
        (hfz : ∀ t, ν t = 0 → f t = 0) :
        (∑ t ∈ T, f t) = ∑ t, f t := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro x hx hxT
      exact hfz x (hout x hxT)
    have hsumT : (∑ t ∈ T, ν t) = 1 := by
      rw [hrest (fun t => ν t) (by intros; assumption)]
      exact hνsum
    have hsqT : (∑ t ∈ T, (ν t)^2) = ∑ t, (ν t)^2 := by
      apply hrest
      intro t ht
      simp [ht]
    have hcs : (1:ℝ) ≤ (∑ t : Space E 2, (ν t)^2) * (T.card : ℝ) := by
      have H := Finset.sum_mul_sq_le_sq_mul_sq T ν (fun _ => (1:ℝ))
      -- simplify the constant sequence and use that the masses on T sum to one
      simp [Finset.sum_const, nsmul_eq_mul, hsumT, hsqT] at H ⊢
      nlinarith
    have hparse := plane_parseval (E:=E) ψ
          (AddChar.FiniteField.primitiveChar_to_Complex_isPrimitive E)
          ν
    have hq2 : (0:ℝ) ≤ (Fintype.card E : ℝ)^2 := sq_nonneg _
    have hcard : 2 * (T.card : ℝ) ≤
          (Fintype.card E : ℝ)^2 + 3 * (Fintype.card E : ℝ) := by
      dsimp [T]
      norm_cast
      simpa [pow_two] using (plane_card_bound E)
    -- Combining Cauchy--Schwarz, Parseval, and the assumed upper bound gives
    -- the impossible numerical inequality at our chosen threshold.
    have hnum : (Fintype.card E : ℝ)^2 ≤ (T.card : ℝ) * (1 + κ^2) := by
      rw [plane_parseval (E:=E) ψ
          (AddChar.FiniteField.primitiveChar_to_Complex_isPrimitive E) ν] at hup
      nlinarith
    have : (1-κ^2) * (Fintype.card E : ℝ) ≤ 3 * (1+κ^2) := by
      have hkpos : 0 < 1 + κ^2 := by positivity
      have := hnum
      nlinarith
    have hbad : (3:ℝ) * (1+κ^2) <
        (Fintype.card E : ℝ) * (1-κ^2) :=
      (div_lt_iff₀ hgap).mp hthr
    nlinarith
/-ResultProofEnd-/
/-ResultEnd-/

end Submission
