import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.Trace
import Mathlib.RepresentationTheory.FiniteIndex
import Submission.OddOrder.PF.Section01.NormalSubgroupInduction

/-!
# Compatibility of class-function induction with induced representations

The explicit averaging operation `ClassFunction.induce` used in the
Peterfalvi port is the character of Mathlib's induced representation.  We
prove this first for coinduction by writing a coinduced vector as a function
on right cosets and computing the trace.  Mathlib's finite-index
induction--coinduction isomorphism then gives the desired induced
representation.

Mathlib's current bundled finite-index induction API has a same-universe
constraint on the field, group, and representation space.  The final bundled
compatibility and irreducibility theorems therefore use one universe; the
underlying coinduced-character computation is universe-polymorphic.
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped BigOperators Classical

universe u v w

namespace InducedCharacterCompatibility

variable {k : Type u} [Field k] {G : Type v} [Group G]
  (H : Subgroup G) {V : Type w} [AddCommGroup V] [Module k V]
  (rho : Representation k H V)

/-- Right cosets of `H`, in the quotient convention used by Mathlib's
coinduced representation. -/
abbrev Cosets := Quotient (QuotientGroup.rightRel H)

/-- The right coset represented by `g`. -/
def cosetMk (g : G) : Cosets H :=
  Quotient.mk (QuotientGroup.rightRel H) g

/-- The subgroup factor in the decomposition of `g` determined by the
chosen representative of its right coset. -/
def cosetFactor (g : G) : H :=
  ⟨g * (Quotient.out (cosetMk H g))⁻¹,
    QuotientGroup.rightRel_apply.mp
      (Quotient.exact (Quotient.out_eq (cosetMk H g)))⟩

theorem cosetFactor_mul_out (g : G) :
    (cosetFactor H g : G) * Quotient.out (cosetMk H g) = g := by
  simp [cosetFactor]

theorem quotient_mk_mul_left (h : H) (g : G) :
    cosetMk H ((h : G) * g) = cosetMk H g := by
  apply Quotient.sound
  change (QuotientGroup.rightRel H) ((h : G) * g) g
  rw [QuotientGroup.rightRel_apply]
  simp

theorem cosetFactor_mul_left (h : H) (g : G) :
    cosetFactor H ((h : G) * g) = h * cosetFactor H g := by
  apply Subtype.ext
  simp [cosetFactor, quotient_mk_mul_left, mul_assoc]

/-- Coinduced vectors are functions on right cosets after choosing a
representative of each coset. -/
def coindVEquivPi :
    Representation.coindV H.subtype rho ≃ₗ[k] (Cosets H → V) where
  toFun f q := f.1 q.out
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun F := ⟨fun g ↦ rho (cosetFactor H g) (F (cosetMk H g)), by
    intro h g
    change rho (cosetFactor H ((h : G) * g)) (F (cosetMk H ((h : G) * g))) =
      rho h (rho (cosetFactor H g) (F (cosetMk H g)))
    rw [quotient_mk_mul_left, cosetFactor_mul_left, map_mul]
    rfl⟩
  left_inv f := by
    apply Subtype.ext
    funext g
    change rho (cosetFactor H g) (f.1 (Quotient.out (cosetMk H g))) = f.1 g
    calc
      _ = f.1 ((cosetFactor H g : G) * Quotient.out (cosetMk H g)) :=
        (f.property (cosetFactor H g) (Quotient.out (cosetMk H g))).symm
      _ = f.1 g := congrArg f.1 (cosetFactor_mul_out H g)
  right_inv F := by
    funext q
    change rho (cosetFactor H q.out) (F (cosetMk H q.out)) = F q
    have hmk : cosetMk H q.out = q := Quotient.out_eq q
    rw [hmk]
    have hout : Quotient.out (cosetMk H q.out) = q.out := by
      exact congrArg Quotient.out (Quotient.out_eq q)
    have hfac : cosetFactor H q.out = 1 := by
      apply Subtype.ext
      simp [cosetFactor, hout]
    rw [hfac, map_one]
    rfl

/-- An endomorphism of a product which permutes coordinates and applies a
linear endomorphism in each coordinate. -/
def weightedReindexEnd {Q : Type*} (s : Q → Q) (A : Q → Module.End k V) :
    Module.End k (Q → V) :=
  LinearMap.pi fun q ↦ (A q).comp (LinearMap.proj (s q))

@[simp]
theorem weightedReindexEnd_apply {Q : Type*} (s : Q → Q)
    (A : Q → Module.End k V) (F : Q → V) (q : Q) :
    weightedReindexEnd s A F q = A q (F (s q)) :=
  rfl

theorem coindVEquivPi_conj (g : G) :
    (coindVEquivPi H rho).conj (Representation.coind H.subtype rho g) =
      weightedReindexEnd
        (fun q : Cosets H ↦ cosetMk H (q.out * g))
        (fun q : Cosets H ↦ rho (cosetFactor H (q.out * g))) := by
  ext F q
  rfl

/-- The trace of a weighted coordinate permutation is the sum of the traces
on its fixed coordinates. -/
theorem trace_weightedReindexEnd {Q : Type*} [Fintype Q] [DecidableEq Q]
    [FiniteDimensional k V] (s : Q → Q) (A : Q → Module.End k V) :
    LinearMap.trace k (Q → V) (weightedReindexEnd s A) =
      ∑ q : Q, if s q = q then LinearMap.trace k V (A q) else 0 := by
  classical
  let b := Module.finBasis k V
  let B := Pi.basis (fun _ : Q ↦ b)
  rw [LinearMap.trace_eq_matrix_trace k B]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply, B, Pi.basis_repr,
    Pi.basis_apply, weightedReindexEnd_apply]
  let d : (q : Q) → Fin (Module.finrank k V) → k := fun q i ↦
    b.repr (A q ((Pi.single q (b i) : Q → V) (s q))) i
  change (∑ qi : Σ _ : Q, Fin (Module.finrank k V), d qi.1 qi.2) = _
  rw [Fintype.sum_sigma' d]
  apply Fintype.sum_congr
  intro q
  by_cases hq : s q = q
  · simp only [d, hq, Pi.single_eq_same, if_pos]
    rw [LinearMap.trace_eq_matrix_trace k b]
    simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply]
  · simp [d, hq]

/-- Character formula for coinduction from a normal subgroup, expressed as a
sum over right cosets. -/
theorem coind_character_formula_normal [Fintype G] [Fintype (Cosets H)]
    [FiniteDimensional k V] [H.Normal] (g : G) :
    Representation.character (Representation.coind H.subtype rho) g =
      if hg : g ∈ H then
        ∑ q : Cosets H,
          Representation.character rho
            ⟨q.out * g * q.out⁻¹,
              (inferInstance : H.Normal).conj_mem g hg q.out⟩
      else 0 := by
  classical
  have htrace := LinearMap.trace_conj'
    (Representation.coind H.subtype rho g) (coindVEquivPi H rho)
  rw [coindVEquivPi_conj, trace_weightedReindexEnd] at htrace
  change (LinearMap.trace k (Representation.coindV H.subtype rho)
      (Representation.coind H.subtype rho g)) = _
  rw [← htrace]
  by_cases hg : g ∈ H
  · rw [dif_pos hg]
    apply Fintype.sum_congr
    intro q
    have hfix : cosetMk H (q.out * g) = q := by
      calc
        cosetMk H (q.out * g) = cosetMk H q.out := by
          apply Quotient.sound
          change (QuotientGroup.rightRel H) (q.out * g) q.out
          rw [QuotientGroup.rightRel_apply]
          simpa [mul_inv_rev, mul_assoc] using
            (inferInstance : H.Normal).conj_mem g⁻¹ (H.inv_mem hg) q.out
        _ = q := Quotient.out_eq q
    rw [if_pos hfix]
    apply congrArg (Representation.character rho)
    apply Subtype.ext
    have hout := congrArg Quotient.out hfix
    simp [cosetFactor, hout]
  · rw [dif_neg hg]
    apply Fintype.sum_eq_zero
    intro q
    rw [if_neg]
    intro hfix
    apply hg
    have hq : cosetMk H q.out = q := Quotient.out_eq q
    have hrel := Quotient.exact (hfix.trans hq.symm)
    have hconj : q.out * g⁻¹ * q.out⁻¹ ∈ H := by
      simpa [mul_inv_rev, mul_assoc] using
        (QuotientGroup.rightRel_apply.mp hrel)
    have hinv : g⁻¹ ∈ H := by
      have := (inferInstance : H.Normal).conj_mem
        (q.out * g⁻¹ * q.out⁻¹) hconj q.out⁻¹
      simpa [mul_assoc] using this
    exact H.inv_mem_iff.mp hinv

def inverseCosetMap (x : G) : Cosets H :=
  cosetMk H x⁻¹

/-- Each fiber of `x ↦ Hx⁻¹` is a torsor for `H`. -/
noncomputable def subgroupEquivInverseCosetFiber (q : Cosets H) :
    H ≃ {x : G // inverseCosetMap H x = q} := by
  classical
  refine
    { toFun := fun h ↦ ⟨q.out⁻¹ * (h : G), ?_⟩
      invFun := fun x ↦ ⟨q.out * (x : G), ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · change cosetMk H (q.out⁻¹ * (h : G))⁻¹ = q
    calc
      _ = cosetMk H q.out := by
        apply Quotient.sound
        change (QuotientGroup.rightRel H) (q.out⁻¹ * (h : G))⁻¹ q.out
        rw [QuotientGroup.rightRel_apply]
        simp [mul_inv_rev]
      _ = q := Quotient.out_eq q
  · have hx := x.property
    have hq : cosetMk H q.out = q := Quotient.out_eq q
    have hrel := Quotient.exact (hx.trans hq.symm)
    simpa [inverseCosetMap, mul_assoc] using
      (QuotientGroup.rightRel_apply.mp hrel)
  · intro h
    apply Subtype.ext
    simp
  · intro x
    apply Subtype.ext
    simp

theorem conjugate_term_eq_coset_term [H.Normal] (f : ClassFunction H k)
    {g : G} (hg : g ∈ H) (q : Cosets H)
    (x : {x : G // inverseCosetMap H x = q}) :
    f ⟨(x : G)⁻¹ * g * x,
        by simpa using (inferInstance : H.Normal).conj_mem g hg (x : G)⁻¹⟩ =
      f ⟨q.out * g * q.out⁻¹,
        (inferInstance : H.Normal).conj_mem g hg q.out⟩ := by
  let h : H := (subgroupEquivInverseCosetFiber H q).symm x
  have hh : (h : G) = q.out * (x : G) := rfl
  let t : H := ⟨q.out * g * q.out⁻¹,
    (inferInstance : H.Normal).conj_mem g hg q.out⟩
  have harg :
      (⟨(x : G)⁻¹ * g * x,
        by simpa using (inferInstance : H.Normal).conj_mem g hg (x : G)⁻¹⟩ : H) =
        h⁻¹ * t * (h⁻¹)⁻¹ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, t, hh]
    group
  rw [harg]
  exact ClassFunction.conj_apply f h⁻¹ t

/-- Regroup the conjugate sum in the explicit induction formula by right
cosets. -/
theorem sum_conjugates_eq_card_nsmul_sum_cosets [Fintype G] [Fintype H]
    [Fintype (Cosets H)] [H.Normal]
    (f : ClassFunction H k) {g : G} (hg : g ∈ H) :
    (∑ x : G, f ⟨x⁻¹ * g * x,
        by simpa using (inferInstance : H.Normal).conj_mem g hg x⁻¹⟩) =
      Nat.card H • ∑ q : Cosets H,
        f ⟨q.out * g * q.out⁻¹,
          (inferInstance : H.Normal).conj_mem g hg q.out⟩ := by
  classical
  rw [← Fintype.sum_fiberwise (inverseCosetMap H)
    (fun x : G ↦ f ⟨x⁻¹ * g * x,
      by simpa using (inferInstance : H.Normal).conj_mem g hg x⁻¹⟩)]
  calc
    ∑ q : Cosets H,
        ∑ x : {x : G // inverseCosetMap H x = q},
          f ⟨(x : G)⁻¹ * g * x,
            by simpa using (inferInstance : H.Normal).conj_mem g hg (x : G)⁻¹⟩ =
      ∑ q : Cosets H, Fintype.card H •
        f ⟨q.out * g * q.out⁻¹,
          (inferInstance : H.Normal).conj_mem g hg q.out⟩ := by
      apply Fintype.sum_congr
      intro q
      rw [Fintype.card_congr (subgroupEquivInverseCosetFiber H q)]
      rw [← Finset.card_univ, ← Finset.sum_const]
      apply Finset.sum_congr rfl
      intro x _
      exact conjugate_term_eq_coset_term H f hg q x
    _ = Fintype.card H • ∑ q : Cosets H,
        f ⟨q.out * g * q.out⁻¹,
          (inferInstance : H.Normal).conj_mem g hg q.out⟩ := by
      rw [Finset.smul_sum]
    _ = _ := by rw [Nat.card_eq_fintype_card]

/-- The explicit class-function induction formula is the character of
Mathlib's coinduced representation. -/
theorem classFunction_induce_eq_coind_character [Fintype G] [Fintype H]
    [Fintype (Cosets H)] [H.Normal] [FiniteDimensional k V] [CharZero k]
    (g : G) :
    ClassFunction.induce H (ClassFunction.ofRepresentation rho) g =
      Representation.character (Representation.coind H.subtype rho) g := by
  classical
  rw [ClassFunction.induce_apply_formula, coind_character_formula_normal]
  by_cases hg : g ∈ H
  · rw [dif_pos hg]
    have hx (x : G) : x⁻¹ * g * x ∈ H := by
      simpa using (inferInstance : H.Normal).conj_mem g hg x⁻¹
    simp_rw [dif_pos (hx _)]
    rw [sum_conjugates_eq_card_nsmul_sum_cosets H
      (ClassFunction.ofRepresentation rho) hg]
    simp only [ClassFunction.ofRepresentation_apply]
    rw [← Nat.cast_smul_eq_nsmul k, smul_eq_mul, inv_mul_eq_iff_eq_mul₀]
    exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  · rw [dif_neg hg]
    have hx (x : G) : x⁻¹ * g * x ∉ H := by
      intro hx
      apply hg
      have := (inferInstance : H.Normal).conj_mem (x⁻¹ * g * x) hx x
      simpa [mul_assoc] using this
    simp_rw [dif_neg (hx _)]
    simp

end InducedCharacterCompatibility

namespace FDRep

variable {K Γ : Type u} [Field K] [Group Γ] [Fintype Γ]

/-- The finite-dimensional representation induced from a subgroup.

This wrapper records Mathlib's unbundled induced representation as an object
of `FDRep`.  The same-universe parameters reflect the current universe
constraint in `Representation.ind`'s finite-dimensional instance. -/
def induceFromSubgroup (S : Subgroup Γ) (V₀ : FDRep K S) : FDRep K Γ :=
  FDRep.of (Representation.ind S.subtype V₀.ρ)

@[simp]
theorem induceFromSubgroup_ρ (S : Subgroup Γ) (V₀ : FDRep K S) :
    (induceFromSubgroup S V₀).ρ = Representation.ind S.subtype V₀.ρ :=
  FDRep.of_ρ' _

end FDRep

namespace ClassFunction

variable {K Γ : Type u} [Field K] [Group Γ] [Fintype Γ]

/-- Character compatibility between the project-level explicit induction and
Mathlib's induced finite-dimensional representation. -/
theorem ofRepresentation_induceFromSubgroup [CharZero K]
    (S : Subgroup Γ) [S.Normal] (V₀ : FDRep K S) :
    ofRepresentation (FDRep.induceFromSubgroup S V₀).ρ =
      induce S (ofRepresentation V₀.ρ) := by
  classical
  letI : Fintype (InducedCharacterCompatibility.Cosets S) := Fintype.ofFinite _
  letI : DecidableRel (QuotientGroup.rightRel S) := Classical.decRel _
  ext g
  have hcoind :=
    InducedCharacterCompatibility.classFunction_induce_eq_coind_character S V₀.ρ g
  let A : Rep K S := Rep.of V₀.ρ
  have hchar := congrFun
    (Representation.char_iso
      (Representation.equivOfIso (Rep.indCoindIso A))) g
  change Representation.character (FDRep.induceFromSubgroup S V₀).ρ g =
    induce S (ofRepresentation V₀.ρ) g
  rw [FDRep.induceFromSubgroup_ρ]
  exact hchar.trans hcoind.symm

/-- The explicit induction of a realized character is itself realized by
Mathlib's induced representation. -/
theorem induce_ofRepresentation [CharZero K]
    (S : Subgroup Γ) [S.Normal] (V₀ : FDRep K S) :
    induce S (ofRepresentation V₀.ρ) =
      ofRepresentation (FDRep.induceFromSubgroup S V₀).ρ :=
  (ofRepresentation_induceFromSubgroup S V₀).symm

/-- Peterfalvi (1.5)(b): under the inertia hypothesis, induction from a
normal subgroup takes an irreducible character to an irreducible character. -/
theorem inertia_Ind_irr [CharZero K] [IsAlgClosed K]
    (S : Subgroup Γ) [S.Normal] [Fintype S]
    [Invertible (Nat.card S : K)] (chi : IrreducibleCharacter S K)
    (hI : inertia S (chi : ClassFunction S K) ≤ S) :
    IsIrreducibleCharacter Γ K
      (induce S (chi : ClassFunction S K)) := by
  let V := chi.representation
  letI : CategoryTheory.Simple V := chi.representation_simple
  let W : FDRep K Γ := FDRep.induceFromSubgroup S V
  have hcompat :
      ofRepresentation W.ρ = induce S (ofRepresentation V.ρ) :=
    ofRepresentation_induceFromSubgroup S V
  have hrealV : ofRepresentation V.ρ = (chi : ClassFunction S K) :=
    chi.ofRepresentation_representation
  have htarget :
      ofRepresentation W.ρ = induce S (chi : ClassFunction S K) :=
    hcompat.trans (congrArg (induce S) hrealV)
  have hpair := inertia_Ind_norm_one S chi hI
  have hpairW :
      characterPairing (ofRepresentation W.ρ) (ofRepresentation W.ρ) = 1 := by
    simpa only [htarget] using hpair
  have hsum :
      ∑ g : Γ, W.character g * W.character g⁻¹ = Nat.card Γ := by
    change (Nat.card Γ : K)⁻¹ *
      (∑ g : Γ, W.character g * W.character g⁻¹) = 1 at hpairW
    rw [inv_mul_eq_iff_eq_mul₀ (Nat.cast_ne_zero.mpr Nat.card_pos.ne')] at hpairW
    simpa using hpairW
  have hsimple : CategoryTheory.Simple W :=
    (FDRep.simple_iff_char_is_norm_one W).mpr hsum
  exact ⟨W, hsimple, htarget⟩

end ClassFunction

end

end Submission.OddOrder.PF
