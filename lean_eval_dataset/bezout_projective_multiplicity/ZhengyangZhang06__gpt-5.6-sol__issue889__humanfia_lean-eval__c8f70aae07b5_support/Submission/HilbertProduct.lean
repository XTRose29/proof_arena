import Submission.RegularGenerators
import Mathlib.RingTheory.PowerSeries.WellKnown

open MvPolynomial RingTheory.Sequence
open scoped Pointwise

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type*} [Field K]

namespace Submission.Helpers

noncomputable instance homogeneousPiece_moduleFinite {σ : Type*} [Finite σ] (m : ℕ) :
    Module.Finite K (HomogeneousPiece (K := K) (σ := σ) m) :=
  Module.Finite.equiv (homogeneousPieceEquivDegreeFinsupp (K := K) m).symm

lemma idealOfList_isHomogeneous {σ : Type*}
    {rs : List (MvPolynomial σ K)}
    (hrs : ∀ g ∈ rs, ∃ e, g.IsHomogeneous e) :
    (Ideal.ofList rs).IsHomogeneous (homogeneousSubmodule σ K) := by
  apply Ideal.homogeneous_span
  intro g hg
  obtain ⟨e, he⟩ := hrs g hg
  exact ⟨e, he⟩

lemma homogeneousComponent_mem_of_isHomogeneousIdeal {σ : Type*}
    {I : Ideal (MvPolynomial σ K)}
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K))
    {p : MvPolynomial σ K} (hp : p ∈ I) (m : ℕ) :
    homogeneousComponent m p ∈ I := by
  have h := hI m hp
  rw [← MvPolynomial.decomposition.decompose'_apply p m]
  exact h

lemma homogeneousComponent_mul_right_of_le {σ : Type*}
    {g q : MvPolynomial σ K} {d m : ℕ} (hg : g.IsHomogeneous d)
    (hdm : d ≤ m) :
    homogeneousComponent m (q * g) = homogeneousComponent (m - d) q * g := by
  rw [← MvPolynomial.decomposition.decompose'_apply (q * g) m,
    ← MvPolynomial.decomposition.decompose'_apply q (m - d)]
  exact DirectSum.coe_decompose_mul_of_right_mem_of_le
    (homogeneousSubmodule σ K) (a := q) (b := g) hg hdm

lemma homogeneousComponent_mul_right_of_not_le {σ : Type*}
    {g q : MvPolynomial σ K} {d m : ℕ} (hg : g.IsHomogeneous d)
    (hdm : ¬d ≤ m) : homogeneousComponent m (q * g) = 0 := by
  rw [← MvPolynomial.decomposition.decompose'_apply (q * g) m]
  exact DirectSum.coe_decompose_mul_of_right_mem_of_not_le
    (homogeneousSubmodule σ K) (a := q) (b := g) hg hdm

lemma range_homogeneousMulQuotient_eq_ker_factor {σ : Type*}
    (I : Ideal (MvPolynomial σ K)) (g : MvPolynomial σ K) (d m : ℕ)
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K))
    (hg : g.IsHomogeneous d) (hdm : d ≤ m) :
    LinearMap.range (homogeneousMulQuotient I g d m hg hdm) =
      LinearMap.ker
        (homogeneousQuotientFactor
          (show I ≤ I ⊔ Ideal.span {g} from le_sup_left) m) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    induction x using Submodule.Quotient.induction_on with
    | _ p =>
        rw [LinearMap.mem_ker, homogeneousMulQuotient_apply,
          homogeneousQuotientFactor_apply, Submodule.Quotient.mk_eq_zero]
        change g * p.1 ∈ I ⊔ Ideal.span {g}
        apply (show Ideal.span {g} ≤ I ⊔ Ideal.span {g} from le_sup_right)
        simpa [mul_comm] using
          (Ideal.span {g}).mul_mem_left p.1 (Ideal.mem_span_singleton_self g)
  · intro x hx
    induction x using Submodule.Quotient.induction_on with
    | _ p =>
        rw [LinearMap.mem_ker, homogeneousQuotientFactor_apply,
          Submodule.Quotient.mk_eq_zero] at hx
        change p.1 ∈ I ⊔ Ideal.span {g} at hx
        obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hx
        obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.mp hb
        let qh : HomogeneousPiece (K := K) (m - d) :=
          ⟨homogeneousComponent (m - d) q, homogeneousComponent_isHomogeneous _ _⟩
        refine ⟨Submodule.Quotient.mk qh, ?_⟩
        rw [homogeneousMulQuotient_apply]
        apply (Submodule.Quotient.eq' (homogeneousIdealPart I m)).2
        have hacomp : homogeneousComponent m a ∈ I :=
          homogeneousComponent_mem_of_isHomogeneousIdeal hI ha m
        have hpcomp : homogeneousComponent m a + homogeneousComponent m (q * g) = p.1 := by
          calc
            _ = homogeneousComponent m p.1 := by
              rw [← map_add, hab]
            _ = p.1 := by
              rw [homogeneousComponent_of_mem p.2, if_pos rfl]
        have hqcomp : homogeneousComponent m (q * g) =
            g * homogeneousComponent (m - d) q := by
          rw [homogeneousComponent_mul_right_of_le hg hdm, mul_comm]
        change -(g * homogeneousComponent (m - d) q) + p.1 ∈ I
        rw [← hpcomp, hqcomp]
        simpa [add_assoc] using hacomp

lemma homogeneousQuotientFactor_injective_of_not_le {σ : Type*}
    (I : Ideal (MvPolynomial σ K)) (g : MvPolynomial σ K) (d m : ℕ)
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K))
    (hg : g.IsHomogeneous d) (hdm : ¬d ≤ m) :
    Function.Injective
      (homogeneousQuotientFactor
        (show I ≤ I ⊔ Ideal.span {g} from le_sup_left) m) := by
  rw [← LinearMap.ker_eq_bot]
  apply le_antisymm
  · intro x hx
    induction x using Submodule.Quotient.induction_on with
    | _ p =>
        rw [LinearMap.mem_ker, homogeneousQuotientFactor_apply,
          Submodule.Quotient.mk_eq_zero] at hx
        rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
        change p.1 ∈ I ⊔ Ideal.span {g} at hx
        obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hx
        obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.mp hb
        have hacomp : homogeneousComponent m a ∈ I :=
          homogeneousComponent_mem_of_isHomogeneousIdeal hI ha m
        have hpcomp : homogeneousComponent m a + homogeneousComponent m (q * g) = p.1 := by
          calc
            _ = homogeneousComponent m p.1 := by
              rw [← map_add, hab]
            _ = p.1 := by
              rw [homogeneousComponent_of_mem p.2, if_pos rfl]
        rw [homogeneousComponent_mul_right_of_not_le hg hdm, add_zero] at hpcomp
        change p.1 ∈ I
        rwa [← hpcomp]
  · exact bot_le

set_option maxHeartbeats 800000 in
lemma finrank_shift_add_finrank_sup_span {σ : Type*} [Finite σ]
    (I : Ideal (MvPolynomial σ K)) (g : MvPolynomial σ K) (d m : ℕ)
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K))
    (hg : g.IsHomogeneous d) (hdm : d ≤ m) (hreg : RegularModIdeal I g) :
    Module.finrank K (HomogeneousQuotientPiece I (m - d)) +
      Module.finrank K (HomogeneousQuotientPiece (I ⊔ Ideal.span {g}) m) =
        Module.finrank K (HomogeneousQuotientPiece I m) := by
  let mul := homogeneousMulQuotient I g d m hg hdm
  let fac := homogeneousQuotientFactor
    (show I ≤ I ⊔ Ideal.span {g} from le_sup_left) m
  have hinj : Function.Injective mul :=
    homogeneousMulQuotient_injective I g d m hg hdm hreg
  have hsurj : Function.Surjective fac :=
    homogeneousQuotientFactor_surjective
      (show I ≤ I ⊔ Ideal.span {g} from le_sup_left) m
  have hker : LinearMap.range mul = LinearMap.ker fac :=
    range_homogeneousMulQuotient_eq_ker_factor I g d m hI hg hdm
  have hrank := fac.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsurj, ← hker] at hrank
  have hmulrank := (LinearEquiv.ofInjective mul hinj).finrank_eq
  simpa [mul, fac, add_comm, hmulrank] using hrank

set_option maxHeartbeats 800000 in
lemma finrank_sup_span_eq_of_not_le {σ : Type*} [Finite σ]
    (I : Ideal (MvPolynomial σ K)) (g : MvPolynomial σ K) (d m : ℕ)
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K))
    (hg : g.IsHomogeneous d) (hdm : ¬d ≤ m) :
    Module.finrank K (HomogeneousQuotientPiece (I ⊔ Ideal.span {g}) m) =
      Module.finrank K (HomogeneousQuotientPiece I m) := by
  let fac := homogeneousQuotientFactor
    (show I ≤ I ⊔ Ideal.span {g} from le_sup_left) m
  have hinj : Function.Injective fac :=
    homogeneousQuotientFactor_injective_of_not_le I g d m hI hg hdm
  have hsurj : Function.Surjective fac :=
    homogeneousQuotientFactor_surjective
      (show I ≤ I ⊔ Ideal.span {g} from le_sup_left) m
  exact (LinearEquiv.ofBijective fac ⟨hinj, hsurj⟩).finrank_eq.symm

noncomputable def homogeneousQuotientHilbertSeries {σ : Type*} [Finite σ]
    (I : Ideal (MvPolynomial σ K)) : PowerSeries ℤ :=
  PowerSeries.mk fun m ↦ (Module.finrank K (HomogeneousQuotientPiece I m) : ℤ)

lemma homogeneousQuotientHilbertSeries_sup_span {σ : Type*} [Finite σ]
    (I : Ideal (MvPolynomial σ K)) (g : MvPolynomial σ K) (d : ℕ)
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K))
    (hg : g.IsHomogeneous d) (hreg : RegularModIdeal I g) :
    homogeneousQuotientHilbertSeries (I ⊔ Ideal.span {g}) =
      (1 - PowerSeries.X ^ d) * homogeneousQuotientHilbertSeries I := by
  apply PowerSeries.ext
  intro m
  simp only [sub_mul, one_mul, map_sub, PowerSeries.coeff_X_pow_mul',
    homogeneousQuotientHilbertSeries, PowerSeries.coeff_mk]
  by_cases hdm : d ≤ m
  · simp only [hdm, if_true]
    have hrank := finrank_shift_add_finrank_sup_span I g d m hI hg hdm hreg
    omega
  · simp only [hdm, if_false, sub_zero]
    exact_mod_cast finrank_sup_span_eq_of_not_le I g d m hI hg hdm

lemma regularModIdeal_get_of_isRegular {σ : Type*}
    {rs : List (MvPolynomial σ K)} (hreg : IsRegular (MvPolynomial σ K) rs)
    (i : Fin rs.length) :
    RegularModIdeal (Ideal.ofList (rs.take i.1)) (rs.get i) := by
  have h := hreg.toIsWeaklyRegular.regular_mod_prev i.1 i.2
  rw [isSMulRegular_quotient_iff_mem_of_smul_mem] at h
  have hsmul : Ideal.ofList (rs.take i.1) •
      (⊤ : Submodule (MvPolynomial σ K) (MvPolynomial σ K)) =
      (Ideal.ofList (rs.take i.1) :
        Submodule (MvPolynomial σ K) (MvPolynomial σ K)) := by
    simp
  rw [hsmul] at h
  intro p hp
  apply h p
  simpa [smul_eq_mul] using hp

lemma idealOfList_take_isHomogeneous {σ : Type*}
    {rs : List (MvPolynomial σ K)} {es : List ℕ}
    (hhom : List.Forall₂ (fun g e ↦ g.IsHomogeneous e) rs es) (i : ℕ) :
    (Ideal.ofList (rs.take i)).IsHomogeneous (homogeneousSubmodule σ K) := by
  apply idealOfList_isHomogeneous
  intro g hg
  have hg' : g ∈ rs := List.mem_of_mem_take hg
  rw [List.mem_iff_getElem] at hg'
  obtain ⟨j, hj, hgj⟩ := hg'
  have hj' : j < es.length := by simpa [← hhom.length_eq] using hj
  refine ⟨es[j], ?_⟩
  rw [← hgj]
  exact hhom.get hj hj'

noncomputable def hilbertFactor (d : ℕ) : PowerSeries ℤ :=
  1 - PowerSeries.X ^ d

set_option maxHeartbeats 800000 in
lemma homogeneousQuotientHilbertSeries_take {σ : Type*} [Finite σ]
    (rs : List (MvPolynomial σ K)) (es : List ℕ)
    (hhom : List.Forall₂ (fun g e ↦ g.IsHomogeneous e) rs es)
    (hreg : IsRegular (MvPolynomial σ K) rs) (i : ℕ) (hi : i ≤ rs.length) :
    homogeneousQuotientHilbertSeries (Ideal.ofList (rs.take i)) =
      ((es.take i).map hilbertFactor).prod *
        homogeneousQuotientHilbertSeries (⊥ : Ideal (MvPolynomial σ K)) := by
  induction i with
  | zero => simp
  | succ i ih =>
      have hir : i < rs.length := Nat.lt_of_succ_le hi
      have hie : i < es.length := by simpa [← hhom.length_eq] using hir
      let g := rs[i]
      let d := es[i]
      have hg : g.IsHomogeneous d := hhom.get hir hie
      have hI : (Ideal.ofList (rs.take i)).IsHomogeneous
          (homogeneousSubmodule σ K) := idealOfList_take_isHomogeneous hhom i
      have hregular : RegularModIdeal (Ideal.ofList (rs.take i)) g :=
        regularModIdeal_get_of_isRegular hreg ⟨i, hir⟩
      have hstep := homogeneousQuotientHilbertSeries_sup_span
        (Ideal.ofList (rs.take i)) g d hI hg hregular
      have htakeR : rs.take (i + 1) = rs.take i ++ [g] := by
        rw [← List.take_concat_get (l := rs) hir]
        rw [List.concat_eq_append]
      have htakeE : es.take (i + 1) = es.take i ++ [d] := by
        rw [← List.take_concat_get (l := es) hie]
        rw [List.concat_eq_append]
      rw [htakeR, Ideal.ofList_append, Ideal.ofList_singleton, hstep, ih hir.le]
      rw [htakeE, List.map_append, List.prod_append]
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      simp [hilbertFactor, mul_assoc, mul_left_comm]

lemma homogeneousQuotientHilbertSeries_of_regular {σ : Type*} [Finite σ]
    (rs : List (MvPolynomial σ K)) (es : List ℕ)
    (hhom : List.Forall₂ (fun g e ↦ g.IsHomogeneous e) rs es)
    (hreg : IsRegular (MvPolynomial σ K) rs) :
    homogeneousQuotientHilbertSeries (Ideal.ofList rs) =
      (es.map hilbertFactor).prod *
        homogeneousQuotientHilbertSeries (⊥ : Ideal (MvPolynomial σ K)) := by
  have h := homogeneousQuotientHilbertSeries_take rs es hhom hreg rs.length le_rfl
  rw [List.take_length] at h
  have hes : es.take rs.length = es := by
    rw [hhom.length_eq, List.take_length]
  rw [hes] at h
  exact h

lemma homogeneousIdealPart_idealOfVars_zero_eq_bot {σ : Type*} :
    homogeneousIdealPart (idealOfVars σ K) 0 = ⊥ := by
  apply le_antisymm
  · intro p hp
    rw [Submodule.mem_bot]
    apply Subtype.ext
    change p.1 = 0
    have hcomp : homogeneousComponent 0 p.1 = p.1 := by
      rw [homogeneousComponent_of_mem p.2, if_pos rfl]
    have hpC : p.1 = C (coeff 0 p.1) := by
      calc
        p.1 = homogeneousComponent 0 p.1 := hcomp.symm
        _ = C (coeff 0 p.1) := homogeneousComponent_zero p.1
    have hCmem : C (coeff 0 p.1) ∈ idealOfVars σ K := by
      rwa [← hpC]
    have hc : coeff 0 p.1 = 0 := by
      have := (C_mem_pow_idealOfVars_iff (σ := σ) 1 (coeff 0 p.1)).mp
        (by simpa only [pow_one] using hCmem)
      simpa using this
    rw [hpC, hc, C_0]
  · exact bot_le

lemma homogeneousIdealPart_idealOfVars_eq_top_of_pos {σ : Type*}
    {m : ℕ} (hm : 0 < m) : homogeneousIdealPart (idealOfVars σ K) m = ⊤ := by
  apply top_unique
  intro p _
  exact homogeneous_mem_idealOfVars p.2 hm

lemma finrank_homogeneousQuotientPiece_idealOfVars {σ : Type*} [Fintype σ]
    (m : ℕ) :
    Module.finrank K (HomogeneousQuotientPiece (idealOfVars σ K) m) =
      if m = 0 then 1 else 0 := by
  by_cases hm : m = 0
  · subst m
    let e : HomogeneousQuotientPiece (idealOfVars σ K) 0 ≃ₗ[K]
        HomogeneousPiece (K := K) (σ := σ) 0 :=
      Submodule.quotEquivOfEqBot _ homogeneousIdealPart_idealOfVars_zero_eq_bot
    calc
      Module.finrank K (HomogeneousQuotientPiece (idealOfVars σ K) 0) =
          Module.finrank K (HomogeneousPiece (K := K) (σ := σ) 0) := e.finrank_eq
      _ = 1 := by simp [homogeneousSubmodule_finrank]
      _ = if 0 = 0 then 1 else 0 := by simp
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    letI : Subsingleton (HomogeneousQuotientPiece (idealOfVars σ K) m) :=
      Submodule.Quotient.subsingleton_iff.mpr
        (homogeneousIdealPart_idealOfVars_eq_top_of_pos hmpos)
    rw [Module.finrank_zero_of_subsingleton]
    simp [hm]

lemma homogeneousQuotientHilbertSeries_idealOfVars {σ : Type*} [Fintype σ] :
    homogeneousQuotientHilbertSeries (idealOfVars σ K) = 1 := by
  apply PowerSeries.ext
  intro m
  rw [homogeneousQuotientHilbertSeries, PowerSeries.coeff_mk,
    finrank_homogeneousQuotientPiece_idealOfVars, PowerSeries.coeff_one]
  split_ifs <;> norm_num

lemma coordinateList_homogeneous (m : ℕ) :
    List.Forall₂ (fun g e ↦ g.IsHomogeneous e)
      (coordinateList (K := K) m) (List.replicate m 1) := by
  rw [List.forall₂_iff_get]
  refine ⟨by simp [coordinateList], ?_⟩
  intro i hi hj
  simp [coordinateList, isHomogeneous_X]

lemma one_sub_X_pow_card_mul_hilbertSeries_bot (m : ℕ) :
    (1 - PowerSeries.X) ^ m *
      homogeneousQuotientHilbertSeries
        (⊥ : Ideal (MvPolynomial (Fin m) K)) = 1 := by
  have h := homogeneousQuotientHilbertSeries_of_regular
    (coordinateList (K := K) m) (List.replicate m 1)
    (coordinateList_homogeneous (K := K) m) (coordinateList_isRegular (K := K) m)
  rw [ideal_of_coordinateList, homogeneousQuotientHilbertSeries_idealOfVars] at h
  simpa [hilbertFactor] using h.symm

end Submission.Helpers
