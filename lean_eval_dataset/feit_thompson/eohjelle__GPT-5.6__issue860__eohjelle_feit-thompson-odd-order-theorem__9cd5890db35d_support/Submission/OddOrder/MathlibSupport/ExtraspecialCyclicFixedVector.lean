import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Submission.OddOrder.MathlibSupport.Cardinality
import Submission.OddOrder.MathlibSupport.CentralizerConjugationOrbitCount
import Submission.OddOrder.MathlibSupport.CyclicOrbitConjugationRankDrop
import Submission.OddOrder.MathlibSupport.CyclicRepresentationQuasiHomocyclic
import Submission.OddOrder.MathlibSupport.ExtraspecialIrreducibleDegreeNonmodular
import Submission.OddOrder.MathlibSupport.FixedPointFreeCyclicOrbitRepresentatives
import Submission.OddOrder.MathlibSupport.PrimeOrderCentralizer

/-!
The extraspecial fixed-vector theorem underlying Bender-Glauberman Section 2.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped IsMulCommutative

universe u v w

variable {k : Type u} {A : Type v} {V : Type w}
variable [Field k] [IsAlgClosed k] [Group A] [Finite A]
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]

noncomputable section

/-- A faithful irreducible representation of an extraspecial normal factor
cannot be fixed-point-free on an odd prime-order complement. This is the
representation-theoretic core of `BGsection2.v: repr_clP`. -/
theorem extraspecial_prime_action_invariants_ne_bot
    {P H : Subgroup A} {p : ℕ}
    (hp : p.Prime) (hpP : IsPGroup p P) (hP : IsExtraspecial P)
    (hHprime : (Nat.card H).Prime)
    (hHP : H ≤ Subgroup.normalizer P)
    (hcop : (Nat.card P).Coprime (Nat.card H))
    (hodd : Odd (Nat.card A))
    (hcardA : (Nat.card A : k) ≠ 0)
    (hmapCenter : (Subgroup.center P).map P.subtype ≤ Subgroup.center A)
    (hcentralizer : centralizerWithin P H =
      (Subgroup.center P).map P.subtype)
    (rho : Representation k A V)
    [Representation.IsIrreducible (rho.comp P.subtype)]
    (hrhoP : Function.Injective (rho.comp P.subtype)) :
    Representation.invariants (rho.comp H.subtype) ≠ ⊥ := by
  classical
  intro hfix
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fact (Nat.card H).Prime := ⟨hHprime⟩
  letI : IsCyclic H := isCyclic_of_prime_card rfl
  letI : Nontrivial P := hP.nontrivial
  letI : Nontrivial V := by
    by_contra hV
    haveI : Subsingleton V := not_nontrivial_iff_subsingleton.mp hV
    have hsubP : Subsingleton P := hrhoP.subsingleton
    exact not_subsingleton_iff_nontrivial.mpr inferInstance hsubP

  have hcardP : (Nat.card P : k) ≠ 0 := by
    intro hzero
    apply hcardA
    rw [← P.card_mul_index, Nat.cast_mul, hzero, zero_mul]
  have hcardH : (Nat.card H : k) ≠ 0 := by
    intro hzero
    apply hcardA
    rw [← H.card_mul_index, Nat.cast_mul, hzero, zero_mul]
  letI : NeZero (Nat.card H) := ⟨hHprime.ne_zero⟩
  letI : NeZero (Nat.card H : k) := ⟨hcardH⟩

  have hcenter : H ≤ Subgroup.centralizer (centerWithin P : Set A) := by
    intro h hh
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hzA : z ∈ Subgroup.center A := by
      apply hmapCenter
      rw [map_center_eq_centerWithin P]
      exact hz
    exact (Subgroup.mem_center_iff.mp hzA (h : A)).symm
  have hcentralizerZpowers : ∀ h : H, h ≠ 1 ->
      centralizerWithin P (Subgroup.zpowers (h : A)) = centerWithin P := by
    intro h hh
    have hhA : (h : A) ≠ 1 := by
      intro heq
      apply hh
      exact Subtype.ext heq
    rw [centralizerWithin_zpowers_eq_of_mem_prime_card P H hHprime
      h.property hhA, hcentralizer, map_center_eq_centerWithin]

  letI := subgroupConjugationAction P H hHP
  letI := subgroupConjugationCenterQuotientAction P H hHP
  let Q := P ⧸ Subgroup.center P
  let J := nonidentityFixedOneOrbitQuotient (G := H) (X := Q)
  letI : Fintype J := Fintype.ofFinite J
  let e : Multiplicative (ZMod (Nat.card H)) ≃* H :=
    zmodCyclicMulEquiv (inferInstance : IsCyclic H)
  have hfixedQ : ∀ h : H, h ≠ 1 -> ∀ q : Q,
      h • q = q -> q = 1 :=
    centerQuotient_fixed_eq_one_of_centralizers P H hHP hcop hcenter
      hcentralizerZpowers
  have honeQ : ∀ h : H, h • (1 : Q) = 1 := by
    intro h
    change h • ((1 : P) : Q) = ((1 : P) : Q)
    rw [MulAction.Quotient.smul_coe]
    simp

  let orbitClass (j : J) (t : ZMod (Nat.card H)) : Q :=
    fixedPointFreeCyclicOrbitRepresentative e j t
  let orbitElement (j : J) (t : ZMod (Nat.card H)) : P :=
    e (Multiplicative.ofAdd t) • centerQuotientRepresentative j.1.out
  let rhoP : Representation k P V := rho.comp P.subtype
  let orbit (j : J) (t : ZMod (Nat.card H)) : Module.End k V :=
    rhoP (orbitElement j t)

  have horbitMk (j : J) (t : ZMod (Nat.card H)) :
      QuotientGroup.mk' (Subgroup.center P) (orbitElement j t) =
        orbitClass j t := by
    change ((e (Multiplicative.ofAdd t) •
        centerQuotientRepresentative j.1.out : P) : Q) =
      e (Multiplicative.ofAdd t) • j.1.out
    calc
      ((e (Multiplicative.ofAdd t) •
          centerQuotientRepresentative j.1.out : P) : Q) =
          e (Multiplicative.ofAdd t) •
            (centerQuotientRepresentative (G := P) j.1.out : Q) :=
        (MulAction.Quotient.smul_coe (H := Subgroup.center P)
          (e (Multiplicative.ofAdd t))
          (centerQuotientRepresentative (G := P) j.1.out)).symm
      _ = e (Multiplicative.ofAdd t) • j.1.out :=
        congrArg (fun q : Q ↦ e (Multiplicative.ofAdd t) • q)
          (centerQuotientRepresentative_mk (G := P) j.1.out)
  have horbitClassInjective : Function.Injective
      (fun jt : J × ZMod (Nat.card H) ↦ orbitClass jt.1 jt.2) :=
    fixedPointFreeCyclicOrbitRepresentative_injective e hfixedQ

  let fullElement : Option (J × ZMod (Nat.card H)) → P
    | none => 1
    | some jt => orbitElement jt.1 jt.2
  have hfullMk (o : Option (J × ZMod (Nat.card H))) :
      QuotientGroup.mk' (Subgroup.center P) (fullElement o) =
        match o with
        | none => 1
        | some jt => orbitClass jt.1 jt.2 := by
    cases o with
    | none => simp [fullElement]
    | some jt => exact horbitMk jt.1 jt.2
  have hfullClassInjective : Function.Injective
      (fun o : Option (J × ZMod (Nat.card H)) ↦
        QuotientGroup.mk' (Subgroup.center P) (fullElement o)) := by
    intro x y hxy
    cases x with
    | none =>
        cases y with
        | none => rfl
        | some jt =>
            exfalso
            apply fixedPointFreeCyclicOrbitRepresentative_ne_one e honeQ
              jt.1 jt.2
            change orbitClass jt.1 jt.2 = 1
            exact (hfullMk (some jt)).symm.trans
              (hxy.symm.trans (hfullMk none))
    | some jt =>
        cases y with
        | none =>
            exfalso
            apply fixedPointFreeCyclicOrbitRepresentative_ne_one e honeQ
              jt.1 jt.2
            change orbitClass jt.1 jt.2 = 1
            exact (hfullMk (some jt)).symm.trans
              (hxy.trans (hfullMk none))
        | some jt' =>
            apply congrArg some
            apply horbitClassInjective
            exact (hfullMk (some jt)).symm.trans
              (hxy.trans (hfullMk (some jt')))
  have hfullLI : LinearIndependent k
      (fun o : Option (J × ZMod (Nat.card H)) ↦ rhoP (fullElement o)) :=
    hP.representationEnd_linearIndependent_of_quotient_injective hpP rhoP
      hrhoP hcardP fullElement hfullClassInjective
  have horbitLI : LinearIndependent k
      (fun jt : J × ZMod (Nat.card H) ↦ orbit jt.1 jt.2) := by
    change LinearIndependent k
      ((fun o : Option (J × ZMod (Nat.card H)) ↦ rhoP (fullElement o)) ∘
        fun jt : J × ZMod (Nat.card H) ↦ some jt)
    exact hfullLI.comp (fun jt : J × ZMod (Nat.card H) ↦ some jt)
      (Option.some_injective _)

  have honeNotOrbitSpan : (1 : Module.End k V) ∉
      Submodule.span k
        (Set.range (fun jt : J × ZMod (Nat.card H) ↦ orbit jt.1 jt.2)) := by
    have hnone : (none : Option (J × ZMod (Nat.card H))) ∉
        Set.range (fun jt : J × ZMod (Nat.card H) ↦ some jt) := by simp
    have hnot := hfullLI.notMem_span_image hnone
    have himage :
        (fun o : Option (J × ZMod (Nat.card H)) ↦ rhoP (fullElement o)) ''
            Set.range (fun jt : J × ZMod (Nat.card H) ↦ some jt) =
          Set.range (fun jt : J × ZMod (Nat.card H) ↦ orbit jt.1 jt.2) := by
      ext T
      simp [orbit, fullElement]
    rw [himage] at hnot
    simpa [fullElement] using hnot

  have hcount : Nat.card Q =
      1 + Nat.card J * Nat.card H := by
    simpa [Q, J] using
      natCard_centerQuotient_eq_one_add_orbits_mul_natCard_of_centralizers
        P H hHP hcop hcenter hcentralizerZpowers
  have hend : Module.finrank k (Module.End k V) = Nat.card Q := by
    simpa [rhoP, Q] using
      hP.faithful_irreducible_finrank_end_eq_quotient_center_card
        hpP rhoP hrhoP hcardP
  have hambient : Module.finrank k (Module.End k V) =
      Nat.card H * Fintype.card J + 1 := by
    rw [hend, hcount]
    simp only [Nat.card_eq_fintype_card]
    ac_rfl
  have hfullSpanTop :
      Submodule.span k
          (Set.range (fun o : Option (J × ZMod (Nat.card H)) ↦
            rhoP (fullElement o))) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_span_eq_card hfullLI, hambient]
    simp [Nat.card_eq_fintype_card, Nat.mul_comm]
  have hspan :
      endomorphismScalarLine (k := k) (V := V) ⊔
          Submodule.span k
            (Set.range (fun jt : J × ZMod (Nat.card H) ↦
              orbit jt.1 jt.2)) = ⊤ := by
    apply top_unique
    rw [← hfullSpanTop, Submodule.span_le]
    rintro T ⟨o, rfl⟩
    cases o with
    | none =>
        have hone : (1 : Module.End k V) ∈
            endomorphismScalarLine (k := k) (V := V) := by
          exact Submodule.mem_span_singleton_self 1
        simpa [fullElement] using
          (show (1 : Module.End k V) ∈
              endomorphismScalarLine (k := k) (V := V) ⊔ _ from
            (le_sup_left : endomorphismScalarLine (k := k) (V := V) ≤ _) hone)
    | some jt =>
        apply (le_sup_right :
          Submodule.span k
            (Set.range (fun jt : J × ZMod (Nat.card H) ↦
              orbit jt.1 jt.2)) ≤ _)
        exact Submodule.subset_span ⟨jt, by simp [orbit, fullElement]⟩

  obtain ⟨omegaVal, homegaVal⟩ :=
    HasEnoughRootsOfUnity.exists_primitiveRoot k (Nat.card H)
  let omega : kˣ := (homegaVal.isUnit (NeZero.ne (Nat.card H))).unit
  have homega : IsPrimitiveRoot omega (Nat.card H) :=
    homegaVal.isUnit_unit (NeZero.ne (Nat.card H))
  have honeNotBlock : (1 : Module.End k V) ∉
      indexedWeightBlock (k := k)
        (cyclicOrbitFourierFamily homega orbit) 0 := by
    intro hone
    apply honeNotOrbitSpan
    apply (show indexedWeightBlock (k := k)
        (cyclicOrbitFourierFamily homega orbit) 0 ≤
          Submodule.span k
            (Set.range (fun jt : J × ZMod (Nat.card H) ↦
              orbit jt.1 jt.2)) from ?_) hone
    rw [indexedWeightBlock, Submodule.span_le]
    rintro T ⟨j, rfl⟩
    unfold cyclicOrbitFourierFamily
    exact Submodule.sum_mem _ fun t _ ↦
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨(j, t), rfl⟩)

  let z : H := e (Multiplicative.ofAdd (-1 : ZMod (Nat.card H)))
  have hzne : z ≠ 1 := by
    intro hz
    have he : e (Multiplicative.ofAdd (-1 : ZMod (Nat.card H))) =
        e 1 := by simpa [z] using hz
    have he' := e.injective he
    have hadd : (-1 : ZMod (Nat.card H)) = 0 := by
      exact Multiplicative.ofAdd.injective (by simpa using he')
    have : (1 : ZMod (Nat.card H)) = 0 := by simpa using congrArg Neg.neg hadd
    exact one_ne_zero this
  have hzpowers : Subgroup.zpowers z = ⊤ :=
    zpowers_eq_top_of_prime_card rfl hzne
  have hzgen : ∀ x : H, x ∈ Subgroup.zpowers z := by
    intro x
    rw [hzpowers]
    trivial
  have hzpow : z ^ Nat.card H = 1 := pow_card_eq_one'
  have horbitShift (j : J) (t : ZMod (Nat.card H)) :
      z⁻¹ • orbitElement j t = orbitElement j (t + 1) := by
    simp [z, orbitElement, ← mul_smul, ← map_mul, mul_comm]
  have hshift (j : J) (t : ZMod (Nat.card H)) :
      linearEquivConjugation
          (representationLinearEquiv (rho.comp H.subtype) z) (orbit j t) =
        orbit j (t + 1) := by
    rw [linearEquivConjugation_representationLinearEquiv]
    rw [endomorphismConjugationRepresentation_apply]
    change rho (z⁻¹ : H) * rho (orbitElement j t : P) *
        rho ((z⁻¹)⁻¹ : H) = rho (orbitElement j (t + 1) : P)
    rw [inv_inv]
    change rho (z⁻¹ : H) * rho (orbitElement j t : P) * rho (z : H) =
      rho (orbitElement j (t + 1) : P)
    rw [← rho.map_mul, ← rho.map_mul]
    apply congrArg rho
    have hshiftA := congrArg Subtype.val (horbitShift j t)
    simpa [rhoP, coe_subgroupConjugationAction_smul P H hHP] using hshiftA
  have hdrop := primitiveRoot_conjugation_rank_drop_of_cyclic_orbits
    homega (representationLinearEquiv (rho.comp H.subtype) z) orbit
    horbitLI hshift honeNotBlock hspan hambient

  have hrankZero : Module.finrank k
      (Module.End.eigenspace ((rho.comp H.subtype) z)
        (primitiveRootUnitWeight homega 0 : k)) = 0 := by
    have hweight : (primitiveRootUnitWeight homega 0 : k) = 1 := by simp
    rw [hweight, ← invariants_eq_eigenspace_one_of_forall_mem_zpowers
      (rho.comp H.subtype) z hzgen, hfix]
    simp
  have hsquare : Module.finrank k V ^ 2 = Nat.card Q := by
    simpa [rhoP, Q] using
      hP.faithful_irreducible_finrank_sq_eq_quotient_center_card_of_card_ne_zero
        hpP rhoP hrhoP hcardP
  have hdim : 1 < Module.finrank k V := by
    have hquotient : 1 < Nat.card Q :=
      Finite.one_lt_card_iff_nontrivial.mpr hP.quotient_center_nontrivial
    nlinarith
  obtain ⟨horder, _⟩ := cyclicRepresentation_free_quasiHomocyclic_rank_profile
    homega (rho.comp H.subtype) z hzpow hrankZero hdim hdrop

  have hoddH : Odd (Nat.card H) := odd_natCard_subgroup H hodd
  have hoddQ : Odd (Nat.card Q) := by
    simpa [Q] using odd_natCard_quotient (Subgroup.center P)
      (odd_natCard_subgroup P hodd)
  have hoddDim : Odd (Module.finrank k V) := by
    rw [← Nat.odd_pow_iff (by omega : 2 ≠ 0), hsquare]
    exact hoddQ
  exact (Nat.not_even_iff_odd.mpr hoddH) (horder ▸ hoddDim.add_one)

end

end Submission.OddOrder.MathlibSupport
