import Mathlib
namespace Submission

set_option maxHeartbeats 400000

open Polynomial IntermediateField
/-ResultDefinitionsBegin-/
/-ResultProofDefinitionsBegin-/
/-ResultProofDefinitionsEnd-/
/-ResultDefinitionsEnd-/

/-ResultBegin-/

theorem solvable_iff_solvableByRad (F : Type*) [Field F] [CharZero F]
    (p : F[X]) (_hp : p ≠ 0) :
    (∀ x : AlgebraicClosure F, aeval x p = 0 →
        x ∈ solvableByRad F (AlgebraicClosure F)) ↔ IsSolvable p.Gal :=
/-ResultProofBegin-/by
  classical
  constructor
  · intro hroots
    -- The direction supplied by Abel--Ruffini in Mathlib is stated for an
    -- irreducible polynomial.  We first record carefully how to pass from
    -- that version to an arbitrary polynomial.  This reduction uses no
    -- assumption about separability.
    have aux : ∀ n : ℕ, ∀ q : F[X], q.natDegree = n →
        (∀ x : AlgebraicClosure F, aeval x q = 0 →
          x ∈ solvableByRad F (AlgebraicClosure F)) →
        IsSolvable q.Gal := by
      intro n
      induction n using Nat.strong_induction_on with
      | h n ih =>
        intro q hqn hqroot
        by_cases hn : n = 0
        · have hqnd : q.natDegree = 0 := hqn.trans hn
          have hqC : q = C (q.coeff 0) :=
            Polynomial.eq_C_of_natDegree_eq_zero hqnd
          rw [hqC]
          exact gal_C_isSolvable _
        · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
          have hqpos : 0 < q.natDegree := by simpa [hqn] using hnpos
          have hq0 : q ≠ 0 := by
            intro h
            have : q.natDegree = 0 := by simp [h]
            exact (Nat.ne_of_gt hqpos) this
          have hqnu : ¬ IsUnit q := by
            intro hu
            have hd : q.degree = 0 :=
              (Polynomial.isUnit_iff_degree_eq_zero).1 hu
            have hdp : (0 : WithBot ℕ) < q.degree :=
              Polynomial.natDegree_pos_iff_degree_pos.mp hqpos
            rw [hd] at hdp
            exact (lt_irrefl (0 : WithBot ℕ)) hdp
          obtain ⟨s, hsirr, hsdiv⟩ :=
            WfDvdMonoid.exists_irreducible_factor hqnu hq0
          rcases hsdiv with ⟨t, hst⟩
          -- `s` really has positive degree; hence on cancelling it the
          -- quotient has strictly smaller degree.
          have hs0 : s ≠ (0 : F[X]) := hsirr.ne_zero
          have ht0 : t ≠ (0 : F[X]) := by
            intro ht
            have : q = 0 := by simpa [ht] using hst
            exact hq0 this
          have hdeg : s.natDegree + t.natDegree = n := by
            have h := hqn
            rw [hst, Polynomial.natDegree_mul hs0 ht0] at h
            exact h
          have hspos : 0 < s.natDegree :=
            Polynomial.natDegree_pos_iff_degree_pos.mpr
              (Polynomial.degree_pos_of_irreducible hsirr)
          have htlt : t.natDegree < n := by
            rw [← hdeg]
            exact Nat.lt_add_of_pos_left hspos
          have htroot : ∀ x : AlgebraicClosure F, aeval x t = 0 →
              x ∈ solvableByRad F (AlgebraicClosure F) := by
            intro x hx
            apply hqroot x
            rw [hst, Polynomial.aeval_mul, hx, mul_zero]
          have hts : IsSolvable t.Gal :=
            ih t.natDegree htlt t rfl htroot
          have hsroot : ∀ x : AlgebraicClosure F, aeval x s = 0 →
              x ∈ solvableByRad F (AlgebraicClosure F) := by
            intro x hx
            apply hqroot x
            rw [hst, Polynomial.aeval_mul, hx, zero_mul]
          -- An irreducible polynomial has a root in the algebraic closure;
          -- thus the hypothesis on *all* of our roots applies to this
          -- irreducible factor.
          have hsdeg : s.degree ≠ 0 :=
            ne_of_gt (Polynomial.degree_pos_of_irreducible hsirr)
          obtain ⟨x, hx⟩ :=
            IsAlgClosed.exists_aeval_eq_zero (AlgebraicClosure F) s hsdeg
          have hss : IsSolvable s.Gal :=
            isSolvable_gal_of_irreducible (hsroot x hx) hsirr hx
          rw [hst]
          exact gal_mul_isSolvable hss hts
    exact aux p.natDegree p rfl hroots
  · intro h
    -- Restricting the Galois group to a divisor is a surjection.  Thus for a
    -- root it is enough to understand the converse for its *minimal*
    -- irreducible polynomial.
    intro x hx
    letI : Algebra.IsAlgebraic F (AlgebraicClosure F) :=
      AlgebraicClosure.isAlgebraic F
    have hxint : IsIntegral F x :=
      Algebra.IsIntegral.isIntegral x
    have hd : minpoly F x ∣ p := minpoly.dvd F x hx
    have hmin : IsSolvable (minpoly F x).Gal := by
      letI : IsSolvable p.Gal := h
      exact solvable_of_surjective (Gal.restrictDvd_surjective hd _hp)
    -- The basic Kummer *cyclic* step works especially cleanly if we use
    -- the field `solvableByRad` as the base.  It already contains every
    -- primitive root of unity: a primitive root `ζ` in the algebraic
    -- closure satisfies `ζ ^ n = 1`, which is precisely one application
    -- of `solvableByRad.rad_mem`.  Consequently a finite cyclic Galois
    -- subextension of the algebraic closure over this field has no new
    -- elements.  Keeping this lemma in terms of intermediate fields avoids
    -- picking an abstract splitting field or any identifications.
    have cyclic_step
        (T : IntermediateField
          (↥(solvableByRad F (AlgebraicClosure F))) (AlgebraicClosure F))
        [FiniteDimensional
          (↥(solvableByRad F (AlgebraicClosure F))) (↥T)]
        [IsGalois
          (↥(solvableByRad F (AlgebraicClosure F))) (↥T)]
        [IsCyclic
          (Gal( (↥T) / (↥(solvableByRad F (AlgebraicClosure F)))))] :
        ∀ y : T, (y : AlgebraicClosure F) ∈
          solvableByRad F (AlgebraicClosure F) := by
      let S : IntermediateField F (AlgebraicClosure F) :=
        solvableByRad F (AlgebraicClosure F)
      change ∀ y : T, (y : AlgebraicClosure F) ∈ S
      -- Algebraic closures of a characteristic-zero field have primitive
      -- `n`th roots; they can all be regarded as elements of `S`.
      have rootsS (n : ℕ) (hn : n ≠ 0) :
          (primitiveRoots n (↥S)).Nonempty := by
        letI : NeZero (n : F) := ⟨by
          exact_mod_cast hn⟩
        obtain ⟨ζ, hζ⟩ :=
          HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure F) n
        have hζmem : ζ ∈ S := by
          change ζ ∈ solvableByRad F (AlgebraicClosure F)
          refine solvableByRad.rad_mem hn ?_
          rw [hζ.pow_eq_one]
          exact one_mem _
        let z : ↥S := ⟨ζ, hζmem⟩
        have hz : IsPrimitiveRoot z n := by
          constructor
          · apply Subtype.ext
            change ζ ^ n = 1
            exact hζ.pow_eq_one
          · intro l hl
            apply hζ.dvd_of_pow_eq_one l
            have hh := congrArg
              (fun a : ↥S => (a : AlgebraicClosure F)) hl
            exact hh
        exact ⟨z, (mem_primitiveRoots (Nat.pos_of_ne_zero hn)).2 hz⟩
      have hn : Module.finrank (↥S) (↥T) ≠ 0 :=
        ne_of_gt (Module.finrank_pos)
      obtain ⟨α, ha, htop⟩ :=
        exists_root_adjoin_eq_top_of_isCyclic (↥S) (↥T)
          (rootsS _ hn)
      obtain ⟨a, haeq⟩ := ha
      have hva : ((α : ↥T) : AlgebraicClosure F) ^
            (Module.finrank (↥S) (↥T)) =
            ((a : ↥S) : AlgebraicClosure F) := by
        have hh := congrArg (fun y : ↥T =>
          (y : AlgebraicClosure F)) haeq
        simpa using hh.symm
      have hαmem : ((α : ↥T) : AlgebraicClosure F) ∈ S := by
        change ((α : ↥T) : AlgebraicClosure F) ∈
          solvableByRad F (AlgebraicClosure F)
        refine solvableByRad.rad_mem hn ?_
        rw [hva]
        exact (a : ↥S).property
      have hαbot : α ∈ (⊥ : IntermediateField (↥S) (↥T)) := by
        rw [IntermediateField.mem_bot]
        let b : ↥S := ⟨((α : ↥T) : AlgebraicClosure F), hαmem⟩
        refine ⟨b, ?_⟩
        apply Subtype.ext
        rfl
      have hbot_top :
          (⊥ : IntermediateField (↥S) (↥T)) = ⊤ := by
        have hbot : (↥S)⟮α⟯ =
            (⊥ : IntermediateField (↥S) (↥T)) :=
          (IntermediateField.adjoin_simple_eq_bot_iff).2 hαbot
        exact hbot.symm.trans htop
      intro y
      have hybot : y ∈ (⊥ : IntermediateField (↥S) (↥T)) := by
        rw [hbot_top]
        trivial
      rw [IntermediateField.mem_bot] at hybot
      rcases hybot with ⟨b, hb⟩
      have hbval := congrArg (fun z : ↥T =>
        (z : AlgebraicClosure F)) hb
      have heq : (y : AlgebraicClosure F) =
          (b : AlgebraicClosure F) := by
        simpa using hbval.symm
      rw [heq]
      exact b.property
    -- Put all conjugates of `x` in a literal subfield of the fixed algebraic
    -- closure.  It is useful at this point not to use an abstract splitting
    -- field: then the compositum with `S` is quite literally an adjunction.
    let S : IntermediateField F (AlgebraicClosure F) :=
      solvableByRad F (AlgebraicClosure F)
    let q : F[X] := minpoly F x
    have hq0 : q ≠ 0 := minpoly.ne_zero hxint
    -- Changing the ground field from `F` to `S` does not change the roots in
    -- the common overfield.
    have hrs : (q.map (algebraMap F (↥S))).rootSet (AlgebraicClosure F) =
          q.rootSet (AlgebraicClosure F) := by
      ext z
      simp [Polynomial.mem_rootSet', q, Polynomial.map_map,
        IsScalarTower.algebraMap_eq F (↥S) (AlgebraicClosure F)]
    let qS : (↥S)[X] := q.map (algebraMap F (↥S))
    let T : IntermediateField (↥S) (AlgebraicClosure F) :=
      IntermediateField.adjoin (↥S) (qS.rootSet (AlgebraicClosure F))
    have hspl : (qS.map (algebraMap (↥S) (AlgebraicClosure F))).Splits :=
      IsAlgClosed.splits_codomain qS
    letI iTsplit : qS.IsSplittingField (↥S) (↥T) :=
      IntermediateField.adjoin_rootSet_isSplittingField hspl
    letI iTfin : FiniteDimensional (↥S) (↥T) :=
      Polynomial.IsSplittingField.finiteDimensional (↥T) qS
    have hsepS : qS.Separable := by
      dsimp [qS, q]
      exact (minpoly.irreducible hxint).separable.map
    letI iTgal : IsGalois (↥S) (↥T) :=
      IsGalois.of_separable_splitting_field (p := qS) hsepS
    -- The automorphisms of this compositum which fix `S` embed in the old
    -- polynomial Galois group.  This is the restriction-to-the-`F`-roots
    -- formulation of the usual base-change subgroup statement; using the
    -- polynomial restriction map avoids any choices of splitting fields.
    have hTsolv : IsSolvable Gal((↥T)/(↥S)) := by
      letI : IsSolvable q.Gal := by
        simpa [q] using hmin
      have hsplF : (q.map (algebraMap F (↥T))).Splits := by
        -- first split in the algebraic closure, then in the subfield containing
        -- every root
        have hE : (q.map (algebraMap F (AlgebraicClosure F))).Splits :=
          IsAlgClosed.splits_codomain q
        apply IntermediateField.splits_of_splits (F := T.restrictScalars F) hE
        intro z hz
        change z ∈ T
        -- the two root sets in the algebraic closure are identical
        have hz' : z ∈ qS.rootSet (AlgebraicClosure F) := by
          rw [hrs]
          exact hz
        exact IntermediateField.subset_adjoin (↥S) _ hz'
      letI : Fact ((q.map (algebraMap F (↥T))).Splits) := ⟨hsplF⟩
      let phi : Gal((↥T)/(↥S)) →* q.Gal :=
        (Polynomial.Gal.restrict q (↥T)).comp
          (MulSemiringAction.toAlgAut Gal((↥T)/(↥S)) F (↥T))
      apply solvable_of_solvable_injective (f := phi)
      -- A restriction is the identity precisely when it fixes each root.
      -- Those roots, together with `S`, generate `T`.
      rw [injective_iff_map_eq_one]
      intro sig hsig
      have hroot : ∀ z (hz : z ∈ qS.rootSet (AlgebraicClosure F)),
          sig (⟨z, IntermediateField.subset_adjoin (↥S) _ hz⟩ : T) =
            (⟨z, IntermediateField.subset_adjoin (↥S) _ hz⟩ : T) := by
        intro z hz
        let zT : (↥T) := ⟨z, IntermediateField.subset_adjoin (↥S) _ hz⟩
        have hzF : (zT : ↥T) ∈ q.rootSet (↥T) := by
          -- the criterion `aeval=0` is stable under the inclusions into the
          -- algebraic closure
          have hzE : z ∈ q.rootSet (AlgebraicClosure F) := by
            rw [← hrs]
            exact hz
          have hnzT : q.map (algebraMap F (↥T)) ≠ 0 :=
            Polynomial.map_ne_zero (R := F) (S := (↥T)) hq0
          have haE : Polynomial.aeval z q = 0 :=
            (Polynomial.mem_rootSet'.1 hzE).2
          have haT : Polynomial.aeval zT q = 0 := by
            have hev := Polynomial.hom_eval₂ q
              (algebraMap F (↥T)) (IntermediateField.val T).toRingHom zT
            rw [Polynomial.aeval_def] at haE ⊢
            apply (IntermediateField.val T).injective
            -- functoriality of polynomial evaluation
            rw [map_zero]
            rw [hev]
            have hc : (IntermediateField.val T).toRingHom.comp
                  (algebraMap F (↥T)) =
                  algebraMap F (AlgebraicClosure F) := by
              ext u
              change (IntermediateField.val T) ((algebraMap F (↥T)) u) = _
              rw [IsScalarTower.algebraMap_apply F (↥S) (↥T)]
              rw [(IntermediateField.val T).commutes]
              rw [IsScalarTower.algebraMap_apply F (↥S)
                (AlgebraicClosure F)]
            rw [hc]
            exact haE
          exact (Polynomial.mem_rootSet').2 ⟨hnzT, haT⟩
        have oneact :
            (↑((1 : q.Gal) • (⟨zT, hzF⟩ : q.rootSet (↥T))) : ↥T) = zT := by
          simp
        have hact := Polynomial.Gal.restrict_smul
          ((MulSemiringAction.toAlgAut Gal((↥T)/(↥S)) F (↥T)) sig)
          (⟨zT, hzF⟩ : q.rootSet (↥T))
        change
          (↑((Polynomial.Gal.restrict q (↥T)
              ((MulSemiringAction.toAlgAut Gal((↥T)/(↥S)) F (↥T)) sig)) •
              (⟨zT, hzF⟩ : q.rootSet (↥T))) : ↥T) =
            ((MulSemiringAction.toAlgAut Gal((↥T)/(↥S)) F (↥T)) sig) zT at hact
        have hpval : Polynomial.Gal.restrict q (↥T)
              ((MulSemiringAction.toAlgAut Gal((↥T)/(↥S)) F (↥T)) sig) = 1 := hsig
        rw [hpval] at hact
        exact hact.symm.trans oneact
      have heq : (sig : (↥T) ≃ₐ[(↥S)] (↥T)).toAlgHom =
          (1 : (↥T) ≃ₐ[(↥S)] (↥T)).toAlgHom := by
        apply IntermediateField.algHom_ext_of_eq_adjoin (F := (↥S)) (S := T) rfl
        intro z hz
        exact hroot z hz
      exact (AlgEquiv.ext_iff.mpr (fun z =>
        DFunLike.congr_fun heq z))
    have hxroot : x ∈ q.rootSet (AlgebraicClosure F) := by
      have hnz : q.map (algebraMap F (AlgebraicClosure F)) ≠ 0 :=
        Polynomial.map_ne_zero (R := F) (S := AlgebraicClosure F) hq0
      exact (Polynomial.mem_rootSet').2 ⟨hnz, minpoly.aeval F x⟩
    have hxT : x ∈ T := by
      apply IntermediateField.subset_adjoin (↥S)
        (qS.rootSet (AlgebraicClosure F))
      rw [hrs]
      exact hxroot
    -- In fact it is enough to rule out a single nontrivial cyclic
    -- quotient.  A nontrivial finite solvable group has a proper
    -- commutator; extending it to a coatom gives a nontrivial simple
    -- abelian (hence cyclic) quotient.
    let G := Gal((↥T)/(↥S))
    letI : IsSolvable G := hTsolv
    have hsub : Subsingleton G := by
      -- suppose that the Galois group is nontrivial
      by_contra hh
      haveI hnt : Nontrivial G := not_subsingleton_iff_nontrivial.mp hh
      have hc : commutator G < (⊤ : Subgroup G) :=
        IsSolvable.commutator_lt_top_of_nontrivial G
      -- the subgroup lattice is coatomic for a finite group
      obtain hbad | ⟨H, hHcoat, hHc⟩ :=
        (isCoatomic_iff (Subgroup G)).1 (inferInstance)
          (commutator G)
      · exact (ne_of_lt hc) hbad
      · -- `H` contains the commutator, so is normal and has abelian
        -- quotient; its maximality makes this quotient simple.
        letI hHnorm : H.Normal := Subgroup.Normal.of_commutator_le G hHc
        have hHne : H ≠ (⊤ : Subgroup G) := hHcoat.1
        let f : G →* (G ⧸ H) := QuotientGroup.mk' H
        have hf : Function.Surjective f := QuotientGroup.mk'_surjective H
        letI hQnt : Nontrivial (G ⧸ H) :=
          QuotientGroup.nontrivial_iff.mpr hHne
        have hcommQ : IsMulCommutative (G ⧸ H) :=
          (Subgroup.Normal.quotient_commutative_iff_commutator_le).2 hHc
        let hgroup : Group (G ⧸ H) := inferInstance
        letI hQcomm : CommGroup (G ⧸ H) :=
        { hgroup with
          mul_comm := fun a b => @Std.Commutative.comm _ _
            hcommQ.is_comm a b }
        letI hQsimple : IsSimpleGroup (G ⧸ H) := by
          refine IsSimpleGroup.mk (G := (G ⧸ H)) ?_
          intro L hL
          have hle : H ≤ Subgroup.comap f L := by
            intro z hz
            have hz' : z ∈ f.ker := by
              change f z = 1
              change (z : G ⧸ H) = 1
              exact (QuotientGroup.eq_one_iff (N := H) z).2 hz
            exact (Subgroup.ker_le_comap f L) hz' 
          rcases hle.eq_or_lt with heq | hlt
          · left
            have hm := Subgroup.map_comap_eq_self_of_surjective hf L
            have hb : Subgroup.map f H = (⊥ : Subgroup (G ⧸ H)) :=
              (Subgroup.map_eq_bot_iff H).2 (by
                intro z hz
                change f z = 1
                change (z : G ⧸ H) = 1
                exact (QuotientGroup.eq_one_iff (N := H) z).2 hz)
            calc
              L = Subgroup.map f (Subgroup.comap f L) := hm.symm
              _ = Subgroup.map f H :=
                congrArg (Subgroup.map f) heq.symm
              _ = ⊥ := hb
          · have ht : Subgroup.comap f L = (⊤ : Subgroup G) :=
              hHcoat.2 (Subgroup.comap f L) hlt
            right
            apply Subgroup.comap_injective hf
            simpa [ht]
        letI hQcyc : IsCyclic (G ⧸ H) :=
          IsSimpleGroup.isCyclic
        -- The corresponding fixed field, first in `T`, then lifted to the
        -- ambient algebraic closure.
        let U0 : IntermediateField (↥S) (↥T) :=
          IntermediateField.fixedField H
        letI iU0fin : FiniteDimensional (↥S) (↥U0) := by
          exact Module.Finite.of_injective (IntermediateField.val U0).toLinearMap
            (IntermediateField.val U0).injective
        letI iU0gal : IsGalois (↥S) (↥U0) :=
          IsGalois.of_fixedField_normal_subgroup H
        let eQ : (G ⧸ H) ≃* Gal((↥U0)/(↥S)) :=
          IsGalois.normalAutEquivQuotient H
        letI iU0cyc : IsCyclic Gal((↥U0)/(↥S)) :=
          eQ.isCyclic.mp hQcyc
        let U : IntermediateField (↥S) (AlgebraicClosure F) :=
          IntermediateField.lift U0
        let e : (↥U0) ≃ₐ[(↥S)] (↥U) :=
          IntermediateField.liftAlgEquiv U0
        letI iUfin : FiniteDimensional (↥S) (↥U) :=
          Module.Finite.equiv e.toLinearEquiv
        letI iUgal : IsGalois (↥S) (↥U) :=
          IsGalois.of_algEquiv e
        letI iUcyc : IsCyclic Gal((↥U)/(↥S)) :=
          (AlgEquiv.autCongr e).isCyclic.mp iU0cyc
        have hu_all : ∀ u : U, (u : AlgebraicClosure F) ∈ S := by
          simpa [S] using (cyclic_step U)
        have hUbot : U = (⊥ : IntermediateField (↥S)
              (AlgebraicClosure F)) := by
          apply le_bot_iff.mp
          intro z hz
          have hm : z ∈ S := hu_all ⟨z, hz⟩
          rw [IntermediateField.mem_bot]
          exact ⟨⟨z, hm⟩, rfl⟩
        have hU0bot : U0 = (⊥ : IntermediateField (↥S) (↥T)) := by
          apply IntermediateField.lift_injective T
          -- lifting the bottom field is bottom
          simpa [U] using hUbot
        have hHtop : H = (⊤ : Subgroup G) := by
          calc
            H = IntermediateField.fixingSubgroup U0 :=
              (IntermediateField.fixingSubgroup_fixedField H).symm
            _ = IntermediateField.fixingSubgroup
                  (⊥ : IntermediateField (↥S) (↥T)) := by rw [hU0bot]
            _ = ⊤ := IntermediateField.fixingSubgroup_bot
        exact hHne hHtop
    -- A Galois extension with trivial automorphism group is the bottom
    -- field.  Hence every element of `T`, in particular our root, already
    -- lies in `S`.
    have hmem : ∀ y : T, (y : AlgebraicClosure F) ∈ S := by
      intro y
      have hy : y ∈ (⊥ : IntermediateField (↥S) (↥T)) := by
        -- all automorphisms are the identity
        refine (IsGalois.mem_bot_iff_fixed y).2 ?_
        intro σ
        have hs : σ = (1 : Gal((↥T)/(↥S))) :=
          @Subsingleton.elim G hsub σ 1
        simpa using congrArg (fun τ : Gal((↥T)/(↥S)) => τ y) hs
      rw [IntermediateField.mem_bot] at hy
      rcases hy with ⟨b, hb⟩
      have hb' := congrArg (fun z : ↥T =>
        (z : AlgebraicClosure F)) hb
      have hy' : (y : AlgebraicClosure F) =
          (b : AlgebraicClosure F) := by
        simpa using hb'.symm
      rw [hy']
      exact b.property
    change x ∈ solvableByRad F (AlgebraicClosure F)
    exact hmem ⟨x, hxT⟩
/-ResultProofEnd-/
/-ResultEnd-/

end Submission
