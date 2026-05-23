import Mathlib
import Submission.NilpotentHelper
import Submission.NilpotentProof

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Standalone proofs for DiagMapTarget lemmas

These are the two missing lemmas needed to complete the Schur-Weyl duality proof.
-/

namespace Submission.CentralizerLeAdjoinTarget

section UnitTimesIdem

variable {R : Type*} [Field R]
  {M : Type*} [AddCommGroup M] [Module R M] [FiniteDimensional R M]

set_option maxHeartbeats 3200000

/-
Any endomorphism factors as unit * idempotent.
-/
lemma exists_unit_mul_idem (f : Module.End R M) :
    ∃ (u : (Module.End R M)ˣ) (e : Module.End R M),
      e * e = e ∧ f = ↑u * e := by
  -- Let $C$ be a complement of $\ker f$, so $M = \ker f \oplus C$.
  obtain ⟨C, hC⟩ : ∃ C : Submodule R M, IsCompl (LinearMap.ker f) C := Submodule.exists_isCompl _;
  -- Let $u$ be the isomorphism from $M$ to itself such that $u$ maps $C$ to $\text{range}(f)$ and $\text{ker}(f)$ to a complement of $\text{range}(f)$.
  obtain ⟨u, hu⟩ : ∃ u : (Module.End R M)ˣ, ∀ c : C, f c = u.val (Submodule.subtype C c) := by
    -- Let $D$ be a complement of $\text{range}(f)$.
    obtain ⟨D, hD⟩ : ∃ D : Submodule R M, IsCompl (LinearMap.range f) D := Submodule.exists_isCompl _;
    -- The restriction of $f$ to $C$ gives an isomorphism $f_C : C \to \text{range}(f)$.
    obtain ⟨f_C, hf_C⟩ : ∃ f_C : C ≃ₗ[R] LinearMap.range f, ∀ c : C, f c = f_C c := by
      refine' ⟨ _, _ ⟩;
      refine' ( LinearEquiv.ofBijective _ ⟨ _, _ ⟩ );
      refine' { toFun := fun c => ⟨ f c, LinearMap.mem_range_self f c ⟩, map_add' := _, map_smul' := _ };
      all_goals simp +decide [ Function.Injective, Function.Surjective ];
      · intro x hx y hy hxy;
        have := hC.disjoint.le_bot ( show x - y ∈ LinearMap.ker f ⊓ C from ⟨ by simp +decide [ hxy ], by simpa using C.sub_mem hx hy ⟩ ) ; simp_all +decide [ sub_eq_zero ] ;
      · intro x; have := Submodule.mem_sup.mp ( show x ∈ LinearMap.ker f ⊔ C from by rw [ hC.sup_eq_top ] ; exact Submodule.mem_top ) ; aesop;
    -- Choose an isomorphism $\phi : \ker f \to D$ by matching finrank.
    obtain ⟨phi, hphi⟩ : ∃ phi : (LinearMap.ker f) ≃ₗ[R] D, True := by
      have h_finrank : Module.finrank R (LinearMap.ker f) = Module.finrank R D := by
        have := Submodule.finrank_sup_add_finrank_inf_eq ( LinearMap.ker f ) C; have := Submodule.finrank_sup_add_finrank_inf_eq ( LinearMap.range f ) D; simp_all +decide [ hC.sup_eq_top, hD.sup_eq_top ] ;
        rw [ hC.sup_eq_top, hD.sup_eq_top ] at * ; simp_all +decide [ hC.inf_eq_bot, hD.inf_eq_bot ];
        rw [ hC.inf_eq_bot, hD.inf_eq_bot ] at * ; simp_all +decide [ Module.finrank_prod ] ; linarith [ LinearMap.finrank_range_add_finrank_ker f, show Module.finrank R C = Module.finrank R ( LinearMap.range f ) from LinearEquiv.finrank_eq f_C ] ;
      exact ⟨ ( LinearEquiv.ofFinrankEq _ _ h_finrank ), trivial ⟩;
    -- Build $u$ as the composition of the isomorphisms $\phi$ and $f_C$.
    obtain ⟨u, hu⟩ : ∃ u : (LinearMap.ker f × C) ≃ₗ[R] (D × LinearMap.range f), ∀ (k : LinearMap.ker f) (c : C), u (k, c) = (phi k, f_C c) := by
      exact ⟨ phi.prodCongr f_C, fun k c => rfl ⟩;
    -- Build $u$ as the composition of the isomorphisms $\phi$ and $f_C$ and the inclusion maps.
    obtain ⟨u', hu'⟩ : ∃ u' : M ≃ₗ[R] M, ∀ (k : LinearMap.ker f) (c : C), u' (k + c) = (phi k : M) + (f_C c : M) := by
      have h_iso : ∃ u' : (LinearMap.ker f × C) ≃ₗ[R] M, ∀ (k : LinearMap.ker f) (c : C), u' (k, c) = k + c := by
        exact ⟨ Submodule.prodEquivOfIsCompl _ _ hC, fun k c => rfl ⟩;
      obtain ⟨u', hu'⟩ := h_iso
      have h_iso' : ∃ u'' : (D × LinearMap.range f) ≃ₗ[R] M, ∀ (d : D) (r : LinearMap.range f), u'' (d, r) = d + r := by
        refine' ⟨ _, _ ⟩;
        refine' ( LinearEquiv.ofBijective _ ⟨ _, _ ⟩ );
        refine' { toFun := fun p => p.1 + p.2, map_add' := _, map_smul' := _ };
        all_goals simp +decide [ Function.Injective, Function.Surjective ];
        · exact fun _ _ _ _ _ _ => by abel1;
        · intro a ha b c hc d hcd
          have h_eq : a - c = f d - f b := by
            exact eq_of_sub_eq_zero ( by rw [ ← sub_eq_zero_of_eq hcd ] ; abel1 );
          have h_eq_zero : a - c = 0 := by
            have h_eq_zero : a - c ∈ D ∧ a - c ∈ LinearMap.range f := by
              exact ⟨ Submodule.sub_mem _ ha hc, h_eq.symm ▸ Submodule.sub_mem _ ( LinearMap.mem_range_self f d ) ( LinearMap.mem_range_self f b ) ⟩;
            exact hD.symm.disjoint.le_bot ⟨ h_eq_zero.1, h_eq_zero.2 ⟩;
          grind;
        · intro b;
          obtain ⟨ d, hd, r, hr, rfl ⟩ := Submodule.mem_sup.mp ( show b ∈ D ⊔ LinearMap.range f from by rw [ hD.symm.sup_eq_top ] ; exact Submodule.mem_top );
          exact ⟨ d, hd, Classical.choose hr, by rw [ Classical.choose_spec hr ] ⟩;
      obtain ⟨ u'', hu'' ⟩ := h_iso';
      use u'.symm.trans (u.trans u'');
      simp +decide [ ← hu', ← hu'', hu ];
    refine' ⟨ ⟨ u', u'.symm, _, _ ⟩, _ ⟩ <;> simp_all +decide [ LinearMap.ext_iff ];
    intro a ha; specialize hu' 0 ( by simp +decide ) a ha; simp_all +decide ;
  refine' ⟨ u, _, _, _ ⟩;
  exact Submodule.subtype C ∘ₗ ( LinearMap.comp ( Submodule.linearProjOfIsCompl C ( LinearMap.ker f ) hC.symm ) ( LinearMap.id ) );
  · ext; simp +decide [ hu ] ;
  · ext x;
    -- Decompose $x$ into its components in $C$ and $\ker f$.
    obtain ⟨c, k, hc, hk⟩ : ∃ c : C, ∃ k : ↥(LinearMap.ker f), x = c + k := by
      have := Submodule.mem_sup.mp ( show x ∈ LinearMap.ker f ⊔ C from by rw [ hC.sup_eq_top ] ; exact Submodule.mem_top );
      obtain ⟨ y, hy, z, hz, rfl ⟩ := this; exact ⟨ ⟨ z, hz ⟩, ⟨ y, hy ⟩, add_comm _ _ ⟩ ;
    simp +decide [ hu, LinearMap.mem_ker.mp k.2 ]

end UnitTimesIdem

section NilpotentFromIdem

variable {R : Type*} [Field R]
  {M : Type*} [AddCommGroup M] [Module R M] [FiniteDimensional R M]

set_option maxHeartbeats 25600000

open Submission.NilpotentHelper Submission.NilpotentProof in
/-- For a non-trivial idempotent, there exists a unit whose inverse
composed with the idempotent is nilpotent. -/
lemma exists_unit_inv_mul_nilpotent (e : Module.End R M) (he : e * e = e)
    (hne0 : e ≠ 0) (hne1 : e ≠ 1) :
    ∃ u : (Module.End R M)ˣ, IsNilpotent (↑u⁻¹ * e) := by
  let V := LinearMap.range e
  let W := LinearMap.ker e
  have hc : IsCompl V W := LinearMap.IsIdempotentElem.isCompl he
  let r := Module.finrank R V
  let s := Module.finrank R W
  have hr : 0 < r := range_nontrivial_of_ne_zero e he hne0
  have hs : 0 < s := ker_nontrivial_of_ne_one e he hne1
  have hn : Module.finrank R M = r + s := (Submodule.finrank_add_eq_of_isCompl hc).symm
  -- Build combined basis
  let bN := combinedBasis hc rfl rfl
  let n := r + s
  let u_equiv := bN.equiv bN (finRotate n)
  let u : (Module.End R M)ˣ := ⟨u_equiv, u_equiv.symm, by ext; simp, by ext; simp⟩
  refine ⟨u, n, ?_⟩
  apply bN.ext; intro i
  simp only [LinearMap.zero_apply]
  have hbN_V : ∀ j : Fin n, (j : ℕ) < r → e (bN j) = bN j :=
    fun j hj => idem_eq_on_range e he _ (combinedBasis_mem_left hc rfl rfl j hj)
  have hbN_W : ∀ j : Fin n, ¬ (j : ℕ) < r → e (bN j) = 0 :=
    fun j hj => idem_eq_zero_on_ker e he _ (combinedBasis_mem_right hc rfl rfl j (by omega))
  have hu_inv : ∀ j : Fin n, (↑u⁻¹ : Module.End R M) (bN j) = bN ((finRotate n).symm j) := by
    intro j; show u_equiv.symm (bN j) = _
    simp [u_equiv, Module.Basis.equiv]
  exact nilpotent_iterate hr hs rfl bN e (↑u⁻¹) hbN_V hbN_W hu_inv i

end NilpotentFromIdem

end Submission.CentralizerLeAdjoinTarget
