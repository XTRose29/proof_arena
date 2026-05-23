import Mathlib

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Helper lemmas for factoring endomorphisms as unit * idempotent
-/

namespace Submission.DiagMapFactorTarget

variable {R : Type*} [Field R]
  {M : Type*} [AddCommGroup M] [Module R M] [FiniteDimensional R M]

/-- The projection onto q along p, as an endomorphism of M. -/
noncomputable def mkIdem {p q : Submodule R M} (_h : IsCompl p q) : Module.End R M :=
  q.subtype.comp (q.linearProjOfIsCompl p _h.symm)

lemma mkIdem_idem {p q : Submodule R M} (h : IsCompl p q) :
    mkIdem h * mkIdem h = mkIdem h := by
  unfold mkIdem
  ext x
  simp [LinearMap.comp_apply]

lemma mkIdem_ker {p q : Submodule R M} (h : IsCompl p q) :
    LinearMap.ker (mkIdem h) = p := by
  ext x; simp [mkIdem]

lemma mul_mkIdem_eq {f : Module.End R M} {V₁ : Submodule R M}
    (h : IsCompl (LinearMap.ker f) V₁) :
    f * mkIdem h = f := by
  have h_proj : ∀ (x : M), x - mkIdem h x ∈ LinearMap.ker f := by
    intro x
    have : x - mkIdem h x ∈ LinearMap.ker (mkIdem h) := by
      simp +decide [sub_eq_zero, mkIdem_idem]
      exact Eq.symm (LinearMap.congr_fun (mkIdem_idem h) x)
    rw [mkIdem_ker h] at this; exact this
  ext x; specialize h_proj x; simp_all +decide [LinearMap.mem_ker]
  exact Eq.symm (sub_eq_zero.mp h_proj)

lemma finrank_ker_eq_compl_range (f : Module.End R M)
    {W : Submodule R M} (hW : IsCompl (LinearMap.range f) W) :
    Module.finrank R (LinearMap.ker f) = Module.finrank R W := by
  have := LinearMap.finrank_range_add_finrank_ker f
  linarith [show Module.finrank R (LinearMap.range f) + Module.finrank R W = Module.finrank R M by
    rw [← Submodule.finrank_sup_add_finrank_inf_eq, hW.inf_eq_bot, hW.sup_eq_top]; simp +decide]

/-- The complementary projection: projection onto p along q. -/
noncomputable def mkIdemCompl {p q : Submodule R M} (h : IsCompl p q) : Module.End R M :=
  mkIdem (IsCompl.symm h)

/-- The map u = f ∘ proj_V₁ + W.subtype ∘ φ ∘ proj_ker -/
noncomputable def mkUnitMap (f : Module.End R M)
    {V₁ : Submodule R M} (hV : IsCompl (LinearMap.ker f) V₁)
    {W : Submodule R M} (hW : IsCompl (LinearMap.range f) W) :
    Module.End R M :=
  let projV₁ := mkIdem hV
  let projKer : M →ₗ[R] (LinearMap.ker f) :=
    (LinearMap.ker f).linearProjOfIsCompl V₁ hV
  let φ := LinearEquiv.ofFinrankEq (LinearMap.ker f) W (finrank_ker_eq_compl_range f hW)
  f * projV₁ + W.subtype.comp (φ.toLinearMap.comp projKer)

/-
Helper: projKer ∘ projV₁ = 0 (composing complementary projections)
-/
lemma mkIdemCompl_comp_mkIdem {p q : Submodule R M} (h : IsCompl p q) :
    mkIdemCompl h * mkIdem h = 0 := by
  ext x;
  simp +decide [ mkIdemCompl, mkIdem ]

/-
Helper: projV₁ ∘ projKer = 0
-/
lemma mkIdem_comp_mkIdemCompl {p q : Submodule R M} (h : IsCompl p q) :
    mkIdem h * mkIdemCompl h = 0 := by
  -- By definition of $mkIdem$ and $mkIdemCompl$, we have $mkIdem h * mkIdemCompl h = 0$.
  ext; simp [mkIdem, mkIdemCompl]

/-
Helper: projV₁ + projKer = 1
-/
lemma mkIdem_add_mkIdemCompl {p q : Submodule R M} (h : IsCompl p q) :
    mkIdem h + mkIdemCompl h = 1 := by
  ext x;
  simp +decide [ mkIdem, mkIdemCompl ];
  exact Submodule.IsCompl.projection_add_projection_eq_self (mkIdem._proof_2 h) x

lemma mkUnitMap_bijective (f : Module.End R M)
    {V₁ : Submodule R M} (hV : IsCompl (LinearMap.ker f) V₁)
    {W : Submodule R M} (hW : IsCompl (LinearMap.range f) W) :
    Function.Bijective (mkUnitMap f hV hW) := by
  have h_ker : LinearMap.ker (mkUnitMap f hV hW) = ⊥ := by
    refine' eq_bot_iff.mpr _;
    intro x hx
    have h_f_mkIdem : f (mkIdem hV x) = 0 := by
      have h1 : f (mkIdem hV x) + W.subtype (LinearEquiv.toLinearMap (LinearEquiv.ofFinrankEq (LinearMap.ker f) W (finrank_ker_eq_compl_range f hW)) ((LinearMap.ker f).linearProjOfIsCompl V₁ hV x)) = 0 := by
        exact hx;
      have h2 : f (mkIdem hV x) ∈ LinearMap.range f := by
        exact LinearMap.mem_range_self f _
      have h3 : W.subtype (LinearEquiv.toLinearMap (LinearEquiv.ofFinrankEq (LinearMap.ker f) W (finrank_ker_eq_compl_range f hW)) ((LinearMap.ker f).linearProjOfIsCompl V₁ hV x)) ∈ W := by
        exact Submodule.coe_mem _
      have h4 : f (mkIdem hV x) ∈ W := by
        rw [ eq_neg_of_add_eq_zero_left h1 ] ; aesop;
      have h5 : f (mkIdem hV x) = 0 := by
        exact hW.disjoint.le_bot ⟨ h2, h4 ⟩
      exact h5
    have h_W_sub : W.subtype (LinearEquiv.ofFinrankEq (LinearMap.ker f) W (finrank_ker_eq_compl_range f hW) ((LinearMap.ker f).linearProjOfIsCompl V₁ hV x)) = 0 := by
      unfold mkUnitMap at hx; aesop;
    have h_projKer : (LinearMap.ker f).linearProjOfIsCompl V₁ hV x = 0 := by
      exact ( LinearEquiv.ofFinrankEq ( LinearMap.ker f ) W ( finrank_ker_eq_compl_range f hW ) ).injective ( by aesop )
    have h_x_in_V₁ : x ∈ V₁ := by
      exact (Submodule.linearProjOfIsCompl_apply_eq_zero_iff hV).mp h_projKer
    have h_x_in_ker : x ∈ LinearMap.ker f := by
      have h_mkIdem_eq : mkIdem hV x = x := by
        unfold mkIdem; aesop;
      rw [h_mkIdem_eq] at h_f_mkIdem
      exact h_f_mkIdem
    have h_x_zero : x = 0 := by
      exact hV.disjoint.le_bot ⟨ h_x_in_ker, h_x_in_V₁ ⟩
    exact h_x_zero;
  exact ⟨ LinearMap.ker_eq_bot.mp h_ker, LinearMap.surjective_of_injective ( LinearMap.ker_eq_bot.mp h_ker ) ⟩

lemma mkUnitMap_comp_mkIdem (f : Module.End R M)
    {V₁ : Submodule R M} (hV : IsCompl (LinearMap.ker f) V₁)
    {W : Submodule R M} (hW : IsCompl (LinearMap.range f) W) :
    mkUnitMap f hV hW * mkIdem hV = f := by
  simp +decide [ mkUnitMap ];
  simp +decide [ add_mul, mul_mkIdem_eq ];
  ext x;
  simp +decide [ mkIdem, LinearMap.comp_apply ]

/-- Build a LinearEquiv that agrees with f on a complement of ker(f)
    and maps ker(f) isomorphically onto a complement of range(f). -/
noncomputable def mkUnit (f : Module.End R M)
    {V₁ : Submodule R M} (hV : IsCompl (LinearMap.ker f) V₁)
    {W : Submodule R M} (hW : IsCompl (LinearMap.range f) W) :
    M ≃ₗ[R] M :=
  LinearEquiv.ofBijective (mkUnitMap f hV hW) (mkUnitMap_bijective f hV hW)

/-
The factorization property: f = mkUnit * mkIdem
-/
lemma mkUnit_mul_mkIdem (f : Module.End R M)
    {V₁ : Submodule R M} (hV : IsCompl (LinearMap.ker f) V₁)
    {W : Submodule R M} (hW : IsCompl (LinearMap.range f) W) :
    f = (mkUnit f hV hW).toLinearMap * mkIdem hV := by
  convert mkUnitMap_comp_mkIdem f hV hW |> Eq.symm

/-- Converting a LinearEquiv to a unit in the endomorphism monoid. -/
noncomputable def linearEquivToUnit (e : M ≃ₗ[R] M) : (Module.End R M)ˣ where
  val := e.toLinearMap
  inv := e.symm.toLinearMap
  val_inv := by ext; simp
  inv_val := by ext; simp

/-- Main theorem: any endomorphism factors as unit * idempotent -/
theorem exists_unit_mul_idem_proof (f : Module.End R M) :
    ∃ (u : (Module.End R M)ˣ) (e : Module.End R M),
      e * e = e ∧ f = ↑u * e := by
  obtain ⟨V₁, hV⟩ := (LinearMap.ker f).exists_isCompl
  obtain ⟨W, hW⟩ := (LinearMap.range f).exists_isCompl
  exact ⟨linearEquivToUnit (mkUnit f hV hW), mkIdem hV,
    mkIdem_idem hV, mkUnit_mul_mkIdem f hV hW⟩

end Submission.DiagMapFactorTarget
