import Mathlib
import Submission.PeterWeylTrace
import Submission.EigenvalueField

/-!
# Burnside vanishing and assembly for burnside_char_core

This file proves the character-theoretic core of Burnside's p^a q^b theorem:
if G is simple with g ≠ 1 and [G:C_G(g)] = q^k, then q⁻¹ is an algebraic integer.
-/

set_option maxHeartbeats 400000

open scoped Classical
noncomputable section

namespace Submission.BurnsideVanishing

/-! ## Semisimplicity of group algebras (Maschke) -/

instance monoidAlgebra_isSemisimpleRing (G : Type) [Group G] [Fintype G] :
    IsSemisimpleRing (MonoidAlgebra ℂ G) := by
  haveI : NeZero (Nat.card G : ℂ) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  infer_instance

/-! ## Simple non-abelian groups are perfect -/

lemma simple_nonabelian_commutator_eq_top (G : Type) [Group G]
    (hsimple : IsSimpleGroup G) (hnonab : ¬ ∀ a b : G, a * b = b * a) :
    commutator G = ⊤ := by
  rcases hsimple.eq_bot_or_eq_top_of_normal (commutator G) inferInstance with h | h
  · exfalso; apply hnonab; intro a b
    have hmem := Subgroup.commutator_mem_commutator (G := G) (Subgroup.mem_top a) (Subgroup.mem_top b)
    change _ ∈ commutator G at hmem
    rw [h] at hmem; simp [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact hmem
  · exact h

/-! ## Simple group with order divisible by two primes is non-abelian -/

lemma simple_group_nonabelian_of_two_primes {G : Type} [Group G] [Fintype G]
    (hsimple : IsSimpleGroup G) {q : ℕ} (hq : q.Prime)
    (hnonabelian : ∃ (p : ℕ), p.Prime ∧ p ≠ q ∧ p ∣ Fintype.card G)
    (hq_dvd : q ∣ Fintype.card G) :
    ¬ ∀ a b : G, a * b = b * a := by
  obtain ⟨ p, hp, hp', hpq ⟩ := hnonabelian;
  by_contra h_abelian
  have h_card_prime : Fintype.card G = p := by
    have h_card_prime : ∀ H : Subgroup G, H.Normal → H = ⊥ ∨ H = ⊤ := by
      grind +suggestions;
    -- Let $H$ be a subgroup of $G$ of order $p$.
    obtain ⟨H, hH⟩ : ∃ H : Subgroup G, Fintype.card H = p := by
      have := Fact.mk hp; have := exists_prime_orderOf_dvd_card p hpq; obtain ⟨ g, hg ⟩ := this; exact ⟨ Subgroup.zpowers g, by rw [ Fintype.card_zpowers, hg ] ⟩ ;
    cases h_card_prime H ( by constructor ; intros ; simp_all +decide [ Subgroup.mem_bot, Subgroup.mem_top ] ) <;> simp_all +decide [ Subgroup.eq_bot_iff_forall, Subgroup.eq_top_iff' ];
    exact absurd hH.symm hp.ne_one;
  simp_all +decide [ Nat.prime_dvd_prime_iff_eq ]

/-! ## Wedderburn decomposition existence -/

lemma wedderburn_decomp_exists (G : Type) [Group G] [Fintype G] [DecidableEq G] :
    ∃ (n : ℕ) (d : Fin n → ℕ),
      (∀ i, NeZero (d i)) ∧
      Nonempty (MonoidAlgebra ℂ G ≃ₐ[ℂ] ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) := by
  exact IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed ℂ (MonoidAlgebra ℂ G)

/-! ## Character values from Wedderburn are algebraic integers -/

/-
The trace of a Wedderburn representation at a group element is an algebraic integer.
-/
lemma wedderburn_char_isIntegral (G : Type) [Group G] [Fintype G] [DecidableEq G]
    {n : ℕ} (d : Fin n → ℕ) (hd : ∀ i, NeZero (d i))
    (e : MonoidAlgebra ℂ G ≃ₐ[ℂ] ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (g : G) (i : Fin n) :
    IsIntegral ℤ (Matrix.trace ((e (MonoidAlgebra.single g 1)) i)) := by
  -- The matrix M = (e(MonoidAlgebra.single g 1))_i satisfies M^(orderOf g) = I (identity matrix), because (MonoidAlgebra.single g 1)^(orderOf g) = MonoidAlgebra.single (g^(orderOf g)) 1 = MonoidAlgebra.single 1 1 = 1 in MonoidAlgebra, and e preserves this.
  have hM_pow : ((e (MonoidAlgebra.single g 1)) i) ^ (orderOf g) = 1 := by
    nontriviality;
    have hM_pow : ((e (MonoidAlgebra.single g 1)) i) ^ (orderOf g) = e (MonoidAlgebra.single (g ^ orderOf g) 1) i := by
      have hM_pow : ((e (MonoidAlgebra.single g 1)) i) ^ (orderOf g) = e ((MonoidAlgebra.single g 1) ^ (orderOf g)) i := by
        induction' orderOf g with k hk <;> simp_all +decide [ pow_succ, ← mul_assoc ];
        convert congr_arg ( fun x => e x i ) ( show MonoidAlgebra.single ( g ^ k ) 1 * MonoidAlgebra.single g 1 = MonoidAlgebra.single ( g ^ k * g ) 1 from ?_ ) using 1;
        · exact congr_fun ( e.map_mul _ _ ) i ▸ rfl;
        · simp +decide [ MonoidAlgebra.single_mul_single ]
      convert hM_pow using 2;
      induction orderOf g <;> simp_all +decide [ pow_succ, MonoidAlgebra.single_mul_single ];
      module;
    simp_all +decide [ pow_orderOf_eq_one ];
    convert congr_fun ( e.map_one ) i;
  -- Since the minimal polynomial of $M$ divides $X^{orderOf g} - 1$, all eigenvalues of $M$ are roots of unity.
  have h_eigenvalues : ∀ (x : ℂ), x ∈ Polynomial.rootSet (Matrix.charpoly ((e (MonoidAlgebra.single g 1)) i)) ℂ → IsIntegral ℤ x := by
    intro x hx
    have h_eigenvalue : x ^ (orderOf g) = 1 := by
      rw [ Polynomial.mem_rootSet ] at hx;
      -- Since $x$ is an eigenvalue of $M$, we have $Mv = xv$ for some nonzero vector $v$.
      obtain ⟨v, hv⟩ : ∃ v : Fin (d i) → ℂ, v ≠ 0 ∧ (e (MonoidAlgebra.single g 1) i).mulVec v = x • v := by
        have := Matrix.exists_mulVec_eq_zero_iff.mpr ( show Matrix.det ( e ( MonoidAlgebra.single g 1 ) i - Matrix.scalar ( Fin ( d i ) ) x ) = 0 from ?_ );
        · simp_all +decide [ sub_eq_iff_eq_add, Matrix.sub_mulVec ];
        · rw [ Matrix.det_eq_sign_charpoly_coeff ];
          simp_all +decide [ Matrix.charpoly, Matrix.det_apply' ];
          convert hx.2 using 3 ; simp +decide [ Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_prod ];
          exact Finset.prod_congr rfl fun _ _ => by by_cases h : ‹Equiv.Perm ( Fin ( d i ) ) › ‹_› = ‹_› <;> simp +decide [ h ] ;
      -- Applying $M^{orderOf g}$ to $v$, we get $M^{orderOf g} v = x^{orderOf g} v$.
      have hM_pow_v : (e (MonoidAlgebra.single g 1) i ^ orderOf g).mulVec v = x ^ orderOf g • v := by
        refine' Nat.recOn ( orderOf g ) _ _ <;> simp_all +decide [ pow_succ', Matrix.mulVec_smul ];
        intro k hk; simp_all +decide [ ← Matrix.mulVec_mulVec ] ;
        rw [ Matrix.mulVec_smul, hv.2, smul_smul, mul_comm ];
      exact smul_left_injective _ hv.1 <| by simpa [ hM_pow ] using hM_pow_v.symm;
    exact ⟨ Polynomial.X ^ orderOf g - 1, Polynomial.monic_X_pow_sub_C _ ( Nat.ne_of_gt ( orderOf_pos g ) ), by aesop ⟩;
  -- The trace of $M$ is the sum of its eigenvalues, which are roots of unity.
  have h_trace : Matrix.trace ((e (MonoidAlgebra.single g 1)) i) = Multiset.sum (Polynomial.roots (Matrix.charpoly ((e (MonoidAlgebra.single g 1)) i))) := by
    convert Matrix.trace_eq_sum_roots_charpoly _;
    infer_instance;
  rw [ h_trace ];
  refine' IsIntegral.multiset_sum _;
  simp_all +decide [ Polynomial.rootSet_def ]

/-! ## Dim-1 factor existence and character = 1 for perfect groups -/

/-
No nonzero algebra hom from M_d(ℂ) to ℂ when d ≥ 2.
-/
lemma no_algHom_matrix_to_complex {d : ℕ} (hd : 2 ≤ d)
    (φ : Matrix (Fin d) (Fin d) ℂ →ₐ[ℂ] ℂ) : ∀ M, φ M = 0 := by
  -- Since $d \geq 2$, $M_d(\mathbb{C})$ is a simple ring (it has no nontrivial two-sided ideals).
  have h_simple : IsSimpleRing (Matrix (Fin d) (Fin d) ℂ) := by
    rcases d with ( _ | _ | d ) <;> simp_all +decide;
    infer_instance;
  have h_kernel : ∀ (I : TwoSidedIdeal (Matrix (Fin d) (Fin d) ℂ)), I = ⊥ ∨ I = ⊤ := by
    exact fun I => eq_bot_or_eq_top I;
  have h_injective : Function.Injective φ := by
    cases h_kernel ( TwoSidedIdeal.ker φ ) <;> simp_all +decide [ TwoSidedIdeal.ext_iff ];
    · intro x y hxy; specialize ‹∀ x : Matrix ( Fin d ) ( Fin d ) ℂ, x ∈ TwoSidedIdeal.ker φ ↔ x = 0› ( x - y ) ; simp_all +decide [ sub_eq_zero ] ;
      exact ‹x - y ∈ TwoSidedIdeal.ker φ ↔ x = y›.mp ( by simp +decide [ hxy, TwoSidedIdeal.mem_ker ] );
    · rename_i h; specialize h 1; simp_all +decide [ TwoSidedIdeal.mem_ker ] ;
  have h_contradiction : Module.finrank ℂ (Matrix (Fin d) (Fin d) ℂ) ≤ Module.finrank ℂ ℂ := by
    exact LinearMap.finrank_le_finrank_of_injective ( show Function.Injective ( φ.toLinearMap ) from h_injective );
  norm_num [ Module.finrank ] at h_contradiction ; nlinarith

/-- The augmentation map on the group algebra. -/
def augmentation (G : Type) [Group G] [Fintype G] : MonoidAlgebra ℂ G →ₐ[ℂ] ℂ :=
  MonoidAlgebra.liftNCAlgHom (AlgHom.id ℂ ℂ) 1 (fun _ _ => Commute.all _ _)

lemma augmentation_single (G : Type) [Group G] [Fintype G] (g : G) :
    augmentation G (MonoidAlgebra.single g 1) = 1 := by
  simp [augmentation, MonoidAlgebra.liftNCAlgHom]

lemma augmentation_surjective (G : Type) [Group G] [Fintype G] :
    Function.Surjective (augmentation G) := by
  intro c
  use MonoidAlgebra.single 1 c
  simp [augmentation, MonoidAlgebra.liftNCAlgHom]

/-- There exists a dim-1 factor in the Wedderburn decomposition. -/
lemma wedderburn_has_dim1 (G : Type) [Group G] [Fintype G] [DecidableEq G]
    {n : ℕ} (d : Fin n → ℕ) (hd : ∀ i, NeZero (d i))
    (e : MonoidAlgebra ℂ G ≃ₐ[ℂ] ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) :
    ∃ i₀ : Fin n, d i₀ = 1 := by
  -- Compose augmentation with e.symm
  set δ : (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) →ₐ[ℂ] ℂ :=
    (augmentation G).comp e.symm.toAlgHom
  -- Helper for Pi.single multiplication
  have pi_single_sq : ∀ i, Pi.single (M := fun j => Matrix (Fin (d j)) (Fin (d j)) ℂ) i 1 *
      Pi.single (M := fun j => Matrix (Fin (d j)) (Fin (d j)) ℂ) i 1 =
      Pi.single i 1 := by
    intro i; ext j; simp only [Pi.mul_apply]
    by_cases hj : j = i
    · subst hj; simp [Pi.single_eq_same]
    · simp [Pi.single_eq_of_ne hj]
  -- Idempotent argument
  have hδ_ei : ∀ i, δ (Pi.single i 1) = 0 ∨ δ (Pi.single i 1) = 1 := by
    intro i
    have hidem : δ (Pi.single i 1) ^ 2 = δ (Pi.single i 1) := by
      rw [sq, ← map_mul, pi_single_sq]
    exact or_iff_not_imp_left.mpr fun h =>
      mul_left_cancel₀ h <| by linear_combination hidem
  -- Some j has δ(e_j) = 1
  obtain ⟨j, hj⟩ : ∃ j, δ (Pi.single j 1) = 1 := by
    have hsum : ∑ i, δ (Pi.single i 1) = 1 := by
      rw [← map_sum]
      convert map_one δ
      ext i; simp [Finset.sum_apply]
    by_contra hall
    push_neg at hall
    have hzero : ∑ i, δ (Pi.single i 1) = 0 :=
      Finset.sum_eq_zero fun i _ => (hδ_ei i).resolve_right (hall i)
    simp [hzero] at hsum
  -- d j must be 1
  by_cases hdj : 2 ≤ d j
  · -- Construct algebra hom M_{d_j} → ℂ
    exfalso
    have pi_single_mul : ∀ (x y : Matrix (Fin (d j)) (Fin (d j)) ℂ),
        Pi.single (M := fun j => Matrix (Fin (d j)) (Fin (d j)) ℂ) j (x * y) =
        Pi.single j x * Pi.single j y := by
      intro x y; ext i; simp only [Pi.mul_apply]
      by_cases hi : i = j
      · subst hi; simp [Pi.single_eq_same]
      · simp [Pi.single_eq_of_ne hi]
    have h0 := no_algHom_matrix_to_complex hdj
      ({ toFun := fun M => δ (Pi.single j M)
         map_one' := hj
         map_mul' := by
           intro x y
           show δ (Pi.single j (x * y)) = δ (Pi.single j x) * δ (Pi.single j y)
           rw [pi_single_mul, map_mul]
         map_zero' := by show δ (Pi.single j 0) = 0; rw [Pi.single_zero]; exact map_zero δ
         map_add' := by
           intro x y; show δ (Pi.single j (x + y)) = _
           rw [Pi.single_add]; exact map_add δ _ _
         commutes' := by
           intro r
           show δ (Pi.single j (algebraMap ℂ _ r)) = algebraMap ℂ ℂ r
           rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
               Pi.single_smul, map_smul, hj, smul_eq_mul, mul_one] })
    have := h0 1; simp [hj] at this
  · exact ⟨j, by have := (hd j).out; omega⟩

/-
For a perfect group, a dim-1 Wedderburn factor has character value 1.
-/
lemma wedderburn_dim1_char_eq_one (G : Type) [Group G] [Fintype G] [DecidableEq G]
    (hperf : commutator G = ⊤)
    {n : ℕ} (d : Fin n → ℕ) (hd : ∀ i, NeZero (d i))
    (e : MonoidAlgebra ℂ G ≃ₐ[ℂ] ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (i : Fin n) (hi : d i = 1) (g : G) :
    Matrix.trace ((e (MonoidAlgebra.single g 1)) i) = 1 := by
  -- Describe the map $\varphi$ by deriving a contradiction from the assumption that $\varphi(g) \neq 1$.
  have h_phi_hom : ∀ g h : G, ((e (MonoidAlgebra.single g 1)) i) 0 0 * ((e (MonoidAlgebra.single h 1)) i) 0 0 = ((e (MonoidAlgebra.single (g * h) 1)) i) 0 0 := by
    intro g h
    have h_mul : e (MonoidAlgebra.single g 1) * e (MonoidAlgebra.single h 1) = e (MonoidAlgebra.single (g * h) 1) := by
      rw [ ← map_mul ] ; aesop;
    convert congr_fun ( congr_fun h_mul i ) 0 |> congr_fun <| 0 using 1 ; simp +decide [ Matrix.mul_apply ];
    rw [ Finset.sum_eq_single 0 ] <;> simp +contextual;
    grind +revert;
  -- Since $\varphi$ is a homomorphism from $G$ to $\mathbb{C}^*$ and $G$ is perfect, $\varphi(g) = 1$ for all $g \in G$.
  have h_phi_trivial : ∀ g : G, ((e (MonoidAlgebra.single g 1)) i) 0 0 = 1 := by
    -- Since $\varphi$ is a homomorphism from $G$ to $\mathbb{C}^*$ and $G$ is perfect, $\varphi(g) = 1$ for all $g \in G$ by the properties of commutators.
    intros g
    have h_comm : ∀ a b : G, ((e (MonoidAlgebra.single (a * b * a⁻¹ * b⁻¹) 1)) i) 0 0 = 1 := by
      intros a b
      have h_comm_step : ((e (MonoidAlgebra.single (a * b * a⁻¹ * b⁻¹) 1)) i) 0 0 = ((e (MonoidAlgebra.single a 1)) i) 0 0 * ((e (MonoidAlgebra.single b 1)) i) 0 0 * ((e (MonoidAlgebra.single a⁻¹ 1)) i) 0 0 * ((e (MonoidAlgebra.single b⁻¹ 1)) i) 0 0 := by
        simp +decide only [h_phi_hom];
      have h_comm_step : ((e (MonoidAlgebra.single a 1)) i) 0 0 * ((e (MonoidAlgebra.single a⁻¹ 1)) i) 0 0 = 1 ∧ ((e (MonoidAlgebra.single b 1)) i) 0 0 * ((e (MonoidAlgebra.single b⁻¹ 1)) i) 0 0 = 1 := by
        have h_comm_step : ((e (MonoidAlgebra.single 1 1)) i) 0 0 = 1 := by
          convert congr_fun ( congr_fun ( e.map_one ) i ) 0 |> congr_arg ( fun x => x 0 ) using 1;
        exact ⟨ by rw [ h_phi_hom, mul_inv_cancel, h_comm_step ], by rw [ h_phi_hom, mul_inv_cancel, h_comm_step ] ⟩;
      grind;
    -- Since $G$ is perfect, every element of $G$ is a product of commutators.
    have h_prod_comm : ∀ g : G, ∃ (l : List G), g = List.prod l ∧ ∀ x ∈ l, ∃ a b : G, x = a * b * a⁻¹ * b⁻¹ := by
      intro g
      have h_prod_comm : g ∈ commutator G := by
        aesop;
      rw [ commutator_eq_closure ] at h_prod_comm;
      refine' Subgroup.closure_induction ( fun x hx => _ ) _ _ _ h_prod_comm;
      · exact ⟨ [ x ], by simp +decide, by obtain ⟨ a, b, rfl ⟩ := hx; exact fun y hy => ⟨ a, b, by aesop ⟩ ⟩;
      · exact ⟨ [ ], rfl, by intros; contradiction ⟩;
      · rintro x y hx hy ⟨ l₁, rfl, hl₁ ⟩ ⟨ l₂, rfl, hl₂ ⟩ ; exact ⟨ l₁ ++ l₂, by simp +decide, by aesop ⟩ ;
      · rintro x hx ⟨ l, rfl, hl ⟩;
        refine' ⟨ l.reverse.map fun x => x⁻¹, _, _ ⟩ <;> simp_all +decide [ List.prod_inv_reverse ];
        intro x hx; obtain ⟨ a, b, h ⟩ := hl _ hx; use b, a; simp_all +decide [ mul_assoc ] ;
        rw [ inv_eq_iff_eq_inv ] at h ; simp_all +decide [ mul_assoc ];
    obtain ⟨ l, rfl, hl ⟩ := h_prod_comm g;
    have h_prod_comm : ∀ (l : List G), (∀ x ∈ l, ((e (MonoidAlgebra.single x 1)) i) 0 0 = 1) → ((e (MonoidAlgebra.single (List.prod l) 1)) i) 0 0 = 1 := by
      intro l hl; induction l <;> simp_all +decide ;
      · convert h_comm 1 1 using 1 ; norm_num;
      · rw [ ← h_phi_hom, hl.1, ‹e ( MonoidAlgebra.single _ 1 ) i 0 0 = 1›, one_mul ];
    exact h_prod_comm l fun x hx => by obtain ⟨ a, b, rfl ⟩ := hl x hx; exact h_comm a b;
  simp_all +decide [ Matrix.trace ];
  rw [ Finset.sum_eq_single 0 ] <;> simp_all +decide;
  lia

/-
For a perfect group, there is at most one dim-1 factor.
-/
lemma wedderburn_at_most_one_dim1 (G : Type) [Group G] [Fintype G] [DecidableEq G]
    (hperf : commutator G = ⊤)
    {n : ℕ} (d : Fin n → ℕ) (hd : ∀ i, NeZero (d i))
    (e : MonoidAlgebra ℂ G ≃ₐ[ℂ] ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (i j : Fin n) (hi : d i = 1) (hj : d j = 1) : i = j := by
  by_contra h_neq;
  -- Define two ℂ-linear maps φ, ψ : MonoidAlgebra ℂ G → ℂ by φ(a) = Matrix.trace(e(a)_i) and ψ(a) = Matrix.trace(e(a)_j).
  set phi : MonoidAlgebra ℂ G →ₗ[ℂ] ℂ := { toFun := fun a => Matrix.trace ((e a) i), map_add' := by
                                            simp +decide [ Matrix.trace_add ], map_smul' := by
                                            simp +decide [ Matrix.trace_smul ] }
  set psi : MonoidAlgebra ℂ G →ₗ[ℂ] ℂ := { toFun := fun a => Matrix.trace ((e a) j), map_add' := by
                                            simp +decide [ Matrix.trace_add ], map_smul' := by
                                            simp +decide [ Matrix.trace_smul ] }
  generalize_proofs at *;
  -- Since $\phi$ and $\psi$ are linear maps and agree on the basis $\{ \text{single } g 1 \mid g \in G \}$, they must be equal.
  have h_eq_maps : phi = psi := by
    have h_eq_maps : ∀ g : G, phi (MonoidAlgebra.single g 1) = psi (MonoidAlgebra.single g 1) := by
      intro g
      have h_eq : phi (MonoidAlgebra.single g 1) = 1 ∧ psi (MonoidAlgebra.single g 1) = 1 := by
        exact ⟨ wedderburn_dim1_char_eq_one G hperf d hd e i hi g, wedderburn_dim1_char_eq_one G hperf d hd e j hj g ⟩
      exact h_eq.left.trans h_eq.right.symm;
    refine' LinearMap.ext fun x => _;
    induction' x using MonoidAlgebra.induction_on with g x y hx hy;
    · convert h_eq_maps g using 1;
    · aesop;
    · aesop;
  -- Since $e$ is a bijection, we can find $x \in \text{MonoidAlgebra } \mathbb{C} G$ such that $e(x) = \text{Pi.single } i (1 : \text{Matrix } (\text{Fin } 1) (\text{Fin } 1) \mathbb{C})$.
  obtain ⟨x, hx⟩ : ∃ x : MonoidAlgebra ℂ G, e x = Pi.single i (1 : Matrix (Fin (d i)) (Fin (d i)) ℂ) := by
    exact e.surjective _;
  replace h_eq_maps := congr_arg ( fun f => f x ) h_eq_maps ; simp_all +decide ;
  simp +zetaDelta at *;
  simp_all +decide [ Matrix.trace ]

/-! ## Class sum eigenvalue integrality -/

/-
Central elements of a matrix ring are scalar matrices.
-/
lemma center_matrix_scalar {m : ℕ} [NeZero m] (A : Matrix (Fin m) (Fin m) ℂ)
    (hA : ∀ B : Matrix (Fin m) (Fin m) ℂ, A * B = B * A) :
    ∃ c : ℂ, A = c • 1 := by
  -- By comparing entries, we see that $A$ must be a scalar multiple of the identity matrix.
  have h_diag : ∀ (i j : Fin m), i ≠ j → A i j = 0 := by
    intro i j hij; specialize hA ( Matrix.diagonal ( fun k => if k = j then 1 else 0 ) ) ; replace hA := congr_fun ( congr_fun hA i ) j ; aesop;
  -- By comparing entries, we see that $A$ must be a scalar multiple of the identity matrix. Hence, $A$ is a scalar matrix.
  have h_scalar : ∀ i j : Fin m, A i i = A j j := by
    intro i j; specialize hA ( Matrix.of fun k l => if k = j then if l = i then 1 else 0 else 0 ) ; replace hA := congr_fun ( congr_fun hA j ) i ; simp_all +decide [ Matrix.mul_apply ] ;
  exact ⟨ A ⟨ 0, NeZero.pos m ⟩ ⟨ 0, NeZero.pos m ⟩, by ext i j; by_cases hi : i = j <;> aesop ⟩

/-
If a central element of MonoidAlgebra ℤ G maps to ω · I under Wedderburn,
    then ω is integral over ℤ.
-/
lemma scalar_integral_of_central_integral
    (G : Type) [Group G] [Fintype G] [DecidableEq G]
    {n : ℕ} (d : Fin n → ℕ) (hd : ∀ i, NeZero (d i))
    (e : MonoidAlgebra ℂ G ≃ₐ[ℂ] ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (c : MonoidAlgebra ℂ G)
    (hc_int : IsIntegral ℤ c)
    (i : Fin n)
    (ω : ℂ)
    (hω : e c i = ω • 1) :
    IsIntegral ℤ ω := by
  -- Apply the algebra homomorphism property to conclude that $a(c) i = p(\omega) • 1$.
  have h_eval : ∀ p : Polynomial ℤ, (e (Polynomial.aeval (R := ℤ) c p)) i = Polynomial.aeval (R := ℤ) ω p • 1 := by
    intro p; induction p using Polynomial.induction_on' <;> simp_all +decide [ Polynomial.aeval_add ] ;
    · rw [ add_smul ];
    · simp +decide [ Algebra.smul_def ];
  obtain ⟨ p, hp_monic, hp_eq ⟩ := hc_int; use p; use hp_monic; specialize h_eval p; simp_all +decide [ Polynomial.aeval_def ] ;
  simpa [ hd i ] using congr_arg ( fun x => x ( 0 : Fin ( d i ) ) ( 0 : Fin ( d i ) ) ) h_eval.symm

/-- Class sum in ℂ[G] -/
private def classSumC (G : Type) [Group G] [Fintype G] [DecidableEq G] (g : G) :
    MonoidAlgebra ℂ G :=
  ∑ h ∈ Finset.univ.filter (fun h => IsConj g h), MonoidAlgebra.single h 1

/-- Class sum in ℤ[G] -/
private def classSumZ (G : Type) [Group G] [Fintype G] [DecidableEq G] (g : G) :
    MonoidAlgebra ℤ G :=
  ∑ h ∈ Finset.univ.filter (fun h => IsConj g h), MonoidAlgebra.single h 1

private lemma classSumC_integral (G : Type) [Group G] [Fintype G] [DecidableEq G] (g : G) :
    IsIntegral ℤ (classSumC G g) := by
  have : classSumC G g = (MonoidAlgebra.mapRangeAlgHom G (Algebra.ofId ℤ ℂ)) (classSumZ G g) := by
    simp [classSumC, classSumZ, MonoidAlgebra.mapRangeAlgHom, map_sum]
  rw [this]; exact IsIntegral.map _ (Algebra.IsIntegral.isIntegral _)

private lemma classSumC_central (G : Type) [Group G] [Fintype G] [DecidableEq G] (g s : G) :
    MonoidAlgebra.single s (1 : ℂ) * classSumC G g = classSumC G g * MonoidAlgebra.single s 1 := by
  unfold classSumC;
  simp +decide [ Finset.mul_sum _ _ _, Finset.sum_mul _ _ _, MonoidAlgebra.single_mul_single ];
  apply Finset.sum_bij (fun x hx => s * x * s⁻¹);
  · simp +decide [ mul_assoc ];
    exact fun a => ⟨ s * a, by group ⟩;
  · simp +contextual [ mul_inv_eq_iff_eq_mul ];
  · simp +decide [ mul_assoc ];
    exact fun a => ⟨ s⁻¹ * a, by group ⟩;
  · simp +decide [ mul_assoc ]

/-
The class sum eigenvalue ω = [G:C_G(g)] · χ(g) / d is an algebraic integer.
-/
lemma class_sum_eigenvalue_isIntegral (G : Type) [Group G] [Fintype G] [DecidableEq G]
    {n : ℕ} (d : Fin n → ℕ) (hd : ∀ i, NeZero (d i))
    (e : MonoidAlgebra ℂ G ≃ₐ[ℂ] ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (g : G) (i : Fin n) :
    IsIntegral ℤ ((Subgroup.centralizer ({g} : Set G)).index *
      Matrix.trace ((e (MonoidAlgebra.single g 1)) i) / (d i : ℂ)) := by
  -- By center_matrix_scalar, there exists some ω such that e(classSumC G g) i = ω • 1.
  obtain ⟨ω, hω⟩ : ∃ ω : ℂ, e (classSumC G g) i = ω • 1 := by
    apply center_matrix_scalar;
    intro B
    have h_comm : ∀ s : G, e (MonoidAlgebra.single s 1) i * e (classSumC G g) i = e (classSumC G g) i * e (MonoidAlgebra.single s 1) i := by
      intro s
      have h_comm : MonoidAlgebra.single s 1 * classSumC G g = classSumC G g * MonoidAlgebra.single s 1 := by
        exact classSumC_central G g s;
      simpa using congr_arg ( fun x => e x i ) h_comm;
    -- By linearity of $e$, we can extend the commutativity to any element of the group algebra.
    have h_comm_all : ∀ x : MonoidAlgebra ℂ G, e x i * e (classSumC G g) i = e (classSumC G g) i * e x i := by
      intro x
      induction' x using MonoidAlgebra.induction_on with s x y hx hy;
      · convert h_comm s using 1;
      · simp_all +decide [ add_mul, mul_add ];
      · simp_all +decide [ Algebra.smul_mul_assoc ];
    convert h_comm_all ( e.symm ( Pi.single i B ) ) |> Eq.symm using 1 <;> simp +decide;
  -- By scalar_integral_of_central_integral, ω is integral.
  have hω_integral : IsIntegral ℤ ω := by
    apply scalar_integral_of_central_integral G d hd e (classSumC G g) (classSumC_integral G g) i ω hω;
  -- By definition of ω, we have ω * d_i = class_size * χ_i(g).
  have hω_eq : ω * (d i : ℂ) = (Finset.card (Finset.filter (fun h => IsConj g h) Finset.univ)) * (Matrix.trace ((e (MonoidAlgebra.single g 1)) i)) := by
    -- By definition of $e$, we know that $e(classSumC G g) i = \sum_{h \in \text{class}(g)} e(single h 1) i$.
    have h_e_classSumC : e (classSumC G g) i = ∑ h ∈ Finset.filter (fun h => IsConj g h) Finset.univ, e (MonoidAlgebra.single h 1) i := by
      simp +decide [ classSumC ];
    -- By definition of $e$, we know that $e(single h 1) i$ is similar to $e(single g 1) i$ for any $h$ conjugate to $g$.
    have h_e_similar : ∀ h : G, IsConj g h → Matrix.trace (e (MonoidAlgebra.single h 1) i) = Matrix.trace (e (MonoidAlgebra.single g 1) i) := by
      intro h hh
      obtain ⟨t, ht⟩ : ∃ t : G, h = t * g * t⁻¹ := by
        obtain ⟨ t, ht ⟩ := hh;
        exact ⟨ t, by simp +decide [ ht.eq, mul_assoc ] ⟩;
      have h_e_similar : e (MonoidAlgebra.single h 1) i = e (MonoidAlgebra.single t 1) i * e (MonoidAlgebra.single g 1) i * e (MonoidAlgebra.single t⁻¹ 1) i := by
        have h_e_similar : e (MonoidAlgebra.single h 1) = e (MonoidAlgebra.single t 1) * e (MonoidAlgebra.single g 1) * e (MonoidAlgebra.single t⁻¹ 1) := by
          simp +decide [ ← map_mul, ht ];
        exact congr_fun h_e_similar i;
      rw [ h_e_similar, Matrix.trace_mul_comm ];
      have h_e_similar : e (MonoidAlgebra.single t⁻¹ 1) i * e (MonoidAlgebra.single t 1) i = 1 := by
        have h_e_similar : e (MonoidAlgebra.single t⁻¹ 1) * e (MonoidAlgebra.single t 1) = 1 := by
          simp +decide [ ← map_mul ];
          simp [MonoidAlgebra.one_def];
        convert congr_fun h_e_similar i using 1;
      rw [ ← Matrix.mul_assoc, h_e_similar, Matrix.one_mul ];
    replace h_e_classSumC := congr_arg Matrix.trace h_e_classSumC; simp_all +decide [ Matrix.trace_smul ] ;
    rw [ Finset.sum_congr rfl fun x hx => show ( e ( MonoidAlgebra.single x 1 ) i |> Matrix.trace ) = ( e ( MonoidAlgebra.single g 1 ) i |> Matrix.trace ) from by obtain ⟨ y, hy, rfl ⟩ := Finset.mem_image.mp hx; exact h_e_similar y ] ; simp +decide;
  -- By definition of class size, we have class_size = (Subgroup.centralizer {g}).index.
  have h_class_size : (Finset.card (Finset.filter (fun h => IsConj g h) Finset.univ)) = (Subgroup.centralizer {g}).index := by
    have h_class_size : (Finset.card (Finset.filter (fun h => IsConj g h) Finset.univ)) = (Finset.card (Finset.image (fun h => h * g * h⁻¹) Finset.univ)) := by
      congr with x ; simp +decide [ isConj_iff ];
    have h_class_size : (Finset.card (Finset.image (fun h => h * g * h⁻¹) Finset.univ)) = (Fintype.card G) / (Fintype.card (MulAction.stabilizer (ConjAct G) g)) := by
      have h_class_size : (Finset.card (Finset.image (fun h => h * g * h⁻¹) Finset.univ)) = (Fintype.card (MulAction.orbit (ConjAct G) g)) := by
        rw [ Fintype.card_of_subtype ];
        simp +decide [ MulAction.orbit, ConjAct.smul_def ];
        exact fun x => ⟨ fun ⟨ y, hy ⟩ => ⟨ y, hy ⟩, fun ⟨ y, hy ⟩ => ⟨ y, hy ⟩ ⟩;
      rw [ h_class_size, Nat.div_eq_of_eq_mul_left ];
      · exact Fintype.card_pos_iff.mpr ⟨ 1, by simp +decide ⟩;
      · nontriviality;
        exact (MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct G) g).symm;
    have h_class_size : (Fintype.card (MulAction.stabilizer (ConjAct G) g)) = (Fintype.card (Subgroup.centralizer {g})) := by
      simp +decide [ Subgroup.mem_centralizer_iff, ConjAct.smul_def ];
      simp +decide [ mul_inv_eq_iff_eq_mul ];
      exact Fintype.card_congr ( Equiv.subtypeEquivRight fun x => by simp +decide [ eq_comm, ConjAct.ofConjAct ] );
    simp_all +decide [ Subgroup.index ];
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup ( Subgroup.centralizer { g } ) ; aesop;
  convert hω_integral using 1;
  rw [ div_eq_iff ] <;> norm_cast at * <;> simp_all +decide [ NeZero.ne ]

/-! ## Burnside vanishing for coprime factors -/

/-- If G is simple and gcd(d_i, class_size) = 1 with d_i > 1, then χ_i(g) = 0. -/
lemma burnside_vanishing_coprime (G : Type) [Group G] [Fintype G] [DecidableEq G]
    (hsimple : IsSimpleGroup G)
    {n : ℕ} (d : Fin n → ℕ) (hd : ∀ i, NeZero (d i))
    (e : MonoidAlgebra ℂ G ≃ₐ[ℂ] ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (g : G) (hg : g ≠ 1) (i : Fin n)
    (hdim : d i > 1)
    (hcoprime : Nat.Coprime (d i) (Subgroup.centralizer ({g} : Set G)).index)
    (hχ_int : IsIntegral ℤ (Matrix.trace ((e (MonoidAlgebra.single g 1)) i)))
    (hω_int : IsIntegral ℤ ((Subgroup.centralizer ({g} : Set G)).index *
        Matrix.trace ((e (MonoidAlgebra.single g 1)) i) / (d i : ℂ))) :
    Matrix.trace ((e (MonoidAlgebra.single g 1)) i) = 0 := by
  set M := (e (MonoidAlgebra.single g 1)) i
  set χ := Matrix.trace M
  -- M^(orderOf g) = I
  have hM_pow : M ^ (orderOf g) = 1 := by
    have hsingle_pow : (MonoidAlgebra.single g 1 : MonoidAlgebra ℂ G) ^ (orderOf g) = 1 := by
      rw [show (MonoidAlgebra.single g (1:ℂ)) ^ orderOf g = MonoidAlgebra.single (g ^ orderOf g) (1 ^ orderOf g) from MonoidAlgebra.single_pow g 1 (orderOf g)]
      simp [pow_orderOf_eq_one]; exact MonoidAlgebra.ext_iff.mpr (congrFun rfl)
    have hpow_eq : ∀ k : ℕ, (e ((MonoidAlgebra.single g 1) ^ k)) i = M ^ k := by
      intro k; induction k with
      | zero => simp [M]
      | succ n ih =>
        rw [pow_succ, map_mul, pow_succ]
        show (e (MonoidAlgebra.single g 1 ^ n)) i * (e (MonoidAlgebra.single g 1)) i = M ^ n * M
        rw [ih]
    rw [← hpow_eq, hsingle_pow, map_one]; rfl
  have hN : 0 < orderOf g := orderOf_pos g
  have hdi_pos : 0 < d i := Nat.lt_of_lt_of_le (by norm_num) hdim
  have hdi_ne : (d i : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  -- Step 1: α = χ / d i is an algebraic integer
  have hα_int : IsIntegral ℤ (χ / (d i : ℂ)) :=
    Submission.BurnsideVanishingHelpers.integral_of_coprime χ (d i)
      (Subgroup.centralizer ({g} : Set G)).index hdi_ne hχ_int hω_int hcoprime
  -- Step 2: By contradiction, assume χ ≠ 0
  by_contra hχ_ne
  -- Then α ≠ 0
  have hα_ne : χ / (d i : ℂ) ≠ 0 := div_ne_zero hχ_ne hdi_ne
  -- Step 3: ‖α‖ = 1
  have hα_norm : ‖χ / (d i : ℂ)‖ = 1 :=
    Submission.EigenvalueField.norm_one_of_trace_div_dim hdi_pos M (orderOf g) hN hM_pow
      (χ / (d i : ℂ)) rfl hα_int hα_ne
  -- Step 4: ‖χ‖ = d i
  have hχ_norm : ‖χ‖ = (d i : ℝ) := by
    have : (d i : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [norm_div, norm_natCast, div_eq_iff this, one_mul] at hα_norm
    exact hα_norm
  have hχ_norm' : ‖χ‖ = ↑(d i) := hχ_norm
  -- Step 5: M is scalar
  have hscalar := Submission.BurnsideVanishingHelpers.scalar_of_norm_trace_eq_dim
    M (orderOf g) hN hM_pow hχ_norm
  -- Step 6: d i ≤ 1
  have hdi_le := Submission.BurnsideVanishingHelpers.wedderburn_scalar_implies_dim_one
    G hsimple d hd e g hg i hscalar
  -- Step 7: Contradiction
  omega

/-! ## Assembly: prove q⁻¹ is algebraic integer -/

/-
The core character-theoretic argument for Burnside's theorem.
-/
theorem burnside_char_core_proof {G : Type} [Group G] [Fintype G] [DecidableEq G]
    {q k : ℕ} (hq : Nat.Prime q) (hk : 0 < k)
    (g : G) (hg : g ≠ 1)
    (hindex : (Subgroup.centralizer ({g} : Set G)).index = q ^ k)
    (hsimple : IsSimpleGroup G)
    (hnonabelian : ∃ (p : ℕ), p.Prime ∧ p ≠ q ∧ p ∣ Fintype.card G) :
    IsIntegral ℤ ((q : ℂ)⁻¹) := by
  -- Step 1: G is non-abelian
  have hq_dvd : q ∣ Fintype.card G := by
    have := Subgroup.index_dvd_card (Subgroup.centralizer ({g} : Set G))
    rw [Nat.card_eq_fintype_card] at this
    exact dvd_trans (dvd_pow_self q hk.ne') (hindex ▸ this)
  have hnonab := simple_group_nonabelian_of_two_primes hsimple hq hnonabelian hq_dvd
  -- Step 2: G is perfect
  have hperf := simple_nonabelian_commutator_eq_top G hsimple hnonab
  -- Step 3: Get Wedderburn decomposition
  obtain ⟨n, d, hd, ⟨e⟩⟩ := wedderburn_decomp_exists G
  -- Step 4: Column identity
  have hcol := Submission.PeterWeylTrace.wedderburn_column_identity G g hg n d hd e
  -- Step 5: Unique dim-1 factor with character = 1
  obtain ⟨i₀, hi₀⟩ := wedderburn_has_dim1 G d hd e
  have hi₀_char : ∀ g' : G, Matrix.trace ((e (MonoidAlgebra.single g' 1)) i₀) = 1 :=
    wedderburn_dim1_char_eq_one G hperf d hd e i₀ hi₀
  have hi₀_uniq : ∀ j, d j = 1 → j = i₀ :=
    fun j hj => wedderburn_at_most_one_dim1 G hperf d hd e j i₀ hj hi₀
  -- Step 6: Character integrality and class sum eigenvalue integrality
  have hχ_int : ∀ i, IsIntegral ℤ (Matrix.trace ((e (MonoidAlgebra.single g 1)) i)) :=
    fun i => wedderburn_char_isIntegral G d hd e g i
  have hω_int : ∀ i, IsIntegral ℤ ((Subgroup.centralizer ({g} : Set G)).index *
      Matrix.trace ((e (MonoidAlgebra.single g 1)) i) / (d i : ℂ)) :=
    fun i => class_sum_eigenvalue_isIntegral G d hd e g i
  -- Step 7: Vanishing for coprime factors
  have hvanish : ∀ i, d i > 1 →
      Nat.Coprime (d i) (q ^ k) →
      Matrix.trace ((e (MonoidAlgebra.single g 1)) i) = 0 := by
    intro i hdim hcop
    exact burnside_vanishing_coprime G hsimple d hd e g hg i hdim
      (hindex ▸ hcop) (hχ_int i) (hω_int i)
  -- Step 8: Assembly
  -- From column identity: 0 = ∑ d_i · χ_i(g)
  -- Split sum: contribution from i₀ (= 1·1 = 1) + contributions from d_i > 1
  -- For coprime: χ = 0
  -- For non-coprime (q | d_i): d_i · χ_i = q · (d_i/q · χ_i)
  -- So: 0 = 1 + q · ∑_{q|d_i} (d_i/q · χ_i)
  -- Hence: q⁻¹ = -(sum of algebraic integers)
  -- Split the sum at i₀: 0 = d_{i₀} · χ_{i₀} + ∑_{i ≠ i₀} d_i · χ_i.
  have h_split : 0 = (d i₀ : ℂ) * Matrix.trace ((e (MonoidAlgebra.single g 1)) i₀) + ∑ i ∈ Finset.univ.erase i₀, (d i : ℂ) * Matrix.trace ((e (MonoidAlgebra.single g 1)) i) := by
    rw [ ← hcol, ← Finset.sum_erase_add _ _ ( Finset.mem_univ i₀ ), add_comm ];
  -- For each i ≠ i₀: d_i = q * (d_i / q) (since q | d_i).
  have h_div : ∀ i ∈ Finset.univ.erase i₀, q ∣ d i ∨ Matrix.trace ((e (MonoidAlgebra.single g 1)) i) = 0 := by
    intro i hi;
    by_cases hi' : d i > 1;
    · exact Classical.or_iff_not_imp_left.2 fun h => hvanish i hi' <| Nat.Coprime.pow_right _ <| Nat.Coprime.symm <| hq.coprime_iff_not_dvd.2 h;
    · exact False.elim <| Finset.ne_of_mem_erase hi <| hi₀_uniq i <| le_antisymm ( le_of_not_gt hi' ) <| Nat.pos_of_ne_zero <| NeZero.ne _;
  -- So: 0 = 1 + q · ∑_{i ∈ B} (d_i/q) · χ_i.
  have h_sum : 0 = 1 + (q : ℂ) * ∑ i ∈ Finset.univ.erase i₀, (if q ∣ d i then (d i / q : ℂ) * Matrix.trace ((e (MonoidAlgebra.single g 1)) i) else 0) := by
    convert h_split using 2;
    · norm_num [ hi₀, hi₀_char ];
    · rw [ Finset.mul_sum _ _ _ ] ; refine' Finset.sum_congr rfl fun i hi => _ ; specialize h_div i hi ; rcases h_div with ( h | h ) <;> simp +decide [ h ] ;
      rw [ ← mul_assoc, mul_div_cancel₀ _ ( Nat.cast_ne_zero.mpr hq.ne_zero ) ];
  -- Hence: q⁻¹ = -(∑_{i ∈ B} (d_i/q) · χ_i).
  have h_inv : (q : ℂ)⁻¹ = -∑ i ∈ Finset.univ.erase i₀, (if q ∣ d i then (d i / q : ℂ) * Matrix.trace ((e (MonoidAlgebra.single g 1)) i) else 0) := by
    grind +splitImp;
  refine' h_inv ▸ IsIntegral.neg _;
  refine' IsIntegral.sum _ fun i hi => _;
  split_ifs;
  · refine' IsIntegral.mul _ ( hχ_int i );
    refine' ⟨ Polynomial.X - Polynomial.C ( d i / q : ℤ ), _, _ ⟩;
    · exact Polynomial.monic_X_sub_C _;
    · norm_num;
      erw [ Polynomial.eval₂_C ] ; norm_num;
      rw [ sub_eq_zero, div_eq_iff ] <;> norm_cast <;> linarith [ hq.two_le, Nat.div_mul_cancel ‹_› ];
  · exact isIntegral_zero

end Submission.BurnsideVanishing
