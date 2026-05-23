import Mathlib

open Set Finset

namespace Submission.ConvexHullCompact

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The "combination map" from weights × points to their weighted sum. -/
noncomputable def combMap (n : ℕ) : ((Fin n → ℝ) × (Fin n → E)) → E :=
  fun ⟨w, x⟩ => ∑ i : Fin n, w i • x i

theorem continuous_combMap (n : ℕ) : Continuous (combMap (E := E) n) := by
  exact continuous_finset_sum _ fun i _ => Continuous.smul ( continuous_apply i |> Continuous.comp <| continuous_fst ) ( continuous_apply i |> Continuous.comp <| continuous_snd )

/-- The domain: weights in stdSimplex, points in s. -/
def combDomain (n : ℕ) (s : Set E) : Set ((Fin n → ℝ) × (Fin n → E)) :=
  {p | p.1 ∈ stdSimplex ℝ (Fin n) ∧ ∀ i, p.2 i ∈ s}

theorem isCompact_combDomain {s : Set E} (hs : IsCompact s) (n : ℕ) :
    IsCompact (combDomain n s) := by
  -- The set of weights in the standard simplex is compact.
  have h_stdSimplex : IsCompact (stdSimplex ℝ (Fin n)) := by
    exact isCompact_stdSimplex ℝ (Fin n)
  convert h_stdSimplex.prod ( isCompact_univ_pi fun _ : Fin n => hs ) using 1;
  ext ⟨w, x⟩; simp [combDomain]

/-
Image of combDomain is contained in convexHull.
-/
theorem combMap_image_subset {s : Set E} (n : ℕ) :
    combMap n '' combDomain n s ⊆ convexHull ℝ s := by
  rintro _ ⟨ x, hx, rfl ⟩;
  exact ( convex_convexHull ℝ s ).sum_mem ( fun i _ => hx.1.1 i ) ( by simpa using hx.1.2 ) fun i _ => subset_convexHull ℝ s ( hx.2 i )

/-
By Carathéodory, convexHull is contained in the image of combDomain
    with n = finrank + 1.
-/
theorem convexHull_subset_combMap_image {s : Set E} :
    convexHull ℝ s ⊆
      combMap (Module.finrank ℝ E + 1) '' combDomain (Module.finrank ℝ E + 1) s := by
  intro y hy
  obtain ⟨t, ht⟩ : ∃ t : Finset E, s ⊇ t ∧ y ∈ convexHull ℝ t ∧ t.card ≤ Module.finrank ℝ E + 1 := by
    have := @Caratheodory.minCardFinsetOfMemConvexHull_subseteq;
    have := @Caratheodory.mem_minCardFinsetOfMemConvexHull;
    have := @Caratheodory.affineIndependent_minCardFinsetOfMemConvexHull;
    have := @AffineIndependent.card_le_finrank_succ;
    rename_i h₁ h₂ h₃ h₄;
    refine' ⟨ Caratheodory.minCardFinsetOfMemConvexHull hy, h₂ hy, h₃ hy, _ ⟩;
    specialize this ( h₄ hy );
    refine' le_trans _ ( Nat.succ_le_succ ( Submodule.finrank_le _ ) );
    convert this using 1;
    exact Eq.symm (Fintype.card_coe (Caratheodory.minCardFinsetOfMemConvexHull hy));
  -- Since $y \in \text{conv}(t)$, we can write $y$ as a convex combination of points in $t$.
  obtain ⟨w, hw⟩ : ∃ w : E → ℝ, (∀ x ∈ t, 0 ≤ w x) ∧ (∑ x ∈ t, w x = 1) ∧ (∑ x ∈ t, w x • x = y) := by
    have := ht.2.1;
    exact mem_convexHull'.mp this;
  -- Pad the weights and points to have exactly `finrank + 1` elements.
  obtain ⟨pad_t, pad_w, h_pad⟩ : ∃ pad_t : Fin (Module.finrank ℝ E + 1) → E, ∃ pad_w : Fin (Module.finrank ℝ E + 1) → ℝ, (∀ i, pad_t i ∈ s) ∧ (∀ i, 0 ≤ pad_w i) ∧ (∑ i, pad_w i = 1) ∧ (∑ i, pad_w i • pad_t i = y) ∧ (∀ x ∈ t, ∃ i, pad_t i = x) := by
    obtain ⟨pad_t, h_pad_t⟩ : ∃ pad_t : Fin (Module.finrank ℝ E + 1) → E, (∀ i, pad_t i ∈ s) ∧ (∀ x ∈ t, ∃ i, pad_t i = x) := by
      have h_pad : ∃ pad_t : Fin (Module.finrank ℝ E + 1) → E, (∀ i, pad_t i ∈ s) ∧ (∀ x ∈ t, ∃ i, pad_t i = x) := by
        have h_card : ∃ pad_t : Fin t.card → E, (∀ i, pad_t i ∈ s) ∧ (∀ x ∈ t, ∃ i, pad_t i = x) := by
          have h_card : Nonempty (Fin t.card ≃ t) := by
            exact ⟨ Fintype.equivOfCardEq <| by simp +decide ⟩;
          exact ⟨ fun i => h_card.some i |>.1, fun i => ht.1 <| h_card.some i |>.2, fun x hx => ⟨ h_card.some.symm ⟨ x, hx ⟩, by simp +decide ⟩ ⟩
        obtain ⟨pad_t, h_pad_t⟩ := h_card
        obtain ⟨x, hx⟩ : ∃ x ∈ s, True := by
          rcases t.eq_empty_or_nonempty with ( rfl | ⟨ x, hx ⟩ ) <;> aesop;
        refine' ⟨ fun i => if hi : i.val < t.card then pad_t ⟨ i.val, hi ⟩ else x, _, _ ⟩ <;> simp_all +decide;
        · grind;
        · intro x hx; obtain ⟨ i, hi ⟩ := h_pad_t.2 x hx; use ⟨ i, by linarith [ Fin.is_lt i ] ⟩ ; aesop;
      exact h_pad;
    -- Define the padded weights such that they sum to 1 and correspond to the padded points.
    obtain ⟨pad_w, h_pad_w⟩ : ∃ pad_w : Fin (Module.finrank ℝ E + 1) → ℝ, (∀ i, 0 ≤ pad_w i) ∧ (∑ i, pad_w i = 1) ∧ (∑ i, pad_w i • pad_t i = ∑ x ∈ t, w x • x) := by
      choose! f hf using h_pad_t.2;
      refine' ⟨ fun i => ∑ x ∈ t.filter ( fun x => f x = i ), w x, _, _, _ ⟩ <;> simp_all +decide [ Finset.sum_filter ];
      · exact fun i => Finset.sum_nonneg fun x hx => by split_ifs <;> linarith [ hw.1 x hx ] ;
      · rw [ ← hw.2.1, Finset.sum_comm ] ; aesop;
      · simp +decide [ ← hw.2.2, Finset.sum_comm, Finset.sum_smul, hf ];
        exact Finset.sum_congr rfl fun x hx => by rw [ hf x hx ] ;
    exact ⟨ pad_t, pad_w, h_pad_t.1, h_pad_w.1, h_pad_w.2.1, h_pad_w.2.2.trans hw.2.2, h_pad_t.2 ⟩;
  exact ⟨ ⟨ pad_w, pad_t ⟩, ⟨ ⟨ fun i => h_pad.2.1 i, h_pad.2.2.1 ⟩, h_pad.1 ⟩, h_pad.2.2.2.1 ⟩

/-- In a finite-dimensional normed space, the convex hull of a compact set is compact. -/
theorem isCompact_convexHull {s : Set E} (hs : IsCompact s) :
    IsCompact (convexHull ℝ s) := by
  set n := Module.finrank ℝ E + 1
  have h_img_eq : combMap n '' combDomain n s = convexHull ℝ s :=
    le_antisymm (combMap_image_subset n) convexHull_subset_combMap_image
  rw [← h_img_eq]
  exact (isCompact_combDomain hs n).image (continuous_combMap n)

end Submission.ConvexHullCompact