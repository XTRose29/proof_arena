import Mathlib
import Submission.Helpers

open Set

namespace Submission

/-ResultProofDefinitionsBegin-/
/-ResultProofDefinitionsEnd-/


theorem mem_convexHull_finset_extremePoints_of_mem_compact_convex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {s : Set E} {x : E}
    (hscomp : IsCompact s)
    (hsconv : Convex ℝ s)
    (hx : x ∈ s) :
    ∃ t : Finset E,
      (↑t : Set E) ⊆ s.extremePoints ℝ ∧
      t.card ≤ Module.finrank ℝ E + 1 ∧
      x ∈ convexHull ℝ (↑t : Set E) := by
  classical
  have aux : ∀ (n : ℕ),
  ∀ (W : Type _) [NormedAddCommGroup W] [NormedSpace ℝ W]
    [FiniteDimensional ℝ W],
    Module.finrank ℝ W = n →
    ∀ (K : Set W), IsCompact K → Convex ℝ K →
      ∀ p ∈ K, p ∈ convexHull ℝ (K.extremePoints ℝ) := by
    classical
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro W _ _ _ hdim K hKc hKv p hp
      -- case of zero direction
      by_cases hzero : vectorSpan ℝ K = (⊥ : Submodule ℝ W)
      · have hone : K = ({p} : Set W) := by
          apply Set.Subset.antisymm
          · intro z hz
            have hm : z -ᵥ p ∈ vectorSpan ℝ K :=
              vsub_mem_vectorSpan ℝ hz hp
            have hm' : z -ᵥ p ∈ (⊥ : Submodule ℝ W) := by
              rw [← hzero]
              exact hm
            have h0 : z -ᵥ p = (0 : W) := by simpa using hm'
            have e : z = p :=
              sub_eq_zero.mp (by simpa [vsub_eq_sub] using h0)
            simpa [e]
          · exact Set.singleton_subset_iff.mpr hp
        rw [hone, extremePoints_singleton]
        exact subset_convexHull ℝ ({p} : Set W) (by simp)
      · -- a reusable reduction for subsets with proper direction
        have reduce_proper : ∀ (L : Set W), IsCompact L → Convex ℝ L →
            ∀ q ∈ L, (vectorSpan ℝ L : Submodule ℝ W) ≠ ⊤ →
              q ∈ convexHull ℝ (L.extremePoints ℝ) := by
          intro L hLc hLv q hq htop
          let V : Submodule ℝ W := vectorSpan ℝ L
          let g : (V : Type _) →ᵃ[ℝ] W :=
            { toFun := fun v => (v : W) + q
              linear := V.subtype
              map_vadd' := by
                intro r v
                change (↑(v + r) : W) + q = (↑v : W) + ((↑r : W) + q)
                simp [add_assoc] }
          have ginj : Function.Injective g := by
            intro v w e
            apply Subtype.ext
            -- addition by q is injective
            have e' : (v : W) + q = (w : W) + q := e
            exact add_right_cancel e'
          let A : Set V := g ⁻¹' L
          have imA : g '' A = L := by
            apply Set.Subset.antisymm
            · rintro z ⟨v, hv, rfl⟩
              exact hv
            · intro z hz
              have hm : z -ᵥ q ∈ vectorSpan ℝ L :=
                vsub_mem_vectorSpan ℝ hz hq
              let v : V := ⟨z - q, by simpa [V, vsub_eq_sub] using hm⟩
              have ev : g v = z := by
                change (z - q) + q = z
                exact sub_add_cancel z q
              refine ⟨v, ?_, ev⟩
              change g v ∈ L
              rw [ev]
              exact hz
          have gc : Topology.IsClosedEmbedding (g : V → W) := by
            have subc : Topology.IsClosedEmbedding ((↑) : V → W) := by
              change Topology.IsClosedEmbedding ((↑) : (↥(vectorSpan ℝ L)) → W)
              exact (vectorSpan ℝ L).closed_of_finiteDimensional.isClosedEmbedding_subtypeVal
            have tr : Topology.IsClosedEmbedding (fun z : W => z + q) :=
              (Homeomorph.addRight q).isClosedEmbedding
            simpa [g, Function.comp_def] using (tr.comp subc)
          have Ac : IsCompact A := by
            change IsCompact (g ⁻¹' L)
            exact gc.isCompact_preimage hLc
          have Av : Convex ℝ A := hLv.affine_preimage g
          let a0 : V := ⟨0, V.zero_mem⟩
          have e0 : g a0 = q := by simp [g, a0]
          have ha0 : a0 ∈ A := by
            change g a0 ∈ L
            simpa [e0] using hq
          have dimV : Module.finrank ℝ V < Module.finrank ℝ W := by
            have lt : (vectorSpan ℝ L : Submodule ℝ W) < ⊤ :=
              lt_top_iff_ne_top.mpr htop
            simpa [V] using (Submodule.finrank_lt_finrank_of_lt lt)
          have haHull : a0 ∈ convexHull ℝ (A.extremePoints ℝ) := by
            have hm : Module.finrank ℝ V < n := by simpa [hdim] using dimV
            exact ih (Module.finrank ℝ V) hm V rfl A Ac Av a0 ha0
          -- images of extreme points by the injection
          have iext : g '' (A.extremePoints ℝ) = (g '' A).extremePoints ℝ := by
            apply Set.Subset.antisymm
            · rintro z ⟨a, ha, rfl⟩
              rw [mem_extremePoints_iff_left] at ha ⊢
              refine ⟨⟨a, ha.1, rfl⟩, ?_⟩
              intro z₁ hz₁ z₂ hz₂ hs
              rcases hz₁ with ⟨b, hb, rfl⟩
              rcases hz₂ with ⟨c, hc, rfl⟩
              have imseg : g '' openSegment ℝ b c = openSegment ℝ (g b) (g c) :=
                image_openSegment ℝ g b c
              have hin : a ∈ openSegment ℝ b c := by
                have him : g a ∈ g '' openSegment ℝ b c := by
                  rw [imseg]
                  exact hs
                rcases him with ⟨r, hr, er⟩
                have er' : r = a := ginj er
                simpa [er'] using hr
              have eb : b = a := ha.2 b hb c hc hin
              simpa [eb]
            · intro z hz
              rw [mem_extremePoints_iff_left] at hz
              rcases hz.1 with ⟨a, ha, rfl⟩
              refine ⟨a, ?_, rfl⟩
              rw [mem_extremePoints_iff_left]
              refine ⟨ha, ?_⟩
              intro b hb c hc hs
              have imseg : g '' openSegment ℝ b c = openSegment ℝ (g b) (g c) :=
                image_openSegment ℝ g b c
              have hgseg : g a ∈ openSegment ℝ (g b) (g c) := by
                rw [← imseg]
                exact ⟨a, hs, rfl⟩
              have e : g b = g a := hz.2 (g b) ⟨b, hb, rfl⟩
                (g c) ⟨c, hc, rfl⟩ hgseg
              exact ginj e
          have him : q ∈ g '' convexHull ℝ (A.extremePoints ℝ) :=
            ⟨a0, haHull, e0⟩
          rw [g.image_convexHull, iext, imA] at him
          exact him
        by_cases htop : (vectorSpan ℝ K : Submodule ℝ W) = ⊤
        · -- full-dimensional
          have afftop : affineSpan ℝ K = (⊤ : AffineSubspace ℝ W) :=
            (AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty
              ℝ W W ⟨p, hp⟩).2 htop
          have intpart : interior K ⊆ convexHull ℝ (K.extremePoints ℝ) := by
            let C : Set W := convexHull ℝ (K.extremePoints ℝ)
            have Cconv : Convex ℝ C := convex_convexHull ℝ _
            have Cclose : closure C = K := by
              dsimp [C]
              exact closure_convexHull_extremePoints hKc hKv
            have Asclosed : IsClosed (affineSpan ℝ C : Set W) :=
              (affineSpan ℝ C).closed_of_finiteDimensional
            have subs : K ⊆ (affineSpan ℝ C : Set W) := by
              rw [← Cclose]
              exact closure_minimal (subset_affineSpan ℝ C) Asclosed
            have Ctop : affineSpan ℝ C = (⊤ : AffineSubspace ℝ W) := by
              apply top_unique
              have hle : affineSpan ℝ K ≤ affineSpan ℝ C :=
                (affineSpan_le).2 subs
              simpa [afftop] using hle
            have ne : (interior C).Nonempty :=
              (Cconv.interior_nonempty_iff_affineSpan_eq_top).2 Ctop
            have eqi : interior (closure C) = interior C :=
              Cconv.interior_closure_eq_interior_of_nonempty_interior ne
            intro z hz
            apply interior_subset
            rw [← eqi, Cclose]
            exact hz
          by_cases hint : p ∈ interior K
          · exact intpart hint
          · -- a proper exposed face
            have Kne : (interior K).Nonempty :=
              (hKv.interior_nonempty_iff_affineSpan_eq_top).2 afftop
            obtain ⟨f, hf⟩ :=
              geometric_hahn_banach_open_point (hKv.interior)
                isOpen_interior hint
            have clint : closure (interior K) = K := by
              calc
                closure (interior K) = closure K :=
                  hKv.closure_interior_eq_closure_of_nonempty_interior Kne
                _ = K := hKc.isClosed.closure_eq
            have leall : ∀ z ∈ K, f z ≤ f p := by
              have hc : IsClosed {z : W | f z ≤ f p} :=
                isClosed_le f.continuous continuous_const
              have hi : closure (interior K) ⊆ {z : W | f z ≤ f p} :=
                closure_minimal (fun z hz => le_of_lt (hf z hz)) hc
              intro z hz
              exact hi (by rw [clint]; exact hz)
            let F : Set W := {z ∈ K | ∀ w ∈ K, f w ≤ f z}
            have Fexp : IsExposed ℝ K F := by
              change IsExposed ℝ K (f.toExposed K)
              exact ContinuousLinearMap.toExposed.isExposed
            have hpF : p ∈ F := ⟨hp, fun w hw => leall w hw⟩
            have Fc : IsCompact F := Fexp.isCompact hKc
            have Fv : Convex ℝ F := Fexp.convex hKv
            have Faff : affineSpan ℝ F ≠ (⊤ : AffineSubspace ℝ W) := by
              intro et
              obtain ⟨z, hz⟩ : (interior F).Nonempty :=
                (Fv.interior_nonempty_iff_affineSpan_eq_top).2 et
              have hzK : z ∈ interior K := interior_mono Fexp.subset hz
              have hzlt : f z < f p := hf z hzK
              have hzge : f p ≤ f z := (interior_subset hz).2 p hp
              exact (not_le_of_gt hzlt) hzge
            have Ftop : (vectorSpan ℝ F : Submodule ℝ W) ≠ ⊤ := by
              intro et
              have eqt : affineSpan ℝ F = (⊤ : AffineSubspace ℝ W) :=
                (AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty
                  ℝ W W ⟨p, hpF⟩).2 et
              exact Faff eqt
            have hpfhull : p ∈ convexHull ℝ (F.extremePoints ℝ) :=
              reduce_proper F Fc Fv p hpF Ftop
            exact (convexHull_mono
              Fexp.isExtreme.extremePoints_subset_extremePoints) hpfhull
        · exact reduce_proper K hKc hKv p hp htop

  have hxHull : x ∈ convexHull ℝ (s.extremePoints ℝ) := by
    exact aux (Module.finrank ℝ E) E rfl s hscomp hsconv x hx
  rw [convexHull_eq_union] at hxHull
  simp only [Set.mem_iUnion] at hxHull
  rcases hxHull with ⟨t, ht, hti, hxt⟩
  refine ⟨t, ht, ?_, hxt⟩
  have hcard := AffineIndependent.card_le_finrank_succ hti
  have hsub : Module.finrank ℝ
        (vectorSpan ℝ (Set.range ((↑) : t → E))) ≤ Module.finrank ℝ E :=
    Submodule.finrank_le (vectorSpan ℝ (Set.range ((↑) : t → E)))
  simpa using (le_trans hcard (Nat.add_le_add_right hsub 1))


end Submission
