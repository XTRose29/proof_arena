import Mathlib.Tactic
import Submission.PolygonalArcCollarLocalTopologyDataExists
import Submission.PolygonalArcCollarVertexLocalPieceDataExists
import Submission.PolygonalArcInitialEndpointCone
import Submission.PolygonalArcInitialEndpointLeftCone
import Submission.PolygonalArcReverse
import Submission.PolygonalArcTerminalEndpointCone
import Submission.PolygonalArcTerminalEndpointLeftCone

open Set
open Classical
noncomputable section

set_option maxHeartbeats 2200000

-- [TABLET NODE: PolygonalArcCollarLocalTopologyDataWithEndpointCaps]
lemma PolygonalArcCollarLocalTopologyDataWithEndpointCaps (γ : PolygonalArc) {η : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii γ η)
    (middleSegments : PolygonalArcCollarMiddleSegmentData γ controlRadii)
    (forbiddenMargins :
      PolygonalArcCollarMiddleForbiddenMargins γ controlRadii middleSegments)
    (compatibleTubes :
      PolygonalArcCollarCompatibleOrientedTubeData γ controlRadii middleSegments
        forbiddenMargins)
    (r₀ r₁ K₀ K₁ : ℝ) :
    0 < r₀ →
      0 < r₁ →
        0 < K₀ →
          0 < K₁ →
            let hsource : 0 < γ.vertices.length := by
              exact Nat.lt_trans Nat.zero_lt_one γ.length_ge_two
            let hfirst : 0 + 1 < γ.vertices.length := by
              exact γ.length_ge_two
            let itarget : ℕ := γ.vertices.length - 1
            let htarget : itarget < γ.vertices.length := by
              have hlen := γ.length_ge_two
              dsimp [itarget]
              omega
            let jlast : ℕ := γ.vertices.length - 2
            let hlast : jlast + 1 < γ.vertices.length := by
              have hlen := γ.length_ge_two
              dsimp [jlast]
              omega
            controlRadii.radius ⟨0, hsource⟩ < r₀ →
              controlRadii.radius ⟨itarget, htarget⟩ < r₁ →
                compatibleTubes.initialConeBound 0 hfirst < K₀ →
                  compatibleTubes.terminalConeBound jlast hlast < K₁ →
                    ∃ vertexLocalPieces :
                        PolygonalArcCollarVertexLocalPieceData γ controlRadii
                          middleSegments forbiddenMargins
                          compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData,
                      ∃ localTopology :
                        PolygonalArcCollarLocalTopologyData γ controlRadii
                          middleSegments forbiddenMargins compatibleTubes
                          vertexLocalPieces,
                        γ.source ∉ localTopology.vertexCollar ⟨0, hsource⟩ ∧
                          γ.target ∉ localTopology.vertexCollar ⟨itarget, htarget⟩ ∧
                            (localTopology.vertexCollar ⟨0, hsource⟩ \
                                γ.relativeInterior ⊆
                              PolygonalArcInitialEndpointCone γ r₀ K₀) ∧
                              (localTopology.vertexCollar ⟨itarget, htarget⟩ \
                                  γ.relativeInterior ⊆
                                PolygonalArcTerminalEndpointCone γ r₁ K₁) ∧
                                localTopology.leftSidePiece ⟨0, hsource⟩ ⊆
                                  PolygonalArcInitialEndpointLeftCone γ r₀ K₀ ∧
                                  localTopology.leftSidePiece ⟨itarget, htarget⟩ ⊆
                                    PolygonalArcTerminalEndpointLeftCone γ r₁ K₁ ∧
                                    localTopology.rightSidePiece ⟨0, hsource⟩ ⊆
                                      PolygonalArcTerminalEndpointLeftCone
                                        (PolygonalArcReverse γ) r₀ K₀ ∧
                                      localTopology.rightSidePiece
                                          ⟨itarget, htarget⟩ ⊆
                                        PolygonalArcInitialEndpointLeftCone
                                          (PolygonalArcReverse γ) r₁ K₁ ∧
                                        (let E := EuclideanSpace ℝ (Fin 2)
                                         let d0 : E := γ.vertices[1] - γ.vertices[0]
                                         let chart0 : E → E := fun z =>
                                           γ.vertices[0] + z 0 • d0 +
                                             z 1 • PlanarRot90 d0
                                         let a0 : ℝ :=
                                           controlRadii.radius ⟨0, hsource⟩ /
                                             dist γ.vertices[0] γ.vertices[1]
                                         let κ0 : ℝ :=
                                           compatibleTubes.initialConeBound 0 hfirst
                                         let C0 : Set E :=
                                           {z | 0 < z 0 ∧
                                             z 0 ^ 2 + z 1 ^ 2 < a0 ^ 2 ∧
                                             -κ0 * z 0 < z 1 ∧ z 1 < κ0 * z 0}
                                         let L0 : Set E :=
                                           {z | 0 < z 0 ∧
                                             z 0 ^ 2 + z 1 ^ 2 < a0 ^ 2 ∧
                                             0 < z 1 ∧ z 1 < κ0 * z 0}
                                         let R0 : Set E :=
                                           {z | 0 < z 0 ∧
                                             z 0 ^ 2 + z 1 ^ 2 < a0 ^ 2 ∧
                                             -κ0 * z 0 < z 1 ∧ z 1 < 0}
                                         let dT : E :=
                                           γ.vertices[jlast] - γ.vertices[itarget]
                                         let chartT : E → E := fun z =>
                                           γ.vertices[itarget] + z 0 • dT +
                                             z 1 • PlanarRot90 dT
                                         let aT : ℝ :=
                                           controlRadii.radius ⟨itarget, htarget⟩ /
                                             dist γ.vertices[itarget] γ.vertices[jlast]
                                         let κT : ℝ :=
                                           compatibleTubes.terminalConeBound jlast hlast
                                         let CT : Set E :=
                                           {z | 0 < z 0 ∧
                                             z 0 ^ 2 + z 1 ^ 2 < aT ^ 2 ∧
                                             -κT * z 0 < z 1 ∧ z 1 < κT * z 0}
                                         let LT : Set E :=
                                           {z | 0 < z 0 ∧
                                             z 0 ^ 2 + z 1 ^ 2 < aT ^ 2 ∧
                                             0 < z 1 ∧ z 1 < κT * z 0}
                                         let RT : Set E :=
                                           {z | 0 < z 0 ∧
                                             z 0 ^ 2 + z 1 ^ 2 < aT ^ 2 ∧
                                             -κT * z 0 < z 1 ∧ z 1 < 0}
                                         localTopology.vertexCollar ⟨0, hsource⟩ =
                                             chart0 '' C0 ∧
                                           localTopology.leftSidePiece ⟨0, hsource⟩ =
                                             chart0 '' L0 ∧
                                           localTopology.rightSidePiece ⟨0, hsource⟩ =
                                             chart0 '' R0 ∧
                                           localTopology.vertexCollar
                                               ⟨itarget, htarget⟩ = chartT '' CT ∧
                                           localTopology.leftSidePiece
                                               ⟨itarget, htarget⟩ = chartT '' RT ∧
                                           localTopology.rightSidePiece
                                               ⟨itarget, htarget⟩ = chartT '' LT) := by
-- BODY
  intro hr₀ hr₁ hK₀pos hK₁pos
  dsimp
  intro hρ0_lt hρT_lt hKinit_lt hKterm_lt
  rcases PolygonalArcCollarVertexLocalPieceDataExists γ controlRadii middleSegments
      forbiddenMargins
      compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData with
    ⟨vertexLocalPieces⟩
  rcases PolygonalArcCollarLocalTopologyDataExists γ controlRadii middleSegments
      forbiddenMargins compatibleTubes vertexLocalPieces with
    ⟨baseTopology⟩
  let sep :=
    compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData
  let E := EuclideanSpace ℝ (Fin 2)
  -- Keep the endpoint chart witnesses explicit through the topology assembly.
  have chart_image_open (p d : E) (hd : d ≠ 0) (S : Set E) (hS : IsOpen S) :
      IsOpen ((fun z : E => p + z 0 • d + z 1 • PlanarRot90 d) '' S) := by
    let chart : E → E := fun z => p + z 0 • d + z 1 • PlanarRot90 d
    let invCoord : E → E :=
      fun q => WithLp.toLp 2 (fun i : Fin 2 =>
        if i = 0 then inner ℝ (q - p) d / (‖d‖ ^ 2)
        else inner ℝ (q - p) (PlanarRot90 d) / (‖d‖ ^ 2))
    have hinv_cont : Continuous invCoord := by
      have hplain : Continuous fun q : E =>
          (fun i : Fin 2 =>
            if i = 0 then inner ℝ (q - p) d / (‖d‖ ^ 2)
            else inner ℝ (q - p) (PlanarRot90 d) / (‖d‖ ^ 2)) := by
        apply continuous_pi
        intro i
        by_cases hi : i = 0
        · simp [hi]
          fun_prop
        · simp [hi]
          fun_prop
      exact (PiLp.continuous_toLp (p := (2 : ENNReal))
        (β := fun _ : Fin 2 => ℝ)).comp hplain
    have hleft_inv : ∀ z : E, invCoord (chart z) = z := by
      intro z
      have hrepz :
          chart z - p = z 0 • d + z 1 • PlanarRot90 d := by
        dsimp [chart]
        abel
      have hcoeff :=
        PlanarRot90CoefficientUniqueness (d := d) (v := chart z - p)
          hd hrepz
      apply PiLp.ext
      intro i
      fin_cases i
      · simpa [invCoord] using hcoeff.1.symm
      · simpa [invCoord] using hcoeff.2.symm
    have hright_inv : ∀ q : E, chart (invCoord q) = q := by
      intro q
      have hdecomp :
          q - p = (invCoord q) 0 • d + (invCoord q) 1 • PlanarRot90 d := by
        simpa [invCoord] using PlanarRot90Decomposition d (q - p) hd
      calc
        chart (invCoord q) =
            p + ((invCoord q) 0 • d + (invCoord q) 1 • PlanarRot90 d) := by
          dsimp [chart]
          abel
        _ = p + (q - p) := by rw [← hdecomp]
        _ = q := by abel
    have himage_eq_preimage (T : Set E) :
        chart '' T = invCoord ⁻¹' T := by
      ext q
      constructor
      · rintro ⟨z, hz, rfl⟩
        simpa [hleft_inv z] using hz
      · intro hq
        exact ⟨invCoord q, hq, hright_inv q⟩
    change IsOpen (chart '' S)
    rw [himage_eq_preimage S]
    exact hS.preimage hinv_cont
  have chart_injective (p d : E) (hd : d ≠ 0) :
      Function.Injective
        (fun z : E => p + z 0 • d + z 1 • PlanarRot90 d) := by
    let chart : E → E := fun z => p + z 0 • d + z 1 • PlanarRot90 d
    change Function.Injective chart
    intro z w hzw
    have hrepz :
        chart z - p = z 0 • d + z 1 • PlanarRot90 d := by
      dsimp [chart]
      abel
    have hrepw :
        chart z - p = w 0 • d + w 1 • PlanarRot90 d := by
      rw [hzw]
      dsimp [chart]
      abel
    have hcoeffz :=
      PlanarRot90CoefficientUniqueness (d := d) (v := chart z - p) hd hrepz
    have hcoeffw :=
      PlanarRot90CoefficientUniqueness (d := d) (v := chart z - p) hd hrepw
    have hz0 : z 0 = w 0 := by
      rw [hcoeffz.1, hcoeffw.1]
    have hz1 : z 1 = w 1 := by
      rw [hcoeffz.2, hcoeffw.2]
    apply PiLp.ext
    intro k
    fin_cases k
    · exact hz0
    · exact hz1
  have chart_continuous (p d : E) :
      Continuous (fun z : E => p + z 0 • d + z 1 • PlanarRot90 d) := by
    have h0 : Continuous fun z : E => z 0 :=
      PiLp.continuous_apply (p := (2 : ENNReal)) (β := fun _ : Fin 2 => ℝ) 0
    have h1 : Continuous fun z : E => z 1 :=
      PiLp.continuous_apply (p := (2 : ENNReal)) (β := fun _ : Fin 2 => ℝ) 1
    have hp : Continuous fun _ : E => p := continuous_const
    have hd : Continuous fun _ : E => d := continuous_const
    have hrot : Continuous fun _ : E => PlanarRot90 d := continuous_const
    exact (hp.add (h0.smul hd)).add (h1.smul hrot)
  have chart_mem_closure_image (p d : E) {S : Set E} {z : E}
      (hz : z ∈ closure S) :
      p + z 0 • d + z 1 • PlanarRot90 d ∈
        closure ((fun z : E => p + z 0 • d + z 1 • PlanarRot90 d) '' S) := by
    exact
      (image_closure_subset_closure_image
        (f := fun z : E => p + z 0 • d + z 1 • PlanarRot90 d)
        (s := S) (chart_continuous p d)) ⟨z, hz, rfl⟩
  have image_disjoint_of_injective {f : E → E} (hf : Function.Injective f)
      {A B : Set E} (hAB : Disjoint A B) :
      Disjoint (f '' A) (f '' B) := by
    rw [Set.disjoint_left]
    rintro q ⟨x, hxA, rfl⟩ ⟨y, hyB, hyx⟩
    have hy_eq : y = x := hf hyx
    rw [hy_eq] at hyB
    exact (Set.disjoint_left.mp hAB) hxA hyB
  have chart_axis_eq_lineMap
      (p0 p1 z : EuclideanSpace ℝ (Fin 2)) (hz : z 1 = 0) :
      p0 + z 0 • (p1 - p0) + z 1 • PlanarRot90 (p1 - p0) =
        AffineMap.lineMap p0 p1 (z 0) := by
    apply PiLp.ext
    intro k
    fin_cases k <;>
      simp [AffineMap.lineMap_apply_module, PlanarRot90, hz] <;>
      ring
  have chart_axis_param_eq_lineMap
      (p0 p1 : EuclideanSpace ℝ (Fin 2)) (t : ℝ) :
      p0 + t • (p1 - p0) =
        AffineMap.lineMap p0 p1 t := by
    apply PiLp.ext
    intro k
    fin_cases k <;>
      simp [AffineMap.lineMap_apply_module] <;>
      ring
  have endpoint_germ_subset_closure_left (a K : ℝ) (ha : 0 < a) (hK : 0 < K) :
      let L : Set E :=
        {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < a ^ 2 ∧ 0 < z 1 ∧
          z 1 < K * z 0}
      let G : Set E :=
        {z | 0 < z 0 ∧ z 0 < a ∧ z 1 = 0}
      G ⊆ closure L := by
    intro L G z hzG
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hz0 : 0 < z 0 := by simpa [G] using hzG.1
    have hza : z 0 < a := by simpa [G] using hzG.2.1
    have hz1 : z 1 = 0 := by simpa [G] using hzG.2.2
    have hmargin : 0 < a ^ 2 - z 0 ^ 2 := by nlinarith
    let δ : ℝ :=
      min (min (ε / 2) (K * z 0 / 2)) (min (1 / 2) ((a ^ 2 - z 0 ^ 2) / 2))
    have hδ_pos : 0 < δ := by
      dsimp [δ]
      positivity
    have hδ_eps : δ < ε := by
      have hδ_le : δ ≤ ε / 2 := by
        dsimp [δ]
        exact le_trans (min_le_left _ _) (min_le_left _ _)
      linarith
    have hδ_K : δ < K * z 0 := by
      have hδ_le : δ ≤ K * z 0 / 2 := by
        dsimp [δ]
        exact le_trans (min_le_left _ _) (min_le_right _ _)
      nlinarith [mul_pos hK hz0]
    have hδ_sq : δ ^ 2 < a ^ 2 - z 0 ^ 2 := by
      have hδ_le_half : δ ≤ (a ^ 2 - z 0 ^ 2) / 2 := by
        dsimp [δ]
        exact le_trans (min_le_right _ _) (min_le_right _ _)
      have hδ_le_one : δ ≤ 1 / 2 := by
        dsimp [δ]
        exact le_trans (min_le_right _ _) (min_le_left _ _)
      nlinarith [hδ_pos, hδ_le_half, hδ_le_one, hmargin]
    let y : E := WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then z 0 else δ)
    refine ⟨y, ?_, ?_⟩
    · dsimp [L, y]
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa using hz0
      · nlinarith
      · simp [hδ_pos]
      · simp [hδ_K]
    · rw [EuclideanSpace.dist_eq]
      rw [Fin.sum_univ_two]
      simp [y, hz1, Real.dist_eq]
      rw [Real.sqrt_sq_eq_abs, abs_of_pos hδ_pos]
      exact hδ_eps
  have endpoint_germ_subset_closure_right (a K : ℝ) (ha : 0 < a) (hK : 0 < K) :
      let R : Set E :=
        {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < a ^ 2 ∧ -K * z 0 < z 1 ∧
          z 1 < 0}
      let G : Set E :=
        {z | 0 < z 0 ∧ z 0 < a ∧ z 1 = 0}
      G ⊆ closure R := by
    intro R G z hzG
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hz0 : 0 < z 0 := by simpa [G] using hzG.1
    have hza : z 0 < a := by simpa [G] using hzG.2.1
    have hz1 : z 1 = 0 := by simpa [G] using hzG.2.2
    have hmargin : 0 < a ^ 2 - z 0 ^ 2 := by nlinarith
    let δ : ℝ :=
      min (min (ε / 2) (K * z 0 / 2)) (min (1 / 2) ((a ^ 2 - z 0 ^ 2) / 2))
    have hδ_pos : 0 < δ := by
      dsimp [δ]
      positivity
    have hδ_eps : δ < ε := by
      have hδ_le : δ ≤ ε / 2 := by
        dsimp [δ]
        exact le_trans (min_le_left _ _) (min_le_left _ _)
      linarith
    have hδ_K : δ < K * z 0 := by
      have hδ_le : δ ≤ K * z 0 / 2 := by
        dsimp [δ]
        exact le_trans (min_le_left _ _) (min_le_right _ _)
      nlinarith [mul_pos hK hz0]
    have hδ_sq : δ ^ 2 < a ^ 2 - z 0 ^ 2 := by
      have hδ_le_half : δ ≤ (a ^ 2 - z 0 ^ 2) / 2 := by
        dsimp [δ]
        exact le_trans (min_le_right _ _) (min_le_right _ _)
      have hδ_le_one : δ ≤ 1 / 2 := by
        dsimp [δ]
        exact le_trans (min_le_right _ _) (min_le_left _ _)
      nlinarith [hδ_pos, hδ_le_half, hδ_le_one, hmargin]
    let y : E := WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then z 0 else -δ)
    refine ⟨y, ?_, ?_⟩
    · dsimp [R, y]
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa using hz0
      · nlinarith
      · simp
        nlinarith
      · simp [hδ_pos]
    · rw [EuclideanSpace.dist_eq]
      rw [Fin.sum_univ_two]
      simp [y, hz1, Real.dist_eq, abs_of_pos hδ_pos]
      rw [Real.sqrt_sq_eq_abs, abs_of_pos hδ_pos]
      exact hδ_eps
  have leftHalf_inter_subset_of_nonincident
      (i : Fin γ.vertices.length) (C L : Set E)
      (hCsub : C ⊆ vertexLocalPieces.vertexDisk i)
      (j : ℕ) (hj : j + 1 < γ.vertices.length)
      (hne_left : i.1 ≠ j) (hne_right : i.1 ≠ j + 1) :
      sep.leftHalf j hj ∩ C ⊆ L := by
    intro x hx
    exfalso
    have hdisj :=
      vertexLocalPieces.vertexDisk_disjoint_nonincident_tubes i j hj
        hne_left hne_right
    have hxDisk : x ∈ vertexLocalPieces.vertexDisk i := hCsub hx.2
    have hxTube : x ∈ sep.tube j hj := sep.leftHalf_subset_tube j hj hx.1
    exact (Set.disjoint_left.mp hdisj) hxDisk hxTube
  have rightHalf_inter_subset_of_nonincident
      (i : Fin γ.vertices.length) (C R : Set E)
      (hCsub : C ⊆ vertexLocalPieces.vertexDisk i)
      (j : ℕ) (hj : j + 1 < γ.vertices.length)
      (hne_left : i.1 ≠ j) (hne_right : i.1 ≠ j + 1) :
      sep.rightHalf j hj ∩ C ⊆ R := by
    intro x hx
    exfalso
    have hdisj :=
      vertexLocalPieces.vertexDisk_disjoint_nonincident_tubes i j hj
        hne_left hne_right
    have hxDisk : x ∈ vertexLocalPieces.vertexDisk i := hCsub hx.2
    have hxTube : x ∈ sep.tube j hj := sep.rightHalf_subset_tube j hj hx.1
    exact (Set.disjoint_left.mp hdisj) hxDisk hxTube
  let GoodCore (i : Fin γ.vertices.length) (C L R : Set E) : Prop :=
    IsOpen C ∧ IsOpen L ∧ IsOpen R ∧
      C ⊆ vertexLocalPieces.vertexDisk i ∧
      (0 < i.1 → i.1 + 1 < γ.vertices.length →
        C = vertexLocalPieces.vertexDisk i) ∧
      ((i.1 = 0 ∨ i.1 + 1 = γ.vertices.length) →
        γ.vertices[i.1] ∉ C) ∧
      L ⊆ C ∧ R ⊆ C ∧
      IsConnected L ∧ IsConnected R ∧
      Disjoint L γ.carrier ∧ Disjoint R γ.carrier ∧
      Disjoint L R ∧
      (∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        sep.leftHalf j hj ∩ C ⊆ L) ∧
      (∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        sep.rightHalf j hj ∩ C ⊆ R) ∧
      C \ γ.relativeInterior = L ∪ R ∧
      (∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        i = ⟨j, Nat.lt_of_succ_lt hj⟩ →
          (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1]) ''
              Set.Ioo (0 : ℝ)
                (controlRadii.radius ⟨j, Nat.lt_of_succ_lt hj⟩ /
                  dist γ.vertices[j] γ.vertices[j + 1]) ⊆ C) ∧
      (∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        i = ⟨j + 1, hj⟩ →
          (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1]) ''
              Set.Ioo
                (1 - controlRadii.radius ⟨j + 1, hj⟩ /
                  dist γ.vertices[j] γ.vertices[j + 1]) (1 : ℝ) ⊆ C) ∧
      (∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        i = ⟨j, Nat.lt_of_succ_lt hj⟩ →
          vertexLocalPieces.outgoingLeftAttachment j hj ⊆ L) ∧
      (∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        i = ⟨j, Nat.lt_of_succ_lt hj⟩ →
          vertexLocalPieces.outgoingRightAttachment j hj ⊆ R) ∧
      (∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        i = ⟨j + 1, hj⟩ →
          vertexLocalPieces.incomingLeftAttachment j hj ⊆ L) ∧
      (∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        i = ⟨j + 1, hj⟩ →
          vertexLocalPieces.incomingRightAttachment j hj ⊆ R)
      ∧
      (∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        i = ⟨j, Nat.lt_of_succ_lt hj⟩ →
          (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1]) ''
              Set.Ioo (0 : ℝ)
                (controlRadii.radius ⟨j, Nat.lt_of_succ_lt hj⟩ /
                  dist γ.vertices[j] γ.vertices[j + 1]) ⊆ closure L) ∧
      (∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        i = ⟨j, Nat.lt_of_succ_lt hj⟩ →
          (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1]) ''
              Set.Ioo (0 : ℝ)
                (controlRadii.radius ⟨j, Nat.lt_of_succ_lt hj⟩ /
                  dist γ.vertices[j] γ.vertices[j + 1]) ⊆ closure R) ∧
      (∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        i = ⟨j + 1, hj⟩ →
          (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1]) ''
              Set.Ioo
                (1 - controlRadii.radius ⟨j + 1, hj⟩ /
                  dist γ.vertices[j] γ.vertices[j + 1]) (1 : ℝ) ⊆ closure L) ∧
      (∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        i = ⟨j + 1, hj⟩ →
          (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1]) ''
              Set.Ioo
                (1 - controlRadii.radius ⟨j + 1, hj⟩ /
                  dist γ.vertices[j] γ.vertices[j + 1]) (1 : ℝ) ⊆ closure R) ∧
      (0 < i.1 → i.1 + 1 < γ.vertices.length →
        γ.vertices[i.1] ∈ closure L) ∧
      (0 < i.1 → i.1 + 1 < γ.vertices.length →
        γ.vertices[i.1] ∈ closure R)
  have hlen_two : 2 ≤ γ.vertices.length := γ.length_ge_two
  have hlen_pos : 0 < γ.vertices.length := by omega
  have hj0 : 0 + 1 < γ.vertices.length := by omega
  let lastJ : ℕ := γ.vertices.length - 2
  have hlastJ : lastJ + 1 < γ.vertices.length := by
    dsimp [lastJ]
    omega
  have hlastJ_succ : lastJ + 2 = γ.vertices.length := by
    dsimp [lastJ]
    omega
  have hsource_vertex : γ.vertices[0] = γ.source := by
    have hget : γ.vertices[0]? = some γ.vertices[0] :=
      List.getElem?_eq_getElem hlen_pos
    rw [← List.head?_eq_getElem?, γ.source_eq_head] at hget
    exact Option.some.inj hget.symm
  let d0 : E := γ.vertices[0 + 1] - γ.vertices[0]
  let K0 : ℝ := compatibleTubes.initialConeBound 0 hj0
  let chart0 : E → E :=
    fun z => γ.vertices[0] + z 0 • d0 + z 1 • PlanarRot90 d0
  let a0 : ℝ :=
    controlRadii.radius ⟨0, Nat.lt_of_succ_lt hj0⟩ /
      dist γ.vertices[0] γ.vertices[0 + 1]
  let C0 : Set E :=
    {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < a0 ^ 2 ∧ -K0 * z 0 < z 1 ∧
      z 1 < K0 * z 0}
  let L0 : Set E :=
    {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < a0 ^ 2 ∧ 0 < z 1 ∧
      z 1 < K0 * z 0}
  let R0 : Set E :=
    {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < a0 ^ 2 ∧ -K0 * z 0 < z 1 ∧
      z 1 < 0}
  let dT : E := γ.vertices[lastJ] - γ.vertices[lastJ + 1]
  let KT : ℝ := compatibleTubes.terminalConeBound lastJ hlastJ
  let chartT : E → E :=
    fun z => γ.vertices[lastJ + 1] + z 0 • dT + z 1 • PlanarRot90 dT
  let aT : ℝ :=
    controlRadii.radius ⟨lastJ + 1, hlastJ⟩ /
      dist γ.vertices[lastJ + 1] γ.vertices[lastJ]
  let CT : Set E :=
    {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < aT ^ 2 ∧ -KT * z 0 < z 1 ∧
      z 1 < KT * z 0}
  let LT : Set E :=
    {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < aT ^ 2 ∧ 0 < z 1 ∧
      z 1 < KT * z 0}
  let RT : Set E :=
    {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < aT ^ 2 ∧ -KT * z 0 < z 1 ∧
      z 1 < 0}
  have hGoodInitial :
      ∃ C L R : Set E,
        GoodCore ⟨0, hlen_pos⟩ C L R ∧
          ((0 : ℕ) = 0 →
            C \ γ.relativeInterior ⊆ PolygonalArcInitialEndpointCone γ r₀ K₀) ∧
          ((0 : ℕ) + 1 = γ.vertices.length →
            C \ γ.relativeInterior ⊆ PolygonalArcTerminalEndpointCone γ r₁ K₁) ∧
          ((0 : ℕ) = 0 →
            L ⊆ PolygonalArcInitialEndpointLeftCone γ r₀ K₀) ∧
          ((0 : ℕ) + 1 = γ.vertices.length →
            L ⊆ PolygonalArcTerminalEndpointLeftCone γ r₁ K₁) ∧
          ((0 : ℕ) = 0 →
            R ⊆ PolygonalArcTerminalEndpointLeftCone (PolygonalArcReverse γ) r₀ K₀) ∧
          ((0 : ℕ) + 1 = γ.vertices.length →
            R ⊆ PolygonalArcInitialEndpointLeftCone (PolygonalArcReverse γ) r₁ K₁) ∧
          ((0 : ℕ) = 0 → C = chart0 '' C0) ∧
          ((0 : ℕ) = 0 → L = chart0 '' L0) ∧
          ((0 : ℕ) = 0 → R = chart0 '' R0) ∧
          ((0 : ℕ) + 1 = γ.vertices.length → C = chartT '' CT) ∧
          ((0 : ℕ) + 1 = γ.vertices.length → L = chartT '' RT) ∧
          ((0 : ℕ) + 1 = γ.vertices.length → R = chartT '' LT) := by
    let G0 : Set E :=
      {z | 0 < z 0 ∧ z 0 < a0 ∧ z 1 = 0}
    have hside :=
      PolygonalArcInitialEndpointDiskCappedTaperSideLabelling γ controlRadii
        middleSegments forbiddenMargins compatibleTubes 0 hj0
    change
      0 < a0 ∧
        IsOpen C0 ∧ IsOpen L0 ∧ IsOpen R0 ∧
        IsConnected L0 ∧ IsConnected R0 ∧
        IsConnected (chart0 '' L0) ∧ IsConnected (chart0 '' R0) ∧
        Disjoint L0 R0 ∧ Disjoint (chart0 '' L0) (chart0 '' R0) ∧
        (0 : E) ∉ C0 ∧ G0 ⊆ C0 ∧ C0 \ G0 = L0 ∪ R0 ∧
        (∀ z : E,
          z 0 ^ 2 + z 1 ^ 2 < a0 ^ 2 →
            chart0 z ∈ Metric.ball γ.vertices[0]
              (controlRadii.radius ⟨0, Nat.lt_of_succ_lt hj0⟩)) ∧
        chart0 '' C0 ⊆ Metric.ball γ.vertices[0]
          (controlRadii.radius ⟨0, Nat.lt_of_succ_lt hj0⟩) ∧
        γ.vertices[0] ∉ chart0 '' C0 ∧
        (∀ {t : ℝ}, 0 < t →
          chart0 (WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then t else 0)) ≠
            γ.vertices[0]) ∧
        ((AffineMap.lineMap γ.vertices[0] γ.vertices[0 + 1]) ''
            Set.Ioo (0 : ℝ) a0 ⊆ chart0 '' G0) ∧
        chart0 '' C0 \ chart0 '' G0 = chart0 '' L0 ∪ chart0 '' R0 ∧
        sep.leftHalf 0 hj0 ∩ chart0 '' C0 ⊆ chart0 '' L0 ∧
        sep.rightHalf 0 hj0 ∩ chart0 '' C0 ⊆ chart0 '' R0 at hside
    rcases hside with
      ⟨ha0, hC0open, hL0open, hR0open, hL0conn, hR0conn, hchartL0conn,
        hchartR0conn, hLR0disj, hchartLR0disj, hzero0_not_C, hG0subC,
        hmodel_split, hdisk_coord, hchartC0_ball, hvertex0_not_chartC,
        hcoord0_omit, hgerm0, himage_split0, hleft0, hright0⟩
    have hattach :=
      PolygonalArcInitialEndpointDiskCappedTaperAttachmentStrengthening γ
        controlRadii middleSegments forbiddenMargins compatibleTubes 0 hj0
    change
      sep.leftHalf 0 hj0 ∩
          Metric.ball γ.vertices[0]
            (controlRadii.radius ⟨0, Nat.lt_of_succ_lt hj0⟩) ⊆
        chart0 '' L0 ∧
      sep.rightHalf 0 hj0 ∩
          Metric.ball γ.vertices[0]
            (controlRadii.radius ⟨0, Nat.lt_of_succ_lt hj0⟩) ⊆
        chart0 '' R0 at hattach
    rcases hattach with ⟨hleft0_ball, hright0_ball⟩
    have hdist0 : 0 < dist γ.vertices[0] γ.vertices[0 + 1] := by
      have hsum := controlRadii.adjacent_radii_sum_lt (j := 0) hj0
      have hleft := controlRadii.radius_pos ⟨0, Nat.lt_of_succ_lt hj0⟩
      have hright := controlRadii.radius_pos ⟨0 + 1, hj0⟩
      simpa using lt_trans (add_pos hleft hright) hsum
    have hd0 : d0 ≠ 0 := by
      dsimp [d0]
      have hdist0' : 0 < dist γ.vertices[0] γ.vertices[1] := by
        simpa using hdist0
      exact sub_ne_zero.mpr (dist_pos.mp (by simpa using hdist0')).symm
    have hK0 : 0 < K0 := by
      dsimp [K0]
      exact compatibleTubes.initialConeBound_pos 0 hj0
    have hCsub_disk :
        chart0 '' C0 ⊆ vertexLocalPieces.vertexDisk ⟨0, hlen_pos⟩ := by
      intro x hx
      rw [vertexLocalPieces.vertexDisk_eq]
      simpa using hchartC0_ball hx
    have hLsubC : chart0 '' L0 ⊆ chart0 '' C0 := by
      rintro x ⟨z, hz, rfl⟩
      refine ⟨z, ?_, rfl⟩
      dsimp [L0, C0] at hz ⊢
      exact ⟨hz.1, hz.2.1, by nlinarith [hK0, hz.1, hz.2.2.1], hz.2.2.2⟩
    have hRsubC : chart0 '' R0 ⊆ chart0 '' C0 := by
      rintro x ⟨z, hz, rfl⟩
      refine ⟨z, ?_, rfl⟩
      dsimp [R0, C0] at hz ⊢
      exact ⟨hz.1, hz.2.1, hz.2.2.1, by nlinarith [hK0, hz.1, hz.2.2.2]⟩
    have hchart0_inj : Function.Injective chart0 := by
      dsimp [chart0]
      exact chart_injective γ.vertices[0] d0 hd0
    have hLG0disj : Disjoint L0 G0 := by
      rw [Set.disjoint_left]
      intro z hzL hzG
      dsimp [L0] at hzL
      dsimp [G0] at hzG
      linarith [hzL.2.2.1, hzG.2.2]
    have hRG0disj : Disjoint R0 G0 := by
      rw [Set.disjoint_left]
      intro z hzR hzG
      dsimp [R0] at hzR
      dsimp [G0] at hzG
      linarith [hzR.2.2.2, hzG.2.2]
    have hchartLG0disj : Disjoint (chart0 '' L0) (chart0 '' G0) :=
      image_disjoint_of_injective hchart0_inj hLG0disj
    have hchartRG0disj : Disjoint (chart0 '' R0) (chart0 '' G0) :=
      image_disjoint_of_injective hchart0_inj hRG0disj
    have ha0_lt_one : a0 < 1 := by
      have hrad_lt_dist :
          controlRadii.radius ⟨0, Nat.lt_of_succ_lt hj0⟩ <
            dist γ.vertices[0] γ.vertices[0 + 1] := by
        have hsum := controlRadii.adjacent_radii_sum_lt (j := 0) hj0
        have hright := controlRadii.radius_pos ⟨0 + 1, hj0⟩
        linarith
      have hdist0R : (0 : ℝ) < dist γ.vertices[0] γ.vertices[0 + 1] := by
        simpa using hdist0
      dsimp [a0]
      rw [div_lt_iff₀ hdist0R]
      simpa using hrad_lt_dist
    have hG0_subset_relint : chart0 '' G0 ⊆ γ.relativeInterior := by
      rintro x ⟨z, hzG, rfl⟩
      have hz01 : z 0 ∈ Set.Ioo (0 : ℝ) (1 : ℝ) := by
        dsimp [G0] at hzG
        exact ⟨hzG.1, lt_trans hzG.2.1 ha0_lt_one⟩
      have hline_chart :
          chart0 z = AffineMap.lineMap γ.vertices[0] γ.vertices[0 + 1] (z 0) := by
        dsimp [G0] at hzG
        simpa [chart0, d0] using
          chart_axis_eq_lineMap γ.vertices[0] γ.vertices[0 + 1] z hzG.2.2
      rw [hline_chart]
      exact PolygonalArcOpenSegmentSubsetRelativeInterior γ 0 hj0
        (lineMap_mem_openSegment (𝕜 := ℝ) γ.vertices[0] γ.vertices[0 + 1] hz01)
    have hcarrier_chartC_subset_G :
        γ.carrier ∩ chart0 '' C0 ⊆ chart0 '' G0 := by
      rintro x ⟨hxcarrier, hxC⟩
      have hxDisk : x ∈ vertexLocalPieces.vertexDisk ⟨0, hlen_pos⟩ :=
        hCsub_disk hxC
      rcases vertexLocalPieces.vertexDisk_carrier_subset_incident_segments
          ⟨0, hlen_pos⟩ x hxDisk hxcarrier with
        ⟨j, hj, hxseg, hincident⟩
      have hj_eq : j = 0 := by
        rcases hincident with hleft_inc | hright_inc
        · have : (0 : ℕ) = j := by simpa using hleft_inc
          exact this.symm
        · have : (0 : ℕ) = j + 1 := by simpa using hright_inc
          omega
      subst j
      rw [segment_eq_image_lineMap] at hxseg
      rcases hxseg with ⟨t, ht, htx⟩
      rcases hxC with ⟨z, hzC, hzx⟩
      let zt : E := WithLp.toLp 2 (fun k : Fin 2 => if k = 0 then t else 0)
      have hline_chart :
          chart0 zt = AffineMap.lineMap γ.vertices[0] γ.vertices[0 + 1] t := by
        simpa [chart0, d0, zt] using
          chart_axis_param_eq_lineMap γ.vertices[0] γ.vertices[0 + 1] t
      have hz_eq : z = zt := by
        apply hchart0_inj
        rw [hzx, ← htx, ← hline_chart]
      have hztC : zt ∈ C0 := by
        simpa [hz_eq] using hzC
      have ht_pos : 0 < t := by
        dsimp [C0, zt] at hztC
        simpa [zt] using hztC.1
      have ht_sq : t ^ 2 < a0 ^ 2 := by
        dsimp [C0, zt] at hztC
        simpa [zt] using hztC.2.1
      have ht_lt_a0 : t < a0 := by
        nlinarith [ha0, ht_pos, ht_sq]
      refine ⟨zt, ?_, ?_⟩
      · dsimp [G0, zt]
        exact ⟨by simpa [zt] using ht_pos, by simpa [zt] using ht_lt_a0,
          by simp [zt]⟩
      · rw [hline_chart, htx]
    have hrel_subset_carrier : γ.relativeInterior ⊆ γ.carrier := by
      intro x hx
      rw [γ.relativeInterior_eq] at hx
      exact hx.1
    have hwithout0 :
        chart0 '' C0 \ γ.relativeInterior = chart0 '' L0 ∪ chart0 '' R0 := by
      calc
        chart0 '' C0 \ γ.relativeInterior = chart0 '' C0 \ chart0 '' G0 := by
          ext x
          constructor
          · rintro ⟨hxC, hxnotRel⟩
            exact ⟨hxC, fun hxG => hxnotRel (hG0_subset_relint hxG)⟩
          · rintro ⟨hxC, hxnotG⟩
            exact ⟨hxC, fun hxRel =>
              hxnotG (hcarrier_chartC_subset_G ⟨hrel_subset_carrier hxRel, hxC⟩)⟩
        _ = chart0 '' L0 ∪ chart0 '' R0 := himage_split0
    have hchartC0_subset_initialCone :
        chart0 '' C0 ⊆ PolygonalArcInitialEndpointCone γ r₀ K₀ := by
      rintro x ⟨z, hzC, rfl⟩
      rw [PolygonalArcInitialEndpointCone]
      refine ⟨z, ?_, ?_⟩
      · dsimp [C0] at hzC
        rcases hzC with ⟨hz0, hzdisk, hzlow, hzhigh⟩
        refine ⟨hz0, ?_, ?_, ?_⟩
        · have hρ0_lt' :
              controlRadii.radius ⟨0, Nat.lt_of_succ_lt hj0⟩ < r₀ := by
            simpa using hρ0_lt
          have hDpos : 0 < dist γ.source γ.vertices[1] := by
            simpa [hsource_vertex] using hdist0
          have hDposR : (0 : ℝ) < dist γ.source γ.vertices[1] := by
            simpa using hDpos
          have ha0_lt : a0 < r₀ / dist γ.source γ.vertices[1] := by
            dsimp [a0]
            have hD_eq :
                dist γ.vertices[0] γ.vertices[0 + 1] =
                  dist γ.source γ.vertices[1] := by
              simp [hsource_vertex]
            rw [hD_eq]
            exact div_lt_div_of_pos_right hρ0_lt' hDposR
          have hratio_pos : (0 : ℝ) < r₀ / dist γ.source γ.vertices[1] := by
            exact div_pos hr₀ hDposR
          nlinarith
        · have hK_lt : K0 < K₀ := by
            simpa [K0] using hKinit_lt
          nlinarith [hK_lt, hK₀pos, hz0, hzlow]
        · have hK_lt : K0 < K₀ := by
            simpa [K0] using hKinit_lt
          nlinarith [hK_lt, hz0, hzhigh]
      · dsimp [chart0, d0]
        simp [hsource_vertex]
    have hchartL0_subset_initialLeftCone :
        chart0 '' L0 ⊆ PolygonalArcInitialEndpointLeftCone γ r₀ K₀ := by
      rintro x ⟨z, hzL, rfl⟩
      rw [PolygonalArcInitialEndpointLeftCone]
      refine ⟨z, ?_, ?_⟩
      · dsimp [L0] at hzL
        rcases hzL with ⟨hz0, hzdisk, hzpos, hzhigh⟩
        refine ⟨hz0, ?_, hzpos, ?_⟩
        · have hρ0_lt' :
              controlRadii.radius ⟨0, Nat.lt_of_succ_lt hj0⟩ < r₀ := by
            simpa using hρ0_lt
          have hDpos : 0 < dist γ.source γ.vertices[1] := by
            simpa [hsource_vertex] using hdist0
          have hDposR : (0 : ℝ) < dist γ.source γ.vertices[1] := by
            simpa using hDpos
          have ha0_lt : a0 < r₀ / dist γ.source γ.vertices[1] := by
            dsimp [a0]
            have hD_eq :
                dist γ.vertices[0] γ.vertices[0 + 1] =
                  dist γ.source γ.vertices[1] := by
              simp [hsource_vertex]
            rw [hD_eq]
            exact div_lt_div_of_pos_right hρ0_lt' hDposR
          have hratio_pos : (0 : ℝ) < r₀ / dist γ.source γ.vertices[1] := by
            exact div_pos hr₀ hDposR
          nlinarith
        · have hK_lt : K0 < K₀ := by
            simpa [K0] using hKinit_lt
          nlinarith [hK_lt, hz0, hzhigh]
      · dsimp [chart0, d0]
        simp [hsource_vertex]
    have hchartR0_subset_reverseTerminalLeftCone :
        chart0 '' R0 ⊆
          PolygonalArcTerminalEndpointLeftCone (PolygonalArcReverse γ) r₀ K₀ := by
      rintro x ⟨z, hzR, rfl⟩
      rw [PolygonalArcTerminalEndpointLeftCone]
      refine ⟨z, ?_, ?_⟩
      · dsimp [R0] at hzR
        rcases hzR with ⟨hz0, hzdisk, hzlow, hzneg⟩
        refine ⟨hz0, ?_, ?_, hzneg⟩
        · have hρ0_lt' :
              controlRadii.radius ⟨0, Nat.lt_of_succ_lt hj0⟩ < r₀ := by
            simpa using hρ0_lt
          have hDpos : 0 < dist γ.source γ.vertices[1] := by
            simpa [hsource_vertex] using hdist0
          have hDposR : (0 : ℝ) < dist γ.source γ.vertices[1] := by
            simpa using hDpos
          have ha0_lt : a0 < r₀ / dist γ.source γ.vertices[1] := by
            dsimp [a0]
            have hD_eq :
                dist γ.vertices[0] γ.vertices[0 + 1] =
                  dist γ.source γ.vertices[1] := by
              simp [hsource_vertex]
            rw [hD_eq]
            exact div_lt_div_of_pos_right hρ0_lt' hDposR
          have hratio_pos : (0 : ℝ) < r₀ / dist γ.source γ.vertices[1] := by
            exact div_pos hr₀ hDposR
          have hrevIdx :
              (PolygonalArcReverse γ).vertices.length - 2 <
                (PolygonalArcReverse γ).vertices.length := by
            simp [PolygonalArcReverse, List.length_reverse]
            omega
          have hrev_prev :
              (PolygonalArcReverse γ).vertices[(PolygonalArcReverse γ).vertices.length - 2] =
                γ.vertices[1] := by
            have hidx :
                γ.vertices.length - 1 -
                    ((PolygonalArcReverse γ).vertices.length - 2) = 1 := by
              simp [PolygonalArcReverse, List.length_reverse]
              omega
            have hvalid :
                (PolygonalArcReverse γ).vertices.length - 2 <
                  γ.vertices.reverse.length := by
              simp [PolygonalArcReverse, List.length_reverse]
              omega
            change γ.vertices.reverse[(PolygonalArcReverse γ).vertices.length - 2] =
              γ.vertices[1]
            rw [List.getElem_reverse hvalid]
            simpa [hidx]
          have hdist_eq :
              dist (PolygonalArcReverse γ).target
                  (PolygonalArcReverse γ).vertices[(PolygonalArcReverse γ).vertices.length - 2] =
                dist γ.source γ.vertices[1] := by
            have hidx :
                γ.vertices.length - 1 - (γ.vertices.length - 2) = 1 := by
              omega
            simpa [PolygonalArcReverse, List.length_reverse, hidx]
          rw [hdist_eq]
          nlinarith
        · have hK_lt : K0 < K₀ := by
            simpa [K0] using hKinit_lt
          nlinarith [hK_lt, hz0, hzlow]
      · dsimp [chart0, d0]
        have hidx : γ.vertices.length - 1 - (γ.vertices.length - 2) = 1 := by
          omega
        simp [PolygonalArcReverse, List.length_reverse, hidx, hsource_vertex]
    refine ⟨chart0 '' C0, chart0 '' L0, chart0 '' R0,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    refine ⟨?_, ?_, ?_, hCsub_disk, ?_, ?_, hLsubC, hRsubC,
      hchartL0conn, hchartR0conn, ?_, ?_, hchartLR0disj, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact chart_image_open γ.vertices[0] d0 hd0 C0 hC0open
    · exact chart_image_open γ.vertices[0] d0 hd0 L0 hL0open
    · exact chart_image_open γ.vertices[0] d0 hd0 R0 hR0open
    · intro hpos _
      have : (0 : ℕ) < 0 := by simpa using hpos
      omega
    · intro _
      exact hvertex0_not_chartC
    · rw [Set.disjoint_left]
      intro x hxL hxcarrier
      exact (Set.disjoint_left.mp hchartLG0disj) hxL
        (hcarrier_chartC_subset_G ⟨hxcarrier, hLsubC hxL⟩)
    · rw [Set.disjoint_left]
      intro x hxR hxcarrier
      exact (Set.disjoint_left.mp hchartRG0disj) hxR
        (hcarrier_chartC_subset_G ⟨hxcarrier, hRsubC hxR⟩)
    · intro j hj
      by_cases hj_zero : j = 0
      · subst j
        simpa using hleft0
      · exact leftHalf_inter_subset_of_nonincident ⟨0, hlen_pos⟩
          (chart0 '' C0) (chart0 '' L0) hCsub_disk j hj
          (by
            change (0 : ℕ) ≠ j
            omega)
          (by
            change (0 : ℕ) ≠ j + 1
            omega)
    · intro j hj
      by_cases hj_zero : j = 0
      · subst j
        simpa using hright0
      · exact rightHalf_inter_subset_of_nonincident ⟨0, hlen_pos⟩
          (chart0 '' C0) (chart0 '' R0) hCsub_disk j hj
          (by
            change (0 : ℕ) ≠ j
            omega)
          (by
            change (0 : ℕ) ≠ j + 1
            omega)
    · exact hwithout0
    · intro j hj hij
      have hj_eq : j = 0 := by
        have hval := congrArg Fin.val hij
        simpa using hval.symm
      subst j
      intro x hx
      exact Set.image_mono hG0subC (hgerm0 hx)
    · intro j hj hij
      have hval := congrArg Fin.val hij
      have : (0 : ℕ) = j + 1 := by simpa using hval
      omega
    · intro j hj hij
      have hj_eq : j = 0 := by
        have hval := congrArg Fin.val hij
        simpa using hval.symm
      subst j
      rw [vertexLocalPieces.outgoingLeftAttachment_eq]
      rintro x hx
      exact hleft0_ball ⟨hx.2, by
        rw [vertexLocalPieces.vertexDisk_eq] at hx
        simpa using hx.1⟩
    · intro j hj hij
      have hj_eq : j = 0 := by
        have hval := congrArg Fin.val hij
        simpa using hval.symm
      subst j
      rw [vertexLocalPieces.outgoingRightAttachment_eq]
      rintro x hx
      exact hright0_ball ⟨hx.2, by
        rw [vertexLocalPieces.vertexDisk_eq] at hx
        simpa using hx.1⟩
    · intro j hj hij
      have hval := congrArg Fin.val hij
      have : (0 : ℕ) = j + 1 := by simpa using hval
      omega
    · intro j hj hij
      have hval := congrArg Fin.val hij
      have : (0 : ℕ) = j + 1 := by simpa using hval
      omega
    · intro j hj hij x hx
      have hj_eq : j = 0 := by
        have hval := congrArg Fin.val hij
        simpa using hval.symm
      subst j
      rcases hgerm0 hx with ⟨z, hzG, rfl⟩
      exact chart_mem_closure_image γ.vertices[0] d0
        ((endpoint_germ_subset_closure_left a0 K0 ha0 hK0) hzG)
    · intro j hj hij x hx
      have hj_eq : j = 0 := by
        have hval := congrArg Fin.val hij
        simpa using hval.symm
      subst j
      rcases hgerm0 hx with ⟨z, hzG, rfl⟩
      exact chart_mem_closure_image γ.vertices[0] d0
        ((endpoint_germ_subset_closure_right a0 K0 ha0 hK0) hzG)
    · intro j hj hij
      have hval := congrArg Fin.val hij
      have : (0 : ℕ) = j + 1 := by simpa using hval
      omega
    · intro j hj hij
      have hval := congrArg Fin.val hij
      have : (0 : ℕ) = j + 1 := by simpa using hval
      omega
    · intro hpos _
      have : (0 : ℕ) < 0 := by simpa using hpos
      omega
    · intro hpos _
      have : (0 : ℕ) < 0 := by simpa using hpos
      omega
    · intro _ x hx
      exact hchartC0_subset_initialCone hx.1
    · intro hlast
      change (0 : ℕ) + 1 = γ.vertices.length at hlast
      omega
    · intro _
      exact hchartL0_subset_initialLeftCone
    · intro hlast
      change (0 : ℕ) + 1 = γ.vertices.length at hlast
      omega
    · intro _
      exact hchartR0_subset_reverseTerminalLeftCone
    · intro hlast
      change (0 : ℕ) + 1 = γ.vertices.length at hlast
      omega
    · intro _
      rfl
    · intro _
      rfl
    · intro _
      rfl
    · intro hlast
      change (0 : ℕ) + 1 = γ.vertices.length at hlast
      omega
    · intro hlast
      change (0 : ℕ) + 1 = γ.vertices.length at hlast
      omega
    · intro hlast
      change (0 : ℕ) + 1 = γ.vertices.length at hlast
      omega
  have htarget_vertex : γ.vertices[γ.vertices.length - 1] = γ.target := by
    have htargetIdx : γ.vertices.length - 1 < γ.vertices.length := by omega
    have hget :
        γ.vertices[γ.vertices.length - 1]? =
          some γ.vertices[γ.vertices.length - 1] :=
      List.getElem?_eq_getElem htargetIdx
    rw [← List.getLast?_eq_getElem?, γ.target_eq_last] at hget
    exact Option.some.inj hget.symm
  have htarget_chart : γ.vertices[lastJ + 1] = γ.target := by
    have hidx : lastJ + 1 = γ.vertices.length - 1 := by
      dsimp [lastJ]
      omega
    simpa [hidx] using htarget_vertex
  have hGoodTerminal :
      ∃ C L R : Set E,
        GoodCore ⟨lastJ + 1, hlastJ⟩ C L R ∧
          (lastJ + 1 = 0 →
            C \ γ.relativeInterior ⊆ PolygonalArcInitialEndpointCone γ r₀ K₀) ∧
          (lastJ + 1 + 1 = γ.vertices.length →
            C \ γ.relativeInterior ⊆ PolygonalArcTerminalEndpointCone γ r₁ K₁) ∧
          (lastJ + 1 = 0 →
            L ⊆ PolygonalArcInitialEndpointLeftCone γ r₀ K₀) ∧
          (lastJ + 1 + 1 = γ.vertices.length →
            L ⊆ PolygonalArcTerminalEndpointLeftCone γ r₁ K₁) ∧
          (lastJ + 1 = 0 →
            R ⊆ PolygonalArcTerminalEndpointLeftCone (PolygonalArcReverse γ) r₀ K₀) ∧
          (lastJ + 1 + 1 = γ.vertices.length →
            R ⊆ PolygonalArcInitialEndpointLeftCone (PolygonalArcReverse γ) r₁ K₁) ∧
          (lastJ + 1 = 0 → C = chart0 '' C0) ∧
          (lastJ + 1 = 0 → L = chart0 '' L0) ∧
          (lastJ + 1 = 0 → R = chart0 '' R0) ∧
          (lastJ + 1 + 1 = γ.vertices.length → C = chartT '' CT) ∧
          (lastJ + 1 + 1 = γ.vertices.length → L = chartT '' RT) ∧
          (lastJ + 1 + 1 = γ.vertices.length → R = chartT '' LT) := by
    let GT : Set E :=
      {z | 0 < z 0 ∧ z 0 < aT ∧ z 1 = 0}
    have hside :=
      PolygonalArcTerminalEndpointDiskCappedTaperSideLabelling γ controlRadii
        middleSegments forbiddenMargins compatibleTubes lastJ hlastJ
    change
      0 < aT ∧
        IsOpen CT ∧ IsOpen LT ∧ IsOpen RT ∧
        IsConnected LT ∧ IsConnected RT ∧
        IsConnected (chartT '' LT) ∧ IsConnected (chartT '' RT) ∧
        Disjoint LT RT ∧ Disjoint (chartT '' LT) (chartT '' RT) ∧
        (0 : E) ∉ CT ∧ GT ⊆ CT ∧ CT \ GT = LT ∪ RT ∧
        (∀ z : E,
          z 0 ^ 2 + z 1 ^ 2 < aT ^ 2 →
            chartT z ∈ Metric.ball γ.vertices[lastJ + 1]
              (controlRadii.radius ⟨lastJ + 1, hlastJ⟩)) ∧
        chartT '' CT ⊆ Metric.ball γ.vertices[lastJ + 1]
          (controlRadii.radius ⟨lastJ + 1, hlastJ⟩) ∧
        γ.vertices[lastJ + 1] ∉ chartT '' CT ∧
        (∀ {t : ℝ}, 0 < t →
          chartT (WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then t else 0)) ≠
            γ.vertices[lastJ + 1]) ∧
        ((AffineMap.lineMap γ.vertices[lastJ] γ.vertices[lastJ + 1]) ''
            Set.Ioo
              (1 - controlRadii.radius ⟨lastJ + 1, hlastJ⟩ /
                dist γ.vertices[lastJ] γ.vertices[lastJ + 1]) (1 : ℝ) ⊆
          chartT '' GT) ∧
        chartT '' CT \ chartT '' GT = chartT '' LT ∪ chartT '' RT ∧
        sep.leftHalf lastJ hlastJ ∩ chartT '' CT ⊆ chartT '' RT ∧
        sep.rightHalf lastJ hlastJ ∩ chartT '' CT ⊆ chartT '' LT at hside
    rcases hside with
      ⟨haT, hCTopen, hLTopen, hRTopen, hLTconn, hRTconn, hchartLTconn,
        hchartRTconn, hLRTdisj, hchartLRTdisj, hzeroT_not_C, hGTsubC,
        hmodel_splitT, hdisk_coordT, hchartCT_ball, hvertexT_not_chartC,
        hcoordT_omit, hgermT, himage_splitT, hleftT, hrightT⟩
    have hattach :=
      PolygonalArcTerminalEndpointDiskCappedTaperAttachmentStrengthening γ
        controlRadii middleSegments forbiddenMargins compatibleTubes lastJ hlastJ
    change
      sep.leftHalf lastJ hlastJ ∩
          Metric.ball γ.vertices[lastJ + 1]
            (controlRadii.radius ⟨lastJ + 1, hlastJ⟩) ⊆
        chartT '' RT ∧
      sep.rightHalf lastJ hlastJ ∩
          Metric.ball γ.vertices[lastJ + 1]
            (controlRadii.radius ⟨lastJ + 1, hlastJ⟩) ⊆
        chartT '' LT at hattach
    rcases hattach with ⟨hleftT_ball, hrightT_ball⟩
    have hdistT : 0 < dist γ.vertices[lastJ] γ.vertices[lastJ + 1] := by
      have hsum := controlRadii.adjacent_radii_sum_lt (j := lastJ) hlastJ
      have hleft := controlRadii.radius_pos ⟨lastJ, Nat.lt_of_succ_lt hlastJ⟩
      have hright := controlRadii.radius_pos ⟨lastJ + 1, hlastJ⟩
      simpa using lt_trans (add_pos hleft hright) hsum
    have hdT : dT ≠ 0 := by
      dsimp [dT]
      exact sub_ne_zero.mpr (dist_pos.mp hdistT)
    have hKT : 0 < KT := by
      dsimp [KT]
      exact compatibleTubes.terminalConeBound_pos lastJ hlastJ
    have hCsub_disk :
        chartT '' CT ⊆ vertexLocalPieces.vertexDisk ⟨lastJ + 1, hlastJ⟩ := by
      intro x hx
      rw [vertexLocalPieces.vertexDisk_eq]
      simpa using hchartCT_ball hx
    have hLmodel_subC : chartT '' LT ⊆ chartT '' CT := by
      rintro x ⟨z, hz, rfl⟩
      refine ⟨z, ?_, rfl⟩
      dsimp [LT, CT] at hz ⊢
      exact ⟨hz.1, hz.2.1, by nlinarith [hKT, hz.1, hz.2.2.1], hz.2.2.2⟩
    have hRmodel_subC : chartT '' RT ⊆ chartT '' CT := by
      rintro x ⟨z, hz, rfl⟩
      refine ⟨z, ?_, rfl⟩
      dsimp [RT, CT] at hz ⊢
      exact ⟨hz.1, hz.2.1, hz.2.2.1, by nlinarith [hKT, hz.1, hz.2.2.2]⟩
    have hchartT_inj : Function.Injective chartT := by
      dsimp [chartT]
      exact chart_injective γ.vertices[lastJ + 1] dT hdT
    have hLGTdisj : Disjoint LT GT := by
      rw [Set.disjoint_left]
      intro z hzL hzG
      dsimp [LT] at hzL
      dsimp [GT] at hzG
      linarith [hzL.2.2.1, hzG.2.2]
    have hRGTdisj : Disjoint RT GT := by
      rw [Set.disjoint_left]
      intro z hzR hzG
      dsimp [RT] at hzR
      dsimp [GT] at hzG
      linarith [hzR.2.2.2, hzG.2.2]
    have hchartLGTdisj : Disjoint (chartT '' LT) (chartT '' GT) :=
      image_disjoint_of_injective hchartT_inj hLGTdisj
    have hchartRGTdisj : Disjoint (chartT '' RT) (chartT '' GT) :=
      image_disjoint_of_injective hchartT_inj hRGTdisj
    have haT_lt_one : aT < 1 := by
      have hrad_lt_dist :
          controlRadii.radius ⟨lastJ + 1, hlastJ⟩ <
            dist γ.vertices[lastJ + 1] γ.vertices[lastJ] := by
        have hsum := controlRadii.adjacent_radii_sum_lt (j := lastJ) hlastJ
        have hleft := controlRadii.radius_pos ⟨lastJ, Nat.lt_of_succ_lt hlastJ⟩
        have hdist_comm :
            dist γ.vertices[lastJ + 1] γ.vertices[lastJ] =
              dist γ.vertices[lastJ] γ.vertices[lastJ + 1] := by
          rw [dist_comm]
        rw [hdist_comm]
        linarith
      have hdistTR : (0 : ℝ) < dist γ.vertices[lastJ + 1] γ.vertices[lastJ] := by
        rwa [dist_comm]
      dsimp [aT]
      rw [div_lt_iff₀ hdistTR]
      simpa using hrad_lt_dist
    have hGT_subset_relint : chartT '' GT ⊆ γ.relativeInterior := by
      rintro x ⟨z, hzG, rfl⟩
      have hz01 : (1 - z 0) ∈ Set.Ioo (0 : ℝ) (1 : ℝ) := by
        dsimp [GT] at hzG
        exact ⟨by linarith [lt_trans hzG.2.1 haT_lt_one], by linarith [hzG.1]⟩
      have hline_chart :
          chartT z =
            AffineMap.lineMap γ.vertices[lastJ] γ.vertices[lastJ + 1]
              (1 - z 0) := by
        dsimp [GT] at hzG
        have haxis :
            chartT z =
              AffineMap.lineMap γ.vertices[lastJ + 1] γ.vertices[lastJ]
                (z 0) := by
          simpa [chartT, dT] using
            chart_axis_eq_lineMap γ.vertices[lastJ + 1] γ.vertices[lastJ] z
              hzG.2.2
        have hrev :
            AffineMap.lineMap γ.vertices[lastJ + 1] γ.vertices[lastJ] (z 0) =
              AffineMap.lineMap γ.vertices[lastJ] γ.vertices[lastJ + 1]
                (1 - z 0) := by
          apply PiLp.ext
          intro k
          fin_cases k <;>
            simp [AffineMap.lineMap_apply_module] <;>
            ring
        exact haxis.trans hrev
      rw [hline_chart]
      exact PolygonalArcOpenSegmentSubsetRelativeInterior γ lastJ hlastJ
        (lineMap_mem_openSegment (𝕜 := ℝ) γ.vertices[lastJ]
          γ.vertices[lastJ + 1] hz01)
    have hcarrier_chartC_subset_G :
        γ.carrier ∩ chartT '' CT ⊆ chartT '' GT := by
      rintro x ⟨hxcarrier, hxC⟩
      have hxDisk : x ∈ vertexLocalPieces.vertexDisk ⟨lastJ + 1, hlastJ⟩ :=
        hCsub_disk hxC
      rcases vertexLocalPieces.vertexDisk_carrier_subset_incident_segments
          ⟨lastJ + 1, hlastJ⟩ x hxDisk hxcarrier with
        ⟨j, hj, hxseg, hincident⟩
      have hj_eq : j = lastJ := by
        rcases hincident with hleft_inc | hright_inc
        · have : lastJ + 1 = j := by simpa using hleft_inc
          have : j + 1 = γ.vertices.length := by omega
          omega
        · have : lastJ + 1 = j + 1 := by simpa using hright_inc
          omega
      subst j
      rw [segment_eq_image_lineMap] at hxseg
      rcases hxseg with ⟨t, ht, htx⟩
      rcases hxC with ⟨z, hzC, hzx⟩
      let zt : E := WithLp.toLp 2 (fun k : Fin 2 => if k = 0 then 1 - t else 0)
      have hline_chart :
          chartT zt = AffineMap.lineMap γ.vertices[lastJ] γ.vertices[lastJ + 1] t := by
        have haxis :
            chartT zt =
              AffineMap.lineMap γ.vertices[lastJ + 1] γ.vertices[lastJ]
                (1 - t) := by
          simpa [chartT, dT, zt] using
            chart_axis_param_eq_lineMap γ.vertices[lastJ + 1]
              γ.vertices[lastJ] (1 - t)
        have hrev :
            AffineMap.lineMap γ.vertices[lastJ + 1] γ.vertices[lastJ]
                (1 - t) =
              AffineMap.lineMap γ.vertices[lastJ] γ.vertices[lastJ + 1] t := by
          apply PiLp.ext
          intro k
          fin_cases k <;>
            simp [AffineMap.lineMap_apply_module] <;>
            ring
        exact haxis.trans hrev
      have hz_eq : z = zt := by
        apply hchartT_inj
        rw [hzx, ← htx, ← hline_chart]
      have hztC : zt ∈ CT := by
        simpa [hz_eq] using hzC
      have ht_back_pos : 0 < 1 - t := by
        dsimp [CT, zt] at hztC
        simpa [zt] using hztC.1
      have ht_back_sq : (1 - t) ^ 2 < aT ^ 2 := by
        dsimp [CT, zt] at hztC
        simpa [zt] using hztC.2.1
      have ht_back_lt_aT : 1 - t < aT := by
        nlinarith [haT, ht_back_pos, ht_back_sq]
      refine ⟨zt, ?_, ?_⟩
      · dsimp [GT, zt]
        exact ⟨by simpa [zt] using ht_back_pos,
          by simpa [zt] using ht_back_lt_aT, by simp [zt]⟩
      · rw [hline_chart, htx]
    have hrel_subset_carrier : γ.relativeInterior ⊆ γ.carrier := by
      intro x hx
      rw [γ.relativeInterior_eq] at hx
      exact hx.1
    have hwithoutT :
        chartT '' CT \ γ.relativeInterior = chartT '' RT ∪ chartT '' LT := by
      calc
        chartT '' CT \ γ.relativeInterior = chartT '' CT \ chartT '' GT := by
          ext x
          constructor
          · rintro ⟨hxC, hxnotRel⟩
            exact ⟨hxC, fun hxG => hxnotRel (hGT_subset_relint hxG)⟩
          · rintro ⟨hxC, hxnotG⟩
            exact ⟨hxC, fun hxRel =>
              hxnotG (hcarrier_chartC_subset_G ⟨hrel_subset_carrier hxRel, hxC⟩)⟩
        _ = chartT '' LT ∪ chartT '' RT := himage_splitT
        _ = chartT '' RT ∪ chartT '' LT := by rw [Set.union_comm]
    have hchartCT_subset_terminalCone :
        chartT '' CT ⊆ PolygonalArcTerminalEndpointCone γ r₁ K₁ := by
      rintro x ⟨z, hzC, rfl⟩
      rw [PolygonalArcTerminalEndpointCone]
      refine ⟨z, ?_, ?_⟩
      · dsimp [CT] at hzC
        rcases hzC with ⟨hz0, hzdisk, hzlow, hzhigh⟩
        refine ⟨hz0, ?_, ?_, ?_⟩
        · have hρT_lt' :
              controlRadii.radius ⟨lastJ + 1, hlastJ⟩ < r₁ := by
            have htargetIdx : γ.vertices.length - 1 < γ.vertices.length := by omega
            have hfin :
                (⟨lastJ + 1, hlastJ⟩ : Fin γ.vertices.length) =
                  ⟨γ.vertices.length - 1, htargetIdx⟩ := by
              apply Fin.ext
              dsimp [lastJ]
              omega
            rw [hfin]
            simpa using hρT_lt
          have hDpos_rev : 0 < dist γ.vertices[lastJ + 1] γ.vertices[lastJ] := by
            simpa [dist_comm] using hdistT
          have hDpos : 0 < dist γ.target γ.vertices[lastJ] := by
            simpa [htarget_chart] using hDpos_rev
          have hDposR : (0 : ℝ) < dist γ.target γ.vertices[lastJ] := by
            simpa using hDpos
          have haT_lt : aT < r₁ / dist γ.target γ.vertices[lastJ] := by
            dsimp [aT]
            have hD_eq :
                dist γ.vertices[lastJ + 1] γ.vertices[lastJ] =
                  dist γ.target γ.vertices[lastJ] := by
              simp [htarget_chart]
            rw [hD_eq]
            exact div_lt_div_of_pos_right hρT_lt' hDposR
          have hratio_pos : (0 : ℝ) < r₁ / dist γ.target γ.vertices[lastJ] := by
            exact div_pos hr₁ hDposR
          nlinarith
        · have hK_lt : KT < K₁ := by
            simpa [KT, lastJ] using hKterm_lt
          nlinarith [hK_lt, hK₁pos, hz0, hzlow]
        · have hK_lt : KT < K₁ := by
            simpa [KT, lastJ] using hKterm_lt
          nlinarith [hK_lt, hz0, hzhigh]
      · dsimp [chartT, dT]
        simp [htarget_chart, lastJ]
    have hchartRT_subset_terminalLeftCone :
        chartT '' RT ⊆ PolygonalArcTerminalEndpointLeftCone γ r₁ K₁ := by
      rintro x ⟨z, hzR, rfl⟩
      rw [PolygonalArcTerminalEndpointLeftCone]
      refine ⟨z, ?_, ?_⟩
      · dsimp [RT] at hzR
        rcases hzR with ⟨hz0, hzdisk, hzlow, hzneg⟩
        refine ⟨hz0, ?_, ?_, hzneg⟩
        · have hρT_lt' :
              controlRadii.radius ⟨lastJ + 1, hlastJ⟩ < r₁ := by
            have htargetIdx : γ.vertices.length - 1 < γ.vertices.length := by omega
            have hfin :
                (⟨lastJ + 1, hlastJ⟩ : Fin γ.vertices.length) =
                  ⟨γ.vertices.length - 1, htargetIdx⟩ := by
              apply Fin.ext
              dsimp [lastJ]
              omega
            rw [hfin]
            simpa using hρT_lt
          have hDpos_rev : 0 < dist γ.vertices[lastJ + 1] γ.vertices[lastJ] := by
            simpa [dist_comm] using hdistT
          have hDpos : 0 < dist γ.target γ.vertices[lastJ] := by
            simpa [htarget_chart] using hDpos_rev
          have hDposR : (0 : ℝ) < dist γ.target γ.vertices[lastJ] := by
            simpa using hDpos
          have haT_lt : aT < r₁ / dist γ.target γ.vertices[lastJ] := by
            dsimp [aT]
            have hD_eq :
                dist γ.vertices[lastJ + 1] γ.vertices[lastJ] =
                  dist γ.target γ.vertices[lastJ] := by
              simp [htarget_chart]
            rw [hD_eq]
            exact div_lt_div_of_pos_right hρT_lt' hDposR
          have hratio_pos : (0 : ℝ) < r₁ / dist γ.target γ.vertices[lastJ] := by
            exact div_pos hr₁ hDposR
          nlinarith
        · have hK_lt : KT < K₁ := by
            simpa [KT, lastJ] using hKterm_lt
          nlinarith [hK_lt, hz0, hzlow]
      · dsimp [chartT, dT]
        simp [htarget_chart, lastJ]
    have hchartLT_subset_reverseInitialLeftCone :
        chartT '' LT ⊆
          PolygonalArcInitialEndpointLeftCone (PolygonalArcReverse γ) r₁ K₁ := by
      rintro x ⟨z, hzL, rfl⟩
      rw [PolygonalArcInitialEndpointLeftCone]
      refine ⟨z, ?_, ?_⟩
      · dsimp [LT] at hzL
        rcases hzL with ⟨hz0, hzdisk, hzpos, hzhigh⟩
        refine ⟨hz0, ?_, hzpos, ?_⟩
        · have hρT_lt' :
              controlRadii.radius ⟨lastJ + 1, hlastJ⟩ < r₁ := by
            have htargetIdx : γ.vertices.length - 1 < γ.vertices.length := by omega
            have hfin :
                (⟨lastJ + 1, hlastJ⟩ : Fin γ.vertices.length) =
                  ⟨γ.vertices.length - 1, htargetIdx⟩ := by
              apply Fin.ext
              dsimp [lastJ]
              omega
            rw [hfin]
            simpa using hρT_lt
          have hDpos_rev : 0 < dist γ.vertices[lastJ + 1] γ.vertices[lastJ] := by
            simpa [dist_comm] using hdistT
          have hDpos : 0 < dist γ.target γ.vertices[lastJ] := by
            simpa [htarget_chart] using hDpos_rev
          have hDposR : (0 : ℝ) < dist γ.target γ.vertices[lastJ] := by
            simpa using hDpos
          have haT_lt : aT < r₁ / dist γ.target γ.vertices[lastJ] := by
            dsimp [aT]
            have hD_eq :
                dist γ.vertices[lastJ + 1] γ.vertices[lastJ] =
                  dist γ.target γ.vertices[lastJ] := by
              simp [htarget_chart]
            rw [hD_eq]
            exact div_lt_div_of_pos_right hρT_lt' hDposR
          have hratio_pos : (0 : ℝ) < r₁ / dist γ.target γ.vertices[lastJ] := by
            exact div_pos hr₁ hDposR
          have hrevIdx : 1 < (PolygonalArcReverse γ).vertices.length := by
            simp [PolygonalArcReverse, List.length_reverse]
            omega
          have hdist_eq :
              dist (PolygonalArcReverse γ).source
                  (PolygonalArcReverse γ).vertices[1] =
                dist γ.target γ.vertices[lastJ] := by
            have hidx : γ.vertices.length - 1 - 1 = lastJ := by
              omega
            simpa [PolygonalArcReverse, List.length_reverse, hidx]
          rw [hdist_eq]
          nlinarith
        · have hK_lt : KT < K₁ := by
            simpa [KT, lastJ] using hKterm_lt
          nlinarith [hK_lt, hz0, hzhigh]
      · dsimp [chartT, dT]
        have hidx : γ.vertices.length - 1 - 1 = lastJ := by
          omega
        simp [PolygonalArcReverse, List.length_reverse, hidx, htarget_chart]
    refine ⟨chartT '' CT, chartT '' RT, chartT '' LT,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    refine ⟨?_, ?_, ?_, hCsub_disk, ?_, ?_, hRmodel_subC, hLmodel_subC,
      hchartRTconn, hchartLTconn, ?_, ?_, hchartLRTdisj.symm, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact chart_image_open γ.vertices[lastJ + 1] dT hdT CT hCTopen
    · exact chart_image_open γ.vertices[lastJ + 1] dT hdT RT hRTopen
    · exact chart_image_open γ.vertices[lastJ + 1] dT hdT LT hLTopen
    · intro hpos hnext
      exfalso
      have hnext' : lastJ + 2 < γ.vertices.length := by
        simpa [Nat.add_assoc] using hnext
      omega
    · intro _
      exact hvertexT_not_chartC
    · rw [Set.disjoint_left]
      intro x hxR hxcarrier
      exact (Set.disjoint_left.mp hchartRGTdisj) hxR
        (hcarrier_chartC_subset_G ⟨hxcarrier, hRmodel_subC hxR⟩)
    · rw [Set.disjoint_left]
      intro x hxL hxcarrier
      exact (Set.disjoint_left.mp hchartLGTdisj) hxL
        (hcarrier_chartC_subset_G ⟨hxcarrier, hLmodel_subC hxL⟩)
    · intro j hj
      by_cases hj_last : j = lastJ
      · subst j
        simpa using hleftT
      · exact leftHalf_inter_subset_of_nonincident ⟨lastJ + 1, hlastJ⟩
          (chartT '' CT) (chartT '' RT) hCsub_disk j hj
          (by
            change lastJ + 1 ≠ j
            omega)
          (by
            change lastJ + 1 ≠ j + 1
            omega)
    · intro j hj
      by_cases hj_last : j = lastJ
      · subst j
        simpa using hrightT
      · exact rightHalf_inter_subset_of_nonincident ⟨lastJ + 1, hlastJ⟩
          (chartT '' CT) (chartT '' LT) hCsub_disk j hj
          (by
            change lastJ + 1 ≠ j
            omega)
          (by
            change lastJ + 1 ≠ j + 1
            omega)
    · exact hwithoutT
    · intro j hj hij
      have hval := congrArg Fin.val hij
      have : lastJ + 1 = j := by simpa using hval
      have : j + 1 = γ.vertices.length := by omega
      omega
    · intro j hj hij
      have hj_eq : j = lastJ := by
        have hval := congrArg Fin.val hij
        have : lastJ + 1 = j + 1 := by simpa using hval
        omega
      subst j
      intro x hx
      exact Set.image_mono hGTsubC (hgermT hx)
    · intro j hj hij
      have hval := congrArg Fin.val hij
      have : lastJ + 1 = j := by simpa using hval
      have : j + 1 = γ.vertices.length := by omega
      omega
    · intro j hj hij
      have hval := congrArg Fin.val hij
      have : lastJ + 1 = j := by simpa using hval
      have : j + 1 = γ.vertices.length := by omega
      omega
    · intro j hj hij
      have hj_eq : j = lastJ := by
        have hval := congrArg Fin.val hij
        have : lastJ + 1 = j + 1 := by simpa using hval
        omega
      subst j
      rw [vertexLocalPieces.incomingLeftAttachment_eq]
      rintro x hx
      exact hleftT_ball ⟨hx.2, by
        rw [vertexLocalPieces.vertexDisk_eq] at hx
        simpa using hx.1⟩
    · intro j hj hij
      have hj_eq : j = lastJ := by
        have hval := congrArg Fin.val hij
        have : lastJ + 1 = j + 1 := by simpa using hval
        omega
      subst j
      rw [vertexLocalPieces.incomingRightAttachment_eq]
      rintro x hx
      exact hrightT_ball ⟨hx.2, by
        rw [vertexLocalPieces.vertexDisk_eq] at hx
        simpa using hx.1⟩
    · intro j hj hij
      have hval := congrArg Fin.val hij
      have : lastJ + 1 = j := by simpa using hval
      have : j + 1 = γ.vertices.length := by omega
      omega
    · intro j hj hij
      have hval := congrArg Fin.val hij
      have : lastJ + 1 = j := by simpa using hval
      have : j + 1 = γ.vertices.length := by omega
      omega
    · intro j hj hij x hx
      have hj_eq : j = lastJ := by
        have hval := congrArg Fin.val hij
        have : lastJ + 1 = j + 1 := by simpa using hval
        omega
      subst j
      rcases hgermT hx with ⟨z, hzG, rfl⟩
      exact chart_mem_closure_image γ.vertices[lastJ + 1] dT
        ((endpoint_germ_subset_closure_right aT KT haT hKT) hzG)
    · intro j hj hij x hx
      have hj_eq : j = lastJ := by
        have hval := congrArg Fin.val hij
        have : lastJ + 1 = j + 1 := by simpa using hval
        omega
      subst j
      rcases hgermT hx with ⟨z, hzG, rfl⟩
      exact chart_mem_closure_image γ.vertices[lastJ + 1] dT
        ((endpoint_germ_subset_closure_left aT KT haT hKT) hzG)
    · intro hpos hnext
      exfalso
      have hnext' : lastJ + 2 < γ.vertices.length := by
        simpa [Nat.add_assoc] using hnext
      omega
    · intro hpos hnext
      exfalso
      have hnext' : lastJ + 2 < γ.vertices.length := by
        simpa [Nat.add_assoc] using hnext
      omega
    · intro hzero
      change lastJ + 1 = 0 at hzero
      omega
    · intro _ x hx
      exact hchartCT_subset_terminalCone hx.1
    · intro hzero
      change lastJ + 1 = 0 at hzero
      omega
    · intro _
      exact hchartRT_subset_terminalLeftCone
    · intro hzero
      change lastJ + 1 = 0 at hzero
      omega
    · intro _
      exact hchartLT_subset_reverseInitialLeftCone
    · intro hzero
      change lastJ + 1 = 0 at hzero
      omega
    · intro hzero
      change lastJ + 1 = 0 at hzero
      omega
    · intro hzero
      change lastJ + 1 = 0 at hzero
      omega
    · intro _
      rfl
    · intro _
      rfl
    · intro _
      rfl

  have hGood : ∀ i : Fin γ.vertices.length,
      ∃ C L R : Set E,
        GoodCore i C L R ∧
          (i.1 = 0 → C \ γ.relativeInterior ⊆
            PolygonalArcInitialEndpointCone γ r₀ K₀) ∧
          (i.1 + 1 = γ.vertices.length → C \ γ.relativeInterior ⊆
            PolygonalArcTerminalEndpointCone γ r₁ K₁) ∧
          (i.1 = 0 → L ⊆
            PolygonalArcInitialEndpointLeftCone γ r₀ K₀) ∧
          (i.1 + 1 = γ.vertices.length → L ⊆
            PolygonalArcTerminalEndpointLeftCone γ r₁ K₁) ∧
          (i.1 = 0 → R ⊆
            PolygonalArcTerminalEndpointLeftCone (PolygonalArcReverse γ) r₀ K₀) ∧
          (i.1 + 1 = γ.vertices.length → R ⊆
            PolygonalArcInitialEndpointLeftCone (PolygonalArcReverse γ) r₁ K₁) ∧
          (i.1 = 0 → C = chart0 '' C0) ∧
          (i.1 = 0 → L = chart0 '' L0) ∧
          (i.1 = 0 → R = chart0 '' R0) ∧
          (i.1 + 1 = γ.vertices.length → C = chartT '' CT) ∧
          (i.1 + 1 = γ.vertices.length → L = chartT '' RT) ∧
          (i.1 + 1 = γ.vertices.length → R = chartT '' LT) := by
    intro i
    by_cases hi0 : i.1 = 0
    · have hi_eq : i = ⟨0, hlen_pos⟩ := by
        apply Fin.ext
        simpa using hi0
      simpa [hi_eq] using hGoodInitial
    · by_cases hiterm : i.1 + 1 = γ.vertices.length
      · have hi_eq : i = ⟨lastJ + 1, hlastJ⟩ := by
          apply Fin.ext
          dsimp [lastJ] at *
          omega
        simpa [hi_eq] using hGoodTerminal
      · refine ⟨baseTopology.vertexCollar i, baseTopology.leftSidePiece i,
          baseTopology.rightSidePiece i,
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · refine ⟨baseTopology.vertexCollar_open i,
            baseTopology.leftSidePiece_open i,
            baseTopology.rightSidePiece_open i,
            baseTopology.vertexCollar_subset_vertexDisk i,
            baseTopology.interior_vertexCollar_eq_vertexDisk i,
            ?_,
            baseTopology.leftSidePiece_subset_vertexCollar i,
            baseTopology.rightSidePiece_subset_vertexCollar i,
            baseTopology.leftSidePiece_connected i,
            baseTopology.rightSidePiece_connected i,
            baseTopology.leftSidePiece_disjoint_carrier i,
            baseTopology.rightSidePiece_disjoint_carrier i,
            baseTopology.local_sidePieces_disjoint i,
            ?_, ?_,
            baseTopology.vertexCollar_without_arc i,
            ?_, ?_, ?_, ?_, ?_, ?_,
            ?_, ?_, ?_, ?_, ?_, ?_⟩
          · exact baseTopology.endpoint_vertexCollar_omits_vertex i
          · intro j hj
            exact baseTopology.leftHalf_inter_vertexCollar_subset_leftSidePiece j hj i
          · intro j hj
            exact baseTopology.rightHalf_inter_vertexCollar_subset_rightSidePiece j hj i
          · intro j hj hij
            simpa [hij] using baseTopology.outgoing_germ_subset_vertexCollar j hj
          · intro j hj hij
            simpa [hij] using baseTopology.incoming_germ_subset_vertexCollar j hj
          · intro j hj hij
            simpa [hij] using baseTopology.outgoingLeftAttachment_subset_leftSidePiece j hj
          · intro j hj hij
            simpa [hij] using baseTopology.outgoingRightAttachment_subset_rightSidePiece j hj
          · intro j hj hij
            simpa [hij] using baseTopology.incomingLeftAttachment_subset_leftSidePiece j hj
          · intro j hj hij
            simpa [hij] using baseTopology.incomingRightAttachment_subset_rightSidePiece j hj
          · intro j hj hij
            simpa [hij] using
              baseTopology.outgoing_germ_subset_closure_leftSidePiece j hj
          · intro j hj hij
            simpa [hij] using
              baseTopology.outgoing_germ_subset_closure_rightSidePiece j hj
          · intro j hj hij
            simpa [hij] using
              baseTopology.incoming_germ_subset_closure_leftSidePiece j hj
          · intro j hj hij
            simpa [hij] using
              baseTopology.incoming_germ_subset_closure_rightSidePiece j hj
          · intro hpos hnext
            exact baseTopology.interior_vertex_mem_closure_leftSidePiece i hpos hnext
          · intro hpos hnext
            exact baseTopology.interior_vertex_mem_closure_rightSidePiece i hpos hnext
        · intro h0
          exact (hi0 h0).elim
        · intro hlast
          exact (hiterm hlast).elim
        · intro h0
          exact (hi0 h0).elim
        · intro hlast
          exact (hiterm hlast).elim
        · intro h0
          exact (hi0 h0).elim
        · intro hlast
          exact (hiterm hlast).elim
        · intro h0
          exact (hi0 h0).elim
        · intro h0
          exact (hi0 h0).elim
        · intro h0
          exact (hi0 h0).elim
        · intro hlast
          exact (hiterm hlast).elim
        · intro hlast
          exact (hiterm hlast).elim
        · intro hlast
          exact (hiterm hlast).elim

  let vertexCollar : Fin γ.vertices.length → Set E :=
    fun i => Classical.choose (hGood i)
  let leftSidePiece : Fin γ.vertices.length → Set E :=
    fun i => Classical.choose (Classical.choose_spec (hGood i))
  let rightSidePiece : Fin γ.vertices.length → Set E :=
    fun i =>
      Classical.choose (Classical.choose_spec
        (Classical.choose_spec (hGood i)))
  have hGoodSpec :
      ∀ i : Fin γ.vertices.length,
        GoodCore i (vertexCollar i) (leftSidePiece i) (rightSidePiece i) ∧
          (i.1 = 0 → vertexCollar i \ γ.relativeInterior ⊆
            PolygonalArcInitialEndpointCone γ r₀ K₀) ∧
          (i.1 + 1 = γ.vertices.length → vertexCollar i \ γ.relativeInterior ⊆
            PolygonalArcTerminalEndpointCone γ r₁ K₁) ∧
          (i.1 = 0 → leftSidePiece i ⊆
            PolygonalArcInitialEndpointLeftCone γ r₀ K₀) ∧
          (i.1 + 1 = γ.vertices.length → leftSidePiece i ⊆
            PolygonalArcTerminalEndpointLeftCone γ r₁ K₁) ∧
          (i.1 = 0 → rightSidePiece i ⊆
            PolygonalArcTerminalEndpointLeftCone (PolygonalArcReverse γ) r₀ K₀) ∧
          (i.1 + 1 = γ.vertices.length → rightSidePiece i ⊆
            PolygonalArcInitialEndpointLeftCone (PolygonalArcReverse γ) r₁ K₁) ∧
          (i.1 = 0 → vertexCollar i = chart0 '' C0) ∧
          (i.1 = 0 → leftSidePiece i = chart0 '' L0) ∧
          (i.1 = 0 → rightSidePiece i = chart0 '' R0) ∧
          (i.1 + 1 = γ.vertices.length → vertexCollar i = chartT '' CT) ∧
          (i.1 + 1 = γ.vertices.length → leftSidePiece i = chartT '' RT) ∧
          (i.1 + 1 = γ.vertices.length → rightSidePiece i = chartT '' LT) := by
    intro i
    dsimp [vertexCollar, leftSidePiece, rightSidePiece]
    exact Classical.choose_spec
      (Classical.choose_spec (Classical.choose_spec (hGood i)))
  have hGoodCoreSpec :
      ∀ i : Fin γ.vertices.length,
        GoodCore i (vertexCollar i) (leftSidePiece i) (rightSidePiece i) := by
    intro i
    exact (hGoodSpec i).1
  let localTopology :
      PolygonalArcCollarLocalTopologyData γ controlRadii middleSegments
        forbiddenMargins compatibleTubes vertexLocalPieces := by
    refine
      { vertexCollar := vertexCollar
        leftSidePiece := leftSidePiece
        rightSidePiece := rightSidePiece
        vertexCollar_open := ?_
        leftSidePiece_open := ?_
        rightSidePiece_open := ?_
        vertexCollar_subset_vertexDisk := ?_
        interior_vertexCollar_eq_vertexDisk := ?_
        endpoint_vertexCollar_omits_vertex := ?_
        vertexCollar_subset_eta_neighborhood := ?_
        vertexCollar_carrier_subset_incident_segments := ?_
        outgoing_germ_subset_vertexCollar := ?_
        incoming_germ_subset_vertexCollar := ?_
        outgoing_germ_subset_closure_leftSidePiece := ?_
        outgoing_germ_subset_closure_rightSidePiece := ?_
        incoming_germ_subset_closure_leftSidePiece := ?_
        incoming_germ_subset_closure_rightSidePiece := ?_
        interior_vertex_mem_closure_leftSidePiece := ?_
        interior_vertex_mem_closure_rightSidePiece := ?_
        leftSidePiece_subset_vertexCollar := ?_
        rightSidePiece_subset_vertexCollar := ?_
        leftSidePiece_connected := ?_
        rightSidePiece_connected := ?_
        leftSidePiece_disjoint_carrier := ?_
        rightSidePiece_disjoint_carrier := ?_
        local_sidePieces_disjoint := ?_
        leftHalf_inter_vertexCollar_subset_leftSidePiece := ?_
        rightHalf_inter_vertexCollar_subset_rightSidePiece := ?_
        vertexCollar_without_arc := ?_
        outgoingLeftAttachment_subset_leftSidePiece := ?_
        outgoingRightAttachment_subset_rightSidePiece := ?_
        incomingLeftAttachment_subset_leftSidePiece := ?_
        incomingRightAttachment_subset_rightSidePiece := ?_ }
    · intro i
      rcases hGoodCoreSpec i with ⟨hCopen, _⟩
      exact hCopen
    · intro i
      rcases hGoodCoreSpec i with ⟨_, hLopen, _⟩
      exact hLopen
    · intro i
      rcases hGoodCoreSpec i with ⟨_, _, hRopen, _⟩
      exact hRopen
    · intro i
      rcases hGoodCoreSpec i with ⟨_, _, _, hCsub, _⟩
      exact hCsub
    · intro i hpos hnext
      rcases hGoodCoreSpec i with ⟨_, _, _, _, hinterior, _⟩
      exact hinterior hpos hnext
    · intro i hend
      rcases hGoodCoreSpec i with ⟨_, _, _, _, _, hendpoint, _⟩
      exact hendpoint hend
    · intro i z hz
      rcases hGoodCoreSpec i with ⟨_, _, _, hCsub, _⟩
      exact vertexLocalPieces.vertexDisk_subset_eta_neighborhood i z
        (hCsub hz)
    · intro i z hz hcarrier
      rcases hGoodCoreSpec i with ⟨_, _, _, hCsub, _⟩
      exact vertexLocalPieces.vertexDisk_carrier_subset_incident_segments i z
        (hCsub hz) hcarrier
    · intro j hj
      rcases hGoodCoreSpec ⟨j, Nat.lt_of_succ_lt hj⟩ with
        ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hout, _⟩
      exact hout j hj rfl
    · intro j hj
      rcases hGoodCoreSpec ⟨j + 1, hj⟩ with
        ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hin, _⟩
      exact hin j hj rfl
    · intro j hj x hx
      rcases hGoodCoreSpec ⟨j, Nat.lt_of_succ_lt hj⟩ with
        ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
          houtClL, _, _, _, _, _⟩
      exact houtClL j hj rfl hx
    · intro j hj x hx
      rcases hGoodCoreSpec ⟨j, Nat.lt_of_succ_lt hj⟩ with
        ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
          _, houtClR, _, _, _, _⟩
      exact houtClR j hj rfl hx
    · intro j hj x hx
      rcases hGoodCoreSpec ⟨j + 1, hj⟩ with
        ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
          _, _, hinClL, _, _, _⟩
      exact hinClL j hj rfl hx
    · intro j hj x hx
      rcases hGoodCoreSpec ⟨j + 1, hj⟩ with
        ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
          _, _, _, hinClR, _, _⟩
      exact hinClR j hj rfl hx
    · intro i hi_pos hi_next
      rcases hGoodCoreSpec i with
        ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
          _, _, _, _, hvClL, _⟩
      exact hvClL hi_pos hi_next
    · intro i hi_pos hi_next
      rcases hGoodCoreSpec i with
        ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
          _, _, _, _, _, hvClR⟩
      exact hvClR hi_pos hi_next
    · intro i
      rcases hGoodCoreSpec i with ⟨_, _, _, _, _, _, hLsub, _⟩
      exact hLsub
    · intro i
      rcases hGoodCoreSpec i with ⟨_, _, _, _, _, _, _, hRsub, _⟩
      exact hRsub
    · intro i
      rcases hGoodCoreSpec i with ⟨_, _, _, _, _, _, _, _, hLconn, _⟩
      exact hLconn
    · intro i
      rcases hGoodCoreSpec i with ⟨_, _, _, _, _, _, _, _, _, hRconn, _⟩
      exact hRconn
    · intro i
      rcases hGoodCoreSpec i with ⟨_, _, _, _, _, _, _, _, _, _, hLdisj, _⟩
      exact hLdisj
    · intro i
      rcases hGoodCoreSpec i with ⟨_, _, _, _, _, _, _, _, _, _, _, hRdisj, _⟩
      exact hRdisj
    · intro i
      rcases hGoodCoreSpec i with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hLRdisj, _⟩
      exact hLRdisj
    · intro j hj i
      rcases hGoodCoreSpec i with
        ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hleftHalf, _⟩
      exact hleftHalf j hj
    · intro j hj i
      rcases hGoodCoreSpec i with
        ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hrightHalf, _⟩
      exact hrightHalf j hj
    · intro i
      rcases hGoodCoreSpec i with
        ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hwithout, _⟩
      exact hwithout
    · intro j hj
      rcases hGoodCoreSpec ⟨j, Nat.lt_of_succ_lt hj⟩ with
        ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, houtLeft, _⟩
      exact houtLeft j hj rfl
    · intro j hj
      rcases hGoodCoreSpec ⟨j, Nat.lt_of_succ_lt hj⟩ with
        ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, houtRight, _⟩
      exact houtRight j hj rfl
    · intro j hj
      rcases hGoodCoreSpec ⟨j + 1, hj⟩ with
        ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hinLeft, _⟩
      exact hinLeft j hj rfl
    · intro j hj
      rcases hGoodCoreSpec ⟨j + 1, hj⟩ with
        ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hinRight, _⟩
      exact hinRight j hj rfl

  refine ⟨vertexLocalPieces, localTopology,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h := localTopology.endpoint_vertexCollar_omits_vertex ⟨0, hlen_pos⟩ (Or.inl rfl)
    simpa [hsource_vertex] using h
  · have htargetIdx : γ.vertices.length - 1 < γ.vertices.length := by omega
    have htarget_eq_fin :
        (⟨γ.vertices.length - 1, htargetIdx⟩ : Fin γ.vertices.length) =
          (⟨lastJ + 1, hlastJ⟩ : Fin γ.vertices.length) := by
      apply Fin.ext
      dsimp [lastJ]
      omega
    have h := localTopology.endpoint_vertexCollar_omits_vertex ⟨lastJ + 1, hlastJ⟩ (Or.inr (by dsimp [lastJ]; omega))
    simpa [htarget_eq_fin, htarget_chart] using h
  · simpa using (hGoodSpec ⟨0, hlen_pos⟩).2.1 rfl
  · have htargetIdx : γ.vertices.length - 1 < γ.vertices.length := by omega
    have htarget_eq_fin :
        (⟨γ.vertices.length - 1, htargetIdx⟩ : Fin γ.vertices.length) =
          (⟨lastJ + 1, hlastJ⟩ : Fin γ.vertices.length) := by
      apply Fin.ext
      dsimp [lastJ]
      omega
    have hcap := (hGoodSpec ⟨lastJ + 1, hlastJ⟩).2.2.1 (by dsimp [lastJ]; omega)
    simpa [htarget_eq_fin] using hcap
  · simpa using (hGoodSpec ⟨0, hlen_pos⟩).2.2.2.1 rfl
  · have htargetIdx : γ.vertices.length - 1 < γ.vertices.length := by omega
    have htarget_eq_fin :
        (⟨γ.vertices.length - 1, htargetIdx⟩ : Fin γ.vertices.length) =
          (⟨lastJ + 1, hlastJ⟩ : Fin γ.vertices.length) := by
      apply Fin.ext
      dsimp [lastJ]
      omega
    have hleft := (hGoodSpec ⟨lastJ + 1, hlastJ⟩).2.2.2.2.1 (by dsimp [lastJ]; omega)
    simpa [htarget_eq_fin] using hleft
  · simpa using (hGoodSpec ⟨0, hlen_pos⟩).2.2.2.2.2.1 rfl
  · have htargetIdx : γ.vertices.length - 1 < γ.vertices.length := by omega
    have htarget_eq_fin :
        (⟨γ.vertices.length - 1, htargetIdx⟩ : Fin γ.vertices.length) =
          (⟨lastJ + 1, hlastJ⟩ : Fin γ.vertices.length) := by
      apply Fin.ext
      dsimp [lastJ]
      omega
    have hright := (hGoodSpec ⟨lastJ + 1, hlastJ⟩).2.2.2.2.2.2.1
      (by dsimp [lastJ]; omega)
    simpa [htarget_eq_fin] using hright
  · rcases hGoodSpec ⟨0, hlen_pos⟩ with
      ⟨_, _, _, _, _, _, _, hsourceCore, _, _, _, _, _⟩
    change vertexCollar ⟨0, hlen_pos⟩ = chart0 '' C0
    exact hsourceCore rfl
  · rcases hGoodSpec ⟨0, hlen_pos⟩ with
      ⟨_, _, _, _, _, _, _, _, hsourceLeft, _, _, _, _⟩
    change leftSidePiece ⟨0, hlen_pos⟩ = chart0 '' L0
    exact hsourceLeft rfl
  · rcases hGoodSpec ⟨0, hlen_pos⟩ with
      ⟨_, _, _, _, _, _, _, _, _, hsourceRight, _, _, _⟩
    change rightSidePiece ⟨0, hlen_pos⟩ = chart0 '' R0
    exact hsourceRight rfl
  · have hterminal : lastJ + 1 + 1 = γ.vertices.length := by
      dsimp [lastJ]
      omega
    have hidx : lastJ + 1 = γ.vertices.length - 1 := by
      dsimp [lastJ]
      omega
    rcases hGoodSpec ⟨lastJ + 1, hlastJ⟩ with
      ⟨_, _, _, _, _, _, _, _, _, _, htargetCore, _, _⟩
    simpa [localTopology, vertexCollar, hidx, dT, chartT, aT, KT, CT] using
      htargetCore hterminal
  · have hterminal : lastJ + 1 + 1 = γ.vertices.length := by
      dsimp [lastJ]
      omega
    have hidx : lastJ + 1 = γ.vertices.length - 1 := by
      dsimp [lastJ]
      omega
    rcases hGoodSpec ⟨lastJ + 1, hlastJ⟩ with
      ⟨_, _, _, _, _, _, _, _, _, _, _, htargetLeft, _⟩
    simpa [localTopology, leftSidePiece, hidx, dT, chartT, aT, KT, RT] using
      htargetLeft hterminal
  · have hterminal : lastJ + 1 + 1 = γ.vertices.length := by
      dsimp [lastJ]
      omega
    have hidx : lastJ + 1 = γ.vertices.length - 1 := by
      dsimp [lastJ]
      omega
    rcases hGoodSpec ⟨lastJ + 1, hlastJ⟩ with
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, htargetRight⟩
    simpa [localTopology, rightSidePiece, hidx, dT, chartT, aT, KT, LT] using
      htargetRight hterminal
