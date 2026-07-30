import Submission.EndpointSidePrefixAttachment
import Submission.EndpointSidePrefixOrderedTerminalSuffix
import Submission.EndpointSidePrefixTerminalChain
import Submission.PolygonalArcFiniteFirstContactPrefix
import Submission.StraightSegmentPolygonalArc

set_option maxHeartbeats 8000000

open Classical
noncomputable section

-- [TABLET NODE: EndpointSidePrefixTerminalAssembly]
lemma EndpointSidePrefixTerminalAssembly
    (Aarc Barc BplusArc P predecessor approach : PolygonalArc)
    (SelectedSide Rbeta H Bad StartSector DeltaX Qx
      TerminalSideRegion TerminalBridgeRegion Vin :
        Set (EuclideanSpace ℝ (Fin 2)))
    (terminalGate terminalSideSource quadrantGate h lastGate :
      EuclideanSpace ℝ (Fin 2))
    (K : FinitePolygonalSet)
    (XA xClean : Finset (EuclideanSpace ℝ (Fin 2)))
    (charge : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)) :
    K.carrier = H →
      Disjoint Aarc.carrier Rbeta →
        Aarc.source ∉ SelectedSide →
          Aarc.source ≠ BplusArc.target →
            terminalGate ∉ SelectedSide →
            SelectedSide ∩
                (closure TerminalSideRegion ∪
                  closure TerminalBridgeRegion ∪ closure Qx) =
              (∅ : Set (EuclideanSpace ℝ (Fin 2))) →
              TerminalSideRegion ⊆ DeltaX →
                TerminalBridgeRegion ⊆ DeltaX →
                  Qx ⊆ DeltaX →
            P.source = Aarc.source →
          P.target = predecessor.source →
            P.carrier ⊆
              SelectedSide ∪
                ({Aarc.source} : Set (EuclideanSpace ℝ (Fin 2))) →
              P.relativeInterior ∩
                  (Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪
                    Rbeta ∪ Bad) =
                (∅ : Set (EuclideanSpace ℝ (Fin 2))) →
              Set.Finite
                (P.carrier ∩
                  (predecessor.carrier ∪ approach.carrier ∪
                    segment ℝ h terminalGate)) →
                (∃ hfirst : 0 + 1 < P.vertices.length,
                  segment ℝ P.vertices[0] P.vertices[1] ⊆
                      StartSector ∪
                        ({Aarc.source} : Set (EuclideanSpace ℝ (Fin 2))) ∧
                    openSegment ℝ P.vertices[0] P.vertices[1] ⊆ StartSector) →
                (∀ z : EuclideanSpace ℝ (Fin 2),
                  z ∈ xClean ↔ z ∈ P.relativeInterior ∧ z ∈ H) →
                  (∀ z : EuclideanSpace ℝ (Fin 2),
                    z ∈ xClean → charge z ∈ XA) →
                    (∀ z w : EuclideanSpace ℝ (Fin 2),
                      z ∈ xClean → w ∈ xClean →
                        charge z = charge w → z = w) →
                      (∀ z : EuclideanSpace ℝ (Fin 2),
                        z ∈ xClean →
                          z ∉ Bad ∧
                            z ∉ (K.points : Set (EuclideanSpace ℝ (Fin 2))) ∧
                              ∃ j : ℕ,
                                ∃ hj : j + 1 < P.vertices.length,
                                  z ∈ openSegment ℝ
                                      P.vertices[j] P.vertices[j + 1] ∧
                                    ∃! s :
                                      EuclideanSpace ℝ (Fin 2) ×
                                        EuclideanSpace ℝ (Fin 2),
                                      s ∈ K.segments ∧
                                        z ∈ openSegment ℝ s.1 s.2 ∧
                                          ¬ ∃ c : ℝ,
                                            s.2 - s.1 =
                                              c • (P.vertices[j + 1] - P.vertices[j])) →
                        predecessor.carrier ⊆ SelectedSide ∩ Vin →
                          approach.carrier ⊆ SelectedSide ∩ Vin →
                            predecessor.target = lastGate →
                              approach.source = lastGate →
                                predecessor.carrier ∩ approach.carrier =
                                  ({lastGate} : Set (EuclideanSpace ℝ (Fin 2))) →
                                  approach.target = h →
                                    approach.carrier ∩ segment ℝ h terminalGate =
                                      ({h} : Set (EuclideanSpace ℝ (Fin 2))) →
                                      Disjoint predecessor.carrier
                                        (segment ℝ h terminalGate) →
                                        h ∈ Vin →
                                          h ≠ terminalGate →
                                            h ∉
                                              (Aarc.carrier ∪ Barc.carrier ∪
                                                BplusArc.carrier ∪ Rbeta ∪ H ∪ Bad) →
                                            Vin ⊆ SelectedSide →
                                              Vin ⊆ DeltaX →
                                                Vin ∩ Qx =
                                                  (∅ : Set (EuclideanSpace ℝ (Fin 2))) →
                                                  Vin ∩
                                                      ((Aarc.carrier ∪ Barc.carrier ∪
                                                          BplusArc.carrier ∪ Rbeta ∪ H) ∪ Bad) =
                                                    (∅ : Set (EuclideanSpace ℝ (Fin 2))) →
                                                    terminalGate ∈ closure Vin →
                                                      terminalGate ∉ Vin →
                                                        segment ℝ h terminalGate ⊆
                                                          Vin ∪
                                                            ({terminalGate} :
                                                              Set (EuclideanSpace ℝ (Fin 2))) →
                                                          openSegment ℝ h terminalGate ⊆ Vin →
                                                            segment ℝ h terminalGate ∩
                                                                (TerminalSideRegion ∪
                                                                  ({terminalGate} :
                                                                    Set (EuclideanSpace ℝ (Fin 2)))) =
                                                              ({terminalGate} :
                                                                Set (EuclideanSpace ℝ (Fin 2))) →
                                                            closure Vin ∩
                                                                closure TerminalSideRegion =
                                                              ({terminalGate} :
                                                                Set (EuclideanSpace ℝ (Fin 2))) →
                                                              closure Vin ∩
                                                                  closure TerminalBridgeRegion =
                                                                (∅ : Set (EuclideanSpace ℝ (Fin 2))) →
                                                              terminalGate ∈ DeltaX →
                                                                terminalGate ∉ Qx →
                                                                  terminalSideSource ∈ DeltaX →
                                                                    terminalGate ≠ terminalSideSource →
                                                                      segment ℝ terminalGate terminalSideSource ⊆
                                                                        TerminalSideRegion ∪
                                                                          ({terminalGate, terminalSideSource} :
                                                                            Set (EuclideanSpace ℝ (Fin 2))) →
                                                                        openSegment ℝ terminalGate terminalSideSource ⊆
                                                                          TerminalSideRegion →
                                                                          (TerminalSideRegion ∪
                                                                              ({terminalGate, terminalSideSource} :
                                                                                Set (EuclideanSpace ℝ (Fin 2)))) ∩
                                                                              ((Aarc.carrier ∪ Barc.carrier ∪
                                                                                  BplusArc.carrier ∪ Rbeta ∪ H) ∪ Bad) =
                                                                            (∅ : Set (EuclideanSpace ℝ (Fin 2))) →
                                                                            terminalSideSource ≠ quadrantGate →
                                                                              segment ℝ terminalSideSource quadrantGate ⊆
                                                                                TerminalBridgeRegion ∪
                                                                                  ({terminalSideSource, quadrantGate} :
                                                                                    Set (EuclideanSpace ℝ (Fin 2))) →
                                                                                openSegment ℝ terminalSideSource quadrantGate ⊆
                                                                                  TerminalBridgeRegion →
                                                                                  (TerminalBridgeRegion ∪
                                                                                      ({terminalSideSource, quadrantGate} :
                                                                                        Set (EuclideanSpace ℝ (Fin 2)))) ∩
                                                                                      ((Aarc.carrier ∪ Barc.carrier ∪
                                                                                          BplusArc.carrier ∪ Rbeta ∪ H) ∪ Bad) =
                                                                                    (∅ : Set (EuclideanSpace ℝ (Fin 2))) →
                                                                                    quadrantGate ∈ Qx →
                                                                                      quadrantGate ≠ BplusArc.target →
                                                                                        segment ℝ terminalSideSource quadrantGate ∩ Qx =
                                                                                          ({quadrantGate} :
                                                                                            Set (EuclideanSpace ℝ (Fin 2))) →
                                                                                        closure TerminalSideRegion ∩
                                                                                            closure TerminalBridgeRegion =
                                                                                          ({terminalSideSource} :
                                                                                            Set (EuclideanSpace ℝ (Fin 2))) →
                                                                                          closure TerminalSideRegion ∩ closure Qx =
                                                                                            (∅ : Set (EuclideanSpace ℝ (Fin 2))) →
                                                                                            closure TerminalBridgeRegion ∩ closure Qx =
                                                                                              ({quadrantGate} :
                                                                                                Set (EuclideanSpace ℝ (Fin 2))) →
                                                                                              segment ℝ quadrantGate BplusArc.target ⊆ Qx →
                                                                                                openSegment ℝ quadrantGate BplusArc.target ∩
                                                                                                    ((Aarc.carrier ∪ Barc.carrier ∪
                                                                                                        BplusArc.carrier ∪ Rbeta ∪ H) ∪ Bad) =
                                                                                                  (∅ : Set (EuclideanSpace ℝ (Fin 2))) →
      ∃ E : EndpointSidePrefixAttachment
          Aarc Barc BplusArc Rbeta H Bad DeltaX Qx K XA,
        (E.prefixPiece 0).source = Aarc.source ∧
          (E.prefixPiece 0).carrier ⊆
              StartSector ∪
                ({Aarc.source} : Set (EuclideanSpace ℝ (Fin 2))) ∧
            (E.prefixPiece 0).relativeInterior ⊆ StartSector ∧
              3 ≤ E.r ∧
                ∃ h' lastGate' : EuclideanSpace ℝ (Fin 2),
                  ∃ Vin' : Set (EuclideanSpace ℝ (Fin 2)),
                    (E.prefixPiece (E.r - 3)).carrier ⊆ SelectedSide ∩ Vin' ∧
                      (E.prefixPiece (E.r - 2)).carrier ⊆ SelectedSide ∩ Vin' ∧
                        (E.prefixPiece (E.r - 3)).target = lastGate' ∧
                          (E.prefixPiece (E.r - 2)).source = lastGate' ∧
                            (E.prefixPiece (E.r - 3)).carrier ∩
                                (E.prefixPiece (E.r - 2)).carrier =
                              ({lastGate'} : Set (EuclideanSpace ℝ (Fin 2))) ∧
                              (E.prefixPiece (E.r - 2)).target = h' ∧
                                (E.prefixPiece (E.r - 1)).source = h' ∧
                                  (E.prefixPiece (E.r - 1)).target = terminalGate ∧
                                    (E.prefixPiece (E.r - 2)).carrier ∩
                                        (E.prefixPiece (E.r - 1)).carrier =
                                      ({h'} : Set (EuclideanSpace ℝ (Fin 2))) ∧
                                      (E.prefixPiece (E.r - 1)).carrier =
                                        segment ℝ h' terminalGate ∧
                                        Disjoint
                                          (E.prefixPiece (E.r - 3)).carrier
                                          (E.prefixPiece (E.r - 1)).carrier ∧
                                          (E.prefixPiece E.r).source = terminalGate ∧
                                            (E.prefixPiece (E.r - 1)).carrier ∩
                                                (E.prefixPiece E.r).carrier =
                                              ({terminalGate} :
                                                Set (EuclideanSpace ℝ (Fin 2))) ∧
                                              (E.prefixPiece E.r).carrier =
                                                segment ℝ terminalGate terminalSideSource ∧
                                                E.terminalSide.carrier =
                                                  segment ℝ terminalSideSource quadrantGate ∧
                                                  E.terminalConnector.carrier =
                                                    segment ℝ quadrantGate BplusArc.target := by
-- BODY
  intro hK hAarcRbeta hAarcSourceNotSide hAarcSourceNeTarget
    hterminalGateNotSide hsideTerminalSep hTerminalSideDelta
    hTerminalBridgeDelta hQxDelta hPsource hPtarget hPcarrier
    hPavoid hfinite hfirst hxClean hchargeMem hchargeInj hclean
    hpredecessorSide happroachSide hpredecessorTarget happroachSource
    hpredecessorApproach happroachTarget happroachSegment
    hpredecessorSegment hhVin hhNeGate hhAvoid hVinSide hVinDelta
    hVinQx hVinAvoid hgateClosure hgateNotVin hsegmentVin hopenSegmentVin
    hsegmentTerminalSide hclosureVinTerminalSide hclosureVinTerminalBridge
    hgateDelta hgateNotQx hterminalSideSourceDelta hgateNeTerminalSideSource
    hterminalSideSegment hterminalSideOpen hterminalSideAvoid
    hterminalSideSourceNeQuadrant hterminalBridgeSegment hterminalBridgeOpen
    hterminalBridgeAvoid hquadrantMemQx hquadrantNeTarget
    hterminalBridgeMeetsQx hterminalClosuresMeet hterminalSideClosureQx
    hterminalBridgeClosureQx hconnectorSegment hconnectorAvoid
  obtain ⟨terminalSegment, chain, hterminalSegmentSource,
      hterminalSegmentTarget, hterminalSegmentCarrier,
      hterminalSegmentInterior, happroachTerminalSegment,
      hpredecessorTerminalSegment, hchainVertices, hchainSource,
      hchainTarget, hchainCarrier, hchainInterior, hpredecessorInterior,
      happroachInterior, hterminalSegmentInteriorSubset, hchainTransfer⟩ :=
    EndpointSidePrefixTerminalChain predecessor approach lastGate h terminalGate
      hpredecessorTarget happroachSource hpredecessorApproach happroachTarget
      happroachSegment hpredecessorSegment hhNeGate
  have polygonalArc_source_mem (Γ : PolygonalArc) : Γ.source ∈ Γ.carrier := by
    rw [Γ.carrier_eq]
    have hzero : Γ.vertices[0]'(by
        have := Γ.length_ge_two
        omega) = Γ.source := by
      have hhead := Γ.source_eq_head
      rw [List.head?_eq_getElem?] at hhead
      rw [List.getElem?_eq_getElem (by
        have := Γ.length_ge_two
        omega)] at hhead
      exact Option.some.inj hhead
    refine ⟨0, by
      have := Γ.length_ge_two
      omega, ?_⟩
    rw [hzero]
    exact left_mem_segment ℝ Γ.source
      (Γ.vertices[1]'(by
        have := Γ.length_ge_two
        omega))
  have polygonalArc_target_mem (Γ : PolygonalArc) : Γ.target ∈ Γ.carrier := by
    rw [Γ.carrier_eq]
    let i := Γ.vertices.length - 2
    have hi : i + 1 < Γ.vertices.length := by
      dsimp [i]
      have := Γ.length_ge_two
      omega
    refine ⟨i, hi, ?_⟩
    have hlast : Γ.vertices[i + 1] = Γ.target := by
      have hlast' := Γ.target_eq_last
      rw [List.getLast?_eq_getElem?] at hlast'
      have hidx : Γ.vertices.length - 1 < Γ.vertices.length := by
        have := Γ.length_ge_two
        omega
      rw [List.getElem?_eq_getElem hidx] at hlast'
      have hiEq : i + 1 = Γ.vertices.length - 1 := by
        dsimp [i]
        have := Γ.length_ge_two
        omega
      simpa [hiEq] using Option.some.inj hlast'
    rw [hlast]
    exact right_mem_segment ℝ Γ.vertices[i] Γ.target
  have hAarcSourceMem : Aarc.source ∈ Aarc.carrier :=
    polygonalArc_source_mem Aarc
  have hterminalGateAvoid :
      terminalGate ∉
        (Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪
          Rbeta ∪ H ∪ Bad) := by
    intro hmem
    have hleft :
        terminalGate ∈
          TerminalSideRegion ∪ ({terminalGate, terminalSideSource} :
            Set (EuclideanSpace ℝ (Fin 2))) := by simp
    have hright :
        terminalGate ∈
          ((Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪
              Rbeta ∪ H) ∪ Bad) := by
      simpa only [Set.union_assoc] using hmem
    have : terminalGate ∈
        (TerminalSideRegion ∪ ({terminalGate, terminalSideSource} :
            Set (EuclideanSpace ℝ (Fin 2)))) ∩
          ((Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪
              Rbeta ∪ H) ∪ Bad) := ⟨hleft, hright⟩
    rw [hterminalSideAvoid] at this
    exact this
  have hAarcSourceNeGate : Aarc.source ≠ terminalGate := by
    intro hEq
    apply hterminalGateAvoid
    rw [← hEq]
    simp only [Set.mem_union]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hAarcSourceMem))))
  have hPsourceNotChain : P.source ∉ chain.carrier := by
    intro hz
    rw [hchainCarrier, hterminalSegmentCarrier] at hz
    rcases hz with (hz | hz) | hz
    · have hside : P.source ∈ SelectedSide := (hpredecessorSide hz).1
      exact hAarcSourceNotSide (by simpa [hPsource] using hside)
    · have hside : P.source ∈ SelectedSide := (happroachSide hz).1
      exact hAarcSourceNotSide (by simpa [hPsource] using hside)
    · have hz' := hsegmentVin hz
      rcases hz' with hzVin | hzGate
      · have hside : P.source ∈ SelectedSide := hVinSide hzVin
        exact hAarcSourceNotSide (by simpa [hPsource] using hside)
      · have : P.source = terminalGate := by simpa using hzGate
        exact hAarcSourceNeGate (by simpa [hPsource] using this)
  have hPtargetMemChain : P.target ∈ chain.carrier := by
    rw [hPtarget, ← hchainSource]
    exact polygonalArc_source_mem chain
  have hfiniteChain : Set.Finite (P.carrier ∩ chain.carrier) := by
    simpa [hchainCarrier, hterminalSegmentCarrier, Set.union_assoc] using hfinite
  obtain ⟨q, Pq, hqContact, hqNeSource, hPqSource, hPqTarget,
      hPqCarrier, hPqInterior, hPqMeetsChain, hPqInteriorAvoidsChain,
      hPqAlternative, hPqFirst, hPqFirstCarrier, hPqFirstOpen,
      hPqTransfer, firstCut, firstPiece, remainder, hfirstCutNotClean,
      hfirstCutInterior, hfirstPieceSource, hfirstPieceTarget, hremainderSource,
      hremainderTarget, hPqDecomposition, hfirstPieceRemainder,
      hfirstPieceDisjointChain, hremainderMeetsChain,
      hfirstPieceCarrier, hfirstPieceInterior, hfirstPieceInteriorPq,
      hremainderInteriorPq, hsplitTransfer⟩ :=
    PolygonalArcFiniteFirstContactPrefix P chain xClean hfiniteChain
      hPtargetMemChain hPsourceNotChain
  have hqNeTerminalGate : q ≠ terminalGate := by
    intro hEq
    have hqP : q ∈ P.carrier := hqContact.1
    have hqSide := hPcarrier hqP
    rcases hqSide with hqSide | hqSource
    · exact hterminalGateNotSide (by simpa [hEq] using hqSide)
    · have : Aarc.source = terminalGate := by
        simpa [hPsource, hEq] using hqSource.symm
      exact hAarcSourceNeGate this
  obtain ⟨lastGate', h', suffix, Cprev', approach', final',
      hlastGateNotClean, hhNotClean, hsuffixSource, hsuffixTarget,
      hsuffixCarrier, hsuffixAlternative, hCprevSource, hCprevTarget,
      happroach'Source, happroach'Target, hfinalSource, hfinalTarget,
      hCprevSide, happroach'Side, hfinalCarrier, hfinalVin,
      hfinalInteriorVin, hCprevChain, happroachChain, hfinalChain,
      hPqCprev, hPqApproach, hPqFinal,
      hCprevApproach, happroachFinal, hCprevFinal, hsuffixTransfer⟩ :=
    EndpointSidePrefixOrderedTerminalSuffix
      remainder chain predecessor approach terminalSegment SelectedSide Vin
        xClean q lastGate h terminalGate hchainSource hchainTarget
        hterminalSegmentSource hterminalSegmentTarget hterminalSegmentCarrier
        hchainVertices hchainCarrier hpredecessorApproach
        happroachTerminalSegment hpredecessorTerminalSegment hremainderTarget
        hqContact.2 hqNeTerminalGate hremainderMeetsChain
        hpredecessorSide happroachSide hpredecessorTarget happroachSource
        happroachTarget hsegmentVin hopenSegmentVin hVinSide
        hterminalGateNotSide
  obtain ⟨gateSide, hgateSideSource, hgateSideTarget, hgateSideCarrier,
      hgateSideInterior⟩ :=
    StraightSegmentPolygonalArc terminalGate terminalSideSource
      hgateNeTerminalSideSource
  obtain ⟨terminalSide, hterminalSideSource, hterminalSideTarget,
      hterminalSideCarrier, hterminalSideInterior⟩ :=
    StraightSegmentPolygonalArc terminalSideSource quadrantGate
      hterminalSideSourceNeQuadrant
  obtain ⟨terminalConnector, hterminalConnectorSource,
      hterminalConnectorTarget, hterminalConnectorCarrier,
      hterminalConnectorInterior⟩ :=
    StraightSegmentPolygonalArc quadrantGate BplusArc.target hquadrantNeTarget
  have hselectedDisjointTerminalSide :
      Disjoint SelectedSide (closure TerminalSideRegion) := by
    rw [Set.disjoint_left]
    intro z hzSide hzTerminal
    have hz :
        z ∈ SelectedSide ∩
      (closure TerminalSideRegion ∪ closure TerminalBridgeRegion ∪
            closure Qx) :=
      ⟨hzSide, Or.inl (Or.inl hzTerminal)⟩
    rw [hsideTerminalSep] at hz
    exact hz
  have hselectedDisjointTerminalBridge :
      Disjoint SelectedSide (closure TerminalBridgeRegion) := by
    rw [Set.disjoint_left]
    intro z hzSide hzTerminal
    have hz :
        z ∈ SelectedSide ∩
      (closure TerminalSideRegion ∪ closure TerminalBridgeRegion ∪
            closure Qx) :=
      ⟨hzSide, Or.inl (Or.inr hzTerminal)⟩
    rw [hsideTerminalSep] at hz
    exact hz
  have hselectedDisjointQx : Disjoint SelectedSide (closure Qx) := by
    rw [Set.disjoint_left]
    intro z hzSide hzQ
    have hz :
        z ∈ SelectedSide ∩
      (closure TerminalSideRegion ∪ closure TerminalBridgeRegion ∪
            closure Qx) :=
      ⟨hzSide, Or.inr hzQ⟩
    rw [hsideTerminalSep] at hz
    exact hz
  have hgateSideClosure :
      gateSide.carrier ⊆ closure TerminalSideRegion := by
    rw [hgateSideCarrier]
    exact segment_subset_closure_openSegment.trans
      (closure_mono hterminalSideOpen)
  have hterminalSideClosure :
      terminalSide.carrier ⊆ closure TerminalBridgeRegion := by
    rw [hterminalSideCarrier]
    exact segment_subset_closure_openSegment.trans
      (closure_mono hterminalBridgeOpen)
  have hfinalClosure : final'.carrier ⊆ closure Vin := by
    intro z hz
    rcases hfinalVin hz with hzVin | hzGate
    · exact subset_closure hzVin
    · have hzEq : z = terminalGate := by simpa using hzGate
      simpa [hzEq] using hgateClosure
  have hgateSideFinal :
      final'.carrier ∩ gateSide.carrier =
        ({terminalGate} : Set (EuclideanSpace ℝ (Fin 2))) := by
    apply Set.Subset.antisymm
    · intro z hz
      have hz' : z ∈ closure Vin ∩ closure TerminalSideRegion :=
        ⟨hfinalClosure hz.1, hgateSideClosure hz.2⟩
      rw [hclosureVinTerminalSide] at hz'
      exact hz'
    · intro z hz
      have hzEq : z = terminalGate := by simpa using hz
      subst z
      exact ⟨by
        rw [← hfinalTarget]
        exact polygonalArc_target_mem final', by
          rw [← hgateSideSource]
          exact polygonalArc_source_mem gateSide⟩
  have hgateSideTerminalSide :
      gateSide.carrier ∩ terminalSide.carrier =
        ({terminalSideSource} : Set (EuclideanSpace ℝ (Fin 2))) := by
    apply Set.Subset.antisymm
    · intro z hz
      have hz' :
          z ∈ closure TerminalSideRegion ∩ closure TerminalBridgeRegion :=
        ⟨hgateSideClosure hz.1, hterminalSideClosure hz.2⟩
      rw [hterminalClosuresMeet] at hz'
      exact hz'
    · intro z hz
      have hzEq : z = terminalSideSource := by simpa using hz
      subst z
      exact ⟨by
        rw [← hgateSideTarget]
        exact polygonalArc_target_mem gateSide, by
          rw [← hterminalSideSource]
          exact polygonalArc_source_mem terminalSide⟩
  have hpointAvoidOfVin {z : EuclideanSpace ℝ (Fin 2)} (hz : z ∈ Vin) :
      z ∉
        (Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪
          Rbeta ∪ H ∪ Bad) := by
    intro hzForbidden
    have : z ∈
        Vin ∩
          ((Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪
              Rbeta ∪ H) ∪ Bad) := by
      refine ⟨hz, ?_⟩
      simpa only [Set.union_assoc] using hzForbidden
    rw [hVinAvoid] at this
    exact this
  have hforbiddenNoHSubset :
      (Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪
          Rbeta ∪ Bad) ⊆
        (Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪
          Rbeta ∪ H ∪ Bad) := by
    intro z hz
    simp only [Set.mem_union] at hz ⊢
    tauto
  have hterminalSideSourceAvoid :
      terminalSideSource ∉
        (Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪
          Rbeta ∪ H ∪ Bad) := by
    intro hzForbidden
    have hzLeft :
        terminalSideSource ∈
          TerminalSideRegion ∪
            ({terminalGate, terminalSideSource} :
              Set (EuclideanSpace ℝ (Fin 2))) := by simp
    have hz :
        terminalSideSource ∈
          (TerminalSideRegion ∪
              ({terminalGate, terminalSideSource} :
                Set (EuclideanSpace ℝ (Fin 2)))) ∩
            ((Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪
                Rbeta ∪ H) ∪ Bad) := by
      refine ⟨hzLeft, ?_⟩
      simpa only [Set.union_assoc] using hzForbidden
    rw [hterminalSideAvoid] at hz
    exact hz
  have hquadrantAvoid :
      quadrantGate ∉
        (Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪
          Rbeta ∪ H ∪ Bad) := by
    intro hzForbidden
    have hzLeft :
        quadrantGate ∈
          TerminalBridgeRegion ∪
            ({terminalSideSource, quadrantGate} :
              Set (EuclideanSpace ℝ (Fin 2))) := by simp
    have hz :
        quadrantGate ∈
          (TerminalBridgeRegion ∪
              ({terminalSideSource, quadrantGate} :
                Set (EuclideanSpace ℝ (Fin 2)))) ∩
            ((Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪
                Rbeta ∪ H) ∪ Bad) := by
      refine ⟨hzLeft, ?_⟩
      simpa only [Set.union_assoc] using hzForbidden
    rw [hterminalBridgeAvoid] at hz
    exact hz
  have hAarcSourceNotGateSide : Aarc.source ∉ gateSide.carrier := by
    intro hz
    have hzLeft := hterminalSideSegment (by
      simpa [hgateSideCarrier] using hz)
    have hzRight :
        Aarc.source ∈
          ((Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪
              Rbeta ∪ H) ∪ Bad) := by
      simp only [Set.mem_union]
      exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hAarcSourceMem))))
    have :
        Aarc.source ∈
          (TerminalSideRegion ∪
              ({terminalGate, terminalSideSource} :
                Set (EuclideanSpace ℝ (Fin 2)))) ∩
            ((Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪
                Rbeta ∪ H) ∪ Bad) :=
      ⟨hzLeft, hzRight⟩
    rw [hterminalSideAvoid] at this
    exact this
  have hPqGateSide : Disjoint Pq.carrier gateSide.carrier := by
    rw [Set.disjoint_left]
    intro z hzPq hzGateSide
    rcases hPcarrier (hPqCarrier hzPq) with hzSide | hzSource
    · exact (Set.disjoint_left.mp hselectedDisjointTerminalSide hzSide)
        (hgateSideClosure hzGateSide)
    · have hzEq : z = Aarc.source := by simpa using hzSource
      exact hAarcSourceNotGateSide (by simpa [hzEq] using hzGateSide)
  have hCprevGateSide : Disjoint Cprev'.carrier gateSide.carrier := by
    rw [Set.disjoint_left]
    intro z hzC hzGate
    exact (Set.disjoint_left.mp hselectedDisjointTerminalSide
      (hCprevSide hzC).1) (hgateSideClosure hzGate)
  have happroachGateSide : Disjoint approach'.carrier gateSide.carrier := by
    rw [Set.disjoint_left]
    intro z hzC hzGate
    exact (Set.disjoint_left.mp hselectedDisjointTerminalSide
      (happroach'Side hzC).1) (hgateSideClosure hzGate)
  have hAarcSourceNotTerminalSide : Aarc.source ∉ terminalSide.carrier := by
    intro hz
    have hzLeft := hterminalBridgeSegment (by
      simpa [hterminalSideCarrier] using hz)
    have hzRight :
        Aarc.source ∈
          ((Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪
              Rbeta ∪ H) ∪ Bad) := by
      simp only [Set.mem_union]
      exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hAarcSourceMem))))
    have :
        Aarc.source ∈
          (TerminalBridgeRegion ∪
              ({terminalSideSource, quadrantGate} :
                Set (EuclideanSpace ℝ (Fin 2)))) ∩
            ((Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪
                Rbeta ∪ H) ∪ Bad) :=
      ⟨hzLeft, hzRight⟩
    rw [hterminalBridgeAvoid] at this
    exact this
  have hPqTerminalSide : Disjoint Pq.carrier terminalSide.carrier := by
    rw [Set.disjoint_left]
    intro z hzPq hzTerminal
    rcases hPcarrier (hPqCarrier hzPq) with hzSide | hzSource
    · exact (Set.disjoint_left.mp hselectedDisjointTerminalBridge hzSide)
        (hterminalSideClosure hzTerminal)
    · have hzEq : z = Aarc.source := by simpa using hzSource
      exact hAarcSourceNotTerminalSide (by simpa [hzEq] using hzTerminal)
  have hCprevTerminalSide : Disjoint Cprev'.carrier terminalSide.carrier := by
    rw [Set.disjoint_left]
    intro z hzC hzTerminal
    exact (Set.disjoint_left.mp hselectedDisjointTerminalBridge
      (hCprevSide hzC).1) (hterminalSideClosure hzTerminal)
  have happroachTerminalSide :
      Disjoint approach'.carrier terminalSide.carrier := by
    rw [Set.disjoint_left]
    intro z hzC hzTerminal
    exact (Set.disjoint_left.mp hselectedDisjointTerminalBridge
      (happroach'Side hzC).1) (hterminalSideClosure hzTerminal)
  have hfinalTerminalSide : Disjoint final'.carrier terminalSide.carrier := by
    rw [Set.disjoint_left]
    intro z hzFinal hzTerminal
    have hz :
        z ∈ closure Vin ∩ closure TerminalBridgeRegion :=
      ⟨hfinalClosure hzFinal, hterminalSideClosure hzTerminal⟩
    rw [hclosureVinTerminalBridge] at hz
    exact hz
  have hgateSideDisjointQx : Disjoint gateSide.carrier Qx := by
    rw [Set.disjoint_left]
    intro z hzGate hzQ
    have hz :
        z ∈ closure TerminalSideRegion ∩ closure Qx :=
      ⟨hgateSideClosure hzGate, subset_closure hzQ⟩
    rw [hterminalSideClosureQx] at hz
    exact hz
  have hAarcSourceNotConnector : Aarc.source ∉ terminalConnector.carrier := by
    intro hz
    by_cases hzEndpoints :
        Aarc.source ∈
          ({quadrantGate, BplusArc.target} :
            Set (EuclideanSpace ℝ (Fin 2)))
    · rcases hzEndpoints with hzQuad | hzTarget
      · have hEq : Aarc.source = quadrantGate := by simpa using hzQuad
        exact hquadrantAvoid (by
          rw [← hEq]
          simp only [Set.mem_union]
          exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hAarcSourceMem)))))
      · exact hAarcSourceNeTarget (by simpa using hzTarget)
    · have hzInterior : Aarc.source ∈ terminalConnector.relativeInterior := by
        rw [terminalConnector.relativeInterior_eq]
        refine ⟨hz, ?_⟩
        simpa [hterminalConnectorSource, hterminalConnectorTarget] using
          hzEndpoints
      have hzOpen : Aarc.source ∈
          openSegment ℝ quadrantGate BplusArc.target := by
        simpa [hterminalConnectorInterior] using hzInterior
      have hzForbidden :
          Aarc.source ∈
            (Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪
              Rbeta ∪ H ∪ Bad) := by
        simp only [Set.mem_union]
        exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hAarcSourceMem))))
      have :
          Aarc.source ∈
            openSegment ℝ quadrantGate BplusArc.target ∩
              (Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪
                Rbeta ∪ H ∪ Bad) :=
        ⟨hzOpen, hzForbidden⟩
      rw [hconnectorAvoid] at this
      exact this
  have hPqConnector :
      Disjoint Pq.carrier terminalConnector.carrier := by
    rw [Set.disjoint_left]
    intro z hzPq hzConnector
    rcases hPcarrier (hPqCarrier hzPq) with hzSide | hzSource
    · exact (Set.disjoint_left.mp hselectedDisjointQx hzSide)
        (subset_closure (hconnectorSegment (by
          simpa [hterminalConnectorCarrier] using hzConnector)))
    · have hzEq : z = Aarc.source := by simpa using hzSource
      exact hAarcSourceNotConnector (by simpa [hzEq] using hzConnector)
  have hCprevConnector :
      Disjoint Cprev'.carrier terminalConnector.carrier := by
    rw [Set.disjoint_left]
    intro z hzC hzConnector
    have hzVin := (hCprevSide hzC).2
    have hzQ := hconnectorSegment (by
      simpa [hterminalConnectorCarrier] using hzConnector)
    have hz : z ∈ Vin ∩ Qx := ⟨hzVin, hzQ⟩
    rw [hVinQx] at hz
    exact hz
  have happroachConnector :
      Disjoint approach'.carrier terminalConnector.carrier := by
    rw [Set.disjoint_left]
    intro z hzC hzConnector
    have hzVin := (happroach'Side hzC).2
    have hzQ := hconnectorSegment (by
      simpa [hterminalConnectorCarrier] using hzConnector)
    have hz : z ∈ Vin ∩ Qx := ⟨hzVin, hzQ⟩
    rw [hVinQx] at hz
    exact hz
  have hfinalConnector :
      Disjoint final'.carrier terminalConnector.carrier := by
    rw [Set.disjoint_left]
    intro z hzFinal hzConnector
    have hzQ := hconnectorSegment (by
      simpa [hterminalConnectorCarrier] using hzConnector)
    rcases hfinalVin hzFinal with hzVin | hzGate
    · have hz : z ∈ Vin ∩ Qx := ⟨hzVin, hzQ⟩
      rw [hVinQx] at hz
      exact hz
    · have hzEq : z = terminalGate := by simpa using hzGate
      exact hgateNotQx (by simpa [hzEq] using hzQ)
  have hgateSideConnector :
      Disjoint gateSide.carrier terminalConnector.carrier := by
    rw [Set.disjoint_left]
    intro z hzGate hzConnector
    exact Set.disjoint_left.mp hgateSideDisjointQx hzGate
      (hconnectorSegment (by
        simpa [hterminalConnectorCarrier] using hzConnector))
  have hfirstPieceSubsetPq : firstPiece.carrier ⊆ Pq.carrier := by
    rw [hPqDecomposition]
    exact Set.subset_union_left
  have hremainderSubsetPq : remainder.carrier ⊆ Pq.carrier := by
    rw [hPqDecomposition]
    exact Set.subset_union_right
  have hfirstPieceCprev : Disjoint firstPiece.carrier Cprev'.carrier :=
    hfirstPieceDisjointChain.mono_right hCprevChain
  have hfirstPieceApproach : Disjoint firstPiece.carrier approach'.carrier :=
    hfirstPieceDisjointChain.mono_right happroachChain
  have hfirstPieceFinal : Disjoint firstPiece.carrier final'.carrier :=
    hfirstPieceDisjointChain.mono_right hfinalChain
  have hfirstPieceGateSide : Disjoint firstPiece.carrier gateSide.carrier :=
    hPqGateSide.mono_left hfirstPieceSubsetPq
  have hremainderGateSide : Disjoint remainder.carrier gateSide.carrier :=
    hPqGateSide.mono_left hremainderSubsetPq
  have hfirstPieceTerminalSide :
      Disjoint firstPiece.carrier terminalSide.carrier :=
    hPqTerminalSide.mono_left hfirstPieceSubsetPq
  have hremainderTerminalSide :
      Disjoint remainder.carrier terminalSide.carrier :=
    hPqTerminalSide.mono_left hremainderSubsetPq
  have hfirstPieceConnector :
      Disjoint firstPiece.carrier terminalConnector.carrier :=
    hPqConnector.mono_left hfirstPieceSubsetPq
  have hremainderConnector :
      Disjoint remainder.carrier terminalConnector.carrier :=
    hPqConnector.mono_left hremainderSubsetPq
  have hfirstCutAvoid :
      firstCut ∉
        (Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪
          Rbeta ∪ H ∪ Bad) := by
    intro hzForbidden
    have hcutP : firstCut ∈ P.relativeInterior :=
      hPqInterior hfirstCutInterior
    by_cases hzH : firstCut ∈ H
    · exact hfirstCutNotClean ((hxClean firstCut).mpr ⟨hcutP, hzH⟩)
    · have hzNoH :
          firstCut ∈
            (Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪
              Rbeta ∪ Bad) := by
        rcases hzForbidden with (((((hzA | hzB) | hzBplus) | hzRbeta) | hzH') | hzBad)
        · exact Or.inl (Or.inl (Or.inl (Or.inl hzA)))
        · exact Or.inl (Or.inl (Or.inl (Or.inr hzB)))
        · exact Or.inl (Or.inl (Or.inr hzBplus))
        · exact Or.inl (Or.inr hzRbeta)
        · exact False.elim (hzH hzH')
        · exact Or.inr hzBad
      have hz :
          firstCut ∈ P.relativeInterior ∩
            (Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪
              Rbeta ∪ Bad) := ⟨hcutP, hzNoH⟩
      rw [hPavoid] at hz
      exact hz
  let prefixPiece : ℕ → PolygonalArc :=
    fun i =>
      match i with
      | 0 => firstPiece
      | 1 => remainder
      | 2 => Cprev'
      | 3 => approach'
      | 4 => final'
      | 5 => gateSide
      | _ => firstPiece
  let xPrefix :=
    xClean.filter (fun z => z ∈ Pq.relativeInterior)
  let E : EndpointSidePrefixAttachment
      Aarc Barc BplusArc Rbeta H Bad DeltaX Qx K XA :=
    { r := 5
      prefixPiece := prefixPiece
      xPrefix := xPrefix
      chargePrefix := charge
      omega := quadrantGate
      terminalSide := terminalSide
      terminalConnector := terminalConnector
      presentation_carrier := hK
      copied_prefix_disjoint_tail := hAarcRbeta
      prefix_source := by
        simp [prefixPiece, hfirstPieceSource, hPsource]
      prefix_target := by
        simp [prefixPiece, hgateSideTarget, hterminalSideSource]
      prefix_consecutive_sources := by
        intro i hi
        interval_cases i
        · simpa [prefixPiece] using
            hfirstPieceTarget.trans hremainderSource.symm
        · simpa [prefixPiece] using hremainderTarget.trans hCprevSource.symm
        · simpa [prefixPiece] using hCprevTarget.trans happroach'Source.symm
        · simpa [prefixPiece] using happroach'Target.trans hfinalSource.symm
        · simpa [prefixPiece] using hfinalTarget.trans hgateSideSource.symm
      prefix_consecutive_meets := by
        intro i hi
        interval_cases i
        · rw [show prefixPiece 0 = firstPiece by rfl,
            show prefixPiece (0 + 1) = remainder by rfl,
            hfirstPieceTarget]
          exact hfirstPieceRemainder
        · rw [show prefixPiece 1 = remainder by rfl,
            show prefixPiece (1 + 1) = Cprev' by rfl, hremainderTarget]
          exact hPqCprev
        · rw [show prefixPiece 2 = Cprev' by rfl,
            show prefixPiece (2 + 1) = approach' by rfl, hCprevTarget]
          exact hCprevApproach
        · rw [show prefixPiece 3 = approach' by rfl,
            show prefixPiece (3 + 1) = final' by rfl, happroach'Target]
          exact happroachFinal
        · rw [show prefixPiece 4 = final' by rfl,
            show prefixPiece (4 + 1) = gateSide by rfl, hfinalTarget]
          exact hgateSideFinal
      prefix_nonconsecutive_disjoint := by
        intro i j hi hj hij
        interval_cases i <;> interval_cases j <;>
          simp_all [prefixPiece]
      prefix_internal_gates_avoid := by
        intro i hi
        interval_cases i
        · simpa [prefixPiece, hfirstPieceTarget] using hfirstCutAvoid
        · simp only [prefixPiece, hremainderTarget]
          have hqVin : q ∈ Vin := (hCprevSide (by
            rw [← hCprevSource]
            exact polygonalArc_source_mem Cprev')).2
          exact hpointAvoidOfVin hqVin
        · simp only [prefixPiece, hCprevTarget]
          have hlastVin : lastGate' ∈ Vin := (hCprevSide (by
            rw [← hCprevTarget]
            exact polygonalArc_target_mem Cprev')).2
          exact hpointAvoidOfVin hlastVin
        · simp only [prefixPiece, happroach'Target]
          have hh'Vin : h' ∈ Vin := (happroach'Side (by
            rw [← happroach'Target]
            exact polygonalArc_target_mem approach')).2
          exact hpointAvoidOfVin hh'Vin
        · simpa [prefixPiece, hfinalTarget] using hterminalGateAvoid
      prefix_relative_interiors_avoid := by
        intro i hi
        interval_cases i
        · rw [show prefixPiece 0 = firstPiece by rfl]
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro z hz
          have hzP : z ∈ P.relativeInterior :=
            hPqInterior (hfirstPieceInteriorPq hz.1)
          have hz' :
              z ∈ P.relativeInterior ∩
                (Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪
                  Rbeta ∪ Bad) := ⟨hzP, hz.2⟩
          rw [hPavoid] at hz'
          exact hz'
        · rw [show prefixPiece 1 = remainder by rfl]
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro z hz
          have hzP : z ∈ P.relativeInterior :=
            hPqInterior (hremainderInteriorPq hz.1)
          have hz' :
              z ∈ P.relativeInterior ∩
                (Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪
                  Rbeta ∪ Bad) := ⟨hzP, hz.2⟩
          rw [hPavoid] at hz'
          exact hz'
        · rw [show prefixPiece 2 = Cprev' by rfl]
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro z hz
          exact hpointAvoidOfVin (hCprevSide
            ((by
              rw [Cprev'.relativeInterior_eq] at hz
              exact hz.1.1))).2 (hforbiddenNoHSubset hz.2)
        · rw [show prefixPiece 3 = approach' by rfl]
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro z hz
          exact hpointAvoidOfVin (happroach'Side
            ((by
              rw [approach'.relativeInterior_eq] at hz
              exact hz.1.1))).2 (hforbiddenNoHSubset hz.2)
        · rw [show prefixPiece 4 = final' by rfl]
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro z hz
          exact hpointAvoidOfVin (hfinalInteriorVin hz.1)
            (hforbiddenNoHSubset hz.2)
        · rw [show prefixPiece 5 = gateSide by rfl]
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro z hz
          have hzRegion : z ∈
              TerminalSideRegion ∪
                ({terminalGate, terminalSideSource} :
                  Set (EuclideanSpace ℝ (Fin 2))) :=
            Or.inl (hterminalSideOpen (by
              simpa [hgateSideInterior] using hz.1))
          have hz' :
              z ∈
                (TerminalSideRegion ∪
                    ({terminalGate, terminalSideSource} :
                      Set (EuclideanSpace ℝ (Fin 2)))) ∩
                  ((Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪
                      Rbeta ∪ H) ∪ Bad) := by
            refine ⟨hzRegion, ?_⟩
            exact hforbiddenNoHSubset hz.2
          rw [hterminalSideAvoid] at hz'
          exact hz'
      xPrefix_spec := by
        intro z
        constructor
        · intro hz
          have hz' := (Finset.mem_filter.mp hz)
          have hzCarrier : z ∈ Pq.carrier := by
            rw [Pq.relativeInterior_eq] at hz'
            exact hz'.2.1
          rcases hPqDecomposition ▸ hzCarrier with hzFirst | hzRemainder
          · refine ⟨⟨0, by omega, ?_⟩, ?_⟩
            · rw [show prefixPiece 0 = firstPiece by rfl,
                firstPiece.relativeInterior_eq]
              refine ⟨hzFirst, ?_⟩
              intro hzEndpoints
              rcases hzEndpoints with hzSource | hzCut
              · have hzEq : z = P.source := by
                  simpa [hfirstPieceSource] using hzSource
                have hzPqRI := hz'.2
                rw [Pq.relativeInterior_eq] at hzPqRI
                exact hzPqRI.2 (by
                  simp [hzEq, hPqSource])
              · have hzEq : z = firstCut := by
                  simpa [hfirstPieceTarget] using hzCut
                exact hfirstCutNotClean (by simpa [hzEq] using hz'.1)
            · exact (hxClean z).mp hz'.1 |>.2
          · refine ⟨⟨1, by omega, ?_⟩, ?_⟩
            · rw [show prefixPiece 1 = remainder by rfl,
                remainder.relativeInterior_eq]
              refine ⟨hzRemainder, ?_⟩
              intro hzEndpoints
              rcases hzEndpoints with hzCut | hzTarget
              · have hzEq : z = firstCut := by
                  simpa [hremainderSource] using hzCut
                exact hfirstCutNotClean (by simpa [hzEq] using hz'.1)
              · have hzEq : z = q := by
                  simpa [hremainderTarget] using hzTarget
                have hzPqRI := hz'.2
                rw [Pq.relativeInterior_eq] at hzPqRI
                exact hzPqRI.2 (by
                  simp [hzEq, hPqTarget])
            · exact (hxClean z).mp hz'.1 |>.2
        · rintro ⟨⟨i, hi, hzPiece⟩, hzH⟩
          have hzPq : z ∈ Pq.relativeInterior := by
            interval_cases i
            · exact hfirstPieceInteriorPq (by
                simpa [prefixPiece] using hzPiece)
            · exact hremainderInteriorPq (by
                simpa [prefixPiece] using hzPiece)
            · exfalso
              change z ∈ Cprev'.relativeInterior at hzPiece
              have hzVin : z ∈ Vin := (hCprevSide (by
                rw [Cprev'.relativeInterior_eq] at hzPiece
                exact hzPiece.1)).2
              exact hpointAvoidOfVin hzVin (by
                simp only [Set.mem_union]
                exact Or.inl (Or.inr hzH))
            · exfalso
              change z ∈ approach'.relativeInterior at hzPiece
              have hzVin : z ∈ Vin := (happroach'Side (by
                rw [approach'.relativeInterior_eq] at hzPiece
                exact hzPiece.1)).2
              exact hpointAvoidOfVin hzVin (by
                simp only [Set.mem_union]
                exact Or.inl (Or.inr hzH))
            · exfalso
              have hzVin : z ∈ Vin := hfinalInteriorVin (by
                simpa [prefixPiece] using hzPiece)
              exact hpointAvoidOfVin hzVin (by
                simp only [Set.mem_union]
                exact Or.inl (Or.inr hzH))
            · exfalso
              have hzOpen : z ∈
                  openSegment ℝ terminalGate terminalSideSource := by
                simpa [prefixPiece, hgateSideInterior] using hzPiece
              have hzRegion :
                  z ∈ TerminalSideRegion ∪
                    ({terminalGate, terminalSideSource} :
                      Set (EuclideanSpace ℝ (Fin 2))) :=
                Or.inl (hterminalSideOpen hzOpen)
              have hz' :
                  z ∈
                    (TerminalSideRegion ∪
                        ({terminalGate, terminalSideSource} :
                          Set (EuclideanSpace ℝ (Fin 2)))) ∩
                      ((Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪
                          Rbeta ∪ H) ∪ Bad) := by
                refine ⟨hzRegion, ?_⟩
                simp only [Set.mem_union]
                exact Or.inl (Or.inr hzH)
              rw [hterminalSideAvoid] at hz'
              exact hz'
          apply Finset.mem_filter.mpr
          refine ⟨(hxClean z).mpr ⟨hPqInterior hzPq, hzH⟩, hzPq⟩
      chargePrefix_mem := by
        intro z hz
        exact hchargeMem z (Finset.mem_filter.mp hz).1
      chargePrefix_injective := by
        intro z w hz hw hEq
        exact hchargeInj z w (Finset.mem_filter.mp hz).1
          (Finset.mem_filter.mp hw).1 hEq
      xPrefix_clean := by
        intro z hz
        have hzFilter := Finset.mem_filter.mp hz
        obtain ⟨hzBad, hzPoints, j, hj, hzOld, hUnique⟩ :=
          hclean z hzFilter.1
        obtain ⟨s, hsSpec, hsUnique⟩ := hUnique
        have hzNeq : z ≠ q := by
          intro hEq
          have hzEndpoints : z ∈
              ({Pq.source, Pq.target} :
                Set (EuclideanSpace ℝ (Fin 2))) := by
            simp [hEq, hPqTarget]
          have hzRI := hzFilter.2
          rw [Pq.relativeInterior_eq] at hzRI
          exact hzRI.2 hzEndpoints
        have hzCutNe : z ≠ firstCut := by
          intro hEq
          exact hfirstCutNotClean (by simpa [hEq] using hzFilter.1)
        have hzPqCarrier : z ∈ Pq.carrier := by
          rw [Pq.relativeInterior_eq] at hzFilter
          exact hzFilter.2.1
        rcases hPqDecomposition ▸ hzPqCarrier with hzFirst | hzRemainder
        · obtain ⟨j', hj', hzNew, c, hc, hdir⟩ :=
            hsplitTransfer firstPiece (by simp) z j hj hzOld hzFirst hzCutNe
              hzNeq
          refine ⟨hzBad, hzPoints, 0, by omega, j', hj', ?_, ?_⟩
          · simpa [prefixPiece] using hzNew
          · refine ⟨s, ?_, ?_⟩
            · refine ⟨hsSpec.1, hsSpec.2.1, ?_⟩
              intro hparallel
              rcases hparallel with ⟨d, hd⟩
              apply hsSpec.2.2
              refine ⟨d * c, ?_⟩
              change s.2 - s.1 =
                d • (firstPiece.vertices[j' + 1] - firstPiece.vertices[j']) at hd
              rw [hdir] at hd
              simpa [mul_smul] using hd
            · intro t ht
              apply hsUnique
              refine ⟨ht.1, ht.2.1, ?_⟩
              intro hparallel
              rcases hparallel with ⟨d, hd⟩
              apply ht.2.2
              refine ⟨d * c⁻¹, ?_⟩
              change t.2 - t.1 = (d * c⁻¹) •
                (firstPiece.vertices[j' + 1] - firstPiece.vertices[j'])
              rw [hdir]
              calc
                t.2 - t.1 = d • (P.vertices[j + 1] - P.vertices[j]) := hd
                _ = (d * c⁻¹) •
                      (c • (P.vertices[j + 1] - P.vertices[j])) := by
                  have hcoef : (d * c⁻¹) * c = d := by
                    field_simp
                  rw [← mul_smul, hcoef]
        · obtain ⟨j', hj', hzNew, c, hc, hdir⟩ :=
            hsplitTransfer remainder (by simp) z j hj hzOld hzRemainder hzCutNe
              hzNeq
          refine ⟨hzBad, hzPoints, 1, by omega, j', hj', ?_, ?_⟩
          · simpa [prefixPiece] using hzNew
          · refine ⟨s, ?_, ?_⟩
            · refine ⟨hsSpec.1, hsSpec.2.1, ?_⟩
              intro hparallel
              rcases hparallel with ⟨d, hd⟩
              apply hsSpec.2.2
              refine ⟨d * c, ?_⟩
              change s.2 - s.1 =
                d • (remainder.vertices[j' + 1] - remainder.vertices[j']) at hd
              rw [hdir] at hd
              simpa [mul_smul] using hd
            · intro t ht
              apply hsUnique
              refine ⟨ht.1, ht.2.1, ?_⟩
              intro hparallel
              rcases hparallel with ⟨d, hd⟩
              apply ht.2.2
              refine ⟨d * c⁻¹, ?_⟩
              change t.2 - t.1 = (d * c⁻¹) •
                (remainder.vertices[j' + 1] - remainder.vertices[j'])
              rw [hdir]
              calc
                t.2 - t.1 = d • (P.vertices[j + 1] - P.vertices[j]) := hd
                _ = (d * c⁻¹) •
                      (c • (P.vertices[j + 1] - P.vertices[j])) := by
                  have hcoef : (d * c⁻¹) * c = d := by
                    field_simp
                  rw [← mul_smul, hcoef]
      terminal_source_mem_delta := by
        simpa [hterminalSideSource] using hterminalSideSourceDelta
      terminal_source_not_mem_Q := by
        rw [hterminalSideSource]
        intro hzQ
        have hzSeg :
            terminalSideSource ∈
              segment ℝ terminalSideSource quadrantGate :=
          left_mem_segment ℝ terminalSideSource quadrantGate
        have hz :
            terminalSideSource ∈
              segment ℝ terminalSideSource quadrantGate ∩ Qx :=
          ⟨hzSeg, hzQ⟩
        rw [hterminalBridgeMeetsQx] at hz
        have : terminalSideSource = quadrantGate := by simpa using hz
        exact hterminalSideSourceNeQuadrant this
      terminal_source_avoid := by
        simpa [hterminalSideSource] using hterminalSideSourceAvoid
      terminal_side_target := hterminalSideTarget
      terminal_connector_source := hterminalConnectorSource
      terminal_connector_target := hterminalConnectorTarget
      omega_mem_Q := hquadrantMemQx
      omega_ne_target := hquadrantNeTarget
      omega_avoid := hquadrantAvoid
      terminal_side_subset_delta := by
        intro z hz
        have hz' := hterminalBridgeSegment (by
          simpa [hterminalSideCarrier] using hz)
        rcases hz' with hzRegion | hzEndpoint
        · exact hTerminalBridgeDelta hzRegion
        · rcases hzEndpoint with hzSource | hzQuad
          · have hzEq : z = terminalSideSource := by simpa using hzSource
            simpa [hzEq] using hterminalSideSourceDelta
          · have hzEq : z = quadrantGate := by simpa using hzQuad
            exact hQxDelta (by simpa [hzEq] using hquadrantMemQx)
      terminal_side_meets_Q := by
        simpa [hterminalSideCarrier] using hterminalBridgeMeetsQx
      terminal_side_relativeInterior_avoid := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro z hz
        have hzRegion :
            z ∈ TerminalBridgeRegion ∪
              ({terminalSideSource, quadrantGate} :
                Set (EuclideanSpace ℝ (Fin 2))) :=
          Or.inl (hterminalBridgeOpen (by
            simpa [hterminalSideInterior] using hz.1))
        have hz' :
            z ∈
              (TerminalBridgeRegion ∪
                  ({terminalSideSource, quadrantGate} :
                    Set (EuclideanSpace ℝ (Fin 2)))) ∩
                ((Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪
                    Rbeta ∪ H) ∪ Bad) := by
          refine ⟨hzRegion, ?_⟩
          simpa only [Set.union_assoc] using hz.2
        rw [hterminalBridgeAvoid] at hz'
        exact hz'
      terminal_connector_subset_Q := by
        simpa [hterminalConnectorCarrier] using hconnectorSegment
      terminal_connector_relativeInterior_avoid := by
        simpa [hterminalConnectorInterior] using hconnectorAvoid
      predecessor_meets_terminal := by
        simpa [prefixPiece, hterminalSideSource] using hgateSideTerminalSide
      earlier_prefix_disjoint_terminal := by
        intro i hi
        interval_cases i <;>
          simp [prefixPiece, hfirstPieceTerminalSide,
            hremainderTerminalSide, hCprevTerminalSide,
            happroachTerminalSide, hfinalTerminalSide]
      prefix_disjoint_terminal_connector := by
        intro i hi
        interval_cases i <;>
          simp [prefixPiece, hfirstPieceConnector, hremainderConnector,
            hCprevConnector,
            happroachConnector, hfinalConnector, hgateSideConnector] }
  refine ⟨E, ?_⟩
  refine ⟨by simpa [E, prefixPiece, hfirstPieceSource, hPsource], ?_⟩
  refine ⟨?_, ?_⟩
  · simpa [E, prefixPiece] using hfirstPieceCarrier.trans hfirst.choose_spec.1
  refine ⟨?_, by simp [E], h', lastGate', Vin, ?_⟩
  · simpa [E, prefixPiece] using
      hfirstPieceInterior.trans hfirst.choose_spec.2
  simp [E, prefixPiece]
  exact ⟨Set.subset_inter_iff.mp hCprevSide,
    Set.subset_inter_iff.mp happroach'Side, hCprevTarget, happroach'Source,
    hCprevApproach, happroach'Target, hfinalSource, hfinalTarget,
    happroachFinal, hfinalCarrier, hCprevFinal, hgateSideSource,
    hgateSideFinal, hgateSideCarrier, hterminalSideCarrier,
    hterminalConnectorCarrier⟩
