import ChallengeDeps
import Submission.Helpers

open LeanEval.GroupTheory.BooneHigmanSimpleProblem
open Submission.Helpers

namespace Submission

theorem boone_higman_simple {G : Type*} [Group G] [IsSimpleGroup G]
    {n : ℕ} (φ : FreeGroup (Fin n) →* G)
    (hsurj : Function.Surjective φ)
    (hker : (MonoidHom.ker φ).IsNormalClosureFG) :
    WordProblemSolvable φ := by
  classical
  unfold WordProblemSolvable
  obtain ⟨S, hSfinite, hSclosure⟩ := hker
  let relatorElements : List (FreeGroup (Fin n)) := hSfinite.toFinset.toList
  let rels : List (Word n) := relatorElements.map FreeGroup.toWord
  have hwordSet : wordSet rels = S := by
    ext x
    simp [wordSet, rels, relatorElements, FreeGroup.mk_toWord]
  have hclosure : Subgroup.normalClosure (wordSet rels) = MonoidHom.ker φ := by
    rw [hwordSet]
    exact hSclosure
  have hpositive (w : Word n) :
      (∃ certificate, Certifies rels w certificate) ↔ φ (FreeGroup.mk w) = 1 := by
    rw [← mem_normalClosure_iff_exists_certificate, hclosure]
    exact MonoidHom.mem_ker
  have hwordSet_append (w : Word n) :
      wordSet (rels ++ [w]) = wordSet rels ∪ {FreeGroup.mk w} := by
    ext x
    simp [wordSet, or_comm, eq_comm]
  have hker_ne_top : MonoidHom.ker φ ≠ ⊤ := by
    intro htop
    obtain ⟨g, hg⟩ := exists_ne (1 : G)
    obtain ⟨x, hx⟩ := hsurj g
    have hxker : x ∈ MonoidHom.ker φ := by rw [htop]; trivial
    have hxone : φ x = 1 := MonoidHom.mem_ker.mp hxker
    exact hg (hx.symm.trans hxone)
  have simple_normalClosure_top {a : G} (ha : a ≠ 1) :
      Subgroup.normalClosure ({a} : Set G) = ⊤ := by
    rcases (inferInstance : (Subgroup.normalClosure ({a} : Set G)).Normal).eq_bot_or_eq_top with
      hbot | htop
    · exfalso
      apply ha
      have hamem := Subgroup.subset_normalClosure (Set.mem_singleton a)
      rw [hbot] at hamem
      simpa using hamem
    · exact htop
  have htop_iff (w : Word n) :
      Subgroup.normalClosure (wordSet (rels ++ [w])) = ⊤ ↔
        φ (FreeGroup.mk w) ≠ 1 := by
    constructor
    · intro htop hw
      apply hker_ne_top
      apply le_antisymm le_top
      rw [← htop]
      apply Subgroup.normalClosure_le_normal
      intro x hx
      rw [hwordSet_append w, hwordSet] at hx
      rcases hx with hx | hx
      · rw [← hSclosure]
        exact Subgroup.subset_normalClosure hx
      · rw [Set.mem_singleton_iff] at hx
        subst x
        exact MonoidHom.mem_ker.mpr hw
    · intro hw
      let N := Subgroup.normalClosure (wordSet (rels ++ [w]))
      have hker_le : MonoidHom.ker φ ≤ N := by
        rw [← hclosure]
        change Subgroup.normalClosure (wordSet rels) ≤
          Subgroup.normalClosure (wordSet (rels ++ [w]))
        rw [hwordSet_append w]
        exact Subgroup.normalClosure_mono Set.subset_union_left
      have hword : FreeGroup.mk w ∈ wordSet (rels ++ [w]) :=
        ⟨w, by simp, rfl⟩
      have himage : φ (FreeGroup.mk w) ∈ φ '' wordSet (rels ++ [w]) :=
        ⟨FreeGroup.mk w, hword, rfl⟩
      have hsingle : Subgroup.normalClosure ({φ (FreeGroup.mk w)} : Set G) = ⊤ :=
        simple_normalClosure_top hw
      have hmap : N.map φ = ⊤ := by
        change (Subgroup.normalClosure (wordSet (rels ++ [w]))).map φ = ⊤
        rw [Subgroup.map_normalClosure _ φ hsurj]
        apply le_antisymm le_top
        rw [← hsingle]
        exact Subgroup.normalClosure_mono (Set.singleton_subset_iff.mpr himage)
      calc
        N = (N.map φ).comap φ := (Subgroup.comap_map_eq_self hker_le).symm
        _ = ⊤ := by rw [hmap]; simp
  have hnegative (w : Word n) :
      (∃ certificates, NegativeCertifies rels w certificates) ↔
        φ (FreeGroup.mk w) ≠ 1 :=
    exists_negativeCertifies_iff.trans (htop_iff w)
  have hexists (w : Word n) : ∃ code, EncodedDecisionCertifies rels w code := by
    by_cases hw : φ (FreeGroup.mk w) = 1
    · obtain ⟨certificate, hcertificate⟩ := (hpositive w).mpr hw
      let decisionCertificate : DecisionCertificate n := Sum.inl certificate
      refine ⟨encodeDecisionCertificate decisionCertificate, ?_⟩
      simp [EncodedDecisionCertifies, decisionCertificate, DecisionCertifies, hcertificate]
    · obtain ⟨certificates, hcertificates⟩ := (hnegative w).mpr hw
      let decisionCertificate : DecisionCertificate n := Sum.inr certificates
      refine ⟨encodeDecisionCertificate decisionCertificate, ?_⟩
      simp [EncodedDecisionCertifies, decisionCertificate, DecisionCertifies, hcertificates]
  have hsearchable : ComputablePred fun p : Word n × ℕ =>
      EncodedDecisionCertifies rels p.1 p.2 :=
    (primrecRel_encodedDecisionCertifies rels).computablePred
  have hfind : Computable fun w : Word n => Nat.find (hexists w) :=
    Computable.find hsearchable hexists
  let decision (w : Word n) : Bool := @codeIsPositive n (Nat.find (hexists w))
  have hdecision : Computable decision :=
    (@primrec_codeIsPositive n).to_comp.comp hfind
  have hdecision_spec (w : Word n) :
      (decision w : Prop) ↔ φ (FreeGroup.mk w) = 1 := by
    let code := Nat.find (hexists w)
    have hvalid : EncodedDecisionCertifies rels w code := Nat.find_spec (hexists w)
    cases hdecode : @decodeDecisionCertificate n code with
    | none =>
        simp [EncodedDecisionCertifies, hdecode] at hvalid
    | some decisionCertificate =>
        cases decisionCertificate with
        | inl certificate =>
            have hcertificate : Certifies rels w certificate := by
              simpa [EncodedDecisionCertifies, hdecode, DecisionCertifies] using hvalid
            constructor
            · intro _
              exact (hpositive w).mp ⟨certificate, hcertificate⟩
            · intro _
              simp [decision, code, codeIsPositive, hdecode]
        | inr certificates =>
            have hcertificates : NegativeCertifies rels w certificates := by
              simpa [EncodedDecisionCertifies, hdecode, DecisionCertifies] using hvalid
            have hne : φ (FreeGroup.mk w) ≠ 1 :=
              (hnegative w).mp ⟨certificates, hcertificates⟩
            constructor
            · intro hpositiveCode
              simp [decision, code, codeIsPositive, hdecode] at hpositiveCode
            · intro hw
              exact (hne hw).elim
  refine ComputablePred.computable_iff.mpr ⟨decision, hdecision, ?_⟩
  funext w
  exact propext (hdecision_spec w).symm

end Submission
