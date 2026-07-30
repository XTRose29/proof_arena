import ChallengeDeps
import Submission.Helpers

open LeanEval.GroupTheory.BooneHigmanEmbedding
open Submission.Helpers

namespace Submission

theorem boone_higman_embedding {G H K : Type*} [Group G] [Group H] [Group K]
    [IsSimpleGroup H] [Group.IsFinitelyPresented K]
    (f : G →* H) (hf : Function.Injective f)
    (g : H →* K) (hg : Function.Injective g)
    {n : ℕ} (φ : FreeGroup (Fin n) →* G)
    (hsurj : Function.Surjective φ)
    (hker : (MonoidHom.ker φ).IsNormalClosureFG) :
    WordProblemSolvable φ := by
  classical
  unfold WordProblemSolvable
  obtain ⟨m, presentation, hpresentation, hpresentationKer⟩ :=
    Group.IsFinitelyPresented.out (G := K)
  obtain ⟨relationSet, hrelationSetFinite, hrelationSetKer⟩ := hpresentationKer
  let relations : List (Word m) :=
    hrelationSetFinite.toFinset.toList.map FreeGroup.toWord
  have hrelatorSet : relatorSet relations = relationSet := by
    ext x
    simp [relations, relatorSet, FreeGroup.mk_toWord]
  have hbase :
      Subgroup.normalClosure (relatorSet relations) = MonoidHom.ker presentation := by
    rw [hrelatorSet, hrelationSetKer]
  let embedding : FreeGroup (Fin n) →* K := g.comp (f.comp φ)
  let generatorLift : Fin n → FreeGroup (Fin m) := fun generator =>
    Classical.choose (hpresentation (embedding (FreeGroup.of generator)))
  have hgeneratorLift (generator : Fin n) :
      presentation (generatorLift generator) = embedding (FreeGroup.of generator) :=
    Classical.choose_spec (hpresentation (embedding (FreeGroup.of generator)))
  let images : Fin n → Word m := fun generator => (generatorLift generator).toWord
  have himages (generator : Fin n) :
      presentation (FreeGroup.mk (images generator)) = embedding (FreeGroup.of generator) := by
    rw [show images generator = (generatorLift generator).toWord by rfl,
      FreeGroup.mk_toWord]
    exact hgeneratorLift generator
  let lifted : FreeGroup (Fin n) →* FreeGroup (Fin m) :=
    FreeGroup.lift fun generator => FreeGroup.mk (images generator)
  have hlifted : presentation.comp lifted = embedding := by
    apply FreeGroup.ext_hom
    intro generator
    simpa [lifted] using himages generator
  have hsubstitute (word : Word n) :
      presentation (FreeGroup.mk (substitute images word)) = embedding (FreeGroup.mk word) := by
    rw [mk_substitute]
    change (presentation.comp lifted) (FreeGroup.mk word) = embedding (FreeGroup.mk word)
    rw [hlifted]
  have hsubstituteComputable : Computable (substitute images) :=
    (primrec_substitute images).to_comp
  have hembedding_one (word : Word n) :
      embedding (FreeGroup.mk word) = 1 ↔ φ (FreeGroup.mk word) = 1 := by
    constructor
    · intro hembedding
      apply hf
      apply hg
      simpa [embedding] using hembedding
    · intro hword
      simp [embedding, hword]
  have hequalityRE : REPred (fun word : Word n => φ (FreeGroup.mk word) = 1) := by
    refine (normalClosure_re (fun _ : Word n => relations) (substitute images)
      (Computable.const relations) hsubstituteComputable).of_eq fun word => ?_
    rw [hbase, MonoidHom.mem_ker, hsubstitute, hembedding_one]
  obtain ⟨nonidentity, hnonidentity⟩ := exists_ne (1 : H)
  let targetLift : FreeGroup (Fin m) :=
    Classical.choose (hpresentation (g nonidentity))
  have htargetLift : presentation targetLift = g nonidentity :=
    Classical.choose_spec (hpresentation (g nonidentity))
  let targetWord : Word m := targetLift.toWord
  have htargetWord : presentation (FreeGroup.mk targetWord) = g nonidentity := by
    rw [show targetWord = targetLift.toWord by rfl, FreeGroup.mk_toWord]
    exact htargetLift
  let augmentedRelations : Word n → List (Word m) := fun word =>
    substitute images word :: relations
  have haugmentedRelations : Computable augmentedRelations :=
    Computable.list_cons.comp hsubstituteComputable (Computable.const relations)
  have hsimple (element : H) :
      g nonidentity ∈ Subgroup.normalClosure ({g element} : Set K) ↔ element ≠ 1 := by
    constructor
    · intro hmember helement
      subst element
      have hclosure :
          Subgroup.normalClosure ({g (1 : H)} : Set K) = (⊥ : Subgroup K) := by
        rw [Subgroup.normalClosure_eq_bot_iff]
        intro x hx
        simpa using hx
      rw [hclosure] at hmember
      apply hnonidentity
      apply hg
      simpa using hmember
    · intro helement
      have hclosure :
          Subgroup.normalClosure ({element} : Set H) = (⊤ : Subgroup H) := by
        rcases (Subgroup.normalClosure_normal :
          (Subgroup.normalClosure ({element} : Set H)).Normal).eq_bot_or_eq_top with
          hbottom | htop
        · exfalso
          apply helement
          have hmember := Subgroup.subset_normalClosure
            (s := ({element} : Set H)) (Set.mem_singleton element)
          rw [hbottom] at hmember
          simpa using hmember
        · exact htop
      have hmember : nonidentity ∈ Subgroup.normalClosure ({element} : Set H) := by
        rw [hclosure]
        exact Subgroup.mem_top nonidentity
      have hmapped :
          g nonidentity ∈ (Subgroup.normalClosure ({element} : Set H)).map g :=
        Subgroup.mem_map_of_mem g hmember
      have himage :
          g nonidentity ∈ Subgroup.normalClosure (g '' ({element} : Set H)) :=
        Subgroup.map_normalClosure_le ({element} : Set H) g hmapped
      simpa using himage
  have hinequalityRaw : REPred (fun word : Word n =>
      FreeGroup.mk targetWord ∈
        Subgroup.normalClosure (relatorSet (augmentedRelations word))) :=
    normalClosure_re augmentedRelations (fun _ => targetWord) haugmentedRelations
      (Computable.const targetWord)
  have hinequalityRE : REPred (fun word : Word n => ¬φ (FreeGroup.mk word) = 1) := by
    refine hinequalityRaw.of_eq fun word => ?_
    let normalSubgroup :=
      Subgroup.normalClosure (relatorSet (augmentedRelations word))
    have hkernelLe : MonoidHom.ker presentation ≤ normalSubgroup := by
      rw [← hbase]
      apply Subgroup.normalClosure_mono
      intro x hx
      rw [show augmentedRelations word = substitute images word :: relations by rfl,
        relatorSet_cons]
      exact Or.inr hx
    have hmemberMap :
        FreeGroup.mk targetWord ∈ normalSubgroup ↔
          presentation (FreeGroup.mk targetWord) ∈ normalSubgroup.map presentation := by
      rw [← Subgroup.mem_comap, Subgroup.comap_map_eq_self hkernelLe]
    have hmap : normalSubgroup.map presentation =
        Subgroup.normalClosure ({embedding (FreeGroup.mk word)} : Set K) := by
      dsimp [normalSubgroup, augmentedRelations]
      rw [map_normalClosure_cons_of_base_eq_ker presentation hpresentation relations hbase,
        hsubstitute]
    rw [show Subgroup.normalClosure (relatorSet (augmentedRelations word)) = normalSubgroup by rfl,
      hmemberMap, hmap, htargetWord]
    calc
      g nonidentity ∈ Subgroup.normalClosure ({embedding (FreeGroup.mk word)} : Set K) ↔
          f (φ (FreeGroup.mk word)) ≠ 1 := by
            simpa [embedding] using hsimple (f (φ (FreeGroup.mk word)))
      _ ↔ φ (FreeGroup.mk word) ≠ 1 := by
        constructor
        · intro himage hword
          apply himage
          simp [hword]
        · intro hword himage
          apply hword
          apply hf
          simpa using himage
  exact (fun _ _ => ComputablePred.computable_iff_re_compl_re'.mpr
    ⟨hequalityRE, hinequalityRE⟩) hsurj hker

end Submission
