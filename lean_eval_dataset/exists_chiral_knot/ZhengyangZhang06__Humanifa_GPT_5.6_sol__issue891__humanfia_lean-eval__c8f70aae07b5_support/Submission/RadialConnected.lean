import Submission.ComplementLift

open scoped unitInterval

namespace Submission.RadialConnected

noncomputable section

def coreBase : RadialCore.Core := CoreCycles.aVertex 0

theorem coreBase_joined (q : RadialCore.Core) : Joined coreBase q := by
  obtain ⟨i, j, u, rfl⟩ := CoreClassification.exists_edge q
  let segment : Path (CoreCycles.aVertex i) (CoreCycles.edgePath i j u) :=
    ((CoreCycles.edgePath i j).subpath 0 u).cast (by simp) rfl
  refine ⟨(CoreCycles.edgePath 0 0).trans
    ((CoreCycles.edgePath i 0).symm.trans segment)⟩

instance corePathConnectedSpace : PathConnectedSpace RadialCore.Core where
  nonempty := ⟨coreBase⟩
  joined x y := (coreBase_joined x).symm.trans (coreBase_joined y)

def prunePath (q : RadialSpine.Spine) :
    Path q (CoreDeformation.coreInclusion (CoreDeformation.coreRetraction q)) where
  toFun s := CoreDeformation.pruneSpine s q
  continuous_toFun := by
    have hpair : Continuous (fun s : unitInterval => (s, q)) :=
      continuous_id.prodMk continuous_const
    have hcomp := CoreDeformation.pruneSpine_continuous.comp hpair
    simpa only [Function.comp_def] using hcomp
  source' := CoreDeformation.pruneSpine_zero_time q
  target' := rfl

instance spinePathConnectedSpace : PathConnectedSpace RadialSpine.Spine where
  nonempty := ⟨CoreDeformation.coreInclusion coreBase⟩
  joined x y := by
    let corePath : Path (CoreDeformation.coreRetraction x)
        (CoreDeformation.coreRetraction y) :=
      PathConnectedSpace.somePath _ _
    exact ⟨(prunePath x).trans
      ((corePath.map CoreDeformation.coreInclusion.continuous).trans
        (prunePath y).symm)⟩

def flattenPath (q : RadialMilnor.Fiber) :
    Path q (RadialSpine.spineInclusion (RadialSpine.spineRetraction q)) where
  toFun s := RadialSpine.flattenFiber (s : ℝ) q
  continuous_toFun := by
    have hpair : Continuous (fun s : unitInterval => (s, q)) :=
      continuous_id.prodMk continuous_const
    have hcomp := RadialSpine.flattenFiber_continuous.comp hpair
    simpa only [Function.comp_def] using hcomp
  source' := RadialSpine.flattenFiber_zero_time q
  target' := rfl

instance fiberPathConnectedSpace : PathConnectedSpace RadialMilnor.Fiber where
  nonempty := ⟨RadialSpine.spineInclusion
    (CoreDeformation.coreInclusion coreBase)⟩
  joined x y := by
    let spinePath : Path (RadialSpine.spineRetraction x)
        (RadialSpine.spineRetraction y) :=
      PathConnectedSpace.somePath _ _
    exact ⟨(flattenPath x).trans
      ((spinePath.map RadialSpine.spineInclusion.continuous).trans
        (flattenPath y).symm)⟩

end

end Submission.RadialConnected
