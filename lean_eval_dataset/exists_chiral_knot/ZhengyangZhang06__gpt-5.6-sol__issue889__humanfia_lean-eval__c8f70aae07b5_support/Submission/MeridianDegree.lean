import Submission.PhaseDegree

namespace Submission.MeridianDegree

noncomputable section

abbrev Complement := RadialPhase.Complement

def mapLoop (u : C(Complement, Circle)) {q : Complement}
    (gamma : Path q q) : Path (u q) (u q) :=
  gamma.map u.continuous

def startHeight (q : Complement) : ℝ :=
  Classical.choose (Circle.exp_surjective (RadialPhase.phase q))

theorem exp_startHeight (q : Complement) :
    Circle.exp (startHeight q) = RadialPhase.phase q :=
  Classical.choose_spec (Circle.exp_surjective (RadialPhase.phase q))

def startCover (q : Complement) : RadialCyclicCover.Cover :=
  ⟨(q, startHeight q), (exp_startHeight q).symm⟩

def phaseLoop {q : Complement} (gamma : Path q q) :
    Path (RadialPhase.phase q) (RadialPhase.phase q) :=
  mapLoop PhaseDegree.phaseMap gamma

def coverPath {q : Complement} (gamma : Path q q) :
    C(unitInterval, RadialCyclicCover.Cover) :=
  ⟨fun t => ⟨(gamma t,
      startHeight q + CircleWinding.liftedLoop (phaseLoop gamma) t), by
        rw [Circle.exp_add, exp_startHeight,
          CircleWinding.exp_liftedLoop]
        change RadialPhase.phase (gamma t) = RadialPhase.phase q *
          (RadialPhase.phase (gamma t) * (RadialPhase.phase q)⁻¹)
        calc
          RadialPhase.phase (gamma t) = RadialPhase.phase (gamma t) *
              (RadialPhase.phase q * (RadialPhase.phase q)⁻¹) := by simp
          _ = RadialPhase.phase q *
              (RadialPhase.phase (gamma t) * (RadialPhase.phase q)⁻¹) := by
                ac_rfl⟩, by
    apply Continuous.subtype_mk
    exact gamma.continuous.prodMk
      (continuous_const.add (CircleWinding.liftedLoop (phaseLoop gamma)).continuous)⟩

@[simp] theorem coverPath_zero {q : Complement} (gamma : Path q q) :
    coverPath gamma 0 = startCover q := by
  apply Subtype.ext
  apply Prod.ext
  · exact gamma.source
  · simp [coverPath, startCover]

theorem coverPath_one_of_phase_winding {q : Complement} (gamma : Path q q)
    (hphase : CircleWinding.windingReal (phaseLoop gamma) = 2 * Real.pi) :
    coverPath gamma 1 = RadialCyclicCover.deck (startCover q) := by
  apply Subtype.ext
  apply Prod.ext
  · exact gamma.target
  · change startHeight q + CircleWinding.windingReal (phaseLoop gamma) =
      startHeight q + 2 * Real.pi
    rw [hphase]

def relativeLift (u : C(Complement, Circle)) {q : Complement}
    (gamma : Path q q) : C(unitInterval, ℝ) :=
  ⟨fun t => ComplementLift.coverLift u (coverPath gamma t) -
      ComplementLift.coverLift u (coverPath gamma 0),
    ((ComplementLift.coverLift u).continuous.comp (coverPath gamma).continuous).sub
      continuous_const⟩

theorem exp_relativeLift (u : C(Complement, Circle)) {q : Complement}
    (gamma : Path q q) (t : unitInterval) :
    Circle.exp (relativeLift u gamma t) =
      CircleWinding.normalizeLoop (mapLoop u gamma) t := by
  change Circle.exp (ComplementLift.coverLift u (coverPath gamma t) -
      ComplementLift.coverLift u (coverPath gamma 0)) =
    u (gamma t) * (u q)⁻¹
  rw [Circle.exp_sub, ComplementLift.exp_coverLift,
    ComplementLift.exp_coverLift]
  change u (gamma t) / u (gamma 0) = u (gamma t) * (u q)⁻¹
  rw [gamma.source, div_eq_mul_inv]

@[simp] theorem relativeLift_zero (u : C(Complement, Circle)) {q : Complement}
    (gamma : Path q q) : relativeLift u gamma 0 = 0 := by
  simp [relativeLift]

theorem relativeLift_eq_liftedLoop (u : C(Complement, Circle))
    {q : Complement} (gamma : Path q q) :
    relativeLift u gamma = CircleWinding.liftedLoop (mapLoop u gamma) := by
  apply (Circle.isCoveringMap_exp.eq_liftPath_iff' (γ_0 := by simp)).mpr
  constructor
  · funext t
    exact exp_relativeLift u gamma t
  · exact relativeLift_zero u gamma

theorem winding_eq_degree_mul_two_pi (u : C(Complement, Circle))
    {q : Complement} (gamma : Path q q)
    (hphase : CircleWinding.windingReal (phaseLoop gamma) = 2 * Real.pi) :
    CircleWinding.windingReal (mapLoop u gamma) =
      DeckDegree.degree u * (2 * Real.pi) := by
  have hend := DFunLike.congr_fun (relativeLift_eq_liftedLoop u gamma) 1
  change ComplementLift.coverLift u (coverPath gamma 1) -
      ComplementLift.coverLift u (coverPath gamma 0) =
    CircleWinding.windingReal (mapLoop u gamma) at hend
  rw [coverPath_one_of_phase_winding gamma hphase,
    coverPath_zero, DeckDegree.coverLift_deck] at hend
  linarith

end

end Submission.MeridianDegree
