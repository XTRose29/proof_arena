import ChallengeDeps
import Submission.QuaternionObstruction
import Submission.SphereComplement
import Mathlib.Analysis.Quaternion
import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# The quaternionic spherical space form

This file constructs the standard free action of the quaternion group `Q₈` on
the unit three-sphere of the real quaternions and packages its quotient as a
closed three-manifold.
-/

open LeanEval.Topology
open Metric
open scoped Quaternion

namespace Submission.QuaternionSpaceForm

abbrev SphereThree := SphereComplement.QuaternionSphere

local instance : Fact (Module.finrank ℝ ℍ = 3 + 1) :=
  ⟨by simpa using (Quaternion.finrank_eq_four (R := ℝ))⟩

local instance : ConnectedSpace SphereThree :=
  Subtype.connectedSpace <|
    isConnected_sphere
      (Module.one_lt_rank_of_one_lt_finrank (by
        rw [Quaternion.finrank_eq_four]
        norm_num))
      (0 : ℍ) (r := 1) (by norm_num)

local instance : PathConnectedSpace SphereThree :=
  isPathConnected_iff_pathConnectedSpace.mp <|
    isPathConnected_sphere
      (Module.one_lt_rank_of_one_lt_finrank (by
        rw [Quaternion.finrank_eq_four]
        norm_num))
      (0 : ℍ) (r := 1) (by norm_num)

private def intQuaternionI : ℍ[ℤ] := ⟨0, 1, 0, 0⟩

private def intQuaternionJ : ℍ[ℤ] := ⟨0, 0, 1, 0⟩

private instance : DecidableEq ℍ[ℤ] := fun q r =>
  if h :
      q.re = r.re ∧ q.imI = r.imI ∧ q.imJ = r.imJ ∧ q.imK = r.imK then
    isTrue (Quaternion.ext q r h.1 h.2.1 h.2.2.1 h.2.2.2)
  else
    isFalse fun e =>
      h ⟨congr_arg QuaternionAlgebra.re e,
        congr_arg QuaternionAlgebra.imI e,
        congr_arg QuaternionAlgebra.imJ e,
        congr_arg QuaternionAlgebra.imK e⟩

def q8IntValue : QuaternionObstruction.Q8 → ℍ[ℤ]
  | QuaternionGroup.a k =>
      ![(⟨1, 0, 0, 0⟩ : ℍ[ℤ]),
        (⟨0, 1, 0, 0⟩ : ℍ[ℤ]),
        (⟨-1, 0, 0, 0⟩ : ℍ[ℤ]),
        (⟨0, -1, 0, 0⟩ : ℍ[ℤ])] k
  | QuaternionGroup.xa k =>
      ![(⟨0, 0, 1, 0⟩ : ℍ[ℤ]),
        (⟨0, 0, 0, -1⟩ : ℍ[ℤ]),
        (⟨0, 0, -1, 0⟩ : ℍ[ℤ]),
        (⟨0, 0, 0, 1⟩ : ℍ[ℤ])] k

private theorem q8IntValue_mul :
    ∀ q r, q8IntValue (q * r) = q8IntValue q * q8IntValue r := by
  rintro (i | i) (j | j)
  all_goals
    fin_cases i <;> fin_cases j <;> decide

private def q8ToIntQuaternion :
    QuaternionObstruction.Q8 →* ℍ[ℤ] where
  toFun := q8IntValue
  map_one' := by decide
  map_mul' := q8IntValue_mul

def intQuaternionCast : ℍ[ℤ] →+* ℍ where
  toFun q := ⟨q.re, q.imI, q.imJ, q.imK⟩
  map_zero' := by ext <;> norm_num
  map_one' := by ext <;> norm_num
  map_add' q r := by ext <;> norm_num
  map_mul' q r := by
    apply Quaternion.ext <;>
      norm_num [Quaternion.re_mul, Quaternion.imI_mul,
        Quaternion.imJ_mul, Quaternion.imK_mul]

private noncomputable def q8ToRealQuaternion :
    QuaternionObstruction.Q8 →* ℍ :=
  intQuaternionCast.toMonoidHom.comp q8ToIntQuaternion

private theorem normSq_intQuaternionCast (q : ℍ[ℤ]) :
    Quaternion.normSq (intQuaternionCast q) =
      (Quaternion.normSq (R := ℤ) q : ℝ) := by
  norm_num [Quaternion.normSq_def', intQuaternionCast]

private theorem normSq_q8IntValue
    (q : QuaternionObstruction.Q8) :
    Quaternion.normSq (q8IntValue q) = 1 := by
  rcases q with k | k <;> fin_cases k <;> decide

private theorem norm_q8ToRealQuaternion
    (q : QuaternionObstruction.Q8) :
    ‖q8ToRealQuaternion q‖ = 1 := by
  rw [norm_eq_sqrt_real_inner, Quaternion.inner_self]
  change
    Real.sqrt (Quaternion.normSq (intQuaternionCast (q8IntValue q))) = 1
  rw [normSq_intQuaternionCast, normSq_q8IntValue]
  norm_num

/-- The usual inclusion of `Q₈` in the unit quaternions. -/
noncomputable def q8ToSphere : QuaternionObstruction.Q8 →* SphereThree where
  toFun q :=
    ⟨q8ToRealQuaternion q, by
      simpa [mem_sphere_zero_iff_norm] using norm_q8ToRealQuaternion q⟩
  map_one' := by
    apply Subtype.ext
    exact q8ToRealQuaternion.map_one
  map_mul' q r := by
    apply Subtype.ext
    exact q8ToRealQuaternion.map_mul q r

/-- Coordinate-level values of the eight quaternion units. -/
noncomputable def q8RealValue (q : QuaternionObstruction.Q8) : ℍ :=
  intQuaternionCast (q8IntValue q)

theorem q8ToSphere_coe (q : QuaternionObstruction.Q8) :
    (q8ToSphere q : SphereThree).1 = q8RealValue q := by
  rfl

private theorem q8IntValue_injective :
    Function.Injective q8IntValue := by
  rintro (i | i) (j | j)
  all_goals
    fin_cases i <;> fin_cases j <;> decide

private theorem intQuaternionCast_injective :
    Function.Injective intQuaternionCast := by
  intro q r h
  apply Quaternion.ext
  · have h' : (q.re : ℝ) = r.re := by
      simpa [intQuaternionCast] using congr_arg (fun z : ℍ => z.re) h
    exact_mod_cast h'
  · have h' : (q.imI : ℝ) = r.imI := by
      simpa [intQuaternionCast] using congr_arg (fun z : ℍ => z.imI) h
    exact_mod_cast h'
  · have h' : (q.imJ : ℝ) = r.imJ := by
      simpa [intQuaternionCast] using congr_arg (fun z : ℍ => z.imJ) h
    exact_mod_cast h'
  · have h' : (q.imK : ℝ) = r.imK := by
      simpa [intQuaternionCast] using congr_arg (fun z : ℍ => z.imK) h
    exact_mod_cast h'

theorem q8ToSphere_injective : Function.Injective q8ToSphere := by
  intro q r h
  apply q8IntValue_injective
  apply intQuaternionCast_injective
  simpa [q8ToSphere, q8ToRealQuaternion, q8ToIntQuaternion] using
    congr_arg Subtype.val h

noncomputable instance q8MulAction :
    MulAction QuaternionObstruction.Q8 SphereThree :=
  MulAction.compHom SphereThree q8ToSphere

instance q8ContinuousConstSMul :
    ContinuousConstSMul QuaternionObstruction.Q8 SphereThree where
  continuous_const_smul q := by
    simpa only [MulAction.compHom_smul_def] using
      (continuous_const_smul (q8ToSphere q) : Continuous fun x : SphereThree => q8ToSphere q • x)

instance q8IsCancelSMul :
    IsCancelSMul QuaternionObstruction.Q8 SphereThree := by
  rw [isCancelSMul_iff_eq_one_of_smul_eq]
  intro q x hqx
  change q8ToSphere q * x = x at hqx
  apply q8ToSphere_injective
  apply mul_right_cancel (b := x)
  simpa only [map_one, one_mul] using hqx

abbrev SpaceForm :=
  MulAction.orbitRel.Quotient QuaternionObstruction.Q8 SphereThree

/-- The image of `1 ∈ S³` in the quaternionic space form. -/
noncomputable def basepoint : SpaceForm :=
  Quotient.mk'' (1 : SphereThree)

/-- The orbit projection from the quaternionic three-sphere. -/
noncomputable def quotientMap : C(SphereThree, SpaceForm) :=
  ⟨Quotient.mk (MulAction.orbitRel QuaternionObstruction.Q8 SphereThree),
    continuous_quot_mk⟩

/-- Translating `1 ∈ S³` does not change its image in the orbit quotient. -/
theorem quotient_smul_one_eq (q : QuaternionObstruction.Q8) :
    (Quotient.mk'' (q • (1 : SphereThree)) : SpaceForm) = basepoint :=
  Quotient.sound ⟨q, rfl⟩

/-- The point of the fiber over `basepoint` indexed by a deck transformation. -/
noncomputable def fiberPoint (q : QuaternionObstruction.Q8) :
    (Quotient.mk (MulAction.orbitRel QuaternionObstruction.Q8 SphereThree)) ⁻¹'
      {basepoint} :=
  ⟨q • (1 : SphereThree), quotient_smul_one_eq q⟩

/-- Freeness makes the deck-transformation points in the basepoint fiber distinct. -/
theorem fiberPoint_injective : Function.Injective fiberPoint := by
  intro q r h
  have hsmul : q • (1 : SphereThree) = r • 1 :=
    congr_arg Subtype.val h
  have hfix : (r⁻¹ * q) • (1 : SphereThree) = 1 := by
    rw [mul_smul, hsmul, inv_smul_smul]
  exact (eq_of_inv_mul_eq_one (IsCancelSMul.eq_one_of_smul hfix)).symm

/-- The orbit projection is a covering map. -/
theorem quotient_isCoveringMap :
    IsCoveringMap
      (Quotient.mk (MulAction.orbitRel QuaternionObstruction.Q8 SphereThree)) :=
  isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul.isCoveringMap

/-- A chosen path from `1` to its translate by `q`. -/
noncomputable def pathToOrbit (q : QuaternionObstruction.Q8) :
    Path (1 : SphereThree) (q • 1) :=
  PathConnectedSpace.somePath 1 (q • 1)

/-- The projected path is a loop in the space form. -/
noncomputable def orbitLoop (q : QuaternionObstruction.Q8) :
    Path basepoint basepoint :=
  ((pathToOrbit q).map quotientMap.continuous).cast rfl
    (quotient_smul_one_eq q).symm

/-- The fundamental-group element represented by the chosen orbit loop. -/
noncomputable def orbitElement (q : QuaternionObstruction.Q8) :
    FundamentalGroup SpaceForm basepoint :=
  FundamentalGroup.fromPath (.mk (orbitLoop q))

/-- Monodromy sends the chosen orbit loop to its indexed fiber point. -/
theorem orbitElement_monodromy (q : QuaternionObstruction.Q8) :
    quotient_isCoveringMap.monodromy
        (FundamentalGroup.toPath (orbitElement q))
        ⟨1, rfl⟩ =
      fiberPoint q := by
  apply Subtype.ext
  have h := congr_arg Subtype.val <|
    quotient_isCoveringMap.monodromy_map
      (Path.Homotopic.Quotient.mk (pathToOrbit q))
  exact h

/-- Distinct quaternion deck transformations give distinct chosen loop classes. -/
theorem orbitElement_injective : Function.Injective orbitElement := by
  intro q r h
  apply fiberPoint_injective
  rw [← orbitElement_monodromy q, ← orbitElement_monodromy r, h]

/--
A point with all four quaternion coordinates nonzero.  Its `Q₈`-orbit is
disjoint from the orbit of `1`; it will be used as a puncture orbit avoided by
the coherent deck-transformation paths.
-/
noncomputable def genericPoint : SphereThree :=
  ⟨⟨(1 / 2 : ℝ), 1 / 2, 1 / 2, 1 / 2⟩, by
    rw [mem_sphere_zero_iff_norm, norm_eq_sqrt_real_inner,
      Quaternion.inner_self]
    norm_num [Quaternion.normSq_def']⟩

/-- No quaternion unit in the basepoint orbit is `genericPoint`. -/
theorem genericPoint_ne_baseOrbit (q : QuaternionObstruction.Q8) :
    genericPoint ≠ q • (1 : SphereThree) := by
  intro h
  have hre := congr_arg (fun z : SphereThree => z.1.re) h
  have hre' :
      (1 / 2 : ℝ) = ((q8IntValue q).re : ℝ) := by
    simpa [genericPoint, MulAction.compHom_smul_def, q8ToSphere,
      q8ToRealQuaternion, q8ToIntQuaternion, intQuaternionCast] using hre
  have hodd : (1 : ℤ) = 2 * (q8IntValue q).re := by
    exact_mod_cast (show (1 : ℝ) = 2 * (q8IntValue q).re by linarith)
  omega

/-- The invariant eight-point orbit used as the puncture set upstairs. -/
def genericOrbit : Set SphereThree :=
  Set.range fun q : QuaternionObstruction.Q8 => q • genericPoint

theorem genericOrbit_finite : genericOrbit.Finite :=
  Set.finite_range _

theorem genericPoint_mem_genericOrbit : genericPoint ∈ genericOrbit :=
  ⟨1, one_smul _ _⟩

theorem smul_mem_genericOrbit
    (q : QuaternionObstruction.Q8) {x : SphereThree}
    (hx : x ∈ genericOrbit) :
    q • x ∈ genericOrbit := by
  rcases hx with ⟨r, rfl⟩
  exact ⟨q * r, mul_smul q r genericPoint⟩

/-- The orbit of `1` and the chosen generic orbit are disjoint. -/
theorem baseOrbit_not_mem_genericOrbit (q : QuaternionObstruction.Q8) :
    q • (1 : SphereThree) ∉ genericOrbit := by
  rintro ⟨r, hr⟩
  apply genericPoint_ne_baseOrbit (r⁻¹ * q)
  calc
    genericPoint = r⁻¹ • (r • genericPoint) := (inv_smul_smul r genericPoint).symm
    _ = r⁻¹ • (q • (1 : SphereThree)) := congr_arg (r⁻¹ • ·) hr
    _ = (r⁻¹ * q) • (1 : SphereThree) := (mul_smul _ _ _).symm

noncomputable local instance :
    PathConnectedSpace (genericOrbitᶜ : Set SphereThree) :=
  isPathConnected_iff_pathConnectedSpace.mp <|
    SphereComplement.compl_finite_isPathConnected genericPoint genericOrbit
      genericOrbit_finite genericPoint_mem_genericOrbit

/--
A path from `1` to the deck translate indexed by `q`, chosen in the
complement of the invariant generic orbit.
-/
private noncomputable def coherentSource :
    (genericOrbitᶜ : Set SphereThree) :=
  ⟨1, by simpa using baseOrbit_not_mem_genericOrbit 1⟩

private noncomputable def coherentTarget
    (q : QuaternionObstruction.Q8) :
    (genericOrbitᶜ : Set SphereThree) :=
  ⟨q • 1, baseOrbit_not_mem_genericOrbit q⟩

noncomputable def coherentPath (q : QuaternionObstruction.Q8) :
    Path (1 : SphereThree) (q • 1) :=
  (PathConnectedSpace.somePath
      coherentSource (coherentTarget q)).map
    continuous_subtype_val

theorem coherentPath_not_mem_genericOrbit
    (q : QuaternionObstruction.Q8) (t) :
    coherentPath q t ∉ genericOrbit := by
  exact
    (PathConnectedSpace.somePath
      coherentSource (coherentTarget q) t).2

/-- Translate a sphere path by a deck transformation. -/
noncomputable def translatePath
    (q : QuaternionObstruction.Q8) {x y : SphereThree}
    (p : Path x y) :
    Path (q • x) (q • y) :=
  p.map (continuous_const_smul q)

theorem translate_coherentPath_not_mem_genericOrbit
    (q r : QuaternionObstruction.Q8) (t) :
    translatePath q (coherentPath r) t ∉ genericOrbit := by
  rintro ⟨s, hs⟩
  apply coherentPath_not_mem_genericOrbit r t
  refine ⟨q⁻¹ * s, ?_⟩
  change s • genericPoint = q • coherentPath r t at hs
  change (q⁻¹ * s) • genericPoint = coherentPath r t
  rw [mul_smul, hs]
  exact inv_smul_smul q (coherentPath r t)

/-- The lift of the product of two projected coherent loops. -/
noncomputable def productPath
    (q r : QuaternionObstruction.Q8) :
    Path (1 : SphereThree) ((q * r) • 1) :=
  (coherentPath q).trans <|
    (translatePath q (coherentPath r)).cast rfl
      (mul_smul q r (1 : SphereThree))

theorem productPath_not_mem_genericOrbit
    (q r : QuaternionObstruction.Q8) (t) :
    productPath q r t ∉ genericOrbit := by
  intro ht
  have hm : productPath q r t ∈ Set.range (productPath q r) :=
    Set.mem_range_self t
  rw [productPath, Path.trans_range] at hm
  rcases hm with ⟨u, hu⟩ | ⟨u, hu⟩
  · apply coherentPath_not_mem_genericOrbit q u
    rw [hu]
    exact ht
  · apply translate_coherentPath_not_mem_genericOrbit q r u
    simpa using hu.symm ▸ ht

/-- Coherent product lifts are homotopic to the lift chosen for the product. -/
theorem productPath_homotopic
    (q r : QuaternionObstruction.Q8) :
    (productPath q r).Homotopic (coherentPath (q * r)) := by
  apply SphereComplement.paths_homotopic_of_avoid genericPoint
  · intro t h
    exact productPath_not_mem_genericOrbit q r t
      (h ▸ genericPoint_mem_genericOrbit)
  · intro t h
    exact coherentPath_not_mem_genericOrbit (q * r) t
      (h ▸ genericPoint_mem_genericOrbit)

/-- The orbit quotient identifies every translate of a sphere point. -/
theorem quotient_smul_eq
    (q : QuaternionObstruction.Q8) (x : SphereThree) :
    (Quotient.mk'' (q • x) : SpaceForm) = Quotient.mk'' x :=
  Quotient.sound ⟨q, rfl⟩

/-- The projected coherent path, regarded as a loop at the quotient basepoint. -/
noncomputable def coherentOrbitLoop
    (q : QuaternionObstruction.Q8) :
    Path basepoint basepoint :=
  ((coherentPath q).map quotientMap.continuous).cast rfl
    (quotient_smul_one_eq q).symm

/-- The fundamental-group element associated to a deck transformation. -/
noncomputable def coherentOrbitElement
    (q : QuaternionObstruction.Q8) :
    FundamentalGroup SpaceForm basepoint :=
  FundamentalGroup.fromPath (.mk (coherentOrbitLoop q))

private theorem quotient_productPath_eq_loop_trans
    (q r : QuaternionObstruction.Q8) :
    ((productPath q r).map quotientMap.continuous).cast rfl
        (quotient_smul_one_eq (q * r)).symm =
      (coherentOrbitLoop q).trans (coherentOrbitLoop r) := by
  apply Path.ext
  funext t
  change Quotient.mk'' (productPath q r t) =
    ((coherentOrbitLoop q).trans (coherentOrbitLoop r)) t
  rw [productPath, Path.trans_apply, Path.trans_apply]
  split_ifs
  · rfl
  · exact Quotient.sound ⟨q, rfl⟩

theorem coherentOrbitLoop_mul_homotopic
    (q r : QuaternionObstruction.Q8) :
    ((coherentOrbitLoop q).trans (coherentOrbitLoop r)).Homotopic
      (coherentOrbitLoop (q * r)) := by
  have h := (productPath_homotopic q r).map quotientMap
  have h' := h.pathCast rfl (quotient_smul_one_eq (q * r)).symm
  rw [quotient_productPath_eq_loop_trans q r] at h'
  exact h'

theorem coherentOrbitElement_mul
    (q r : QuaternionObstruction.Q8) :
    coherentOrbitElement q * coherentOrbitElement r =
      coherentOrbitElement (r * q) := by
  exact Quotient.sound (coherentOrbitLoop_mul_homotopic r q)

theorem coherentOrbitElement_one :
    coherentOrbitElement 1 = 1 := by
  apply mul_left_cancel (a := coherentOrbitElement 1)
  simpa using coherentOrbitElement_mul 1 1

/-- The deck transformations embed homomorphically in the quotient fundamental group. -/
noncomputable def q8FundamentalGroupHom :
    QuaternionObstruction.Q8 →* FundamentalGroup SpaceForm basepoint where
  toFun q := coherentOrbitElement q⁻¹
  map_one' := by simpa using coherentOrbitElement_one
  map_mul' q r := by
    simpa only [mul_inv_rev] using
      (coherentOrbitElement_mul q⁻¹ r⁻¹).symm

/-- Monodromy evaluates the coherent element at its indexed fiber point. -/
theorem coherentOrbitElement_monodromy
    (q : QuaternionObstruction.Q8) :
    quotient_isCoveringMap.monodromy
        (FundamentalGroup.toPath (coherentOrbitElement q))
        ⟨1, rfl⟩ =
      fiberPoint q := by
  apply Subtype.ext
  have h := congr_arg Subtype.val <|
    quotient_isCoveringMap.monodromy_map
      (Path.Homotopic.Quotient.mk (coherentPath q))
  exact h

theorem q8FundamentalGroupHom_injective :
    Function.Injective q8FundamentalGroupHom := by
  intro q r h
  change coherentOrbitElement q⁻¹ = coherentOrbitElement r⁻¹ at h
  have hinv : q⁻¹ = r⁻¹ := by
    apply fiberPoint_injective
    rw [← coherentOrbitElement_monodromy q⁻¹,
      ← coherentOrbitElement_monodromy r⁻¹, h]
  exact inv_injective hinv

/-- The quaternionic spherical space form as a closed three-manifold. -/
noncomputable def closed3Manifold : Closed3Manifold where
  carrier := SpaceForm
  topology := inferInstance
  t2 := inferInstance
  secondCountable := ContinuousConstSMul.secondCountableTopology
  charted := inferInstance
  compact := inferInstance
  connected := inferInstance

end Submission.QuaternionSpaceForm
