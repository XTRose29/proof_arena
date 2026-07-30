import Mathlib

/-!
# A four-dimensional obstruction from two quaternion groups

The central involution of a faithfully represented quaternion group acts as
`-1` in real dimension four. Consequently, two quaternion subgroups with
distinct central involutions rule out a faithful representation into
`GL(4, ℝ)`.
-/

open Matrix

namespace Submission.QuaternionObstruction

private theorem quaternionOrbit_linearIndependent
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (I J : V →ₗ[ℝ] V) (w : V) (hw : w ≠ 0)
    (hII : I (I w) = -w)
    (hJJ : J (J w) = -w)
    (hJI : J (I w) = -I (J w))
    (hIK : I (I (J w)) = -J w)
    (hJK : J (I (J w)) = I w) :
    LinearIndependent ℝ ![w, I w, J w, I (J w)] := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  rw [Fin.sum_univ_four] at hc
  change
    c 0 • w + c 1 • I w + c 2 • J w + c 3 • I (J w) = 0 at hc
  have hcI :
      c 0 • I w + c 1 • (-w) + c 2 • I (J w) +
          c 3 • (-J w) = 0 := by
    simpa only [map_add, map_smul, map_zero, hII, hIK] using congr_arg I hc
  have hcJ :
      c 0 • J w + c 1 • (-I (J w)) + c 2 • (-w) +
          c 3 • I w = 0 := by
    simpa only [map_add, map_smul, map_zero, hJI, hJJ, hJK] using congr_arg J hc
  have hKI : I (J (I w)) = J w := by
    rw [hJI, map_neg, hIK, neg_neg]
  have hKJ : I (J (J w)) = -I w := by
    rw [hJJ, map_neg]
  have hKK : I (J (I (J w))) = -w := by
    rw [hJK, hII]
  have hcK :
      c 0 • I (J w) + c 1 • J w + c 2 • (-I w) +
          c 3 • (-w) = 0 := by
    simpa only [map_add, map_smul, map_zero, LinearMap.coe_comp,
      Function.comp_apply, hKI, hKJ, hKK] using
        congr_arg (I ∘ₗ J) hc
  have hnorm :
      (c 0 ^ 2 + c 1 ^ 2 + c 2 ^ 2 + c 3 ^ 2) • w = 0 := by
    linear_combination (norm := module)
      c 0 • hc - c 1 • hcI - c 2 • hcJ - c 3 • hcK
  have hsum : c 0 ^ 2 + c 1 ^ 2 + c 2 ^ 2 + c 3 ^ 2 = 0 := by
    exact (smul_eq_zero.mp hnorm).resolve_right hw
  have hc0 : c 0 = 0 := by
    nlinarith [sq_nonneg (c 0), sq_nonneg (c 1), sq_nonneg (c 2), sq_nonneg (c 3)]
  have hc1 : c 1 = 0 := by
    nlinarith [sq_nonneg (c 0), sq_nonneg (c 1), sq_nonneg (c 2), sq_nonneg (c 3)]
  have hc2 : c 2 = 0 := by
    nlinarith [sq_nonneg (c 0), sq_nonneg (c 1), sq_nonneg (c 2), sq_nonneg (c 3)]
  have hc3 : c 3 = 0 := by
    nlinarith [sq_nonneg (c 0), sq_nonneg (c 1), sq_nonneg (c 2), sq_nonneg (c 3)]
  intro i
  fin_cases i
  · exact hc0
  · exact hc1
  · exact hc2
  · exact hc3

/-- The quaternion group of order eight. -/
abbrev Q8 := QuaternionGroup 2

private def qi : Q8 := QuaternionGroup.a 1

private def qj : Q8 := QuaternionGroup.xa 0

/-- The unique central involution in `Q8`. -/
def centralInvolution : Q8 := QuaternionGroup.a 2

private theorem qi_sq : qi * qi = centralInvolution := by
  decide

private theorem qj_sq : qj * qj = centralInvolution := by
  decide

private theorem centralInvolution_sq :
    centralInvolution * centralInvolution = 1 := by
  decide

theorem centralInvolution_ne_one : centralInvolution ≠ 1 := by
  decide

private theorem centralInvolution_commutes_qi :
    centralInvolution * qi = qi * centralInvolution := by
  decide

private theorem centralInvolution_commutes_qj :
    centralInvolution * qj = qj * centralInvolution := by
  decide

private theorem qi_mul_qj :
    qi * qj = centralInvolution * (qj * qi) := by
  decide

/--
In every faithful four-dimensional real representation of `Q8`, its central
involution acts as the scalar `-1`.
-/
theorem map_centralInvolution_eq_negOne
    (ρ : Q8 →* GL (Fin 4) ℝ) (hρ : Function.Injective ρ) :
    ρ centralInvolution =
      Matrix.GeneralLinearGroup.scalar (Fin 4) (-1 : ℝˣ) := by
  let V := Fin 4 → ℝ
  let ρ' : Q8 →* LinearMap.GeneralLinearGroup ℝ V :=
    Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp ρ
  let i : LinearMap.GeneralLinearGroup ℝ V := ρ' qi
  let j : LinearMap.GeneralLinearGroup ℝ V := ρ' qj
  let z : LinearMap.GeneralLinearGroup ℝ V := ρ' centralInvolution
  let I : V →ₗ[ℝ] V := i.val
  let J : V →ₗ[ℝ] V := j.val
  let Z : V →ₗ[ℝ] V := z.val
  have hi_sq : i * i = z := by
    change ρ' qi * ρ' qi = ρ' centralInvolution
    rw [← map_mul, qi_sq]
  have hj_sq : j * j = z := by
    change ρ' qj * ρ' qj = ρ' centralInvolution
    rw [← map_mul, qj_sq]
  have hz_sq : z * z = 1 := by
    change ρ' centralInvolution * ρ' centralInvolution = 1
    rw [← map_mul, centralInvolution_sq, map_one]
  have hz_i : z * i = i * z := by
    change
      ρ' centralInvolution * ρ' qi =
        ρ' qi * ρ' centralInvolution
    rw [← map_mul, ← map_mul, centralInvolution_commutes_qi]
  have hz_j : z * j = j * z := by
    change
      ρ' centralInvolution * ρ' qj =
        ρ' qj * ρ' centralInvolution
    rw [← map_mul, ← map_mul, centralInvolution_commutes_qj]
  have hi_j : i * j = z * (j * i) := by
    change ρ' qi * ρ' qj = ρ' centralInvolution * (ρ' qj * ρ' qi)
    rw [← map_mul, ← map_mul, ← map_mul, qi_mul_qj]
  have hII (v : V) : I (I v) = Z v := by
    simpa [I, Z] using congr_arg (fun g => g.val v) hi_sq
  have hJJ (v : V) : J (J v) = Z v := by
    simpa [J, Z] using congr_arg (fun g => g.val v) hj_sq
  have hZZ (v : V) : Z (Z v) = v := by
    simpa [Z] using congr_arg (fun g => g.val v) hz_sq
  have hZI (v : V) : Z (I v) = I (Z v) := by
    simpa [I, Z] using congr_arg (fun g => g.val v) hz_i
  have hZJ (v : V) : Z (J v) = J (Z v) := by
    simpa [J, Z] using congr_arg (fun g => g.val v) hz_j
  have hIJ (v : V) : I (J v) = Z (J (I v)) := by
    simpa [I, J, Z] using congr_arg (fun g => g.val v) hi_j
  have hz_ne_one : z ≠ 1 := by
    intro hz
    apply centralInvolution_ne_one
    apply hρ
    apply Matrix.GeneralLinearGroup.toLin.injective
    simpa [ρ', z] using hz
  have hZ_ne_id : Z ≠ LinearMap.id := by
    intro hZ
    apply hz_ne_one
    apply Units.ext
    change Z = LinearMap.id
    exact hZ
  obtain ⟨v, hv⟩ : ∃ v : V, Z v ≠ v := by
    by_contra h
    simp only [not_exists, not_not] at h
    apply hZ_ne_id
    apply LinearMap.ext
    intro u
    exact h u
  let w : V := Z v - v
  have hw : w ≠ 0 := sub_ne_zero.mpr hv
  have hZw : Z w = -w := by
    simp only [w, map_sub, hZZ]
    module
  have hanti (u : V) (hu : Z u = -u) :
      J (I u) = -I (J u) := by
    have hZJI : Z (J (I u)) = -J (I u) := by
      calc
        Z (J (I u)) = J (Z (I u)) := hZJ (I u)
        _ = J (I (Z u)) := congr_arg J (hZI u)
        _ = J (I (-u)) := by rw [hu]
        _ = -J (I u) := by simp
    have h := hIJ u
    rw [hZJI] at h
    have hn := (congr_arg Neg.neg h).symm
    rw [neg_neg] at hn
    exact hn
  have hZIw : Z (I w) = -I w := by
    rw [hZI, hZw, map_neg]
  have hZJw : Z (J w) = -J w := by
    rw [hZJ, hZw, map_neg]
  have hZKw : Z (I (J w)) = -I (J w) := by
    rw [hZI, hZJw, map_neg]
  have hIIw : I (I w) = -w := (hII w).trans hZw
  have hJJw : J (J w) = -w := (hJJ w).trans hZw
  have hJIw : J (I w) = -I (J w) := hanti w hZw
  have hIKw : I (I (J w)) = -J w := (hII (J w)).trans hZJw
  have hJKw : J (I (J w)) = I w := by
    calc
      J (I (J w)) = -I (J (J w)) := hanti (J w) hZJw
      _ = -I (-w) := by rw [hJJw]
      _ = I w := by rw [map_neg, neg_neg]
  let b : Fin 4 → V := ![w, I w, J w, I (J w)]
  have hb : LinearIndependent ℝ b := by
    exact quaternionOrbit_linearIndependent I J w hw hIIw hJJw hJIw hIKw hJKw
  have hb_span : Submodule.span ℝ (Set.range b) = ⊤ := by
    apply hb.span_eq_top_of_card_eq_finrank'
    simp [V]
  have hZ_eq : Z = -LinearMap.id := by
    apply LinearMap.ext_on_range hb_span
    intro k
    fin_cases k
    · simpa [b] using hZw
    · simpa [b] using hZIw
    · simpa [b] using hZJw
    · simpa [b] using hZKw
  apply Matrix.GeneralLinearGroup.toLin.injective
  apply Units.ext
  calc
    (Matrix.GeneralLinearGroup.toLin (ρ centralInvolution)).val = Z := rfl
    _ = -LinearMap.id := hZ_eq
    _ =
        (Matrix.GeneralLinearGroup.toLin
          (Matrix.GeneralLinearGroup.scalar (Fin 4) (-1 : ℝˣ))).val := by
      apply LinearMap.ext
      intro v
      funext k
      change
        -v k =
          ((Matrix.diagonal fun _ : Fin 4 => (-1 : ℝ)) *ᵥ v) k
      rw [Matrix.mulVec_diagonal]
      ring

end Submission.QuaternionObstruction
