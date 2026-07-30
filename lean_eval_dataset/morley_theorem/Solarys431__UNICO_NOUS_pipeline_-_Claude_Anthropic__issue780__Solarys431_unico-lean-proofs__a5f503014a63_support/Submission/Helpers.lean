/-
Submission helpers — full self-contained development.
Layer 1: Morley's theorem in the complex plane (equilaterality criterion,
polynomial core with exact cofactors, trigonometric bridge, ray-intersection
master lemma, arg toolkit, oriented-trisector statement with existence/
uniqueness and non-degeneracy companions). Layer 2: the bridge from the
benchmark's unoriented-angle configuration to the oriented statement (pointwise
angle as |arg|, barycentric coordinates recovering the orientation sign from
the convex-hull hypothesis). AI-generated (Claude, Anthropic; exact cofactors
by sympy); every step kernel-checked.
-/
import ChallengeDeps

open LeanEval.Geometry.Morley
open scoped EuclideanGeometry

open scoped EuclideanGeometry



open Complex in
/-- **Criterio di equilateralità (Connes, passo finale)** — copia certificata dell'anello 1.
Sia `ω` una radice cubica non banale dell'unità. Se `a + ω*b + ω²*c = 0` allora
`dist a b = dist b c = dist c a`. -/
theorem morley_criterio_equilatero
    (a b c ω : ℂ) (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1)
    (h : a + ω * b + ω ^ 2 * c = 0) :
    dist a b = dist b c ∧ dist b c = dist c a := by
  have hsum : ω ^ 2 + ω + 1 = 0 := by
    have hfact : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by linear_combination hω3
    rcases mul_eq_zero.mp hfact with h1 | h2
    · exact absurd (sub_eq_zero.mp h1) hω1
    · exact h2
  have hnorm : ‖ω‖ = 1 := norm_eq_one_of_pow_eq_one hω3 (by norm_num)
  have e1 : a - b = ω ^ 2 * (b - c) := by linear_combination h - b * hsum
  have e2 : c - a = ω * (b - c) := by linear_combination -h + c * hsum
  refine ⟨?_, ?_⟩
  · rw [dist_eq_norm, dist_eq_norm, e1, norm_mul, norm_pow, hnorm]; ring
  · rw [dist_eq_norm, dist_eq_norm, e2, norm_mul, hnorm]; ring


set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **Nucleo affine di Morley.** Sotto `z²−z+1=0`, i punti di Morley `P₁,P₂,P₃`
(caratterizzati dalle equazioni lineari, con `C` terzo vertice derivato) soddisfano
`P₁ + z²·P₂ + z⁴·P₃ = 0` per ogni scelta dei vertici `A,B`. -/
theorem morley_nucleo_affine
    (A B C P1 P2 P3 p q z : ℂ)
    (hz : z ^ 2 - z + 1 = 0)
    (hd1 : 1 - p ^ 2 * q ^ 2 ≠ 0)
    (hdC : 1 - p ^ 6 * q ^ 6 ≠ 0)
    (hd2 : p ^ 2 - z ^ 2 ≠ 0)
    (hd3 : p ^ 2 * (q ^ 2 - z ^ 2) ≠ 0)
    (hP1 : (1 - p ^ 2 * q ^ 2) * (P1 - A) = p ^ 2 * (1 - q ^ 2) * (B - A))
    (hC : (1 - p ^ 6 * q ^ 6) * (C - A) = p ^ 6 * (1 - q ^ 6) * (B - A))
    (hP2 : (p ^ 2 - z ^ 2) * (P2 - B) = (p ^ 2 * q ^ 2 - z ^ 2) * (C - B))
    (hP3 : p ^ 2 * (q ^ 2 - z ^ 2) * (P3 - C) = z ^ 2 * (1 - p ^ 2) * (A - C)) :
    P1 + z ^ 2 * P2 + z ^ 4 * P3 = 0 := by
  have hD : (1 - p ^ 2 * q ^ 2) * ((1 - p ^ 6 * q ^ 6) *
      ((p ^ 2 - z ^ 2) * (p ^ 2 * (q ^ 2 - z ^ 2)))) ≠ 0 :=
    mul_ne_zero hd1 (mul_ne_zero hdC (mul_ne_zero hd2 hd3))
  apply mul_left_cancel₀ hD
  linear_combination (-p^10*q^8 + p^10*q^6*z^2 + p^8*q^8*z^2 - p^8*q^6*z^4 + p^4*q^2 - p^4*z^2 - p^2*q^2*z^2 + p^2*z^4) * hP1 + (p^10*q^10*z^2 - p^10*q^8*z^4 - p^8*q^8*z^2 + p^8*q^6*z^4 - p^4*q^4*z^2 + p^4*q^2*z^4 + p^2*q^2*z^2 - p^2*z^4) * hP2 + (p^10*q^8*z^4 - p^8*q^8*z^6 - p^8*q^6*z^4 + p^6*q^6*z^6 - p^4*q^2*z^4 + p^2*q^2*z^6 + p^2*z^4 - z^6) * hP3 + (-p^6*q^6*z^2 + p^4*q^4*z^6 + p^4*q^4*z^4 + p^4*q^4*z^2 - p^2*q^2*z^8 - p^2*q^2*z^6 - p^2*q^2*z^4 + z^8) * hC + (-A*p^12*q^8*z^4 - A*p^12*q^8*z^3 + A*p^12*q^8*z + A*p^12*q^8 + A*p^10*q^8*z^6 + A*p^10*q^8*z^5 + A*p^10*q^8*z^4 - A*p^10*q^8*z^2 - A*p^10*q^8*z - A*p^10*q^8 + A*p^10*q^6*z^4 + A*p^10*q^6*z^3 + A*p^10*q^6*z^2 - A*p^10*q^4*z^4 - A*p^10*q^4*z^3 - A*p^10*q^4*z^2 - A*p^8*q^8*z^6 - A*p^8*q^8*z^5 + A*p^8*q^8*z^3 + A*p^8*q^8*z^2 - A*p^8*q^6*z^6 - A*p^8*q^6*z^5 - A*p^8*q^6*z^4 + A*p^8*q^2*z^6 + A*p^8*q^2*z^5 + A*p^8*q^2*z^4 + A*p^6*q^6*z^6 + A*p^6*q^6*z^5 - A*p^6*q^6*z^3 - A*p^6*q^6*z^2 + A*p^6*q^2*z^4 + A*p^6*q^2*z^3 - A*p^6*q^2*z - A*p^6*q^2 - A*p^6*z^6 - A*p^6*z^5 + A*p^6*z^3 + A*p^6*z^2 + A*p^4*q^4*z^4 + A*p^4*q^4*z^3 + A*p^4*q^4*z^2 - A*p^4*q^2*z^6 - A*p^4*q^2*z^5 - A*p^4*q^2*z^4 + A*p^4*q^2*z^2 + A*p^4*q^2*z + A*p^4*q^2 - A*p^4*z^4 - A*p^4*z^3 - A*p^4*z^2 - A*p^2*q^2*z^4 - A*p^2*q^2*z^3 - A*p^2*q^2*z^2 + A*p^2*z^6 + A*p^2*z^5 + A*p^2*z^4 + B*p^12*q^10*z^2 + B*p^12*q^10*z + B*p^12*q^10 - B*p^12*q^8*z^2 - B*p^12*q^8*z - B*p^12*q^8 - B*p^10*q^10*z^4 - B*p^10*q^10*z^3 - B*p^10*q^10*z^2 + B*p^10*q^4*z^4 + B*p^10*q^4*z^3 + B*p^10*q^4*z^2 + B*p^8*q^8*z^6 + B*p^8*q^8*z^5 + B*p^8*q^8*z^4 - B*p^8*q^2*z^6 - B*p^8*q^2*z^5 - B*p^8*q^2*z^4 - B*p^6*q^6*z^6 - B*p^6*q^6*z^5 + B*p^6*q^6*z^3 + B*p^6*q^6*z^2 - B*p^6*q^4*z^2 - B*p^6*q^4*z - B*p^6*q^4 + B*p^6*q^2*z^2 + B*p^6*q^2*z + B*p^6*q^2 + B*p^6*z^6 + B*p^6*z^5 - B*p^6*z^3 - B*p^6*z^2) * hz

set_option maxHeartbeats 800000 in
/-- **Morley parametrico.** Sotto le stesse ipotesi, i tre punti di Morley formano
un triangolo equilatero: le tre distanze coincidono. Assemblaggio del nucleo affine
col criterio di equilateralità, con `ω = z²` (radice cubica non banale dell'unità). -/
theorem morley_equilatero_parametrico
    (A B C P1 P2 P3 p q z : ℂ)
    (hz : z ^ 2 - z + 1 = 0)
    (hd1 : 1 - p ^ 2 * q ^ 2 ≠ 0)
    (hdC : 1 - p ^ 6 * q ^ 6 ≠ 0)
    (hd2 : p ^ 2 - z ^ 2 ≠ 0)
    (hd3 : p ^ 2 * (q ^ 2 - z ^ 2) ≠ 0)
    (hP1 : (1 - p ^ 2 * q ^ 2) * (P1 - A) = p ^ 2 * (1 - q ^ 2) * (B - A))
    (hC : (1 - p ^ 6 * q ^ 6) * (C - A) = p ^ 6 * (1 - q ^ 6) * (B - A))
    (hP2 : (p ^ 2 - z ^ 2) * (P2 - B) = (p ^ 2 * q ^ 2 - z ^ 2) * (C - B))
    (hP3 : p ^ 2 * (q ^ 2 - z ^ 2) * (P3 - C) = z ^ 2 * (1 - p ^ 2) * (A - C)) :
    dist P1 P2 = dist P2 P3 ∧ dist P2 P3 = dist P3 P1 := by
  have hω3 : (z ^ 2) ^ 3 = 1 := by linear_combination (z ^ 4 + z ^ 3 - z - 1) * hz
  have hω1 : (z ^ 2 : ℂ) ≠ 1 := by
    intro hzz
    have h2 : z = 2 := by linear_combination hzz - hz
    rw [h2] at hzz
    norm_num at hzz
  have hnuc := morley_nucleo_affine A B C P1 P2 P3 p q z hz hd1 hdC hd2 hd3 hP1 hC hP2 hP3
  have h' : P1 + z ^ 2 * P2 + (z ^ 2) ^ 2 * P3 = 0 := by linear_combination hnuc
  exact morley_criterio_equilatero P1 P2 P3 (z ^ 2) hω3 hω1 h'

open Complex

/-- **Chiave dei denominatori.** `e^{iθ} ≠ 1` per `θ` reale non nullo con `|θ| < 2π`. -/
theorem morley_exp_ne_one (θ : ℝ) (h0 : θ ≠ 0) (hlt : |θ| < 2 * Real.pi) :
    exp ((θ : ℂ) * I) ≠ 1 := by
  intro h
  rw [Complex.exp_eq_one_iff] at h
  obtain ⟨n, hn⟩ := h
  have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
  have hn' : (↑θ : ℂ) * I = ((n : ℂ) * (2 * (Real.pi : ℂ))) * I := by
    rw [hn]; ring
  have hc : (↑θ : ℂ) = (n : ℂ) * (2 * (Real.pi : ℂ)) := mul_right_cancel₀ I_ne_zero hn'
  have hr : θ = (n : ℝ) * (2 * Real.pi) := by exact_mod_cast hc
  rw [abs_lt] at hlt
  obtain ⟨hlo, hhi⟩ := hlt
  rw [hr] at hlo hhi h0
  have hn1 : (-1 : ℝ) < (n : ℝ) := by nlinarith
  have hn2 : ((n : ℝ)) < 1 := by nlinarith
  have hnz : n = 0 := by
    have e1 : (-1 : ℤ) < n := by exact_mod_cast hn1
    have e2 : n < (1 : ℤ) := by exact_mod_cast hn2
    omega
  rw [hnz] at h0
  norm_num at h0

/-- **Ponte trigonometrico.** Per un triangolo con angoli `α` in A e `β` in B
(`α, β > 0`, `α + β < π`), i parametri `p = e^{iα/3}`, `q = e^{iβ/3}`, `z = e^{iπ/3}`
soddisfano tutte le ipotesi del nucleo affine (anello 6): `z²−z+1 = 0` e le quattro
non-annullazioni dei denominatori. -/
theorem morley_ponte_trig (α β : ℝ) (p q z : ℂ)
    (hp : p = exp ((↑(α / 3) : ℂ) * I))
    (hq : q = exp ((↑(β / 3) : ℂ) * I))
    (hzd : z = exp ((↑(Real.pi / 3) : ℂ) * I))
    (hα : 0 < α) (hβ : 0 < β) (hsum : α + β < Real.pi) :
    z ^ 2 - z + 1 = 0 ∧ 1 - p ^ 2 * q ^ 2 ≠ 0 ∧ 1 - p ^ 6 * q ^ 6 ≠ 0 ∧
    p ^ 2 - z ^ 2 ≠ 0 ∧ p ^ 2 * (q ^ 2 - z ^ 2) ≠ 0 := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hαπ : α < Real.pi := by linarith
  have hβπ : β < Real.pi := by linarith
  -- (0) z² − z + 1 = 0  (come nell'anello 2: z³ = −1, Im z ≠ 0, fattorizzazione)
  have hz1 : z ^ 2 - z + 1 = 0 := by
    have hz3 : z ^ 3 = -1 := by
      rw [hzd, ← Complex.exp_nat_mul]
      have harg : ((3 : ℕ) : ℂ) * ((↑(Real.pi / 3) : ℂ) * I) = (Real.pi : ℂ) * I := by
        push_cast; ring
      rw [harg, exp_pi_mul_I]
    have himz : z.im = Real.sin (Real.pi / 3) := by rw [hzd]; exact exp_ofReal_mul_I_im _
    have hzim : z.im ≠ 0 := by rw [himz, Real.sin_pi_div_three]; positivity
    have hzne : z + 1 ≠ 0 := by
      intro hc
      have hz' : z = -1 := by linear_combination hc
      rw [hz'] at hzim; simp at hzim
    have hfac : (z + 1) * (z ^ 2 - z + 1) = 0 := by linear_combination hz3
    rcases mul_eq_zero.mp hfac with h1 | h2
    · exact absurd h1 hzne
    · exact h2
  -- (1) 1 − p²q² ≠ 0 : p²q² = e^{iθ} con θ = 2α/3 + 2β/3 ∈ (0, 2π)
  have h1 : 1 - p ^ 2 * q ^ 2 ≠ 0 := by
    have e : p ^ 2 * q ^ 2 = exp ((↑(2 * α / 3 + 2 * β / 3) : ℂ) * I) := by
      rw [hp, hq, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
      congr 1
      push_cast; ring
    rw [e]
    refine sub_ne_zero.mpr (Ne.symm (morley_exp_ne_one _ (by positivity) ?_))
    rw [abs_of_pos (by positivity)]
    linarith
  -- (2) 1 − p⁶q⁶ ≠ 0 : p⁶q⁶ = e^{iθ} con θ = 2α + 2β ∈ (0, 2π)
  have h6 : 1 - p ^ 6 * q ^ 6 ≠ 0 := by
    have e : p ^ 6 * q ^ 6 = exp ((↑(2 * α + 2 * β) : ℂ) * I) := by
      rw [hp, hq, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
      congr 1
      push_cast; ring
    rw [e]
    refine sub_ne_zero.mpr (Ne.symm (morley_exp_ne_one _ (by positivity) ?_))
    rw [abs_of_pos (by positivity)]
    linarith
  -- (3) p² − z² ≠ 0 : altrimenti e^{iθ} = 1 con θ = 2α/3 − 2π/3 ∈ (−2π, 0)
  have ep2 : p ^ 2 = exp ((↑(2 * α / 3) : ℂ) * I) := by
    rw [hp, ← Complex.exp_nat_mul]
    congr 1
    push_cast; ring
  have ez2 : z ^ 2 = exp ((↑(2 * Real.pi / 3) : ℂ) * I) := by
    rw [hzd, ← Complex.exp_nat_mul]
    congr 1
    push_cast; ring
  have h2 : p ^ 2 - z ^ 2 ≠ 0 := by
    rw [ep2, ez2]
    intro hc
    rw [sub_eq_zero] at hc
    have hdiv : exp ((↑(2 * α / 3 - 2 * Real.pi / 3) : ℂ) * I) = 1 := by
      have hsub : (↑(2 * α / 3 - 2 * Real.pi / 3) : ℂ) * I
          = (↑(2 * α / 3) : ℂ) * I - (↑(2 * Real.pi / 3) : ℂ) * I := by
        push_cast; ring
      rw [hsub, Complex.exp_sub, hc, div_self (Complex.exp_ne_zero _)]
    have hne : 2 * α / 3 - 2 * Real.pi / 3 ≠ 0 := ne_of_lt (by linarith)
    have habs : |2 * α / 3 - 2 * Real.pi / 3| < 2 * Real.pi := by
      rw [abs_of_neg (by linarith)]
      linarith
    exact morley_exp_ne_one _ hne habs hdiv
  -- (4) p²(q² − z²) ≠ 0 : p ≠ 0 e (come sopra) con θ = 2β/3 − 2π/3
  have eq2 : q ^ 2 = exp ((↑(2 * β / 3) : ℂ) * I) := by
    rw [hq, ← Complex.exp_nat_mul]
    congr 1
    push_cast; ring
  have h3 : p ^ 2 * (q ^ 2 - z ^ 2) ≠ 0 := by
    refine mul_ne_zero ?_ ?_
    · rw [hp]; exact pow_ne_zero 2 (Complex.exp_ne_zero _)
    · rw [eq2, ez2]
      intro hc
      rw [sub_eq_zero] at hc
      have hdiv : exp ((↑(2 * β / 3 - 2 * Real.pi / 3) : ℂ) * I) = 1 := by
        have hsub : (↑(2 * β / 3 - 2 * Real.pi / 3) : ℂ) * I
            = (↑(2 * β / 3) : ℂ) * I - (↑(2 * Real.pi / 3) : ℂ) * I := by
          push_cast; ring
        rw [hsub, Complex.exp_sub, hc, div_self (Complex.exp_ne_zero _)]
      have hne : 2 * β / 3 - 2 * Real.pi / 3 ≠ 0 := ne_of_lt (by linarith)
      have habs : |2 * β / 3 - 2 * Real.pi / 3| < 2 * Real.pi := by
        rw [abs_of_neg (by linarith)]
        linarith
      exact morley_exp_ne_one _ hne habs hdiv
  exact ⟨hz1, h1, h6, h2, h3⟩

/-- **Le formule chiuse soddisfano le caratterizzazioni.** Il punto `P = X + (n/d)·(Y−X)`
con `d ≠ 0` soddisfa l'equazione lineare `d·(P−X) = n·(Y−X)` dell'anello 6. -/
theorem morley_formula_soddisfa (X Y P n d : ℂ) (hd : d ≠ 0)
    (hP : P = X + n / d * (Y - X)) :
    d * (P - X) = n * (Y - X) := by
  rw [hP]
  field_simp
  ring

/-- **Teorema di Morley, forma «dagli angoli».** Per un triangolo di vertici `A`, `B`
e angoli `α` in A, `β` in B (`0 < α`, `0 < β`, `α + β < π`), con il terzo vertice `C`
dato dalla legge dei seni e i punti `P₁, P₂, P₃` d'incontro dei trisettori adiacenti
(formule chiuse nei parametri `p = e^{iα/3}`, `q = e^{iβ/3}`, `z = e^{iπ/3}`),
il triangolo `P₁P₂P₃` è equilatero. -/
theorem morley_equilatero_da_angoli
    (α β : ℝ) (A B : ℂ)
    (hα : 0 < α) (hβ : 0 < β) (hsum : α + β < Real.pi)
    (p q z P1 C P2 P3 : ℂ)
    (hp : p = exp ((↑(α / 3) : ℂ) * I))
    (hq : q = exp ((↑(β / 3) : ℂ) * I))
    (hzd : z = exp ((↑(Real.pi / 3) : ℂ) * I))
    (hP1 : P1 = A + p ^ 2 * (1 - q ^ 2) / (1 - p ^ 2 * q ^ 2) * (B - A))
    (hC : C = A + p ^ 6 * (1 - q ^ 6) / (1 - p ^ 6 * q ^ 6) * (B - A))
    (hP2 : P2 = B + (p ^ 2 * q ^ 2 - z ^ 2) / (p ^ 2 - z ^ 2) * (C - B))
    (hP3 : P3 = C + z ^ 2 * (1 - p ^ 2) / (p ^ 2 * (q ^ 2 - z ^ 2)) * (A - C)) :
    dist P1 P2 = dist P2 P3 ∧ dist P2 P3 = dist P3 P1 := by
  obtain ⟨hz1, h1, h6, h2, h3⟩ := morley_ponte_trig α β p q z hp hq hzd hα hβ hsum
  exact morley_equilatero_parametrico A B C P1 P2 P3 p q z hz1 h1 h6 h2 h3
    (morley_formula_soddisfa A B P1 _ _ h1 hP1)
    (morley_formula_soddisfa A B C _ _ h6 hC)
    (morley_formula_soddisfa B C P2 _ _ h2 hP2)
    (morley_formula_soddisfa C A P3 _ _ h3 hP3)

/-- La semiretta aperta uscente da `X` con direzione `d`. -/
def raggio (X d : ℂ) : Set ℂ := {w | ∃ t : ℝ, 0 < t ∧ w = X + (t : ℂ) * d}

/-- Il seno reale, visto in ℂ, come espressione razionale in `p = exp(x·I)`
(copia certificata dell'anello 3). -/
theorem morley_sin_razionale (x : ℝ) :
    (Real.sin x : ℂ) = ((exp ((x : ℂ) * I))⁻¹ - exp ((x : ℂ) * I)) * I / 2 := by
  have h2 : 2 * Complex.sin ((x : ℂ)) = (exp (-(x : ℂ) * I) - exp ((x : ℂ) * I)) * I :=
    Complex.two_sin _
  have hneg : exp (-(x : ℂ) * I) = (exp ((x : ℂ) * I))⁻¹ := by
    rw [neg_mul, Complex.exp_neg]
  rw [Complex.ofReal_sin]
  rw [hneg] at h2
  linear_combination h2 / 2

/-- **Identità dei tre seni** in ℂ: `sinφ·e^{iθ} + sinθ·e^{−iφ} = sin(θ+φ)`.
Dimostrata interamente nel mondo `exp` (niente formule di addizione). -/
theorem morley_sin_mix (θ φ : ℝ) :
    (Real.sin φ : ℂ) * exp ((θ : ℂ) * I) + (Real.sin θ : ℂ) * exp ((↑(-φ) : ℂ) * I)
      = (Real.sin (θ + φ) : ℂ) := by
  have e1 : exp ((↑(θ + φ) : ℂ) * I) = exp ((θ : ℂ) * I) * exp ((φ : ℂ) * I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast; ring
  have e2 : exp ((↑(-φ) : ℂ) * I) = (exp ((φ : ℂ) * I))⁻¹ := by
    rw [← Complex.exp_neg]
    congr 1
    push_cast; ring
  rw [morley_sin_razionale φ, morley_sin_razionale θ, morley_sin_razionale (θ + φ), e1, e2]
  have h1 := Complex.exp_ne_zero ((θ : ℂ) * I)
  have h2 := Complex.exp_ne_zero ((φ : ℂ) * I)
  field_simp
  ring

/-- **Lemma master (intersezione di semirette).** Siano `X ≠ Y`, `0 < θ`, `0 < φ`,
`θ + φ < π`. Un punto `w` appartiene a entrambe le semirette — da `X` con direzione
`e^{iθ}·(Y−X)` e da `Y` con direzione `e^{−iφ}·(X−Y)` — se e solo se `w` è il punto
della formula chiusa `X + (sin φ / sin(θ+φ))·e^{iθ}·(Y−X)`. Esistenza, unicità e
formula in un colpo solo. -/
theorem raggio_raggio_unico (X Y w : ℂ) (θ φ : ℝ)
    (hXY : X ≠ Y) (hθ : 0 < θ) (hφ : 0 < φ) (hsum : θ + φ < Real.pi) :
    (w ∈ raggio X (exp ((θ : ℂ) * I) * (Y - X)) ∧
     w ∈ raggio Y (exp ((↑(-φ) : ℂ) * I) * (X - Y)))
    ↔ w = X + (↑(Real.sin φ / Real.sin (θ + φ)) : ℂ) * (exp ((θ : ℂ) * I) * (Y - X)) := by
  have hYX : Y - X ≠ 0 := sub_ne_zero.mpr (Ne.symm hXY)
  have hsθ : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ (by linarith)
  have hsφ : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi hφ (by linarith)
  have hD : 0 < Real.sin (θ + φ) :=
    Real.sin_pos_of_pos_of_lt_pi (add_pos hθ hφ) hsum
  have hD' : (Real.sin (θ + φ) : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  -- l'identità scalare chiave, già divisa per sin(θ+φ)
  have hE' : (↑(Real.sin φ / Real.sin (θ + φ)) : ℂ) * exp ((θ : ℂ) * I)
      + (↑(Real.sin θ / Real.sin (θ + φ)) : ℂ) * exp ((↑(-φ) : ℂ) * I) = 1 := by
    have expand : (↑(Real.sin φ / Real.sin (θ + φ)) : ℂ) * exp ((θ : ℂ) * I)
        + (↑(Real.sin θ / Real.sin (θ + φ)) : ℂ) * exp ((↑(-φ) : ℂ) * I)
        = ((Real.sin φ : ℂ) * exp ((θ : ℂ) * I)
            + (Real.sin θ : ℂ) * exp ((↑(-φ) : ℂ) * I)) / (Real.sin (θ + φ) : ℂ) := by
      rw [Complex.ofReal_div, Complex.ofReal_div]
      ring
    rw [expand, morley_sin_mix, div_self hD']
  constructor
  · rintro ⟨⟨t, ht, hw1⟩, ⟨s, hs, hw2⟩⟩
    -- riduzione all'equazione scalare t·e^{iθ} + s·e^{−iφ} = 1
    have h0 : ((t : ℂ) * exp ((θ : ℂ) * I) + (s : ℂ) * exp ((↑(-φ) : ℂ) * I)) * (Y - X)
        = 1 * (Y - X) := by linear_combination hw2 - hw1
    have hE : (t : ℂ) * exp ((θ : ℂ) * I) + (s : ℂ) * exp ((↑(-φ) : ℂ) * I) = 1 :=
      mul_right_cancel₀ hYX h0
    -- sistema 2×2 reale: parti reale e immaginaria
    have hEre := congrArg Complex.re hE
    have hEim := congrArg Complex.im hE
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, exp_ofReal_mul_I_re, exp_ofReal_mul_I_im,
      Complex.one_re, Complex.one_im, Real.cos_neg, Real.sin_neg,
      zero_mul, sub_zero, add_zero, mul_zero, mul_neg, zero_add] at hEre hEim
    -- il determinante: t·sin(θ+φ) = sin φ
    have key : t * Real.sin (θ + φ) = Real.sin φ := by
      rw [Real.sin_add]
      linear_combination Real.cos φ * hEim + Real.sin φ * hEre
    have ht' : t = Real.sin φ / Real.sin (θ + φ) := by
      rw [eq_div_iff hD.ne']; exact key
    rw [hw1, ht']
  · intro hw
    constructor
    · exact ⟨Real.sin φ / Real.sin (θ + φ), div_pos hsφ hD, hw⟩
    · refine ⟨Real.sin θ / Real.sin (θ + φ), div_pos hsθ hD, ?_⟩
      rw [hw]
      linear_combination (Y - X) * hE'

/-- **Raccordo trigonometria → algebra.** Il coefficiente del lemma master, nel mondo
`exp`, è esattamente il coefficiente razionale del nucleo: con `a = e^{iθ}`, `b = e^{iφ}`,
`(sin φ / sin(θ+φ))·e^{iθ} = a²(1−b²)/(1−a²b²)`. È il ponte fra l'intersezione delle
semirette e le formule chiuse dei punti di Morley. -/
theorem morley_raccordo (θ φ : ℝ)
    (hD : Real.sin (θ + φ) ≠ 0)
    (hab : 1 - exp ((θ : ℂ) * I) ^ 2 * exp ((φ : ℂ) * I) ^ 2 ≠ 0) :
    (↑(Real.sin φ / Real.sin (θ + φ)) : ℂ) * exp ((θ : ℂ) * I)
      = exp ((θ : ℂ) * I) ^ 2 * (1 - exp ((φ : ℂ) * I) ^ 2)
        / (1 - exp ((θ : ℂ) * I) ^ 2 * exp ((φ : ℂ) * I) ^ 2) := by
  have hD' : (Real.sin (θ + φ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hD
  have ha := Complex.exp_ne_zero ((θ : ℂ) * I)
  have hb := Complex.exp_ne_zero ((φ : ℂ) * I)
  have e1 : exp ((↑(θ + φ) : ℂ) * I) = exp ((θ : ℂ) * I) * exp ((φ : ℂ) * I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast; ring
  rw [Complex.ofReal_div, morley_sin_razionale φ, morley_sin_razionale (θ + φ), e1]
  field_simp

/-- (i-a) `0 < arg z` se `0 < im z`. -/
theorem morley_arg_pos {z : ℂ} (hz : 0 < z.im) : 0 < z.arg := by
  rcases lt_or_eq_of_le (Complex.arg_nonneg_iff.mpr hz.le) with h | h
  · exact h
  · exfalso
    exact absurd (Complex.arg_eq_zero_iff.mp h.symm).2 hz.ne'

/-- (i-b) `arg z < π` se `0 < im z`. -/
theorem morley_arg_lt_pi {z : ℂ} (hz : 0 < z.im) : z.arg < Real.pi := by
  rcases lt_or_eq_of_le (Complex.arg_le_pi z) with h | h
  · exact h
  · exfalso
    exact absurd (Complex.arg_eq_pi_iff.mp h).2 hz.ne'

/-- (iv) `arg z⁻¹ = −arg z` se `0 < im z` (il ramo `arg = π` è escluso). -/
theorem morley_arg_inv {z : ℂ} (hz : 0 < z.im) : z⁻¹.arg = -z.arg := by
  rw [Complex.arg_inv]
  rw [if_neg]
  intro h
  exact absurd (Complex.arg_eq_pi_iff.mp h).2 hz.ne'

/-- Il prodotto `im(w/v)·normSq v` è il determinante reale (area orientata). -/
theorem morley_im_div_mul_normSq (w v : ℂ) (hv : v ≠ 0) :
    (w / v).im * Complex.normSq v = v.re * w.im - v.im * w.re := by
  have h : Complex.normSq v ≠ 0 := (Complex.normSq_pos.mpr hv).ne'
  rw [div_eq_mul_inv, Complex.mul_im, Complex.inv_re, Complex.inv_im]
  field_simp
  ring

/-- (ii) **Orientazione ciclica**: l'orientazione positiva su un vertice si propaga
al vertice successivo (i tre determinanti ciclici sono la stessa area orientata). -/
theorem morley_orientazione_ciclica (A B C : ℂ) (hBA : B - A ≠ 0) (hCB : C - B ≠ 0)
    (h : 0 < ((C - A) / (B - A)).im) : 0 < ((A - B) / (C - B)).im := by
  have hs1 : 0 < Complex.normSq (B - A) := Complex.normSq_pos.mpr hBA
  have hs2 : 0 < Complex.normSq (C - B) := Complex.normSq_pos.mpr hCB
  have e1 := morley_im_div_mul_normSq (C - A) (B - A) hBA
  have e2 := morley_im_div_mul_normSq (A - B) (C - B) hCB
  -- i due determinanti coincidono (pura identità su re/im)
  have echain : (B - A).re * (C - A).im - (B - A).im * (C - A).re
      = (C - B).re * (A - B).im - (C - B).im * (A - B).re := by
    simp only [Complex.sub_re, Complex.sub_im]
    ring
  have hpos : 0 < ((A - B) / (C - B)).im * Complex.normSq (C - B) := by
    rw [e2, ← echain, ← e1]
    exact mul_pos h hs1
  by_contra hneg
  push_neg at hneg
  nlinarith

/-- (iii) **Somma degli angoli**: se il triangolo è orientato positivamente,
`arg((C−A)/(B−A)) + arg((A−B)/(C−B)) + arg((B−C)/(A−C)) = π`. -/
theorem morley_somma_angoli (A B C : ℂ) (hBA : B - A ≠ 0) (hCB : C - B ≠ 0)
    (hAC : A - C ≠ 0) (h1 : 0 < ((C - A) / (B - A)).im) :
    ((C - A) / (B - A)).arg + ((A - B) / (C - B)).arg + ((B - C) / (A - C)).arg
      = Real.pi := by
  have h2 : 0 < ((A - B) / (C - B)).im := morley_orientazione_ciclica A B C hBA hCB h1
  have h3 : 0 < ((B - C) / (A - C)).im := morley_orientazione_ciclica B C A hCB hAC h2
  set z₁ := (C - A) / (B - A) with hz₁
  set z₂ := (A - B) / (C - B) with hz₂
  set z₃ := (B - C) / (A - C) with hz₃
  have hz1ne : z₁ ≠ 0 := by
    intro hc
    rw [hc] at h1
    simp at h1
  have hz2ne : z₂ ≠ 0 := by
    intro hc
    rw [hc] at h2
    simp at h2
  have hz3ne : z₃ ≠ 0 := by
    intro hc
    rw [hc] at h3
    simp at h3
  -- il prodotto dei tre rapporti ciclici è −1
  have hprod : z₁ * z₂ * z₃ = -1 := by
    rw [hz₁, hz₂, hz₃]
    field_simp
    ring
  -- in Real.Angle la somma è π
  have hang : ((z₁.arg + z₂.arg + z₃.arg : ℝ) : Real.Angle) = ((Real.pi : ℝ) : Real.Angle) := by
    rw [Real.Angle.coe_add, Real.Angle.coe_add,
        ← Complex.arg_mul_coe_angle hz1ne hz2ne,
        ← Complex.arg_mul_coe_angle (mul_ne_zero hz1ne hz2ne) hz3ne,
        hprod, Complex.arg_neg_one]
  -- ciascun angolo in (0,π) ⟹ la somma reale è esattamente π
  rw [Real.Angle.angle_eq_iff_two_pi_dvd_sub] at hang
  obtain ⟨k, hk⟩ := hang
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have b1 : 0 < z₁.arg := morley_arg_pos h1
  have b2 : 0 < z₂.arg := morley_arg_pos h2
  have b3 : 0 < z₃.arg := morley_arg_pos h3
  have u1 : z₁.arg < Real.pi := morley_arg_lt_pi h1
  have u2 : z₂.arg < Real.pi := morley_arg_lt_pi h2
  have u3 : z₃.arg < Real.pi := morley_arg_lt_pi h3
  have hk1 : (k : ℝ) < 1 := by nlinarith
  have hk2 : (-1 : ℝ) < (k : ℝ) := by nlinarith
  have hk0 : k = 0 := by
    have e1' : k < (1 : ℤ) := by exact_mod_cast hk1
    have e2' : (-1 : ℤ) < k := by exact_mod_cast hk2
    omega
  rw [hk0] at hk
  push_cast at hk
  linarith

/-- (v) **Il vertice giace sul raggio**: `C` appartiene alla semiretta da `X` con
direzione `e^{i·arg((C−X)/(Y−X))}·(Y−X)`. -/
theorem morley_mem_raggio (X Y C : ℂ) (hYX : Y - X ≠ 0) (hCX : C - X ≠ 0) :
    C ∈ raggio X (exp ((↑(((C - X) / (Y - X)).arg) : ℂ) * I) * (Y - X)) := by
  have hzne : (C - X) / (Y - X) ≠ 0 := div_ne_zero hCX hYX
  refine ⟨‖(C - X) / (Y - X)‖, norm_pos_iff.mpr hzne, ?_⟩
  have hna := Complex.norm_mul_exp_arg_mul_I ((C - X) / (Y - X))
  have hz : (C - X) / (Y - X) * (Y - X) = C - X := div_mul_cancel₀ _ hYX
  linear_combination (-(Y - X)) * hna - hz

/-- (ii) Il prodotto dei terzi degli angoli di un triangolo è la rotazione di 60°:
se `a + b + c = π` allora `e^{i·a/3}·e^{i·b/3}·e^{i·c/3} = e^{i·π/3}`. -/
theorem morley_prodotto_terzi (a b c : ℝ) (h : a + b + c = Real.pi) :
    exp ((↑(a / 3) : ℂ) * I) * exp ((↑(b / 3) : ℂ) * I) * exp ((↑(c / 3) : ℂ) * I)
      = exp ((↑(Real.pi / 3) : ℂ) * I) := by
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  have hc : (a : ℂ) + (b : ℂ) + (c : ℂ) = (Real.pi : ℂ) := by exact_mod_cast h
  push_cast
  linear_combination (I / 3) * hc

/-- Trisettore dell'angolo interno in `X` del triangolo `X Y Z`, adiacente al lato
`XY`: la semiretta da `X` che ruota la direzione `Y − X` di un terzo dell'angolo
orientato da `XY` a `XZ` (il segno di `arg` codifica l'orientazione). -/
def trisettore (X Y Z : ℂ) : Set ℂ :=
  raggio X (exp ((↑(((Z - X) / (Y - X)).arg / 3) : ℂ) * I) * (Y - X))

/-- **Identificazione dei punti di Morley.** In un triangolo orientato positivamente,
ogni punto che giace sull'intersezione dei trisettori adiacenti a un lato è dato
dalla formula chiusa del nucleo (in `p = e^{iα/3}, q = e^{iβ/3}, z = e^{iπ/3}`),
e il vertice `C` soddisfa la legge dei seni. Con `α, β` gli angoli in `A` e `B`. -/
theorem morley_identifica (A B C P₁ P₂ P₃ : ℂ) (α β γ : ℝ)
    (hα : α = ((C - A) / (B - A)).arg) (hβ : β = ((A - B) / (C - B)).arg)
    (hγ : γ = ((B - C) / (A - C)).arg)
    (horient : 0 < ((C - A) / (B - A)).im)
    (h₁ : P₁ ∈ trisettore A B C ∩ trisettore B A C)
    (h₂ : P₂ ∈ trisettore B C A ∩ trisettore C B A)
    (h₃ : P₃ ∈ trisettore C A B ∩ trisettore A C B) :
    0 < α ∧ 0 < β ∧ α + β < Real.pi ∧
    P₁ = A + exp ((↑(α / 3) : ℂ) * I) ^ 2 * (1 - exp ((↑(β / 3) : ℂ) * I) ^ 2) / (1 - exp ((↑(α / 3) : ℂ) * I) ^ 2 * exp ((↑(β / 3) : ℂ) * I) ^ 2) * (B - A) ∧
    C = A + exp ((↑(α / 3) : ℂ) * I) ^ 6 * (1 - exp ((↑(β / 3) : ℂ) * I) ^ 6) / (1 - exp ((↑(α / 3) : ℂ) * I) ^ 6 * exp ((↑(β / 3) : ℂ) * I) ^ 6) * (B - A) ∧
    P₂ = B + (exp ((↑(α / 3) : ℂ) * I) ^ 2 * exp ((↑(β / 3) : ℂ) * I) ^ 2 - exp ((↑(Real.pi / 3) : ℂ) * I) ^ 2) / (exp ((↑(α / 3) : ℂ) * I) ^ 2 - exp ((↑(Real.pi / 3) : ℂ) * I) ^ 2) * (C - B) ∧
    P₃ = C + exp ((↑(Real.pi / 3) : ℂ) * I) ^ 2 * (1 - exp ((↑(α / 3) : ℂ) * I) ^ 2) / (exp ((↑(α / 3) : ℂ) * I) ^ 2 * (exp ((↑(β / 3) : ℂ) * I) ^ 2 - exp ((↑(Real.pi / 3) : ℂ) * I) ^ 2)) * (A - C) := by
  -- non-degenerazioni dal solo orientamento
  have hBA : B - A ≠ 0 := by
    intro hc
    rw [hc, div_zero] at horient
    simp at horient
  have hCA : C - A ≠ 0 := by
    intro hc
    rw [hc, zero_div] at horient
    simp at horient
  have hCB : C - B ≠ 0 := by
    intro hc
    have hCBe : C = B := by linear_combination hc
    rw [hCBe] at horient
    rw [div_self hBA] at horient
    simp at horient
  have hAC : A - C ≠ 0 := by
    intro hc
    apply hCA
    linear_combination -hc
  have hABn : A - B ≠ 0 := by
    intro hc
    apply hBA
    linear_combination -hc
  have hAB : A ≠ B := fun hc => hABn (by rw [hc]; ring)
  have hBC : B ≠ C := fun hc => hCB (by rw [hc]; ring)
  have hCAne : C ≠ A := fun hc => hAC (by rw [hc]; ring)
  -- orientazione ciclica e angoli in (0,π)
  have h2im : 0 < ((A - B) / (C - B)).im := morley_orientazione_ciclica A B C hBA hCB horient
  have h3im : 0 < ((B - C) / (A - C)).im := morley_orientazione_ciclica B C A hCB hAC h2im
  have hα0 : 0 < α := by rw [hα]; exact morley_arg_pos horient
  have hβ0 : 0 < β := by rw [hβ]; exact morley_arg_pos h2im
  have hγ0 : 0 < γ := by rw [hγ]; exact morley_arg_pos h3im
  have hsum : α + β + γ = Real.pi := by
    rw [hα, hβ, hγ]
    exact morley_somma_angoli A B C hBA hCB hAC horient
  have hαβπ : α + β < Real.pi := by linarith
  have hβγπ : β + γ < Real.pi := by linarith
  have hγαπ : γ + α < Real.pi := by linarith
  -- il ponte trigonometrico sui tre parametri (denominatori non nulli)
  obtain ⟨hzz, hd_pq, hd_p6q6, hd_pz, hd_pqz⟩ :=
    morley_ponte_trig α β (exp ((↑(α / 3) : ℂ) * I)) (exp ((↑(β / 3) : ℂ) * I)) (exp ((↑(Real.pi / 3) : ℂ) * I)) rfl rfl rfl hα0 hβ0 hαβπ
  obtain ⟨_, hd_qr, _, _, _⟩ :=
    morley_ponte_trig β γ (exp ((↑(β / 3) : ℂ) * I)) (exp ((↑(γ / 3) : ℂ) * I)) (exp ((↑(Real.pi / 3) : ℂ) * I)) rfl rfl rfl hβ0 hγ0 hβγπ
  obtain ⟨_, hd_rp, _, _, _⟩ :=
    morley_ponte_trig γ α (exp ((↑(γ / 3) : ℂ) * I)) (exp ((↑(α / 3) : ℂ) * I)) (exp ((↑(Real.pi / 3) : ℂ) * I)) rfl rfl rfl hγ0 hα0 hγαπ
  -- membership → forma del lemma master
  obtain ⟨h11, h12⟩ := h₁
  obtain ⟨h21, h22⟩ := h₂
  obtain ⟨h31, h32⟩ := h₃
  simp only [trisettore] at h11 h12 h21 h22 h31 h32
  rw [← hα] at h11
  rw [← hβ] at h21
  rw [← hγ] at h31
  have hargB : ((C - B) / (A - B)).arg = -β := by
    rw [← inv_div, morley_arg_inv h2im, ← hβ]
  have hargC : ((A - C) / (B - C)).arg = -γ := by
    rw [← inv_div, morley_arg_inv h3im, ← hγ]
  have hargA : ((B - A) / (C - A)).arg = -α := by
    rw [← inv_div, morley_arg_inv horient, ← hα]
  rw [hargB, neg_div] at h12
  rw [hargC, neg_div] at h22
  rw [hargA, neg_div] at h32
  -- P₁: master + raccordo sul lato AB
  have hP1t := (raggio_raggio_unico A B P₁ (α / 3) (β / 3) hAB (by linarith) (by linarith)
    (by linarith)).mp ⟨h11, h12⟩
  have hD1 : Real.sin (α / 3 + β / 3) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)).ne'
  have hrac1 := morley_raccordo (α / 3) (β / 3) hD1 hd_pq
  have hP1f : P₁ = A + exp ((↑(α / 3) : ℂ) * I) ^ 2 * (1 - exp ((↑(β / 3) : ℂ) * I) ^ 2) / (1 - exp ((↑(α / 3) : ℂ) * I) ^ 2 * exp ((↑(β / 3) : ℂ) * I) ^ 2) * (B - A) := by
    rw [hP1t, ← mul_assoc, hrac1]
  -- C: il vertice sta sui raggi con gli angoli interi → master + raccordo
  have hC1 := morley_mem_raggio A B C hBA hCA
  rw [← hα] at hC1
  have hC2 := morley_mem_raggio B A C hABn hCB
  rw [hargB] at hC2
  have hCt := (raggio_raggio_unico A B C α β hAB hα0 hβ0 hαβπ).mp ⟨hC1, hC2⟩
  have hDC : Real.sin (α + β) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (by linarith) hαβπ).ne'
  have habC : 1 - exp ((↑α : ℂ) * I) ^ 2 * exp ((↑β : ℂ) * I) ^ 2 ≠ 0 := by
    have eab : exp ((↑α : ℂ) * I) ^ 2 * exp ((↑β : ℂ) * I) ^ 2
        = exp ((↑(2 * α + 2 * β) : ℂ) * I) := by
      rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
      congr 1
      push_cast; ring
    rw [eab]
    refine sub_ne_zero.mpr (Ne.symm (morley_exp_ne_one _ (by positivity) ?_))
    rw [abs_of_pos (by positivity)]
    linarith
  have hracC := morley_raccordo α β hDC habC
  have hCf : C = A + exp ((↑α : ℂ) * I) ^ 2 * (1 - exp ((↑β : ℂ) * I) ^ 2)
      / (1 - exp ((↑α : ℂ) * I) ^ 2 * exp ((↑β : ℂ) * I) ^ 2) * (B - A) := by
    rw [hCt, ← mul_assoc, hracC]
  have hap2 : exp ((↑α : ℂ) * I) ^ 2 = exp ((↑(α / 3) : ℂ) * I) ^ 6 := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
    congr 1
    push_cast; ring
  have hbq2 : exp ((↑β : ℂ) * I) ^ 2 = exp ((↑(β / 3) : ℂ) * I) ^ 6 := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
    congr 1
    push_cast; ring
  rw [hap2, hbq2] at hCf
  -- P₂: master + raccordo sul lato BC, poi eliminazione di r via p·q·r = z
  have hP2t := (raggio_raggio_unico B C P₂ (β / 3) (γ / 3) hBC (by linarith) (by linarith)
    (by linarith)).mp ⟨h21, h22⟩
  have hD2 : Real.sin (β / 3 + γ / 3) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)).ne'
  have hrac2 := morley_raccordo (β / 3) (γ / 3) hD2 hd_qr
  have hP2f : P₂ = B + exp ((↑(β / 3) : ℂ) * I) ^ 2 * (1 - exp ((↑(γ / 3) : ℂ) * I) ^ 2) / (1 - exp ((↑(β / 3) : ℂ) * I) ^ 2 * exp ((↑(γ / 3) : ℂ) * I) ^ 2) * (C - B) := by
    rw [hP2t, ← mul_assoc, hrac2]
  have hpqr : exp ((↑(α / 3) : ℂ) * I) * exp ((↑(β / 3) : ℂ) * I) * exp ((↑(γ / 3) : ℂ) * I) = exp ((↑(Real.pi / 3) : ℂ) * I) := morley_prodotto_terzi α β γ hsum
  have hz2 : exp ((↑(Real.pi / 3) : ℂ) * I) ^ 2 = exp ((↑(α / 3) : ℂ) * I) ^ 2 * exp ((↑(β / 3) : ℂ) * I) ^ 2 * exp ((↑(γ / 3) : ℂ) * I) ^ 2 := by
    rw [← hpqr]; ring
  have hkey2 : exp ((↑(β / 3) : ℂ) * I) ^ 2 * (1 - exp ((↑(γ / 3) : ℂ) * I) ^ 2) / (1 - exp ((↑(β / 3) : ℂ) * I) ^ 2 * exp ((↑(γ / 3) : ℂ) * I) ^ 2)
      = (exp ((↑(α / 3) : ℂ) * I) ^ 2 * exp ((↑(β / 3) : ℂ) * I) ^ 2 - exp ((↑(Real.pi / 3) : ℂ) * I) ^ 2) / (exp ((↑(α / 3) : ℂ) * I) ^ 2 - exp ((↑(Real.pi / 3) : ℂ) * I) ^ 2) := by
    rw [hz2]
    have hd2' : exp ((↑(α / 3) : ℂ) * I) ^ 2 - exp ((↑(α / 3) : ℂ) * I) ^ 2 * exp ((↑(β / 3) : ℂ) * I) ^ 2 * exp ((↑(γ / 3) : ℂ) * I) ^ 2 ≠ 0 := by
      have e : exp ((↑(α / 3) : ℂ) * I) ^ 2 - exp ((↑(α / 3) : ℂ) * I) ^ 2 * exp ((↑(β / 3) : ℂ) * I) ^ 2 * exp ((↑(γ / 3) : ℂ) * I) ^ 2
          = exp ((↑(α / 3) : ℂ) * I) ^ 2 * (1 - exp ((↑(β / 3) : ℂ) * I) ^ 2 * exp ((↑(γ / 3) : ℂ) * I) ^ 2) := by ring
      rw [e]
      exact mul_ne_zero (pow_ne_zero 2 (Complex.exp_ne_zero _)) hd_qr
    field_simp
  rw [hkey2] at hP2f
  -- P₃: master + raccordo sul lato CA, poi eliminazione di r
  have hP3t := (raggio_raggio_unico C A P₃ (γ / 3) (α / 3) hCAne (by linarith) (by linarith)
    (by linarith)).mp ⟨h31, h32⟩
  have hD3 : Real.sin (γ / 3 + α / 3) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)).ne'
  have hrac3 := morley_raccordo (γ / 3) (α / 3) hD3 hd_rp
  have hP3f : P₃ = C + exp ((↑(γ / 3) : ℂ) * I) ^ 2 * (1 - exp ((↑(α / 3) : ℂ) * I) ^ 2) / (1 - exp ((↑(γ / 3) : ℂ) * I) ^ 2 * exp ((↑(α / 3) : ℂ) * I) ^ 2) * (A - C) := by
    rw [hP3t, ← mul_assoc, hrac3]
  have hkey3 : exp ((↑(γ / 3) : ℂ) * I) ^ 2 * (1 - exp ((↑(α / 3) : ℂ) * I) ^ 2) / (1 - exp ((↑(γ / 3) : ℂ) * I) ^ 2 * exp ((↑(α / 3) : ℂ) * I) ^ 2)
      = exp ((↑(Real.pi / 3) : ℂ) * I) ^ 2 * (1 - exp ((↑(α / 3) : ℂ) * I) ^ 2) / (exp ((↑(α / 3) : ℂ) * I) ^ 2 * (exp ((↑(β / 3) : ℂ) * I) ^ 2 - exp ((↑(Real.pi / 3) : ℂ) * I) ^ 2)) := by
    rw [hz2]
    have hd3' : exp ((↑(α / 3) : ℂ) * I) ^ 2 * (exp ((↑(β / 3) : ℂ) * I) ^ 2 - exp ((↑(α / 3) : ℂ) * I) ^ 2 * exp ((↑(β / 3) : ℂ) * I) ^ 2 * exp ((↑(γ / 3) : ℂ) * I) ^ 2) ≠ 0 := by
      have e : exp ((↑(α / 3) : ℂ) * I) ^ 2 * (exp ((↑(β / 3) : ℂ) * I) ^ 2 - exp ((↑(α / 3) : ℂ) * I) ^ 2 * exp ((↑(β / 3) : ℂ) * I) ^ 2 * exp ((↑(γ / 3) : ℂ) * I) ^ 2)
          = exp ((↑(α / 3) : ℂ) * I) ^ 2 * exp ((↑(β / 3) : ℂ) * I) ^ 2 * (1 - exp ((↑(γ / 3) : ℂ) * I) ^ 2 * exp ((↑(α / 3) : ℂ) * I) ^ 2) := by ring
      rw [e]
      exact mul_ne_zero
        (mul_ne_zero (pow_ne_zero 2 (Complex.exp_ne_zero _))
          (pow_ne_zero 2 (Complex.exp_ne_zero _))) hd_rp
    field_simp
  rw [hkey3] at hP3f
  exact ⟨hα0, hβ0, hαβπ, hP1f, hCf, hP2f, hP3f⟩
/-- **Teorema di Morley, ramo orientato.** In un triangolo orientato positivamente,
ogni terna di punti sulle intersezioni dei trisettori adiacenti ai tre lati forma
un triangolo equilatero. -/
theorem morley_orientato (A B C P₁ P₂ P₃ : ℂ)
    (horient : 0 < ((C - A) / (B - A)).im)
    (h₁ : P₁ ∈ trisettore A B C ∩ trisettore B A C)
    (h₂ : P₂ ∈ trisettore B C A ∩ trisettore C B A)
    (h₃ : P₃ ∈ trisettore C A B ∩ trisettore A C B) :
    dist P₁ P₂ = dist P₂ P₃ ∧ dist P₂ P₃ = dist P₃ P₁ := by
  obtain ⟨hα0, hβ0, hαβπ, hP1, hC, hP2, hP3⟩ :=
    morley_identifica A B C P₁ P₂ P₃ (((C - A) / (B - A)).arg) (((A - B) / (C - B)).arg)
      (((B - C) / (A - C)).arg) rfl rfl rfl horient h₁ h₂ h₃
  exact morley_equilatero_da_angoli (((C - A) / (B - A)).arg) (((A - B) / (C - B)).arg) A B
    hα0 hβ0 hαβπ _ _ _ P₁ C P₂ P₃ rfl rfl rfl hP1 hC hP2 hP3

/-- **Teorema di Morley.** In un triangolo non degenere del piano complesso (vertici
non allineati: `im((C−A)/(B−A)) ≠ 0`), i tre punti d'incontro dei trisettori adiacenti
a ciascun lato formano un triangolo equilatero. Il caso di orientazione negativa si
riduce al ramo orientato scambiando due vertici: i sei trisettori sono gli stessi
sei insiemi, e la conclusione (in `dist`) è simmetrica. -/
theorem morley (A B C P₁ P₂ P₃ : ℂ)
    (hnc : ((C - A) / (B - A)).im ≠ 0)
    (h₁ : P₁ ∈ trisettore A B C ∩ trisettore B A C)
    (h₂ : P₂ ∈ trisettore B C A ∩ trisettore C B A)
    (h₃ : P₃ ∈ trisettore C A B ∩ trisettore A C B) :
    dist P₁ P₂ = dist P₂ P₃ ∧ dist P₂ P₃ = dist P₃ P₁ := by
  rcases lt_or_gt_of_ne hnc with hneg | hpos
  · -- orientazione negativa: ramo positivo sul triangolo (A,C,B)
    have hzne : (C - A) / (B - A) ≠ 0 := by
      intro hc
      rw [hc] at hneg
      simp at hneg
    have hinv : 0 < (((C - A) / (B - A))⁻¹).im := by
      rw [Complex.inv_im]
      exact div_pos (by linarith) (Complex.normSq_pos.mpr hzne)
    have horient' : 0 < ((B - A) / (C - A)).im := by
      rw [← inv_div]
      exact hinv
    obtain ⟨e1, e2⟩ := morley_orientato A C B P₃ P₂ P₁ horient'
      ⟨h₃.2, h₃.1⟩ ⟨h₂.2, h₂.1⟩ ⟨h₁.2, h₁.1⟩
    constructor
    · calc dist P₁ P₂ = dist P₂ P₁ := dist_comm _ _
        _ = dist P₃ P₂ := e1.symm
        _ = dist P₂ P₃ := dist_comm _ _
    · calc dist P₂ P₃ = dist P₃ P₂ := dist_comm _ _
        _ = dist P₂ P₁ := e1
        _ = dist P₁ P₃ := e2
        _ = dist P₃ P₁ := dist_comm _ _
  · exact morley_orientato A B C P₁ P₂ P₃ hpos h₁ h₂ h₃

/-- **Esistenza e unicità (ramo orientato)**: in un triangolo orientato positivamente
i due trisettori adiacenti al lato `AB` si incontrano in un punto, unico. -/
theorem morley_esistenza_orientato (A B C : ℂ)
    (horient : 0 < ((C - A) / (B - A)).im) :
    ∃! P, P ∈ trisettore A B C ∩ trisettore B A C := by
  have hBA : B - A ≠ 0 := by
    intro hc
    rw [hc, div_zero] at horient
    simp at horient
  have hCA : C - A ≠ 0 := by
    intro hc
    rw [hc, zero_div] at horient
    simp at horient
  have hCB : C - B ≠ 0 := by
    intro hc
    have hCBe : C = B := by linear_combination hc
    rw [hCBe] at horient
    rw [div_self hBA] at horient
    simp at horient
  have hAC : A - C ≠ 0 := by
    intro hc
    apply hCA
    linear_combination -hc
  have hAB : A ≠ B := fun hc => hBA (by rw [hc]; ring)
  have h2im : 0 < ((A - B) / (C - B)).im := morley_orientazione_ciclica A B C hBA hCB horient
  have h3im : 0 < ((B - C) / (A - C)).im := morley_orientazione_ciclica B C A hCB hAC h2im
  have hα0 : 0 < ((C - A) / (B - A)).arg := morley_arg_pos horient
  have hβ0 : 0 < ((A - B) / (C - B)).arg := morley_arg_pos h2im
  have hγ0 : 0 < ((B - C) / (A - C)).arg := morley_arg_pos h3im
  have hsum : ((C - A) / (B - A)).arg + ((A - B) / (C - B)).arg + ((B - C) / (A - C)).arg
      = Real.pi := morley_somma_angoli A B C hBA hCB hAC horient
  have hargB : ((C - B) / (A - B)).arg = -(((A - B) / (C - B)).arg) := by
    rw [← inv_div, morley_arg_inv h2im]
  have hiff := fun P : ℂ => raggio_raggio_unico A B P ((((C - A) / (B - A)).arg) / 3)
    ((((A - B) / (C - B)).arg) / 3) hAB (by linarith) (by linarith) (by linarith)
  have hset : ∀ P : ℂ, (P ∈ trisettore A B C ∩ trisettore B A C) ↔
      (P ∈ raggio A (exp ((↑((((C - A) / (B - A)).arg) / 3) : ℂ) * I) * (B - A)) ∧
       P ∈ raggio B (exp ((↑(-((((A - B) / (C - B)).arg) / 3)) : ℂ) * I) * (A - B))) := by
    intro P
    simp only [trisettore, Set.mem_inter_iff]
    rw [hargB, neg_div]
  exact ⟨A + (↑(Real.sin ((((A - B) / (C - B)).arg) / 3)
      / Real.sin ((((C - A) / (B - A)).arg) / 3 + (((A - B) / (C - B)).arg) / 3)) : ℂ)
      * (exp ((↑((((C - A) / (B - A)).arg) / 3) : ℂ) * I) * (B - A)),
    (hset _).mpr ((hiff _).mpr rfl),
    fun y hy => (hiff y).mp ((hset y).mp hy)⟩

/-- **Esistenza e unicità.** In un triangolo non degenere i due trisettori adiacenti
al lato `AB` si incontrano in un punto, unico (il teorema di Morley non è vacuo).
Per gli altri lati si applica alla terna ciclata. -/
theorem morley_esistenza (A B C : ℂ) (hnc : ((C - A) / (B - A)).im ≠ 0) :
    ∃! P, P ∈ trisettore A B C ∩ trisettore B A C := by
  rcases lt_or_gt_of_ne hnc with hneg | hpos
  · -- orientazione negativa: la terna (B,A,C) ha lo stesso lato e orientazione positiva
    have hzne : (C - A) / (B - A) ≠ 0 := by
      intro hc
      rw [hc] at hneg
      simp at hneg
    have hBA : B - A ≠ 0 := by
      intro hc
      rw [hc, div_zero] at hneg
      simp at hneg
    have hCA : C - A ≠ 0 := by
      intro hc
      rw [hc, zero_div] at hneg
      simp at hneg
    have hCB : C - B ≠ 0 := by
      intro hc
      have hCBe : C = B := by linear_combination hc
      rw [hCBe, div_self hBA] at hneg
      simp at hneg
    have hBC : B - C ≠ 0 := by
      intro hc
      apply hCB
      linear_combination -hc
    have hABn : A - B ≠ 0 := by
      intro hc
      apply hBA
      linear_combination -hc
    have h1' : 0 < ((B - A) / (C - A)).im := by
      rw [← inv_div]
      rw [Complex.inv_im]
      exact div_pos (by linarith) (Complex.normSq_pos.mpr hzne)
    have h2im' : 0 < ((A - C) / (B - C)).im :=
      morley_orientazione_ciclica A C B hCA hBC h1'
    have h3im' : 0 < ((C - B) / (A - B)).im :=
      morley_orientazione_ciclica C B A hBC hABn h2im'
    rw [Set.inter_comm]
    exact morley_esistenza_orientato B A C h3im'
  · exact morley_esistenza_orientato A B C hpos

/-- **Non-degenerazione (ramo orientato)**: i punti di Morley sui lati `AB` e `BC`
sono distinti. Se coincidessero, il punto starebbe su due raggi distinti uscenti
da `B` (angoli `−β/3` e `+β/3` rispetto ai lati): eliminando i fattori si ottiene
`t₁ = t₂·ρ·e^{−iβ/3}` con `t₁,t₂,ρ > 0` reali, e la parte immaginaria dà
`0 = −t₂·ρ·sin(β/3) < 0`. -/
theorem morley_non_degenere_orientato (A B C P₁ P₂ : ℂ)
    (horient : 0 < ((C - A) / (B - A)).im)
    (h₁ : P₁ ∈ trisettore A B C ∩ trisettore B A C)
    (h₂ : P₂ ∈ trisettore B C A ∩ trisettore C B A) :
    P₁ ≠ P₂ := by
  have hBA : B - A ≠ 0 := by
    intro hc
    rw [hc, div_zero] at horient
    simp at horient
  have hCB : C - B ≠ 0 := by
    intro hc
    have hCBe : C = B := by linear_combination hc
    rw [hCBe, div_self hBA] at horient
    simp at horient
  have hABn : A - B ≠ 0 := by
    intro hc
    apply hBA
    linear_combination -hc
  have h2im : 0 < ((A - B) / (C - B)).im := morley_orientazione_ciclica A B C hBA hCB horient
  have hb0 : 0 < ((A - B) / (C - B)).arg := morley_arg_pos h2im
  have hbpi : ((A - B) / (C - B)).arg < Real.pi := morley_arg_lt_pi h2im
  have hargB : ((C - B) / (A - B)).arg = -(((A - B) / (C - B)).arg) := by
    rw [← inv_div, morley_arg_inv h2im]
  intro hP
  obtain ⟨-, h12⟩ := h₁
  obtain ⟨h21, -⟩ := h₂
  simp only [trisettore] at h12 h21
  rw [hargB, neg_div] at h12
  obtain ⟨t₁, ht₁, hw₁⟩ := h12
  obtain ⟨t₂, ht₂, hw₂⟩ := h21
  rw [hP] at hw₁
  -- forma polare del lato C−B rispetto ad A−B
  have hρpos : 0 < ‖(C - B) / (A - B)‖ := norm_pos_iff.mpr (div_ne_zero hCB hABn)
  have hpol0 := Complex.norm_mul_exp_arg_mul_I ((C - B) / (A - B))
  rw [hargB] at hpol0
  have hdiv : (C - B) / (A - B) * (A - B) = C - B := div_mul_cancel₀ _ hABn
  have hCBpol : C - B = ↑‖(C - B) / (A - B)‖
      * exp ((↑(-(((A - B) / (C - B)).arg)) : ℂ) * I) * (A - B) := by
    linear_combination -((A - B) * hpol0) - hdiv
  -- cancellazione di (A−B): equazione scalare fra i due raggi da B
  -- (hCBpol entra come equazione: un rw riscriverebbe anche il C−B dentro arg)
  have hstep : ((↑t₁ : ℂ) * exp ((↑(-((((A - B) / (C - B)).arg) / 3)) : ℂ) * I)) * (A - B)
      = ((↑t₂ : ℂ) * (exp ((↑((((A - B) / (C - B)).arg) / 3) : ℂ) * I)
        * (↑‖(C - B) / (A - B)‖
          * exp ((↑(-(((A - B) / (C - B)).arg)) : ℂ) * I)))) * (A - B) := by
    linear_combination hw₂ - hw₁
      + (↑t₂ : ℂ) * exp ((↑((((A - B) / (C - B)).arg) / 3) : ℂ) * I) * hCBpol
  have hcanc := mul_right_cancel₀ hABn hstep
  -- ricombinazione degli esponenziali: t₁ = (t₂·ρ)·e^{−iβ/3}
  have heA : exp ((↑(-((((A - B) / (C - B)).arg) / 3)) : ℂ) * I)
      * exp ((↑((((A - B) / (C - B)).arg) / 3) : ℂ) * I) = 1 := by
    rw [← Complex.exp_add]
    have e0 : (↑(-((((A - B) / (C - B)).arg) / 3)) : ℂ) * I
        + (↑((((A - B) / (C - B)).arg) / 3) : ℂ) * I = 0 := by
      push_cast; ring
    rw [e0, Complex.exp_zero]
  have heB : exp ((↑((((A - B) / (C - B)).arg) / 3) : ℂ) * I)
      * exp ((↑(-(((A - B) / (C - B)).arg)) : ℂ) * I)
      * exp ((↑((((A - B) / (C - B)).arg) / 3) : ℂ) * I)
      = exp ((↑(-((((A - B) / (C - B)).arg) / 3)) : ℂ) * I) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast; ring
  have hfin : (↑t₁ : ℂ) = (↑t₂ : ℂ) * (↑‖(C - B) / (A - B)‖ : ℂ)
      * exp ((↑(-((((A - B) / (C - B)).arg) / 3)) : ℂ) * I) := by
    linear_combination exp ((↑((((A - B) / (C - B)).arg) / 3) : ℂ) * I) * hcanc
      - (↑t₁ : ℂ) * heA + (↑t₂ : ℂ) * (↑‖(C - B) / (A - B)‖ : ℂ) * heB
  -- la parte immaginaria: 0 = −(t₂·ρ)·sin(β/3) < 0, assurdo
  have him := congrArg Complex.im hfin
  simp only [Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.mul_re,
    exp_ofReal_mul_I_im, exp_ofReal_mul_I_re, Real.sin_neg, Real.cos_neg,
    zero_mul, sub_zero, add_zero, mul_zero, mul_neg, zero_add] at him
  have hs : 0 < Real.sin ((((A - B) / (C - B)).arg) / 3) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hprod : 0 < t₂ * ‖(C - B) / (A - B)‖ * Real.sin ((((A - B) / (C - B)).arg) / 3) := by
    have := mul_pos (mul_pos ht₂ hρpos) hs
    linarith
  nlinarith [him, hprod]

/-- **Non-degenerazione.** Nelle stesse ipotesi del teorema di Morley, i tre punti
sono a due a due distinti: il triangolo di Morley è un equilatero vero e proprio,
mai un punto. -/
theorem morley_non_degenere (A B C P₁ P₂ P₃ : ℂ)
    (hnc : ((C - A) / (B - A)).im ≠ 0)
    (h₁ : P₁ ∈ trisettore A B C ∩ trisettore B A C)
    (h₂ : P₂ ∈ trisettore B C A ∩ trisettore C B A)
    (h₃ : P₃ ∈ trisettore C A B ∩ trisettore A C B) :
    P₁ ≠ P₂ ∧ P₂ ≠ P₃ ∧ P₃ ≠ P₁ := by
  obtain ⟨hd1, hd2⟩ := morley A B C P₁ P₂ P₃ hnc h₁ h₂ h₃
  have h12 : P₁ ≠ P₂ := by
    rcases lt_or_gt_of_ne hnc with hneg | hpos
    · -- ramo speculare: non-degenerazione sulla terna (A,C,B), poi via distanze
      have hzne : (C - A) / (B - A) ≠ 0 := by
        intro hc
        rw [hc] at hneg
        simp at hneg
      have horient' : 0 < ((B - A) / (C - A)).im := by
        rw [← inv_div]
        rw [Complex.inv_im]
        exact div_pos (by linarith) (Complex.normSq_pos.mpr hzne)
      have hne32 : P₃ ≠ P₂ :=
        morley_non_degenere_orientato A C B P₃ P₂ horient' ⟨h₃.2, h₃.1⟩ ⟨h₂.2, h₂.1⟩
      have hd : dist P₁ P₂ ≠ 0 := by
        rw [hd1]
        exact dist_ne_zero.mpr hne32.symm
      exact dist_ne_zero.mp hd
    · exact morley_non_degenere_orientato A B C P₁ P₂ hpos h₁ h₂
  refine ⟨h12, ?_, ?_⟩
  · have hd : dist P₂ P₃ ≠ 0 := by
      rw [← hd1]
      exact dist_ne_zero.mpr h12
    exact dist_ne_zero.mp hd
  · have hd : dist P₃ P₁ ≠ 0 := by
      rw [← hd2, ← hd1]
      exact dist_ne_zero.mpr h12
    exact dist_ne_zero.mp hd

/-- **Ponte alla forma classica**: se i tre vertici non sono allineati (nel senso
di mathlib, `Collinear ℝ`), il rapporto `(C−A)/(B−A)` non è reale. Contrapposta:
rapporto reale ⟹ i tre punti giacciono su una retta. -/
theorem morley_not_collinear_im (A B C : ℂ)
    (hnc : ¬ Collinear ℝ ({A, B, C} : Set ℂ)) :
    ((C - A) / (B - A)).im ≠ 0 := by
  intro h0
  apply hnc
  by_cases hBA : B - A = 0
  · -- B = A: due soli punti, sempre allineati
    have hB : B = A := by linear_combination hBA
    rw [hB, Set.insert_idem]
    exact collinear_pair ℝ A C
  · -- rapporto reale: C sta sulla retta per A diretta come B−A
    have hz : (C - A) / (B - A) = ((((C - A) / (B - A)).re : ℝ) : ℂ) := by
      have hri := Complex.re_add_im ((C - A) / (B - A))
      rw [h0] at hri
      simpa using hri.symm
    have hC : C = ((((C - A) / (B - A)).re : ℝ) : ℂ) * (B - A) + A := by
      have hmul : (C - A) / (B - A) * (B - A) = C - A := div_mul_cancel₀ _ hBA
      rw [hz] at hmul
      linear_combination -hmul
    apply (collinear_iff_exists_forall_eq_smul_vadd ({A, B, C} : Set ℂ)).mpr
    refine ⟨A, B - A, ?_⟩
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with hpA | hpB | hpC
    · exact ⟨0, by rw [hpA]; simp⟩
    · refine ⟨1, ?_⟩
      rw [hpB]
      simp only [vadd_eq_add, Complex.real_smul]
      push_cast
      ring
    · refine ⟨(((C - A) / (B - A)).re : ℝ), ?_⟩
      rw [hpC]
      simp only [vadd_eq_add, Complex.real_smul]
      exact hC

/-- **Teorema di Morley, forma classica.** In un triangolo con vertici non
allineati, i tre punti d'incontro dei trisettori adiacenti a ciascun lato
formano un triangolo equilatero. -/
theorem morley_classico (A B C P₁ P₂ P₃ : ℂ)
    (hnc : ¬ Collinear ℝ ({A, B, C} : Set ℂ))
    (h₁ : P₁ ∈ trisettore A B C ∩ trisettore B A C)
    (h₂ : P₂ ∈ trisettore B C A ∩ trisettore C B A)
    (h₃ : P₃ ∈ trisettore C A B ∩ trisettore A C B) :
    dist P₁ P₂ = dist P₂ P₃ ∧ dist P₂ P₃ = dist P₃ P₁ :=
  morley A B C P₁ P₂ P₃ (morley_not_collinear_im A B C hnc) h₁ h₂ h₃

/-- **Esistenza e unicità, forma classica.** -/
theorem morley_esistenza_classico (A B C : ℂ)
    (hnc : ¬ Collinear ℝ ({A, B, C} : Set ℂ)) :
    ∃! P, P ∈ trisettore A B C ∩ trisettore B A C :=
  morley_esistenza A B C (morley_not_collinear_im A B C hnc)

/-- **Non-degenerazione, forma classica.** -/
theorem morley_non_degenere_classico (A B C P₁ P₂ P₃ : ℂ)
    (hnc : ¬ Collinear ℝ ({A, B, C} : Set ℂ))
    (h₁ : P₁ ∈ trisettore A B C ∩ trisettore B A C)
    (h₂ : P₂ ∈ trisettore B C A ∩ trisettore C B A)
    (h₃ : P₃ ∈ trisettore C A B ∩ trisettore A C B) :
    P₁ ≠ P₂ ∧ P₂ ≠ P₃ ∧ P₃ ≠ P₁ :=
  morley_non_degenere A B C P₁ P₂ P₃ (morley_not_collinear_im A B C hnc) h₁ h₂ h₃

open Complex InnerProductGeometry

/-- **L5 — angolo puntuale come |arg|.** Per `X, Y ≠ A` in ℂ:
`∠ X A Y = |arg((X−A)/(Y−A))|`. -/
theorem angle_punti_eq_abs_arg {A X Y : ℂ} (hX : X ≠ A) (hY : Y ≠ A) :
    ∠ X A Y = |((X - A) / (Y - A)).arg| := by
  rw [EuclideanGeometry.angle, vsub_eq_sub, vsub_eq_sub]
  exact Complex.angle_eq_abs_arg (sub_ne_zero.mpr hX) (sub_ne_zero.mpr hY)

/-- **L6 — coordinate baricentriche dal vertice A.** Se `X` sta nell'inviluppo
convesso di `{A, B, C}`, allora `X − A = b·(B−A) + c·(C−A)` con `b, c ≥ 0`,
`b + c ≤ 1`. -/
theorem hull_tre_baricentriche {A B C X : ℂ}
    (hX : X ∈ convexHull ℝ ({A, B, C} : Set ℂ)) :
    ∃ b c : ℝ, 0 ≤ b ∧ 0 ≤ c ∧ b + c ≤ 1 ∧
      X - A = (b : ℂ) * (B - A) + (c : ℂ) * (C - A) := by
  rw [convexHull_insert ⟨B, by simp⟩, convexHull_pair, mem_convexJoin] at hX
  obtain ⟨a, ha, y, hy, hXy⟩ := hX
  rw [Set.mem_singleton_iff] at ha
  rw [ha] at hXy
  obtain ⟨u, v, hu, hv, huv, hy_eq⟩ := hy
  obtain ⟨s, t, hs, ht, hst, hX_eq⟩ := hXy
  refine ⟨t * u, t * v, mul_nonneg ht hu, mul_nonneg ht hv, ?_, ?_⟩
  · have htuv : t * u + t * v = t := by rw [← mul_add, huv, mul_one]
    linarith
  · rw [← hX_eq, ← hy_eq]
    simp only [Complex.real_smul]
    have hs1 : (s : ℂ) + (t : ℂ) = 1 := by exact_mod_cast hst
    have hu1 : (u : ℂ) + (v : ℂ) = 1 := by exact_mod_cast huv
    push_cast
    linear_combination A * hs1 + (t : ℂ) * A * hu1

/-- **L7 — IL CRUX: dal terzo non orientato all'argomento orientato.**
Se `X` sta nell'inviluppo convesso di `{A,B,C}`, l'angolo `∠XAB` è positivo e
vale un terzo di `∠CAB`, allora l'argomento orientato di `X` visto da `A`
(rispetto alla direzione `B−A`) è esattamente un terzo di quello di `C`:
il segno viene dalle coordinate baricentriche (`im zX = c·im zC`, `c > 0`). -/
theorem arg_terzo_da_hull {A B C X : ℂ}
    (hnc : ¬ Collinear ℝ ({A, B, C} : Set ℂ))
    (hX : X ∈ convexHull ℝ ({A, B, C} : Set ℂ))
    (hpos : 0 < ∠ X A B)
    (hthird : 3 * ∠ X A B = ∠ C A B) :
    ((X - A) / (B - A)).arg = ((C - A) / (B - A)).arg / 3 := by
  have hAB : A ≠ B := ne₁₂_of_not_collinear hnc
  have hAC : A ≠ C := ne₁₃_of_not_collinear hnc
  have hBA : B - A ≠ 0 := sub_ne_zero.mpr (Ne.symm hAB)
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  -- X ≠ A: altrimenti ∠XAB = π/2 e 3·(π/2) = ∠CAB ≤ π, assurdo
  have hXA : X ≠ A := by
    intro h
    rw [h] at hthird
    rw [EuclideanGeometry.angle, vsub_eq_sub, vsub_eq_sub, sub_self,
        angle_zero_left] at hthird
    have hle : ∠ C A B ≤ Real.pi := by
      rw [EuclideanGeometry.angle, vsub_eq_sub, vsub_eq_sub]
      exact angle_le_pi _ _
    linarith
  have hXAd : X - A ≠ 0 := sub_ne_zero.mpr hXA
  -- coordinate baricentriche e forma zX = b + c·zC
  obtain ⟨b, c, hb, hc, hbc, hcomb⟩ := hull_tre_baricentriche hX
  have hzX : (X - A) / (B - A) = (b : ℂ) + (c : ℂ) * ((C - A) / (B - A)) := by
    field_simp
    linear_combination hcomb
  have him : ((X - A) / (B - A)).im = c * ((C - A) / (B - A)).im := by
    rw [hzX]
    simp [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re]
  have hzCim : ((C - A) / (B - A)).im ≠ 0 := morley_not_collinear_im A B C hnc
  -- gli angoli come |arg|
  have hangX : ∠ X A B = |((X - A) / (B - A)).arg| :=
    angle_punti_eq_abs_arg hXA (Ne.symm hAB)
  have hangC : ∠ C A B = |((C - A) / (B - A)).arg| :=
    angle_punti_eq_abs_arg (Ne.symm hAC) (Ne.symm hAB)
  -- la coordinata trasversale è positiva
  have hcpos : 0 < c := by
    rcases lt_or_eq_of_le hc with h | h
    · exact h
    · exfalso
      have hc0 : c = 0 := h.symm
      have hbne : b ≠ 0 := by
        intro hb0
        apply hXAd
        rw [hcomb, hb0, hc0]
        push_cast
        ring
      have hreale : (X - A) / (B - A) = ((b : ℝ) : ℂ) := by
        rw [hzX, hc0]
        push_cast
        ring
      have hargX0 : ((X - A) / (B - A)).arg = 0 := by
        rw [hreale]
        exact Complex.arg_ofReal_of_nonneg hb
      rw [hangX, hargX0] at hpos
      simp at hpos
  -- i due rami sul segno, con segni concordi
  rw [hangX, hangC] at hthird
  rcases lt_or_gt_of_ne hzCim with hneg | hposC
  · have hXneg : ((X - A) / (B - A)).arg < 0 := by
      rw [Complex.arg_neg_iff, him]
      exact mul_neg_of_pos_of_neg hcpos hneg
    have hCneg : ((C - A) / (B - A)).arg < 0 := Complex.arg_neg_iff.mpr hneg
    rw [abs_of_neg hXneg, abs_of_neg hCneg] at hthird
    linarith
  · have hXpos : 0 < ((X - A) / (B - A)).arg := by
      apply morley_arg_pos
      rw [him]
      exact mul_pos hcpos hposC
    have hCpos : 0 < ((C - A) / (B - A)).arg := morley_arg_pos hposC
    rw [abs_of_pos hXpos, abs_of_pos hCpos] at hthird
    linarith

/-- **Non-degenerazione dal terzo**: se `3·∠XAB = ∠CAB` allora `X ≠ A`
(altrimenti l'angolo degenere varrebbe `π/2` e `3·π/2 ≤ π`). -/
theorem ne_da_terzo {A B C X : ℂ} (hthird : 3 * ∠ X A B = ∠ C A B) : X ≠ A := by
  intro h
  rw [h] at hthird
  rw [EuclideanGeometry.angle, vsub_eq_sub, vsub_eq_sub, sub_self,
      angle_zero_left] at hthird
  have hle : ∠ C A B ≤ Real.pi := by
    rw [EuclideanGeometry.angle, vsub_eq_sub, vsub_eq_sub]
    exact angle_le_pi _ _
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  linarith

/-- **L8 — dall'argomento alla semiretta**: se `arg((W−X)/(Y−X)) = arg((Z−X)/(Y−X))/3`
e `W ≠ X`, allora `W` sta sul trisettore di `X` adiacente a `XY`. -/
theorem mem_trisettore_da_arg {X Y Z W : ℂ}
    (hYX : Y - X ≠ 0) (hWX : W - X ≠ 0)
    (harg : ((W - X) / (Y - X)).arg = ((Z - X) / (Y - X)).arg / 3) :
    W ∈ trisettore X Y Z := by
  have hzW : (W - X) / (Y - X) ≠ 0 := div_ne_zero hWX hYX
  refine ⟨‖(W - X) / (Y - X)‖, norm_pos_iff.mpr hzW, ?_⟩
  have hna := Complex.norm_mul_exp_arg_mul_I ((W - X) / (Y - X))
  rw [harg] at hna
  have hdiv : (W - X) / (Y - X) * (Y - X) = W - X := div_mul_cancel₀ _ hYX
  linear_combination (-(Y - X)) * hna - hdiv

/-- **L9 — vertice completo**: dalle ipotesi non orientate del benchmark a un
vertice (tre angoli uguali, terzo del totale, punti nell'inviluppo), i due punti
stanno sui due trisettori orientati adiacenti ai lati `XY` e `XZ`. -/
theorem due_trisettori_da_vertice {X Y Z U V : ℂ}
    (hnc : ¬ Collinear ℝ ({X, Y, Z} : Set ℂ))
    (hU : U ∈ convexHull ℝ ({X, Y, Z} : Set ℂ))
    (hV : V ∈ convexHull ℝ ({X, Y, Z} : Set ℂ))
    (hpos : 0 < ∠ Z X V)
    (h₁ : ∠ Z X V = ∠ V X U) (h₂ : ∠ V X U = ∠ U X Y)
    (h₃ : 3 * ∠ U X Y = ∠ Z X Y) :
    U ∈ trisettore X Y Z ∧ V ∈ trisettore X Z Y := by
  have hXY : X ≠ Y := ne₁₂_of_not_collinear hnc
  have hXZ : X ≠ Z := ne₁₃_of_not_collinear hnc
  have hYX : Y - X ≠ 0 := sub_ne_zero.mpr (Ne.symm hXY)
  have hZX : Z - X ≠ 0 := sub_ne_zero.mpr (Ne.symm hXZ)
  -- non-collinearità della terna scambiata {X, Z, Y}
  have hnc' : ¬ Collinear ℝ ({X, Z, Y} : Set ℂ) := by
    intro hcol
    apply hnc
    have : ({X, Y, Z} : Set ℂ) = ({X, Z, Y} : Set ℂ) := by
      rw [Set.pair_comm Y Z]
    rwa [this]
  have hU' : U ∈ convexHull ℝ ({X, Z, Y} : Set ℂ) := by
    have : ({X, Z, Y} : Set ℂ) = ({X, Y, Z} : Set ℂ) := by
      rw [Set.pair_comm Z Y]
    rwa [this]
  have hV' : V ∈ convexHull ℝ ({X, Z, Y} : Set ℂ) := by
    have : ({X, Z, Y} : Set ℂ) = ({X, Y, Z} : Set ℂ) := by
      rw [Set.pair_comm Z Y]
    rwa [this]
  constructor
  · -- U sul trisettore adiacente a XY
    have hposU : 0 < ∠ U X Y := by
      rw [← h₂, ← h₁]; exact hpos
    have hargU := arg_terzo_da_hull hnc hU hposU h₃
    exact mem_trisettore_da_arg hYX (sub_ne_zero.mpr (ne_da_terzo h₃)) hargU
  · -- V sul trisettore adiacente a XZ (terna scambiata)
    have hVXZ : ∠ V X Z = ∠ U X Y := by
      rw [EuclideanGeometry.angle_comm]
      rw [h₁, h₂]
    have hposV : 0 < ∠ V X Z := by
      rw [hVXZ, ← h₂, ← h₁]; exact hpos
    have hthirdV : 3 * ∠ V X Z = ∠ Y X Z := by
      rw [hVXZ, h₃, EuclideanGeometry.angle_comm]
    have hargV := arg_terzo_da_hull hnc' hV' hposV hthirdV
    exact mem_trisettore_da_arg hZX (sub_ne_zero.mpr (ne_da_terzo hthirdV)) hargV


/-- L'isometria lineare canonica `Plane ≃ ℂ`: `(x₀, x₁) ↦ x₀ + x₁·I`. -/
noncomputable def planeToComplex : LeanEval.Geometry.Morley.Plane ≃ₗᵢ[ℝ] ℂ :=
  Complex.orthonormalBasisOneI.repr.symm

/-- **L1 — trasporto della distanza.** -/
theorem planeToComplex_dist (X Y : LeanEval.Geometry.Morley.Plane) :
    dist (planeToComplex X) (planeToComplex Y) = dist X Y :=
  planeToComplex.dist_map X Y

/-- **L2 — trasporto dell'angolo non orientato.** -/
theorem planeToComplex_angle (X Y Z : LeanEval.Geometry.Morley.Plane) :
    ∠ (planeToComplex X) (planeToComplex Y) (planeToComplex Z) = ∠ X Y Z :=
  planeToComplex.toAffineIsometryEquiv.toAffineIsometry.angle_map X Y Z

/-- **L3 — trasporto dell'inviluppo convesso.** -/
theorem planeToComplex_mem_convexHull {A B C X : LeanEval.Geometry.Morley.Plane}
    (hX : X ∈ convexHull ℝ ({A, B, C} : Set LeanEval.Geometry.Morley.Plane)) :
    planeToComplex X ∈
      convexHull ℝ ({planeToComplex A, planeToComplex B, planeToComplex C} : Set ℂ) := by
  have hlin : IsLinearMap ℝ (planeToComplex : Plane → ℂ) :=
    ⟨fun x y => map_add _ x y, fun c x => map_smul _ c x⟩
  have himage := hlin.image_convexHull ({A, B, C} : Set Plane)
  have himg := Set.mem_image_of_mem (planeToComplex : Plane → ℂ) hX
  rw [himage] at himg
  have hset : (planeToComplex : Plane → ℂ) '' ({A, B, C} : Set Plane)
      = ({planeToComplex A, planeToComplex B, planeToComplex C} : Set ℂ) := by
    simp [Set.image_insert_eq]
  rwa [hset] at himg

/-- **L4 — trasporto della non-collinearità.** -/
theorem planeToComplex_not_collinear {A B C : LeanEval.Geometry.Morley.Plane}
    (h : ¬ Collinear ℝ ({A, B, C} : Set LeanEval.Geometry.Morley.Plane)) :
    ¬ Collinear ℝ
      ({planeToComplex A, planeToComplex B, planeToComplex C} : Set ℂ) := by
  intro hc
  apply h
  rw [collinear_iff_exists_forall_eq_smul_vadd] at hc ⊢
  obtain ⟨p₀, v, hpv⟩ := hc
  refine ⟨planeToComplex.symm p₀, planeToComplex.symm v, ?_⟩
  intro p hp
  have himg : planeToComplex p
      ∈ ({planeToComplex A, planeToComplex B, planeToComplex C} : Set ℂ) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl <;> simp
  obtain ⟨r, hr⟩ := hpv _ himg
  refine ⟨r, ?_⟩
  apply planeToComplex.injective
  rw [hr]
  simp [vadd_eq_add, map_add, map_smul,
    LinearIsometryEquiv.apply_symm_apply]
/-- **L10 — configurazione del benchmark in ℂ ⟹ distanze uguali.**
Le dodici condizioni angolari non orientate ai tre vertici, più le appartenenze
all'inviluppo convesso, mettono i tre punti sulle sei intersezioni di trisettori
orientati; il nostro `morley_classico` conclude. -/
theorem morley_config_complessa (A B C P Q R : ℂ)
    (hnc : ¬ Collinear ℝ ({A, B, C} : Set ℂ))
    (hP : P ∈ convexHull ℝ ({A, B, C} : Set ℂ))
    (hQ : Q ∈ convexHull ℝ ({A, B, C} : Set ℂ))
    (hR : R ∈ convexHull ℝ ({A, B, C} : Set ℂ))
    (hA1 : 0 < ∠ C A R) (hA2 : ∠ C A R = ∠ R A P) (hA3 : ∠ R A P = ∠ P A B)
    (hA4 : 3 * ∠ P A B = ∠ C A B)
    (hB1 : 0 < ∠ A B P) (hB2 : ∠ A B P = ∠ P B Q) (hB3 : ∠ P B Q = ∠ Q B C)
    (hB4 : 3 * ∠ Q B C = ∠ A B C)
    (hC1 : 0 < ∠ B C Q) (hC2 : ∠ B C Q = ∠ Q C R) (hC3 : ∠ Q C R = ∠ R C A)
    (hC4 : 3 * ∠ R C A = ∠ B C A) :
    dist P Q = dist Q R ∧ dist Q R = dist R P := by
  -- rotazioni cicliche dell'insieme dei vertici
  have hrotB : ({B, C, A} : Set ℂ) = ({A, B, C} : Set ℂ) := by
    ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have hrotC : ({C, A, B} : Set ℂ) = ({A, B, C} : Set ℂ) := by
    ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have hncB : ¬ Collinear ℝ ({B, C, A} : Set ℂ) := by rwa [hrotB]
  have hncC : ¬ Collinear ℝ ({C, A, B} : Set ℂ) := by rwa [hrotC]
  have hPB : P ∈ convexHull ℝ ({B, C, A} : Set ℂ) := by rwa [hrotB]
  have hQB : Q ∈ convexHull ℝ ({B, C, A} : Set ℂ) := by rwa [hrotB]
  have hQC : Q ∈ convexHull ℝ ({C, A, B} : Set ℂ) := by rwa [hrotC]
  have hRC : R ∈ convexHull ℝ ({C, A, B} : Set ℂ) := by rwa [hrotC]
  -- vertice A: P sul trisettore di AB, R su quello di AC
  obtain ⟨hPA, hRA⟩ := due_trisettori_da_vertice hnc hP hR hA1 hA2 hA3 hA4
  -- vertice B: Q sul trisettore di BC, P su quello di BA
  obtain ⟨hQB', hPB'⟩ := due_trisettori_da_vertice hncB hQB hPB hB1 hB2 hB3 hB4
  -- vertice C: R sul trisettore di CA, Q su quello di CB
  obtain ⟨hRC', hQC'⟩ := due_trisettori_da_vertice hncC hRC hQC hC1 hC2 hC3 hC4
  exact morley_classico A B C P Q R hnc ⟨hPA, hPB'⟩ ⟨hQB', hQC'⟩ ⟨hRC', hRA⟩
