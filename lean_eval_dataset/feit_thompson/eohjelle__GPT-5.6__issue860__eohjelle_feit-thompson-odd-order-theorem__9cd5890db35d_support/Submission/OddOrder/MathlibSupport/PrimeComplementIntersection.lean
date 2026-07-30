import Submission.OddOrder.MathlibSupport.PrimeComplementContainment
import Submission.OddOrder.MathlibSupport.PrimeOrderInvariantSylow

/-!
Intersecting a Hall subgroup containing a complement with the normal factor.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped Pointwise

universe u

variable {G : Type u} [Group G] [Finite G] [IsSolvable G]
variable {K R : Subgroup G}

/-- A coprime prime-order factor acting on `K` normalizes a proper Hall
`q'`-subgroup of `K`; that subgroup generates `K` together with every ambient
image of a Sylow `q`-subgroup of `K`. -/
theorem exists_normalized_primeComplement_intersection
    (hKR : K.IsComplement' R)
    (hnormK : R ≤ Subgroup.normalizer (K : Set G))
    (hcop : Nat.Coprime (Nat.card K) (Nat.card R))
    (hRprime : (Nat.card R).Prime)
    {q : ℕ} (hq : q.Prime) (hqdvd : q ∣ Nat.card K) :
    ∃ Q' : Subgroup G,
      Q' < K ∧
      IsPrimeComplement q (Q'.subgroupOf K) ∧
      R ≤ Subgroup.normalizer (Q' : Set G) ∧
      ∀ Q : Subgroup G, IsSylowSubgroupOf q Q K → K ≤ Q ⊔ Q' := by
  classical
  letI : K.Normal := by
    apply Subgroup.normalizer_eq_top_iff.mp
    apply top_unique
    rw [← hKR.sup_eq_top]
    exact sup_le Subgroup.le_normalizer hnormK
  obtain ⟨J, hJ, hRJ⟩ :=
    exists_primeComplement_ge_prime_factor hKR hcop hRprime hq hqdvd
  let Q' : Subgroup G := K ⊓ J
  have hQ'K : Q' ≤ K := inf_le_left
  have hQ'J : Q' ≤ J := inf_le_right
  have hKJ : K ⊔ J = ⊤ := by
    apply top_unique
    rw [← hKR.sup_eq_top]
    exact sup_le le_sup_left (hRJ.trans le_sup_right)
  have hrelQ'J : Q'.relIndex J = K.index := by
    calc
      Q'.relIndex J = K.relIndex J := by
        exact Subgroup.inf_relIndex_right K J
      _ = K.relIndex (J ⊔ K) :=
        (Subgroup.relIndex_sup_right J K).symm
      _ = K.index := by rw [sup_comm, hKJ, Subgroup.relIndex_top_right]
  have hcardQ'J : Nat.card (Q'.subgroupOf J) = Nat.card Q' :=
    natCard_subgroupOf_eq hQ'J
  have hcardJ : Nat.card J = K.index * Nat.card Q' := by
    calc
      Nat.card J = (Q'.subgroupOf J).index * Nat.card (Q'.subgroupOf J) :=
        (Q'.subgroupOf J).index_mul_card.symm
      _ = K.index * Nat.card Q' := by
        change Q'.relIndex J * Nat.card (Q'.subgroupOf J) = _
        rw [hrelQ'J, hcardQ'J]
  let QK : Subgroup K := Q'.subgroupOf K
  have hcardQK : Nat.card QK = Nat.card Q' :=
    natCard_subgroupOf_eq hQ'K
  have hindexQK : QK.index = J.index := by
    have heq :
        (J.index * K.index) * Nat.card Q' =
          (QK.index * K.index) * Nat.card Q' := by
      calc
        (J.index * K.index) * Nat.card Q' =
            J.index * Nat.card J := by rw [hcardJ, mul_assoc]
        _ = Nat.card G := J.index_mul_card
        _ = K.index * Nat.card K := K.index_mul_card.symm
        _ = K.index * (QK.index * Nat.card QK) := by
          rw [QK.index_mul_card]
        _ = (QK.index * K.index) * Nat.card Q' := by
          rw [hcardQK]
          ac_rfl
    have hcancelQ := Nat.eq_of_mul_eq_mul_right Nat.card_pos heq
    exact Nat.eq_of_mul_eq_mul_right
      (Nat.pos_of_ne_zero K.index_ne_zero_of_finite) hcancelQ.symm
  have hQKHall : IsPrimeComplement q QK := by
    constructor
    · rw [hcardQK]
      exact hJ.card_coprime.coprime_dvd_left
        (Subgroup.card_dvd_of_le hQ'J)
    · rw [hindexQK]
      exact hJ.exists_index_eq_pow
  have hQ'lt : Q' < K := by
    refine lt_of_le_of_ne hQ'K ?_
    intro hQ'eq
    apply hQKHall.ne_top_of_dvd_card hq hqdvd
    apply Subgroup.subgroupOf_eq_top.mpr
    simp [hQ'eq]
  have hQ'norm : R ≤ Subgroup.normalizer (Q' : Set G) := by
    calc
      R ≤ Subgroup.normalizer (K : Set G) ⊓
          Subgroup.normalizer (J : Set G) :=
        le_inf hnormK (hRJ.trans Subgroup.le_normalizer)
      _ ≤ Subgroup.normalizer (Q' : Set G) := by
        exact Subgroup.inf_normalizer_le_normalizer_inf
  refine ⟨Q', hQ'lt, hQKHall, hQ'norm, ?_⟩
  intro Q hQsylow
  obtain ⟨P, rfl⟩ := hQsylow
  have htop : (P : Subgroup K) ⊔ QK = ⊤ :=
    hQKHall.sylow_sup_eq_top hq P
  have hmapped := congrArg (Subgroup.map K.subtype) htop
  rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hQ'K,
    ← MonoidHom.range_eq_map, Subgroup.range_subtype] at hmapped
  exact hmapped.ge

end Submission.OddOrder.MathlibSupport
