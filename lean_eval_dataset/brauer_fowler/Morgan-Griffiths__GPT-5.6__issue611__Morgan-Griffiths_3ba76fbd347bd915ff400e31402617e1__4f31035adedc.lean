import Mathlib
import Submission.Helpers

namespace Submission

/-ResultProofDefinitionsBegin-/

-- If a simple group has any nontrivial permutation representation, simplicity
-- turns it into a faithful one.  It is useful to make this cardinal bookkeeping
-- completely explicit; it does not use `Fintype` choices on the original group.
private lemma bf_card_le_factorial_of_action {G α : Type*}
    [Group G] [Finite G] [Finite α] [IsSimpleGroup G]
    (ρ : G →* Equiv.Perm α) (hnon : ∃ g : G, ρ g ≠ 1) :
    Nat.card G ≤ (Nat.card α).factorial := by
  classical
  have hbot : ρ.ker = (⊥ : Subgroup G) := by
    rcases (ρ.normal_ker).eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      obtain ⟨g, hg⟩ := hnon
      have hgker : g ∈ ρ.ker := by rw [h]; trivial
      exact hg (MonoidHom.mem_ker.mp hgker)
  have hinj : Function.Injective (fun g : G => ρ g) :=
    (MonoidHom.ker_eq_bot_iff ρ).mp hbot
  have hle : Nat.card G ≤ Nat.card (Equiv.Perm α) :=
    Nat.card_le_card_of_injective (fun g : G => ρ g) hinj
  simpa [Nat.card_perm] using hle

-- Action on the left cosets of a proper subgroup is nonconstant.  This little
-- lemma avoids using normality of the subgroup.
private lemma bf_toPermHom_nontrivial {G : Type*} [Group G]
    (H : Subgroup G) (hproper : H ≠ ⊤) :
    ∃ g : G, (MulAction.toPermHom G (G ⧸ H)) g ≠ 1 := by
  classical
  by_contra hh
  push_neg at hh
  have hstab_mem : ∀ g : G,
      g ∈ MulAction.stabilizer G ((1 : G) : G ⧸ H) := by
    intro g
    have hp := congrArg (fun σ : Equiv.Perm (G ⧸ H) =>
        σ ((1 : G) : G ⧸ H)) (hh g)
    have hs : g • ((1 : G) : G ⧸ H) = ((1 : G) : G ⧸ H) := by
      simpa [MulAction.toPermHom_apply, MulAction.toPerm_apply] using hp
    exact (MulAction.mem_stabilizer_iff).2 hs
  have hstop : MulAction.stabilizer G ((1 : G) : G ⧸ H) = ⊤ :=
    (Subgroup.eq_top_iff' _).2 hstab_mem
  have hHtop : H = ⊤ := by
    rw [← MulAction.stabilizer_quotient H]
    exact hstop
  exact hproper hHtop

-- Thus a proper subgroup of small index is enough for the desired numerical
-- estimate; no normality hypothesis is needed.
private lemma bf_card_le_factorial_index {G : Type*}
    [Group G] [Finite G] [IsSimpleGroup G]
    (H : Subgroup G) (hproper : H ≠ ⊤) :
    Nat.card G ≤ H.index.factorial := by
  classical
  have h := bf_card_le_factorial_of_action
    (G:=G) (α:= G ⧸ H)
    (MulAction.toPermHom G (G ⧸ H))
    (bf_toPermHom_nontrivial H hproper)
  simpa [Subgroup.index_eq_card] using h

-- The involution centralizer is at least a *proper* subgroup.  Notice that
-- one cannot argue this from noncommutativity alone: it is simplicity which
-- first kills the centre.
private lemma bf_centralizer_proper {G : Type*} [Group G]
    [IsSimpleGroup G] (hnab : ∃ a b : G, a*b ≠ b*a)
    (t : G) (ht : orderOf t = 2) :
    Subgroup.centralizer ({t} : Set G) ≠ ⊤ := by
  have hcent_not : Subgroup.center G ≠ ⊤ := by
    intro hC
    have hcomm : ∀ a b : G, a*b = b*a :=
      (isMulCommutative_iff.mp (Subgroup.center_eq_top_iff.mp hC))
    obtain ⟨a,b,hab⟩ := hnab
    exact hab (hcomm a b)
  have hcent_bot : Subgroup.center G = ⊥ := by
    rcases (show (Subgroup.center G).Normal from inferInstance).eq_bot_or_eq_top with h|h
    · exact h
    · exact False.elim (hcent_not h)
  intro htop
  have hsub : ({t} : Set G) ⊆ (Subgroup.center G : Set G) :=
    (Subgroup.centralizer_eq_top_iff_subset.mp htop)
  have htmem : t ∈ Subgroup.center G := hsub (by simp)
  have teq : t = 1 := (Subgroup.mem_bot.mp (by simpa [hcent_bot] using htmem))
  have hone : orderOf t = 1 := by simpa [teq]
  omega


private lemma orbit_card {G:Type*}[Group G][Finite G] (t:G) :
 Nat.card {x:G // x ∈ MulAction.orbit (ConjAct G) t} *
   Nat.card (Subgroup.centralizer ({t}:Set G)) = Nat.card G := by
 classical
 letI : Fintype G := Fintype.ofFinite G
 letI : Fintype (ConjAct G) := Fintype.ofEquiv G ConjAct.toConjAct.toEquiv
 -- use formula with chosen finite instances
 rw [Subgroup.nat_card_centralizer_nat_card_stabilizer]
 -- translate all cards
 repeat' rw [Nat.card_eq_fintype_card]
 have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct G) t
 -- card subgroup conj
 have hc : Fintype.card (ConjAct G) = Fintype.card G := Fintype.card_congr ConjAct.toConjAct.toEquiv.symm
 exact h.trans hc
private lemma inv_orbit {G:Type*}[Group G] {t:G} (ht : t⁻¹=t)
 (x : {x:G // x ∈ MulAction.orbit (ConjAct G) t}) : (x:G)⁻¹ = (x:G) := by
 rcases (MulAction.mem_orbit_iff.mp x.property) with ⟨g, hg⟩
 -- g : ConjAct G
 have hv : (x:G) = (ConjAct.ofConjAct g) * t * (ConjAct.ofConjAct g)⁻¹ := by
   rw [← hg]
   rfl
 rw [hv]
 simp [ht, mul_assoc]

private lemma card_neqpairs (X:Type*) [Fintype X] [DecidableEq X] :
 (Finset.univ.filter (fun p : X×X => p.1 ≠ p.2)).card =
   Fintype.card X * (Fintype.card X - 1) := by
 classical
 let e : {p : X×X // p.1 = p.2} ≃ X :=
   { toFun := fun p => p.val.1
     invFun := fun x => ⟨(x,x), rfl⟩
     left_inv := by intro p; cases p with | mk p h => ?_ ; cases p with | mk a b => ?_ ; cases h; rfl
     right_inv := by intro x; rfl }
 have hc : Fintype.card {p : X×X // p.1 = p.2} = Fintype.card X :=
   Fintype.card_congr e
 have hcomp := Fintype.card_subtype_compl (α:=X×X) (fun p : X×X => p.1 = p.2)
 -- desired card filter = subtype ¬eq
 rw [Fintype.card_prod, hc] at hcomp
 calc
  _ = Fintype.card {p : X×X // ¬ p.1 = p.2} := by
    symm
    apply Fintype.card_of_subtype
    intro x
    simp
  _ = _ := by simpa [Nat.mul_sub_left_distrib] using hcomp
private lemma card_neone {G:Type*}[Group G][Fintype G] [DecidableEq G] :
 (Finset.univ.filter (fun y:G => y ≠ 1)).card = Fintype.card G -1 := by
 have he : Fintype.card {y:G // y=1} = 1 := by simp
 have h := Fintype.card_subtype_compl (α:=G) (fun y:G => y=1)
 rw [he] at h
 calc _ = Fintype.card {y:G // ¬ y=1} := by
          symm
          apply Fintype.card_of_subtype
          intro x
          simp
      _ = _ := h

private lemma bf_fiber_bound {G:Type*}[Group G][Finite G] {t:G}
 (ht : t⁻¹=t) (hn : 1 < Nat.card {x:G // x ∈ MulAction.orbit (ConjAct G) t}) :
 ∃ y : G, y ≠ 1 ∧
  (Nat.card {x:G // x ∈ MulAction.orbit (ConjAct G) t}) *
    (Nat.card {x:G // x ∈ MulAction.orbit (ConjAct G) t} - 1)
  ≤ (Nat.card G - 1) * Nat.card (Subgroup.centralizer ({y}:Set G)) := by
 classical
 letI : Fintype G := Fintype.ofFinite G
 let X := {x:G // x ∈ MulAction.orbit (ConjAct G) t}
 letI : Fintype X := Fintype.ofFinite X
 let s : Finset (X×X) := Finset.univ.filter (fun p => p.1 ≠ p.2)
 let T : Finset G := Finset.univ.filter (fun y => y ≠ 1)
 let f : X×X → G := fun p => (p.1:G)*(p.2:G)
 have maps : Set.MapsTo f (s:Set (X×X)) (T:Set G) := by
   intro p hp
   have hne : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
   have hmul : f p ≠ 1 := by
     intro he
     have hvals : (p.1:G) = (p.2:G) := by
       have hi : (p.1:G)⁻¹ = (p.1:G) := inv_orbit ht p.1
       -- from av*b=1 b=...
       have hb : (p.2:G) = (p.1:G)⁻¹ := eq_inv_of_mul_eq_one_right he
       -- check orientation
       simpa [hi] using hb.symm --?
     exact hne (Subtype.ext hvals)
   exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmul⟩
 -- T nonempty follows s nonempty? at least maybe t=1 then s empty; require y≠1 existence not. derive from ?
 -- actually if G trivial fails, assume existence of distinct class.
 have Tnon : T.Nonempty := by
   have nle : Fintype.card X ≤ Fintype.card G := Fintype.card_subtype_le _
   have ngo : 1 < Fintype.card G := lt_of_lt_of_le (by simpa [X, Nat.card_eq_fintype_card] using hn) nle
   haveI : Nontrivial G := Fintype.one_lt_card_iff_nontrivial.mp ngo
   obtain ⟨g, g', hg⟩ := exists_pair_ne G
   -- choose one nonone
   by_cases h1 : g = 1
   · refine ⟨g', Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
     intro e
     exact hg (h1.trans e.symm)
   · exact ⟨g, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩⟩
 have hT : T.Nonempty := Tnon

 obtain ⟨y, hyT, hymax⟩ := Finset.exists_max_image T
     (fun y => (s.filter (fun p => f p = y)).card) hT
 refine ⟨y, (Finset.mem_filter.mp hyT).2, ?_⟩
 have sumid := Finset.card_eq_sum_card_fiberwise maps
 have hsum : (∑ z ∈ T, (s.filter (fun p => f p = z)).card) ≤
     T.card * (s.filter (fun p => f p = y)).card := by
   have h := Finset.sum_le_card_nsmul T
     (fun z => (s.filter (fun p => f p = z)).card)
     ((s.filter (fun p => f p = y)).card)
     (by intro z hz; exact hymax z hz)
   simpa [nsmul_eq_mul, Nat.mul_comm] using h
 have hsc : s.card ≤ T.card * (s.filter (fun p => f p = y)).card := by
   rw [sumid]
   exact hsum
 -- inject filtration into centralizer
 -- define injection a0^-1*a
 have hyfiber : (s.filter (fun p => f p = y)).card ≤
     Nat.card (Subgroup.centralizer ({y}:Set G)) := by
   -- if empty trivial, otherwise choose p0
   classical
   by_cases hE : (s.filter (fun p => f p = y)).Nonempty
   · obtain ⟨p0, hp0⟩ := hE
     have h0 : f p0 = y := (Finset.mem_filter.mp hp0).2
     -- construct injection to centralizer using first coordinates
     let phi : {p // p ∈ s.filter (fun p => f p = y)} →
         Subgroup.centralizer ({y}:Set G) := fun p => ⟨((p0.1:G)⁻¹ * (p.val.1:G)), by
           -- commute y using inversions
           rw [Subgroup.mem_centralizer_singleton_iff]
           have h := (Finset.mem_filter.mp p.property).2
           -- both a invert y: since product=y and involutions
           have invp : (p.val.1:G)⁻¹ = (p.val.1:G) := inv_orbit ht p.val.1
           have invp2 : (p.val.2:G)⁻¹ = (p.val.2:G) := inv_orbit ht p.val.2
           have inv0 : (p0.1:G)⁻¹ = (p0.1:G) := inv_orbit ht p0.1
           have inv02 : (p0.2:G)⁻¹ = (p0.2:G) := inv_orbit ht p0.2
           -- derive a*y = y^-1*a for p etc maybe use y = a*b, a invol -> a*y = b ; y^-1*a = b
           -- use group calc by substitutions h h0
           -- target a0^-1*a*y = y*a0^-1*a
           -- expression with a,b; using self inverse and equality y products? wait both substitutions produce different rhs positions consistently: h:f p=y, h0:f p0=y; rw both fails
           change (p0.1:G)⁻¹ * (p.val.1:G) * y = y * ((p0.1:G)⁻¹ * (p.val.1:G))
           -- use substitutions
           have h0' : (p0.1:G)*(p0.2:G) = y := h0
           have h' : (p.val.1:G)*(p.val.2:G) = y := h
           -- group simplify after substituting y on lhs by h' and rhs by h0'
           have aa : (p.val.1:G)*(p.val.1:G)=1 := by
             conv_lhs => lhs; rw [← invp]
             simp
           have eql : (p.val.2:G) = (p0.2:G)*(p0.1:G)*(p.val.1:G) := by
             calc
              (p.val.2:G) = ((p.val.1:G)*(p.val.2:G))⁻¹ * (p.val.1:G) := by simp [invp, invp2, aa, mul_assoc]
              _ = ((p0.1:G)*(p0.2:G))⁻¹ * (p.val.1:G) := by rw [h', h0']
              _ = _ := by simp [inv0, inv02, mul_assoc]
           calc
            (p0.1:G)⁻¹ * (p.val.1:G) * y = (p0.1:G)⁻¹ * (p.val.1:G) * ((p.val.1:G)*(p.val.2:G)) := congrArg _ h'.symm
            _ = (p0.1:G) * (p.val.2:G) := by
              rw [inv0]
              -- reassociate the two equal involutions
              calc
               (p0.1:G) * (p.val.1:G) * ((p.val.1:G)*(p.val.2:G)) =
                 (p0.1:G) * ((p.val.1:G)*(p.val.1:G)) * (p.val.2:G) := by simp [mul_assoc]
               _ = _ := by rw [aa]; simp
            _ = ((p0.1:G)*(p0.2:G)) * ((p0.1:G)⁻¹ * (p.val.1:G)) := by rw [eql]; simp [inv0, mul_assoc]
            _ = y * ((p0.1:G)⁻¹ * (p.val.1:G)) := by rw [h0']

         ⟩
     have phi_inj : Function.Injective phi := by
       intro p q hh
       -- equality in subgroup gives first values equal, products fix second
       apply Subtype.ext
       -- equality pairs
       cases p with | mk p hp => ?_
       cases q with | mk q hq => ?_
       dsimp [phi] at hh
       have hfirst : (p.1:G) = (q.1:G) := by
         -- cancel a0^-1
         exact mul_left_cancel (congrArg Subtype.val hh)
       have hpv : f p = y := (Finset.mem_filter.mp hp).2
       have hqv : f q = y := (Finset.mem_filter.mp hq).2
       cases p with | mk p1 p2 => ?_
       cases q with | mk q1 q2 => ?_
       dsimp [f] at hpv hqv hfirst ⊢
       -- subtype vals
       have firsteq : p1 = q1 := Subtype.ext hfirst
       subst q1
       have secondeq : p2 = q2 := by
         apply Subtype.ext
         exact mul_left_cancel (hpv.trans hqv.symm)
       subst q2
       rfl
     have le := Nat.card_le_card_of_injective phi phi_inj
     -- card subtype finset
     -- translate finite filtered subtype
     calc
      (s.filter (fun p => f p = y)).card = Fintype.card {p // p ∈ s.filter (fun p => f p = y)} := by symm; exact Fintype.card_coe _
      _ ≤ _ := by simpa [Nat.card_eq_fintype_card] using le
   · have hz : (s.filter (fun p => f p = y)).card = 0 := Finset.not_nonempty_iff_eq_empty.mp hE ▸ rfl
     simp [hz]
 have small := hsc.trans (Nat.mul_le_mul_left T.card hyfiber)
 refine ?_ 
 -- the two filtered univ cards
 have sc : s.card = Fintype.card X * (Fintype.card X - 1) := card_neqpairs X
 have tc : T.card = Fintype.card G - 1 := card_neone
 simpa [sc, tc, X, Nat.card_eq_fintype_card] using small

/-ResultProofDefinitionsEnd-/


theorem brauer_fowler :
    ∃ f : ℕ → ℕ, ∀ (G : Type) [Group G] [Finite G],
      IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
      ∀ t : G, orderOf t = 2 →
        Nat.card G ≤ f (Nat.card (Subgroup.centralizer ({t} : Set G))) :=  by
  classical
  refine ⟨fun c => (2*c^2).factorial, ?_⟩
  intro G _ _ hs hnab
  letI : IsSimpleGroup G := hs
  intro t ht
  let C : Subgroup G := Subgroup.centralizer ({t}:Set G)
  let c := Nat.card C
  let X := {x:G // x ∈ MulAction.orbit (ConjAct G) t}
  let n := Nat.card X
  have centertriv : Subgroup.center G = ⊥ := by
    have nt : Subgroup.center G ≠ ⊤ := by
      intro h
      obtain ⟨a,b,hh⟩ := hnab
      exact hh ((isMulCommutative_iff.mp (Subgroup.center_eq_top_iff.mp h)) a b)
    rcases (show (Subgroup.center G).Normal from inferInstance).eq_bot_or_eq_top with h|h
    · exact h
    · exact False.elim (nt h)
  have proper_any {y:G} (hy:y≠1) : Subgroup.centralizer ({y}:Set G) ≠ ⊤ := by
    intro htop
    have hsub := Subgroup.centralizer_eq_top_iff_subset.mp htop
    have mem : y ∈ Subgroup.center G := hsub (by simp)
    have : y = (1:G) := Subgroup.mem_bot.mp (by simpa [centertriv] using mem)
    exact hy this
  have Cproper : C ≠ ⊤ := by dsimp [C]; exact bf_centralizer_proper hnab t ht
  have idx : n = C.index := by
    have pos : 0 < c := Nat.card_pos
    have h1 : n * c = Nat.card G := orbit_card t
    have h2 : C.index * c = Nat.card G := Subgroup.index_mul_card C
    exact (Nat.eq_of_mul_eq_mul_right (by omega : 0 < c) (h1.trans h2.symm))
  have ng : 1 < n := by
    have z : 0 < C.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    have ne : C.index ≠ 1 := fun h => Cproper (Subgroup.index_eq_one.mp h)
    omega
  have invt : t⁻¹=t := by
    have hp := pow_orderOf_eq_one t
    rw [ht] at hp
    exact inv_eq_of_mul_eq_one_left (by simpa [pow_two] using hp)
  obtain ⟨y, hy, hbound⟩ := bf_fiber_bound invt (by
    change 1 < Nat.card {x:G // x ∈ MulAction.orbit (ConjAct G) t} at ng
    exact ng)
  let H : Subgroup G := Subgroup.centralizer ({y}:Set G)
  have Hp : H ≠ ⊤ := proper_any hy
  have posc : 0 < c := Nat.card_pos
  let d := Nat.card H
  have posd : 0 < d := Nat.card_pos
  have ncard : n*c = Nat.card G := orbit_card t
  have hHcard : H.index * d = Nat.card G := Subgroup.index_mul_card H
  have ar : H.index ≤ 2*c^2 := by
    -- Only numerical arithmetic remains.  Write the fibre estimate with the
    -- abbreviations `n,c,d` above.
    have hb0 : n * (n - 1) ≤ (Nat.card G - 1) * d := by
      change n * (n - 1) ≤ (Nat.card G - 1) * d at hbound
      exact hbound
    have hb : n * (n - 1) ≤ (n * c - 1) * d := by
      have hh := hb0
      rw [← ncard] at hh
      exact hh
    have hnpos : 0 < n := lt_trans Nat.zero_lt_one ng
    have hn1 : 1 ≤ n := Nat.le_of_lt ng
    have hweak : n * (n - 1) ≤ n * (c * d) := by
      have hle : (n * c - 1) * d ≤ (n * c) * d :=
        Nat.mul_le_mul_right d (Nat.sub_le _ _)
      have h' := le_trans hb hle
      simpa [Nat.mul_assoc] using h'
    have hnminus : n - 1 ≤ c * d :=
      Nat.le_of_mul_le_mul_left hweak hnpos
    have hncd1 : n ≤ c * d + 1 := by
      have hadd : (n - 1) + 1 ≤ c * d + 1 :=
        Nat.add_le_add_right hnminus 1
      simpa [Nat.sub_add_cancel hn1] using hadd
    have hcdpos : 0 < c * d := Nat.mul_pos posc posd
    have htwice : c * d + 1 ≤ 2 * (c * d) := by
      omega
    have hncd : n ≤ 2 * (c * d) := le_trans hncd1 htwice
    have hnc : n * c ≤ (2 * c^2) * d := by
      have hm := Nat.mul_le_mul_right c hncd
      -- just reassociate the commutative products
      simpa [pow_two, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hm
    have hkd : H.index * d ≤ (2 * c^2) * d := by
      calc
        H.index * d = Nat.card G := hHcard
        _ = n * c := ncard.symm
        _ ≤ (2 * c^2) * d := hnc
    exact Nat.le_of_mul_le_mul_right hkd posd
  have fac := bf_card_le_factorial_index H Hp
  exact fac.trans (Nat.factorial_le ar)


end Submission
