import Incomplete.Obj.SolovayStep
import Incomplete.Modal.Kripke

/-!
# Solovay's lemmas

For a code `f` at an input `d` whose walk starts at `0` and steps by `nextC K q`, with tests `q`
reading the checks `Qt`, the theory proves, about the sentences `S_a`:

- the walk stays among the worlds (`range`);
- `S_i → ¬S_j` for `i ≠ j` (`Ss_disj`);
- `S_i → ¬Prov(¬S_j)` when `i R j` (`Ss_not_prov`);
- with double-negation elimination, `Pa a → ⋁_{b ∈ {a} ∪ R(a)} S_b` (`reach_lim`), by induction on
  the number of worlds `a` sees;
- for `i ≠ 0`, `S_i → Prov(⋁_{i R j} S_j)` (`Ss_prov`): the walk entered `i` along a proof of
  `¬S_i`, and it provably reaches `i`.

And from a refutation of `Stay a` a proof that `lvC f nx a` halts (`halts_lv`).
-/

namespace Incomplete.Obj
open Lean4Lean
open VExpr VEnv PR

section
variable {env : VEnv} [E : ObjEnv env] {T : Tables} {f : PR} {d : Nat}

/-- The walk stays at `a` from `m` on. -/
theorem stay_add {Γ : List VExpr} {a : Nat} {m l : VExpr} (hm : Tm env Γ m) (hl : Tm env Γ l)
    (hS : Thm env Γ (Stay f d a)) (h : Thm env Γ (hT f d m =ₒ lit a)) :
    Thm env Γ (hT f d (add m l) =ₒ lit a) := by
  have hall : Thm env Γ (all (hT f d (add m.lift (.bvar 0)) =ₒ lit a)) := by
    oind
    · orw [add_zero]; exact h
    · ointro ih
      orw [add_succ]
      have hS' := hS.weak (A := nat)
      olift hS'
      unfold Stay at hS'
      have := Thm.allE hS' (t := add m.lift.lift (.bvar 1)) (by otype)
      onorm at this
      exact this.mp ih
  have := Thm.allE hall hl
  onorm at this
  exact this

/-- From `S_a`, the walk is at `a` from some `m` on. -/
theorem Ss_from {Γ : List VExpr} {a : Nat} (h : Thm env Γ (Ss f d a)) :
    Thm env Γ (∃ₒ m, ∀ₒ l, hT f d (add m l) =ₒ lit a) := by
  unfold Ss at h
  have hP := Thm.conjE1 (by otype) (by otype) h
  have hS := Thm.conjE2 (by otype) (by otype) h
  unfold Pa at hP
  ocases hP with hm
  olift hS
  oexists .bvar 1
  ointro
  have hS' := hS.weak (A := nat)
  have hm' := hm.weak (A := nat)
  onorm at hS' hm'
  exact stay_add (by otype) (by otype) hS' hm'

/-- **Disjointness**: `S_i ∧ S_j → ⊥` for `i ≠ j`. -/
theorem Ss_disj {Γ : List VExpr} {i j : Nat} (hij : i ≠ j) (hi : Thm env Γ (Ss f d i))
    (hj : Thm env Γ (Ss f d j)) : Thm env Γ falseS := by
  have hi := Ss_from hi
  have hj := Ss_from hj
  ocases hi with h1
  olift hj
  ocases hj with h2
  olift h1
  have e1 := Thm.allE h1 (t := .bvar 1) (by otype)
  have e2 := Thm.allE h2 (t := .bvar 3) (by otype)
  onorm at e1 e2
  orw [add_comm] at e2
  exact (lit_ne hij).mp (Thm.trans (by otype) (by otype) (by otype)
    (Thm.symm (by otype) (by otype) e1) e2)

end

section
variable {env : VEnv} [E : ObjEnv env] {T : Tables} {f : PR} {d : Nat} {q : Nat → PR}
  {K : SFrame}
  (hq : ∀ {Γ : List VExpr} (b : Nat) {r k : VExpr}, Tm env Γ r → Tm env Γ k →
    Thm env Γ (ev (q b) [r, k, lit d] =ₒ Qt f d T b k))
  (hs : ∀ {Γ : List VExpr} {k : VExpr}, Tm env Γ k →
    Thm env Γ (hT f d (S k) =ₒ ev (nextC K q) [hT f d k, k, lit d]))
  (h0 : ∀ {Γ : List VExpr}, Thm env Γ (hT f d zero =ₒ zero))

include hq hs in
/-- From `h k = a`, the walk at `k + 1` is a world. -/
theorem range_step {Γ : List VExpr} {a : Nat} {k : VExpr} (ha : a ≤ K.N) (hk : Tm env Γ k)
    (h : Thm env Γ (hT f d k =ₒ lit a)) :
    Thm env Γ (bigOr (K.worlds.map fun b => hT f d (S k) =ₒ lit b)) := by
  refine bigOr_elim (bigOrTy (props_map fun _ => by otype))
    (props_cons (by otype) (props_map fun _ => by otype)) (step hq hs ha hk h) fun p hp kp => ?_
  have hW : Props env (p :: Γ) (K.worlds.map fun b => hT f d (S k.lift) =ₒ lit b) :=
    props_map fun _ => by otype
  simp only [obj_simp, List.map_map, Function.comp_def]
  rcases List.mem_cons.1 hp with rfl | hp
  · onorm at kp
    exact bigOr_intro hW (List.mem_map_of_mem ((K.mem_worlds).2 ha)) kp
  · obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hp
    onorm at kp
    have := Thm.conjE1 (by otype) (by otype) kp
    exact bigOr_intro hW (List.mem_map_of_mem ((K.mem_worlds).2 (K.le ((K.mem_succL).1 hb)).2)) this

include hq hs h0 in
/-- **The walk stays among the worlds.** -/
theorem range {Γ : List VExpr} {k : VExpr} (hk : Tm env Γ k) :
    Thm env Γ (bigOr (K.worlds.map fun a => hT f d k =ₒ lit a)) := by
  have hall : Thm env [] (all (bigOr (K.worlds.map fun a => hT f d (.bvar 0) =ₒ lit a))) := by
    refine Thm.ind (bigOrTy (props_map fun _ => by otype)) ?_ ?_
    · simp only [obj_simp, List.map_map, Function.comp_def]
      exact bigOr_intro (props_map fun _ => by otype)
        (List.mem_map_of_mem ((K.mem_worlds).2 (Nat.zero_le _))) h0
    · ointro ih
      simp only [obj_simp, List.map_map, Function.comp_def] at ih ⊢
      refine bigOr_elim (bigOrTy (props_map fun _ => by otype)) (props_map fun _ => by otype) ih
        fun p hp kp => ?_
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hp
      onorm at kp
      have := range_step hq hs ((K.mem_worlds).1 ha) (by otype) kp
      simpa only [obj_simp, List.map_map, Function.comp_def] using this
  have := Thm.allE (hall.weak0 (Γ := Γ)) hk
  simpa only [obj_simp, List.map_map, Function.comp_def] using this

include h0 in
/-- **Entering a world**: if the walk is at `i ≠ 0` at `m`, it moved into `i` at some `k`. -/
theorem entry {Γ : List VExpr} {i : Nat} {m : VExpr} (hi : i ≠ 0) (hm : Tm env Γ m)
    (h : Thm env Γ (hT f d m =ₒ lit i)) :
    Thm env Γ (∃ₒ k, ¬ₒ (hT f d k =ₒ lit i) ∧ₒ hT f d (S k) =ₒ lit i) := by
  have hall : Thm env [] (all (imp (hT f d (.bvar 0) =ₒ lit i)
      (∃ₒ k, ¬ₒ (hT f d k =ₒ lit i) ∧ₒ hT f d (S k) =ₒ lit i))) := by
    oind
    · ointro h1
      oexfalso
      exact (lit_ne (Ne.symm hi)).mp (Thm.trans (by otype) (by otype) (by otype)
        (Thm.symm (by otype) (by otype) h0) h1)
    · ointro ih
      ointro h1
      refine Thm.disjEH (by otype) (by otype) (by otype)
        (eq_or_ne (a := hT f d (.bvar 2)) (b := lit i) (by otype) (by otype)) (fun e => ?_)
        (fun n => ?_)
      · onorm at e ⊢
        olift ih
        exact ih.mp e
      · onorm at n ⊢
        oexists .bvar 3
        osplit
        · exact n
        · olift h1; exact h1
  have := Thm.allE (hall.weak0 (Γ := Γ)) hm
  onorm at this
  exact this.mp h

include hq hs in
theorem not_prov_core {Γ : List VExpr} {i j : Nat} {p m : VExpr} (hij : K.R i j = true)
    (hp : Tm env Γ p) (hm : Tm env Γ m) (hS : Thm env Γ (Stay f d i))
    (hmi : Thm env Γ (hT f d m =ₒ lit i))
    (hc : Thm env Γ (prfT T (numT (encExpr (neg (Ss f d j)))) p =ₒ zero)) : Thm env Γ falseS := by
  have e0 := stay_add (m := m) (l := tri (add p m)) hm (by otype) hS hmi
  have e1 : Thm env Γ (hT f d (pair p m) =ₒ lit i) := by
    orw [pair_eq, add_comm]; exact e0
  have e2 : Thm env Γ (Qt f d T j (pair p m) =ₒ zero) := by
    unfold Qt; orw [fst_pair]; exact hc
  have hne := step_ne hq hs (K.le hij).1 ((K.mem_succL).2 hij) (by otype) e1 e2
  unfold Stay at hS
  have hst := Thm.allE hS (t := pair p m) (by otype)
  onorm at hst
  exact hne.mp (hst.mp e1)

include hq hs in
/-- **`S_i → ¬Prov(¬S_j)` for `i R j`.** From `m` on the walk is at `i`; a proof `p` of `¬S_j` is
read at the step `pair p m`, which moves the walk off `i`. -/
theorem Ss_not_prov {Γ : List VExpr} {i j : Nat} (hij : K.R i j = true)
    (hi : Thm env Γ (Ss f d i)) (hp : Thm env Γ (Prov T (neg (Ss f d j)))) :
    Thm env Γ falseS := by
  unfold Ss at hi
  have hP := Thm.conjE1 (by otype) (by otype) hi
  have hS := Thm.conjE2 (by otype) (by otype) hi
  unfold Pa at hP
  unfold Prov at hp
  ocases hP with hm
  olift hp
  olift hS
  ocases hp with hc
  olift hm
  olift hS
  exact not_prov_core hq hs hij (by otype) (by otype) hS hm hc

omit [ObjEnv env] in
theorem succL_lt {a b : Nat} (hb : b ∈ K.succL a) : (K.succL b).length < (K.succL a).length := by
  have hab := (K.mem_succL).1 hb
  simp only [SFrame.succL, ← List.countP_eq_length_filter]
  refine Modal.FinModel.countP_lt (fun x _ hx => K.trans hab hx) ⟨b, ?_, hab, ?_⟩
  · exact (K.mem_worlds).2 (K.le hab).2
  · rw [K.irrefl]; exact Bool.false_ne_true

include hq hs in
theorem stay_core {Γ : List VExpr} {a : Nat} {k : VExpr} (ha : a ≤ K.N) (hk : Tm env Γ k)
    (hka : Thm env Γ (hT f d k =ₒ lit a))
    (hnG : Thm env Γ (neg (bigOr ((a :: K.succL a).map (Ss f d)))))
    (IH : ∀ b ∈ K.succL a, Thm env [] (imp (Pa f d b) (bigOr ((b :: K.succL b).map (Ss f d))))) :
    Thm env Γ (hT f d (S k) =ₒ lit a) := by
  refine bigOr_elim (by otype) (props_cons (by otype) (props_map fun _ => by otype))
    (step hq hs ha hk hka) fun p hp kp => ?_
  rcases List.mem_cons.1 hp with rfl | hp
  · onorm at kp ⊢; exact kp
  · obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hp
    onorm at kp ⊢
    have e := Thm.conjE1 (by otype) (by otype) kp
    have hPb : Thm env (((hT f d (S k) =ₒ lit b) ∧ₒ (Qt f d T b k =ₒ zero)) :: Γ) (Pa f d b) := by
      unfold Pa; oexists S k.lift; exact e
    have g := (IH b hb).weak0.mp hPb
    have g' := bigOr_mono (qs := (a :: K.succL a).map (Ss f d)) (props_map fun _ => by otype)
      (props_map fun _ => by otype) ?_ g
    · oexfalso
      have hc : (neg (bigOr ((a :: K.succL a).map (Ss f d)))).ClosedN :=
        (negTy (bigOrTy (env := natEnv) (Γ := []) (props_map fun _ => SsTy _))).closedN
          natEnv_ordered trivial
      have hn := (hnG.weak (A := (hT f d (S k) =ₒ lit b) ∧ₒ (Qt f d T b k =ₒ zero))).cast hc.lift_eq
      exact hn.mp g'
    · intro r hr
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hr
      refine List.mem_map_of_mem (List.mem_cons_of_mem _ ?_)
      rcases List.mem_cons.1 hc with rfl | hc
      · exact hb
      · exact (K.mem_succL).2 (K.trans ((K.mem_succL).1 hb) ((K.mem_succL).1 hc))

include hq hs in
/-- **The walk has a limit above every world it reaches**, given double-negation elimination:
`Pa a → ⋁_{b ∈ {a} ∪ R(a)} S_b`. -/
theorem reach_lim (hdne : Provable env dneS) (a : Nat) (ha : a ≤ K.N) :
    Thm env [] (imp (Pa f d a) (bigOr ((a :: K.succL a).map (Ss f d)))) := by
  have hG : env.HasType 0 [] (bigOr ((a :: K.succL a).map (Ss f d))) (.sort .zero) := by otype
  have IH : ∀ b ∈ K.succL a, Thm env [] (imp (Pa f d b) (bigOr ((b :: K.succL b).map (Ss f d)))) :=
    fun b hb => reach_lim hdne b (K.le ((K.mem_succL).1 hb)).2
  refine Thm.intro (PaTy a) ?_
  rw [(hG.closedN E.ordered trivial).lift_eq]
  have hP : Thm env [Pa f d a] (Pa f d a) := (Thm.hyp .zero).cast Pa_liftN
  refine (imp_dne hG hdne).weak0.mp ?_
  refine Thm.intro (negTy (closedTy hG)) ?_
  have hnG : Thm env [neg (bigOr ((a :: K.succL a).map (Ss f d))), Pa f d a]
      (neg (bigOr ((a :: K.succL a).map (Ss f d)))) :=
    (Thm.hyp .zero).cast (negTy hG |>.closedN E.ordered trivial).lift_eq
  show Thm env _ falseS
  have hSt : Thm env [neg (bigOr ((a :: K.succL a).map (Ss f d))), Pa f d a] (Stay f d a) := by
    unfold Stay
    refine Thm.allI (Thm.intro (by otype) ?_)
    have hk : Thm env [hT f d (.bvar 0) =ₒ lit a, nat, neg (bigOr ((a :: K.succL a).map (Ss f d))),
        Pa f d a] (hT f d (.bvar 1) =ₒ lit a) := (Thm.hyp .zero).cast (by simp only [obj_simp])
    have hn := (Thm.weakL [hT f d (.bvar 0) =ₒ lit a, nat] hnG).cast
      ((negTy hG).closedN E.ordered trivial |>.liftN_eq (Nat.zero_le _))
    have := stay_core hq hs ha (by otype) hk hn IH
    simpa only [obj_simp] using this
  have hP' : Thm env [neg (bigOr ((a :: K.succL a).map (Ss f d))), Pa f d a] (Pa f d a) :=
    hP.weak.cast Pa_liftN
  have hS : Thm env [neg (bigOr ((a :: K.succL a).map (Ss f d))), Pa f d a] (Ss f d a) :=
    Thm.conjI (by otype) (by otype) hP' hSt
  exact hnG.mp (bigOr_intro (props_map fun _ => by otype) (List.mem_map_of_mem (.head _)) hS)
termination_by (K.succL a).length
decreasing_by exact succL_lt hb

end

end Incomplete.Obj
