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
open VExpr Typing PR

section
variable {env : Typing} [E : ObjEnv env] {T : Tables} {f : PR} {d : Nat}

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
variable {env : Typing} [E : ObjEnv env] {T : Tables} {f : PR} {d : Nat} {q : Nat → PR}
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
        (negTy (bigOrTy (env := natEnv) (Γ := []) (props_map fun _ => SsTy _))).closedN.1
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
theorem reach_lim (hdne : Thm env [] dneS) (a : Nat) (ha : a ≤ K.N) :
    Thm env [] (imp (Pa f d a) (bigOr ((a :: K.succL a).map (Ss f d)))) := by
  have hG : env.HasType [] (bigOr ((a :: K.succL a).map (Ss f d))) (.sort .zero) := by otype
  have IH : ∀ b ∈ K.succL a, Thm env [] (imp (Pa f d b) (bigOr ((b :: K.succL b).map (Ss f d)))) :=
    fun b hb => reach_lim hdne b (K.le ((K.mem_succL).1 hb)).2
  refine Thm.intro (PaTy a) ?_
  rw [(hG.closedN.1).lift_eq]
  have hP : Thm env [Pa f d a] (Pa f d a) := (Thm.hyp .zero).cast Pa_liftN
  refine (imp_dne hG hdne).weak0.mp ?_
  refine Thm.intro (negTy (closedTy hG)) ?_
  have hnG : Thm env [neg (bigOr ((a :: K.succL a).map (Ss f d))), Pa f d a]
      (neg (bigOr ((a :: K.succL a).map (Ss f d)))) :=
    (Thm.hyp .zero).cast (negTy hG |>.closedN.1).lift_eq
  show Thm env _ falseS
  have hSt : Thm env [neg (bigOr ((a :: K.succL a).map (Ss f d))), Pa f d a] (Stay f d a) := by
    unfold Stay
    refine Thm.allI (Thm.intro (by otype) ?_)
    have hk : Thm env [hT f d (.bvar 0) =ₒ lit a, nat, neg (bigOr ((a :: K.succL a).map (Ss f d))),
        Pa f d a] (hT f d (.bvar 1) =ₒ lit a) := (Thm.hyp .zero).cast (by simp only [obj_simp])
    have hn := (Thm.weakL [hT f d (.bvar 0) =ₒ lit a, nat] hnG).cast
      ((negTy hG).closedN.1 |>.liftN_eq (Nat.zero_le _))
    have := stay_core hq hs ha (by otype) hk hn IH
    simpa only [obj_simp] using this
  have hP' : Thm env [neg (bigOr ((a :: K.succL a).map (Ss f d))), Pa f d a] (Pa f d a) :=
    hP.weak.cast Pa_liftN
  have hS : Thm env [neg (bigOr ((a :: K.succL a).map (Ss f d))), Pa f d a] (Ss f d a) :=
    Thm.conjI (by otype) (by otype) hP' hSt
  exact hnG.mp (bigOr_intro (props_map fun _ => by otype) (List.mem_map_of_mem (.head _)) hS)
termination_by (K.succL a).length
decreasing_by exact succL_lt hb

omit hq hs in
/-- **Internal Σ₁-completeness for `Pa`**: a code `σ` turns, provably, every `k` at which the walk
is at `i` into a certificate `σ k` of `Pa i`. -/
theorem sigma_Pa (hTb : TablesFor env.env T) (i : Nat) :
    ∃ σ : PR, Thm env [] (∀ₒ k, ev (eqz f (num i)) [k, lit d] =ₒ zero →ₒ
      prfT T (numT (encExpr (Pa f d i))) (ev σ [k]) =ₒ zero) := by
  have hR : (ex (app2 (fn f) (.bvar 2) (.bvar 0) =ₒ lit i)).inst (lit d) 1 = Pa f d i := by
    simp only [Pa, Obj.hT, obj_simp]
  have hG : Thm env [] (allN 2 (imp ((valF (eqz f (num i)) 2).inst zero 0)
      (ex (app2 (fn f) (.bvar 2) (.bvar 0) =ₒ lit i)))) := by
    rw [valF_fin_eq]
    refine allN_intro (env := env) 2 (Γ := []) ?_
    simp only [List.replicate]
    ointro h
    have h' := (ev_eqz_zero (p := f) (q := num i) (by otype)).mp h
    oexists .bvar 1
    orw [fn_ev]
    simpa only [obj_simp] using h'
  obtain ⟨z, hz⟩ := closed_cert hTb (E.hasNat.zeroT (U := 0) (Γ := []))
  obtain ⟨s, hs⟩ := closed_cert hTb (E.hasNat.succT (U := 0) (Γ := []))
  have hz1 := (hz (env := env) (Γ := [])).1
  have hz2 := (hz (env := env) (Γ := [])).2
  have hs1 := (hs (env := env) (Γ := [])).1
  have hs2 := (hs (env := env) (Γ := [])).2
  obtain ⟨τ, hτ⟩ := ok_exists hz1 hz2 hs1 hs2 hTb (eqz f (num i)) 2
  obtain ⟨c, hc⟩ := closed_prf hTb hG
  refine ⟨mpP (instC z s c [num d, var 0]) (.push (num d) (ren swap01 τ)), ?_⟩
  ointro
  ointro h
  have hk : Tm env [ev (eqz f (num i)) [.bvar 0, lit d] =ₒ zero, nat] (.bvar 1) := by otype
  exact prf_fin hz1 hz2 hs1 hs2 hτ hR (Pa_closed i) hc hk h

omit hq hs in
/-- A step at which the walk is at `i` proves that it reaches `i`, provably. -/
theorem prov_Pa (hTb : TablesFor env.env T) {Γ : List VExpr} {i : Nat} {k : VExpr}
    (hk : Tm env Γ k) (h : Thm env Γ (hT f d k =ₒ lit i)) : Thm env Γ (Prov T (Pa f d i)) := by
  obtain ⟨σ, hσ⟩ := sigma_Pa (f := f) (d := d) hTb i
  have hl : Tms env Γ [k, lit d] := by otype
  have e1 : Thm env Γ (ev f [k, lit d] =ₒ ev (num i) [k, lit d]) := by
    simp only [obj_simp]
    unfold hT at h
    exact Thm.trans (by otype) (by otype) (by otype) (Thm.symm (by otype) (by otype)
      (fn_ev (litTy d) hk)) h
  have hs := Thm.allE (hσ.weak0 (Γ := Γ)) hk
  onorm at hs
  exact prov_intro (by otype) (hs.mp (ev_eqz_of_eq hl e1))

include hq hs h0 in
/-- Entering `i` at `k + 1` from elsewhere is reading a proof of `¬S_i`. -/
theorem prov_neg_core {Γ : List VExpr} {i : Nat} {k : VExpr} (hk : Tm env Γ k)
    (hk1 : Thm env Γ (¬ₒ (hT f d k =ₒ lit i))) (hk2 : Thm env Γ (hT f d (S k) =ₒ lit i)) :
    Thm env Γ (Prov T (neg (Ss f d i))) := by
  refine bigOr_elim (by otype) (props_map fun _ => by otype) (range hq hs h0 hk)
    fun p hp kp => ?_
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hp
  onorm at kp ⊢
  have hk1' := hk1.weak (A := hT f d k =ₒ lit a)
  have hk2' := hk2.weak (A := hT f d k =ₒ lit a)
  onorm at hk1' hk2'
  by_cases hai : a = i
  · subst hai
    exact Thm.exfalso (hk1'.mp kp) (by otype)
  refine bigOr_elim (by otype) (props_cons (by otype) (props_map fun _ => by otype))
    (step hq hs ((K.mem_worlds).1 ha) (by otype) kp) fun p' hp' kp' => ?_
  onorm at kp' ⊢
  have hk2'' := hk2'.weak (A := p')
  onorm at hk2''
  rcases List.mem_cons.1 hp' with rfl | hp'
  · onorm at kp'
    exact Thm.exfalso ((lit_ne hai).mp (Thm.trans (by otype) (by otype) (by otype)
      (Thm.symm (by otype) (by otype) kp') hk2'')) (by otype)
  · obtain ⟨b, -, rfl⟩ := List.mem_map.1 hp'
    onorm at kp'
    have e1 := Thm.conjE1 (by otype) (by otype) kp'
    have e2 := Thm.conjE2 (by otype) (by otype) kp'
    by_cases hbi : b = i
    · subst hbi
      unfold Qt at e2
      exact prov_intro (by otype) e2
    · exact Thm.exfalso ((lit_ne hbi).mp (Thm.trans (by otype) (by otype) (by otype)
        (Thm.symm (by otype) (by otype) e1) hk2'')) (by otype)

theorem bigOr_Ss_closed (bs : List Nat) : (bigOr (bs.map (Ss f d))).ClosedN :=
  (bigOrTy (env := natEnv) (Γ := []) (props_map fun _ => SsTy _)).closedN.1

include hq hs h0 in
/-- **`S_i → Prov(⋁_{i R j} S_j)` for `i ≠ 0`.** The walk entered `i` along a proof of `¬S_i`,
and it provably reaches `i`; and `Pa i ∧ ¬S_i → ⋁_{i R j} S_j` (`reach_lim`). -/
theorem Ss_prov (hTb : TablesFor env.env T) (hdne : Thm env [] dneS) {Γ : List VExpr} {i : Nat}
    (hi0 : i ≠ 0) (hiN : i ≤ K.N) (h : Thm env Γ (Ss f d i)) :
    Thm env Γ (Prov T (bigOr ((K.succL i).map (Ss f d)))) := by
  have hBc := bigOr_Ss_closed (f := f) (d := d) (K.succL i)
  have hB : env.HasType [] (bigOr ((K.succL i).map (Ss f d))) (.sort .zero) := by otype
  have hD := reach_lim hq hs hdne i hiN
  have hNB : (imp (neg (Ss f d i)) (bigOr ((K.succL i).map (Ss f d)))).ClosedN :=
    (impTy (negTy (SsTy (env := env) (Γ := []) i)) hB).closedN.1
  have hDimp : Thm env [] (imp (Pa f d i) (imp (neg (Ss f d i)) (bigOr ((K.succL i).map (Ss f d))))) := by
    refine Thm.intro (PaTy i) ?_
    rw [hNB.lift_eq]
    refine Thm.intro (negTy (SsTy i)) ?_
    rw [hBc.lift_eq]
    have hP : Thm env [neg (Ss f d i), Pa f d i] (Pa f d i) := (Thm.hyp (.succ .zero)).cast
      (by simp only [obj_simp])
    have hn : Thm env [neg (Ss f d i), Pa f d i] (neg (Ss f d i)) := (Thm.hyp .zero).cast
      (by simp only [obj_simp])
    refine bigOr_elim (closedTy hB) (props_map fun _ => by otype) (hD.weak0.mp hP)
      fun p hp kp => ?_
    rw [hBc.lift_eq]
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hp
    rcases List.mem_cons.1 hb with rfl | hb
    · exact Thm.exfalso (Thm.absurd (hn.weak.cast (by simp only [obj_simp]))
        (kp.cast Ss_liftN)) (by otype)
    · exact bigOr_intro (props_map fun _ => by otype) (List.mem_map_of_mem hb) (kp.cast Ss_liftN)
  have hP1 : Thm env [] (Prov T (imp (Pa f d i) (imp (neg (Ss f d i))
      (bigOr ((K.succL i).map (Ss f d)))))) :=
    Thm.nec hTb hDimp
  unfold Ss at h
  have hPa := Thm.conjE1 (by otype) (by otype) h
  unfold Pa at hPa
  refine Thm.exEHT (by otype) (by otype) hPa fun hmT hm => ?_
  onorm at hm ⊢
  have hPP := prov_Pa hTb hmT hm
  have hE := entry h0 hi0 hmT hm
  refine Thm.exEHT (by otype) (by otype) hE fun hkT hk => ?_
  onorm at hk ⊢
  have hk1 := Thm.conjE1 (by otype) (by otype) hk
  have hk2 := Thm.conjE2 (by otype) (by otype) hk
  have hPN := prov_neg_core hq hs h0 hkT hk1 hk2
  exact prov_mp_ctx hBc (prov_mp_ctx hNB hP1.weak0
    ((hPP.weak.weak).cast (by simp only [obj_simp]))) hPN

end

/-! ### Leaving a world -/

section
variable {env : Typing} [E : ObjEnv env] {f nx : PR} {d : Nat}
  (hs : ∀ {Γ : List VExpr} {k : VExpr}, Tm env Γ k →
    Thm env Γ (hT f d (S k) =ₒ ev nx [hT f d k, k, lit d]))
include hs

theorem lv_zero {Γ : List VExpr} {a : Nat} {k : VExpr} (hk : Tm env Γ k)
    (h1 : Thm env Γ (hT f d k =ₒ lit a)) (h2 : Thm env Γ (¬ₒ (hT f d (S k) =ₒ lit a))) :
    Thm env Γ (ev (lvC f nx a) [k, lit d] =ₒ zero) := by
  have hl : Tms env Γ [k, lit d] := by otype
  have e1 : Thm env Γ (ev f [k, lit d] =ₒ hT f d k) := by
    unfold hT; exact Thm.symm (by otype) (by otype) (fn_ev (litTy d) hk)
  have z1 : Thm env Γ (ev (eqz f (num a)) [k, lit d] =ₒ zero) :=
    ev_eqz_of_eq hl (by simp only [obj_simp]; exact Thm.trans (by otype) (by otype) (by otype) e1 h1)
  have r1 := ev_ifz_zero (f := lvC f nx a) rfl hl z1
  refine Thm.trans (by otype) (by otype) (by otype) r1 ?_
  refine Thm.disjEH (by otype) (by otype) (by otype) (ifz_cases (c := eqz (push f nx) (num a))
    (a := num 1) (b := .zero) hl) (fun c1 => ?_) (fun c2 => ?_)
  · onorm at c1 ⊢
    oexfalso
    ocases c1 with c11 c12
    have e := (ev_eqz_zero (p := push f nx) (q := num a) (by otype)).mp c12
    olift e1
    olift h2
    orw [ev_push (f := push f nx) rfl (by otype), e1, ← hs (by otype)] at e
    exact h2.mp (by simpa only [obj_simp] using e)
  · onorm at c2 ⊢
    exact Thm.conjE1 (by otype) (by otype) c2

/-- **Leaving `a`, as a halting sentence**: a refutation of `Stay a` proves that `lvC f nx a`
halts on `d`. -/
theorem halts_lv {a : Nat} (h : Thm env [] (neg (Stay f d a))) :
    Thm env [] (halts (lvC f nx a) d) := by
  show Thm env [] (imp (all (imp (isZero (app2 (fn (lvC f nx a)) (lit d) (.bvar 0))) falseS))
    falseS)
  ointro hn
  refine (h.weak0).mp ?_
  unfold Stay
  ointro
  ointro hk
  refine Thm.disjEH (by otype) (by otype) (by otype)
    (eq_or_ne (a := hT f d (S (.bvar 1))) (b := lit a) (by otype) (by otype)) (fun e => ?_)
    (fun n => ?_)
  · onorm at e ⊢; exact e
  · onorm at n ⊢
    oexfalso
    olift hn
    olift hk
    have hz := Thm.allE hn (t := .bvar 2) (by otype)
    onorm at hz
    refine hz.mp (isZero_of_eq_zero (by otype) ?_)
    orw [fn_ev (litTy d) (by otype)]
    exact lv_zero hs (by otype) hk n

end

end Incomplete.Obj
