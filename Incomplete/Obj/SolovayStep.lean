import Incomplete.Obj.SolovayCode

/-!
# The walk, internally

For a code `f` at an input `d`, `hT f d k` is its value at `k` as an object term, and `Ss f d a`
the sentence `S_a`: the walk reaches `a` (`Pa`) and never leaves it (`Stay`); `bigOr` is finite
disjunction. For a walk stepping by `nextC K q` whose tests `q b` read the checks `Qt b` of `¬S_b`
at the first component of the step, the theory reads the step at each world: from `h k = a` the
walk stays at `a` at `k + 1` or moves to a world `b` that `a` sees with `Qt b k = 0` (`step`); and
`Qt b k = 0` makes it leave `a` (`step_ne`). Solovay's machine is such a walk at its own code
(`hM_zero`, `hM_succ`, `hM_test`).
-/

namespace Incomplete.Obj
open Lean4Lean
open VExpr Typing PR

/-! ### Finite disjunctions -/

/-- `p₁ ∨ … ∨ pₙ ∨ ⊥`. -/
def bigOr : List VExpr → VExpr
  | [] => falseS
  | p :: ps => disj p (bigOr ps)

@[obj_simp] theorem bigOr_liftN {n k : Nat} :
    ∀ ps : List VExpr, (bigOr ps).liftN n k = bigOr (ps.map (·.liftN n k))
  | [] => rfl
  | p :: ps => by simp only [bigOr, disj_liftN, bigOr_liftN ps, List.map_cons]

@[obj_simp] theorem bigOr_inst {e : VExpr} {k : Nat} :
    ∀ ps : List VExpr, (bigOr ps).inst e k = bigOr (ps.map (·.inst e k))
  | [] => rfl
  | p :: ps => by simp only [bigOr, disj_inst, bigOr_inst ps, List.map_cons]

section
variable {env : Typing} [E : ObjEnv env] {Γ : List VExpr} {R : VExpr}

/-- Every member of `ps` is a proposition in `Γ`. -/
def Props (env : Typing) (Γ ps : List VExpr) : Prop := ∀ p ∈ ps, env.HasType Γ p (.sort .zero)

theorem bigOrTy : ∀ {ps : List VExpr}, Props env Γ ps → env.HasType Γ (bigOr ps) (.sort .zero)
  | [], _ => falseTy
  | p :: _, h => disjTy (h p (.head _)) (bigOrTy fun q hq => h q (.tail _ hq))

theorem bigOr_intro : ∀ {ps : List VExpr} {p : VExpr}, Props env Γ ps → p ∈ ps → Thm env Γ p →
    Thm env Γ (bigOr ps)
  | q :: ps, p, hps, hp, h => by
    have hq := hps q (.head _)
    have hr := bigOrTy (env := env) (Γ := Γ) fun r hr => hps r (.tail _ hr)
    rcases List.mem_cons.1 hp with rfl | hp
    · exact Thm.disjI1 hq hr h
    · exact Thm.disjI2 hq hr (bigOr_intro (fun r hr => hps r (.tail _ hr)) hp h)

theorem bigOr_elim_len : ∀ (n : Nat) {ps : List VExpr} {Γ : List VExpr} {R : VExpr},
    ps.length = n → env.HasType Γ R (.sort .zero) → Props env Γ ps → Thm env Γ (bigOr ps) →
      (∀ p ∈ ps, Thm env (p :: Γ) p.lift → Thm env (p :: Γ) R.lift) → Thm env Γ R
  | _, [], _, _, _, hR, _, h, _ => Thm.exfalso h hR
  | n + 1, q :: ps, Γ, R, hn, hR, hps, h, k => by
    have hq := hps q (.head _)
    have hr := bigOrTy (env := env) (Γ := Γ) fun r hr => hps r (.tail _ hr)
    refine Thm.disjEH hq hr hR h (k q (.head _)) fun hh => ?_
    have hps' : Props env (bigOr ps :: Γ) (ps.map (·.liftN 1 0)) := by
      intro r hr
      obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hr
      exact weakTy (hps r' (.tail _ hr'))
    have hh' : Thm env (bigOr ps :: Γ) (bigOr (ps.map (·.liftN 1 0))) := by
      simpa only [obj_simp] using hh
    refine bigOr_elim_len n (by simpa using hn) (weakTy hR) hps' hh' fun p hp kp => ?_
    obtain ⟨p', hp', rfl⟩ := List.mem_map.1 hp
    have := k p' (.tail _ hp') (Thm.hyp .zero)
    have hi : Thm env (p'.lift :: bigOr ps :: Γ) (imp p'.lift.lift R.lift.lift) :=
      ((Thm.intro (hps p' (.tail _ hp')) this).weak.weak).cast (by simp only [imp_liftN])
    exact hi.mp kp

theorem bigOr_elim {ps : List VExpr} {Γ : List VExpr} {R : VExpr}
    (hR : env.HasType Γ R (.sort .zero)) (hps : Props env Γ ps) (h : Thm env Γ (bigOr ps))
    (k : ∀ p ∈ ps, Thm env (p :: Γ) p.lift → Thm env (p :: Γ) R.lift) : Thm env Γ R :=
  bigOr_elim_len _ rfl hR hps h k

omit E in
theorem props_cons {p : VExpr} {ps : List VExpr} (hp : env.HasType Γ p (.sort .zero))
    (hps : Props env Γ ps) : Props env Γ (p :: ps) := by
  intro r hr
  rcases List.mem_cons.1 hr with rfl | hr
  · exact hp
  · exact hps r hr

omit E in
theorem props_map {α : Type} {g : α → VExpr} {bs : List α}
    (h : ∀ b, env.HasType Γ (g b) (.sort .zero)) : Props env Γ (bs.map g) := by
  intro r hr
  obtain ⟨b, -, rfl⟩ := List.mem_map.1 hr
  exact h b

theorem bigOr_mono {ps qs : List VExpr} (hps : Props env Γ ps) (hqs : Props env Γ qs)
    (hsub : ∀ p ∈ ps, p ∈ qs) (h : Thm env Γ (bigOr ps)) : Thm env Γ (bigOr qs) := by
  refine bigOr_elim (bigOrTy hqs) hps h fun p hp kp => ?_
  have hqs' : Props env (p :: Γ) (qs.map (·.liftN 1 0)) := by
    intro r hr
    obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hr
    exact weakTy (hqs r' hr')
  simp only [obj_simp]
  exact bigOr_intro hqs' (List.mem_map_of_mem (hsub p hp)) kp

end

macro_rules | `(tactic| otype_rules) => `(tactic|
  ((with_reducible refine bigOrTy (props_map fun _ => ?_)); otype))
macro_rules | `(tactic| otype_rules) => `(tactic|
  ((with_reducible refine bigOrTy (props_cons ?_ (props_map fun _ => ?_))) <;> otype))

/-! ### Numerals -/

section
variable {env : Typing} [E : ObjEnv env] {Γ : List VExpr} {a b : VExpr}

/-- Distinct numerals are provably distinct. -/
theorem lit_ne : ∀ {Γ : List VExpr} {i j : Nat}, i ≠ j → Thm env Γ (¬ₒ (lit i =ₒ lit j))
  | _, 0, 0, h => absurd rfl h
  | _, 0, j + 1, _ => zero_ne_succ (litTy j)
  | _, i + 1, 0, _ => succ_ne_zero (litTy i)
  | Γ, i + 1, j + 1, h => by
    ointro e
    have e' := (succ_inj (litTy (env := env) (Γ := (lit (i + 1) =ₒ lit (j + 1)) :: Γ) i)
      (litTy j)).mp e
    exact (lit_ne (Γ := (lit (i + 1) =ₒ lit (j + 1)) :: Γ) (fun h' => h (by rw [h']))).mp e'

/-- Equality of numbers is decidable. -/
theorem eq_or_ne (ha : Tm env Γ a) (hb : Tm env Γ b) : Thm env Γ (a =ₒ b ∨ₒ ¬ₒ (a =ₒ b)) := by
  ocases (lt_trichotomy ha hb) with h1 h2
  · oright; ointro e; olift h1; orw [e] at h1; exact lt_irrefl (by otype) h1
  · ocases h2 with h3 h4
    · oleft; exact h3
    · oright; ointro e; olift h4; orw [e] at h4; exact lt_irrefl (by otype) h4

end

/-! ### The walk and the sentences, over a code -/

section
variable (f : PR) (d : Nat)

/-- The walk of `f` at `d`, at `k`. -/
def hT (k : VExpr) : VExpr := app2 (fn f) (lit d) k

/-- The walk reaches `a`. -/
def Pa (a : Nat) : VExpr := ex (hT f d (.bvar 0) =ₒ lit a)

/-- The walk never leaves `a`. -/
def Stay (a : Nat) : VExpr := all (imp (hT f d (.bvar 0) =ₒ lit a) (hT f d (S (.bvar 0)) =ₒ lit a))

/-- **`S_a`**: the walk reaches `a` and never leaves it. -/
def Ss (a : Nat) : VExpr := conj (Pa f d a) (Stay f d a)

theorem Ss_eq (a : Nat) : Ss f d a = Sb (fn f) (lit d) a := rfl

/-- The certificate check of `¬S_b` at the first component of `k`. -/
noncomputable def Qt (T : PR) (b : Nat) (k : VExpr) : VExpr :=
  prf T (numT (encExpr (neg (Ss f d b)))) (fst k)

end

section
variable {f : PR} {d : Nat} {T : PR} {b n j : Nat} {k e : VExpr}

@[obj_simp] theorem hT_liftN : (hT f d k).liftN n j = hT f d (k.liftN n j) := by
  simp only [hT, obj_simp]
@[obj_simp] theorem hT_inst : (hT f d k).inst e j = hT f d (k.inst e j) := by
  simp only [hT, obj_simp]
@[obj_simp] theorem Qt_liftN : (Qt f d T b k).liftN n j = Qt f d T b (k.liftN n j) := by
  simp only [Qt, numT, fst, obj_simp]
@[obj_simp] theorem Qt_inst : (Qt f d T b k).inst e j = Qt f d T b (k.inst e j) := by
  simp only [Qt, numT, fst, obj_simp]

end

section
variable {env : Typing} [E : ObjEnv env] {Γ : List VExpr} {f : PR} {d : Nat}

theorem hTTy {k : VExpr} (hk : Tm env Γ k) : Tm env Γ (hT f d k) := by unfold hT; otype
theorem QtTy {T : PR} {b : Nat} {k : VExpr} (hk : Tm env Γ k) : Tm env Γ (Qt f d T b k) := by
  unfold Qt; otype

end

macro_rules | `(tactic| otype_rules) => `(tactic| ((with_reducible refine hTTy ?_); otype))
macro_rules | `(tactic| otype_rules) => `(tactic| ((with_reducible refine QtTy ?_); otype))

section
variable {env : Typing} [E : ObjEnv env] {Γ : List VExpr} {f : PR} {d : Nat}

theorem PaTy (a : Nat) : env.HasType Γ (Pa f d a) (.sort .zero) := by unfold Pa; otype
theorem StayTy (a : Nat) : env.HasType Γ (Stay f d a) (.sort .zero) := by unfold Stay; otype
theorem SsTy (a : Nat) : env.HasType Γ (Ss f d a) (.sort .zero) := by
  unfold Ss; exact conjTy (PaTy a) (StayTy a)

end

macro_rules | `(tactic| otype_rules) => `(tactic| with_reducible exact PaTy _)
macro_rules | `(tactic| otype_rules) => `(tactic| with_reducible exact StayTy _)
macro_rules | `(tactic| otype_rules) => `(tactic| with_reducible exact SsTy _)

section
variable {f : PR} {d : Nat}

theorem Pa_closed (a : Nat) : (Pa f d a).ClosedN :=
  (PaTy (env := natEnv) (Γ := []) a).closedN.1
theorem Stay_closed (a : Nat) : (Stay f d a).ClosedN :=
  (StayTy (env := natEnv) (Γ := []) a).closedN.1
theorem Ss_closed (a : Nat) : (Ss f d a).ClosedN :=
  (SsTy (env := natEnv) (Γ := []) a).closedN.1

@[obj_simp] theorem Pa_liftN {n k a : Nat} : (Pa f d a).liftN n k = Pa f d a :=
  (Pa_closed a).liftN_eq (Nat.zero_le _)
@[obj_simp] theorem Pa_inst {e : VExpr} {k a : Nat} : (Pa f d a).inst e k = Pa f d a :=
  (Pa_closed a).instN_eq (Nat.zero_le _)
@[obj_simp] theorem Stay_liftN {n k a : Nat} : (Stay f d a).liftN n k = Stay f d a :=
  (Stay_closed a).liftN_eq (Nat.zero_le _)
@[obj_simp] theorem Stay_inst {e : VExpr} {k a : Nat} : (Stay f d a).inst e k = Stay f d a :=
  (Stay_closed a).instN_eq (Nat.zero_le _)
@[obj_simp] theorem Ss_liftN {n k a : Nat} : (Ss f d a).liftN n k = Ss f d a :=
  (Ss_closed a).liftN_eq (Nat.zero_le _)
@[obj_simp] theorem Ss_inst {e : VExpr} {k a : Nat} : (Ss f d a).inst e k = Ss f d a :=
  (Ss_closed a).instN_eq (Nat.zero_le _)

end

/-! ### Tests and the step, over codes -/

section
variable {env : Typing} [E : ObjEnv env] {Γ : List VExpr} {l : List VExpr}

theorem ev2_congr {f : PR} {x x' y y' : VExpr} (hx : Tm env Γ x) (hx' : Tm env Γ x')
    (hy : Tm env Γ y) (hy' : Tm env Γ y') (h1 : Thm env Γ (x =ₒ x')) (h2 : Thm env Γ (y =ₒ y')) :
    Thm env Γ (ev f [x, y] =ₒ ev f [x', y']) := by
  orw [h1, h2]

/-- `ifz c a b` runs `a` at a zero of `c` and `b` elsewhere. -/
theorem ifz_cases {c a b : PR} (hl : Tms env Γ l) :
    Thm env Γ ((ev (ifz c a b) l =ₒ ev a l ∧ₒ ev c l =ₒ zero) ∨ₒ
      (ev (ifz c a b) l =ₒ ev b l ∧ₒ ¬ₒ (ev c l =ₒ zero))) := by
  ocases (zero_or_succ (evTy (f := c) hl)) with hz hs
  · oleft
    osplit
    · exact ev_ifz_zero rfl (by otype) hz
    · exact hz
  · ocases hs with m hm
    oright
    osplit
    · exact ev_ifz_succ rfl (by otype) mT hm
    · ointro e
      olift hm
      orw [hm] at e
      exact (succ_ne_zero (by otype)).mp e

end

section
variable {env : Typing} [E : ObjEnv env] {T : PR} {f : PR} {d : Nat} {q : Nat → PR}
  (hq : ∀ {Γ : List VExpr} (b : Nat) {r k : VExpr}, Tm env Γ r → Tm env Γ k →
    Thm env Γ (ev (q b) [r, k, lit d] =ₒ Qt f d T b k))
include hq

/-- The tests of `scC` read the checks `Qt`: its value `v` is `a`, or a `b` of `bs` whose check
is `0`. -/
theorem scC_cases {a : Nat} : ∀ (bs : List Nat) {Γ : List VExpr} {r k v : VExpr}, Tm env Γ r →
    Tm env Γ k → Tm env Γ v → Thm env Γ (v =ₒ ev (scC q bs a) [r, k, lit d]) →
    Thm env Γ (bigOr ((v =ₒ lit a) :: bs.map fun b => (v =ₒ lit b) ∧ₒ (Qt f d T b k =ₒ zero)))
  | [], Γ, r, k, v, hr, hk, hv, h => by
    refine bigOr_intro (props_cons (by otype) (props_map fun _ => by otype)) (.head _) ?_
    simpa only [scC, obj_simp] using h
  | b :: bs, Γ, r, k, v, hr, hk, hv, h => by
    have hl : Tms env Γ [r, k, lit d] := by otype
    have hP : Props env Γ ((v =ₒ lit a) :: (b :: bs).map fun b =>
        (v =ₒ lit b) ∧ₒ (Qt f d T b k =ₒ zero)) :=
      props_cons (by otype) (props_map fun _ => by otype)
    refine Thm.disjEH (by otype) (by otype) (bigOrTy hP) (ifz_cases (c := q b) (a := num b)
      (b := scC q bs a) hl) (fun h1 => ?_) (fun h2 => ?_)
    · simp only [obj_simp, List.map_map, Function.comp_def] at h1 ⊢
      ocases h1 with e1 e2
      have h' := h.weak (A := (ev (ifz (q b) (num b) (scC q bs a)) [r, k, lit d] =ₒ lit b) ∧ₒ
        (ev (q b) [r, k, lit d] =ₒ zero))
      simp only [scC, obj_simp] at h'
      have hb := Thm.trans (by otype) (by otype) (by otype) h' e1
      refine bigOr_intro (props_cons (by otype) (props_cons (by otype)
        (props_map fun _ => by otype))) (.tail _ (.head _)) (Thm.conjI (by otype) (by otype) hb ?_)
      exact Thm.trans (by otype) (by otype) (by otype)
        (Thm.symm (by otype) (by otype) (hq b (by otype) (by otype))) e2
    · simp only [obj_simp, List.map_map, Function.comp_def] at h2 ⊢
      ocases h2 with e1 e2
      have h' := h.weak (A := (ev (ifz (q b) (num b) (scC q bs a)) [r, k, lit d] =ₒ
        ev (scC q bs a) [r, k, lit d]) ∧ₒ ¬ₒ (ev (q b) [r, k, lit d] =ₒ zero))
      simp only [scC, obj_simp] at h'
      have ih := scC_cases bs (by otype) (by otype) (by otype)
        (Thm.trans (by otype) (by otype) (by otype) h' e1)
      refine bigOr_mono (props_cons (by otype) (props_map fun _ => by otype))
        (props_cons (by otype) (props_cons (by otype) (props_map fun _ => by otype))) ?_ ih
      intro p hp
      simp only [List.mem_cons, List.mem_map] at hp ⊢
      rcases hp with hp | hp
      · exact .inl hp
      · exact .inr (.inr hp)

/-- A check of `0` at some `b` of `bs`, none of which is `a`, makes the value of `scC` differ
from `a`. -/
theorem scC_ne {a b : Nat} : ∀ (bs : List Nat) {Γ : List VExpr} {r k : VExpr}, a ∉ bs → b ∈ bs →
    Tm env Γ r → Tm env Γ k → Thm env Γ (Qt f d T b k =ₒ zero) →
    Thm env Γ (¬ₒ (ev (scC q bs a) [r, k, lit d] =ₒ lit a))
  | [], _, _, _, _, hb, _, _, _ => absurd hb List.not_mem_nil
  | c :: bs, Γ, r, k, ha, hb, hr, hk, hQ => by
    have hl : Tms env Γ [r, k, lit d] := by otype
    have hac : a ≠ c := fun e => ha (e ▸ .head _)
    refine Thm.disjEH (by otype) (by otype) (by otype) (ifz_cases (c := q c) (a := num c)
      (b := scC q bs a) hl) (fun h1 => ?_) (fun h2 => ?_)
    · simp only [obj_simp] at h1 ⊢
      ocases h1 with e1 e2
      simp only [scC]
      ointro e
      olift e1
      have := Thm.trans (by otype) (by otype) (by otype) (Thm.symm (by otype) (by otype) e1) e
      exact (lit_ne (Ne.symm hac)).mp this
    · simp only [obj_simp] at h2 ⊢
      ocases h2 with e1 e2
      rcases List.mem_cons.1 hb with rfl | hb
      · have hQ' := hQ.weak (A := (ev (ifz (q b) (num b) (scC q bs a)) [r, k, lit d] =ₒ
          ev (scC q bs a) [r, k, lit d]) ∧ₒ ¬ₒ (ev (q b) [r, k, lit d] =ₒ zero))
        simp only [obj_simp] at hQ'
        exact Thm.exfalso (e2.mp (Thm.trans (by otype) (by otype) (by otype)
          (hq b (by otype) (by otype)) hQ')) (by otype)
      · have ih := scC_ne bs (Γ := ((ev (ifz (q c) (num c) (scC q bs a)) [r, k, lit d] =ₒ
          ev (scC q bs a) [r, k, lit d]) ∧ₒ ¬ₒ (ev (q c) [r, k, lit d] =ₒ zero)) :: Γ)
          (r := r.lift) (k := k.lift) (fun h => ha (.tail _ h)) hb (by otype) (by otype)
          (by simpa only [obj_simp] using hQ.weak)
        simp only [scC]
        ointro e
        olift ih
        olift e1
        exact ih.mp (Thm.trans (by otype) (by otype) (by otype) (Thm.symm (by otype) (by otype) e1) e)

variable {K : SFrame}

omit hq in
theorem nextC_lit {Γ : List VExpr} {a : Nat} {k : VExpr} (ha : a ≤ K.N) (hk : Tm env Γ k) :
    Thm env Γ (ev (nextC K q) [lit a, k, lit d] =ₒ ev (scC q (K.succL a) a) [lit a, k, lit d]) := by
  have h := ev_casc (c := var 0) (d := var 0) (show Tms env Γ [lit a, k, lit d] by otype)
    (K.worlds.map fun a => scC q (K.succL a) a) 0 a
    (by simp only [SFrame.worlds, List.length_map, List.length_range]; omega)
    (by rw [Nat.zero_add]; simp only [obj_simp]; orefl)
  simp only [SFrame.worlds, List.getElem_map, List.getElem_range] at h
  rw [nextC, SFrame.worlds]
  exact h

variable (hs : ∀ {Γ : List VExpr} {k : VExpr}, Tm env Γ k →
    Thm env Γ (hT f d (S k) =ₒ ev (nextC K q) [hT f d k, k, lit d]))
include hs

/-- **The step**: from `h k = a`, the walk stays at `a` or moves to a world `b` that `a` sees,
with `Qt b k` checking. -/
theorem step {Γ : List VExpr} {a : Nat} {k : VExpr} (ha : a ≤ K.N) (hk : Tm env Γ k)
    (h : Thm env Γ (hT f d k =ₒ lit a)) :
    Thm env Γ (bigOr ((hT f d (S k) =ₒ lit a) :: (K.succL a).map fun b =>
      (hT f d (S k) =ₒ lit b) ∧ₒ (Qt f d T b k =ₒ zero))) := by
  refine scC_cases hq (K.succL a) (litTy a) hk (hTTy (STy hk)) ?_
  orw [hs hk, h, nextC_lit ha hk]

/-- A checking `Qt b k`, for a world `b` that `a` sees, moves the walk off `a`. -/
theorem step_ne {Γ : List VExpr} {a b : Nat} {k : VExpr} (ha : a ≤ K.N) (hb : b ∈ K.succL a)
    (hk : Tm env Γ k) (h : Thm env Γ (hT f d k =ₒ lit a)) (hQ : Thm env Γ (Qt f d T b k =ₒ zero)) :
    Thm env Γ (¬ₒ (hT f d (S k) =ₒ lit a)) := by
  have hn := scC_ne hq (K.succL a) (K.not_mem_succL_self a) hb (litTy a) hk hQ
  orw [hs hk, h, nextC_lit ha hk]
  exact hn

end

/-! ### Solovay's machine computes its walk -/

section
variable {env : Typing} [E : ObjEnv env] {Γ : List VExpr} {T : PR} {K : SFrame} {d : Nat}
  {k r : VExpr}

theorem hT_prec_zero {nx : PR} : Thm env Γ (hT (prec .zero nx) d zero =ₒ zero) := by
  unfold hT
  orw [fn_ev, ev_prec_zero (f := prec .zero nx) rfl]

theorem hT_prec_succ {nx : PR} (hk : Tm env Γ k) :
    Thm env Γ (hT (prec .zero nx) d (S k) =ₒ ev nx [hT (prec .zero nx) d k, k, lit d]) := by
  unfold hT
  orw [fn_ev (litTy d) (STy hk), ev_prec_succ (f := prec .zero nx) rfl (.cons (litTy d) .nil) hk,
    ← fn_ev (f := prec .zero nx) (litTy d) hk]

theorem ev_test (hb : bnd T ≤ 2) {c : PR} {f : PR} {b : Nat}
    (hc : c.eval (fun i => [d].getD i 0) = encExpr (neg (Ss f d b))) (hr : Tm env Γ r)
    (hk : Tm env Γ k) :
    Thm env Γ (ev (comp2 T (ren (· + 2) c) (fstC (var 1))) [r, k, lit d] =ₒ
      Qt f d T b k) := by
  have hl : Tms env Γ [r, k, lit d] := by otype
  have h1 : Thm env Γ (ev (ren (· + 2) c) [r, k, lit d] =ₒ numT (encExpr (neg (Ss f d b)))) := by
    have e := ev_lits (env := env) (Γ := Γ) c [d]
    rw [hc] at e
    refine Thm.trans (by otype) (by otype) (by otype)
      (ev_ren_eq (· + 2) hl (l' := [lit d]) fun i => by cases i <;> rfl) ?_
    refine Thm.trans (by otype) (by otype) (by otype) e ?_
    exact Thm.symm (by otype) (by otype) (numT_lit _)
  have h2 : Thm env Γ (ev (fstC (var 1)) [r, k, lit d] =ₒ fst k) := by
    orw [ev_fstC hl]
  orw [ev_comp2 (f := comp2 T (ren (· + 2) c) (fstC (var 1))) rfl hl]
  rw [ev_take 2 hb]
  simp only [List.take_succ_cons, List.take_zero]
  exact ev2_congr (by otype) (by otype) (by otype) (by otype) h1 h2

theorem hM_zero : Thm env Γ (hT (hM T K) d zero =ₒ zero) := hT_prec_zero

theorem hM_succ (hk : Tm env Γ k) :
    Thm env Γ (hT (hM T K) d (S k) =ₒ ev (nextC K (qC T)) [hT (hM T K) d k, k, lit d]) :=
  hT_prec_succ hk

/-- At its own code, the machine's tests are the checks `Qt`. -/
theorem hM_test (hb : bnd T ≤ 2) (hd : d = (hM T K).code) (b : Nat) (hr : Tm env Γ r) (hk : Tm env Γ k) :
    Thm env Γ (ev (qC T b) [r, k, lit d] =ₒ Qt (hM T K) d T b k) := by
  refine ev_test hb ?_ hr hk
  rw [eval_negSC (hM T K) b (by exact hd), Ss_eq]
  rfl

end

end Incomplete.Obj
