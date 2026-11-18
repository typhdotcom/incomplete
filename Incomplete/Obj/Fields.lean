import Incomplete.Obj.Numeral

/-!
# Tuples, and codes at numerals

`restT i x` drops the first `i` fields of the tuple `x`, and `fldT i x` is its `i`th field, as
the codes `restC` and `fldC` compute them (`ev_restC`, `ev_fldC`); on nested pairs they read off
the components (`fldT_pair_zero`, `fldT_pair_succ`, `restT_pair_succ`).

A code at numerals is the numeral of its value (`ev_lits`): by adequacy, with no reasoning about
the code. So `numT` commutes with `pair` (`numT_pair`), and any fact about fixed numbers that the
meta level computes is an object equation.
-/

namespace Incomplete.Obj
open Lean4Lean
open VExpr VEnv PR

/-- The tuple `x` with its first `i` fields dropped, as `restC` computes it. -/
def restT : Nat → VExpr → VExpr
  | 0, x => x
  | i + 1, x => restT i (snd x)

/-- The `i`th field of the tuple `x`, as `fldC` computes it. -/
abbrev fldT (i : Nat) (x : VExpr) : VExpr := fst (restT i x)

section
variable {n k : Nat} {e x : VExpr}

@[obj_simp] theorem restT_liftN : ∀ i x, (restT i x).liftN n k = restT i (x.liftN n k)
  | 0, _ => rfl
  | i + 1, x => by simp only [restT, restT_liftN i]; simp only [obj_simp]

@[obj_simp] theorem restT_inst : ∀ i x, (restT i x).inst e k = restT i (x.inst e k)
  | 0, _ => rfl
  | i + 1, x => by simp only [restT, restT_inst i]; simp only [obj_simp]

end

section
variable {env : VEnv} [E : ObjEnv env] {Γ l : List VExpr} {a b x : VExpr}

theorem restTTy : ∀ (i : Nat) {x : VExpr}, Tm env Γ x → Tm env Γ (restT i x)
  | 0, _, h => h
  | i + 1, _, h => restTTy i (app2Ty (fnTy _) zeroTy h)

end

macro_rules | `(tactic| otype_rules) => `(tactic| ((with_reducible refine restTTy _ ?_); otype))

section
variable {env : VEnv} [E : ObjEnv env] {Γ l : List VExpr} {a b x y : VExpr}

theorem ev_restC (hl : Tms env Γ l) : ∀ (i : Nat) (p : PR),
    Thm env Γ (ev (restC i p) l =ₒ restT i (ev p l))
  | 0, p => Thm.refl (evTy hl)
  | i + 1, p => by
    have ih := ev_restC hl i (sndC p)
    simp only [restC, restT]
    orw [ih, ev_sndC hl]

theorem ev_fldC (hl : Tms env Γ l) (i : Nat) (p : PR) :
    Thm env Γ (ev (fldC i p) l =ₒ fldT i (ev p l)) := by
  simp only [fldC]
  orw [ev_fstC hl, ev_restC hl]

theorem restT_pair_succ (ha : Tm env Γ a) (hb : Tm env Γ b) (i : Nat) :
    Thm env Γ (restT (i + 1) (pair a b) =ₒ restT i b) := by
  simp only [restT]
  orw [snd_pair ha hb]

theorem fldT_pair_zero (ha : Tm env Γ a) (hb : Tm env Γ b) : Thm env Γ (fldT 0 (pair a b) =ₒ a) :=
  fst_pair ha hb

theorem fldT_pair_succ (ha : Tm env Γ a) (hb : Tm env Γ b) (i : Nat) :
    Thm env Γ (fldT (i + 1) (pair a b) =ₒ fldT i b) := by
  show Thm env Γ (fst (restT (i + 1) (pair a b)) =ₒ fst (restT i b))
  orw [restT_pair_succ ha hb]

theorem snd_le (ha : Tm env Γ a) : Thm env Γ (snd a ≤ₒ a) := by
  orw [snd_eq ha]; exact sub_le ha (by otype)

theorem triRoot_le (ha : Tm env Γ a) : Thm env Γ (triRoot a ≤ₒ a) :=
  le_trans (by otype) (by otype) ha (le_tri (by otype))
    (Thm.conjE1 (by otype) (by otype) (triRoot_spec ha))

theorem fst_le (ha : Tm env Γ a) : Thm env Γ (fst a ≤ₒ a) := by
  orw [fst_eq ha]
  exact le_trans (by otype) (by otype) ha (sub_le (by otype) (by otype)) (triRoot_le ha)

theorem restT_le : ∀ (i : Nat) {x : VExpr}, Tm env Γ x → Thm env Γ (restT i x ≤ₒ x)
  | 0, _, hx => le_refl hx
  | i + 1, _, hx => le_trans (by otype) (by otype) hx (restT_le i (by otype)) (snd_le hx)

theorem fldT_le (i : Nat) (hx : Tm env Γ x) : Thm env Γ (fldT i x ≤ₒ x) :=
  le_trans (by otype) (by otype) hx (fst_le (by otype)) (restT_le i hx)

/-- The second component is at most the root: `y - tri r ≤ r` for `r = triRoot y`. -/
theorem snd_le_triRoot (hy : Tm env Γ y) : Thm env Γ (snd y ≤ₒ triRoot y) := by
  ocases (triRoot_spec hy) with h1 h2
  orw [tri_succ (by otype)] at h2
  orw [snd_eq hy]
  ole (sub (add (tri (triRoot y)) (S (triRoot y))) (S y)) [h1, h2]

/-- **Surjective pairing.** -/
theorem pair_fst_snd (hy : Tm env Γ y) : Thm env Γ (pair (fst y) (snd y) =ₒ y) := by
  have h1 := Thm.conjE1 (by otype) (by otype) (triRoot_spec hy)
  have hs := snd_le_triRoot hy
  have e1 : Thm env Γ (add (fst y) (snd y) =ₒ triRoot y) := by
    orw [fst_eq hy]; exact sub_add_of_le (by otype) (by otype) hs
  orw [pair_eq (by otype) (by otype), e1, snd_eq hy]
  exact add_sub_of_le (by otype) hy h1

theorem restT_succ' : ∀ (i : Nat) (y : VExpr), restT (i + 1) y = snd (restT i y)
  | 0, _ => rfl
  | i + 1, y => restT_succ' i (snd y)

/-- A tuple is its field `i` paired with the rest. -/
theorem restT_split (i : Nat) (hy : Tm env Γ y) :
    Thm env Γ (restT i y =ₒ pair (fldT i y) (restT (i + 1) y)) := by
  rw [restT_succ']
  exact Thm.symm (by otype) (by otype) (pair_fst_snd (by otype))

/-! ### Codes at numerals -/

theorem getD_map_lit : ∀ (ns : List Nat) (i : Nat), (ns.map lit).getD i zero = lit (ns.getD i 0)
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: ns, i + 1 => getD_map_lit ns i

/-- **Closed computation.** A code at numerals is the numeral of its value. -/
theorem ev_lits (f : PR) (ns : List Nat) :
    Thm env Γ (ev f (ns.map lit) =ₒ lit (f.eval fun i => ns.getD i 0)) := by
  have h := PR.adequate E.hasNat E.ordered f (fun i => ns.getD i 0)
  have e : ev f (ns.map lit) = f.tr.subst (litS fun i => ns.getD i 0) := by
    unfold ev; congr 1; funext i; exact getD_map_lit ns i
  rw [e]; exact (Thm.ofDefEq h).weak0

theorem pair_lit (a b : Nat) : Thm env Γ (pair (lit a) (lit b) =ₒ lit (PR.pair a b)) := by
  have h := ev_lits (env := env) (Γ := Γ) pairC [a, b]
  rw [pairC_computes] at h
  orw [fn_ev]; exact h

theorem numT_pair (a b : Nat) : Thm env Γ (numT (PR.pair a b) =ₒ pair (numT a) (numT b)) := by
  orw [numT_lit, numT_lit, numT_lit, pair_lit]

end

end Incomplete.Obj
