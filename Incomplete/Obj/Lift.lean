import Incomplete.Obj.Key

/-!
# Lifting numbered expressions, one constructor at a time

`liftT n e k` is the code `liftC` at `[n, e, k]`, the number of `(decExpr e).liftN n k`: the
recursion `kcov liftStep n e k`. For each constructor of `encExpr` at symbolic components, the
equation one step of it gives: a variable `7 * i` below the cutoff `k` is kept, one at or above it
is moved up by `n` (`liftT_bvar_lt`, `liftT_bvar_ge`); sorts and constants are kept; `app`,
`lam`, `forallE` and `proj` lift their components, at `k + 1` under a binder.
-/

namespace Incomplete.Obj
open Lean4Lean
open VExpr VEnv PR

/-- `liftNum n e k`: the code `liftC` at `[n, e, k]`. -/
abbrev liftT (n e k : VExpr) : VExpr := ev liftC [n, e, k]

theorem bnd_liftStep : bnd liftStep ≤ 3 := by unfold liftStep; obnd
theorem bnd_covPC_liftStep : bnd (covPC liftStep) ≤ 2 := by have := bnd_liftStep; obnd
theorem bnd_liftC : bnd liftC ≤ 3 := by
  unfold liftC; refine bnd_comp2_le (bnd_const_le bnd_covPC_liftStep (by decide)) ?_ ?_ <;> obnd

/-- `liftStep`'s own branch, for variables. -/
def liftB0 : PR := tagC 7 0 (ifz (leq (PR.succ stP) stK) stP (addP (var 0) stP))

theorem liftStep_casc : liftStep = ifz stT liftB0 (casc stT stBranches stProj 1) := rfl

section
variable {env : VEnv} [E : ObjEnv env] {Γ : List VExpr} {a b e f k n p : VExpr}

theorem liftT_eq (hn : Tm env Γ n) (he : Tm env Γ e) (hk : Tm env Γ k) :
    Thm env Γ (liftT n e k =ₒ kcov liftStep n e k) := by
  orw [ev_comp2 (f := liftC) rfl]
  rw [ev_take2 bnd_covPC_liftStep _ _ (_ :: _)]
  orw [ev_keyC]

theorem liftT_app (hn : Tm env Γ n) (hf : Tm env Γ f) (ha : Tm env Γ a) (hk : Tm env Γ k) :
    Thm env Γ (liftT n (add (mul (lit 7) (pair f a)) (lit 3)) k =ₒ
      add (mul (lit 7) (pair (liftT n f k) (liftT n a k))) (lit 3)) := by
  orw [liftT_eq hn (by otype) hk, kcov_app liftStep_casc bnd_liftStep hn hf ha hk,
    ← liftT_eq hn hf hk, ← liftT_eq hn ha hk]

theorem liftT_lam (hn : Tm env Γ n) (ha : Tm env Γ a) (hb : Tm env Γ b) (hk : Tm env Γ k) :
    Thm env Γ (liftT n (add (mul (lit 7) (pair a b)) (lit 4)) k =ₒ
      add (mul (lit 7) (pair (liftT n a k) (liftT n b (S k)))) (lit 4)) := by
  orw [liftT_eq hn (by otype) hk, kcov_lam liftStep_casc bnd_liftStep hn ha hb hk,
    ← liftT_eq hn ha hk, ← liftT_eq hn hb (STy hk)]

theorem liftT_forallE (hn : Tm env Γ n) (ha : Tm env Γ a) (hb : Tm env Γ b) (hk : Tm env Γ k) :
    Thm env Γ (liftT n (add (mul (lit 7) (pair a b)) (lit 5)) k =ₒ
      add (mul (lit 7) (pair (liftT n a k) (liftT n b (S k)))) (lit 5)) := by
  orw [liftT_eq hn (by otype) hk, kcov_forallE liftStep_casc bnd_liftStep hn ha hb hk,
    ← liftT_eq hn ha hk, ← liftT_eq hn hb (STy hk)]

theorem liftT_proj (hn : Tm env Γ n) (hs : Tm env Γ a) (hi : Tm env Γ b) (he : Tm env Γ e)
    (hk : Tm env Γ k) :
    Thm env Γ (liftT n (add (mul (lit 7) (pair a (pair b e))) (lit 6)) k =ₒ
      add (mul (lit 7) (pair a (pair b (liftT n e k)))) (lit 6)) := by
  orw [liftT_eq hn (by otype) hk, kcov_proj liftStep_casc bnd_liftStep hn hs hi he hk,
    ← liftT_eq hn he hk]

theorem liftT_sort (hn : Tm env Γ n) (hu : Tm env Γ a) (hk : Tm env Γ k) :
    Thm env Γ (liftT n (add (mul (lit 7) a) (lit 1)) k =ₒ add (mul (lit 7) a) (lit 1)) := by
  orw [liftT_eq hn (by otype) hk, kcov_sort liftStep_casc bnd_liftStep hn hu hk]

theorem liftT_const (hn : Tm env Γ n) (hc : Tm env Γ a) (hk : Tm env Γ k) :
    Thm env Γ (liftT n (add (mul (lit 7) a) (lit 2)) k =ₒ add (mul (lit 7) a) (lit 2)) := by
  orw [liftT_eq hn (by otype) hk, kcov_const liftStep_casc bnd_liftStep hn hc hk]

theorem liftT_bvar_lt (hn : Tm env Γ n) (hi : Tm env Γ p) (hk : Tm env Γ k)
    (h : Thm env Γ (p <ₒ k)) : Thm env Γ (liftT n (mul (lit 7) p) k =ₒ mul (lit 7) p) := by
  have hc : Thm env Γ (ev (leq (PR.succ stP) stK)
      [n, keyT (mul (lit 7) p) k, histP liftStep n (keyT (mul (lit 7) p) k)] =ₒ zero) := by
    orw [ev_leq rfl, rd_P0 hn hi hk (by otype), rd_K hn (by otype) hk (by otype)]
    refine le_minT hk (by otype) (by otype) h (succ_le_succ hi (by otype) ?_)
    have := le_tag (t := zero) hi zeroTy (by decide : 0 < 7)
    orw [add_zero] at this; exact this
  orw [liftT_eq hn (by otype) hk, kcov_bvar liftStep_casc bnd_liftStep hn hi hk]
  rw [liftB0]
  orw [ev_tagC, ev_ifz_zero rfl (by otype) hc, rd_P0 hn hi hk (by otype), add_zero]

theorem liftT_bvar_ge (hn : Tm env Γ n) (hi : Tm env Γ p) (hk : Tm env Γ k)
    (h : Thm env Γ (k ≤ₒ p)) : Thm env Γ (liftT n (mul (lit 7) p) k =ₒ mul (lit 7) (add n p)) := by
  have hK : Thm env Γ (minT k (S (mul (lit 7) p)) ≤ₒ p) :=
    le_trans (by otype) hk hi (minT_le_left hk (by otype)) h
  have hc : Thm env Γ (ev (leq (PR.succ stP) stK)
      [n, keyT (mul (lit 7) p) k, histP liftStep n (keyT (mul (lit 7) p) k)] =ₒ
      S (sub (S p) (S (minT k (S (mul (lit 7) p)))))) := by
    orw [ev_leq rfl, rd_P0 hn hi hk (by otype), rd_K hn (by otype) hk (by otype)]
    exact sub_eq_succ_of_lt (by otype) (by otype) (lt_succ_of_le (by otype) hi hK)
  orw [liftT_eq hn (by otype) hk, kcov_bvar liftStep_casc bnd_liftStep hn hi hk]
  rw [liftB0]
  orw [ev_tagC, ev_ifz_succ rfl (by otype) (by otype) hc]
  rw [addP]
  orw [ev_comp2, ev_fn2 (f := addC), rd_P0 hn hi hk (by otype), add_zero, add_comm (a := p)]

end
end Incomplete.Obj
