import Incomplete.Obj.Lift

/-!
# Instantiating numbered expressions, one constructor at a time

`instT e a k` is the code `instC` at `[e, a, k]`, the number of
`(decExpr e).inst (decExpr a) k`: the recursion `kcov instStep a e k`. A variable `7 * i` below
the cutoff `k` is kept, the one at `k` becomes `a` lifted by `k` (`liftT k a 0`), and one above
it moves down by one (`instT_bvar_lt`, `instT_bvar_eq`, `instT_bvar_gt`); the other constructors
are as for lifting.
-/

namespace Incomplete.Obj
open Lean4Lean
open VExpr Typing PR

/-- `instNum e a k`: the code `instC` at `[e, a, k]`. -/
abbrev instT (e a k : VExpr) : VExpr := ev instC [e, a, k]

theorem bnd_instStep : bnd instStep ≤ 3 := by have := bnd_liftC; unfold instStep; obnd
theorem bnd_covPC_instStep : bnd (covPC instStep) ≤ 2 := by have := bnd_instStep; obnd

/-- `instStep`'s own branch, for variables. -/
def instB0 : PR := ifz (leq (PR.succ stP) stK) (tagC 7 0 stP)
  (ifz (eqz stP stK) (liftP stK (var 0) (num 0)) (tagC 7 0 (leq stP (num 1))))

theorem instStep_casc : instStep = ifz stT instB0 (casc stT stBranches stProj 1) := rfl

section
variable {env : Typing} [E : ObjEnv env] {Γ : List VExpr} {a b c e f k p : VExpr}

theorem instT_eq (he : Tm env Γ e) (ha : Tm env Γ a) (hk : Tm env Γ k) :
    Thm env Γ (instT e a k =ₒ kcov instStep a e k) := by
  orw [ev_comp2 (f := instC) rfl]
  rw [ev_take2 bnd_covPC_instStep _ _ (_ :: _)]
  orw [ev_keyC]

theorem instT_app (hf : Tm env Γ f) (hb : Tm env Γ b) (ha : Tm env Γ a) (hk : Tm env Γ k) :
    Thm env Γ (instT (add (mul (lit 7) (pair f b)) (lit 3)) a k =ₒ
      add (mul (lit 7) (pair (instT f a k) (instT b a k))) (lit 3)) := by
  orw [instT_eq (by otype) ha hk, kcov_app instStep_casc bnd_instStep ha hf hb hk,
    ← instT_eq hf ha hk, ← instT_eq hb ha hk]

theorem instT_lam (hA : Tm env Γ c) (hb : Tm env Γ b) (ha : Tm env Γ a) (hk : Tm env Γ k) :
    Thm env Γ (instT (add (mul (lit 7) (pair c b)) (lit 4)) a k =ₒ
      add (mul (lit 7) (pair (instT c a k) (instT b a (S k)))) (lit 4)) := by
  orw [instT_eq (by otype) ha hk, kcov_lam instStep_casc bnd_instStep ha hA hb hk,
    ← instT_eq hA ha hk, ← instT_eq hb ha (STy hk)]

theorem instT_forallE (hA : Tm env Γ c) (hb : Tm env Γ b) (ha : Tm env Γ a) (hk : Tm env Γ k) :
    Thm env Γ (instT (add (mul (lit 7) (pair c b)) (lit 5)) a k =ₒ
      add (mul (lit 7) (pair (instT c a k) (instT b a (S k)))) (lit 5)) := by
  orw [instT_eq (by otype) ha hk, kcov_forallE instStep_casc bnd_instStep ha hA hb hk,
    ← instT_eq hA ha hk, ← instT_eq hb ha (STy hk)]

theorem instT_proj (hs : Tm env Γ c) (hi : Tm env Γ b) (he : Tm env Γ e) (ha : Tm env Γ a)
    (hk : Tm env Γ k) :
    Thm env Γ (instT (add (mul (lit 7) (pair c (pair b e))) (lit 6)) a k =ₒ
      add (mul (lit 7) (pair c (pair b (instT e a k)))) (lit 6)) := by
  orw [instT_eq (by otype) ha hk, kcov_proj instStep_casc bnd_instStep ha hs hi he hk,
    ← instT_eq he ha hk]

theorem instT_sort (hu : Tm env Γ c) (ha : Tm env Γ a) (hk : Tm env Γ k) :
    Thm env Γ (instT (add (mul (lit 7) c) (lit 1)) a k =ₒ add (mul (lit 7) c) (lit 1)) := by
  orw [instT_eq (by otype) ha hk, kcov_sort instStep_casc bnd_instStep ha hu hk]

theorem instT_const (hc : Tm env Γ c) (ha : Tm env Γ a) (hk : Tm env Γ k) :
    Thm env Γ (instT (add (mul (lit 7) c) (lit 2)) a k =ₒ add (mul (lit 7) c) (lit 2)) := by
  orw [instT_eq (by otype) ha hk, kcov_const instStep_casc bnd_instStep ha hc hk]

theorem instT_bvar_lt (hi : Tm env Γ p) (ha : Tm env Γ a) (hk : Tm env Γ k)
    (h : Thm env Γ (p <ₒ k)) : Thm env Γ (instT (mul (lit 7) p) a k =ₒ mul (lit 7) p) := by
  have hc : Thm env Γ (ev (leq (PR.succ stP) stK)
      [a, keyT (mul (lit 7) p) k, histP instStep a (keyT (mul (lit 7) p) k)] =ₒ zero) := by
    orw [ev_leq rfl, rd_P0 ha hi hk (by otype), rd_K ha (by otype) hk (by otype)]
    refine le_minT hk (by otype) (by otype) h (succ_le_succ hi (by otype) ?_)
    have := le_tag (t := zero) hi zeroTy (by decide : 0 < 7)
    orw [add_zero] at this; exact this
  orw [instT_eq (by otype) ha hk, kcov_bvar instStep_casc bnd_instStep ha hi hk]
  rw [instB0]
  orw [ev_ifz_zero rfl (by otype) hc, ev_tagC, rd_P0 ha hi hk (by otype), add_zero]

theorem instT_bvar_eq (ha : Tm env Γ a) (hk : Tm env Γ k) :
    Thm env Γ (instT (mul (lit 7) k) a k =ₒ liftT k a zero) := by
  have hK : Thm env Γ (minT k (S (mul (lit 7) k)) =ₒ k) := by
    refine minT_of_le hk (by otype) (le_trans hk (STy hk) (by otype) (le_succ hk)
      (succ_le_succ hk (by otype) ?_))
    have := le_tag (t := zero) hk zeroTy (by decide : 0 < 7)
    orw [add_zero] at this; exact this
  have hc : Thm env Γ (ev (leq (PR.succ stP) stK)
      [a, keyT (mul (lit 7) k) k, histP instStep a (keyT (mul (lit 7) k) k)] =ₒ S zero) := by
    orw [ev_leq rfl, rd_P0 ha hk hk (by otype), rd_K ha (by otype) hk (by otype), hK]
    exact succ_sub_self hk
  have hz : Thm env Γ (ev (eqz stP stK)
      [a, keyT (mul (lit 7) k) k, histP instStep a (keyT (mul (lit 7) k) k)] =ₒ zero) := by
    refine ev_eqz_of_eq (by otype) ?_
    orw [rd_P0 ha hk hk (by otype), rd_K ha (by otype) hk (by otype), hK]
  orw [instT_eq (by otype) ha hk, kcov_bvar instStep_casc bnd_instStep ha hk hk]
  rw [instB0]
  orw [ev_ifz_succ rfl (by otype) zeroTy hc, ev_ifz_zero rfl (by otype) hz]
  rw [liftP]
  orw [ev_comp3]
  rw [ev_take3 bnd_liftC _ _ _ (_ :: _)]
  orw [rd_K ha (by otype) hk (by otype), hK]

theorem instT_bvar_gt (hi : Tm env Γ p) (ha : Tm env Γ a) (hk : Tm env Γ k)
    (h : Thm env Γ (k <ₒ p)) : Thm env Γ (instT (mul (lit 7) p) a k =ₒ mul (lit 7) (sub p (lit 1))) := by
  have hK : Thm env Γ (minT k (S (mul (lit 7) p)) <ₒ p) :=
    lt_of_le_of_lt (by otype) hk hi (minT_le_left hk (by otype)) h
  have hc : Thm env Γ (ev (leq (PR.succ stP) stK)
      [a, keyT (mul (lit 7) p) k, histP instStep a (keyT (mul (lit 7) p) k)] =ₒ
      S (sub (S p) (S (minT k (S (mul (lit 7) p)))))) := by
    orw [ev_leq rfl, rd_P0 ha hi hk (by otype), rd_K ha (by otype) hk (by otype)]
    exact sub_eq_succ_of_lt (by otype) (by otype) (lt_trans (by otype) hi (by otype) hK (lt_succ hi))
  have hz : Thm env Γ (ev (eqz stP stK)
      [a, keyT (mul (lit 7) p) k, histP instStep a (keyT (mul (lit 7) p) k)] =ₒ
      S (sub p (S (minT k (S (mul (lit 7) p)))))) := by
    orw [ev_eqz rfl, rd_P0 ha hi hk (by otype), rd_K ha (by otype) hk (by otype),
      le_of_lt (by otype) hi hK, zero_add]
    exact sub_eq_succ_of_lt hi (by otype) hK
  orw [instT_eq (by otype) ha hk, kcov_bvar instStep_casc bnd_instStep ha hi hk]
  rw [instB0]
  orw [ev_ifz_succ rfl (by otype) (by otype) hc, ev_ifz_succ rfl (by otype) (by otype) hz, ev_tagC,
    ev_leq rfl, rd_P0 ha hi hk (by otype), add_zero]

end
end Incomplete.Obj
