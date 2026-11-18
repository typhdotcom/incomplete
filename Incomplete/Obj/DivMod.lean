import Incomplete.Obj.Pair
import Incomplete.Obj.Bnd

/-!
# Division by a constant

The codes `dmC k`, `divC k` and `modC k` of `PRLib`, for every `k ≥ 1` given as a meta-level
number: `y = k * div y + mod y` with `mod y < k`, by induction on `y` through `dmC`'s step; the
quotient and remainder are unique, so `div (k * p + t) = p` and `mod (k * p + t) = t` for
`t < k`.
-/

namespace Incomplete.Obj
open Lean4Lean
open VExpr Typing
open PR (dmC divC modC tagC selC fstC sndC cpair)

/-- `dm k a`, the code `dmC k` at `a`: `pair (a / k) (a % k)`. -/
abbrev dm (k : Nat) (a : VExpr) : VExpr := app2 (fn (dmC k)) zero a

/-- `div k a`, the code `divC k (var 0)` at `a`. -/
abbrev div (k : Nat) (a : VExpr) : VExpr := app2 (fn (divC k (.var 0))) zero a

/-- `mod k a`, the code `modC k (var 0)` at `a`. -/
abbrev mod (k : Nat) (a : VExpr) : VExpr := app2 (fn (modC k (.var 0))) zero a

@[obj_simp] theorem lit_zero : lit 0 = zero := rfl

section
variable {env : Typing} [E : ObjEnv env] {Γ l : List VExpr} {a b c p q r t y k' q' r' : VExpr}
  {k : Nat} {f : PR}

theorem lit_pos (hk : 0 < k) : Thm env Γ (zero <ₒ lit k) := by
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  exact zero_lt_succ (litTy k)

/-- `b < a` gives `a - b = S (a - S b)`. -/
theorem sub_eq_succ_of_lt (ha : Tm env Γ a) (hb : Tm env Γ b) (h : Thm env Γ (b <ₒ a)) :
    Thm env Γ (sub a b =ₒ S (sub a (S b))) := by
  have e : Thm env Γ (add b (S (sub a (S b))) =ₒ a) := by oring [le_elim (STy hb) ha h]
  have h' := add_sub_cancel_left hb (STy (subTy ha (STy hb)))
  orw [e] at h'; exact h'

/-! ### `dmC` -/

theorem dm_zero : Thm env Γ (dm k zero =ₒ pair zero zero) := by
  orw [fn_ev, ev_prec_zero, ev_cpair]

theorem dm_succ (hy : Tm env Γ y) : Thm env Γ (dm k (S y) =ₒ ev selC
    [add (sub (lit k) (S (snd (dm k y)))) (sub (S (snd (dm k y))) (lit k)),
      pair (S (fst (dm k y))) zero, pair (fst (dm k y)) (S (snd (dm k y))), dm k y, y, zero]) := by
  orw [fn_ev, ev_prec_succ, ev_ifz, ev_eqz, ev_cpair, ev_cpair, ev_fstC, ev_sndC, ← fn_ev]

theorem dm_succ_of_eq (hy : Tm env Γ y) (h : Thm env Γ (S (snd (dm k y)) =ₒ lit k)) :
    Thm env Γ (dm k (S y) =ₒ pair (S (fst (dm k y))) zero) := by
  orw [dm_succ hy, h, sub_self, add_zero, ev_selC_zero]

theorem dm_succ_of_lt (hy : Tm env Γ y) (h : Thm env Γ (S (snd (dm k y)) <ₒ lit k)) :
    Thm env Γ (dm k (S y) =ₒ pair (fst (dm k y)) (S (snd (dm k y)))) := by
  orw [dm_succ hy, sub_eq_succ_of_lt (litTy k) (by otype) h, le_of_lt (by otype) (by otype) h,
    add_zero, ev_selC_succ]

theorem dm_spec_succ (hy : Tm env Γ y)
    (h : Thm env Γ (y =ₒ add (mul (lit k) (fst (dm k y))) (snd (dm k y)) ∧ₒ snd (dm k y) <ₒ lit k)) :
    Thm env Γ (S y =ₒ add (mul (lit k) (fst (dm k (S y)))) (snd (dm k (S y))) ∧ₒ
      snd (dm k (S y)) <ₒ lit k) := by
  ocases h with h1 h2
  ocases (eq_or_lt_of_le (by otype) (litTy k) h2) with he hl
  · orw [dm_succ_of_eq (by otype) he, fst_pair, snd_pair]
    olift h1
    osplit
    · oring [h1, he]
    · exact le_trans (b := S (snd (dm k y.lift))) (by otype) (by otype) (by otype)
        (succ_le_succ (by otype) (by otype) (zero_le (by otype))) (le_of_eq (by otype) (by otype) he)
  · orw [dm_succ_of_lt (by otype) hl, fst_pair, snd_pair]
    olift h1
    osplit
    · oring [h1]
    · exact hl

/-- `y = k * div y + mod y` and `mod y < k`, through `dmC`. -/
theorem dm_spec_c (hk : 0 < k) : Thm env []
    (∀ₒ y, y =ₒ add (mul (lit k) (fst (dm k y))) (snd (dm k y)) ∧ₒ snd (dm k y) <ₒ lit k) := by
  oind
  · orw [dm_zero, fst_pair, snd_pair]
    osplit
    · oring
    · exact lit_pos hk
  · ointro ih; exact dm_spec_succ (by otype) ih

/-! ### `divC` and `modC` -/

theorem ev_divC (hl : Tms env Γ l) : Thm env Γ (ev (divC k f) l =ₒ fst (dm k (ev f l))) := by
  rw [show divC k f = fstC (.push f (dmC k)) from rfl]
  orw [ev_fstC hl, ev_push, ev_fn1 (f := dmC k)]

theorem ev_modC (hl : Tms env Γ l) : Thm env Γ (ev (modC k f) l =ₒ snd (dm k (ev f l))) := by
  rw [show modC k f = sndC (.push f (dmC k)) from rfl]
  orw [ev_sndC hl, ev_push, ev_fn1 (f := dmC k)]

theorem div_eq (ha : Tm env Γ a) : Thm env Γ (div k a =ₒ fst (dm k a)) := by
  orw [fn_ev, ev_divC (by otype)]

theorem mod_eq (ha : Tm env Γ a) : Thm env Γ (mod k a =ₒ snd (dm k a)) := by
  orw [fn_ev, ev_modC (by otype)]

/-- `y = k * div y + mod y` and `mod y < k`. -/
theorem div_mod_spec (hk : 0 < k) (hy : Tm env Γ y) :
    Thm env Γ (y =ₒ add (mul (lit k) (div k y)) (mod k y) ∧ₒ mod k y <ₒ lit k) := by
  have h : Thm env Γ (y =ₒ add (mul (lit k) (fst (dm k y))) (snd (dm k y)) ∧ₒ
      snd (dm k y) <ₒ lit k) := by ospec (dm_spec_c (env := env) hk) hy
  orw [div_eq hy, mod_eq hy]; exact h

theorem div_mod_lt_false (hk : Tm env Γ k') (hq : Tm env Γ q) (hr : Tm env Γ r)
    (hq' : Tm env Γ q') (hr' : Tm env Γ r') (h : Thm env Γ (add (mul k' q) r =ₒ add (mul k' q') r'))
    (h1 : Thm env Γ (r <ₒ k')) (l : Thm env Γ (q <ₒ q')) : Thm env Γ ⊥ₒ := by
  refine lt_irrefl (a := add (mul k' q) r) (by otype) ?_
  ole (add (sub k' (S r)) (add (mul k' (sub q' (S q))) r')) [h, h1, l]

/-- Quotient and remainder are unique. -/
theorem div_mod_unique (hk : Tm env Γ k') (hq : Tm env Γ q) (hr : Tm env Γ r) (hq' : Tm env Γ q')
    (hr' : Tm env Γ r') (h : Thm env Γ (add (mul k' q) r =ₒ add (mul k' q') r'))
    (h1 : Thm env Γ (r <ₒ k')) (h2 : Thm env Γ (r' <ₒ k')) :
    Thm env Γ (q =ₒ q' ∧ₒ r =ₒ r') := by
  have hq : Thm env Γ (q =ₒ q') := by
    ocases (lt_trichotomy hq hq') with l1 l23
    · oexfalso; olift h; olift h1
      exact div_mod_lt_false (by otype) (by otype) (by otype) (by otype) (by otype) h h1 l1
    · ocases l23 with e l3
      · exact e
      · oexfalso; olift h; olift h2
        exact div_mod_lt_false (by otype) (by otype) (by otype) (by otype) (by otype)
          (Thm.symm (by otype) (by otype) h) h2 l3
  osplit
  · exact hq
  · oring [h, hq]

theorem div_mod_tag (hk : 0 < k) (hp : Tm env Γ p) (ht : Tm env Γ t) (h : Thm env Γ (t <ₒ lit k)) :
    Thm env Γ (div k (add (mul (lit k) p) t) =ₒ p ∧ₒ mod k (add (mul (lit k) p) t) =ₒ t) := by
  have hs := div_mod_spec hk (addTy (mulTy (litTy k) hp) ht)
  ocases hs with h1 h2
  have u := div_mod_unique (litTy k) (by otype) (by otype) hp ht
    (Thm.symm (by otype) (by otype) h1) h2 h
  exact u

theorem div_tag (hk : 0 < k) (hp : Tm env Γ p) (ht : Tm env Γ t) (h : Thm env Γ (t <ₒ lit k)) :
    Thm env Γ (div k (add (mul (lit k) p) t) =ₒ p) :=
  Thm.conjE1 (by otype) (by otype) (div_mod_tag hk hp ht h)

theorem mod_tag (hk : 0 < k) (hp : Tm env Γ p) (ht : Tm env Γ t) (h : Thm env Γ (t <ₒ lit k)) :
    Thm env Γ (mod k (add (mul (lit k) p) t) =ₒ t) :=
  Thm.conjE2 (by otype) (by otype) (div_mod_tag hk hp ht h)

/-! ### Tags -/

/-- `t < k` for numerals, from the meta level. -/
theorem lit_lt : ∀ {t k : Nat}, t < k → Thm env Γ (lit t <ₒ lit k)
  | 0, k + 1, _ => zero_lt_succ (litTy k)
  | t + 1, k + 1, h => succ_le_succ (STy (litTy t)) (litTy k) (lit_lt (Nat.lt_of_succ_lt_succ h))

theorem ev_tagC {t : Nat} (hl : Tms env Γ l) :
    Thm env Γ (ev (tagC k t f) l =ₒ add (mul (lit k) (ev f l)) (lit t)) := by
  orw [ev_comp2, ev_fn2 (f := PR.addC), ev_comp2, ev_fn2 (f := PR.mulC), mulC_eq_mul]
  oring

theorem ev_divC_tagC {t : Nat} (hk : t < k) (hl : Tms env Γ l) :
    Thm env Γ (ev (divC k (tagC k t f)) l =ₒ ev f l) := by
  orw [ev_divC hl, ev_tagC hl, ← div_eq]
  exact div_tag (by omega) (by otype) (litTy t) (lit_lt hk)

theorem ev_modC_tagC {t : Nat} (hk : t < k) (hl : Tms env Γ l) :
    Thm env Γ (ev (modC k (tagC k t f)) l =ₒ lit t) := by
  orw [ev_modC hl, ev_tagC hl, ← mod_eq]
  exact mod_tag (by omega) (by otype) (litTy t) (lit_lt hk)

/-! ### Closed -/

theorem div_mod_spec_c (hk : 0 < k) :
    Thm env [] (∀ₒ y, y =ₒ add (mul (lit k) (div k y)) (mod k y) ∧ₒ mod k y <ₒ lit k) := by
  ointro; exact div_mod_spec hk (by otype)

theorem div_tag_c (hk : 0 < k) :
    Thm env [] (∀ₒ p t, t <ₒ lit k →ₒ div k (add (mul (lit k) p) t) =ₒ p) := by
  ointro; ointro; ointro h; exact div_tag hk (by otype) (by otype) h

theorem mod_tag_c (hk : 0 < k) :
    Thm env [] (∀ₒ p t, t <ₒ lit k →ₒ mod k (add (mul (lit k) p) t) =ₒ t) := by
  ointro; ointro; ointro h; exact mod_tag hk (by otype) (by otype) h

theorem div_mod_unique_c : Thm env [] (∀ₒ k q r q' r', add (mul k q) r =ₒ add (mul k q') r' →ₒ
    r <ₒ k →ₒ r' <ₒ k →ₒ q =ₒ q' ∧ₒ r =ₒ r') := by
  ointro; ointro; ointro; ointro; ointro; ointro h; ointro h1; ointro h2; olift h; olift h1
  exact div_mod_unique (by otype) (by otype) (by otype) (by otype) (by otype) h h1 h2

end

theorem dm_spec_provable {k : Nat} (hk : 0 < k) : Provable natEnv
    (∀ₒ y, y =ₒ add (mul (lit k) (fst (dm k y))) (snd (dm k y)) ∧ₒ snd (dm k y) <ₒ lit k) :=
  Thm.provable (dm_spec_c hk)
theorem div_mod_spec_provable {k : Nat} (hk : 0 < k) : Provable natEnv
    (∀ₒ y, y =ₒ add (mul (lit k) (div k y)) (mod k y) ∧ₒ mod k y <ₒ lit k) := Thm.provable (div_mod_spec_c hk)
theorem div_tag_provable {k : Nat} (hk : 0 < k) : Provable natEnv
    (∀ₒ p t, t <ₒ lit k →ₒ div k (add (mul (lit k) p) t) =ₒ p) := Thm.provable (div_tag_c hk)
theorem mod_tag_provable {k : Nat} (hk : 0 < k) : Provable natEnv
    (∀ₒ p t, t <ₒ lit k →ₒ mod k (add (mul (lit k) p) t) =ₒ t) := Thm.provable (mod_tag_c hk)
theorem div_mod_unique_provable : Provable natEnv (∀ₒ k q r q' r', add (mul k q) r =ₒ
    add (mul k q') r' →ₒ r <ₒ k →ₒ r' <ₒ k →ₒ q =ₒ q' ∧ₒ r =ₒ r') := Thm.provable div_mod_unique_c

end Incomplete.Obj
