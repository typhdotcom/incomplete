import Incomplete.Obj.Inst
import Incomplete.Diag

/-!
# Numerals are inert

`numT n`, the value of the binary numeral code `numC n`, is `k * numT a + b` at `n = k * a + b`
with `b < k` (`numT_tag`), by recursion on the binary digits and never at a concrete `n`; so the
code of a constant is tagged as one (`numT_const`). `litT v`, the code `litC` at `v`, is the
number of the numeral `lit v`: a tower of `app succ` over `zero`. Lifting and instantiating leave
it unchanged, by induction on `v` (`liftT_litT_c`, `instT_litT_c`).
-/

namespace Incomplete.Obj
open Lean4Lean
open VExpr VEnv PR

/-- The value of the binary numeral code `numC n`. -/
abbrev numT (n : Nat) : VExpr := ev (numC n) []

theorem ev_numC_ctx (n : Nat) (l : List VExpr) : ev (numC n) l = numT n := by
  exact ev_congr fun i hi => by rw [bnd_numC] at hi; omega

theorem numC_zero : numC 0 = .zero := by rw [numC]; rfl

section
variable {env : VEnv} [E : ObjEnv env] {Γ : List VExpr}

theorem numT_step {n : Nat} (hn : n ≠ 0) :
    Thm env Γ (numT n =ₒ add (add (numT (n / 2)) (numT (n / 2))) (lit (n % 2))) := by
  dsimp only [numT]
  rw [numC.eq_1 n, if_neg hn]
  split
  · rename_i h
    rw [h, dblC]
    orw [ev_comp2, ev_fn2 (f := addC)]
    rw [ev_numC_ctx]
    orw [add_zero]
  · rename_i h
    rw [show n % 2 = 1 by omega, dblC]
    orw [ev_comp2, ev_fn2 (f := addC)]
    rw [ev_numC_ctx]
    orw [add_lit_one]

theorem numT_lit (n : Nat) : Thm env Γ (numT n =ₒ lit n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [numT, numC_zero, ev_zero]; orefl
  · have ih := numT_lit (n / 2)
    orw [numT_step (by omega), ih, add_lit, add_lit]
    rw [show n / 2 + n / 2 + n % 2 = n by omega]
    orefl
termination_by n
decreasing_by omega

/-- A numeral code at `k * a + b` with `b < k` is `k` times the one at `a`, plus `b`. -/
theorem numT_tag {k : Nat} (hk : 2 ≤ k) (a b : Nat) (hb : b < k) :
    Thm env Γ (numT (k * a + b) =ₒ add (mul (lit k) (numT a)) (lit b)) := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · rw [Nat.mul_zero, Nat.zero_add]
    simp only [numT, numC_zero, ev_zero]
    orw [numT_lit, mul_zero, zero_add]
  · have hn : k * a + b ≠ 0 := by have := Nat.mul_pos (by omega : 0 < k) ha; omega
    have e1 : (k * a + b) / 2 = k * (a / 2) + ((k * a + b) / 2) % k := by
      have : (k * a + b) / 2 / k = a / 2 := by
        rw [Nat.div_div_eq_div_mul, Nat.mul_comm 2 k, ← Nat.div_div_eq_div_mul,
          Nat.mul_add_div (by omega), Nat.div_eq_of_lt hb, Nat.add_zero]
      rw [← this]; exact (Nat.div_add_mod _ _).symm
    have ih := numT_tag hk (a / 2) ((k * a + b) / 2 % k) (Nat.mod_lt _ (by omega))
    rw [← e1] at ih
    have ha' := numT_step (env := env) (Γ := Γ) (n := a) (by omega)
    have e2 : Thm env Γ (add (add (lit ((k * a + b) / 2 % k)) (lit ((k * a + b) / 2 % k)))
        (lit ((k * a + b) % 2)) =ₒ add (mul (lit k) (lit (a % 2))) (lit b)) := by
      orw [add_lit, add_lit]
      have : (k * a + b) / 2 % k + (k * a + b) / 2 % k + (k * a + b) % 2 = k * (a % 2) + b := by
        have h1 := Nat.div_add_mod (k * a + b) 2
        have h2 := Nat.div_add_mod a 2
        rw [e1] at h1
        have : k * a = k * (2 * (a / 2) + a % 2) := by rw [h2]
        rw [Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm k 2, Nat.mul_assoc] at this
        omega
      rw [this]
      oring
    orw [numT_step hn, ih, ha']
    oring [e2]
termination_by a
decreasing_by omega

/-- The number of a constant, through `numC`: tag `2` over the code of its payload. -/
theorem numT_const (c : Lean.Name) (ls : List VLevel) :
    Thm env Γ (numT (encExpr (.const c ls)) =ₒ
      add (mul (lit 7) (numT (PR.pair (encName c) (encList encLevel ls)))) (lit 2)) :=
  numT_tag (by decide) _ 2 (by decide)

theorem numT_zero_eq : Thm env Γ (numT (encExpr Incomplete.zero) =ₒ
    add (mul (lit 7) (numT (PR.pair (encName ``Nat.zero) (encList encLevel [])))) (lit 2)) :=
  numT_const _ _

theorem numT_succ_eq : Thm env Γ (numT (encExpr Incomplete.succ) =ₒ
    add (mul (lit 7) (numT (PR.pair (encName ``Nat.succ) (encList encLevel [])))) (lit 2)) :=
  numT_const _ _

/-- `litT v`: the code `litC` at `v`, the number of the numeral `lit v`. -/
abbrev litT (v : VExpr) : VExpr := ev litC [v]

theorem litT_zero : Thm env Γ (litT zero =ₒ numT (encExpr Incomplete.zero)) := by
  orw [ev_prec_zero]

theorem litT_succ {v : VExpr} (hv : Tm env Γ v) : Thm env Γ (litT (S v) =ₒ
    add (mul (lit 7) (pair (numT (encExpr Incomplete.succ)) (litT v))) (lit 3)) := by
  orw [ev_prec_succ, ev_tagC, ev_cpair]
  rw [ev_numC_ctx]
  orefl

/-- Numerals have no variables: lifting leaves them. -/
theorem liftT_litT_c : Thm env [] (∀ₒ n k v, liftT n (litT v) k =ₒ litT v) := by
  ointro; ointro; oind
  · orw [litT_zero, numT_zero_eq, liftT_const]
  · ointro ih
    orw [litT_succ, numT_succ_eq, liftT_app, liftT_const, ih]

theorem liftT_litT {n k v : VExpr} (hn : Tm env Γ n) (hk : Tm env Γ k) (hv : Tm env Γ v) :
    Thm env Γ (liftT n (litT v) k =ₒ litT v) := by ospec liftT_litT_c hn hk hv

/-- Numerals have no variables: instantiating leaves them. -/
theorem instT_litT_c : Thm env [] (∀ₒ a k v, instT (litT v) a k =ₒ litT v) := by
  ointro; ointro; oind
  · orw [litT_zero, numT_zero_eq, instT_const]
  · ointro ih
    orw [litT_succ, numT_succ_eq, instT_app, instT_const, ih]

theorem instT_litT {a k v : VExpr} (ha : Tm env Γ a) (hk : Tm env Γ k) (hv : Tm env Γ v) :
    Thm env Γ (instT (litT v) a k =ₒ litT v) := by ospec instT_litT_c ha hk hv

end

theorem liftT_litT_provable : Provable natEnv (∀ₒ n k v, liftT n (litT v) k =ₒ litT v) :=
  liftT_litT_c

theorem instT_litT_provable : Provable natEnv (∀ₒ a k v, instT (litT v) a k =ₒ litT v) :=
  instT_litT_c

end Incomplete.Obj
