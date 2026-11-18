import Incomplete.Obj.Strong
import Incomplete.CheckPR

/-!
# Dispatch on a tag

`casc c bs d j` tests the value of `c` against `j, j+1, …` and runs the matching branch of `bs`,
or `d` past the end: the shape of `PRLib`-style dispatch codes. At a known numeral value of `c`
the matching branch is one rewrite (`ev_casc`, `ev_casc_end`). The checker's `dispC` is such a
cascade on the certificate's tag (`dispC_casc`), so `certStep` at a known tag runs that tag's rule
(`ev_certStep`). Numerals compute: `lit a + lit b`
and `lit a - lit b` are numerals (`add_lit`, `sub_lit`), and `eqz` of distinct numerals is
nonzero.
-/

namespace Incomplete.Obj
open Lean4Lean
open VExpr VEnv PR

/-- `ifz (eqz c (num j)) b₀ (ifz (eqz c (num (j+1))) b₁ (… d))`. -/
def casc (c : PR) : List PR → PR → Nat → PR
  | [], d, _ => d
  | b :: bs, d, j => ifz (eqz c (num j)) b (casc c bs d (j + 1))

section
variable {env : VEnv} [E : ObjEnv env] {Γ l : List VExpr} {c a b d : PR} {f : PR}

theorem add_lit (a : Nat) : ∀ b, Thm env Γ (add (lit a) (lit b) =ₒ lit (a + b))
  | 0 => add_zero (litTy a)
  | b + 1 => by
    show Thm env Γ (add (lit a) (S (lit b)) =ₒ S (lit (a + b)))
    orw [add_succ, add_lit a b]

theorem sub_lit (a : Nat) : ∀ b, Thm env Γ (sub (lit a) (lit b) =ₒ lit (a - b))
  | 0 => sub_zero (litTy a)
  | b + 1 => by
    show Thm env Γ (sub (lit a) (S (lit b)) =ₒ lit (a - (b + 1)))
    orw [sub_succ, sub_lit a b]
    rcases h : a - b with _ | m
    · rw [show a - (b + 1) = 0 by omega]; exact pred_zero
    · rw [show a - (b + 1) = m by omega]; exact pred_succ (litTy m)

theorem ev_ifz_eqz_eq {j : Nat} (hl : Tms env Γ l) (hc : Thm env Γ (ev c l =ₒ lit j)) :
    Thm env Γ (ev (ifz (eqz c (num j)) a b) l =ₒ ev a l) :=
  ev_ifz_zero rfl hl (ev_eqz_of_eq hl (by onorm; exact hc))

theorem ev_eqz_lit_ne {t j : Nat} (hl : Tms env Γ l) (hc : Thm env Γ (ev c l =ₒ lit t)) (h : t ≠ j) :
    Thm env Γ (ev (eqz c (num j)) l =ₒ S (lit ((j - t) + (t - j) - 1))) := by
  orw [ev_eqz rfl, hc, sub_lit, sub_lit, add_lit]
  rw [show j - t + (t - j) = (j - t + (t - j) - 1) + 1 by omega]
  orefl

theorem ev_ifz_eqz_ne {t j : Nat} (hl : Tms env Γ l) (hc : Thm env Γ (ev c l =ₒ lit t)) (h : t ≠ j) :
    Thm env Γ (ev (ifz (eqz c (num j)) a b) l =ₒ ev b l) :=
  ev_ifz_succ rfl hl (litTy _) (ev_eqz_lit_ne hl hc h)

/-- At the value `j + i` of `c`, the cascade from `j` runs its `i`th branch. -/
theorem ev_casc (hl : Tms env Γ l) : ∀ (bs : List PR) (j i : Nat) (hi : i < bs.length),
    Thm env Γ (ev c l =ₒ lit (j + i)) → Thm env Γ (ev (casc c bs d j) l =ₒ ev bs[i] l)
  | b :: bs, j, 0, _, hc => ev_ifz_eqz_eq hl hc
  | b :: bs, j, i + 1, hi, hc => by
    have ih := ev_casc hl bs (j + 1) i (by simp at hi; omega)
      (by rw [show j + 1 + i = j + (i + 1) by omega]; exact hc)
    simp only [casc, List.getElem_cons_succ]
    orw [ev_ifz_eqz_ne hl hc (by omega), ih]

/-- Past the branches, the cascade runs its default. -/
theorem ev_casc_end (hl : Tms env Γ l) : ∀ (bs : List PR) (j i : Nat), bs.length ≤ i →
    Thm env Γ (ev c l =ₒ lit (j + i)) → Thm env Γ (ev (casc c bs d j) l =ₒ ev d l)
  | [], _, _, _, _ => by simp only [casc]; orefl
  | b :: bs, j, i, hi, hc => by
    have ih := ev_casc_end hl bs (j + 1) (i - 1) (by simp at hi; omega)
      (by rw [show j + 1 + (i - 1) = j + i by simp at hi; omega]; exact hc)
    simp only [casc]
    orw [ev_ifz_eqz_ne hl hc (by simp at hi; omega), ih]

theorem dispC_casc (T : Tables) (R : Nat → Bool) : ∀ k t, dispC T R k t =
    casc (modC 16 (var 0)) ((List.range k).map fun i => if R (t + i) then ruleC T (t + i) else num 1)
      (num 1) t
  | 0, _ => rfl
  | k + 1, t => by
    rw [dispC, dispC_casc T R k (t + 1), List.range_succ_eq_map, List.map_cons, List.map_map, casc]
    simp only [Nat.add_zero, Nat.add_assoc, Nat.add_comm 1]
    rfl

/-- The checker's step at a certificate number with tag `t` runs the rule of `t`. -/
theorem ev_certStep {T : Tables} {R : Nat → Bool} {t : Nat} (ht : t < 16) (hl : Tms env Γ l)
    (hc : Thm env Γ (ev (modC 16 (var 0)) l =ₒ lit t)) :
    Thm env Γ (ev (certStep T R) l =ₒ ev (if R t then ruleC T t else num 1) l) := by
  have h := ev_casc (d := num 1) hl ((List.range 16).map fun i =>
    if R (0 + i) then ruleC T (0 + i) else num 1) 0 t (by simpa using ht) (by simpa using hc)
  simp only [List.getElem_map, List.getElem_range, Nat.zero_add] at h
  rw [certStep, dispC_casc]
  simpa only [Nat.zero_add] using h

end

end Incomplete.Obj
