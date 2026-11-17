/-!
# The machine model: primitive recursion with one unbounded search

A code is a primitive recursive term over a valuation `ρ : Nat → Nat` of variables. `push h g` runs `g` with the value of `h` pushed onto
the valuation; `prec g h` recurses on variable `0`, running `g` on the rest of the valuation at
`0` and `h` on the result, the predecessor and the rest at a successor.

A code `f` halts on `n` when `f [k, n, 0, …] = 0` for some `k`. By Kleene's normal form theorem every
partial recursive function is a search of this shape, so this is a universal model. The
correspondence with the object theory needs only the primitive recursive part.
-/

namespace Incomplete

inductive PR where
  | zero
  | var (i : Nat)
  | succ (f : PR)
  | push (h g : PR)
  | prec (g h : PR)
  deriving DecidableEq, Repr

/-- `Nat.rec` into `Nat`, by structural recursion so that it compiles. -/
def recNat (z : Nat) (s : Nat → Nat → Nat) : Nat → Nat
  | 0 => z
  | y + 1 => s y (recNat z s y)

abbrev Val := Nat → Nat

def vcons (a : Nat) (ρ : Val) : Val
  | 0 => a
  | i + 1 => ρ i

def tl (ρ : Val) : Val := fun i => ρ (i + 1)

@[simp] theorem vcons_zero : vcons a ρ 0 = a := rfl
@[simp] theorem vcons_succ : vcons a ρ (i + 1) = ρ i := rfl
@[simp] theorem tl_vcons : tl (vcons a ρ) = ρ := rfl
@[simp] theorem tl_apply : tl ρ i = ρ (i + 1) := rfl

/-- The valuation `[k, n, 0, 0, …]`. -/
def val2 (k n : Nat) : Val := vcons k (vcons n fun _ => 0)

namespace PR

def eval : PR → Val → Nat
  | zero, _ => 0
  | var i, ρ => ρ i
  | succ f, ρ => f.eval ρ + 1
  | push h g, ρ => g.eval (vcons (h.eval ρ) ρ)
  | prec g h, ρ => recNat (g.eval (tl ρ)) (fun y r => h.eval (vcons r (vcons y (tl ρ)))) (ρ 0)

def Halts (f : PR) (n : Nat) : Prop := ∃ k, f.eval (val2 k n) = 0

/-- Triangular numbers, in closed form so that the kernel computes them in binary. -/
def tri (s : Nat) : Nat := s * (s + 1) / 2

theorem tri_zero : tri 0 = 0 := rfl

theorem tri_succ (s : Nat) : tri (s + 1) = tri s + (s + 1) := by
  unfold tri
  rw [show (s + 1) * (s + 1 + 1) = s * (s + 1) + (s + 1) * 2 by
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul]; omega]
  rw [Nat.add_mul_div_right _ _ (by decide)]

/-- Cantor's pairing. -/
def pair (a b : Nat) : Nat := tri (a + b) + b

theorem tri_le : ∀ {s t : Nat}, s < t → tri (s + 1) ≤ tri t
  | _, 0, h => absurd h (Nat.not_lt_zero _)
  | s, t + 1, h => by
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | rfl
    · have := tri_le h; rw [tri_succ t]; omega
    · exact Nat.le_refl _

theorem pair_sum {a b a' b' : Nat} (h : pair a b = pair a' b') : a + b = a' + b' := by
  unfold pair at h
  rcases Nat.lt_trichotomy (a + b) (a' + b') with l | e | l
  · have := tri_le l; rw [tri_succ] at this; omega
  · exact e
  · have := tri_le l; rw [tri_succ] at this; omega

theorem pair_inj {a b a' b' : Nat} (h : pair a b = pair a' b') : a = a' ∧ b = b' := by
  have e := pair_sum h; unfold pair at h; rw [e] at h; omega

end PR
end Incomplete
