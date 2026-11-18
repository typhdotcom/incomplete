import Incomplete.Obj.Eval

/-!
# Variables read by codes with symbolic numerals

`bnd` bounds the variables a code reads (`Obj.Eval`), and `ev_fn1`/`ev_fn2` need it. Renaming
moves the bound along the renaming (`bnd_ren_le`), so the numerals `num n` and `numC n` read
nothing for every `n`; with the `bnd_simp` set, `otype` computes `bnd` of a code built from
`PRLib`'s combinators and such numerals without evaluating them.
-/

namespace Incomplete.Obj
open PR

theorem bnd_ren_le : ∀ (f : PR) (σ : Nat → Nat) (m : Nat), (∀ i < bnd f, σ i < m) →
    bnd (ren σ f) ≤ m
  | .zero, _, _, _ => Nat.zero_le _
  | .var i, _, _, h => h i (by simp only [bnd]; omega)
  | .succ f, σ, m, h => bnd_ren_le f σ m h
  | .push h g, σ, m, hσ => by
    have ih1 := bnd_ren_le h σ m fun i hi => hσ i (by simp only [bnd]; omega)
    have ih2 := bnd_ren_le g (liftR σ) (m + 1) fun i hi => by
      rcases i with _ | i
      · show 0 < m + 1; omega
      · show σ i + 1 < m + 1
        have := hσ i (by simp only [bnd]; omega); omega
    simp only [ren, bnd]; omega
  | .prec g h, σ, m, hσ => by
    have h0 := hσ 0 (by simp only [bnd]; omega)
    have ih1 := bnd_ren_le g (fun i => σ (i + 1)) m fun i hi => hσ (i + 1) (by simp only [bnd]; omega)
    have ih2 := bnd_ren_le h (liftR (liftR fun i => σ (i + 1))) (m + 2) fun i hi => by
      rcases i with _ | _ | i
      · show 0 < m + 2; omega
      · show 0 + 1 < m + 2; omega
      · show σ (i + 1) + 1 + 1 < m + 2
        have := hσ (i + 1) (by simp only [bnd]; omega); omega
    simp only [ren, bnd]; omega

theorem bnd_ren_closed {f : PR} (σ : Nat → Nat) (h : bnd f = 0) : bnd (ren σ f) = 0 :=
  Nat.le_zero.1 (bnd_ren_le f σ 0 fun _ hi => absurd hi (by omega))

theorem bnd_num : ∀ n, bnd (num n) = 0
  | 0 => rfl
  | n + 1 => bnd_num n

theorem ren_num (σ : Nat → Nat) : ∀ n, ren σ (num n) = num n
  | 0 => rfl
  | n + 1 => congrArg PR.succ (ren_num σ n)

theorem bnd_dblC {a : PR} (h : bnd a = 0) : bnd (dblC a) = 0 := by
  have := bnd_ren_closed Nat.succ h
  simp only [dblC, comp2, bnd, h, this]; decide

theorem bnd_numC (n : Nat) : bnd (numC n) = 0 := by
  rw [numC]
  split
  · rfl
  have ih := bnd_numC (n / 2)
  split
  · exact bnd_dblC ih
  · exact bnd_dblC ih
termination_by n
decreasing_by all_goals omega

theorem bnd_ren_numC (σ : Nat → Nat) (n : Nat) : bnd (ren σ (numC n)) = 0 :=
  bnd_ren_closed σ (bnd_numC n)

attribute [bnd_simp] bnd ren liftR bnd_num ren_num bnd_numC bnd_ren_numC comp2 comp3 cpair ifz
  leq eqz fstC fstC.sndC sndC dmC divC modC tagC minP dblC addC mulC subC predC selC triC
  triRootC pairC histC covC iterC nthC histPC covPC

macro_rules | `(tactic| otype) => `(tactic| ((with_reducible show bnd _ ≤ _); simp [bnd_simp]; done))

end Incomplete.Obj
