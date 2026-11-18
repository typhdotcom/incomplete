import Lean

/-!
# The `obj_simp` simp set

Lemmas pushing `liftN` and `inst` through object formulas and terms, used to normalize goals of
object-level proofs.
-/

register_simp_attr obj_simp
