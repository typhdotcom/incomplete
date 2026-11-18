import Lean

/-!
# Simp sets for object-level proofs

`obj_simp`: lemmas pushing `liftN` and `inst` through object formulas and terms, used to normalize
goals of object-level proofs. `bnd_simp`: what computes `bnd` of a code with symbolic numerals.
-/

register_simp_attr obj_simp
register_simp_attr bnd_simp
