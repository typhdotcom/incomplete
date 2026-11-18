import Lean

/-!
# Simp sets for object-level proofs

`obj_simp`: lemmas pushing `liftN` and `inst` through object formulas and terms, used to normalize
goals of object-level proofs. `bnd_simp`: what computes `bnd` of a code with symbolic numerals. `obnd_le`: bounds
`bnd (c …) ≤ m` from bounds on the parts, which `obnd` applies at a code with head `c`.
-/

register_simp_attr obj_simp
register_simp_attr bnd_simp
register_label_attr obnd_le
