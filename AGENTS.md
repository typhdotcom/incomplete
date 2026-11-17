# incomplete

- Build: `nix develop -c lake build`. The toolchain is elan's, pinned by
  `lean-toolchain` to lean4lean's.
- Library `Incomplete` (root `Incomplete.lean`, modules `Incomplete/*.lean`),
  namespace `Lean4Lean.Incomplete`.
- lean4lean is a git dependency pinned in `lakefile.toml`; bump `rev` and run
  `lake update` together, and keep `lean-toolchain` equal to its.
- Keep the sources free of `sorry`, `native_decide` and `axiom`; the headline
  theorems' `#print axioms` must stay `[propext, Classical.choice, Quot.sound]`.
