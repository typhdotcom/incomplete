# incomplete

- Build: `nix develop -c lake build`. The toolchain is elan's, pinned by
  `lean-toolchain`.
- Library `Incomplete` (root `Incomplete.lean`, modules `Incomplete/*.lean`),
  namespace `Incomplete` (files that use lean4lean `open Lean4Lean`).
- lean4lean is a git dependency pinned in `lakefile.toml`; bump `rev` and run
  `lake update` together. Only its `Theory` is imported, which builds on this
  toolchain; lean4lean pins an older one for its kernel replica and tests, so
  `lakefile.toml` requires `batteries` at this toolchain's tag itself.
- Keep the sources free of `sorry`, `native_decide` and `axiom`; the headline
  theorems' `#print axioms` must stay `[propext, Classical.choice, Quot.sound]`.
