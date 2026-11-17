# incomplete

A Lean 4 proof of Gödel–Kleene incompleteness for the formal type theory of
[lean4lean](https://github.com/typhdotcom/lean4lean): the typing judgment
`VEnv.HasType` / `VEnv.IsDefEq` of `Lean4Lean.Theory.Typing`, taken as a proof
system for sentences about `Nat`. It is about that formal judgment, not about
the kernel implementation in lean4lean or Lean's own kernel.

## Theorems

All are in namespace `Lean4Lean.Incomplete`.

```lean
theorem incomplete_unconditional :
    ∃ d : PR, ¬d.Halts d.code ∧ ¬BProvable natEnv (notHalts d d.code) ∧
      ¬BProvable natEnv (halts d d.code)
```

Some machine does not halt on its own code, and the Prop/Type fragment of
`natEnv` neither proves nor refutes that. No hypotheses.
(`Incomplete/Unconditional.lean`)

```lean
theorem incomplete_of_wf (env : VEnv) (hwf : env.WF) (hext : natEnv ≤ env) (hC : Consistent env) :
    ∃ d : PR, ¬d.Halts d.code ∧ ¬Provable env (notHalts d d.code) ∧
      (HaltsSound env → ¬Provable env (halts d d.code))
```

Every consistent well-formed extension of `natEnv` leaves some true
non-halting sentence unprovable, and, if its halting proofs are sound, also
irrefutable. (`Incomplete/Extend.lean`)

```lean
theorem incomplete_of_wf' {ds : List VDecl} {env : VEnv} (H : env.WF' ds)
    (hm : .induct natDecl ∈ ds) (hC : Consistent env) :
    ∃ d : PR, ¬d.Halts d.code ∧ ¬Provable env (notHalts d d.code) ∧
      (HaltsSound env → ¬Provable env (halts d d.code))
```

The same for any consistent environment built from well-formed declarations,
one of which is `Nat`. (`Incomplete/Extend.lean`)

```lean
theorem bconsistent : ¬BProvable natEnv falseS
```

The Prop/Type fragment of `natEnv` does not prove `False`.
(`Incomplete/ModelSound.lean`)

```lean
theorem bhaltsSound {f : PR} {n : Nat} (hp : BProvable natEnv (halts f n)) : f.Halts n
```

The fragment proves `halts f n` only when `f` halts on `n`.
(`Incomplete/ModelSound.lean`)

## Hypotheses and definitions

- `PR`, `PR.Halts f n`, `PR.code`: primitive recursive codes with one
  unbounded search; `f` halts on `n` when `f(n, k) = 0` for some `k`; `code`
  numbers a machine.
- `natEnv`: the environment with `Nat`, `Nat.zero`, `Nat.succ`, `Nat.rec` and
  its iota rules.
- `notHalts f n`: `∀ k : Nat, isZero (f n k) → False`, with `f` compiled to
  `Nat.rec` terms. `halts f n` is `notHalts f n → False`. `falseS` is
  `∀ p : Prop, p`.
- `Provable env P`: some closed term has type `P` (`env.HasType 0 [] e P`).
- `BProvable env P`: provable by a derivation whose sorts are `Prop` and `Type`
  and that uses no projection rule (`BDefEq`, `Incomplete/Bounded.lean`).
- `Consistent env`: `¬Provable env falseS`.
- `HaltsSound env`: every provable `halts f n` is true (1-consistency for these
  sentences).
- `env.WF`, `env.WF' ds`, `natEnv ≤ env`: lean4lean's well-formedness of an
  environment built from the declarations `ds`, and environment extension.

## Scope

The unconditional result is for the Prop/Type, projection-free fragment of
`natEnv`; its consistency and soundness for `halts` come from a set model
(`Incomplete/Model.lean`, `Incomplete/ModelSound.lean`). For the full theory
and its well-formed extensions, unprovability is conditional on `Consistent`
and irrefutability on `HaltsSound`, neither of which is proved here.

## Dependency

`lakefile.toml` requires lean4lean from `github.com/typhdotcom/lean4lean` at a
fixed commit of its `main`, and imports only
`Lean4Lean.Theory.Typing.{Basic,Env,EnvLemmas,Meta,Projection,Telescope}`.
Batteries comes transitively at lean4lean's pin; `lean-toolchain` matches
lean4lean's.

## Build and audit

```nu
nix develop -c lake build
```

To audit, check the axioms of each theorem in a file importing the library:

```lean
import Incomplete
open Lean4Lean.Incomplete
#print axioms incomplete_unconditional
#print axioms incomplete_of_wf
#print axioms incomplete_of_wf'
#print axioms bconsistent
#print axioms bhaltsSound
```

and run it with `nix develop -c lake env lean <file>`. Each reports only
`propext`, `Classical.choice` and `Quot.sound`. The sources contain no `sorry`,
`native_decide` or `axiom`.

## Layout

Each file in `Incomplete/` opens with a heading saying what it proves.

- `Kleene`: the abstract argument. `Main`, `Final`: its instance, from
  consistency.
- `PR`, `PRLib`: the machine model. `Sentences`, `Arith`, `Adequacy`: halting
  sentences and Σ₁-completeness.
- `Cert*`, `Check*`, `Encode`, `*PR`, `Rules*`, `ProjRules`: the proof checker as
  a machine. `Enumerate`, `Diag`: the diagonal machine.
- `NatEnv`, `NatWF`, `NatDeclWF`, `AndEnv`, `EqEnv`, `Extend`: well-formed
  environments and their extensions.
- `Bounded`, `BArith`, `BSigma`, `ZF`, `ZFUniv`, `Model`, `ModelSound`,
  `Unconditional`: the Prop/Type fragment, its set model, and the unconditional
  result.

## License

Apache 2.0, as lean4lean (`LICENSE`).
