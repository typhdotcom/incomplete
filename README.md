# incomplete

A Lean 4 proof of Gödel–Kleene and Rosser incompleteness for the formal type
theory of [lean4lean](https://github.com/digama0/lean4lean), with the inductive
and primitive projection extensions from
[typhdotcom/lean4lean](https://github.com/typhdotcom/lean4lean) described below.
The proof system is the typing judgment `VEnv.HasType` / `VEnv.IsDefEq` of
`Lean4Lean.Theory.Typing`, for sentences about `Nat`. It is about that formal
judgment, not about the kernel implementation in lean4lean or Lean's own
kernel.

## Theorems

All are in namespace `Incomplete`.

```lean
theorem incomplete_unconditional :
    ∃ d : PR, ¬d.Halts d.code ∧ ¬BProvable natEnv (notHalts d d.code) ∧
      ¬BProvable natEnv (halts d d.code)
```

Some machine does not halt on its own code, and the Prop/Type fragment of
`natEnv` neither proves nor refutes that. No hypotheses.
(`Incomplete/Unconditional.lean`)

```lean
theorem incomplete_rosser (env : VEnv) (hwf : env.WF) (hext : natEnv ≤ env) (hC : Consistent env) :
    ∃ d : PR, env.HasType 0 [] (notHalts d d.code) (.sort .zero) ∧ ¬d.Halts d.code ∧
      ¬Provable env (notHalts d d.code) ∧ ¬Provable env (halts d d.code)
```

Every consistent well-formed extension of `natEnv` neither proves nor refutes
some closed proposition: the true non-halting sentence of the Rosser machine on
its own code. `halts d n` is `notHalts d n → False`. (`Incomplete/Rosser.lean`)

```lean
theorem incomplete_rosser' {ds : List VDecl} {env : VEnv} (H : env.WF' ds)
    (hm : .induct natDecl ∈ ds) (hC : Consistent env) :
    ∃ d : PR, env.HasType 0 [] (notHalts d d.code) (.sort .zero) ∧ ¬d.Halts d.code ∧
      ¬Provable env (notHalts d d.code) ∧ ¬Provable env (halts d d.code)
```

The same for any consistent environment built from well-formed declarations,
one of which is `Nat`. (`Incomplete/Rosser.lean`)

```lean
theorem incomplete_of_wf (env : VEnv) (hwf : env.WF) (hext : natEnv ≤ env) (hC : Consistent env) :
    ∃ d : PR, ¬d.Halts d.code ∧ ¬Provable env (notHalts d d.code) ∧
      (HaltsSound env → ¬Provable env (halts d d.code))
```

The Gödel–Kleene form, for the diagonal machine: its true non-halting sentence
is unprovable, and, if halting proofs are sound, irrefutable.
(`Incomplete/Extend.lean`)

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
  sentences). Only the Gödel–Kleene form uses it.
- `env.WF`, `env.WF' ds`, `natEnv ≤ env`: lean4lean's well-formedness of an
  environment built from the declarations `ds`, and environment extension.

## Scope

The unconditional result is for the Prop/Type, projection-free fragment of
`natEnv`; its consistency and soundness for `halts` come from a set model
(`Incomplete/Model.lean`, `Incomplete/ModelSound.lean`). For the full theory
and its well-formed extensions, the Rosser form is conditional on `Consistent`
alone, and the Gödel–Kleene form's irrefutability also on `HaltsSound`;
neither hypothesis is proved here.

The Rosser machine races certificates for `notHalts d ⌜d⌝` against
certificates for `halts d ⌜d⌝`. Refuting a proof of `halts` takes reasoning
inside the object theory about every number: `Incomplete/Induct.lean` builds
those proofs with `Nat.rec` into `Prop`.

## Dependency

`lakefile.toml` pins [typhdotcom/lean4lean](https://github.com/typhdotcom/lean4lean),
a fork of [digama0/lean4lean](https://github.com/digama0/lean4lean), at commit
[`979fe59306db`](https://github.com/typhdotcom/lean4lean/commit/979fe59306db077bc2c681319a53b4f521791603).
The core typing and definitional-equality rules are inherited from upstream.
The proof uses the following additions from the fork:

- **Concrete inductive declarations and environments** (`Theory/VEnv.lean`,
  `Theory/Inductive.lean`, `Theory/Typing/Env.lean`). The fork defines
  `VInductDecl.WF`, recursor and iota-rule generation, and `VEnv.addInduct`,
  filling the inductive-specification placeholders in its upstream base.
  `Incomplete/NatEnv.lean` identifies the explicit `Nat` environment with this
  construction. The fork's `VDecl.WF.induct` also requires `GeneratedWF`:
  evidence that the generated recursors and iota rules are well typed.
  `Incomplete/NatDeclWF.lean` proves both obligations directly for `Nat`.
- **Primitive projections and structure eta** (`Theory/Typing/Basic.lean`).
  The fork adds `VExpr.proj`, the inductive-block table `VEnv.inducts`, and the
  rules `IsDefEq.projDF`, `projIota` and `projEta`, with their `ProjAllowed`
  conditions. `Incomplete/Cert.lean` and `Incomplete/ProjRules.lean` include
  these rules in the proof enumeration used for the full-theory results.
  The unconditional theorem's `BDefEq` fragment omits them.
- **Supporting environment and telescope lemmas** (`Theory/Typing/EnvLemmas.lean`,
  `Projection.lean`, `Telescope.lean`, and their dependencies). These include
  `VEnv.WF.ordered` for the concrete inductive specification, `VDecl.WF.le`
  for environment extensions, and `IsDefEq.appN_substT` and `IsDefEq.lams_beta`
  for the `Nat.rec` computations in `Incomplete/Arith.lean`.

Thus the full-theory statements use the judgment including the fork's
projection rules and its definition of well-formed environments. The proofs
do not depend on the fork's kernel-verification theorem, runtime-model axioms,
or open injectivity assumptions; the axiom audit below checks the resulting
theorems.

The direct lean4lean imports are
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
open Incomplete
#print axioms incomplete_unconditional
#print axioms incomplete_rosser
#print axioms incomplete_rosser'
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
- `Induct`, `Rosser`: induction in the object theory, the Rosser machine, and
  Rosser's theorem.
- `Second`: the consistency sentence `Con`, and the second theorem reduced to
  proving `Con → G0` in the object theory.
- `PR`, `PRLib`: the machine model. `Sentences`, `Arith`, `Adequacy`: halting
  sentences and Σ₁-completeness.
- `Cert*`, `Check*`, `Encode`, `*PR`, `Rules*`, `ProjRules`: the proof checker as
  a machine. `Enumerate`, `Diag`: the diagonal machine.
- `NatEnv`, `NatWF`, `NatDeclWF`, `AndEnv`, `EqEnv`, `Extend`: well-formed
  environments and their extensions.
- `Bounded`, `BArith`, `BSigma`, `ZF`, `ZFUniv`, `Model`, `ModelSound`,
  `Unconditional`: the Prop/Type fragment, its set model, and the unconditional
  result.
- `Obj/*`: natural deduction inside the object theory, over any environment
  with `Nat` that is ordered (`ObjEnv`). `Obj/Core`: the judgment
  `Thm env Γ P` (a proof of `P` in context `Γ`), the formulas `imp`, `all` and
  Leibniz equality `EqN`, and the rules, with induction by `Nat.rec` into
  `Prop`. `Obj/Tactic`: `otype` for typing side conditions, `orw` for
  rewriting by object equations in the goal or a hypothesis, also under object
  binders, `ointro`, `oind`, `ospec`, `olift`, and `∀ₒ x y, P` statements with
  named variables. `Obj/Iota`: the iota rules and `Nat.rec` congruence in every
  context. `Obj/Logic`: impredicative `⊥`, `¬`, `∧`, `∨`, `↔` and `∃` over
  `Nat`, their rules and tactics (`ocases`, which can name an existential's
  witness, `osplit`, `oleft`, `oright`, `oexists`), `0 ≠ S n`, injectivity of
  `S`, and `n = 0 ∨ ∃ m, n = S m`. `Obj/Rec`: binary functions by primitive
  recursion and their computation rules. `Obj/Arith`: `add` and `mul`,
  commutativity and associativity, closed in `natEnv` and at arbitrary terms.
  `Obj/Code`: the compiled codes `fn f` as closed atoms; `add` is
  `fn PR.addC`. `Obj/Eval`: `ev f l`, the code `f` at symbolic arguments `l`,
  with `fn f x y` equal to `ev f [y, x]`, and the computation rules of each
  constructor and of `ren`, `comp2` and `comp3` in every context. `Obj/Bnd`:
  the variables read by codes with symbolic numerals (`num n`, `numC n`), for
  `ev_fn1` and `ev_fn2`. `Obj/Codes`: the defining equations of `mulC`,
  `predC` and `subC`, and of `leq`, `eqz`, `selC`, `ifz` and `andz` on codes.
  `Obj/Order`: `a ≤ₒ b` as `a - b = 0`, its equivalence with
  `∃ c, a + c = b`, the laws of truncated subtraction, `fn mulC = mul`, and
  what `leq` and `eqz` test. `Obj/Closed`: these as closed theorems, and so
  `Provable natEnv`. `Obj/Ring`: distributivity, associativity of `mul` and
  cancellation; `ONat env Γ`, the terms of `Nat` in `Γ` up to provable
  equality, as a `Lean.Grind` commutative semiring; and `oring [h, …]`, which
  proves an equation from equations by `grind` in it. `Obj/Ineq`: `a <ₒ b` as
  `S a ≤ₒ b`; reflexivity, transitivity, totality, trichotomy, monotonicity
  and cancellation of `+` and `*`, truncated subtraction, and `eqz` nonzero at
  unequal values; and `ole c [h, …]`, which proves `a ≤ₒ b` from `a + c = b`
  by `oring`. `Obj/Pair`: `triC`, `triRootC`, `pairC`, `fstC`, `sndC` and
  `cpair` at symbolic arguments: `tri (S n) = tri n + S n`, monotonicity,
  `tri (triRoot n) ≤ n < tri (S (triRoot n))`, `triRoot (tri w + j) = w` for
  `j ≤ w`, `fst (pair a b) = a`, `snd (pair a b) = b`, and `a, b ≤ pair a b`.
  `Obj/DivMod`: `dmC k`, `divC k`, `modC k` and `tagC` for every `k ≥ 1`:
  `y = k * div y + mod y` with `mod y < k`, uniqueness, and
  `div (k * p + t) = p`, `mod (k * p + t) = t` for `t < k`. Both as schematic
  `Thm env Γ` lemmas and as `Provable natEnv`.
  `Obj/Strong`: strong induction `(∀ n, (∀ m < n, P m) → P n) → ∀ n, P n` for an
  open motive in any context (`Thm.sind`, tactic `osind`), and the measures the
  encodings decrease: `a, b < S (pair a b)`, `p < k * p + S t`, and `pair` along
  a smaller sum. `Obj/Cases`: `casc`, a cascade of tests of a code's value
  against `j, j+1, …`, its branch at a known numeral in one step, and the
  checker's `dispC` as such a cascade (`ev_certStep`). `Obj/Cov`: `iterC`,
  `nthC`, `histC`/`covC` and `histPC`/`covPC` with the step symbolic:
  `hist (S n) = S (pair (cov n) (hist n))`, and `cov j` read back from the
  history at `n` for `j < n`. `Obj/Reads`: `obnd`, bounds on the variables a
  composed code reads, by its structure. `Obj/Key`: the recursion of `liftC`
  and `instC` on the capped key `pair e (min k (e + 1))`, one equation per
  constructor of `encExpr` for any step of their shape. `Obj/Lift`, `Obj/Inst`:
  `liftC` and `instC` one constructor at a time at symbolic components:
  variables below, at and above the cutoff, sorts, constants, `app`, `lam`,
  `forallE`, `proj`. `Obj/Numeral`: the binary numeral codes `numC n` at
  `n = k * a + b`, and the number of the numeral `lit v` (`litC`) left
  unchanged by lifting and instantiation, for every `v`.

## License

Apache 2.0, as lean4lean (`LICENSE`).
