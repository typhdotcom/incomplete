# incomplete

Lean 4 proofs of the Gödel–Kleene, Rosser, and second incompleteness theorems
and of Löb's theorem for the formal type theory of [lean4lean](https://github.com/digama0/lean4lean),
extended with concrete inductives and primitive projections from
[typhdotcom/lean4lean](https://github.com/typhdotcom/lean4lean).

Provability is defined directly against the typing judgment
`VEnv.HasType` / `VEnv.IsDefEq` of `Lean4Lean.Theory.Typing`. The results
concern that formal specification, not lean4lean's kernel implementation or
Lean's own kernel.

## Theorems

All theorems live in namespace `Incomplete`.

### Unconditional fragment

```lean
theorem incomplete_unconditional :
    ∃ d : PR, ¬d.Halts d.code ∧ ¬BProvable natEnv (notHalts d d.code) ∧
      ¬BProvable natEnv (halts d d.code)

theorem bconsistent : ¬BProvable natEnv falseS

theorem bhaltsSound {f : PR} {n : Nat} (hp : BProvable natEnv (halts f n)) : f.Halts n
```

With no hypotheses, the projection-free `Prop`/`Type` fragment of `natEnv` is
consistent, sound for `halts`, and neither proves nor refutes the true
non-halting sentence of some machine on its own code
(`Incomplete/ModelSound.lean`, `Incomplete/Unconditional.lean`).

### First incompleteness (full theory)

```lean
theorem incomplete_rosser (env : VEnv) (hwf : env.WF) (hext : natEnv ≤ env) (hC : Consistent env) :
    ∃ d : PR, env.HasType 0 [] (notHalts d d.code) (.sort .zero) ∧ ¬d.Halts d.code ∧
      ¬Provable env (notHalts d d.code) ∧ ¬Provable env (halts d d.code)

theorem incomplete_of_wf (env : VEnv) (hwf : env.WF) (hext : natEnv ≤ env) (hC : Consistent env) :
    ∃ d : PR, ¬d.Halts d.code ∧ ¬Provable env (notHalts d d.code) ∧
      (HaltsSound env → ¬Provable env (halts d d.code))
```

Every consistent well-formed extension of `natEnv` neither proves nor refutes
the closed, true non-halting sentence of the Rosser machine on its own code
(`Incomplete/Rosser.lean`). For the Gödel–Kleene diagonal machine, the true
non-halting sentence is unprovable under `Consistent env` and irrefutable under
`HaltsSound env` (`Incomplete/Extend.lean`).

### Second incompleteness

```lean
theorem second_incompleteness (env : VEnv) (hwf : env.WF) (hext : natEnv ≤ env)
    (hC : Consistent env) :
    ∃ T, TablesFor env T ∧ env.HasType 0 [] (Con T) (.sort .zero) ∧
      (¬(conM T).Halts 0 ↔ Consistent env) ∧ ¬Provable env (Con T)

theorem con_unprovable (env : VEnv) (hwf : env.WF) (hext : natEnv ≤ env)
    {T : Tables} (hT : TablesFor env T) (hC : Consistent env) : ¬Provable env (Con T)
```

Every consistent well-formed extension of `natEnv` admits tables `T` for which
`Con T` is a closed proposition. For every `T` with `TablesFor env T`, `Con T`
is true iff `Consistent env` (`con_true_iff`) and unprovable in `env`. Both
theorems rest on proving `Con T → G0 T` inside the theory
(`con_imp_G0_provable`, `Incomplete/Obj/Second.lean`).

### Löb's theorem

```lean
theorem loeb (env : VEnv) (hwf : env.WF) (hext : natEnv ≤ env) {T : Tables}
    (hT : TablesFor env T) {P : VExpr} (hP : env.HasType 0 [] P (.sort .zero))
    (h : Provable env (.forallE (Prov T P) P)) : Provable env P
```

For every well-formed extension of `natEnv`, every `T` with `TablesFor env T`,
and every closed proposition `P`: if the theory proves `Prov T P → P`, it proves
`P`. No consistency hypothesis is needed. `Prov T P` is the closed proposition
`∃ k, chkT T (⌜P⌝, k) = 0` with an impredicative `∃` over numbers: some
certificate checks as a proof of `P` (`ProvT`). Related results
(`Incomplete/Obj/Loeb.lean`):

- `prov_of_provable`: `Provable env P → Provable env (Prov T P)`.
- `prov_lit_iff`: under `Consistent env`, the theory proves
  `chkT T (⌜P⌝, k) = 0` for some numeral `k` iff `Provable env P`. Externally,
  `chkNum_eq_zero`: some `k` has `chkNumFor T _ ⌜P⌝ k = 0` iff `Provable env P`.
- `prov_sound`: under `HaltsSound env`, `Provable env (Prov T P)` implies
  `Provable env P`.
- `loeb_halts`: the same conclusion from a proof of
  `halts (provM T P) 0 → P`, the double-negation provability sentence, which
  the theory derives from `Prov T P` (`prov_imp_halts`).
- `con_iff_not_prov`: the theory proves `Con T ↔ ¬Prov T ⊥`.
- `con_unprovable_of_loeb`: `con_unprovable`, from `loeb` at `P := ⊥`.

### A consistent, ω-inconsistent context

```lean
theorem omega_inconsistent (env : VEnv) (hwf : env.WF) (hext : natEnv ≤ env) {T : Tables}
    (hT : TablesFor env T) (hC : Consistent env) :
    ¬Thm env [Prov T falseS] falseS ∧
    Thm env [Prov T falseS] (Prov T falseS) ∧
    ∀ k : Nat, Thm env [Prov T falseS] (neg (prfT T (numT (encExpr falseS)) (lit k) =ₒ zero))
```

For every consistent well-formed extension of `natEnv` and every `T` with
`TablesFor env T`, the context `[Prov T ⊥]` is consistent, proves that some
certificate checks as a proof of `⊥`, and refutes each numeral `k` as that
certificate. `Prov T ⊥` speaks of `env`'s own checker: the context is a
hypothesis over `env`, not a new environment. Consistency is `loeb` at
`P := ⊥`; each refutation holds already in the empty context
(`not_prf_false_lit`). `omega_inconsistent_exists` states the same for tables
that every well-formed `env` admits (`Incomplete/Obj/Omega.lean`).

### Declaration-list variants

`incomplete_rosser'`, `incomplete_of_wf'`, and `second_incompleteness'` prove
the identical conclusions for any consistent environment built from
well-formed declarations that include `Nat`. They replace the binders
`(env : VEnv) (hwf : env.WF) (hext : natEnv ≤ env)` with

```lean
{ds : List VDecl} {env : VEnv} (H : env.WF' ds) (hm : .induct natDecl ∈ ds)
```

## Definitions

- `PR`, `PR.Halts f n`, `PR.code`: primitive recursive codes equipped with one
  outer unbounded search; `f.Halts n` holds when `f(n, k) = 0` for some `k`,
  and `f.code` numbers `f`.
- `natEnv`: the environment declaring `Nat`, `Nat.zero`, `Nat.succ`, `Nat.rec`,
  and its iota rules.
- `falseS`, `notHalts f n`, `halts f n`: `falseS` is `∀ p : Prop, p`;
  `notHalts f n` is `∀ k : Nat, isZero (f n k) → False` with `f` compiled to
  `Nat.rec` terms; `halts f n` is `notHalts f n → False`.
- `Provable env P`: some closed term `e` satisfies `env.HasType 0 [] e P`.
- `BProvable env P`: provable by a derivation restricted to sorts `Prop` and
  `Type` and free of projection rules (`BDefEq`, `Incomplete/Bounded.lean`).
- `Consistent env`: `¬Provable env falseS`.
- `HaltsSound env`: every provable `halts f n` is true (1-consistency for
  halting sentences).
- `TablesFor env T`: the finite lists in `T` enumerate `env`'s constants,
  definitional-equality rules, and inductive types.
- `chkT T`, `Con T`, `G0 T`: `chkT T` is the `PR` proof checker for `T`. On the
  number of a sentence `P` and a number `k`, it returns `0` when `k` encodes a
  `T`-checked certificate of a closed proof of `P`; some `k` yields `0` iff `P`
  is provable (`chkNum_eq_zero`). `conM T` runs `chkT T` on the number of
  `falseS`, defining `Con T := notHalts (conM T) 0`. `dg T` runs `chkT T` on
  the number of the diagonal sentence of its input, defining
  `G0 T := notHalts (dg T) ⌜dg T⌝`.
- `Prov T P`, `provM T P`: `Prov T P` is `∃ k, chkT T (⌜P⌝, k) = 0` as an
  object proposition with an impredicative `∃`; `provM T P` runs `chkT T` on the
  number of `P`, so `conM T = provM T falseS`.
- `Thm env Γ P`, `prfT T s k`: `Thm env Γ P` holds when some term `e`
  satisfies `env.HasType 0 Γ e P`, so `Provable env P` is `Thm env [] P`;
  `prfT T s k` is the object term evaluating `chkT T` at `(s, k)`, and
  `numT (encExpr P)` and `lit k` are numerals for `⌜P⌝` and `k`.
- `env.WF`, `env.WF' ds`, `natEnv ≤ env`: lean4lean's environment
  well-formedness predicates and environment extension order.

## Scope

`incomplete_unconditional` applies to the projection-free `Prop`/`Type`
fragment of `natEnv`, whose consistency and `halts`-soundness are established
via a set model (`Incomplete/Model.lean`, `Incomplete/ModelSound.lean`). For
the full theory and its well-formed extensions, Rosser's theorem and the second
incompleteness theorem assume `Consistent`, and Gödel–Kleene irrefutability
additionally assumes `HaltsSound`; neither hypothesis is proved here for the
full type theory. Löb's theorem assumes neither.

Refuting `halts` for the Rosser machine requires universal reasoning inside the
object theory, built in `Incomplete/Induct.lean` via `Nat.rec` into `Prop`.
Proving `Con T → G0 T` for the second theorem requires formalizing natural
deduction, arithmetic, symbolic proof checking, and internal Σ₁-completeness
inside the object theory (`Incomplete/Obj/`).

## Dependency

`lakefile.toml` pins [typhdotcom/lean4lean](https://github.com/typhdotcom/lean4lean)
(a fork of [digama0/lean4lean](https://github.com/digama0/lean4lean)) at
[`979fe59306db`](https://github.com/typhdotcom/lean4lean/commit/979fe59306db077bc2c681319a53b4f521791603).
Core typing and definitional equality come from upstream; this repository uses
three additions from the fork:

- **Concrete inductive declarations** (`Theory/VEnv.lean`,
  `Theory/Inductive.lean`, `Theory/Typing/Env.lean`): `VInductDecl.WF`, recursor
  and iota-rule generation, `VEnv.addInduct`, and the `GeneratedWF` obligation
  that generated recursors and iota rules are well typed.
  `Incomplete/NatEnv.lean` identifies the explicit `Nat` environment with this
  construction; `Incomplete/NatDeclWF.lean` discharges both well-formedness
  obligations for `Nat`.
- **Primitive projections and structure eta** (`Theory/Typing/Basic.lean`):
  `VExpr.proj`, `VEnv.inducts`, and the `IsDefEq` rules `projDF`, `projIota`,
  and `projEta` with their `ProjAllowed` side conditions. Included in the
  full-theory proof checker (`Incomplete/Cert.lean`, `Incomplete/ProjRules.lean`)
  and omitted from `BDefEq`.
- **Environment and telescope lemmas**
  (`Theory/Typing/{EnvLemmas,Projection,Telescope}.lean`): `VEnv.WF.ordered`,
  `VDecl.WF.le`, `IsDefEq.appN_substT`, and `IsDefEq.lams_beta`.

Thus the full-theory statements use the judgment including the fork's
projection rules and its definition of well-formed environments. The proofs do
not depend on the fork's kernel verification, runtime-model axioms, or open
injectivity assumptions. Direct imports are limited to
`Lean4Lean.Theory.Typing.{Basic,Env,EnvLemmas,Meta,Projection,Telescope}`, with
`lean-toolchain` and transitive `batteries` matching lean4lean.

## Build and audit

```nu
nix develop -c lake build
```

To verify axiom usage, run `nix develop -c lake env lean <file>` on:

```lean
import Incomplete
open Incomplete
#print axioms incomplete_unconditional
#print axioms incomplete_rosser
#print axioms incomplete_rosser'
#print axioms incomplete_of_wf
#print axioms incomplete_of_wf'
#print axioms second_incompleteness
#print axioms second_incompleteness'
#print axioms con_unprovable
#print axioms loeb
#print axioms loeb_halts
#print axioms con_unprovable_of_loeb
#print axioms omega_inconsistent
#print axioms omega_inconsistent_exists
#print axioms bconsistent
#print axioms bhaltsSound
```

Each theorem depends only on `propext`, `Classical.choice`, and `Quot.sound`.
The codebase contains no `sorry`, `native_decide`, or custom `axiom`.

## Layout

Every file in `Incomplete/` opens with a module docstring stating its main
results.

- **Machines and external arithmetic** (`PR`, `PRLib`, `Sentences`, `Arith`,
  `Adequacy`): the `PR` model, halting sentences, and external Σ₁-completeness.
- **Proof checker and diagonalization** (`Encode`, `Cert*`, `Check*`, `*PR`,
  `Rules*`, `ProjRules`, `Enumerate`, `Diag`): Gödel numbering, proof
  certificates, the `PR` checker, and the diagonal machine.
- **Environments** (`NatEnv`, `NatWF`, `NatDeclWF`, `AndEnv`, `EqEnv`,
  `Extend`): well-formedness of `natEnv` and environment extensions.
- **Incompleteness reductions** (`Kleene`, `Main`, `Final`, `Induct`, `Rosser`,
  `Second`): abstract diagonal arguments, Gödel–Kleene and Rosser theorems, and
  reduction of the second theorem to an object-theory proof of `Con T → G0 T`.
- **Bounded fragment and set model** (`Bounded`, `BArith`, `BSigma`, `ZF`,
  `ZFUniv`, `Model`, `ModelSound`, `Unconditional`): `BDefEq`, its set model,
  and `incomplete_unconditional`.
- **Object-theory formalization (`Obj/`)**: internal development over any
  ordered environment containing `Nat` (`ObjEnv`):
  - *Logic and proof mode* (`Attr`, `Core`, `Tactic`, `Iota`, `Logic`): natural
    deduction `Thm env Γ P`, Leibniz equality, impredicative connectives and
    quantifiers, `Nat.rec` induction into `Prop`, `0 ≠ S n`, injectivity of
    `S`, `n = 0 ∨ ∃ m, n = S m`, and custom object-level tactics (`otype`,
    `orw`, `ointro`, `oind`, `ocases`, etc.) with their simp and label
    attributes.
  - *Arithmetic and recursion* (`Rec`, `Arith`, `Code`, `Eval`, `Bnd`, `Codes`,
    `Order`, `Closed`, `Ring`, `Ineq`, `Pair`, `DivMod`, `Strong`, `Cases`,
    `Cov`): symbolic evaluation `ev f l` of `PR` codes, `Lean.Grind` commutative
    semiring integration (`oring`, `ole`), strong induction (`osind`), Cantor
    pairing, Euclidean division, dispatch cascades, and course-of-values
    recursion.
  - *Internal syntax and proof checking* (`Reads`, `Key`, `Lift`, `Inst`,
    `Numeral`, `Fields`, `Check`, `Certs`, `Free`, `NumCert`, `Template`,
    `Holes`, `Chain`): variable-read bounds, de Bruijn lifting and
    instantiation on encoded terms, symbolic certificate verification (`certT`,
    `chkT`), closed certificate adequacy, multi-hole expression templates, and
    internal instantiation and modus ponens.
  - *Internal Σ₁-completeness, second theorem and Löb's theorem* (`Graph`,
    `Sigma`, `Reduce`, `Second`, `Loeb`, `Omega`): internal graph proofs
    (`ok_exists`) showing every `PR` code provably computes its values on
    numerals, yielding `Con T → G0 T` (`con_imp_G0_provable`) and
    `second_incompleteness`; for the Löb machine `loebM` searching for proofs
    of `haltsE d ⌜d⌝ → P`, `loeb`; and the ω-inconsistent context `[Prov T ⊥]`
    (`omega_inconsistent`).

## License

Apache 2.0, matching lean4lean (`LICENSE`).
