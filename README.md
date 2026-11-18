# incomplete

Lean 4 proofs of the Gödel–Kleene, Rosser, and second incompleteness theorems
and of Löb's theorem, together with the derivability conditions and
arithmetical soundness and completeness of the provability logic GL, for the formal type theory of [lean4lean](https://github.com/digama0/lean4lean),
extended with concrete inductives and primitive projections from
[typhdotcom/lean4lean](https://github.com/typhdotcom/lean4lean).

GL is also shown sound and complete for finite transitive irreflexive Kripke
models, and on letterless formulas it is decided by a level tower on `ω`, which
also gives their provability and truth in the object theory.

For `clEnv`, `natEnv` with a double-negation axiom, GL is the provability logic
of its `Prop`/`Type` fragment with no hypotheses: soundness and consistency of
the fragment come from a set model, and `□` is read as provability in the
fragment.

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

### Provability logic of the classical fragment

```lean
def clEnv : VEnv := withConst natEnv dneName ⟨0, dneS⟩

noncomputable def BProv (P : VExpr) : VExpr := ProvC (bchkT clT) P

theorem GL_iff_bprovable {A : Modal} :
    Modal.GL A ↔ ∀ σ : Nat → VExpr, (∀ n, BDefEq clEnv [] (σ n) (σ n) (.sort .zero)) →
      BProvable clEnv (A.breal σ)

theorem bprovable_iff_lvl {A : Modal} (hA : A.Letterless) (σ : Nat → VExpr) :
    BProvable clEnv (A.breal σ) ↔ ∀ n, Modal.lvl n A = true

theorem btr_iff_lim : ∀ {A : Modal}, A.Letterless → (A.btr ↔ Modal.lim A = true)

theorem bcon_iterated (σ : Nat → VExpr) (n : Nat) :
    ¬BProvable clEnv ((Modal.boxBot n).breal σ) ∧
      (Modal.imp (Modal.boxBot (n + 1)) (Modal.boxBot n)).btr ∧
      ¬BProvable clEnv ((Modal.imp (Modal.boxBot (n + 1)) (Modal.boxBot n)).breal σ)
```

`clEnv` adds to `natEnv` one axiom constant `Classical.dne : dneS`. It is well formed and extends
`natEnv` (`clEnv_wf`, `natEnv_le_clEnv`), its fragment proves `dneS` (`clEnv_dne`), and the set
model interprets the axiom, so the fragment is consistent and `halts`-sound (`clEnv_bconsistent`,
`clEnv_bhaltsSound`) (`Incomplete/ClEnv.lean`). `BProv P` says that some certificate passes the
fragment's checker `bchkT clT`, which accepts what `chkT clT` accepts within the bounds of
`BDefEq`, as a proof of `P`; `A.breal σ` realizes `□` as `BProv`. Then GL is exactly the
provability logic of the fragment (`GL_iff_bprovable`), a letterless sentence is provable iff it
holds at every level (`bprovable_iff_lvl`), and true, with `□B` read as provability of `B`'s
realization (`Modal.btr`), iff its limit is `true` (`btr_iff_lim`); so the iterated consistency
statements `□ⁿ⁺¹⊥ → □ⁿ⊥` are true and unprovable for every `n` (`bcon_iterated`)
(`Incomplete/BProvLogic.lean`).

The object-level development behind these runs over any judgment closed under the rules it uses
(`ObjEnv`), with full typing and the fragment as instances (`Incomplete/Obj/Typing.lean`), and
the provability logic over any proof-checking code the theory reasons about (`IsChecker`), with
the full checker and the fragment's checker as instances (`Incomplete/Obj/Checker.lean`,
`Incomplete/Obj/BChecker.lean`). The fragment's checker stays within the bounds through internal
modus ponens and instantiation at numerals (`Incomplete/Obj/Leaf.lean`).

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

### Derivability conditions and formalized Löb

```lean
theorem prov_mp_provable (env : VEnv) (hwf : env.WF) (hext : natEnv ≤ env) {T : Tables}
    {P Q : VExpr} (hQ : env.HasType 0 [] Q (.sort .zero)) :
    Provable env (.forallE (Prov T (.forallE P Q)) (.forallE (Prov T P) (Prov T Q)))

theorem prov_prov_provable (env : VEnv) (hwf : env.WF) (hext : natEnv ≤ env) {T : Tables}
    (hT : TablesFor env T) (P : VExpr) :
    Provable env (.forallE (Prov T P) (Prov T (Prov T P)))

theorem loeb_formalized (env : VEnv) (hwf : env.WF) (hext : natEnv ≤ env) {T : Tables}
    (hT : TablesFor env T) {P : VExpr} (hP : env.HasType 0 [] P (.sort .zero)) :
    Provable env (.forallE (Prov T (.forallE (Prov T P) P)) (Prov T P))
```

Together with necessitation (`prov_of_provable`, D1), these are the
Hilbert–Bernays–Löb derivability conditions D2 and D3 and Löb's theorem, all
proved inside the theory without consistency or soundness hypotheses
(`Incomplete/Obj/Derivability.lean`). D2 is internal modus ponens on
certificates. D3 is internal Σ₁-completeness for `Prov`: a `PR` code `σ` turns,
provably, each certificate `k` of `P` into a certificate `σ k` of
`Prov T P` (`sigma_prov`). Formalized Löb follows from D2, D3, and `loeb`
applied to `Prov T (Prov T P → P) → Prov T P`.

### Arithmetical soundness of GL

```lean
theorem GL_sound (env : VEnv) (hwf : env.WF) (hext : natEnv ≤ env) {T : Tables}
    (hT : TablesFor env T) (hdne : Provable env dneS) {σ : Nat → VExpr}
    (hσ : ∀ n, env.HasType 0 [] (σ n) (.sort .zero)) {A : Modal} (h : Modal.GL A) :
    Provable env (A.real T σ)

theorem iGL_sound (env : VEnv) (hwf : env.WF) (hext : natEnv ≤ env) {T : Tables}
    (hT : TablesFor env T) {σ : Nat → VExpr} (hσ : ∀ n, env.HasType 0 [] (σ n) (.sort .zero))
    {A : Modal} (h : Modal.iGL A) : Provable env (A.real T σ)

theorem fairbot (env : VEnv) (hwf : env.WF) (hext : natEnv ≤ env) {T : Tables}
    (hT : TablesFor env T) {A B : VExpr} (hA : env.HasType 0 [] A (.sort .zero))
    (hB : env.HasType 0 [] B (.sort .zero)) (hAB : Provable env (A ↔ₒ Prov T B))
    (hBA : Provable env (B ↔ₒ Prov T A)) : Provable env A ∧ Provable env B
```

Every theorem of the provability logic GL is provable under every
realization that sends propositional variables to closed propositions and `□`
to `Prov T`, provided the theory proves double-negation elimination `dneS`.
The object logic is intuitionistic, so this hypothesis is needed for GL's
classical tautologies only: the theorems of `iGL`, GL without
double-negation elimination, are provable under every realization in every
well-formed extension of `natEnv` (`Incomplete/Obj/GL.lean`). `fairbot`: two
closed propositions, each equivalent to the provability of the other, are both
provable.

### Kripke semantics of GL

```lean
structure Modal.FinModel (n : Nat) where
  R : Fin n → Fin n → Bool
  V : Fin n → Nat → Bool
  trans : ∀ {a b c}, R a b = true → R b c = true → R a c = true
  irrefl : ∀ a, R a a = false

theorem Modal.FinModel.GL_sound {n : Nat} (M : FinModel n) {A : Modal} (h : GL A) (w : Fin n) :
    M.Forces w A

theorem Modal.GL_complete {A : Modal} (h : ¬GL A) :
    ∃ (n : Nat) (M : FinModel (n + 1)), M.Rooted ∧ (∀ i k, M.V i k = true → var k ∈ sub A) ∧
      ¬M.Forces 0 A

theorem Modal.GL_iff {A : Modal} :
    GL A ↔ ∀ (n : Nat) (M : FinModel n) (w : Fin n), M.Forces w A
```

GL is sound and complete for finite transitive irreflexive Kripke models.
`M.Forces w A` is forcing, with `□A` forced at `w` when `A` is forced at
every world `w` sees; `M.eval` decides it (`FinModel.eval_iff`).
`M.Rooted` says world `0` sees every other world. Soundness holds more
generally for every transitive model whose accessibility relation is
conversely well-founded (`Modal.Kripke.GL_sound`). Completeness builds the
countermodel from the consistent sets of literals over the subformulas of
`A` (`Incomplete/Modal/`). This part is ordinary Lean mathematics about
`Modal` and does not involve the object theory.

### Arithmetical completeness of GL

```lean
theorem GL_arith_complete (env : VEnv) (hwf : env.WF) (hext : natEnv ≤ env) {T : Tables}
    (hT : TablesFor env T) (hdne : Provable env dneS) (hS : HaltsSound env) {A : Modal}
    (h : ¬Modal.GL A) :
    ∃ σ : Nat → VExpr, (∀ n, env.HasType 0 [] (σ n) (.sort .zero)) ∧
      ¬Provable env (A.real T σ)

theorem GL_iff_provable (env : VEnv) (hwf : env.WF) (hext : natEnv ≤ env) {T : Tables}
    (hT : TablesFor env T) (hdne : Provable env dneS) (hS : HaltsSound env) {A : Modal} :
    Modal.GL A ↔ ∀ σ : Nat → VExpr, (∀ n, env.HasType 0 [] (σ n) (.sort .zero)) →
      Provable env (A.real T σ)
```

Solovay's theorem: in a well-formed extension of `natEnv` that proves `dneS`
and is `halts`-sound, a modal formula is a theorem of GL exactly when the
theory proves it under every realization by closed propositions with `□` read
as `Prov T`. For `¬GL A`, the finite countermodel of `Modal.GL_complete`, below
a new root `0`, is the frame of a `PR` walk `hM T K` that, run on its own code,
starts at `0` and moves to a world `b` above its current one when the first
component of the step checks as a proof of `¬S_b`. `S_b` says that the walk
reaches `b` and never leaves it; each variable is realized as the disjunction
of the `S_(w+1)` over the worlds `w` forcing it (`solσ`). Inside the theory,
the `S_b` are pairwise exclusive, `S_i` refutes `Prov T ¬S_j` for `i R j`, and
for `i ≠ 0`, `S_i` proves `Prov T` of the disjunction of the `S_j` with `i R j`;
so `S_(w+1)` proves `A`'s realization or its negation as `w` forces `A` or not
(`truth`). A proof of the realization of `A` would refute `S_0`, and
`halts`-soundness turns every refutation of a sentence `S_b` at a world the
walk reaches into a move of the walk up the finite frame (`no_refuted`)
(`Incomplete/Obj/Solovay*.lean`).

### Letterless sentences

```lean
def Modal.lvl (n : Nat) : Modal → Bool
  | var _ => false
  | bot => false
  | imp A B => !lvl n A || lvl n B
  | box A => decide (∀ m, m < n → lvl m A = true)

theorem Modal.FinModel.forces_iff_lvl {n : Nat} (M : FinModel n) {A : Modal}
    (hA : Letterless A) (w : Fin n) : M.Forces w A ↔ lvl (M.height w) A = true

theorem Modal.GL_iff_lvl {A : Modal} (hA : Letterless A) : GL A ↔ ∀ n, lvl n A = true

theorem Modal.GL_iff_dec {A : Modal} (hA : Letterless A) : GL A ↔ dec A = true

theorem provable_iff_lvl (env : VEnv) (hwf : env.WF) (hext : natEnv ≤ env) {T : Tables}
    (hT : TablesFor env T) (hdne : Provable env dneS) (hS : HaltsSound env) {A : Modal}
    (hA : A.Letterless) (σ : Nat → VExpr) :
    Provable env (A.real T σ) ↔ ∀ n, Modal.lvl n A = true

theorem tr_iff_lim (env : VEnv) (hwf : env.WF) (hext : natEnv ≤ env) {T : Tables}
    (hT : TablesFor env T) (hdne : Provable env dneS) (hS : HaltsSound env) :
    ∀ {A : Modal}, A.Letterless → (A.tr env T ↔ Modal.lim A = true)

theorem boxBot_unprovable (env : VEnv) (hwf : env.WF) (hext : natEnv ≤ env) {T : Tables}
    (hT : TablesFor env T) (hS : HaltsSound env) (σ : Nat → VExpr) :
    ∀ n, ¬Provable env ((Modal.boxBot n).real T σ)

theorem boxBot_succ_imp_unprovable (env : VEnv) (hwf : env.WF) (hext : natEnv ≤ env)
    {T : Tables} (hT : TablesFor env T) (hS : HaltsSound env) (σ : Nat → VExpr) (n : Nat) :
    ¬Provable env ((Modal.imp (Modal.boxBot (n + 1)) (Modal.boxBot n)).real T σ)
```

A letterless modal formula, built from `⊥`, `→` and `□` alone, is evaluated on the level tower:
`□B` holds at level `n` when `B` holds at every level `m < n`. In a finite transitive irreflexive
model, a letterless formula is forced at a world exactly when it holds at the level given by the
world's height, the length of the longest chain above it (`FinModel.height`; more generally
`Kripke.forces_iff_lvl` for any `IsHeight`). So `GL` proves a letterless formula iff it holds at
every level. From the box depth `bd A` on, `lvl n A` is constant, `lim A` (`lvl_eq_lim`), so the
Boolean `dec A`, which checks the levels `n ≤ bd A`, decides `GL` on letterless formulas
(`Incomplete/Modal/Letterless.lean`).

The realization of a letterless formula does not depend on `σ` (`Modal.real_letterless`). In a
`halts`-sound well-formed extension of `natEnv` that proves `dneS`, the theory proves it iff it
holds at every level, iff `dec A = true` (`provable_iff_dec`). The direction from the levels
needs only `dneS` (`provable_of_lvl`); `dneS` is not removable through `iGL`, since `GL` proves the
letterless `¬¬□⊥ → □⊥` and `iGL` does not (`Modal.not_iGL_dne_box`, by a three-element algebra).
With truth `Modal.tr`, which reads `□B` as provability of `B`'s realization, a letterless sentence
is true iff its limit value is `true` (`tr_iff_lim`): the letterless case of Solovay's theorem on
true provability.

With `halts`-soundness alone, `□ⁿ⊥` is unprovable for every `n`, and `□ⁿ⁺¹⊥ → □ⁿ⊥` is true
(`tr_boxBot_succ_imp`) and, by Löb's theorem, unprovable; `GL` does not prove it, while its limit
value is `true` (`Modal.boxBot_succ_imp`). The case `n = 0` is `¬□⊥`, which the theory proves
equivalent to `Con T` (`con_iff_real_neg_box`); its unprovability needs only `Consistent env`
(`con_unprovable_letterless`). `halts`-soundness implies consistency
(`HaltsSound.consistent`) (`Incomplete/Obj/Letterless.lean`).

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
- `Typing`, `full env`, `bounded env`, `ObjEnv`: a `Typing` is an environment with a
  judgment `IsDefEq Γ e₁ e₂ A`; `full env` is `env.IsDefEq 0`, also written `env` by coercion,
  and `bounded env` is `BDefEq env`; `ObjEnv J` lists the rules the object-level development
  uses.
- `Thm env Γ P`, `prfT T s k`: `Thm env Γ P` holds when some term `e`
  satisfies `env.HasType Γ e P` in the judgment `env`, so for `env : VEnv`,
  `Provable env P` is `Thm env [] P`, and `BProvable env P` is `Thm (bounded env) [] P`;
  `prfT T s k` is the object term evaluating `chkT T` at `(s, k)`, and
  `numT (encExpr P)` and `lit k` are numerals for `⌜P⌝` and `k`.
- `Modal`, `Modal.Deriv`, `Modal.GL`, `Modal.iGL`, `Modal.real`: modal formulas
  over variables, `⊥`, `→`, and `□`; `Deriv cl` is the Hilbert system with
  axioms `A → B → A`, `(A → B → C) → (A → B) → A → C`, `⊥ → A`, K
  `□(A → B) → □A → □B`, and Löb `□(□A → A) → □A`, rules modus ponens and
  necessitation, and double-negation elimination `¬¬A → A` when `cl = true`;
  `GL := Deriv true`, `iGL := Deriv false`. `A.real T σ` replaces each variable
  `n` by `σ n`, `⊥` by `falseS`, `→` by `.forallE`, and `□` by `Prov T`.
- `dneS`: `∀ p : Prop, ¬¬p → p`.
- `clEnv`, `clT`: `natEnv` with the axiom `Classical.dne : dneS`, and its tables.
- `IsChecker env T`, `ProvC T P`, `Modal.realC T σ`: a code `T` read as a proof
  checker that the judgment `env` reasons about; `∃ k, T(⌜P⌝, k) = 0`; the
  realization with `□` read as `ProvC T`, so `Prov T = ProvC (chkT T)` and
  `Modal.real T = Modal.realC (chkT T)`.
- `bchkT T`, `BProv`, `Modal.breal`, `Modal.btr`: the checker of the fragment,
  `chkT T` together with the bounds of `BDefEq` on the certificate (`leafC`);
  `ProvC (bchkT clT)`; `Modal.realC (bchkT clT)`; truth with `□B` read as
  `BProvable clEnv (B.breal fun _ => falseS)`.
- `Modal.Kripke`, `Modal.FinModel n`, `Forces`, `Rooted`: a Kripke model is
  an accessibility relation and a valuation on a type of worlds; a
  `FinModel n` is a transitive irreflexive one on `Fin n` with Boolean
  relation and valuation; `Modal.sub A` lists the subformulas of `A`.
- `Modal.Letterless`, `Modal.lvl`, `Modal.bd`, `Modal.lim`, `Modal.dec`, `Modal.boxBot`,
  `Modal.tr`: `A` has no variables; `A`'s value at level `n`; box depth; `lvl (bd A) A`, the
  eventual value; the conjunction of `lvl n A` over `n ≤ bd A`; `□ⁿ⊥`; truth with `□B` read as
  `Provable env (B.real T fun _ => falseS)`.
- `env.WF`, `env.WF' ds`, `natEnv ≤ env`: lean4lean's environment
  well-formedness predicates and environment extension order.

## Scope

`incomplete_unconditional` applies to the projection-free `Prop`/`Type`
fragment of `natEnv`, whose consistency and `halts`-soundness are established
via a set model (`Incomplete/Model.lean`, `Incomplete/ModelSound.lean`). For
the full theory and its well-formed extensions, Rosser's theorem and the second
incompleteness theorem assume `Consistent`, and Gödel–Kleene irrefutability
additionally assumes `HaltsSound`; neither hypothesis is proved here for the
full type theory. Löb's theorem, the derivability conditions, formalized Löb,
`iGL_sound`, and `fairbot` assume neither; `GL_sound` assumes only that the
theory proves `dneS`; `GL_arith_complete` and `GL_iff_provable` assume that
and `HaltsSound env`, as do `provable_iff_lvl` and `tr_iff_lim`; `boxBot_unprovable` and
`boxBot_succ_imp_unprovable` assume only `HaltsSound env`. For the fragment of `clEnv`,
`GL_iff_bprovable`, `bprovable_iff_lvl`, `btr_iff_lim`, and `bcon_iterated` assume nothing.

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
#print axioms prov_mp_provable
#print axioms prov_prov_provable
#print axioms loeb_formalized
#print axioms GL_sound
#print axioms iGL_sound
#print axioms fairbot
#print axioms Modal.Kripke.GL_sound
#print axioms Modal.FinModel.GL_sound
#print axioms Modal.GL_complete
#print axioms Modal.GL_iff
#print axioms GL_arith_complete
#print axioms GL_iff_provable
#print axioms Modal.FinModel.forces_iff_lvl
#print axioms Modal.GL_iff_lvl
#print axioms Modal.GL_iff_dec
#print axioms Modal.not_iGL_dne_box
#print axioms provable_iff_lvl
#print axioms provable_iff_dec
#print axioms tr_iff_lim
#print axioms boxBot_unprovable
#print axioms boxBot_succ_imp_unprovable
#print axioms tr_boxBot_succ_imp
#print axioms con_unprovable_letterless
#print axioms bconsistent
#print axioms bhaltsSound
#print axioms clEnv_wf
#print axioms clEnv_bconsistent
#print axioms clEnv_bhaltsSound
#print axioms GL_iff_bprovable
#print axioms bprovable_iff_lvl
#print axioms bprovable_iff_dec
#print axioms btr_iff_lim
#print axioms bcon_iterated
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
  `ZFUniv`, `Model`, `ModelSound`, `Unconditional`, `ClEnv`): `BDefEq`, its set model over
  environments whose constants have values (`ModelEnv`), `incomplete_unconditional`, and the
  classical environment `clEnv`.
- **Provability logic of the classical fragment** (`BProvLogic`): `GL_iff_bprovable` and its
  letterless corollaries.
- **Object-theory formalization (`Obj/`)**: internal development over any
  judgment with the rules of `ObjEnv` (`Typing`), full typing or the fragment, of an ordered
  environment containing `Nat`:
  - *Logic and proof mode* (`Attr`, `Typing`, `Core`, `Tactic`, `Iota`, `Logic`): natural
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
  - *Checking codes* (`Leaf`, `Checker`, `BChecker`): the bounds of `BDefEq` at symbolic
    certificates, the interface `IsChecker` of a proof checker the theory reasons about, and
    its instances `chkT T` and `bchkT T`.
  - *Internal Σ₁-completeness, second theorem and Löb's theorem* (`Graph`,
    `Sigma`, `Reduce`, `Second`, `Loeb`, `Omega`): internal graph proofs
    (`ok_exists`) showing every `PR` code provably computes its values on
    numerals, yielding `Con T → G0 T` (`con_imp_G0_provable`) and
    `second_incompleteness`; for the Löb machine `loebM` searching for proofs
    of `haltsE d ⌜d⌝ → P`, `loeb`; and the ω-inconsistent context `[Prov T ⊥]`
    (`omega_inconsistent`).
  - *Provability logic* (`Derivability`, `GL`): the derivability conditions,
    formalized Löb, arithmetical soundness of GL and iGL, and `fairbot`, for any checking
    code.
  - *Arithmetical completeness* (`SolovayCode`, `SolovayStep`,
    `SolovayLemmas`, `Solovay`): Solovay's walk on a finite frame, as a `PR`
    code that finds the numbers of the sentences about itself from its input
    and its external behaviour; its step read inside the theory; Solovay's
    lemmas about the sentences `S_b`; the truth lemma; and
    `GL_arith_complete`.
  - *Letterless sentences* (`Letterless`): provability decided by the level tower, truth by its
    limit, and iterated consistency.
- **Modal logic (`Modal/`)**, independent of the object theory: `Modal`,
  `GL` and `iGL` (`Basic`); derivations from hypotheses, the deduction
  theorem, the 4 axiom and the Lindenbaum step (`Deduction`); Kripke models,
  forcing and soundness (`Kripke`); completeness for finite rooted models
  (`Complete`); and letterless formulas, the level tower and the height lemma (`Letterless`).

## License

Apache 2.0, matching lean4lean (`LICENSE`).
