# incomplete

Lean 4 proofs of classical incompleteness and provability-logic theorems for **Lean 4's formal type theory**, specified by the declarative typing judgment of [lean4lean](https://github.com/digama0/lean4lean) (extended with concrete inductive declarations and primitive projections in [typhdotcom/lean4lean](https://github.com/typhdotcom/lean4lean)):

- **Gödel–Kleene, Rosser, and Gödel's second** incompleteness theorems, plus a consistent ω-inconsistent context;
- **Löb's theorem**, the Hilbert–Bernays–Löb derivability conditions, and **Solovay's arithmetical completeness theorem** for the provability logic **GL** (alongside finite Kripke completeness and a decision procedure and truth theorem for letterless sentences);
- **Chaitin's incompleteness theorem** on program-size complexity.

> [!NOTE]
> Provability is defined directly against `VEnv.HasType` / `VEnv.IsDefEq` in `Lean4Lean.Theory.Typing`. These results concern that formal specification of Lean's type theory, not Lean's C++ kernel or lean4lean's executable kernel replica.

## Scope

The library works in two regimes at once, keeping full and bounded provability strictly distinct:

1. **Full theory (well-formed extensions of `Nat`)**: theorems apply to any well-formed environment (`env.WF`) extending [`natEnv`](Incomplete/NatEnv.lean#L80) — arbitrary axioms, definitions, mutual blocks, opaques, quotients, inductive families, and structures with primitive projections. Neither consistency nor halting soundness is proved here for full `Provable env`; they appear as explicit hypotheses where needed, and [`second_incompleteness`](Incomplete/Obj/Second.lean#L200-L203) shows that no consistent well-formed extension of `natEnv` proves its own internal consistency sentence `Con T`.
2. **Unconditional fragment (zero hypotheses)**: restricting derivations to sorts `Prop` and `Type` (`u ≤ 1`) without primitive projections ([`BProvable`](Incomplete/Bounded.lean#L49)) keeps all of arithmetic, proof checking, Solovay's walk, and Chaitin's machine intact while admitting a ZF set model ([ModelSound.lean](Incomplete/ModelSound.lean)). That model proves consistency and Σ₁-soundness outright for both `natEnv` and [`clEnv`](Incomplete/ClEnv.lean#L18) (`natEnv` plus double-negation elimination [`dneS`](Incomplete/Obj/GL.lean#L22)).

The matrix below lists only consistency, halting-soundness, and classical-axiom hypotheses (`None` means none of those three). All full-judgment rows also take `env.WF` and `natEnv ≤ env` (or `env.WF' ds` with `.induct natDecl ∈ ds`); statements mentioning `Con T`, `Prov T`, or `A.real T σ` take `TablesFor env T` (except [`prov_mp_provable`](Incomplete/Obj/Derivability.lean#L140-L142), which holds for any `T : Tables`, and [`second_incompleteness`](Incomplete/Obj/Second.lean#L200-L203) and [`omega_inconsistent_exists`](Incomplete/Obj/Omega.lean#L60-L64), which construct `T` from `hwf.checkable.tables`); and statements quantified over object propositions or modal realizations take closed-proposition typing (`env.HasType 0 [] · (.sort .zero)` in `VEnv`, `BDefEq clEnv [] · · (.sort .zero)` in `clEnv`) and `A.Letterless` where stated.

| Result                                                | Full `VEnv` extra hypotheses                     | `{Prop, Type}` fragment (`BProvable`)                                                                 | Entry points                                                                                                                                                                                                                  |
| :---------------------------------------------------- | :----------------------------------------------- | :---------------------------------------------------------------------------------------------------- | :---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| **1st incompleteness** (Gödel–Kleene)                 | `Consistent` (+ `HaltsSound` for irrefutability) | **Unconditional** (`natEnv`)                                                                          | [`incomplete_of_wf`](Incomplete/Extend.lean#L217-L219), [`incomplete_unconditional`](Incomplete/Unconditional.lean#L65-L67)                                                                                                   |
| **Rosser's theorem** (unprovable & irrefutable)       | `Consistent`                                     | — (`bhaltsSound` covers `natEnv` above)                                                               | [`incomplete_rosser`](Incomplete/Rosser.lean#L431-L433)                                                                                                                                                                       |
| **2nd incompleteness**                                | `Consistent`                                     | **Unconditional** (`clEnv` at `n = 0`: `¬BProvable clEnv (BProv ⊥ → ⊥)`)                              | [`second_incompleteness`](Incomplete/Obj/Second.lean#L200-L203), [`con_unprovable`](Incomplete/Obj/Second.lean#L191-L192), [`bcon_iterated`](Incomplete/BProvLogic.lean#L107-L110)                                            |
| **Consistent, ω-inconsistent context** (`[Prov T ⊥]`) | `Consistent`                                     | — (full-judgment result)                                                                              | [`omega_inconsistent`](Incomplete/Obj/Omega.lean#L50-L54)                                                                                                                                                                     |
| **Löb**, **D1–D3**, **FairBot**, **iGL soundness**    | **None**                                         | **Unconditional** for Löb, D1–D3, iGL ([`IsChecker.bounded`](Incomplete/Obj/BChecker.lean#L101-L102)) | [`loeb`](Incomplete/Obj/Loeb.lean#L394-L396), [`loeb_formalized`](Incomplete/Obj/Derivability.lean#L164-L167), [`iGL_sound`](Incomplete/Obj/GL.lean#L194-L196), [`fairbot`](Incomplete/Obj/GL.lean#L203-L206)                 |
| **GL arithmetical soundness**                         | `Provable env dneS`                              | **Unconditional** (`clEnv`)                                                                           | [`GL_sound`](Incomplete/Obj/GL.lean#L184-L187), [`GL_bsound`](Incomplete/BProvLogic.lean#L43-L44)                                                                                                                             |
| **Solovay completeness of GL** & **letterless truth** | `HaltsSound` + `Provable env dneS`               | **Unconditional** (`clEnv`, `□` as `BProv`)                                                           | [`GL_iff_provable`](Incomplete/Obj/Solovay.lean#L324-L327), [`tr_iff_lim`](Incomplete/Obj/Letterless.lean#L93-L95), [`GL_iff_bprovable`](Incomplete/BProvLogic.lean#L58-L60), [`btr_iff_lim`](Incomplete/BProvLogic.lean#L91) |
| **Iterated consistency** (`□ⁿ⊥`, `□ⁿ⁺¹⊥ → □ⁿ⊥`)       | `HaltsSound` (`Consistent` at `n = 0`)           | **Unconditional** (`clEnv`)                                                                           | [`boxBot_succ_imp_unprovable`](Incomplete/Obj/Letterless.lean#L128-L130), [`bcon_iterated`](Incomplete/BProvLogic.lean#L107-L110)                                                                                             |
| **Chaitin's incompleteness theorem**                  | `Consistent`                                     | **Unconditional** (`clEnv`)                                                                           | [`chaitin`](Incomplete/Chaitin.lean#L138-L142), [`chaitin_unconditional`](Incomplete/Chaitin.lean#L149-L152)                                                                                                                  |

## Theorems

All declarations displayed in the code blocks below live in `Incomplete` (including its `Incomplete.Modal` subnamespace, with `Incomplete.Obj` opened for `Thm`, `neg`, `prfT`, `numT`, `=ₒ`, and `↔ₒ`); the dot-notation helper [`Lean4Lean.VEnv.WF.checkable`](Incomplete/Extend.lean#L207) is defined in `Lean4Lean`. First, the core vocabulary appearing in the statements ([PR.lean](Incomplete/PR.lean), [Sentences.lean](Incomplete/Sentences.lean), [Main.lean](Incomplete/Main.lean), [Bounded.lean](Incomplete/Bounded.lean)):

```lean
-- Primitive recursive codes equipped with one outer unbounded search
def PR.Halts (f : PR) (n : Nat) : Prop := ∃ k, f.eval (val2 k n) = 0
def PR.code  (f : PR) : Nat := encExpr (fn f)

-- Impredicative False, Π₁ non-halting, and negated non-halting (not identified with ∃ in intuitionistic Prop)
def falseS : VExpr := .forallE (.sort .zero) (.bvar 0)
def notHalts (f : PR) (n : Nat) : VExpr :=
  .forallE nat (.forallE (isZero (.app (.app (fn f) (lit n)) (.bvar 0))) falseS)
def halts (f : PR) (n : Nat) : VExpr := .forallE (notHalts f n) falseS

-- Closed proofs in full typing vs. the {Prop, Type} projection-free judgment BDefEq
def Provable  (env : VEnv) (P : VExpr) : Prop := ∃ e, env.HasType 0 [] e P
def BProvable (env : VEnv) (P : VExpr) : Prop := ∃ e, BDefEq env [] e e P

def Consistent (env : VEnv) : Prop := ¬Provable env falseS
def HaltsSound (env : VEnv) : Prop := ∀ f n, Provable env (halts f n) → PR.Halts f n
```

### 1. Unconditional fragment and classical provability logic

With consistency and halting soundness discharged by the set model ([ModelSound.lean](Incomplete/ModelSound.lean), [Unconditional.lean](Incomplete/Unconditional.lean), [ClEnv.lean](Incomplete/ClEnv.lean), [BProvLogic.lean](Incomplete/BProvLogic.lean)):

```lean
theorem incomplete_unconditional :
    ∃ d : PR, ¬d.Halts d.code ∧ ¬BProvable natEnv (notHalts d d.code) ∧
      ¬BProvable natEnv (halts d d.code)

theorem bconsistent : ¬BProvable natEnv falseS

theorem bhaltsSound {f : PR} {n : Nat} (hp : BProvable natEnv (halts f n)) : f.Halts n

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

theorem chaitin_unconditional :
    ∃ L, (∀ n, BDefEq clEnv [] (Complex L n) (Complex L n) (.sort .zero)) ∧
      (∀ ns : List Nat, ns.Nodup → (∀ n ∈ ns, ¬IsComplex L n) → ns.length ≤ L + 1) ∧
      (∃ N, ∀ n, N ≤ n → IsComplex L n) ∧ ∀ n, ¬BProvable clEnv (Complex L n)
```

`BProv P` internalizes bounded provability via the fragment's own certificate checker, and `A.breal σ` realizes `□` as `BProv`. On variable-free modal formulas, provability holds iff the formula holds at every natural level `n : Nat` of the ω-tower (`bprovable_iff_lvl`); because `Modal.lvl n A` stabilizes at `Modal.lim A` from box depth [`Modal.bd`](Incomplete/Modal/Letterless.lean#L53) onward ([`Modal.lvl_eq_lim`](Incomplete/Modal/Letterless.lean#L80)), [`Modal.dec`](Incomplete/Modal/Letterless.lean#L84) decides provability by checking only the finite prefix `n ≤ bd A` ([`bprovable_iff_dec`](Incomplete/BProvLogic.lean#L80-L81)). Truth (`Modal.btr`) coincides with `Modal.lim A` (`btr_iff_lim`), and every iterated consistency statement `□ⁿ⁺¹⊥ → □ⁿ⊥` is true and unprovable (`bcon_iterated`, with `n = 0` giving `¬BProv ⊥`).

### 2. Full-theory incompleteness, Rosser, and ω-inconsistency

Every well-formed environment admits finite lookup tables ([`TablesFor`](Incomplete/CertNat.lean#L85)) for its constants, definitional-equality rules, and inductive blocks ([`Lean4Lean.VEnv.WF.checkable`](Incomplete/Extend.lean#L207)). From `T : Tables`, [`Con`](Incomplete/Second.lean#L26) states that no certificate checks as a proof of `⊥`, and [`Prov`](Incomplete/Obj/Loeb.lean#L19) states `∃ k, chkT T (⌜P⌝, k) = 0` using an impredicative `∃` ([Extend.lean](Incomplete/Extend.lean), [Rosser.lean](Incomplete/Rosser.lean), [Obj/Second.lean](Incomplete/Obj/Second.lean), [Obj/Omega.lean](Incomplete/Obj/Omega.lean)):

```lean
theorem incomplete_rosser (env : VEnv) (hwf : env.WF) (hext : natEnv ≤ env) (hC : Consistent env) :
    ∃ d : PR, env.HasType 0 [] (notHalts d d.code) (.sort .zero) ∧ ¬d.Halts d.code ∧
      ¬Provable env (notHalts d d.code) ∧ ¬Provable env (halts d d.code)

theorem incomplete_of_wf (env : VEnv) (hwf : env.WF) (hext : natEnv ≤ env) (hC : Consistent env) :
    ∃ d : PR, ¬d.Halts d.code ∧ ¬Provable env (notHalts d d.code) ∧
      (HaltsSound env → ¬Provable env (halts d d.code))

theorem second_incompleteness (env : VEnv) (hwf : env.WF) (hext : natEnv ≤ env)
    (hC : Consistent env) :
    ∃ T, TablesFor env T ∧ env.HasType 0 [] (Con T) (.sort .zero) ∧
      (¬(conM T).Halts 0 ↔ Consistent env) ∧ ¬Provable env (Con T)

theorem con_unprovable (env : VEnv) (hwf : env.WF) (hext : natEnv ≤ env)
    {T : Tables} (hT : TablesFor env T) (hC : Consistent env) : ¬Provable env (Con T)

theorem omega_inconsistent (env : VEnv) (hwf : env.WF) (hext : natEnv ≤ env) {T : Tables}
    (hT : TablesFor env T) (hC : Consistent env) :
    ¬Thm env [Prov T falseS] falseS ∧
    Thm env [Prov T falseS] (Prov T falseS) ∧
    ∀ k : Nat, Thm env [Prov T falseS] (neg (prfT T (numT (encExpr falseS)) (lit k) =ₒ zero))
```

The second theorem rests on proving `Con T → G0 T` inside the object theory ([`con_imp_G0_provable`](Incomplete/Obj/Second.lean#L177-L178)). In [`omega_inconsistent`](Incomplete/Obj/Omega.lean#L50-L54), `[Prov T ⊥]` is a hypothesis context over `env` itself (consistent by Löb at `P := ⊥`), proving that some certificate checks as a proof of `⊥` while refuting each numeral `k` ([`omega_inconsistent_exists`](Incomplete/Obj/Omega.lean#L60-L64) existentially supplies `T` from `env.WF`). Declaration-list variants ([`incomplete_rosser'`](Incomplete/Rosser.lean#L440-L443), [`incomplete_of_wf'`](Incomplete/Extend.lean#L284-L287), [`second_incompleteness'`](Incomplete/Obj/Second.lean#L210-L213)) replace `(hwf : env.WF) (hext : natEnv ≤ env)` with `(H : env.WF' ds) (hm : .induct natDecl ∈ ds)`.

### 3. Löb's theorem, derivability conditions, and Solovay completeness

Because the object logic is intuitionistic, Löb's theorem, the Hilbert–Bernays–Löb conditions D1–D3 ([`prov_of_provable`](Incomplete/Obj/Loeb.lean#L325-L326), [`prov_mp_provable`](Incomplete/Obj/Derivability.lean#L140-L142), [`prov_prov_provable`](Incomplete/Obj/Derivability.lean#L153-L155)), formalized Löb, and intuitionistic **iGL** soundness require neither consistency nor `dneS`. Classical **GL** soundness adds `Provable env dneS`, and Solovay's arithmetical completeness adds `HaltsSound env` ([Obj/Loeb.lean](Incomplete/Obj/Loeb.lean), [Obj/Derivability.lean](Incomplete/Obj/Derivability.lean), [Obj/GL.lean](Incomplete/Obj/GL.lean), [Obj/Solovay.lean](Incomplete/Obj/Solovay.lean)):

```lean
theorem loeb (env : VEnv) (hwf : env.WF) (hext : natEnv ≤ env) {T : Tables}
    (hT : TablesFor env T) {P : VExpr} (hP : env.HasType 0 [] P (.sort .zero))
    (h : Provable env (.forallE (Prov T P) P)) : Provable env P

theorem prov_mp_provable (env : VEnv) (hwf : env.WF) (hext : natEnv ≤ env) {T : Tables}
    {P Q : VExpr} (hQ : env.HasType 0 [] Q (.sort .zero)) :
    Provable env (.forallE (Prov T (.forallE P Q)) (.forallE (Prov T P) (Prov T Q)))

theorem prov_prov_provable (env : VEnv) (hwf : env.WF) (hext : natEnv ≤ env) {T : Tables}
    (hT : TablesFor env T) (P : VExpr) :
    Provable env (.forallE (Prov T P) (Prov T (Prov T P)))

theorem loeb_formalized (env : VEnv) (hwf : env.WF) (hext : natEnv ≤ env) {T : Tables}
    (hT : TablesFor env T) {P : VExpr} (hP : env.HasType 0 [] P (.sort .zero)) :
    Provable env (.forallE (Prov T (.forallE (Prov T P) P)) (Prov T P))

theorem GL_iff_provable (env : VEnv) (hwf : env.WF) (hext : natEnv ≤ env) {T : Tables}
    (hT : TablesFor env T) (hdne : Provable env dneS) (hS : HaltsSound env) {A : Modal} :
    Modal.GL A ↔ ∀ σ : Nat → VExpr, (∀ n, env.HasType 0 [] (σ n) (.sort .zero)) →
      Provable env (A.real T σ)
```

<details>
<summary>Companion modal, Kripke, FairBot, and letterless signatures (<a href="Incomplete/Modal">Modal/</a>, <a href="Incomplete/Obj/GL.lean">Obj/GL.lean</a>, <a href="Incomplete/Obj/Letterless.lean">Obj/Letterless.lean</a>)</summary>

```lean
-- Arithmetical soundness of GL and iGL, mutual Löb ("FairBot"), and Solovay counter-realization
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

theorem GL_arith_complete (env : VEnv) (hwf : env.WF) (hext : natEnv ≤ env) {T : Tables}
    (hT : TablesFor env T) (hdne : Provable env dneS) (hS : HaltsSound env) {A : Modal}
    (h : ¬Modal.GL A) :
    ∃ σ : Nat → VExpr, (∀ n, env.HasType 0 [] (σ n) (.sort .zero)) ∧
      ¬Provable env (A.real T σ)

-- Standalone Kripke completeness of GL on finite transitive irreflexive frames
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

-- Letterless ω-level tower, finite-prefix Boolean decider (n ≤ bd A), limit truth, and □ⁿ⊥
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

[`provable_iff_dec`](Incomplete/Obj/Letterless.lean#L86-L89) equates `Provable env (A.real T σ)` with the finite-prefix check `Modal.dec A = true` (`n ≤ bd A`). On letterless formulas **GL** is strictly stronger than **iGL**: [`Modal.not_iGL_dne_box`](Incomplete/Modal/Letterless.lean#L295-L296) proves `GL (¬¬□⊥ → □⊥)` and `¬iGL (¬¬□⊥ → □⊥)` via a three-element Heyting modal algebra.

</details>

### 4. Chaitin's incompleteness theorem

A number `c` describes `n` when `c` is the numeric Gödel code `f.code` of a machine `f` that, run on `c`, has `n` as the first projection of its least halting witness ([Obj/Chaitin.lean](Incomplete/Obj/Chaitin.lean), [Chaitin.lean](Incomplete/Chaitin.lean)):

```lean
def PR.Outputs (f : PR) (x n : Nat) : Prop :=
  ∃ k, f.eval (val2 k x) = 0 ∧ (∀ j < k, f.eval (val2 j x) ≠ 0) ∧ unpair1 k = n

def Describes (c n : Nat) : Prop := ∃ f : PR, f.code = c ∧ f.Outputs c n

def IsComplex (L n : Nat) : Prop := ∀ c ≤ L, ¬Describes c n

noncomputable def Complex (L n : Nat) : VExpr := bigAnd ((List.range (L + 1)).map (cplxC n))

theorem chaitin (env : VEnv) (hwf : env.WF) (hext : natEnv ≤ env) {T : Tables}
    (hT : TablesFor env T) (hC : Consistent env) :
    ∃ L, (∀ n, env.HasType 0 [] (Complex L n) (.sort .zero)) ∧
      (∀ ns : List Nat, ns.Nodup → (∀ n ∈ ns, ¬IsComplex L n) → ns.length ≤ L + 1) ∧
      (∃ N, ∀ n, N ≤ n → IsComplex L n) ∧ ∀ n, ¬Provable env (Complex L n)
```

Description size here is the numeric code `PR.code` itself (no binary program-length or invariance theorem is claimed). Because codes with the same expression number compute the same function ([`PR.eval_eq_of_code`](Incomplete/Chaitin.lean#L26-L27)), each code describes at most one number, leaving at most `L + 1` numbers below complexity `L` while no `Complex L n` is provable at Chaitin's machine threshold. (See [`chaitin_unconditional`](Incomplete/Chaitin.lean#L149-L152) in Section 1 for the hypothesis-free version in `clEnv`.)

## Design

Four architectural choices keep the development compact despite targeting a dependent type theory rather than first-order arithmetic:

- **`Nat` is the only inductive type required.** Propositional connectives, quantifiers, and Leibniz equality are impredicatively encoded in `Prop`, and `0 ≠ succ n` uses large elimination of `Nat` into `Prop`. Base arithmetic ([`natEnv_wf`](Incomplete/NatDeclWF.lean#L92)) is therefore a single inductive declaration added to the empty environment.
- **Kleene normal form separates recursion from search.** Machines are total primitive recursive terms ([`PR`](Incomplete/PR.lean#L15)) paired with one outer `∃ k` search. Every partial recursive function has this shape, while the object theory only ever evaluates total primitive recursive functions on numerals by β- and ι-conversion ([`PR.adequate`](Incomplete/Adequacy.lean#L128-L129)).
- **Gödel numbering is a bijection.** Names, universe levels, expressions, judgments, and 16-rule derivation trees ([`Cert`](Incomplete/Cert.lean#L44)) map bijectively to `Nat` ([`decCert_enc`](Incomplete/Encode.lean#L382), [`encCert_dec`](Incomplete/Encode.lean#L417)). Every natural number is a valid syntactic object, so neither external nor internal proof checkers need well-formedness guards against junk codes.
- **One internal development serves both regimes.** Object-level proof theory in [Incomplete/Obj/](Incomplete/Obj) (equipped with a custom natural-deduction tactic mode for nameless de Bruijn terms) is parameterized over an abstract typing interface ([`ObjEnv`](Incomplete/Obj/Typing.lean#L41)) and checker interface ([`IsChecker`](Incomplete/Obj/Checker.lean#L33)), instantiated once for full `VEnv` typing and once for `BDefEq` to prove internal Σ₁-completeness ([`ok_exists`](Incomplete/Obj/Sigma.lean#L474)) and everything downstream.

## Layout

Every module in [Incomplete/](Incomplete) opens with a docstring summarizing its definitions and proof idea.

- **External arithmetic, proof checking, and 1st incompleteness**: [PR.lean](Incomplete/PR.lean), [Adequacy.lean](Incomplete/Adequacy.lean), [Sentences.lean](Incomplete/Sentences.lean), [Cert.lean](Incomplete/Cert.lean), [Encode.lean](Incomplete/Encode.lean), [CheckPR.lean](Incomplete/CheckPR.lean), [Kleene.lean](Incomplete/Kleene.lean), [Main.lean](Incomplete/Main.lean), [Final.lean](Incomplete/Final.lean), [Rosser.lean](Incomplete/Rosser.lean).
- **Well-formed environments and extensions**: [NatEnv.lean](Incomplete/NatEnv.lean), [NatDeclWF.lean](Incomplete/NatDeclWF.lean), [Extend.lean](Incomplete/Extend.lean), plus concrete extensions with `Eq` and `And` ([EqEnv.lean](Incomplete/EqEnv.lean), [AndEnv.lean](Incomplete/AndEnv.lean)).
- **Bounded fragment and ZF set model**: [Bounded.lean](Incomplete/Bounded.lean), [ZF.lean](Incomplete/ZF.lean), [ZFUniv.lean](Incomplete/ZFUniv.lean), [Model.lean](Incomplete/Model.lean), [ModelSound.lean](Incomplete/ModelSound.lean), [ClEnv.lean](Incomplete/ClEnv.lean), [Unconditional.lean](Incomplete/Unconditional.lean), [BProvLogic.lean](Incomplete/BProvLogic.lean).
- **Standalone modal logic**: [Incomplete/Modal/](Incomplete/Modal) — Hilbert systems **GL** and **iGL** ([Basic.lean](Incomplete/Modal/Basic.lean)), Kripke frames ([Kripke.lean](Incomplete/Modal/Kripke.lean)), finite rooted completeness ([Complete.lean](Incomplete/Modal/Complete.lean)), and the letterless height tower ([Letterless.lean](Incomplete/Modal/Letterless.lean)).
- **Internalized proof theory**: [Incomplete/Obj/](Incomplete/Obj) — typing and tactics ([Typing.lean](Incomplete/Obj/Typing.lean), [Core.lean](Incomplete/Obj/Core.lean), [Tactic.lean](Incomplete/Obj/Tactic.lean)), symbolic arithmetic and certificate checking ([Checker.lean](Incomplete/Obj/Checker.lean), [BChecker.lean](Incomplete/Obj/BChecker.lean)), internal Σ₁-completeness ([Sigma.lean](Incomplete/Obj/Sigma.lean)), second theorem ([Second.lean](Incomplete/Obj/Second.lean)), Löb and D1–D3 ([Loeb.lean](Incomplete/Obj/Loeb.lean), [Omega.lean](Incomplete/Obj/Omega.lean), [Derivability.lean](Incomplete/Obj/Derivability.lean), [GL.lean](Incomplete/Obj/GL.lean)), Solovay's walk ([Solovay.lean](Incomplete/Obj/Solovay.lean), [Letterless.lean](Incomplete/Obj/Letterless.lean)), and Chaitin's machine ([Obj/Chaitin.lean](Incomplete/Obj/Chaitin.lean), [Chaitin.lean](Incomplete/Chaitin.lean)).

## Dependency

[lakefile.toml](lakefile.toml) pins [typhdotcom/lean4lean](https://github.com/typhdotcom/lean4lean) (a fork of [digama0/lean4lean](https://github.com/digama0/lean4lean)) at [`db323b9f1770`](https://github.com/typhdotcom/lean4lean/commit/db323b9f1770df1bd15c54b01b10eb85a7b0962b). Core typing and definitional equality come from upstream; this repository uses three theory-level additions from the fork:

- **Concrete inductive declarations** (`Theory/VEnv.lean`, `Theory/Inductive.lean`, `Theory/Typing/Env.lean`): `VInductDecl.WF`, recursor and iota-rule generation, `VEnv.addInduct`, and the `GeneratedWF` obligation that generated recursors and iota rules are well typed (discharged for `Nat` in [NatDeclWF.lean](Incomplete/NatDeclWF.lean)).
- **Primitive projections and structure η** (`Theory/Typing/Basic.lean`): `VExpr.proj`, `VEnv.inducts`, and the `IsDefEq` rules `projDF`, `projIota`, and `projEta` with their `ProjAllowed` side conditions (included in the full-theory checker in [Cert.lean](Incomplete/Cert.lean) and [ProjRules.lean](Incomplete/ProjRules.lean), and omitted from `BDefEq`).
- **Environment and telescope lemmas** (`Theory/Typing/{EnvLemmas,Projection,Telescope}.lean`): `VEnv.WF.ordered`, `VDecl.WF.le`, `IsDefEq.appN_substT`, and `IsDefEq.lams_beta`.

The proofs do not depend on the fork's kernel verification, runtime-model axioms, or open injectivity assumptions; direct imports are limited to `Lean4Lean.Theory.Typing.{Basic,Env,EnvLemmas,Meta,Projection,Telescope}`. The toolchain is Lean `v4.34.1` ([lean-toolchain](lean-toolchain)) with `batteries` `v4.34.0`; lean4lean itself pins `v4.33.0-rc2` for its kernel replica and regression tests.

## Build and audit

```nu
nix develop -c lake build
nu tasks.nu fmt
nu tasks.nu check
```

Every theorem depends only on `propext`, `Classical.choice`, and `Quot.sound`. The codebase contains no `sorry`, `native_decide`, or custom `axiom`.

Markdown links to Lean declarations are managed automatically ([nix/lean-anchors.py](nix/lean-anchors.py)): write single-line `` [`symbol`](Incomplete/File.lean) `` or `[label](Incomplete/File.lean "lean:symbol")` (titles without the `lean:` prefix remain ordinary tooltips on file links). After editing Lean or Markdown sources, run `nu tasks.nu fmt` (`nix fmt`) to refresh `#L` signature spans and table alignment, then `nu tasks.nu check` (`nix flake check`) to verify formatting, symbol spans (`checks.lean-anchors`), and relative file and heading links (`checks.links`). Unmanaged, reference-style, or multiline `.lean#...` line links are rejected.

<details>
<summary>Full <code>#print axioms</code> audit script (run with <code>nix develop -c lake env lean --trust=0 &lt;file&gt;</code>)</summary>

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
#print axioms chaitin
#print axioms chaitin_unconditional
```

</details>

## License

Apache 2.0 ([LICENSE](LICENSE)), matching lean4lean.
