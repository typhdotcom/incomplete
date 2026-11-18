import Incomplete.Obj.Typing
import Incomplete.Obj.Attr

/-!
# Object-level proofs: formulas, typing, derived rules

`Thm env Γ P` says `P` has a proof in context `Γ`. The formula constructors are implication
`imp`, quantification over `Nat` `all`, and Leibniz equality `EqN`; the rules below are natural
deduction over them in an arbitrary context, with induction by `Nat.rec` into `Prop` (`Thm.ind`).
Every rule takes typing side conditions on the terms it mentions, which `otype` proves.
-/

namespace Incomplete.Obj
open Lean4Lean
open VExpr Typing

/-! ### Formulas -/

/-- `P → Q`, with `Q` in the context of `P`'s, not depending on the proof. -/
def imp (P Q : VExpr) : VExpr := .forallE P Q.lift

/-- `∀ x : Nat, P`. -/
def all (P : VExpr) : VExpr := .forallE nat P

/-- `Nat → Prop`. -/
def predTy : VExpr := .forallE nat (.sort .zero)

/-- Leibniz equality: `∀ M : Nat → Prop, M a → M b`. -/
def EqN (a b : VExpr) : VExpr := .forallE predTy (imp (.app (.bvar 0) a.lift) (.app (.bvar 0) b.lift))

/-- A binary function applied. -/
def app2 (f a b : VExpr) : VExpr := .app (.app f a) b

/-- The successor applied. -/
def S (a : VExpr) : VExpr := .app succ a

/-- `a` is a term of `Nat` in context `Γ`. -/
abbrev Tm (env : Typing) (Γ : List VExpr) (a : VExpr) : Prop := env.HasType Γ a nat

/-- `Thm env Γ P`: the formula `P` has a proof in context `Γ`. -/
def Thm (env : Typing) (Γ : List VExpr) (P : VExpr) : Prop := ∃ p, env.HasType Γ p P

theorem Thm.provable {env : VEnv} {P : VExpr} (h : Thm env [] P) : Provable env P := h

theorem Thm.ofProvable {env : VEnv} {P : VExpr} (h : Provable env P) : Thm env [] P := h

theorem Thm.bprovable_iff {env : VEnv} {P : VExpr} : Thm (bounded env) [] P ↔ BProvable env P :=
  Iff.rfl

/-- A theorem of the judgment is a theorem of full typing. -/
theorem Thm.toFull {env : Typing} [E : ObjEnv env] {Γ : List VExpr} {P : VExpr} (h : Thm env Γ P) :
    Thm env.env Γ P :=
  let ⟨_, hp⟩ := h; ⟨_, E.toFull hp⟩

/-! ### Lifting and instantiation -/

section
variable {n k : Nat} {e a b f P Q : VExpr}

attribute [obj_simp] Nat.reduceLT Nat.reduceEqDiff Nat.reduceSub Nat.reduceAdd Nat.lt_irrefl
  Nat.not_lt_zero reduceIte ite_true ite_false

@[obj_simp] theorem bvar_liftN' : (VExpr.bvar i).liftN n k = .bvar (if i < k then i else n + i) :=
  rfl
@[obj_simp] theorem bvar_inst' :
    (VExpr.bvar i).inst e k = if i < k then .bvar i else if i = k then e.liftN k else .bvar (i - 1) :=
  rfl
@[obj_simp] theorem app_liftN' : (VExpr.app f a).liftN n k = .app (f.liftN n k) (a.liftN n k) := rfl
@[obj_simp] theorem app_inst' : (VExpr.app f a).inst e k = .app (f.inst e k) (a.inst e k) := rfl
@[obj_simp] theorem lam_liftN' : (VExpr.lam P Q).liftN n k = .lam (P.liftN n k) (Q.liftN n (k+1)) := rfl
@[obj_simp] theorem lam_inst' : (VExpr.lam P Q).inst e k = .lam (P.inst e k) (Q.inst e (k+1)) := rfl
@[obj_simp] theorem forallE_liftN' :
    (VExpr.forallE P Q).liftN n k = .forallE (P.liftN n k) (Q.liftN n (k+1)) := rfl
@[obj_simp] theorem forallE_inst' : (VExpr.forallE P Q).inst e k = .forallE (P.inst e k) (Q.inst e (k+1)) :=
  rfl
@[obj_simp] theorem sort_liftN' : (VExpr.sort u).liftN n k = .sort u := rfl
@[obj_simp] theorem sort_inst' : (VExpr.sort u).inst e k = .sort u := rfl

attribute [obj_simp] nat_liftN nat_inst zero_liftN zero_inst succ_liftN succ_inst liftN_zero
  inst_lift inst_liftN_lo natRec_inst

@[obj_simp] theorem lit_liftN (m : Nat) : (lit m).liftN n k = lit m := (Inert.lit m).liftN n k
@[obj_simp] theorem lit_inst (m : Nat) : (lit m).inst e k = lit m := (Inert.lit m).inst e k

@[obj_simp] theorem imp_liftN : (imp P Q).liftN n k = imp (P.liftN n k) (Q.liftN n k) := by
  simp only [imp, VExpr.liftN, lift_liftN']
@[obj_simp] theorem imp_inst : (imp P Q).inst e k = imp (P.inst e k) (Q.inst e k) := by
  simp only [imp, VExpr.inst, lift_instN_lo]
@[obj_simp] theorem all_liftN : (all P).liftN n k = all (P.liftN n (k+1)) := rfl
@[obj_simp] theorem all_inst : (all P).inst e k = all (P.inst e (k+1)) := rfl
@[obj_simp] theorem predTy_liftN : predTy.liftN n k = predTy := rfl
@[obj_simp] theorem predTy_inst : predTy.inst e k = predTy := rfl
@[obj_simp] theorem EqN_liftN : (EqN a b).liftN n k = EqN (a.liftN n k) (b.liftN n k) := by
  simp only [EqN, VExpr.liftN, imp_liftN, lift_liftN', liftVar_zero]; rfl
@[obj_simp] theorem EqN_inst : (EqN a b).inst e k = EqN (a.inst e k) (b.inst e k) := by
  simp only [EqN, VExpr.inst, imp_inst, lift_instN_lo, instVar_lower]; rfl
@[obj_simp] theorem app2_liftN : (app2 f a b).liftN n k = app2 (f.liftN n k) (a.liftN n k) (b.liftN n k) :=
  rfl
@[obj_simp] theorem app2_inst : (app2 f a b).inst e k = app2 (f.inst e k) (a.inst e k) (b.inst e k) := rfl
@[obj_simp] theorem S_liftN : (S a).liftN n k = S (a.liftN n k) := rfl
@[obj_simp] theorem S_inst : (S a).inst e k = S (a.inst e k) := rfl

theorem EqN_lift : (EqN a b).lift = EqN a.lift b.lift := EqN_liftN

/-- Lifts of a lifted term are normalized to iterated `lift`s. -/
@[obj_simp] theorem liftN_lift_succ : (e.liftN 1 0).liftN n (k + 1) = (e.liftN n k).liftN 1 0 :=
  (lift_liftN' e k).symm
@[obj_simp] theorem liftN_succ_zero : e.liftN (n + 2) 0 = (e.liftN (n + 1) 0).liftN 1 0 :=
  liftN_succ e (n + 1)
@[obj_simp] theorem inst_lift_succ : (e.liftN 1 0).inst a (k + 1) = (e.inst a k).liftN 1 0 :=
  (lift_instN_lo e a).symm

end

/-! ### Typing -/

section
variable {env : Typing} [E : ObjEnv env] {Γ : List VExpr}

theorem natTy : env.HasType Γ nat (.sort (.succ .zero)) := natT
theorem zeroTy : env.HasType Γ zero nat := zeroT
theorem litTy (m : Nat) : env.HasType Γ (lit m) nat := litNatT m
theorem STy (ha : env.HasType Γ a nat) : env.HasType Γ (S a) nat := .app' succT ha rfl
theorem predTyTy : env.HasType Γ predTy (.sort (.imax (.succ .zero) (.succ .zero))) :=
  .forallE natTy .sort0

theorem app2Ty (hf : env.HasType Γ f (.forallE nat (.forallE nat nat)))
    (ha : env.HasType Γ a nat) (hb : env.HasType Γ b nat) :
    env.HasType Γ (app2 f a b) nat :=
  .app' (.app' hf ha rfl) hb rfl

theorem weakTy (h : env.HasType Γ e A) : env.HasType (B :: Γ) e.lift A.lift :=
  IsDefEq.weak h

theorem closedTy (h : env.HasType [] e A) : env.HasType Γ e A := h.weak0

theorem impTy (hP : env.HasType Γ P (.sort .zero)) (hQ : env.HasType Γ Q (.sort .zero)) :
    env.HasType Γ (imp P Q) (.sort .zero) :=
  forallE_prop hP (weakTy hQ)

theorem allTy (hP : env.HasType (nat :: Γ) P (.sort .zero)) :
    env.HasType Γ (all P) (.sort .zero) :=
  forallE_prop natTy hP

theorem predAppTy (ha : env.HasType Γ a nat) :
    env.HasType (predTy :: Γ) (.app (.bvar 0) a.lift) (.sort .zero) :=
  .app' (.bvar .zero) (weakTy ha) rfl

theorem EqNTy (ha : env.HasType Γ a nat) (hb : env.HasType Γ b nat) :
    env.HasType Γ (EqN a b) (.sort .zero) :=
  forallE_prop predTyTy (impTy (predAppTy ha) (predAppTy hb))

theorem instTy (h : env.HasType (A :: Γ) e B) (ha : env.HasType Γ a A) :
    env.HasType Γ (e.inst a) (B.inst a) :=
  h.instN .zero ha

end

/-- `Lookup Γ i A`, checking each lift by `simp` rather than by unfolding. -/
syntax "olookup" : tactic
macro_rules | `(tactic| olookup) => `(tactic| first
  | (refine VEnv.Lookup.zero' ?_; first | with_reducible rfl | (simp only [obj_simp]; done))
  | (refine VEnv.Lookup.succ' (ty := ?_) ?_ ?_ <;>
      [skip; olookup; first | with_reducible rfl | (simp only [obj_simp]; done)]))

/-- The rules of `otype`, tried in turn; extended with `macro_rules`. -/
syntax "otype_rules" : tactic

/-- Proves `HasType env 0 Γ e A` for object terms and formulas: by the typing lemma of the head
of `e` (`otype_head`), and otherwise by `otype_rules`. -/
syntax "otype" : tactic

open Lean Meta Elab Tactic in
/-- The typing lemma for a term or formula with head `c`, of which `T` is the type. -/
def otypeLemma (c : Name) (args : Array Expr) (T : Expr) : MetaM (Option Name) := do
  let some n := (match c with
    | ``Incomplete.zero => some `Incomplete.Obj.zeroTy
    | ``Incomplete.nat => some `Incomplete.Obj.natTy
    | ``Incomplete.lit => some `Incomplete.Obj.litTy
    | ``Incomplete.fn => some `Incomplete.Obj.fnTy
    | ``Incomplete.falseS => some `Incomplete.Obj.falseTy
    | `Incomplete.Obj.S => some `Incomplete.Obj.STy
    | `Incomplete.Obj.add => some `Incomplete.Obj.addTy
    | `Incomplete.Obj.mul => some `Incomplete.Obj.mulTy
    | `Incomplete.Obj.sub => some `Incomplete.Obj.subTy
    | `Incomplete.Obj.pred => some `Incomplete.Obj.predTy'
    | `Incomplete.Obj.app2 => some `Incomplete.Obj.app2Ty
    | `Incomplete.Obj.ev => some `Incomplete.Obj.evTy
    | `Incomplete.Obj.EqN => some `Incomplete.Obj.EqNTy
    | `Incomplete.Obj.imp => some `Incomplete.Obj.impTy
    | `Incomplete.Obj.all => some `Incomplete.Obj.allTy
    | `Incomplete.Obj.neg => some `Incomplete.Obj.negTy
    | `Incomplete.Obj.conj => some `Incomplete.Obj.conjTy
    | `Incomplete.Obj.disj => some `Incomplete.Obj.disjTy
    | `Incomplete.Obj.ex => some `Incomplete.Obj.exTy
    | `Incomplete.Obj.iff => some `Incomplete.Obj.iffTy
    | ``VExpr.lift | ``VExpr.liftN =>
      if c == ``VExpr.liftN && !(args.size == 3 && args[0]!.nat? == some 1 && args[2]!.nat? == some 0)
      then none
      else if T.isConstOf ``Incomplete.nat then some `Incomplete.Obj.weakNat
      else if T == mkApp (mkConst ``VExpr.sort) (mkConst ``VLevel.zero) then
        some `Incomplete.Obj.weakProp
      else some ``Incomplete.Obj.weakTy
    | _ => none) | return none
  return if (← getEnv).contains n then some n else none

open Lean Meta Elab Tactic in
/-- Type a term or formula by a hypothesis, or by the typing lemma of its head and then its parts
by `otype`. -/
elab "otype_head" : tactic => withMainContext do
  let g ← getMainGoal
  let rest := (← getGoals).tail
  let tgt ← whnfR (← instantiateMVars (← g.getType))
  let n ← match_expr tgt with
    | Typing.HasType _ _ e T =>
      if (← try withReducible g.assumption; pure true catch _ => pure false) then
        setGoals rest; return
      if e.isAppOfArity ``VExpr.bvar 1 then
        evalTactic (← `(tactic| ((with_reducible refine HasType.bvar ?_); olookup)))
        return
      let .const c _ := e.getAppFn | throwError "otype_head: no head"
      let some n ← otypeLemma c e.getAppArgs T | throwError "otype_head: no lemma for {c}"
      pure n
    | _ =>
      let some l := tgt.getAppArgs.back? | throwError "otype_head: not a typing"
      unless tgt.isAppOfArity `Incomplete.Obj.Tms 3 do throwError "otype_head: not a typing"
      if l.isAppOfArity ``List.nil 1 then pure `Incomplete.Obj.Tms.nil
      else if l.isAppOfArity ``List.cons 3 then pure `Incomplete.Obj.Tms.cons
      else throwError "otype_head: list {l}"
  let gs ← withReducible (g.apply (← mkConstWithFreshMVarLevels n))
  for g in gs do
    unless ← g.isAssigned do
      setGoals [g]
      evalTactic (← `(tactic| otype))
  setGoals rest

macro_rules | `(tactic| otype) => `(tactic| first | otype_head | otype_rules)

macro_rules | `(tactic| otype_rules) => `(tactic| with_reducible assumption)
macro_rules | `(tactic| otype_rules) => `(tactic| with_reducible exact natTy)
macro_rules | `(tactic| otype_rules) => `(tactic| with_reducible exact zeroTy)
macro_rules | `(tactic| otype_rules) => `(tactic| ((with_reducible refine STy ?_); otype))
macro_rules | `(tactic| otype_rules) => `(tactic| ((with_reducible refine HasType.bvar ?_); olookup))
macro_rules | `(tactic| otype_rules) => `(tactic| with_reducible exact litTy _)
macro_rules | `(tactic| otype_rules) => `(tactic| ((with_reducible refine app2Ty ?_ ?_ ?_) <;> otype))
macro_rules | `(tactic| otype_rules) => `(tactic| ((with_reducible refine impTy ?_ ?_) <;> otype))
macro_rules | `(tactic| otype_rules) => `(tactic| ((with_reducible refine allTy ?_); otype))
macro_rules | `(tactic| otype_rules) => `(tactic| ((with_reducible refine EqNTy ?_ ?_) <;> otype))
macro_rules | `(tactic| otype_rules) => `(tactic| ((with_reducible refine weakTy ?_); otype))

/-! ### Conversion -/

section
variable {env : Typing} [E : ObjEnv env] {Γ : List VExpr}

theorem IsDefEq.toProp (h : env.IsDefEq Γ e e' (.sort (.imax u .zero))) (hu : u.WF 0 := by trivial) :
    env.IsDefEq Γ e e' (.sort .zero) :=
  .defeqDF (.sortDF (l := .imax u .zero) (l' := .zero) ⟨hu, trivial⟩ trivial (VLevel.equiv_def.2 fun _ => by
    simp [VLevel.eval, Lean.Nat.imax]) (by simp [VLevel.eval, Lean.Nat.imax])) h

theorem EqN_congr (ha : env.IsDefEq Γ a a' nat) (hb : env.IsDefEq Γ b b' nat) :
    env.IsDefEq Γ (EqN a b) (EqN a' b') (.sort .zero) := by
  have hP : env.HasType (predTy :: Γ) (.bvar 0) (.forallE nat (.sort .zero)) := .bvar .zero
  have h1 : env.IsDefEq (predTy :: Γ) (.app (.bvar 0) a.lift) (.app (.bvar 0) a'.lift)
      (.sort .zero) := .appDF hP (IsDefEq.weak ha)
  have h2 : env.IsDefEq (predTy :: Γ) (.app (.bvar 0) b.lift) (.app (.bvar 0) b'.lift)
      (.sort .zero) := .appDF hP (IsDefEq.weak hb)
  have h3 : env.IsDefEq (predTy :: Γ) (imp (.app (.bvar 0) a.lift) (.app (.bvar 0) b.lift))
      (imp (.app (.bvar 0) a'.lift) (.app (.bvar 0) b'.lift)) (.sort .zero) :=
    IsDefEq.toProp (.forallEDF h1 (IsDefEq.weak h2))
  exact IsDefEq.toProp (.forallEDF predTyTy h3)

end

/-! ### Rules -/

namespace Thm
variable {env : Typing} [E : ObjEnv env] {Γ : List VExpr} {P Q a b c : VExpr}

omit E in
theorem cast (h : Thm env Γ P) (e : P = Q) : Thm env Γ Q := e ▸ h

theorem conv (h : Thm env Γ P) (e : env.IsDefEq Γ P Q (.sort u)) : Thm env Γ Q :=
  let ⟨_, hp⟩ := h; ⟨_, e.defeq hp⟩

theorem intro (hP : env.HasType Γ P (.sort .zero)) (h : Thm env (P :: Γ) Q.lift) :
    Thm env Γ (imp P Q) :=
  let ⟨_, hq⟩ := h; ⟨_, .lam hP hq⟩

/-- `intro`, naming the hypothesis: `k` gets the proof of `P` in the extended context. -/
theorem introH (hP : env.HasType Γ P (.sort .zero))
    (k : Thm env (P :: Γ) P.lift → Thm env (P :: Γ) Q.lift) : Thm env Γ (imp P Q) :=
  intro hP (k ⟨_, .bvar .zero⟩)

theorem mp (h1 : Thm env Γ (imp P Q)) (h2 : Thm env Γ P) : Thm env Γ Q :=
  let ⟨_, hf⟩ := h1; let ⟨_, ha⟩ := h2; ⟨_, .app' hf ha (inst_lift ..)⟩

theorem hyp (h : Lookup Γ i P) : Thm env Γ P := ⟨_, .bvar h⟩

theorem allI (h : Thm env (nat :: Γ) P) : Thm env Γ (all P) :=
  let ⟨_, hp⟩ := h; ⟨_, .lam natTy hp⟩

theorem allE (h : Thm env Γ (all P)) (ht : env.HasType Γ t nat) : Thm env Γ (P.inst t) :=
  let ⟨_, hp⟩ := h; ⟨_, .app hp ht⟩

theorem weak (h : Thm env Γ P) : Thm env (A :: Γ) P.lift :=
  let ⟨_, hp⟩ := h; ⟨_, weakTy hp⟩

theorem weakL : ∀ (Δ : List VExpr) {Γ : List VExpr} {P : VExpr}, Thm env Γ P →
    Thm env (Δ ++ Γ) (P.liftN Δ.length)
  | [], _, _, h => by simpa only [List.nil_append, List.length_nil, liftN_zero] using h
  | A :: Δ, _, _, h => by
    have := (weakL Δ h).weak (A := A)
    rwa [VExpr.lift, liftN_liftN] at this

theorem weak0 (h : Thm env [] P) : Thm env Γ P :=
  let ⟨_, hp⟩ := h; ⟨_, closedTy hp⟩

/-! #### Equality -/

theorem refl (ha : env.HasType Γ a nat) : Thm env Γ (EqN a a) :=
  ⟨.lam predTy (.lam (.app (.bvar 0) a.lift) (.bvar 0)),
    .lam predTyTy (.lam (predAppTy ha) (.bvar .zero))⟩

theorem ofDefEq (h : env.IsDefEq Γ a b nat) : Thm env Γ (EqN a b) :=
  (refl h.hasType.1).conv (EqN_congr h.hasType.1 h)

/-- Leibniz's rule, at a motive `M` over `Nat`. -/
theorem subst (hM : env.HasType (nat :: Γ) M (.sort .zero)) (h : Thm env Γ (EqN a b))
    (ha : env.HasType Γ a nat) (hb : env.HasType Γ b nat)
    (hMa : Thm env Γ (M.inst a)) : Thm env Γ (M.inst b) := by
  have hL : env.HasType Γ (.lam nat M) predTy := .lam natTy hM
  have h1 : Thm env Γ (imp (.app (.lam nat M) a) (.app (.lam nat M) b)) := by
    obtain ⟨_, hp⟩ := h
    exact ⟨_, .app' hp hL (by simp only [imp_inst, VExpr.inst, instVar_zero, inst_lift])⟩
  exact (h1.mp (hMa.conv (IsDefEq.beta hM ha).symm)).conv (IsDefEq.beta hM hb)

theorem symm (ha : env.HasType Γ a nat) (hb : env.HasType Γ b nat)
    (h : Thm env Γ (EqN a b)) : Thm env Γ (EqN b a) := by
  have := subst (M := EqN (.bvar 0) a.lift) (EqNTy (.bvar .zero) (weakTy ha)) h ha hb
  simp only [obj_simp] at this
  exact this (refl ha)

theorem trans (ha : env.HasType Γ a nat) (hb : env.HasType Γ b nat)
    (hc : env.HasType Γ c nat)
    (h1 : Thm env Γ (EqN a b)) (h2 : Thm env Γ (EqN b c)) : Thm env Γ (EqN a c) := by
  have := subst (M := EqN a.lift (.bvar 0)) (EqNTy (weakTy ha) (.bvar .zero)) h2 hb hc
  simp only [obj_simp] at this
  exact this h1

/-- Congruence, at a term `f` over `Nat`. -/
theorem congr (hf : env.HasType (nat :: Γ) f nat) (ha : env.HasType Γ a nat)
    (hb : env.HasType Γ b nat) (h : Thm env Γ (EqN a b)) :
    Thm env Γ (EqN (f.inst a) (f.inst b)) := by
  have hfa : env.HasType Γ (f.inst a) nat := instTy hf ha
  have := subst (M := EqN (f.inst a).lift f) (EqNTy (weakTy hfa) hf) h ha hb
  simp only [EqN_inst, inst_lift] at this
  exact this (refl hfa)

/-- Rewriting: a formula about `b` follows from one about `a` and `a = b`. -/
theorem rewrite (hM : env.HasType (nat :: Γ) M (.sort .zero)) (ha : env.HasType Γ a nat)
    (hb : env.HasType Γ b nat) (h : Thm env Γ (EqN a b)) (hG : M.inst a = G)
    (hM' : Thm env Γ (M.inst b)) : Thm env Γ G :=
  hG ▸ subst hM (symm ha hb h) hb ha hM'

/-! #### Induction -/

/-- `Nat.rec.{0}` at an open motive `M`: `M 0 → (∀ n, M n → M (n+1)) → ∀ n, M n`. -/
theorem recApp {M z s : VExpr} (hM : env.HasType Γ M predTy) (hz : env.HasType Γ z (.app M zero))
    (hs : env.HasType Γ s
      (.forallE nat (.forallE (.app M.lift (.bvar 0)) (.app (M.liftN 2) (.app succ (.bvar 1)))))) :
    env.HasType Γ (.app (.app (.app (.const ``Nat.rec [.zero]) M) z) s)
      (.forallE nat (.app M.lift (.bvar 0))) := by
  have h0 : env.HasType Γ (.const ``Nat.rec [.zero])
      (.forallE predTy (.forallE (.app (.bvar 0) zero)
        (.forallE (.forallE nat (.forallE (.app (.bvar 2) (.bvar 0))
          (.app (.bvar 3) (.app succ (.bvar 1))))) (.forallE nat (.app (.bvar 3) (.bvar 0)))))) :=
    .const' E.hasNat.hRec (by simp [VLevel.WF]) rfl (by simp [VLevel.eval]) rfl
  have h1 := HasType.app' h0 hM (B' := .forallE (.app M zero) (.forallE
      (.forallE nat (.forallE (.app (M.liftN 2) (.bvar 0)) (.app (M.liftN 3) (.app succ (.bvar 1)))))
      (.forallE nat (.app (M.liftN 3) (.bvar 0))))) (by simp [VExpr.inst, instVar])
  have h2 := HasType.app' h1 hz (B' := .forallE
      (.forallE nat (.forallE (.app M.lift (.bvar 0)) (.app (M.liftN 2) (.app succ (.bvar 1)))))
      (.forallE nat (.app (M.liftN 2) (.bvar 0)))) (by simp [VExpr.inst, instVar, inst_liftN_lo])
  exact HasType.app' h2 hs (by simp [VExpr.inst, instVar, inst_liftN_lo])

theorem ind (hP : env.HasType (nat :: Γ) P (.sort .zero)) (h0 : Thm env Γ (P.inst zero))
    (hs : Thm env (nat :: Γ) (imp P ((P.liftN 1 1).inst (S (.bvar 0))))) :
    Thm env Γ (all P) := by
  have o := E.ordered
  have hM : env.HasType Γ (.lam nat P) predTy := .lam natTy hP
  obtain ⟨z, hz⟩ := h0.conv (IsDefEq.beta hP zeroTy).symm
  obtain ⟨s, hs⟩ := hs
  have hP1 : env.HasType (nat :: nat :: Γ) (P.liftN 1 1) (.sort .zero) :=
    hP.weakN (.succ .one)
  have hP2 : env.HasType (nat :: P :: nat :: Γ) (P.liftN 2 1) (.sort .zero) :=
    hP.weakN (.succ (.zero [P, nat]))
  have e1 : env.IsDefEq (nat :: Γ) P (.app (VExpr.lam nat P).lift (.bvar 0)) (.sort .zero) := by
    have := IsDefEq.beta hP1 (.bvar .zero)
    rw [inst_liftN_bvar] at this
    exact this.symm
  have e2 : env.IsDefEq (P :: nat :: Γ) ((P.liftN 1 1).inst (S (.bvar 0))).lift
      (.app ((VExpr.lam nat P).liftN 2) (.app succ (.bvar 1))) (.sort .zero) := by
    have := IsDefEq.beta hP2
      (STy (.bvar (.succ .zero)) : env.HasType (P :: nat :: Γ) (S (.bvar 1)) nat)
    rw [lift_inst_hi, liftN'_liftN_hi]
    exact this.symm
  have hs' := (IsDefEq.forallEDF natTy (.forallEDF e1 e2)).defeq (HasType.lam natTy hs)
  exact ⟨_, .defeqDF (.forallEDF natTy e1.symm) (recApp hM hz hs')⟩

end Thm

end Incomplete.Obj
