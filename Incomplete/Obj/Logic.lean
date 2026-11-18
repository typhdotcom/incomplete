import Incomplete.Obj.Tactic
import Incomplete.Obj.Iota

/-!
# Connectives

Impredicative `⊥` (`falseS`), `¬`, `∧`, `∨`, `↔` and `∃` over `Nat`, with their introduction
and elimination rules, and the first facts about `Nat` they state: `0 ≠ S n`, injectivity of
`S`, and `n = 0 ∨ ∃ m, n = S m`.

Tactics: `oleft`, `oright`, `osplit`, `oexists t`, `oexfalso`; `ocases h with h₁ h₂`
eliminates a disjunction, existential or conjunction `h`, and `ocases` alone splits a goal
`∀ n, P n` into `P 0` and `P (S n)`.
-/

namespace Incomplete.Obj
open Lean4Lean
open VExpr VEnv

/-! ### Formulas -/

/-- `¬P`. -/
def neg (P : VExpr) : VExpr := imp P falseS

/-- `P ∧ Q`: `∀ R : Prop, (P → Q → R) → R`. -/
def conj (P Q : VExpr) : VExpr :=
  .forallE (.sort .zero) (imp (imp P.lift (imp Q.lift (.bvar 0))) (.bvar 0))

/-- `P ∨ Q`: `∀ R : Prop, (P → R) → (Q → R) → R`. -/
def disj (P Q : VExpr) : VExpr :=
  .forallE (.sort .zero) (imp (imp P.lift (.bvar 0)) (imp (imp Q.lift (.bvar 0)) (.bvar 0)))

/-- `∃ x : Nat, P`, with `P` over `x`: `∀ R : Prop, (∀ x, P → R) → R`. -/
def ex (P : VExpr) : VExpr :=
  .forallE (.sort .zero) (imp (all (imp (P.liftN 1 1) (.bvar 1))) (.bvar 0))

/-- `P ↔ Q`. -/
def iff (P Q : VExpr) : VExpr := conj (imp P Q) (imp Q P)

section
variable {n k : Nat} {e P Q : VExpr}

@[obj_simp] theorem falseS_liftN : falseS.liftN n k = falseS := rfl
@[obj_simp] theorem falseS_inst : falseS.inst e k = falseS := rfl
@[obj_simp] theorem neg_liftN : (neg P).liftN n k = neg (P.liftN n k) := by simp [neg, imp_liftN]; rfl
@[obj_simp] theorem neg_inst : (neg P).inst e k = neg (P.inst e k) := by simp [neg, imp_inst]; rfl
@[obj_simp] theorem conj_liftN : (conj P Q).liftN n k = conj (P.liftN n k) (Q.liftN n k) := by
  simp only [conj, VExpr.liftN, imp_liftN, lift_liftN']; rfl
@[obj_simp] theorem conj_inst : (conj P Q).inst e k = conj (P.inst e k) (Q.inst e k) := by
  simp only [conj, VExpr.inst, imp_inst, lift_instN_lo]; rfl
@[obj_simp] theorem disj_liftN : (disj P Q).liftN n k = disj (P.liftN n k) (Q.liftN n k) := by
  simp only [disj, VExpr.liftN, imp_liftN, lift_liftN']; rfl
@[obj_simp] theorem disj_inst : (disj P Q).inst e k = disj (P.inst e k) (Q.inst e k) := by
  simp only [disj, VExpr.inst, imp_inst, lift_instN_lo]; rfl
@[obj_simp] theorem ex_liftN : (ex P).liftN n k = ex (P.liftN n (k + 1)) := by
  have := liftN'_comm P n 1 (k + 1) 1 (by omega)
  rw [show 1 + (k + 1) = k + 1 + 1 by omega] at this
  simp only [ex, VExpr.liftN, imp_liftN, all_liftN, ← this, liftVar_zero, liftVar_succ]
@[obj_simp] theorem ex_inst : (ex P).inst e k = ex (P.inst e (k + 1)) := by
  have := liftN_instN_lo 1 P e (k + 1) 1 (by omega)
  rw [show 1 + (k + 1) = k + 1 + 1 by omega] at this
  simp only [ex, VExpr.inst, imp_inst, all_inst, ← this, instVar_lower, instVar_succ]; rfl
@[obj_simp] theorem iff_liftN : (iff P Q).liftN n k = iff (P.liftN n k) (Q.liftN n k) := by
  simp only [iff, conj_liftN, imp_liftN]
@[obj_simp] theorem iff_inst : (iff P Q).inst e k = iff (P.inst e k) (Q.inst e k) := by
  simp only [iff, conj_inst, imp_inst]

end

/-! ### Typing -/

section
variable {env : VEnv} [E : ObjEnv env] {Γ : List VExpr} {P Q : VExpr}

omit E in
theorem propTy : env.HasType 0 Γ (.sort .zero) (.sort (.succ .zero)) := .sort trivial

omit E in
theorem falseTy : env.HasType 0 Γ falseS (.sort .zero) := falseT

theorem negTy (hP : env.HasType 0 Γ P (.sort .zero)) : env.HasType 0 Γ (neg P) (.sort .zero) :=
  impTy hP falseT

theorem conjTy (hP : env.HasType 0 Γ P (.sort .zero)) (hQ : env.HasType 0 Γ Q (.sort .zero)) :
    env.HasType 0 Γ (conj P Q) (.sort .zero) :=
  forallE_prop propTy (impTy (impTy (weakTy hP) (impTy (weakTy hQ) (.bvar .zero))) (.bvar .zero))

theorem disjTy (hP : env.HasType 0 Γ P (.sort .zero)) (hQ : env.HasType 0 Γ Q (.sort .zero)) :
    env.HasType 0 Γ (disj P Q) (.sort .zero) :=
  forallE_prop propTy (impTy (impTy (weakTy hP) (.bvar .zero))
    (impTy (impTy (weakTy hQ) (.bvar .zero)) (.bvar .zero)))

theorem liftN11Ty {A : VExpr} (hP : env.HasType 0 (nat :: Γ) P (.sort .zero)) :
    env.HasType 0 (nat :: A :: Γ) (P.liftN 1 1) (.sort .zero) :=
  hP.weakN E.ordered (.succ .one)

theorem exTy (hP : env.HasType 0 (nat :: Γ) P (.sort .zero)) :
    env.HasType 0 Γ (ex P) (.sort .zero) :=
  forallE_prop propTy (impTy (allTy (impTy (liftN11Ty hP) (.bvar (.succ .zero)))) (.bvar .zero))

theorem weakProp {B : VExpr} (hP : env.HasType 0 Γ P (.sort .zero)) :
    env.HasType 0 (B :: Γ) P.lift (.sort .zero) := weakTy hP

theorem weakNat {B a : VExpr} (ha : env.HasType 0 Γ a nat) : env.HasType 0 (B :: Γ) a.lift nat :=
  weakTy ha

theorem iffTy (hP : env.HasType 0 Γ P (.sort .zero)) (hQ : env.HasType 0 Γ Q (.sort .zero)) :
    env.HasType 0 Γ (iff P Q) (.sort .zero) :=
  conjTy (impTy hP hQ) (impTy hQ hP)

end

macro_rules | `(tactic| otype) => `(tactic| with_reducible exact falseTy)
macro_rules | `(tactic| otype) => `(tactic| with_reducible exact propTy)
macro_rules | `(tactic| otype) => `(tactic| ((with_reducible refine weakProp ?_); otype))
macro_rules | `(tactic| otype) => `(tactic| ((with_reducible refine weakNat ?_); otype))
macro_rules | `(tactic| otype) => `(tactic| ((with_reducible refine liftN11Ty ?_); otype))
macro_rules | `(tactic| otype) => `(tactic| ((with_reducible refine negTy ?_); otype))
macro_rules | `(tactic| otype) => `(tactic| ((with_reducible refine conjTy ?_ ?_) <;> otype))
macro_rules | `(tactic| otype) => `(tactic| ((with_reducible refine disjTy ?_ ?_) <;> otype))
macro_rules | `(tactic| otype) => `(tactic| ((with_reducible refine exTy ?_); otype))
macro_rules | `(tactic| otype) => `(tactic| ((with_reducible refine iffTy ?_ ?_) <;> otype))

/-! ### Rules -/

namespace Thm
variable {env : VEnv} [E : ObjEnv env] {Γ : List VExpr} {P Q R a b t : VExpr}

omit E in
/-- `∀ R : Prop, P`, introduced. -/
theorem pallI (h : Thm env (.sort .zero :: Γ) P) : Thm env Γ (.forallE (.sort .zero) P) :=
  let ⟨_, hp⟩ := h; ⟨_, .lam (.sort trivial) hp⟩

omit E in
theorem pallE (h : Thm env Γ (.forallE (.sort .zero) P)) (hR : env.HasType 0 Γ R (.sort .zero)) :
    Thm env Γ (P.inst R) :=
  let ⟨_, hp⟩ := h; ⟨_, .app hp hR⟩

theorem exfalso (h : Thm env Γ falseS) (hP : env.HasType 0 Γ P (.sort .zero)) : Thm env Γ P :=
  (pallE h hP).cast (by simp only [obj_simp])

theorem absurd (h : Thm env Γ (neg P)) (hP : Thm env Γ P) : Thm env Γ falseS := mp h hP

theorem conjI (hP : env.HasType 0 Γ P (.sort .zero)) (hQ : env.HasType 0 Γ Q (.sort .zero))
    (h1 : Thm env Γ P) (h2 : Thm env Γ Q) : Thm env Γ (conj P Q) := by
  refine pallI ?_
  ointro k
  exact mp (mp k h1.weak.weak) h2.weak.weak

theorem conjE1 (hP : env.HasType 0 Γ P (.sort .zero)) (hQ : env.HasType 0 Γ Q (.sort .zero))
    (h : Thm env Γ (conj P Q)) : Thm env Γ P := by
  have h := pallE h hP
  onorm at h
  refine mp h ?_
  ointro; ointro; ohyp

theorem conjE2 (hP : env.HasType 0 Γ P (.sort .zero)) (hQ : env.HasType 0 Γ Q (.sort .zero))
    (h : Thm env Γ (conj P Q)) : Thm env Γ Q := by
  have h := pallE h hQ
  onorm at h
  refine mp h ?_
  ointro; ointro; ohyp

theorem disjI1 (hP : env.HasType 0 Γ P (.sort .zero)) (hQ : env.HasType 0 Γ Q (.sort .zero))
    (h : Thm env Γ P) : Thm env Γ (disj P Q) := by
  refine pallI ?_
  ointro k
  ointro
  exact mp k.weak (by simpa only [obj_simp] using h.weak.weak.weak)

theorem disjI2 (hP : env.HasType 0 Γ P (.sort .zero)) (hQ : env.HasType 0 Γ Q (.sort .zero))
    (h : Thm env Γ Q) : Thm env Γ (disj P Q) := by
  refine pallI ?_
  ointro
  ointro k
  exact mp k (by simpa only [obj_simp] using h.weak.weak.weak)

theorem disjE (hP : env.HasType 0 Γ P (.sort .zero)) (hQ : env.HasType 0 Γ Q (.sort .zero))
    (hR : env.HasType 0 Γ R (.sort .zero)) (h : Thm env Γ (disj P Q))
    (k1 : Thm env (P :: Γ) R.lift) (k2 : Thm env (Q :: Γ) R.lift) : Thm env Γ R := by
  have h := pallE h hR
  onorm at h
  exact mp (mp h (intro hP k1)) (intro hQ k2)

theorem exI (hP : env.HasType 0 (nat :: Γ) P (.sort .zero)) (ht : env.HasType 0 Γ t nat)
    (h : Thm env Γ (P.inst t)) : Thm env Γ (ex P) := by
  refine pallI ?_
  ointro k
  have k := allE k (weakTy (weakTy ht))
  have e : ((P.liftN 1 1).liftN 1 1).inst t.lift.lift = (P.inst t).lift.lift := by
    rw [liftN'_liftN' (n1 := 1) (n2 := 1) (k1 := 1) (k2 := 1) (by omega) (by omega)]
    show (P.liftN 2 1).inst (liftN 1 (liftN 1 t)) = liftN 1 (liftN 1 (P.inst t))
    rw [liftN_liftN, liftN_liftN, liftN_inst_hi]
  onorm at k
  rw [e] at k
  exact mp k h.weak.weak

theorem exE (hR : env.HasType 0 Γ R (.sort .zero))
    (h : Thm env Γ (ex P)) (k : Thm env (nat :: Γ) (imp P R.lift)) : Thm env Γ R := by
  have h := pallE h hR
  simp only [obj_simp, inst_liftN] at h
  exact mp h (allI k)

theorem iffI (hP : env.HasType 0 Γ P (.sort .zero)) (hQ : env.HasType 0 Γ Q (.sort .zero))
    (h1 : Thm env Γ (imp P Q)) (h2 : Thm env Γ (imp Q P)) : Thm env Γ (iff P Q) :=
  conjI (impTy hP hQ) (impTy hQ hP) h1 h2

theorem iffE1 (hP : env.HasType 0 Γ P (.sort .zero)) (hQ : env.HasType 0 Γ Q (.sort .zero))
    (h : Thm env Γ (iff P Q)) : Thm env Γ (imp P Q) := conjE1 (impTy hP hQ) (impTy hQ hP) h

theorem iffE2 (hP : env.HasType 0 Γ P (.sort .zero)) (hQ : env.HasType 0 Γ Q (.sort .zero))
    (h : Thm env Γ (iff P Q)) : Thm env Γ (imp Q P) := conjE2 (impTy hP hQ) (impTy hQ hP) h

/-- `disjE`, naming each case's hypothesis. -/
theorem disjEH (hP : env.HasType 0 Γ P (.sort .zero)) (hQ : env.HasType 0 Γ Q (.sort .zero))
    (hR : env.HasType 0 Γ R (.sort .zero)) (h : Thm env Γ (disj P Q))
    (k1 : Thm env (P :: Γ) P.lift → Thm env (P :: Γ) R.lift)
    (k2 : Thm env (Q :: Γ) Q.lift → Thm env (Q :: Γ) R.lift) : Thm env Γ R :=
  disjE hP hQ hR h (k1 (hyp .zero)) (k2 (hyp .zero))

/-- `exE`, naming the hypothesis on the witness `bvar 0`. -/
theorem exEH (hP : env.HasType 0 (nat :: Γ) P (.sort .zero)) (hR : env.HasType 0 Γ R (.sort .zero))
    (h : Thm env Γ (ex P)) (k : Thm env (P :: nat :: Γ) P.lift → Thm env (P :: nat :: Γ) R.lift.lift) :
    Thm env Γ R :=
  exE hR h (intro hP (by simpa only [obj_simp] using k (hyp .zero)))

/-- `exE`, with the typing of the witness `bvar 1` and the hypothesis on it. -/
theorem exEHT (hP : env.HasType 0 (nat :: Γ) P (.sort .zero)) (hR : env.HasType 0 Γ R (.sort .zero))
    (h : Thm env Γ (ex P)) (k : Tm env (P :: nat :: Γ) (.bvar 1) →
      Thm env (P :: nat :: Γ) P.lift → Thm env (P :: nat :: Γ) R.lift.lift) :
    Thm env Γ R :=
  exEH hP hR h (k (.bvar (.succ .zero)))

/-- Case analysis on a number: `P 0` and `P (S n)` prove `∀ n, P n`. -/
theorem cases (hP : env.HasType 0 (nat :: Γ) P (.sort .zero)) (h0 : Thm env Γ (P.inst zero))
    (hs : Thm env (nat :: Γ) ((P.liftN 1 1).inst (S (.bvar 0)))) : Thm env Γ (all P) :=
  ind hP h0 (intro hP hs.weak)

end Thm

/-! ### Tactics and notation -/

macro "oleft" : tactic => `(tactic| (refine Thm.disjI1 ?_ ?_ ?_ <;> [otype; otype; try onorm]))
macro "oright" : tactic => `(tactic| (refine Thm.disjI2 ?_ ?_ ?_ <;> [otype; otype; try onorm]))

/-- Split a conjunction or an equivalence. -/
macro "osplit" : tactic => `(tactic| first
  | (refine Thm.iffI ?_ ?_ ?_ ?_ <;> [otype; otype; (try onorm); (try onorm)])
  | (refine Thm.conjI ?_ ?_ ?_ ?_ <;> [otype; otype; (try onorm); (try onorm)]))

/-- Prove `∃ x, P` at the witness `t`. -/
macro "oexists " t:term : tactic =>
  `(tactic| (refine Thm.exI (t := $t) ?_ ?_ ?_ <;> [otype; otype; try onorm]))

macro "oexfalso" : tactic => `(tactic| (refine Thm.exfalso ?_ ?_ <;> [skip; otype]))

/-- `ocases h with h₁ h₂` eliminates `h`: a disjunction into two goals with the disjuncts `h₁`
and `h₂` as hypotheses, or a conjunction into its conjuncts `h₁` and `h₂`. On an existential,
`ocases h with h₁` gives a goal over the witness `bvar 1` with `h₁` its property, and
`ocases h with x h₁` names the witness: the goal and `h₁` are generalized over it as `x`, with
`xT` its typing. `ocases` alone splits a goal `∀ n, P n` into `P 0` and `∀ n, P (S n)`. -/
syntax "ocases" (ppSpace colGt term:max " with" (ppSpace colGt ident)+)? : tactic

macro_rules
  | `(tactic| ocases) => `(tactic| (refine Thm.cases ?_ ?_ ?_; otype; (try onorm); on_goal 2 => try onorm))
  | `(tactic| ocases $h with $x $y) => do
    let xT := Lean.mkIdent (x.getId.appendAfter "T")
    `(tactic| first
    | (refine Thm.disjEH ?_ ?_ ?_ $h (fun $x => ?_) (fun $y => ?_) <;> [otype; otype; otype;
        (try onorm at $x:ident ⊢); (try onorm at $y:ident ⊢)])
    | (refine Thm.exEHT ?_ ?_ $h (fun $xT $y => ?_) <;> [otype; otype;
        ((try onorm at $y:ident ⊢); generalize VExpr.bvar 1 = $x at $y $xT ⊢)])
    | (have $x := Thm.conjE1 (by otype) (by otype) $h
       have $y := Thm.conjE2 (by otype) (by otype) $h))
  | `(tactic| ocases $h with $x) => `(tactic|
    (refine Thm.exEH ?_ ?_ $h (fun $x => ?_) <;> [otype; otype; (try onorm at $x:ident ⊢)]))

/-- `∃ₒ x y, P`: the object formula `ex (ex P)`, with `x` and `y` read as the bound variables. -/
elab "∃ₒ " xs:ident+ ", " b:term : term => do
  let names := xs.map (·.getId)
  let decls : Array (Lean.Name × Lean.Expr) := names.map fun n => (n, Lean.mkConst ``VExpr)
  Lean.Meta.withLocalDeclsDND decls fun fvs => do
    let e ← Lean.Elab.Term.elabTermAndSynthesize b (Lean.mkConst ``VExpr)
    let mut r ← bindVars fvs 0 e
    for _ in fvs do r := Lean.mkApp (Lean.mkConst ``Obj.ex) r
    return r

/-- `⊥`, as `falseS`. -/
scoped notation "⊥ₒ" => falseS
@[inherit_doc] scoped prefix:max "¬ₒ " => neg
@[inherit_doc] scoped infixr:35 " ∧ₒ " => conj
@[inherit_doc] scoped infixr:30 " ∨ₒ " => disj
@[inherit_doc] scoped infix:20 " ↔ₒ " => iff

/-! ### Zero and successor -/

/-- `Nat.rec 0 (fun y _ => y)`. -/
def predR (a : VExpr) : VExpr := natRec nat zero (.lam nat (.lam nat (.bvar 1))) a

section
variable {env : VEnv} [E : ObjEnv env] {Γ : List VExpr} {a b n : VExpr}

theorem isZero_zero : env.IsDefEq 0 Γ (isZero zero) trueS (.sort .zero) :=
  natRec_zero (A := .sort .zero) trivial (fun _ => propTy) trueT (isZeroStepT E.hasNat)

theorem isZero_succ' (hn : Tm env Γ n) : env.IsDefEq 0 Γ (isZero (S n)) falseS (.sort .zero) := by
  have hst := isZeroStepT (Γ := Γ) E.hasNat
  have hr := isZeroT E.hasNat hn
  have h1 := natRec_succ (A := .sort .zero) trivial (fun _ => propTy) trueT hst hn
  have b1 := IsDefEq.beta (HasType.lam propTy (falseT (env := env) (Γ := .sort .zero :: nat :: Γ))) hn
  have b2 := IsDefEq.beta (falseT (env := env) (Γ := .sort .zero :: Γ)) hr
  exact h1.trans ((IsDefEq.appDF b1 hr).trans b2)

theorem predRTy (ha : Tm env Γ a) : Tm env Γ (predR a) :=
  E.hasNat.natRecT Inert.nat (fun _ => natTy) zeroTy
    (.lam natTy (.lam natTy (.bvar (.succ .zero)))) ha

theorem predR_succ (ha : Tm env Γ a) : env.IsDefEq 0 Γ (predR (S a)) a nat := by
  have hst : env.HasType 0 Γ (.lam nat (.lam nat (.bvar 1))) (stepT nat) :=
    .lam natTy (.lam natTy (.bvar (.succ .zero)))
  have h1 := natRec_succ (A := nat) trivial (fun _ => natTy) zeroTy hst ha
  have b1 := IsDefEq.beta (HasType.lam natTy (HasType.bvar (env := env) (U := 0)
    (Γ := nat :: nat :: Γ) (.succ .zero))) ha
  have b2 := IsDefEq.beta (weakTy (B := nat) ha) (predRTy ha)
  rw [inst_lift] at b2
  exact h1.trans ((IsDefEq.appDF b1 (predRTy ha)).trans b2)

omit E in
@[obj_simp] theorem predR_liftN {m k : Nat} : (predR a).liftN m k = predR (a.liftN m k) := rfl
omit E in
@[obj_simp] theorem predR_inst {e : VExpr} {k : Nat} : (predR a).inst e k = predR (a.inst e k) := rfl

theorem zero_ne_succ (hn : Tm env Γ n) : Thm env Γ (¬ₒ (zero =ₒ S n)) := by
  ointro h
  have hz : Thm env (EqN zero (S n) :: Γ) (isZero zero) := ⟨_, isZero_zero.symm.defeq trueI_T⟩
  have := Thm.subst (M := isZero (.bvar 0)) (isZeroT E.hasNat (.bvar .zero)) h zeroTy
    (STy (weakTy hn)) hz
  simp only [isZero_instN, obj_simp] at this
  exact this.conv (isZero_succ' (weakTy hn))

theorem succ_ne_zero (hn : Tm env Γ n) : Thm env Γ (¬ₒ (S n =ₒ zero)) := by
  ointro h
  exact (zero_ne_succ (weakTy hn)).mp (Thm.symm (STy (weakTy hn)) zeroTy h)

theorem succ_inj (ha : Tm env Γ a) (hb : Tm env Γ b) : Thm env Γ (S a =ₒ S b →ₒ a =ₒ b) := by
  ointro h
  have := Thm.congr (f := predR (.bvar 0)) (predRTy (.bvar .zero)) (STy (weakTy ha))
    (STy (weakTy hb)) h
  onorm at this
  exact this.conv (EqN_congr (predR_succ (weakTy ha)) (predR_succ (weakTy hb)))

theorem zero_or_succ_c : Thm env [] (∀ₒ n, n =ₒ zero ∨ₒ ∃ₒ m, n =ₒ S m) := by
  ocases
  · oleft; orefl
  · oright; oexists .bvar 0; orefl

theorem zero_or_succ (hn : Tm env Γ n) : Thm env Γ (n =ₒ zero ∨ₒ ∃ₒ m, n.lift =ₒ S m) := by
  ospec zero_or_succ_c hn

end

end Incomplete.Obj
