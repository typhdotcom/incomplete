import Incomplete.Obj.Code
import Incomplete.Obj.Logic

/-!
# Codes on symbolic arguments

`ev f l` is the term of the code `f` with its variables `0, 1, …` read as the terms `l` and as
`zero` past its end; `app2 (fn f) x y` is `ev f [y, x]` (`fn_ev`). For each constructor of `PR`
and the combinators of `PRLib`, its computation rule holds in every context, by beta and iota
(`ev_push`, `ev_prec_zero`, `ev_prec_succ`, `tr_ren`, `ev_comp2`, `ev_comp3`), and a code reads
only its first `bnd f` variables (`ev_take`, `ev_fn2`, `ev_fn1`). Each rule is stated as a
definitional equality (`*_df`) and as an object equation for `orw`, about any code `f` equal by
`rfl` to the constructor's, which `orw` checks when matching; so `orw [ev_prec_succ]` rewrites
`ev PR.mulC (S b :: l)` and keeps the name `mulC`.
-/

namespace Incomplete.Obj
open Lean4Lean
open VExpr VEnv PR

/-! ### Values and their terms -/

/-- The values `l` for variables `0, 1, …`, then `zero`. -/
def valS (l : List VExpr) : Subst := fun i => l.getD i zero

/-- The term of `f` at the values `l`. -/
def ev (f : PR) (l : List VExpr) : VExpr := f.tr.subst (valS l)

/-- Every term of `l` is a number in `Γ`. -/
inductive Tms (env : VEnv) (Γ : List VExpr) : List VExpr → Prop
  | nil : Tms env Γ []
  | cons : Tm env Γ a → Tms env Γ l → Tms env Γ (a :: l)

theorem valS_cons (a : VExpr) (l : List VExpr) : valS (a :: l) = (valS l).cons a := by
  funext i; cases i <;> rfl

theorem getD_append_zero : ∀ (l : List VExpr) (i : Nat), (l ++ [zero]).getD i zero = l.getD i zero
  | [], 0 | [], _ + 1 | _ :: _, 0 => rfl
  | _ :: l, i + 1 => getD_append_zero l i

theorem getD_map {g : VExpr → VExpr} (hg : g zero = zero) :
    ∀ (l : List VExpr) (i : Nat), (l.map g).getD i zero = g (l.getD i zero)
  | [], _ => hg.symm
  | _ :: _, 0 => rfl
  | _ :: l, i + 1 => getD_map hg l i

theorem valS_append_zero (l : List VExpr) : valS (l ++ [zero]) = valS l :=
  funext (getD_append_zero l)

theorem valS_take {l : List VExpr} {n i : Nat} (h : i < n) : valS (l.take n) i = valS l i := by
  simp [valS, List.getD_eq_getElem?_getD, h]

@[obj_simp] theorem ev_zero (l : List VExpr) : ev .zero l = zero := rfl
@[obj_simp] theorem ev_var (i : Nat) (l : List VExpr) : ev (.var i) l = l.getD i zero := rfl
@[obj_simp] theorem ev_succ (f : PR) (l : List VExpr) : ev (.succ f) l = S (ev f l) := rfl

attribute [obj_simp] List.getD_cons_zero List.getD_cons_succ List.getD_nil List.map_cons List.map_id'
  List.map_nil

theorem ev_num (l : List VExpr) : ∀ n, ev (num n) l = lit n
  | 0 => rfl
  | n + 1 => by rw [num, ev_succ, ev_num l n]; rfl

@[obj_simp] theorem ev_liftN (f : PR) (l : List VExpr) (n k : Nat) :
    (ev f l).liftN n k = ev f (l.map (·.liftN n k)) := by
  rw [ev, ev, ← lift'_consN_skipN, lift'_subst]; congr 1; funext i
  simp only [Subst.lift_r, valS, lift'_consN_skipN]
  exact (getD_map (g := fun x => liftN n x k) rfl l i).symm

@[obj_simp] theorem ev_inst (f : PR) (l : List VExpr) (e : VExpr) (k : Nat) :
    (ev f l).inst e k = ev f (l.map (·.inst e k)) := by
  rw [ev, ev, instN_eq, subst_subst]; congr 1; funext i
  simp only [Subst.comp, valS, ← instN_eq]
  exact (getD_map (g := fun x => x.inst e k) rfl l i).symm

/-! ### Variables read -/

/-- One more than the largest variable `f` reads. -/
def bnd : PR → Nat
  | .zero => 0
  | .var i => i + 1
  | .succ f => bnd f
  | .push h g => max (bnd h) (bnd g - 1)
  | .prec g h => max 1 (max (bnd g + 1) (bnd h - 1))

theorem tr_closed : ∀ f : PR, f.tr.ClosedN (bnd f)
  | .zero => trivial
  | .var i => Nat.lt_succ_self i
  | .succ f => ⟨trivial, tr_closed f⟩
  | .push h g => ⟨⟨trivial, (tr_closed g).mono (by simp only [bnd]; omega)⟩,
      (tr_closed h).mono (by simp only [bnd]; omega)⟩
  | .prec g h => by
    refine ⟨⟨⟨⟨trivial, trivial, trivial⟩, ?_⟩, ⟨trivial, trivial, ?_⟩⟩, ?_⟩
    · exact ((tr_closed g).liftN (n := 1) (j := 0)).mono (by simp only [bnd]; omega)
    · exact ((tr_closed h).liftN (n := 1) (j := 2)).mono (by simp only [bnd]; omega)
    · show 0 < _; simp only [bnd]; omega

theorem ev_congr {f : PR} {l l' : List VExpr} (h : ∀ i < bnd f, l.getD i zero = l'.getD i zero) :
    ev f l = ev f l' := (tr_closed f).subst_congr h

/-- `f` reads only its first `n` values. -/
theorem ev_take {f : PR} (n : Nat) (h : bnd f ≤ n) (l : List VExpr) : ev f l = ev f (l.take n) :=
  ev_congr fun _ hi => (valS_take (Nat.lt_of_lt_of_le hi h)).symm

@[obj_simp] theorem map_liftN_inst (l : List VExpr) (e : VExpr) (k : Nat) :
    (l.map fun x => x.liftN 1 k).map (fun x => x.inst e k) = l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, inst_liftN, ih]

theorem ev_append_zero (f : PR) (l : List VExpr) : ev f (l ++ [zero]) = ev f l := by
  rw [ev, valS_append_zero]; rfl

/-! ### Computation rules -/

section
variable {env : VEnv} [E : ObjEnv env] {Γ : List VExpr} {l : List VExpr} {f g h a b c : PR}
  {t x y : VExpr}

theorem Tms.get (hl : Tms env Γ l) : ∀ i, Tm env Γ (valS l i) := by
  induction hl with
  | nil => intro i; exact zeroTy
  | cons ha _ ih => intro i; cases i with | zero => exact ha | succ i => exact ih i

theorem Tms.weak {A : VExpr} (hl : Tms env Γ l) : Tms env (A :: Γ) (l.map fun x => x.liftN 1 0) := by
  induction hl with
  | nil => exact .nil
  | cons ha _ ih => exact .cons (weakTy ha) ih

theorem Tms.liftN {k : Nat} {Γ0 Γ1 : List VExpr} (W : Ctx.LiftN 1 k Γ0 Γ1) (hl : Tms env Γ0 l) :
    Tms env Γ1 (l.map fun x => x.liftN 1 k) := by
  induction hl with
  | nil => exact .nil
  | cons ha _ ih => exact .cons (ha.weakN E.ordered W) ih

theorem liftNTy {k : Nat} {Γ0 Γ1 : List VExpr} {e : VExpr} (W : Ctx.LiftN 1 k Γ0 Γ1)
    (h : Tm env Γ0 e) : Tm env Γ1 (e.liftN 1 k) := h.weakN E.ordered W

theorem Tms.lift1 {A : VExpr} (hl : Tms env (nat :: Γ) l) :
    Tms env (nat :: A :: Γ) (l.map fun x => x.liftN 1 1) := hl.liftN (.succ .one)
theorem Tms.lift2 {A : VExpr} (hl : Tms env (nat :: nat :: Γ) l) :
    Tms env (nat :: nat :: A :: Γ) (l.map fun x => x.liftN 1 2) := hl.liftN (.succ (.succ .one))
theorem lift1Ty {A e : VExpr} (h : Tm env (nat :: Γ) e) : Tm env (nat :: A :: Γ) (e.liftN 1 1) :=
  liftNTy (.succ .one) h
theorem lift2Ty {A e : VExpr} (h : Tm env (nat :: nat :: Γ) e) :
    Tm env (nat :: nat :: A :: Γ) (e.liftN 1 2) := liftNTy (.succ (.succ .one)) h

theorem substTy {σ : Subst} (hσ : ∀ i, Tm env Γ (σ i)) (f : PR) : Tm env Γ (f.tr.subst σ) :=
  f.trT E.hasNat E.ordered hσ

theorem evTy (hl : Tms env Γ l) : Tm env Γ (ev f l) := substTy hl.get f

theorem liftS_T {σ : Subst} (hσ : ∀ i, Tm env Γ (σ i)) :
    ∀ i, Tm env (nat :: Γ) (σ.lift i)
  | 0 => .bvar .zero
  | i + 1 => weakTy (hσ i)

end

macro_rules | `(tactic| otype) => `(tactic| exact Tms.nil)
macro_rules | `(tactic| otype) => `(tactic| ((with_reducible refine Tms.cons ?_ ?_) <;> otype))
macro_rules | `(tactic| otype) => `(tactic| ((with_reducible refine Tms.weak ?_); otype))
macro_rules | `(tactic| otype) => `(tactic| ((with_reducible refine Tms.lift1 ?_); otype))
macro_rules | `(tactic| otype) => `(tactic| ((with_reducible refine Tms.lift2 ?_); otype))
macro_rules | `(tactic| otype) => `(tactic| ((with_reducible refine lift1Ty ?_); otype))
macro_rules | `(tactic| otype) => `(tactic| ((with_reducible refine lift2Ty ?_); otype))
macro_rules | `(tactic| otype) => `(tactic| ((with_reducible refine evTy ?_); otype))
macro_rules | `(tactic| otype) => `(tactic| ((with_reducible show bnd _ ≤ _); decide))

/-- The step of `prec g h`'s recursion, at the values `σ` of its other variables. -/
def precStep (h : PR) (σ : Subst) : VExpr := .lam nat (.lam nat (h.tr.subst σ.lift.lift))

theorem tr_prec_subst (g h : PR) (σ : Subst) (x : VExpr) :
    (PR.prec g h).tr.subst (σ.cons x) = natRec nat (g.tr.subst σ) (precStep h σ) x := by
  show natRec nat (g.tr.lift.subst (σ.cons x))
    (.lam nat (.lam nat ((h.tr.liftN 1 2).subst (σ.cons x).lift.lift))) x = _
  rw [lift_subst_cons, precStep, liftN_subst_eq]
  congr 4; funext i; rcases i with _ | _ | i
  · rfl
  · rfl
  · have e : liftVar 1 (i + 2) 2 = i + 1 + 2 := by rw [liftVar_le (by omega)]; omega
    simp only [shiftS]; rw [e]; rfl

theorem precBody_inst (e : VExpr) (σ : Subst) (t r : VExpr) :
    ((e.subst σ.lift.lift).inst t 1).inst r = e.subst ((σ.cons t).cons r) := by
  rw [← inst_lift_cons]; congr 1
  rw [instN_eq, subst_subst]; congr 1; funext i
  rcases i with _ | _ | i
  · rfl
  · rfl
  · show ((σ i).lift.lift).subst _ = (σ i).lift
    rw [← instN_eq, VExpr.lift, VExpr.lift, liftN_liftN, inst_liftN_lo' _ _ 1 0]

section
variable {env : VEnv} [E : ObjEnv env] {Γ : List VExpr} {l : List VExpr} {f g h a b c : PR}
  {t x y : VExpr}

theorem precStepTy (h : PR) {σ : Subst} (hσ : ∀ i, Tm env Γ (σ i)) :
    env.HasType 0 Γ (precStep h σ) (stepT nat) :=
  HasType.lam natTy (HasType.lam natTy (substTy (liftS_T (liftS_T hσ)) h))

theorem ev_push_df' (hl : Tms env Γ l) (hx : env.IsDefEq 0 Γ (ev h l) x nat) :
    env.IsDefEq 0 Γ (ev (.push h g) l) (ev g (x :: l)) nat := by
  have hg := substTy (liftS_T hl.get) g
  have := IsDefEq.beta hg hx.hasType.2
  rw [inst_lift_cons, ← valS_cons] at this
  exact (IsDefEq.appDF (HasType.lam natTy hg) hx).trans this

theorem ev_push_df (hl : Tms env Γ l) :
    env.IsDefEq 0 Γ (ev (.push h g) l) (ev g (ev h l :: l)) nat :=
  ev_push_df' hl (evTy hl)

theorem ev_prec_zero_df (hl : Tms env Γ l) :
    env.IsDefEq 0 Γ (ev (.prec g h) (zero :: l)) (ev g l) nat := by
  rw [ev, valS_cons, tr_prec_subst]
  exact natRec_zero (A := nat) trivial (fun _ => natTy) (evTy hl) (precStepTy h hl.get)

theorem ev_prec_succ_df (hl : Tms env Γ l) (ht : Tm env Γ t) :
    env.IsDefEq 0 Γ (ev (.prec g h) (S t :: l)) (ev h (ev (.prec g h) (t :: l) :: t :: l)) nat := by
  have hst := precStepTy h hl.get
  have hr : Tm env Γ (natRec nat (ev g l) (precStep h (valS l)) t) :=
    E.hasNat.natRecT Inert.nat (fun _ => natTy) (evTy hl) hst ht
  have i := natRec_succ (A := nat) trivial (fun _ => natTy) (evTy (f := g) hl) hst ht
  have hB : env.HasType 0 (nat :: nat :: Γ) (h.tr.subst (valS l).lift.lift) nat :=
    substTy (liftS_T (liftS_T hl.get)) h
  have b1 := IsDefEq.beta (HasType.lam natTy hB) ht
  have b2 := IsDefEq.beta (hB.instN E.ordered (.succ .zero) ht) hr
  rw [precBody_inst] at b2
  have e1 : ∀ x, ev (.prec g h) (x :: l) = natRec nat (ev g l) (precStep h (valS l)) x := by
    intro x; rw [ev, valS_cons, tr_prec_subst]; rfl
  have e3 : ∀ r, ev h (r :: t :: l) = h.tr.subst (((valS l).cons t).cons r) := by
    intro r; rw [ev, valS_cons, valS_cons]
  rw [e1, e3, e1]
  exact i.trans ((IsDefEq.appDF b1 hr).trans b2)

/-- Renaming: `ren ρ f` at `σ` is `f` at `σ ∘ ρ`. -/
theorem tr_ren : ∀ (f : PR) {Γ : List VExpr} (ρ : Nat → Nat) {σ : Subst}, (∀ i, Tm env Γ (σ i)) →
    env.IsDefEq 0 Γ ((ren ρ f).tr.subst σ) (f.tr.subst fun i => σ (ρ i)) nat
  | .zero, _, _, _, _ => zeroTy
  | .var i, _, _, _, hσ => hσ _
  | .succ f, _, ρ, _, hσ => .appDF E.hasNat.succT (tr_ren f ρ hσ)
  | .push h g, _, ρ, σ, hσ => by
    have ih := tr_ren g (liftR ρ) (liftS_T hσ)
    have e : (fun i => σ.lift (liftR ρ i)) = Subst.lift (fun i => σ (ρ i)) := by
      funext i; cases i <;> rfl
    rw [e] at ih
    exact .appDF (.lamDF natTy ih) (tr_ren h ρ hσ)
  | .prec g h, _, ρ, σ, hσ => by
    have e0 : (fun i => σ (ρ i)) = Subst.cons (fun i => σ (ρ (i + 1))) (σ (ρ 0)) := by
      funext i; cases i <;> rfl
    have e1 := tr_prec_subst g h (fun i => σ (ρ (i + 1))) (σ (ρ 0))
    rw [← e0] at e1
    show env.IsDefEq 0 _ (.app (.lam nat ((PR.prec _ _).tr.subst σ.lift)) (σ (ρ 0))) _ nat
    rw [e1]
    have hp := substTy (liftS_T hσ)
      (PR.prec (ren (fun i => ρ (i + 1)) g) (ren (liftR (liftR fun i => ρ (i + 1))) h))
    have b := IsDefEq.beta hp (hσ (ρ 0))
    rw [inst_lift_cons, tr_prec_subst] at b
    refine b.trans (natRec_congr3 trivial (fun _ => natTy) (tr_ren g _ hσ) ?_ (hσ _))
    have ih := tr_ren h (liftR (liftR fun i => ρ (i + 1))) (liftS_T (liftS_T hσ))
    have e : (fun i => σ.lift.lift (liftR (liftR fun i => ρ (i + 1)) i)) =
        Subst.lift (Subst.lift (fun i => σ (ρ (i + 1)))) := by
      funext i; rcases i with _ | _ | i <;> rfl
    rw [e] at ih
    exact .lamDF natTy (.lamDF natTy ih)

theorem ev_ren_df (hl : Tms env Γ l) (ρ : Nat → Nat) (f : PR) :
    env.IsDefEq 0 Γ (ev (ren ρ f) l) (f.tr.subst fun i => valS l (ρ i)) nat :=
  tr_ren f ρ hl.get

theorem ev_comp2_df (hl : Tms env Γ l) :
    env.IsDefEq 0 Γ (ev (comp2 g a b) l) (ev g (ev a l :: ev b l :: l)) nat := by
  have hl1 : Tms env Γ (ev a l :: l) := .cons (evTy hl) hl
  have h1 := ev_push_df (h := a) (g := push (ren Nat.succ b) (ren (fun | 0 => 1 | 1 => 0 | i => i) g)) hl
  have h2 := ev_push_df' (g := ren (fun | 0 => 1 | 1 => 0 | i => i) g) hl1 (ev_ren_df hl1 Nat.succ b)
  have h3 := ev_ren_df (.cons (evTy (f := b) hl) hl1) (fun | 0 => 1 | 1 => 0 | i => i) g
  have e : (fun i => valS (ev b l :: ev a l :: l) ((fun | 0 => 1 | 1 => 0 | i => i) i)) =
      valS (ev a l :: ev b l :: l) := by
    funext i; rcases i with _ | _ | i <;> rfl
  rw [e] at h3
  exact h1.trans (h2.trans h3)

theorem ev_comp3_df (hl : Tms env Γ l) :
    env.IsDefEq 0 Γ (ev (comp3 g a b c) l) (ev g (ev a l :: ev b l :: ev c l :: l)) nat := by
  have hl1 : Tms env Γ (ev a l :: l) := .cons (evTy hl) hl
  have hl2 : Tms env Γ (ev b l :: ev a l :: l) := .cons (evTy hl) hl1
  have h1 := ev_push_df (h := a) (g := push (ren Nat.succ b) (push (ren (· + 2) c)
    (ren (fun | 0 => 2 | 1 => 1 | 2 => 0 | i => i) g))) hl
  have h2 := ev_push_df' (g := push (ren (· + 2) c) (ren (fun | 0 => 2 | 1 => 1 | 2 => 0 | i => i) g))
    hl1 (ev_ren_df hl1 Nat.succ b)
  have h3 := ev_push_df' (g := ren (fun | 0 => 2 | 1 => 1 | 2 => 0 | i => i) g) hl2
    (ev_ren_df hl2 (· + 2) c)
  have h4 := ev_ren_df (.cons (evTy (f := c) hl) hl2) (fun | 0 => 2 | 1 => 1 | 2 => 0 | i => i) g
  have e : (fun i => valS (ev c l :: ev b l :: ev a l :: l)
      ((fun | 0 => 2 | 1 => 1 | 2 => 0 | i => i) i)) = valS (ev a l :: ev b l :: ev c l :: l) := by
    funext i; rcases i with _ | _ | _ | i <;> rfl
  rw [e] at h4
  exact h1.trans (h2.trans (h3.trans h4))


/-- `fn f x y` is `f` at `[y, x]`. -/
theorem fn_ev_df (hx : Tm env Γ x) (hy : Tm env Γ y) :
    env.IsDefEq 0 Γ (app2 (fn f) x y) (ev f [y, x]) nat := by
  have hB : env.HasType 0 (nat :: nat :: Γ) (fnBody f) nat :=
    substTy (liftS_T (liftS_T fun _ => litTy 0)) f
  have b1 := IsDefEq.beta (HasType.lam natTy hB) hx
  have b2 := IsDefEq.beta (hB.instN E.ordered (.succ .zero) hx) hy
  have e : ((fnBody f).inst x 1).inst y = ev f [y, x] := by
    rw [fnBody, precBody_inst, ev]; congr 1; funext i; rcases i with _ | _ | i <;> rfl
  rw [e] at b2
  exact (IsDefEq.appDF b1 hy).trans b2

theorem ev_fn2_df (hf : bnd f ≤ 2) (hx : Tm env Γ x) (hy : Tm env Γ y) (l : List VExpr) :
    env.IsDefEq 0 Γ (ev f (y :: x :: l)) (app2 (fn f) x y) nat := by
  rw [ev_take 2 hf]; exact (fn_ev_df hx hy).symm

theorem ev_fn1_df (hf : bnd f ≤ 1) (hy : Tm env Γ y) (l : List VExpr) :
    env.IsDefEq 0 Γ (ev f (y :: l)) (app2 (fn f) zero y) nat := by
  rw [ev_take 1 hf, List.take_succ_cons, List.take_zero, ← ev_append_zero]
  exact (fn_ev_df zeroTy hy).symm

/-! #### As object equations -/

theorem fn_ev (hx : Tm env Γ x) (hy : Tm env Γ y) : Thm env Γ (app2 (fn f) x y =ₒ ev f [y, x]) :=
  .ofDefEq (fn_ev_df hx hy)

theorem ev_fn2 (hf : bnd f ≤ 2) (hx : Tm env Γ x) (hy : Tm env Γ y) :
    Thm env Γ (ev f (y :: x :: l) =ₒ app2 (fn f) x y) := .ofDefEq (ev_fn2_df hf hx hy l)

theorem ev_fn1 (hf : bnd f ≤ 1) (hy : Tm env Γ y) :
    Thm env Γ (ev f (y :: l) =ₒ app2 (fn f) zero y) := .ofDefEq (ev_fn1_df hf hy l)

theorem ev_push (hf : f = .push h g) (hl : Tms env Γ l) :
    Thm env Γ (ev f l =ₒ ev g (ev h l :: l)) := hf ▸ .ofDefEq (ev_push_df hl)

theorem ev_prec_zero (hf : f = .prec g h) (hl : Tms env Γ l) :
    Thm env Γ (ev f (zero :: l) =ₒ ev g l) := hf ▸ .ofDefEq (ev_prec_zero_df hl)

theorem ev_prec_succ (hf : f = .prec g h) (hl : Tms env Γ l) (ht : Tm env Γ t) :
    Thm env Γ (ev f (S t :: l) =ₒ ev h (ev f (t :: l) :: t :: l)) :=
  hf ▸ .ofDefEq (ev_prec_succ_df hl ht)

theorem ev_comp2 (hf : f = comp2 g a b) (hl : Tms env Γ l) :
    Thm env Γ (ev f l =ₒ ev g (ev a l :: ev b l :: l)) := hf ▸ .ofDefEq (ev_comp2_df hl)

theorem ev_comp3 (hf : f = comp3 g a b c) (hl : Tms env Γ l) :
    Thm env Γ (ev f l =ₒ ev g (ev a l :: ev b l :: ev c l :: l)) :=
  hf ▸ .ofDefEq (ev_comp3_df hl)

end

end Incomplete.Obj
