import Incomplete.Obj.SolovayStep
import Incomplete.Diag

/-!
# Chaitin's incompleteness theorem

A number `c` describes `n` when `c` is the code of a machine `f` that, run on `c`, outputs `n`:
the least `k` with `f(c, k) = 0` has first component `n` (`Describes`). `Complex L n` is the
sentence that no code `c ≤ L` describes `n`: the conjunction over `c ≤ L` of `¬Desc(⌜c⌝, c, n)`,
with `Desc(F, D, N)` the Σ₁ formula that the least zero of `F D` has first component `N`
(`descS`), and `⊤` at numbers that are not codes.

The machine `chaitinM T`, at an input `x` and a step `k = ⟨n, p⟩`, checks with `T` whether `p`
proves `¬Desc(⌜x⌝, x, n)`; the number of that sentence is filled into a template with three
holes (`fill3C`). Run on its own code `e`, it halts once some `Complex e n` is provable, and then
its output `n₀` makes `Desc(fn M, e, n₀)` true and so provable, against the proof of its
negation it found. So a consistent theory with a sound and complete checker proves no
`Complex e n` (`chaitin_core`).
-/

namespace Incomplete
open Lean4Lean
open VExpr PR

/-- `f`, run on `x`, outputs `n`: the least `k` with `f(x, k) = 0` has first component `n`. -/
def PR.Outputs (f : PR) (x n : Nat) : Prop :=
  ∃ k, f.eval (val2 k x) = 0 ∧ (∀ j < k, f.eval (val2 j x) ≠ 0) ∧ unpair1 k = n

/-- `c` describes `n`: it is the code of a machine that, run on `c`, outputs `n`. -/
def Describes (c n : Nat) : Prop := ∃ f : PR, f.code = c ∧ f.Outputs c n

/-- `n` is `L`-complex: no code `c ≤ L` describes it. -/
def IsComplex (L n : Nat) : Prop := ∀ c ≤ L, ¬Describes c n

namespace Obj
open Typing

/-- `Desc(F, D, N)`: the least `k` with `F D k = 0` has first component `N`. -/
def descS (F D N : VExpr) : VExpr :=
  ex (conj (app2 F D (.bvar 0) =ₒ zero) (conj (fst (.bvar 0) =ₒ N)
    (all (imp (.bvar 0 <ₒ .bvar 1) (¬ₒ (app2 F D (.bvar 0) =ₒ zero))))))

/-- `p₁ ∧ … ∧ pₙ ∧ ⊤`. -/
def bigAnd : List VExpr → VExpr
  | [] => trueS
  | p :: ps => conj p (bigAnd ps)

open Classical in
/-- The conjunct of `Complex` at `c`: `¬Desc(⌜c⌝, c, n)` if `c` is a code, else `⊤`. -/
noncomputable def cplxC (n c : Nat) : VExpr :=
  if ∃ f : PR, f.code = c then ¬ₒ (descS (decExpr c) (lit c) (lit n)) else trueS

end Obj

open Obj in
/-- **`n` is `L`-complex**, as a sentence: no code `c ≤ L` describes `n`. -/
noncomputable def Complex (L n : Nat) : VExpr := bigAnd ((List.range (L + 1)).map (cplxC n))

namespace Obj
open Typing

/-! ### Expressions with three holes -/

/-- The holes: projection nodes, `0` for the function, `1` for its input, others for the output. -/
def holeN (i : Nat) : VExpr := .proj .anonymous i (.sort .zero)

/-- `e` with its projection nodes filled: index `0` by `F`, `1` by `D`, the others by `N`. -/
def fill3 (F D N : VExpr) : VExpr → VExpr
  | .bvar i => .bvar i
  | .sort u => .sort u
  | .const c ls => .const c ls
  | .app f a => .app (fill3 F D N f) (fill3 F D N a)
  | .lam A b => .lam (fill3 F D N A) (fill3 F D N b)
  | .forallE A b => .forallE (fill3 F D N A) (fill3 F D N b)
  | .proj _ i _ => if i = 0 then F else if i = 1 then D else N

/-- The number of `fill3 F D N e` from the numbers `x`, `y`, `z` of `F`, `D`, `N`. -/
def encFill3 (x y z : Nat) : VExpr → Nat
  | .bvar i => encExpr (.bvar i)
  | .sort u => encExpr (.sort u)
  | .const c ls => encExpr (.const c ls)
  | .app f a => 7 * PR.pair (encFill3 x y z f) (encFill3 x y z a) + 3
  | .lam A b => 7 * PR.pair (encFill3 x y z A) (encFill3 x y z b) + 4
  | .forallE A b => 7 * PR.pair (encFill3 x y z A) (encFill3 x y z b) + 5
  | .proj _ i _ => if i = 0 then x else if i = 1 then y else z

theorem encFill3_eq (F D N : VExpr) :
    ∀ e, encFill3 (encExpr F) (encExpr D) (encExpr N) e = encExpr (fill3 F D N e)
  | .bvar _ | .sort _ | .const _ _ => rfl
  | .app f a => by simp only [encFill3, fill3, encExpr, encFill3_eq F D N f, encFill3_eq F D N a]
  | .lam A b => by simp only [encFill3, fill3, encExpr, encFill3_eq F D N A, encFill3_eq F D N b]
  | .forallE A b => by
    simp only [encFill3, fill3, encExpr, encFill3_eq F D N A, encFill3_eq F D N b]
  | .proj _ i _ => by simp only [encFill3, fill3]; split <;> (try split) <;> rfl

/-- The code of `encFill3`, from codes of the numbers of the holes. -/
def fill3C (cx cy cz : PR) : VExpr → PR
  | .bvar i => numC (encExpr (.bvar i))
  | .sort u => numC (encExpr (.sort u))
  | .const c ls => numC (encExpr (.const c ls))
  | .app f a => tagC 7 3 (cpair (fill3C cx cy cz f) (fill3C cx cy cz a))
  | .lam A b => tagC 7 4 (cpair (fill3C cx cy cz A) (fill3C cx cy cz b))
  | .forallE A b => tagC 7 5 (cpair (fill3C cx cy cz A) (fill3C cx cy cz b))
  | .proj _ i _ => if i = 0 then cx else if i = 1 then cy else cz

theorem eval_fill3C (cx cy cz : PR) (ρ : Val) :
    ∀ e, (fill3C cx cy cz e).eval ρ = encFill3 (cx.eval ρ) (cy.eval ρ) (cz.eval ρ) e
  | .bvar _ | .sort _ | .const _ _ => eval_numC _ _
  | .app f a => by
    simp only [fill3C, encFill3, eval_tagC, eval_cpair, eval_fill3C cx cy cz ρ f,
      eval_fill3C cx cy cz ρ a]
  | .lam A b => by
    simp only [fill3C, encFill3, eval_tagC, eval_cpair, eval_fill3C cx cy cz ρ A,
      eval_fill3C cx cy cz ρ b]
  | .forallE A b => by
    simp only [fill3C, encFill3, eval_tagC, eval_cpair, eval_fill3C cx cy cz ρ A,
      eval_fill3C cx cy cz ρ b]
  | .proj _ i _ => by simp only [fill3C, encFill3]; split <;> (try split) <;> rfl

section
variable {F D N : VExpr} (hF : ∀ n k, F.liftN n k = F) (hD : ∀ n k, D.liftN n k = D)
  (hN : ∀ n k, N.liftN n k = N)
include hF hD hN

theorem fill3_liftN : ∀ (e : VExpr) (n k : Nat), fill3 F D N (e.liftN n k) = (fill3 F D N e).liftN n k
  | .bvar _, _, _ | .sort _, _, _ | .const _ _, _, _ => rfl
  | .app f a, n, k => by
    simp only [VExpr.liftN, fill3, fill3_liftN f, fill3_liftN a]
  | .lam A b, n, k => by
    simp only [VExpr.liftN, fill3, fill3_liftN A, fill3_liftN b]
  | .forallE A b, n, k => by
    simp only [VExpr.liftN, fill3, fill3_liftN A, fill3_liftN b]
  | .proj _ i _, n, k => by
    simp only [VExpr.liftN, fill3]
    split
    · exact (hF n k).symm
    · split
      · exact (hD n k).symm
      · exact (hN n k).symm

end

/-- Expressions without projection nodes, which `fill3` leaves alone. -/
def NoProj : VExpr → Prop
  | .bvar _ | .sort _ | .const _ _ => True
  | .app f a => NoProj f ∧ NoProj a
  | .lam A b | .forallE A b => NoProj A ∧ NoProj b
  | .proj _ _ _ => False

theorem fill3_noProj {F D N : VExpr} : ∀ {e : VExpr}, NoProj e → fill3 F D N e = e
  | .bvar _, _ | .sort _, _ | .const _ _, _ => rfl
  | .app _ _, h | .lam _ _, h | .forallE _ _, h => by
    simp only [fill3, fill3_noProj h.1, fill3_noProj h.2]

theorem NoProj.liftN : ∀ {e : VExpr} (n k : Nat), NoProj e → NoProj (e.liftN n k)
  | .bvar _, _, _, _ | .sort _, _, _, _ | .const _ _, _, _, _ => trivial
  | .app _ _, _, _, h | .lam _ _, _, _, h | .forallE _ _, _, _, h =>
    ⟨NoProj.liftN _ _ h.1, NoProj.liftN _ _ h.2⟩

theorem NoProj.subst : ∀ {e : VExpr} {σ : Subst}, NoProj e → (∀ i, NoProj (σ i)) →
    NoProj (e.subst σ)
  | .bvar i, _, _, hσ => hσ i
  | .sort _, _, _, _ | .const _ _, _, _, _ => trivial
  | .app _ _, _, h, hσ => ⟨NoProj.subst h.1 hσ, NoProj.subst h.2 hσ⟩
  | .lam _ _, _, h, hσ | .forallE _ _, _, h, hσ =>
    ⟨NoProj.subst h.1 hσ, NoProj.subst h.2 fun i => by
      cases i with
      | zero => trivial
      | succ i => exact NoProj.liftN _ _ (hσ i)⟩

theorem noProj_lit : ∀ n, NoProj (lit n)
  | 0 => trivial
  | n + 1 => ⟨trivial, noProj_lit n⟩

theorem noProj_tr : ∀ f : PR, NoProj f.tr
  | .zero | .var _ => trivial
  | .succ f => ⟨trivial, noProj_tr f⟩
  | .push h g => ⟨⟨trivial, noProj_tr g⟩, noProj_tr h⟩
  | .prec g h => by
    simp only [PR.tr, natRec, VExpr.appN, motive, NoProj]
    exact ⟨⟨⟨⟨trivial, trivial, trivial⟩, NoProj.liftN _ _ (noProj_tr g)⟩,
      trivial, trivial, NoProj.liftN _ _ (noProj_tr h)⟩, trivial⟩

theorem noProj_fn (f : PR) : NoProj (fn f) :=
  ⟨trivial, trivial, NoProj.subst (noProj_tr f) fun i => by
    rcases i with _ | _ | i
    · trivial
    · trivial
    · exact NoProj.liftN _ _ (NoProj.liftN _ _ (noProj_lit _))⟩

theorem fill3_fn {F D N : VExpr} (f : PR) : fill3 F D N (fn f) = fn f := fill3_noProj (noProj_fn f)

theorem fill3_lit {F D N : VExpr} (n : Nat) : fill3 F D N (lit n) = lit n :=
  fill3_noProj (noProj_lit n)

theorem holeN_liftN (i n k : Nat) : (holeN i).liftN n k = holeN i := rfl
theorem fill3_hole0 {F D N : VExpr} : fill3 F D N (holeN 0) = F := rfl
theorem fill3_hole1 {F D N : VExpr} : fill3 F D N (holeN 1) = D := rfl
theorem fill3_hole2 {F D N : VExpr} : fill3 F D N (holeN 2) = N := rfl

/-- The template of `¬Desc(F, D, N)`. -/
def descTmpl : VExpr := ¬ₒ (descS (holeN 0) (holeN 1) (holeN 2))

theorem fill3_descTmpl (f : PR) (x n : Nat) :
    fill3 (fn f) (lit x) (lit n) descTmpl = ¬ₒ (descS (fn f) (lit x) (lit n)) := by
  simp only [descTmpl, neg, descS, conj, ex, all, imp, EqN, app2, S, predTy, falseS, nat, succ,
    Incomplete.zero, fill3_liftN (fun _ _ => fn_liftN f) (fun _ _ => lit_liftN x)
      (fun _ _ => lit_liftN n), holeN_liftN, fill3, fill3_fn, fill3_hole0, fill3_hole1,
    fill3_hole2, lit_liftN]

/-! ### The machine -/

/-- The number of `¬Desc(⌜x⌝, x, n)` for the input `x` in variable `1` and `n` the first
component of variable `0`. -/
def ndC : PR := fill3C (var 1) (push (var 1) litC) (push (fstC (var 0)) litC) descTmpl

end Obj

open Obj in
/-- **Chaitin's machine** for the checker `T`: at an input `x` and a step `⟨n, p⟩`, it runs `T` on
the number of `¬Desc(⌜x⌝, x, n)` and `p`. -/
def chaitinM (T : PR) : PR := comp2 T ndC (sndC (var 0))

namespace Obj
open Typing

theorem chaitinM_eval {T : PR} {Fc : Nat → Nat → Nat} (hT : Computes2 T Fc) (f : PR) {x : Nat}
    (hx : x = f.code) (k : Nat) :
    (chaitinM T).eval (val2 k x) = Fc (encExpr (¬ₒ (descS (fn f) (lit x) (lit (unpair1 k)))))
      (unpair2 k) := by
  simp only [chaitinM, eval_comp2 hT, ndC, eval_fill3C, eval_push litC_computes, eval_var,
    eval_fstC, eval_sndC]
  have e1 : val2 k x 1 = x := rfl
  have e0 : val2 k x 0 = k := rfl
  rw [e1, e0, ← fill3_descTmpl, ← encFill3_eq]
  congr 2

/-! ### Σ₁-completeness for descriptions -/

section
variable {env : Typing} [E : ObjEnv env]

/-- A code at numerals, provably. -/
theorem fn_lit {Γ : List VExpr} (f : PR) (x k : Nat) :
    Thm env Γ (app2 (fn f) (lit x) (lit k) =ₒ lit (f.eval (val2 k x))) := by
  have e := ev_lits (env := env) (Γ := Γ) f [k, x]
  have ee : f.eval (fun i => [k, x].getD i 0) = f.eval (val2 k x) := by
    congr 1; funext i; rcases i with _ | _ | i <;> rfl
  rw [ee] at e
  exact Thm.trans (by otype) (by otype) (by otype) (fn_ev (litTy x) (litTy k)) e

theorem fn_lit_ne {Γ : List VExpr} {f : PR} {x k : Nat} (h : f.eval (val2 k x) ≠ 0) :
    Thm env Γ (¬ₒ (app2 (fn f) (lit x) (lit k) =ₒ zero)) := by
  ointro e
  have e' := Thm.trans (by otype) (by otype) (by otype)
    (Thm.symm (by otype) (by otype) (fn_lit f x k)) e
  exact (lit_ne (j := 0) h).mp e'

/-- The non-zeros below a numeral bound, provably. -/
theorem all_lt_lit {Γ : List VExpr} (f : PR) (x : Nat) :
    ∀ K : Nat, (∀ i < K, f.eval (val2 i x) ≠ 0) →
      Thm env Γ (all (imp (.bvar 0 <ₒ lit K) (¬ₒ (app2 (fn f) (lit x) (.bvar 0) =ₒ zero))))
  | 0, _ => by
    refine Thm.allI (Thm.introH (by otype) fun h => ?_)
    onorm at h ⊢
    exact Thm.exfalso (not_lt_zero (by otype) h) (by otype)
  | K + 1, h => by
    have ih := all_lt_lit (Γ := Γ) f x K fun i hi => h i (Nat.lt_succ_of_lt hi)
    refine Thm.allI (Thm.introH (by otype) fun hlt => ?_)
    onorm at hlt ⊢
    have hle : Thm env (_ :: nat :: Γ) (.bvar 1 ≤ₒ lit K) :=
      (lt_succ_iff (by otype) (by otype)).mp hlt
    ocases (eq_or_lt_of_le (by otype) (by otype) hle) with h1 h2
    · orw [h1]
      exact fn_lit_ne (h K (Nat.lt_succ_self K))
    · olift ih
      have := Thm.allE ih (t := .bvar 2) (by otype)
      onorm at this
      exact this.mp h2

theorem fst_lit {Γ : List VExpr} (k : Nat) : Thm env Γ (fst (lit k) =ₒ lit (unpair1 k)) := by
  have := fn_lit (env := env) (Γ := Γ) (fstC (var 0)) 0 k
  simp only [eval_fstC, eval_var] at this
  exact this

/-- **A true description is provable.** -/
theorem descS_of_outputs {Γ : List VExpr} {f : PR} {x n : Nat} (h : f.Outputs x n) :
    Thm env Γ (descS (fn f) (lit x) (lit n)) := by
  obtain ⟨k, h0, hlt, rfl⟩ := h
  unfold descS
  oexists lit k
  have h1 := fn_lit (env := env) (Γ := Γ) f x k
  rw [h0] at h1
  osplit
  · exact h1
  · osplit
    · exact fst_lit k
    · exact all_lt_lit f x k hlt

theorem descSTy {Γ : List VExpr} (f : PR) (x n : Nat) :
    env.HasType Γ (descS (fn f) (lit x) (lit n)) (.sort .zero) := by
  unfold descS; otype

/-! ### The sentence `Complex` -/

theorem bigAndTy {Γ : List VExpr} :
    ∀ {ps : List VExpr}, Props env Γ ps → env.HasType Γ (bigAnd ps) (.sort .zero)
  | [], _ => trueT
  | p :: _, h => conjTy (h p (.head _)) (bigAndTy fun q hq => h q (.tail _ hq))

theorem bigAnd_elim {Γ : List VExpr} : ∀ {ps : List VExpr} {p : VExpr}, Props env Γ ps → p ∈ ps →
    Thm env Γ (bigAnd ps) → Thm env Γ p
  | q :: ps, p, hps, hp, h => by
    have hq := hps q (.head _)
    have hr := bigAndTy (env := env) (Γ := Γ) fun r hr => hps r (.tail _ hr)
    rcases List.mem_cons.1 hp with rfl | hp
    · exact Thm.conjE1 hq hr h
    · exact bigAnd_elim (fun r hr => hps r (.tail _ hr)) hp (Thm.conjE2 hq hr h)

theorem decExpr_code {f : PR} {c : Nat} (hf : f.code = c) : decExpr c = fn f := by
  rw [← hf]; exact decExpr_enc _

theorem cplxC_code {n c : Nat} {f : PR} (hf : f.code = c) :
    cplxC n c = ¬ₒ (descS (fn f) (lit c) (lit n)) := by
  unfold cplxC; rw [ite_eq_left ⟨f, hf⟩, decExpr_code hf]

theorem cplxCTy {Γ : List VExpr} (n c : Nat) : env.HasType Γ (cplxC n c) (.sort .zero) := by
  by_cases h : ∃ f : PR, f.code = c
  · obtain ⟨f, hf⟩ := h
    rw [cplxC_code hf]; exact negTy (descSTy f c n)
  · unfold cplxC; rw [ite_eq_right h]; exact trueT

theorem complexTy {Γ : List VExpr} (L n : Nat) : env.HasType Γ (Complex L n) (.sort .zero) :=
  bigAndTy (props_map fun c => cplxCTy n c)

/-- `Complex L n` proves `¬Desc(fn f, c, n)` for each code `c = ⌜f⌝ ≤ L`. -/
theorem complex_elim {Γ : List VExpr} {L n c : Nat} {f : PR} (hc : c ≤ L) (hf : f.code = c)
    (h : Thm env Γ (Complex L n)) : Thm env Γ (¬ₒ (descS (fn f) (lit c) (lit n))) := by
  have := bigAnd_elim (props_map fun c => cplxCTy (env := env) (Γ := Γ) n c)
    (List.mem_map_of_mem (f := cplxC n) (List.mem_range.2 (Nat.lt_succ_of_le hc))) h
  rwa [cplxC_code hf] at this

/-- In a consistent theory, a provable `Complex L n` is true. -/
theorem complex_true {L n : Nat} (hcon : ¬Thm env [] falseS) (h : Thm env [] (Complex L n)) :
    IsComplex L n :=
  fun _ hc ⟨_, hf, ho⟩ => hcon (Thm.absurd (complex_elim hc hf h) (descS_of_outputs ho))

/-! ### Chaitin's theorem -/

theorem exists_least {P : Nat → Prop} (k : Nat) (hk : P k) : ∃ m, P m ∧ ∀ j < m, ¬P j := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
    by_cases h : ∃ j < k, P j
    · obtain ⟨j, hj, hp⟩ := h; exact ih j hj hp
    · exact ⟨k, hk, fun j hj hp => h ⟨j, hj, hp⟩⟩

/-- **Chaitin's theorem**, over a checker `T` computing `Fc` that accepts exactly the theorems:
in a consistent theory, no sentence `Complex ⌜chaitinM T⌝ n` is provable. -/
theorem chaitin_core {T : PR} {Fc : Nat → Nat → Nat} (hT : Computes2 T Fc)
    (hsound : ∀ (P : VExpr) (k : Nat), Fc (encExpr P) k = 0 → Thm env [] P)
    (hcomp : ∀ P : VExpr, Thm env [] P → ∃ k, Fc (encExpr P) k = 0)
    (hcon : ¬Thm env [] falseS) : ∀ n, ¬Thm env [] (Complex (chaitinM T).code n) := by
  generalize hd : (chaitinM T).code = d
  intro n h
  obtain ⟨p, hp⟩ := hcomp _ (complex_elim (Nat.le_refl d) hd h)
  have hH : (chaitinM T).eval (val2 (PR.pair n p) d) = 0 := by
    rw [chaitinM_eval hT _ hd.symm, unpair1_pair, unpair2_pair]; exact hp
  obtain ⟨k, hk, hmin⟩ := exists_least (P := fun k => (chaitinM T).eval (val2 k d) = 0) _ hH
  have hO : (chaitinM T).Outputs d (unpair1 k) := ⟨k, hk, hmin, rfl⟩
  rw [chaitinM_eval hT _ hd.symm] at hk
  exact hcon (Thm.absurd (hsound _ _ hk) (descS_of_outputs hO))

end

end Obj

end Incomplete
