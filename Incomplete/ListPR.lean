import Incomplete.SubstPR

/-!
# Applications and projections on numbered lists

`appRNum h R` is the number of `decExpr h` applied to the reverse of the list numbered `R`;
`projsC` prepends the reversed projections `proj s i e` for `i < k` to a numbered list. With
substitution, these give a projection's type as a number (`projType_num`).
-/

namespace Incomplete
open Lean4Lean
open PR VExpr

attribute [local simp] eval_eqz eval_succ

/-- The history in variable `2` at `c`, below the key in variable `1`. -/
def histP (c : PR) : PR := nthC (var 2) (leq (leq (var 1) (num 1)) c)

@[simp] theorem eval_histP (c : PR) (ρ : Val) :
    (histP c).eval ρ = nthN (ρ 2) (ρ 1 - 1 - c.eval ρ) := by
  simp [histP, eval_var]

def appStep : PR :=
  ifz (var 1) (var 0) (tagC 7 3 (cpair (histP (sndC (leq (var 1) (num 1))))
    (fstC (leq (var 1) (num 1)))))

def appF (p q h : Nat) : Nat := appStep.eval (val3 p q h)

theorem appStep_computes : Computes3 appStep appF := by
  intro ρ; simp [appF, appStep, val3, eval_var]

theorem appF_eq (h : Nat) : ∀ L : List VExpr,
    cov (appF h) (encList encExpr L) = encExpr ((decExpr h).appN L.reverse)
  | [] => by rw [cov, appF]; simp [appStep, val3, eval_var, encList, appN, encExpr_dec]
  | x :: L => by
    rw [cov, appF]
    simp only [appStep, val3, eval_ifz, eval_var, vcons_zero, vcons_succ, eval_tagC, eval_cpair,
      eval_histP, eval_sndC, eval_fstC, eval_leq, eval_num, encList, Nat.add_sub_cancel,
      unpair1_pair, unpair2_pair, Nat.add_one_ne_zero, if_false]
    rw [nthN_histN' _ (by have := pair_ge_right (encExpr x) (encList encExpr L); omega),
      appF_eq h L, List.reverse_cons, appN_append_singleton]
    simp [encExpr]

/-- The number of `decExpr h` applied to the reverse of the list numbered `R`. -/
def appRP (h R : PR) : PR := comp2 (covPC appStep) R h

@[simp] theorem eval_appRP (h R : PR) (ρ : Val) :
    (appRP h R).eval ρ = encExpr ((decExpr (h.eval ρ)).appN (decList decExpr (R.eval ρ)).reverse) := by
  rw [appRP, eval_comp2 (covPC_computes appStep_computes)]
  show cov (appF (h.eval ρ)) (R.eval ρ) = _
  rw [← encList_dec encExpr_dec (R.eval ρ), appF_eq, decList_enc decExpr_enc]

theorem projs_succ (s : Name) (y : Nat) (e : VExpr) :
    VExpr.projs s (y + 1) e = VExpr.projs s y e ++ [.proj s y e] := by
  simp [VExpr.projs, List.range_succ]

/-- `R0` with the projections `proj s i e`, for `i < k` in variable `0`, prepended in reverse,
where variable `1` holds `pair s (pair e R0)`. -/
def projsC : PR :=
  prec (sndC (sndC (var 0)))
    (PR.succ (cpair (tagC 7 6 (cpair (fstC (var 2)) (cpair (var 1) (fstC (sndC (var 2))))))
      (var 0)))

theorem projsC_eval (ρ : Val) (s : Name) (e : VExpr) (R0 : List VExpr)
    (h : ρ 1 = pair (encName s) (pair (encExpr e) (encList encExpr R0))) :
    projsC.eval ρ = encList encExpr ((VExpr.projs s (ρ 0) e).reverse ++ R0) := by
  show recNat ((sndC (sndC (var 0))).eval (tl ρ)) (fun y r =>
    (PR.succ (cpair (tagC 7 6 (cpair (fstC (var 2)) (cpair (var 1) (fstC (sndC (var 2))))))
      (var 0))).eval (vcons r (vcons y (tl ρ)))) (ρ 0) = _
  generalize ρ 0 = y
  induction y with
  | zero => simp [recNat, eval_var, h, VExpr.projs]
  | succ y ih =>
    rw [recNat_succ, ih, projs_succ]
    simp [eval_var, h, encList, encExpr]

/-- The reversed projections of `e` prepended to `R0`, from codes for `k`, `s`, `e`, `R0`. -/
def projsP (k S E R0 : PR) : PR := comp2 projsC k (cpair S (cpair E R0))

theorem eval_projsP (k S E R0 : PR) (ρ : Val) (s : Name) (e : VExpr) (R0' : List VExpr)
    (hS : S.eval ρ = encName s) (hE : E.eval ρ = encExpr e) (hR : R0.eval ρ = encList encExpr R0') :
    (projsP k S E R0).eval ρ = encList encExpr ((VExpr.projs s (k.eval ρ) e).reverse ++ R0') := by
  unfold projsP comp2
  simp only [PR.eval, eval_ren]
  have hc : (vcons (k.eval ρ) ρ ∘ Nat.succ) = ρ := rfl
  exact projsC_eval _ s e R0' (by simp [hc, hS, hE, hR])

/-- A projection's type as a number. -/
theorem projType_num (c : VConstructor) (ls : List VLevel) (s : Name) (k : Nat)
    (AsR : List VExpr) (e : VExpr) :
    encExpr (c.projType ls s k AsR.reverse e) =
      substNum (encExpr (((c.fields[k]?.map VField.type).getD default).instL ls))
        (encList encExpr ((VExpr.projs s k e).reverse ++ AsR)) 0 := by
  simp only [VConstructor.projType, substNum, decExpr_enc, decList_enc decExpr_enc,
    consList_eq_listS, List.reverse_append, List.reverse_reverse]
  rfl

end Incomplete
