import Incomplete.Induct
import Incomplete.Extend

/-!
# Rosser's incompleteness theorem

The machine `rosserC G` on input `e = ⌜f⌝` races certificates, checked by `G`, for
`notHalts f e` against certificates for `halts f e`: it halts at `k` when `k` proves
`notHalts f e` and no `j ≤ k` proves `halts f e`. At its own number neither sentence is
provable, from consistency alone. A proof of `notHalts` would win the race, since by
consistency `halts` has none, so Σ₁-completeness would prove `halts`. A proof of `halts` at `q`
makes the race's state nonzero from `q` on, which the object theory proves by induction
(`Induct`); with the numerals below `q`, none of which proves `notHalts`, this proves
`notHalts`.
-/

namespace Incomplete
open Lean4Lean
open VExpr VEnv

/-! ### Codes on open terms -/

/-- `Nat.rec` over `prec g h`'s first variable, with its other variables `τ`. -/
def precStep (h : PR) (τ : Subst) : VExpr :=
  .lam nat (.lam nat ((h.tr.liftN 1 2).subst (τ.cons zero).lift.lift))

theorem shiftS_cons (τ : Subst) (a b : VExpr) :
    shiftS (τ.cons a).lift.lift 1 2 = shiftS (τ.cons b).lift.lift 1 2 := by
  funext i; rcases i with _ | _ | i
  · rfl
  · rfl
  · have e : liftVar 1 (i + 2) 2 = i + 1 + 2 := by rw [liftVar_le (by omega)]; omega
    simp only [shiftS]; rw [e]; rfl

theorem tr_prec_subst (g h : PR) (τ : Subst) (x : VExpr) :
    (PR.prec g h).tr.subst (τ.cons x) = natRec nat (g.tr.subst τ) (precStep h τ) x := by
  show natRec nat (g.tr.lift.subst (τ.cons x))
    (.lam nat (.lam nat ((h.tr.liftN 1 2).subst (τ.cons x).lift.lift))) x = _
  rw [lift_subst, Subst.cons_tail, precStep, liftN_subst_eq, liftN_subst_eq, shiftS_cons τ x zero]

theorem precStep_num1 (τ : Subst) : precStep (PR.num 1) τ = oneF := rfl

theorem tr_push_subst (h g : PR) (σ : Subst) :
    (PR.push h g).tr.subst σ = .app (.lam nat (g.tr.subst σ.lift)) (h.tr.subst σ) := rfl

theorem precBody_inst' (h : VExpr) (σ : Subst) (t : VExpr) :
    ((h.liftN 1 2).subst σ.lift.lift).inst t 1 = h.subst (σ.tail.cons t).lift := by
  rw [liftN_subst_eq, instN_eq, subst_subst]; congr 1; funext i
  rcases i with _ | _ | i
  · rfl
  · rfl
  · have e : liftVar 1 (i + 2) 2 = i + 1 + 2 := by rw [liftVar_le (by omega)]; omega
    simp only [Subst.comp, shiftS]; rw [e]
    show ((σ (i + 1)).lift.lift).subst _ = (σ (i + 1)).lift
    rw [← instN_eq, VExpr.lift, VExpr.lift, liftN_liftN, inst_liftN_lo]

theorem litS_cons_inst (e x a : VExpr) (ρ : Val) (k : Nat) :
    (e.subst ((litS ρ).cons x)).inst a k = e.subst ((litS ρ).cons (x.inst a k)) := by
  rw [instN_eq, subst_subst]; congr 1; funext i
  rcases i with _ | i
  · exact (instN_eq x a).symm
  · exact (Inert.lit _).subst _

section
variable {env : VEnv} {Γ : List VExpr} (H : HasNat env) (henv : env.Ordered)
include H henv

omit H henv in
theorem cons_T {τ : Subst} (hτ : ∀ i, env.HasType 0 Γ (τ i) nat) {x : VExpr}
    (hx : env.HasType 0 Γ x nat) : ∀ i, env.HasType 0 Γ ((τ.cons x) i) nat
  | 0 => hx
  | i + 1 => hτ i

omit H in
theorem lift_T {τ : Subst} (hτ : ∀ i, env.HasType 0 Γ (τ i) nat) :
    ∀ i, env.HasType 0 (nat :: Γ) (τ.lift i) nat
  | 0 => .bvar .zero
  | i + 1 => (hτ i).weak henv

theorem precBodyT' (h : PR) {τ : Subst} (hτ : ∀ i, env.HasType 0 Γ (τ i) nat) :
    env.HasType 0 (nat :: nat :: Γ) ((h.tr.liftN 1 2).subst (τ.cons zero).lift.lift) nat := by
  rw [liftN_subst_eq]
  refine h.trT H henv fun i => ?_
  match i with
  | 0 => exact .bvar .zero
  | 1 => exact .bvar (.succ .zero)
  | i + 2 =>
    have e : liftVar 1 (i + 2) 2 = i + 1 + 2 := by rw [liftVar_le (by omega)]; omega
    simp only [shiftS]; rw [e]
    exact lift_T henv (lift_T henv (cons_T hτ H.zeroT)) (i + 1 + 2)

theorem precStepT' (h : PR) {τ : Subst} (hτ : ∀ i, env.HasType 0 Γ (τ i) nat) :
    env.HasType 0 Γ (precStep h τ) (.forallE nat (.forallE nat nat)) :=
  .lam H.natT (.lam H.natT (precBodyT' H henv h hτ))

/-- `prec g h` at a successor, on open terms. -/
theorem tr_prec_succ (hΓ : OnCtx Γ (env.IsType 0)) (g h : PR) {τ : Subst}
    (hτ : ∀ i, env.HasType 0 Γ (τ i) nat) {t : VExpr} (ht : env.HasType 0 Γ t nat) :
    env.IsDefEq 0 Γ ((PR.prec g h).tr.subst (τ.cons (.app succ t)))
      (h.tr.subst ((τ.cons t).cons ((PR.prec g h).tr.subst (τ.cons t)))) nat := by
  rw [tr_prec_subst, tr_prec_subst]
  have hz : env.HasType 0 Γ (g.tr.subst τ) nat := g.trT H henv hτ
  have hs := precStepT' H henv h hτ
  have hr : env.HasType 0 Γ (natRec nat (g.tr.subst τ) (precStep h τ) t) nat :=
    H.natRecT Inert.nat (fun _ => H.natT) hz hs ht
  have h1 := H.iota_succ' henv hΓ Inert.nat (fun _ => H.natT) hz hs ht
  have hB := precBodyT' H henv h hτ
  have hBi : env.HasType 0 (nat :: Γ)
      (((h.tr.liftN 1 2).subst (τ.cons zero).lift.lift).inst t 1) nat := by
    rw [precBody_inst']
    exact h.trT H henv (lift_T henv (cons_T hτ ht))
  have b1 : env.IsDefEq 0 Γ (.app (precStep h τ) t)
      (.lam nat (((h.tr.liftN 1 2).subst (τ.cons zero).lift.lift).inst t 1)) (.forallE nat nat) :=
    IsDefEq.beta (HasType.lam H.natT hB) ht
  have e2 : (((h.tr.liftN 1 2).subst (τ.cons zero).lift.lift).inst t 1).inst
      (natRec nat (g.tr.subst τ) (precStep h τ) t) =
      h.tr.subst ((τ.cons t).cons (natRec nat (g.tr.subst τ) (precStep h τ) t)) := by
    rw [precBody_inst', Subst.cons_tail, inst_lift_cons]
  have b2 := IsDefEq.beta hBi hr
  rw [e2] at b2
  exact h1.trans ((IsDefEq.appDF b1 hr).trans b2)

/-- `push h g` on open terms. -/
theorem tr_push_beta (h g : PR) {σ : Subst} (hσ : ∀ i, env.HasType 0 Γ (σ i) nat) :
    env.IsDefEq 0 Γ ((PR.push h g).tr.subst σ) (g.tr.subst (σ.cons (h.tr.subst σ))) nat := by
  rw [tr_push_subst]
  have := IsDefEq.beta (g.trT H henv (lift_T henv hσ)) (h.trT H henv hσ)
  rwa [inst_lift_cons] at this

/-- `fn f n K` on an open `K`. -/
theorem fn_app (f : PR) (n : Nat) {K : VExpr} (hK : env.HasType 0 Γ K nat) :
    env.IsDefEq 0 Γ (.app (.app (fn f) (lit n)) K)
      (f.tr.subst ((litS (vcons n fun _ => 0)).cons K)) nat := by
  have hb : env.HasType 0 (nat :: nat :: Γ) (fnBody f) nat := by
    refine f.trT H henv fun i => ?_
    match i with
    | 0 => exact .bvar .zero
    | 1 => exact .bvar (.succ .zero)
    | i + 2 => exact ((H.litT 0 (Γ := Γ)).weak henv (B := nat)).weak henv (B := nat)
  have b1 : env.IsDefEq 0 Γ (.app (fn f) (lit n)) (.lam nat ((fnBody f).inst (lit n) 1))
      (.forallE nat nat) :=
    IsDefEq.beta (HasType.lam H.natT hb) (H.litT n)
  have hbT : env.HasType 0 (nat :: Γ) ((fnBody f).inst (lit n) 1) nat := by
    rw [fnBody_inst]; exact f.trT H henv (litS_lift_T H henv _)
  have e2 : ((fnBody f).inst (lit n) 1).inst K =
      f.tr.subst ((litS (vcons n fun _ => 0)).cons K) := by
    rw [fnBody_inst, inst_lift_cons]
  have b2 := IsDefEq.beta hbT hK
  rw [e2] at b2
  exact (IsDefEq.appDF b1 hK).trans b2

end

/-! ### The race -/

namespace PR

/-- The number of `halts f n` from `⌜f⌝` in variable `1`, at `n = ⌜f⌝`. -/
def haltsC : PR := tagC 7 5 (cpair diagC (numC (encExpr falseS)))

/-- `G` at `notHalts f ⌜f⌝`, for the certificate in variable `0` and `⌜f⌝` in variable `1`. -/
def chkNC (G : PR) : PR := push diagC G

/-- `G` at `halts f ⌜f⌝`. -/
def chkHC (G : PR) : PR := push haltsC G

/-- `1` when the certificate in variable `0` proves `halts f ⌜f⌝`, else `0`. -/
def foundC (G : PR) : PR := ifz (chkHC G) (num 1) zero

/-- The race's state at `k`: `0` until some `j ≤ k` proves `halts f ⌜f⌝`, then nonzero. -/
def stateC (G : PR) : PR :=
  prec (comp2 (foundC G) zero (var 0)) (prec (comp2 (foundC G) (succ (var 0)) (var 1)) (num 1))

/-- `0` at `k` when `k` proves `notHalts f ⌜f⌝` and the state is `0`. -/
def outC (G : PR) : PR := prec (chkNC G) (num 1)

/-- **The Rosser machine** for the checker `G`. -/
def rosserC (G : PR) : PR := push (stateC G) (outC G)

theorem vcons_eta (ν : Val) : vcons (ν 0) (tl ν) = ν := by
  funext i; cases i <;> rfl

theorem eval_chkNC (G : PR) (ν : Val) :
    (chkNC G).eval ν = G.eval (vcons (diagNum (ν 1) (ν 1)) (vcons (ν 0) (tl ν))) := by
  simp only [chkNC, eval, eval_diagC, vcons_eta]

theorem eval_chkHC (G : PR) (ν : Val) :
    (chkHC G).eval ν = G.eval (vcons (7 * pair (diagNum (ν 1) (ν 1)) (encExpr falseS) + 5)
      (vcons (ν 0) (tl ν))) := by
  simp only [chkHC, haltsC, eval, eval_tagC, eval_cpair, eval_numC, eval_diagC, vcons_eta]

theorem eval_rosserC (G : PR) (ν : Val) :
    (rosserC G).eval ν = recNat ((chkNC G).eval ν) (fun _ _ => 1) ((stateC G).eval ν) := by
  simp only [rosserC, outC, eval, tl_vcons, vcons_zero, eval_num]

theorem eval_comp2' (g a b : PR) (ν : Val) :
    ∃ ν' : Val, ν' 0 = a.eval ν ∧ ν' 1 = b.eval ν ∧ (comp2 g a b).eval ν = g.eval ν' := by
  simp only [comp2, eval, eval_ren]
  refine ⟨_, ?_, ?_, rfl⟩ <;> rfl

theorem eval_prec_comp2_zero (F h : PR) (ν : Val) :
    ∃ ν' : Val, ν' 0 = 0 ∧ ν' 1 = ν 0 ∧
      (prec (comp2 F zero (var 0)) h).eval (vcons 0 ν) = F.eval ν' :=
  eval_comp2' F zero (var 0) ν

theorem eval_stateC_zero (G : PR) (ν : Val) :
    ∃ ν' : Val, ν' 0 = 0 ∧ ν' 1 = ν 0 ∧ (stateC G).eval (vcons 0 ν) = (foundC G).eval ν' := by
  unfold stateC
  exact eval_prec_comp2_zero (foundC G) _ ν

theorem eval_stateC_succ (G : PR) (ν : Val) (k : Nat) :
    ∃ ν' : Val, ν' 0 = k + 1 ∧ ν' 1 = ν 0 ∧ (stateC G).eval (vcons (k + 1) ν) =
      recNat ((foundC G).eval ν') (fun _ _ => 1) ((stateC G).eval (vcons k ν)) := by
  obtain ⟨ν', h0, h1, h⟩ := eval_comp2' (foundC G) (succ (var 0)) (var 1) (vcons k ν)
  refine ⟨ν', h0, h1, ?_⟩
  rw [← h, stateC]
  simp only [eval, tl_vcons, vcons_zero, recNat_succ, eval_num]

theorem eval_foundC (G : PR) (ν : Val) :
    (foundC G).eval ν = if (chkHC G).eval ν = 0 then 1 else 0 := by
  simp [foundC, eval_ifz, eval_num, eval]

end PR

open PR

/-- The race's state at an open `K`, on input `e`. -/
def stateAt (G : PR) (e : Nat) (K : VExpr) : VExpr :=
  (stateC G).tr.subst ((litS (vcons e fun _ => 0)).cons K)

@[simp] theorem stateAt_inst (G : PR) (e : Nat) (K a : VExpr) (k : Nat) :
    (stateAt G e K).inst a k = stateAt G e (K.inst a k) := litS_cons_inst ..

/-- The motive `fun y => state (q + y) ≠ 0`. -/
def stateMotive (G : PR) (e q : Nat) : VExpr :=
  .lam nat (nonzero (stateAt G e (succIter q (.bvar 0))))

/-- The motive `fun k => f e k ≠ 0`. -/
def outMotive (f : PR) (e : Nat) : VExpr :=
  .lam nat (nonzero (.app (.app (fn f) (lit e)) (.bvar 0)))

section
variable {env : VEnv} (H : HasNat env) (henv : env.Ordered)
include H henv

theorem stateAtT (G : PR) (e : Nat) {Γ K} (hK : env.HasType 0 Γ K nat) :
    env.HasType 0 Γ (stateAt G e K) nat :=
  (stateC G).trT H henv (cons_T (fun _ => H.litT _) hK)

theorem stateMotiveT (G : PR) (e q : Nat) :
    env.HasType 0 [] (stateMotive G e q) (.forallE nat (.sort .zero)) :=
  .lam H.natT (nonzeroT H (stateAtT H henv G e (succIterT H (.bvar .zero) q)))

theorem stateMotive_app (G : PR) (e q : Nat) {Γ K} (hK : env.HasType 0 Γ K nat) :
    env.IsDefEq 0 Γ (.app (stateMotive G e q) K) (nonzero (stateAt G e (succIter q K)))
      (.sort .zero) := by
  have := IsDefEq.beta (nonzeroT H (stateAtT H henv G e (Γ := nat :: Γ)
    (succIterT H (.bvar .zero) q))) hK
  simpa [stateMotive, VExpr.inst] using this

theorem fn_app_T (f : PR) (e : Nat) {Γ K} (hK : env.HasType 0 Γ K nat) :
    env.HasType 0 Γ (.app (.app (fn f) (lit e)) K) nat :=
  .app' (.app' ((fnT H henv f).weak0 henv) (H.litT e) rfl) hK rfl

theorem outMotiveT (f : PR) (e : Nat) :
    env.HasType 0 [] (outMotive f e) (.forallE nat (.sort .zero)) :=
  .lam H.natT (nonzeroT H (fn_app_T H henv f e (.bvar .zero)))

theorem outMotive_app (f : PR) (e : Nat) {Γ K} (hK : env.HasType 0 Γ K nat) :
    env.IsDefEq 0 Γ (.app (outMotive f e) K) (nonzero (.app (.app (fn f) (lit e)) K))
      (.sort .zero) := by
  have hfI := Inert.ofClosed ((fnT H henv f).closedN henv trivial)
  have := IsDefEq.beta (nonzeroT H (fn_app_T H henv f e (Γ := nat :: Γ) (.bvar .zero))) hK
  simpa [outMotive, VExpr.inst, hfI.inst, (Inert.lit e).inst] using this

/-- The state is nonzero from `q` on: induction on `y` for `state (q + y) ≠ 0`. -/
theorem stateAt_nonzero (G : PR) (e q : Nat) (hq : (stateC G).eval (val2 q e) ≠ 0) :
    ∃ p, env.HasType 0 [nat] p (nonzero (stateAt G e (succIter q (.bvar 0)))) := by
  have hMT := stateMotiveT H henv G e q
  have hMTI := Inert.ofClosed (hMT.closedN henv trivial)
  have hz : env.HasType 0 [] (.lam falseS (.bvar 0)) (.app (stateMotive G e q) zero) := by
    refine (stateMotive_app H henv G e q H.zeroT).symm.defeq ?_
    have ha := (stateC G).adequate H henv (val2 q e)
    rw [show litS (val2 q e) = (litS (vcons e fun _ => 0)).cons (lit q) from (litS_cons _ _).symm,
      ← succIter_zero] at ha
    exact (IsDefEq.forallEDF (isZero_congr H ha) falseT).symm.defeq (nonzero_lit H henv hq)
  have hs : ∃ s, env.HasType 0 [] s (stepTy (stateMotive G e q)) := by
    let Γ := [.app (stateMotive G e q) (.bvar 0), nat]
    have hm0 : env.HasType 0 [nat] (.app (stateMotive G e q) (.bvar 0)) (.sort .zero) :=
      .app' (hMT.weak0 henv) (.bvar .zero) rfl
    have hΓ : OnCtx Γ (env.IsType 0) := ⟨⟨trivial, _, H.natT⟩, _, hm0⟩
    have ht : env.HasType 0 Γ (succIter q (.bvar 1)) nat := succIterT H (.bvar (.succ .zero)) q
    have hih : env.HasType 0 Γ (.bvar 0) (nonzero (stateAt G e (succIter q (.bvar 1)))) := by
      refine (stateMotive_app H henv G e q (.bvar (.succ .zero))).defeq ?_
      have := HasType.bvar (env := env) (U := 0)
        (Lookup.zero (ty := .app (stateMotive G e q) (.bvar 0)) (Γ := [nat]))
      simpa [VExpr.liftN, liftVar, hMTI.liftN] using this
    have ha : env.HasType 0 Γ ((comp2 (foundC G) (PR.succ (var 0)) (var 1)).tr.subst
        ((litS (vcons e fun _ => 0)).cons (succIter q (.bvar 1)))) nat :=
      PR.trT H henv _ (cons_T (fun _ => H.litT _) ht)
    obtain ⟨p, hp⟩ := nonzero_natRec_app H henv (stateAtT H henv G e ht) ha hih
    have hE := tr_prec_succ H henv hΓ (comp2 (foundC G) PR.zero (var 0))
      (prec (comp2 (foundC G) (PR.succ (var 0)) (var 1)) (num 1))
      (τ := litS (vcons e fun _ => 0)) (fun _ => H.litT _) ht
    rw [tr_prec_subst (comp2 (foundC G) (PR.succ (var 0)) (var 1)) (num 1), precStep_num1] at hE
    have hq' : env.HasType 0 Γ p (nonzero (stateAt G e (succIter (q + 1) (.bvar 1)))) :=
      (IsDefEq.forallEDF (isZero_congr H hE) falseT).symm.defeq hp
    rw [← succIter_succ] at hq'
    exact ⟨_, .lam H.natT (.lam hm0
      ((stateMotive_app H henv G e q (.app' H.succT (.bvar (.succ .zero)) rfl)).symm.defeq hq'))⟩
  obtain ⟨s, hs⟩ := hs
  have h0 : env.HasType 0 [nat] (.bvar 0) nat := .bvar .zero
  exact ⟨_, (stateMotive_app H henv G e q h0).defeq
    (recPT H henv hMT (hz.weak0 henv) (hs.weak0 henv) h0)⟩

/-- **The object theory proves the race never halts** when no certificate proves
`notHalts f ⌜f⌝`, and the state is nonzero at some `q`. -/
theorem provable_notHalts_rosser (G : PR) (e : Nat)
    (hR : ∀ j, (rosserC G).eval (val2 j e) ≠ 0) (q : Nat) (hq : (stateC G).eval (val2 q e) ≠ 0) :
    Provable env (notHalts (rosserC G) e) := by
  have hM := outMotiveT H henv (rosserC G) e
  have he : ∀ j, ∃ p, env.HasType 0 [] p (.app (outMotive (rosserC G) e) (lit j)) := fun j =>
    ⟨_, (outMotive_app H henv _ e (H.litT j)).symm.defeq <|
      (IsDefEq.forallEDF (isZero_congr H (fn_adequate H henv (rosserC G) e j)) falseT).symm.defeq
        (nonzero_lit H henv (hR j))⟩
  have h0 : env.HasType 0 [nat] (.bvar 0) nat := .bvar .zero
  have hK := succIterT H h0 q
  obtain ⟨pS, hpS⟩ := stateAt_nonzero H henv G e q hq
  have ha : env.HasType 0 [nat]
      ((chkNC G).tr.subst ((litS (vcons e fun _ => 0)).cons (succIter q (.bvar 0)))) nat :=
    PR.trT H henv _ (cons_T (fun _ => H.litT _) hK)
  obtain ⟨p, hp⟩ := nonzero_natRec_app H henv (stateAtT H henv G e hK) ha hpS
  have hF := (fn_app H henv (rosserC G) e hK).trans
    (tr_push_beta H henv (stateC G) (outC G) (cons_T (fun _ => H.litT _) hK))
  rw [outC, tr_prec_subst, precStep_num1] at hF
  have ht : ∃ t, env.HasType 0 [] t
      (.forallE nat (.app (outMotive (rosserC G) e) (succIter q (.bvar 0)))) :=
    ⟨_, .lam H.natT ((outMotive_app H henv _ e hK).symm.defeq
      ((IsDefEq.forallEDF (isZero_congr H hF) falseT).symm.defeq hp))⟩
  obtain ⟨p, hp⟩ := forall_of_numerals H henv hM he q ht
  exact ⟨_, .defeqDF (IsDefEq.forallEDF H.natT (outMotive_app H henv _ e h0)) hp⟩

end

/-! ### Rosser's theorem -/

theorem encExpr_halts (f : PR) (n : Nat) :
    encExpr (halts f n) = 7 * pair (encExpr (notHalts f n)) (encExpr falseS) + 5 := rfl

/-- **Rosser's theorem**, from consistency and the checkability of proofs: the non-halting
sentence `notHalts d ⌜d⌝` of the Rosser machine `d` on its own number is a closed proposition,
true of the machine, and neither provable nor refutable. -/
theorem rosser_of_check {env : VEnv} (H : HasNat env) (henv : env.Ordered)
    (hG : CheckDecidable env) (hC : Consistent env) :
    ∃ d : PR, env.HasType 0 [] (notHalts d d.code) (.sort .zero) ∧ ¬d.Halts d.code ∧
      ¬Provable env (notHalts d d.code) ∧ ¬Provable env (halts d d.code) := by
  obtain ⟨G, hG1, hG2⟩ := hG
  -- what the two checks say
  have hN : ∀ ν : Val, ν 1 = (rosserC G).code → (chkNC G).eval ν = 0 →
      Provable env (notHalts (rosserC G) (rosserC G).code) := by
    intro ν h1 h
    rw [eval_chkNC, h1, diagNum_code] at h
    exact hG1 _ _ _ h
  have hH : ∀ ν : Val, ν 1 = (rosserC G).code → (chkHC G).eval ν = 0 →
      Provable env (halts (rosserC G) (rosserC G).code) := by
    intro ν h1 h
    rw [eval_chkHC, h1, diagNum_code, ← encExpr_halts] at h
    exact hG1 _ _ _ h
  have hHc : Provable env (halts (rosserC G) (rosserC G).code) → ∃ q, ∀ ν : Val, ν 0 = q →
      ν 1 = (rosserC G).code → (chkHC G).eval ν = 0 := by
    intro hp
    obtain ⟨q, hq⟩ := hG2 _ hp
    exact ⟨q, fun ν h0 h1 => by rw [eval_chkHC, h1, diagNum_code, ← encExpr_halts, h0]; exact hq _⟩
  -- the state stays `0` without a proof of `halts`, and is nonzero after one
  have state0 : ¬Provable env (halts (rosserC G) (rosserC G).code) →
      ∀ k (ν : Val), ν 0 = (rosserC G).code → (stateC G).eval (vcons k ν) = 0 := by
    intro hn k ν hν
    have hf : ∀ ν' : Val, ν' 1 = (rosserC G).code → (foundC G).eval ν' = 0 := fun ν' h1 => by
      rw [eval_foundC, ite_eq_right fun h => hn (hH ν' h1 h)]
    induction k with
    | zero => obtain ⟨ν', _, h1, h⟩ := eval_stateC_zero G ν; rw [h]; exact hf ν' (h1.trans hν)
    | succ k ih =>
      obtain ⟨ν', _, h1, h⟩ := eval_stateC_succ G ν k
      rw [h, ih]; exact hf ν' (h1.trans hν)
  have stateq : Provable env (halts (rosserC G) (rosserC G).code) →
      ∃ q, (stateC G).eval (val2 q (rosserC G).code) ≠ 0 := by
    intro hp
    obtain ⟨q, hq⟩ := hHc hp
    have hf : ∀ ν' : Val, ν' 0 = q → ν' 1 = (rosserC G).code → (foundC G).eval ν' = 1 :=
      fun ν' h0 h1 => by rw [eval_foundC, ite_eq_left (hq ν' h0 h1)]
    refine ⟨q, ?_⟩
    cases q with
    | zero =>
      obtain ⟨ν', h0, h1, h⟩ := eval_stateC_zero G (vcons (rosserC G).code fun _ => 0)
      rw [val2, h, hf ν' h0 h1]; omega
    | succ k =>
      obtain ⟨ν', h0, h1, h⟩ := eval_stateC_succ G (vcons (rosserC G).code fun _ => 0) k
      rw [val2, h]
      cases (stateC G).eval (vcons k (vcons (rosserC G).code fun _ => 0)) with
      | zero => rw [recNat, hf ν' h0 h1]; omega
      | succ => simp [recNat]
  have hNP : ¬Provable env (notHalts (rosserC G) (rosserC G).code) := by
    intro hp
    have hn : ¬Provable env (halts (rosserC G) (rosserC G).code) := fun hh => hC (refute hh hp)
    obtain ⟨k, hk⟩ := hG2 _ hp
    refine hn (halts_provable H henv ⟨k, ?_⟩)
    rw [eval_rosserC, val2, state0 hn k _ rfl, recNat, eval_chkNC]
    simp only [vcons_succ, vcons_zero, tl_vcons, diagNum_code]
    exact hk _
  have hHP : ¬Provable env (halts (rosserC G) (rosserC G).code) := by
    intro hh
    have hR : ∀ j, (rosserC G).eval (val2 j (rosserC G).code) ≠ 0 := by
      intro j
      rw [eval_rosserC]
      cases (stateC G).eval (val2 j (rosserC G).code) with
      | zero => exact fun h => hNP (hN _ rfl h)
      | succ => simp [recNat]
    obtain ⟨q, hq⟩ := stateq hh
    exact hC (refute hh (provable_notHalts_rosser H henv G _ hR q hq))
  refine ⟨rosserC G, ?_, ?_, hNP, hHP⟩
  · exact forallE_prop H.natT (nonzeroT H (fn_app_T H henv _ _ (.bvar .zero)))
  · rintro ⟨k, hk⟩
    rw [eval_rosserC] at hk
    revert hk
    cases (stateC G).eval (val2 k (rosserC G).code) with
    | zero => exact fun h => hNP (hN _ rfl h)
    | succ => simp [recNat]

/-- **Rosser's incompleteness theorem.** A consistent well-formed extension of `natEnv` neither
proves nor refutes the true non-halting sentence of some machine on its own number. -/
theorem incomplete_rosser (env : VEnv) (hwf : env.WF) (hext : natEnv ≤ env) (hC : Consistent env) :
    ∃ d : PR, env.HasType 0 [] (notHalts d d.code) (.sort .zero) ∧ ¬d.Halts d.code ∧
      ¬Provable env (notHalts d d.code) ∧ ¬Provable env (halts d d.code) := by
  obtain ⟨T, hT⟩ := hwf.checkable.tables
  exact rosser_of_check (hasNat_natEnv.mono hext) hwf.checkable.ordered
    (checkDecidable_of_tables hT) hC

/-- **Rosser's incompleteness theorem**, for a consistent well-formed environment that declares
`Nat`. -/
theorem incomplete_rosser' {ds : List VDecl} {env : VEnv} (H : env.WF' ds)
    (hm : .induct natDecl ∈ ds) (hC : Consistent env) :
    ∃ d : PR, env.HasType 0 [] (notHalts d d.code) (.sort .zero) ∧ ¬d.Halts d.code ∧
      ¬Provable env (notHalts d d.code) ∧ ¬Provable env (halts d d.code) :=
  incomplete_rosser env ⟨ds, H⟩ (natEnv_le_of_mem H hm) hC

end Incomplete
