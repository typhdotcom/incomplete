import Incomplete.Obj.Second

/-!
# Löb's theorem

`Prov T P` is `∃ k, Prf(⌜P⌝, k)`. The Löb machine `loebM T ⌜P⌝` at its input `x` and witness `k`
runs the checker on `⌜H x → P⌝` and `k`, where `H x` is the positive halting sentence
`∃ k, IsZero (x x k)` (`haltsE`). For its own code `d`, `H := haltsE d ⌜d⌝` and `ψ := H → P`, so
`d` at `⌜d⌝` and `k` is `Prf(⌜ψ⌝, k)` (`fn_loebM_code`). Inside the theory, a witness `k` of `H`
is a proof of `ψ`, and by internal Σ₁-completeness `σ k` is a proof of `H`; modus ponens gives a
proof of `P`, so `Prov T P`, and the hypothesis `Prov T P → P` gives `P`: the theory proves `ψ`
(`loeb_of_fn`). Then `ψ` has a closed certificate, a witness of `H`, and `P` follows (`loeb`).
-/

namespace Incomplete
open Lean4Lean Obj PR

/-- **Provability**, as a sentence: some certificate checks as a proof of `P`. -/
noncomputable def Prov (T : Tables) (P : VExpr) : VExpr := ∃ₒ k, prfT T (numT (encExpr P)) k =ₒ zero

/-- Halts exactly when some certificate checks as a proof of `P`. -/
noncomputable def provM (T : Tables) (P : VExpr) : PR := push (numC (encExpr P)) (chkT T)

theorem conM_eq (T : Tables) : conM T = provM T falseS := rfl

theorem provM_halts_iff {env : VEnv} {T : Tables} (hT : TablesFor env T) (P : VExpr) :
    (provM T P).Halts 0 ↔ Provable env P := by
  rw [← chkNum_eq_zero hT]
  simp only [PR.Halts, provM, PR.eval, eval_chkT, eval_numC, vcons_zero, vcons_succ, val2]

end Incomplete

namespace Incomplete.Obj
open Lean4Lean
open VExpr VEnv PR

/-- `∃ k, IsZero (f n k)`: `f` halts on `n`, positively. -/
def haltsE (f : PR) (n : Nat) : VExpr := ∃ₒ k, isZero (app2 (fn f) (lit n) k)

/-- `haltsE f x`, with the machine's argument `x` a term. -/
def haltsEV (f : PR) (x : VExpr) : VExpr := ∃ₒ k, isZero (app2 (fn f) x.lift k)

/-- The number of `IsZero (f n k)`, with `k` the variable `0`, from the number `x` of `fn f`. -/
def isZNum (x n : Nat) : Nat :=
  7 * PR.pair (encExpr (.appN (.const ``Nat.rec [.succ .zero])
      [motive (.sort .zero), trueS, .lam nat (.lam (.sort .zero) falseS)]))
    (7 * PR.pair (7 * PR.pair x (encExpr (lit n)) + 3) (encExpr (.bvar 0)) + 3) + 3

/-- The number of `haltsE f n` from the number `x` of `fn f`. -/
def haltsENum (x n : Nat) : Nat :=
  7 * PR.pair (encExpr (.sort .zero)) (7 * PR.pair (7 * PR.pair (encExpr nat)
    (7 * PR.pair (isZNum x n) (encExpr (.bvar 2)) + 5) + 5) (encExpr (.bvar 1)) + 5) + 5

/-- The number of `haltsE f ⌜f⌝ → P` from the number `x` of `fn f` and the number `p` of `P`. -/
def loebNum (p x : Nat) : Nat := 7 * PR.pair (haltsENum x x) p + 5

theorem haltsENum_code (f : PR) (n : Nat) : haltsENum f.code n = encExpr (haltsE f n) := by
  simp only [haltsE, ex, imp, all, app2, obj_simp]
  simp only [haltsENum, isZNum, PR.code, isZero, natRec, VExpr.appN, encExpr]

theorem loebNum_code {P : VExpr} (hP : P.ClosedN) (f : PR) :
    loebNum (encExpr P) f.code = encExpr (imp (haltsE f f.code) P) := by
  have e : imp (haltsE f f.code) P = .forallE (haltsE f f.code) P := by
    show VExpr.forallE _ (P.liftN 1 0) = _; rw [hP.liftN_eq (Nat.zero_le _)]
  rw [e, loebNum, haltsENum_code]; rfl

/-- Computes `isZNum x x` from `x` in variable `0`. -/
def isZC : PR :=
  tagC 7 3 (cpair (numC (encExpr (.appN (.const ``Nat.rec [.succ .zero])
      [motive (.sort .zero), trueS, .lam nat (.lam (.sort .zero) falseS)])))
    (tagC 7 3 (cpair (tagC 7 3 (cpair (var 0) litC)) (numC (encExpr (.bvar 0))))))

/-- Computes `loebNum p x` from `x` in variable `0`. -/
def loebC (p : Nat) : PR :=
  tagC 7 5 (cpair (tagC 7 5 (cpair (numC (encExpr (.sort .zero))) (tagC 7 5 (cpair
    (tagC 7 5 (cpair (numC (encExpr nat)) (tagC 7 5 (cpair isZC (numC (encExpr (.bvar 2)))))))
    (numC (encExpr (.bvar 1))))))) (numC p))

theorem loebC_computes (p : Nat) : Computes1 (loebC p) (loebNum p) := by
  intro ρ
  simp only [loebC, isZC, eval_tagC, eval_cpair, eval_numC, eval_var, litC_computes ρ]
  rfl

/-- **The Löb machine** for the sentence numbered `p`: at input `x` and witness `k`, the checker
at `⌜haltsE x x → P⌝` and `k`. -/
noncomputable def loebM (T : Tables) (p : Nat) : PR := push (ren Nat.succ (loebC p)) (chkT T)

theorem haltsEV_inst (f : PR) (d : Nat) : (haltsEV f (.bvar 1)).inst (lit d) 1 = haltsE f d := by
  simp only [haltsEV, haltsE, obj_simp]

section
variable {env : VEnv} [E : ObjEnv env] {Γ : List VExpr} {T : Tables}

theorem haltsEVTy {f : PR} {x : VExpr} (hx : Tm env Γ x) :
    env.HasType 0 Γ (haltsEV f x) (.sort .zero) := by
  unfold haltsEV; otype

theorem haltsETy (f : PR) (n : Nat) : env.HasType 0 Γ (haltsE f n) (.sort .zero) := by
  unfold haltsE; otype

theorem ProvTy (T : Tables) (P : VExpr) : env.HasType 0 Γ (Prov T P) (.sort .zero) := by
  unfold Prov; otype

end

macro_rules | `(tactic| otype_rules) => `(tactic| with_reducible exact haltsETy _ _)
macro_rules | `(tactic| otype_rules) => `(tactic| with_reducible exact ProvTy _ _)
macro_rules | `(tactic| otype_rules) => `(tactic| ((with_reducible refine haltsEVTy ?_); otype))

theorem haltsE_closed (f : PR) (n : Nat) : (haltsE f n).ClosedN :=
  (haltsETy (env := natEnv) (Γ := []) f n).closedN natEnv_ordered trivial

theorem Prov_closed (T : Tables) (P : VExpr) : (Prov T P).ClosedN :=
  (ProvTy (env := natEnv) (Γ := []) T P).closedN natEnv_ordered trivial

@[obj_simp] theorem Prov_liftN {T : Tables} {P : VExpr} {n k : Nat} :
    (Prov T P).liftN n k = Prov T P := (Prov_closed T P).liftN_eq (Nat.zero_le _)
@[obj_simp] theorem Prov_inst {T : Tables} {P e : VExpr} {k : Nat} :
    (Prov T P).inst e k = Prov T P := (Prov_closed T P).instN_eq (Nat.zero_le _)

section
variable {env : VEnv} [E : ObjEnv env] {Γ : List VExpr} {T : Tables} {k : VExpr} {p : Nat}

theorem gp_finE {f : PR} {x : VExpr} (hk : Tm env Γ k) (hx : Tm env Γ x) :
    Thm env Γ (imp (ev f [k, x] =ₒ zero) (haltsEV f x)) := by
  unfold haltsEV
  ointro h
  oexists k.lift
  refine isZero_of_eq_zero (by otype) ?_
  orw [fn_ev (by otype) (by otype)]
  exact h


theorem ev_loebC (hk : Tm env Γ k) (e : Nat) :
    Thm env Γ (ev (ren Nat.succ (loebC p)) [k, lit e] =ₒ numT (loebNum p e)) := by
  have h : Thm env Γ (ev (loebC p) [lit e] =ₒ lit (loebNum p e)) := by
    have h := ev_lits (env := env) (Γ := Γ) (loebC p) [e]
    rw [loebC_computes] at h
    exact h
  exact Thm.trans (by otype) (by otype) (by otype)
    (ev_ren_eq Nat.succ (.cons hk (.cons (litTy e) .nil)) (l' := [lit e]) (valS_succ _ _))
    (Thm.trans (by otype) (by otype) (by otype) h (Thm.symm (by otype) (by otype) (numT_lit _)))

/-- A machine running the checker on the sentence numbered by `h`'s value. -/
theorem fn_push_chkT {h : PR} {s : VExpr} (hs : Tm env Γ s) (hk : Tm env Γ k) (e : Nat)
    (hh : Thm env Γ (ev h [k, lit e] =ₒ s)) :
    Thm env Γ (app2 (fn (push h (chkT T))) (lit e) k =ₒ prfT T s k) := by
  orw [fn_ev (litTy e) hk, ev_push (f := push h (chkT T)) rfl (by otype)]
  rw [ev_take 2 (bnd_chkT T)]
  simp only [List.take_succ_cons, List.take_zero]
  orw [hh]

theorem fn_loebM (hk : Tm env Γ k) (e : Nat) :
    Thm env Γ (app2 (fn (loebM T p)) (lit e) k =ₒ prfT T (numT (loebNum p e)) k) :=
  fn_push_chkT (by otype) hk e (ev_loebC hk e)

/-- `loebM T ⌜P⌝` at its own code `⌜d⌝` and `k` is `Prf(⌜haltsE d ⌜d⌝ → P⌝, k)`. -/
theorem fn_loebM_code {P : VExpr} (hP : P.ClosedN) (hk : Tm env Γ k) :
    Thm env Γ (app2 (fn (loebM T (encExpr P))) (lit (loebM T (encExpr P)).code) k =ₒ
      prfT T (numT (encExpr (imp (haltsE (loebM T (encExpr P)) (loebM T (encExpr P)).code) P)))
        k) := by
  have h := fn_loebM (T := T) (p := encExpr P) hk (loebM T (encExpr P)).code
  rw [loebNum_code hP] at h
  exact h

/-- `provM T P` at `0` and `k` is `Prf(⌜P⌝, k)`. -/
theorem fn_provM {P : VExpr} (hk : Tm env Γ k) :
    Thm env Γ (app2 (fn (provM T P)) (lit 0) k =ₒ prfT T (numT (encExpr P)) k) :=
  fn_push_chkT (by otype) hk 0 (by rw [ev_numC_ctx]; orefl)

/-- **Internal Σ₁-completeness for `haltsE`.** If `f` at `d` and `k` is `Prf(⌜A⌝, k)`, then for
some code `σ` the theory proves `∀ k, Prf(⌜A⌝, k) → Prf(⌜haltsE f d⌝, σ k)`. -/
theorem sigma_E (hT : TablesFor env T) {f : PR} {d : Nat} {A : VExpr}
    (hf : ∀ {Γ : List VExpr} {k : VExpr}, Tm env Γ k →
      Thm env Γ (app2 (fn f) (lit d) k =ₒ prfT T (numT (encExpr A)) k)) :
    ∃ σ : PR, Thm env [] (∀ₒ k, prfT T (numT (encExpr A)) k =ₒ zero →ₒ
      prfT T (numT (encExpr (haltsE f d))) (ev σ [k]) =ₒ zero) := by
  have hG : Thm env [] (allN 2 (imp ((valF f 2).inst zero 0) (haltsEV f (.bvar 1)))) := by
    rw [valF_fin_eq]
    exact allN_intro (env := env) 2 (Γ := []) (gp_finE (bvar_rep (by omega)) (bvar_rep (by omega)))
  exact sigma_of_fin hT (haltsEV_inst f d) (haltsE_closed f d) hG hf

/-- **The internal step of Löb's theorem**, over a code `f` and an input `d` at which `f` reads
`Prf(⌜H → P⌝, ·)` for `H := haltsE f d`: from `σ` turning proofs of `H → P` into proofs of `H`
and from `Prov T P → P`, the theory proves `H → P`. A witness `k` of `H` is a proof of `H → P`,
`σ k` one of `H`, so modus ponens gives a proof of `P`, hence `Prov T P`, hence `P`. -/
theorem loeb_of_fn {f σ : PR} {d : Nat} {P : VExpr} (hPc : P.ClosedN)
    (hPT : env.HasType 0 [] P (.sort .zero))
    (hf : ∀ {Γ : List VExpr} {k : VExpr}, Tm env Γ k →
      Thm env Γ (app2 (fn f) (lit d) k =ₒ prfT T (numT (encExpr (imp (haltsE f d) P))) k))
    (hσ : Thm env [] (∀ₒ k, prfT T (numT (encExpr (imp (haltsE f d) P))) k =ₒ zero →ₒ
      prfT T (numT (encExpr (haltsE f d))) (ev σ [k]) =ₒ zero))
    (hL : Thm env [] (imp (Prov T P) P)) :
    Thm env [] (imp (haltsE f d) P) := by
  have hPl : ∀ n j, P.liftN n j = P := fun n j => hPc.liftN_eq (Nat.zero_le _)
  have hP0 : ∀ {Δ : List VExpr}, env.HasType 0 Δ P (.sort .zero) := closedTy hPT
  unfold haltsE
  ointro hH
  ocases hH with hk
  simp only [hPl]
  generalize hΔ : [isZero (app2 (fn f) (lit d) (.bvar 0)), nat,
    ex (isZero (app2 (fn f) (lit d) (.bvar 0)))] = Δ at hk ⊢
  have hkT : Tm env Δ (.bvar 1) := by subst hΔ; otype
  have hz := eq_zero_of_isZero (by otype) hk
  orw [hf hkT] at hz
  have hs := Thm.allE (hσ.weak0 (Γ := Δ)) (t := .bvar 1) hkT
  simp only [obj_simp] at hs
  have hm := prf_mpT hPc hkT (by otype) hz (hs.mp hz)
  have hProv : Thm env Δ (Prov T P) := by
    unfold Prov
    refine Thm.exI (t := mpT (haltsE f d) P (fldT 1 (jT (.bvar 1))) (fldT 1 (jT (ev σ [.bvar 1])))
      (.bvar 1) (ev σ [.bvar 1])) (by otype) (by otype) ?_
    simp only [obj_simp]
    exact hm
  exact hL.weak0.mp hProv

/-- **Löb's theorem over a code `f` and an input `d`** at which `f` reads `Prf(⌜H → P⌝, ·)` for
`H := haltsE f d`. The theory proves `H → P` (`loeb_of_fn`); that proof has a closed certificate
`c`, so `f` at `d` and `c` is `0`, a witness of `H`; then `P`. -/
theorem loeb_core (hT : TablesFor env T) {f : PR} {d : Nat} {P : VExpr} (hPc : P.ClosedN)
    (hPT : env.HasType 0 [] P (.sort .zero))
    (hf : ∀ {Γ : List VExpr} {k : VExpr}, Tm env Γ k →
      Thm env Γ (app2 (fn f) (lit d) k =ₒ prfT T (numT (encExpr (imp (haltsE f d) P))) k))
    (hL : Thm env [] (imp (Prov T P) P)) : Thm env [] P := by
  obtain ⟨σ, hσ⟩ := sigma_E hT hf
  have hψ := loeb_of_fn hPc hPT hf hσ hL
  obtain ⟨c, hc⟩ := closed_prf hT hψ
  have h1 : Thm env [] (prfT T (numT (encExpr (imp (haltsE f d) P))) (numT c) =ₒ zero) :=
    prf_congr (by otype) (by otype) (by otype) (tmplH_nil _ 0) hc
  have h2 : Thm env [] (app2 (fn f) (lit d) (numT c) =ₒ zero) := by
    orw [hf (by otype)]; exact h1
  have hH : Thm env [] (haltsE f d) := by
    unfold haltsE
    refine Thm.exI (t := numT c) (by otype) (by otype) ?_
    simp only [obj_simp]
    exact isZero_of_eq_zero (by otype) h2
  exact hψ.mp hH

/-- A code `cm` reading `Prf(⌜P⌝, ·)` at `n` never halts on `n` exactly when `P` is not
provable: `notHalts cm n ↔ ¬Prov T P`, inside the theory. -/
theorem notHalts_iff_of_fn {cm : PR} {n : Nat} {P : VExpr}
    (hcm : ∀ {Γ : List VExpr} {k : VExpr}, Tm env Γ k →
      Thm env Γ (app2 (fn cm) (lit n) k =ₒ prfT T (numT (encExpr P)) k)) :
    Thm env [] (iff (notHalts cm n) (neg (Prov T P))) := by
  show Thm env [] (iff (all (imp (isZero (app2 (fn cm) (lit n) (.bvar 0))) falseS))
    (imp (Prov T P) falseS))
  osplit
  · ointro hn
    ointro hp
    unfold Prov at hp
    ocases hp with hk
    olift hn
    generalize hΔ : [prfT T (numT (encExpr P)) (.bvar 0) =ₒ zero, nat,
      Prov T P, all (imp (isZero (app2 (fn cm) (lit n) (.bvar 0))) falseS)] = Δ at hk hn ⊢
    have hkT : Tm env Δ (.bvar 1) := by subst hΔ; otype
    orw [← hcm hkT] at hk
    have h := Thm.allE hn (t := .bvar 1) hkT
    simp only [obj_simp] at h
    exact h.mp (isZero_of_eq_zero (by otype) hk)
  · ointro hnp
    ointro
    ointro hz
    olift hnp
    generalize hΔ : [isZero (app2 (fn cm) (lit n) (.bvar 0)), nat,
      imp (Prov T P) falseS] = Δ at hz hnp ⊢
    have hkT : Tm env Δ (.bvar 1) := by subst hΔ; otype
    have h := eq_zero_of_isZero (by otype) hz
    orw [hcm hkT] at h
    refine hnp.mp ?_
    unfold Prov
    refine Thm.exI (t := .bvar 1) (by otype) hkT ?_
    simp only [obj_simp]
    exact h

end

end Incomplete.Obj

namespace Incomplete
open Lean4Lean Obj

section
variable {env : VEnv} {T : Tables}

/-- `Prov T P` is a closed proposition. -/
theorem ProvT (H : HasNat env) (henv : env.Ordered) (T : Tables) (P : VExpr) :
    env.HasType 0 [] (Prov T P) (.sort .zero) :=
  @ProvTy env ⟨H, henv⟩ [] T P

/-- **Necessitation (D1).** A provable `P` is provably provable. -/
theorem prov_of_provable (H : HasNat env) (henv : env.Ordered) (hT : TablesFor env T) {P : VExpr}
    (h : Provable env P) : Provable env (Prov T P) := by
  have : ObjEnv env := ⟨H, henv⟩
  obtain ⟨e, c, hc⟩ := provable_cert hT h
  have h1 := prfT_of_cert (T := T) (s := numT (encExpr P)) (e := numT (encExpr e)) (by otype)
    (by otype) (by otype) (hc (env := env) (Γ := [])).1 (hc (env := env) (Γ := [])).2
  unfold Prov
  refine (Thm.exI (t := numT c) (by otype) (by otype) ?_).provable
  simp only [obj_simp]
  exact h1

/-- The body of `Prov T P` at the numeral `k` is, provably, the checker's verdict on `⌜P⌝` and
`k`. -/
theorem prov_lit [ObjEnv env] (T : Tables) (P : VExpr) (k : Nat) :
    Thm env [] (prfT T (numT (encExpr P)) (lit k) =ₒ
      lit (chkNumFor T (fun _ => true) (encExpr P) k)) := by
  have h := ev_lits (env := env) (Γ := []) (chkT T) [encExpr P, k]
  rw [eval_chkT] at h
  orw [numT_lit]
  exact h

/-- **The external reading of `Prov T P`**: in a consistent theory, `Prov T P` has a provable
numeral witness exactly when `P` is provable. -/
theorem prov_lit_iff (H : HasNat env) (henv : env.Ordered) (hT : TablesFor env T)
    (hC : Consistent env) (P : VExpr) :
    (∃ k : Nat, Provable env (prfT T (numT (encExpr P)) (lit k) =ₒ zero)) ↔ Provable env P := by
  have : ObjEnv env := ⟨H, henv⟩
  rw [← chkNum_eq_zero hT]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have e : Thm env [] (lit (chkNumFor T (fun _ => true) (encExpr P) k) =ₒ zero) :=
      Thm.trans (by otype) (by otype) (by otype)
        (Thm.symm (by otype) (by otype) (prov_lit T P k)) hk
    generalize chkNumFor T (fun _ => true) (encExpr P) k = m at e
    cases m with
    | zero => rfl
    | succ m => exact absurd (Thm.absurd (succ_ne_zero (litTy m)) e).provable hC
  · rintro ⟨k, hk⟩
    have e := prov_lit (env := env) T P k
    rw [hk] at e
    exact ⟨k, e⟩

/-- `notHalts (provM T P) 0 ↔ ¬Prov T P` inside the theory. -/
theorem notHalts_provM_iff (H : HasNat env) (henv : env.Ordered) (T : Tables) (P : VExpr) :
    Provable env (iff (notHalts (provM T P) 0) (neg (Prov T P))) := by
  have : ObjEnv env := ⟨H, henv⟩
  exact (notHalts_iff_of_fn fun hk => fn_provM hk).provable

/-- **Consistency is unprovability of `⊥`**, inside the theory: `Con T ↔ ¬Prov T ⊥`. -/
theorem con_iff_not_prov (H : HasNat env) (henv : env.Ordered) (T : Tables) :
    Provable env (iff (Con T) (neg (Prov T falseS))) :=
  notHalts_provM_iff H henv T falseS

/-- The double-negation form follows from the positive one: `Prov T P → halts (provM T P) 0`. -/
theorem prov_imp_halts (H : HasNat env) (henv : env.Ordered) (T : Tables) (P : VExpr) :
    Provable env (imp (Prov T P) (halts (provM T P) 0)) := by
  have : ObjEnv env := ⟨H, henv⟩
  have hN : (notHalts (provM T P) 0).ClosedN := (notHalts_prop H henv _ _).closedN henv trivial
  have hNT : ∀ {Γ}, env.HasType 0 Γ (notHalts (provM T P) 0) (.sort .zero) :=
    closedTy (notHalts_prop H henv _ _)
  have hi : Thm env [] (imp (notHalts (provM T P) 0) (neg (Prov T P))) :=
    Thm.iffE1 hNT (negTy (by otype)) (notHalts_provM_iff H henv T P)
  refine Thm.intro (by otype) ?_
  rw [(halts_closed (provM T P) 0).lift_eq, halts_eq]
  refine Thm.intro hNT ?_
  have hn : Thm env [notHalts (provM T P) 0, Prov T P] (notHalts (provM T P) 0) :=
    (Thm.hyp .zero).cast hN.lift_eq
  have hp : Thm env [notHalts (provM T P) 0, Prov T P] (Prov T P) :=
    (Thm.hyp (.succ .zero)).cast (by rw [(Prov_closed T P).lift_eq, (Prov_closed T P).lift_eq])
  exact ((hi.weak0 (Γ := [notHalts (provM T P) 0, Prov T P])).mp hn).mp hp

/-- **Löb's theorem.** For a closed proposition `P` of a well-formed extension of `natEnv`, if
the theory proves `Prov T P → P`, it proves `P`. -/
theorem loeb (env : VEnv) (hwf : env.WF) (hext : natEnv ≤ env) {T : Tables}
    (hT : TablesFor env T) {P : VExpr} (hP : env.HasType 0 [] P (.sort .zero))
    (h : Provable env (.forallE (Prov T P) P)) : Provable env P := by
  have : ObjEnv env := ⟨hasNat_natEnv.mono hext, hwf.ordered⟩
  have hPc : P.ClosedN := hP.closedN hwf.ordered trivial
  have hL : Thm env [] (imp (Prov T P) P) := by
    show Thm env [] (.forallE _ (P.liftN 1 0))
    rw [hPc.liftN_eq (Nat.zero_le _)]
    exact h
  exact (loeb_core hT hPc hP (fun hk => fn_loebM_code hPc hk) hL).provable

/-- Löb's theorem with the double-negation provability sentence `halts (provM T P) 0`. -/
theorem loeb_halts (env : VEnv) (hwf : env.WF) (hext : natEnv ≤ env) {T : Tables}
    (hT : TablesFor env T) {P : VExpr} (hP : env.HasType 0 [] P (.sort .zero))
    (h : Provable env (.forallE (halts (provM T P) 0) P)) : Provable env P := by
  have : ObjEnv env := ⟨hasNat_natEnv.mono hext, hwf.ordered⟩
  have H := hasNat_natEnv.mono hext
  have hPc : P.ClosedN := hP.closedN hwf.ordered trivial
  refine loeb env hwf hext hT hP ?_
  have hi : Thm env [] (imp (Prov T P) (halts (provM T P) 0)) := prov_imp_halts H hwf.ordered T P
  have hh : Thm env [] (imp (halts (provM T P) 0) P) := by
    show Thm env [] (.forallE _ (P.liftN 1 0))
    rw [hPc.liftN_eq (Nat.zero_le _)]
    exact h
  have hP0 : ∀ {Γ : List VExpr}, env.HasType 0 Γ P (.sort .zero) := closedTy hP
  have : Thm env [] (imp (Prov T P) P) := by
    ointro hp
    have := (hh.weak0 (Γ := [Prov T P])).mp ((hi.weak0 (Γ := [Prov T P])).mp hp)
    rw [hPc.lift_eq]
    exact this
  have e : imp (Prov T P) P = .forallE (Prov T P) P := by
    show VExpr.forallE _ (P.liftN 1 0) = _; rw [hPc.liftN_eq (Nat.zero_le _)]
  rw [← e]; exact this

/-- `con_unprovable`, from Löb's theorem at `P := ⊥`: a proof of `Con T`, that is of
`Prov T ⊥ → ⊥`, gives one of `⊥`. -/
theorem con_unprovable_of_loeb (env : VEnv) (hwf : env.WF) (hext : natEnv ≤ env) {T : Tables}
    (hT : TablesFor env T) (hC : Consistent env) : ¬Provable env (Con T) := by
  intro hcon
  have : ObjEnv env := ⟨hasNat_natEnv.mono hext, hwf.ordered⟩
  have H := hasNat_natEnv.mono hext
  have hi := Thm.iffE1 (ConT H hwf.ordered) (negTy (by otype)) (con_iff_not_prov H hwf.ordered T)
  exact hC (loeb env hwf hext hT falseT (hi.mp hcon))

/-- With 1-consistency for halting sentences, `Prov T P` is provable only when `P` is. -/
theorem prov_sound (H : HasNat env) (henv : env.Ordered) (hT : TablesFor env T)
    (hS : HaltsSound env) {P : VExpr} (h : Provable env (Prov T P)) : Provable env P := by
  have : ObjEnv env := ⟨H, henv⟩
  exact (provM_halts_iff hT P).1 (hS _ _ (Thm.mp (prov_imp_halts H henv T P) h))

end

end Incomplete
