import Incomplete.Obj.Sigma
import Incomplete.Obj.Reduce

/-!
# The second incompleteness theorem

A proof `k` of the diagonal sentence `G0 T` is a halting witness for `dg T` at its own code:
`dg T` at `⌜dg T⌝` and `k` is `Prf(⌜G0 T⌝, k)`. By internal Σ₁-completeness the theory turns it
into a proof of `halts (dg T) ⌜dg T⌝`, that is of `G0 T → ⊥`: internally,
`∀ k, Prf(⌜G0 T⌝, k) → Prf(⌜G0 T → ⊥⌝, σ k)` for a code `σ` (`sigma_of`). So the theory proves
`Con T → G0 T` (`con_imp_G0_provable`), and a consistent theory does not prove `Con T`
(`con_unprovable`).
-/

namespace Incomplete.Obj
open Lean4Lean
open VExpr Typing PR

/-- Exchanging variables `0` and `1`. -/
def swap01 : Nat → Nat
  | 0 => 1
  | 1 => 0
  | i + 2 => i + 2

theorem valS_swap01 (a b : VExpr) (i : Nat) : valS [a, b] (swap01 i) = valS [b, a] i := by
  rcases i with _ | _ | i <;> simp [swap01, valS]

/-- `halts f x`, with the machine's argument `x` a term. -/
def haltsV (f : PR) (x : VExpr) : VExpr :=
  imp (all (imp (isZero (app2 (fn f) x.lift (.bvar 0))) falseS)) falseS

theorem haltsV_lit (f : PR) (d : Nat) : haltsV f (lit d) = halts f d := by
  simp only [haltsV, halts, notHalts, imp, all, app2, obj_simp]

section
variable {env : Typing} [E : ObjEnv env] {Γ : List VExpr} {T : PR}

theorem gp_fin {f : PR} {k x : VExpr} (hk : Tm env Γ k) (hx : Tm env Γ x) :
    Thm env Γ (imp (ev f [k, x] =ₒ zero) (haltsV f x)) := by
  unfold haltsV
  ointro h
  ointro hn
  olift h
  have hk' := Thm.allE hn (t := (k.liftN 1 0).liftN 1 0) (by otype)
  simp only [obj_simp] at hk'
  refine hk'.mp (isZero_of_eq_zero (by otype) ?_)
  orw [fn_ev (by otype) (by otype)]
  exact h

theorem valF_fin_eq (f : PR) : (valF f 2).inst zero 0 = (ev f [.bvar 0, .bvar 1] =ₒ zero) := by
  simp only [valF, args, obj_simp]

theorem litT_lit (d : Nat) : Thm env Γ (litT (lit d) =ₒ numT (encExpr (lit d))) := by
  have h := ev_lits (env := env) (Γ := Γ) litC [d]
  rw [litC_computes] at h
  simp only [List.map_cons, List.map_nil, List.getD_cons_zero] at h
  orw [h, numT_lit]

theorem lit_closed (d : Nat) : (lit d).ClosedN :=
  (hasNat_natEnv.litT d (Γ := []) (U := 0)).closedN natEnv_ordered trivial

theorem halts_closed (f : PR) (d : Nat) : (halts f d).ClosedN :=
  ⟨(notHalts_prop hasNat_natEnv natEnv_ordered f d).closedN natEnv_ordered trivial,
    falseS_closed.mono (Nat.zero_le _)⟩

variable {z s : Nat} (hA : AllH env T z s) (hT : IsChecker env T)
include hA hT

/-- From `f` at `[k, lit d]` being `0`, a proof of `B`, given a proof `c` of a closed graph lemma
`∀ k x, f(k, x) = 0 → R` with `R[lit d]` the closed `B`. -/
theorem prf_fin {f τ : PR} {d c : Nat} {k R B : VExpr} (hτ : Ok env T f 2 τ)
    (hR : R.inst (lit d) 1 = B) (hB : B.ClosedN)
    (hc : Thm env Γ (prf T (tmplH [] (allN 2 (imp ((valF f 2).inst zero 0) R)) 0) (numT c) =ₒ zero))
    (hk : Tm env Γ k) (h0 : Thm env Γ (ev f [k, lit d] =ₒ zero)) :
    Thm env Γ (prf T (numT (encExpr B))
      (ev (mpP (instC z s c [num d, var 0]) (.push (num d) (ren swap01 τ))) [k]) =ₒ zero) := by
  have hd : Tm env Γ (lit d) := litTy d
  have hv : Tm env Γ (ev f [k, lit d]) := evTy (.cons hk (.cons hd .nil))
  have p := hτ (Γ := Γ) (.cons hk (.cons hd .nil)) rfl
  unfold okF at p
  simp only [List.map_cons, List.map_nil] at p
  have E1 : Thm env Γ (tmplH [litT (ev f [k, lit d]), litT k, litT (lit d)] (valF f 2) 0 =ₒ
      tmplH [numT (encExpr zero), litT k, litT (lit d)] (valF f 2) 0) :=
    tmplH_congr1 (hs₁ := []) .nil (.cons (by otype) (.cons (by otype) .nil)) (by otype) (by otype)
      (Thm.trans (by otype) (by otype) (by otype) (litT_congr hv zeroTy h0) litT_zero) _ 0
  have e2 : tmplH [litT k, litT (lit d)] ((valF f 2).inst zero 0) 0 =
      tmplH [numT (encExpr zero), litT k, litT (lit d)] (valF f 2) 0 := by
    rw [← tmplH_zero [litT k, litT (lit d)]]
    exact tmplH_inst_insert [] [litT k, litT (lit d)] (e := zero) trivial _ 0
  have p2 := prf_congr (by otype) (by otype) (by otype) E1 p
  rw [← e2] at p2
  have h1 := prf_instC hA [num d, var 0] (Γ := Γ) (l := [k]) (.cons hk .nil) hc
  simp only [List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append, ev_var, ev_num, List.getD_cons_zero] at h1
  have h3 := hT.mpH (ys := [k, lit d]) (.cons hk (.cons hd .nil)) (by otype) (by otype) h1 p2
  simp only [List.map_cons, List.map_nil] at h3
  have E4 : Thm env Γ (tmplH [litT k, litT (lit d)] R 0 =ₒ tmplH [litT k, tmplH [] (lit d) 0] R 0) :=
    tmplH_congr1 (hs₁ := [litT k]) (.cons (by otype) .nil) .nil (by otype) (by otype)
      (Thm.trans (by otype) (by otype) (by otype) (litT_lit d)
        (Thm.symm (by otype) (by otype) (tmplH_nil (lit d) 0))) _ 0
  have h4 := prf_congr (by otype) (by otype) (by otype) E4 h3
  have e5 : tmplH [litT k] (R.inst (lit d) 1) 0 = tmplH [litT k, tmplH [] (lit d) 0] R 0 :=
    tmplH_inst_insert [litT k] [] (e := lit d) (lit_closed d) _ 0
  rw [← e5] at h4
  rw [hR, tmplH_closed [litT k] _ 0 hB] at h4
  have h5 := prf_congr (by otype) (by otype) (by otype) (tmplH_nil B 0) h4
  refine prf_congr_c (by otype) (by otype) (by otype) ?_ h5
  orw [ev_mpP (.cons hk .nil), ev_push (f := .push (num d) (ren swap01 τ)) rfl (.cons hk .nil),
    ev_ren_eq (f := τ) swap01 (.cons hd (.cons hk .nil)) (l' := [k, lit d]) (valS_swap01 _ _)]

/-- From `f` at `[k, lit d]` being `0`, a proof of `halts f d`. -/
theorem prf_halts {f τ : PR} {d c : Nat} {k : VExpr} (hτ : Ok env T f 2 τ)
    (hc : Thm env Γ (prf T
      (tmplH [] (allN 2 (imp ((valF f 2).inst zero 0) (haltsV f (.bvar 1)))) 0)
      (numT c) =ₒ zero))
    (hk : Tm env Γ k) (h0 : Thm env Γ (ev f [k, lit d] =ₒ zero)) :
    Thm env Γ (prf T (numT (encExpr (halts f d)))
      (ev (mpP (instC z s c [num d, var 0]) (.push (num d) (ren swap01 τ))) [k]) =ₒ zero) :=
  prf_fin hA hT hτ (by rw [← haltsV_lit]; simp only [haltsV, obj_simp]) (halts_closed f d) hc
    hk h0

end

/-- **Internal Σ₁-completeness for a machine reading proofs**, for a closed graph lemma
`∀ k x, f(k, x) = 0 → R` with `R[lit d]` the closed `B`: if `f` at `d` and `k` is `Prf(⌜A⌝, k)`,
then for some code `σ` the theory proves `∀ k, Prf(⌜A⌝, k) → Prf(⌜B⌝, σ k)`. -/
theorem sigma_of_fin {env : Typing} [E : ObjEnv env] {T : PR} (hT : IsChecker env T) {f : PR}
    {d : Nat} {A R B : VExpr} (hR : R.inst (lit d) 1 = B) (hB : B.ClosedN)
    (hG : Thm env [] (allN 2 (imp ((valF f 2).inst zero 0) R)))
    (hf : ∀ {Γ : List VExpr} {k : VExpr}, Tm env Γ k →
      Thm env Γ (app2 (fn f) (lit d) k =ₒ prf T (numT (encExpr A)) k)) :
    ∃ σ : PR, Thm env [] (∀ₒ k, prf T (numT (encExpr A)) k =ₒ zero →ₒ
      prf T (numT (encExpr B)) (ev σ [k]) =ₒ zero) := by
  obtain ⟨z, s, hA⟩ := hT.allH
  obtain ⟨τ, hτ⟩ := ok_exists hA hT f 2
  obtain ⟨c, hc⟩ := hT.closed_prf hG
  refine ⟨mpP (instC z s c [num d, var 0]) (.push (num d) (ren swap01 τ)), ?_⟩
  ointro
  ointro h
  have hk : Tm env [prf T (numT (encExpr A)) (.bvar 0) =ₒ zero, nat] (.bvar 1) := by otype
  have h0 : Thm env [prf T (numT (encExpr A)) (.bvar 0) =ₒ zero, nat]
      (ev f [.bvar 1, lit d] =ₒ zero) := by
    have e := hf hk
    orw [← fn_ev (litTy d) hk, e]
    exact h
  exact prf_fin hA hT hτ hR hB hc hk h0

/-- **Internal Σ₁-completeness for a machine reading proofs.** If `f` at `d` and `k` is
`Prf(⌜A⌝, k)`, then for some code `σ` the theory proves
`∀ k, Prf(⌜A⌝, k) → Prf(⌜halts f d⌝, σ k)`. -/
theorem sigma_of {env : Typing} [E : ObjEnv env] {T : PR} (hT : IsChecker env T) {f : PR}
    {d : Nat} {A : VExpr}
    (hf : ∀ {Γ : List VExpr} {k : VExpr}, Tm env Γ k →
      Thm env Γ (app2 (fn f) (lit d) k =ₒ prf T (numT (encExpr A)) k)) :
    ∃ σ : PR, Thm env [] (∀ₒ k, prf T (numT (encExpr A)) k =ₒ zero →ₒ
      prf T (numT (encExpr (halts f d))) (ev σ [k]) =ₒ zero) := by
  have hG : Thm env [] (allN 2 (imp ((valF f 2).inst zero 0) (haltsV f (.bvar 1)))) := by
    rw [valF_fin_eq]
    exact allN_intro (env := env) 2 (Γ := []) (gp_fin (bvar_rep (by omega)) (bvar_rep (by omega)))
  exact sigma_of_fin hT (by rw [← haltsV_lit]; simp only [haltsV, obj_simp]) (halts_closed f d) hG hf

end Incomplete.Obj

namespace Incomplete
open Lean4Lean Obj

section
variable {env : VEnv} {T : Tables}

/-- **Internal Σ₁-completeness for the diagonal machine**: the hypothesis of `second_of_sigma`. -/
theorem sigma_dg [ObjEnv env] (hT : TablesFor env T) :
    ∃ σ : PR, Thm env [] (∀ₒ k, prfT T (numT (encExpr (G0 T))) k =ₒ zero →ₒ
      prfT T (numT (encExpr (halts (dg T) (dg T).code))) (ev σ [k]) =ₒ zero) :=
  sigma_of (env := env) (IsChecker.full hT) (f := dg T) (d := (dg T).code) (A := G0 T) fun hk => fn_dg_code hk

/-- **`Con T → G0 T` inside the theory.** -/
theorem con_imp_G0_provable (hwf : env.WF) (hext : natEnv ≤ env) (hT : TablesFor env T) :
    Provable env (.forallE (Con T) (G0 T)) := by
  have : ObjEnv env := .full (hasNat_natEnv.mono hext) hwf.ordered
  obtain ⟨σ, hσ⟩ := sigma_dg hT
  have h := (con_imp_G0 hσ).provable
  have e : imp (Con T) (G0 T) = .forallE (Con T) (G0 T) := by
    show VExpr.forallE _ ((G0 T).liftN 1 0) = _
    rw [(G0_closed (env := env) T).liftN_eq (Nat.zero_le _)]
  rwa [e] at h

end

/-- **The second incompleteness theorem.** A consistent well-formed extension of `natEnv` does
not prove its consistency sentence `Con T`, for any tables `T` of the environment. -/
theorem con_unprovable (env : VEnv) (hwf : env.WF) (hext : natEnv ≤ env) {T : Tables}
    (hT : TablesFor env T) (hC : Consistent env) : ¬Provable env (Con T) := by
  have : ObjEnv env := .full (hasNat_natEnv.mono hext) hwf.ordered
  obtain ⟨σ, hσ⟩ := sigma_dg hT
  exact second_of_sigma hT hσ hC

/-- **The second incompleteness theorem**, with the consistency sentence: every consistent
well-formed extension of `natEnv` has tables `T` whose closed proposition `Con T` is true exactly
when the theory is consistent, and does not prove it. -/
theorem second_incompleteness (env : VEnv) (hwf : env.WF) (hext : natEnv ≤ env)
    (hC : Consistent env) :
    ∃ T, TablesFor env T ∧ env.HasType 0 [] (Con T) (.sort .zero) ∧
      (¬(conM T).Halts 0 ↔ Consistent env) ∧ ¬Provable env (Con T) := by
  obtain ⟨T, hT⟩ := hwf.checkable.tables
  exact ⟨T, hT, ConT (hasNat_natEnv.mono hext) hwf.ordered, con_true_iff hT,
    con_unprovable env hwf hext hT hC⟩

/-- `second_incompleteness` for any consistent environment built from well-formed declarations,
one of which is `Nat`. -/
theorem second_incompleteness' {ds : List VDecl} {env : VEnv} (H : env.WF' ds)
    (hm : .induct natDecl ∈ ds) (hC : Consistent env) :
    ∃ T, TablesFor env T ∧ env.HasType 0 [] (Con T) (.sort .zero) ∧
      (¬(conM T).Halts 0 ↔ Consistent env) ∧ ¬Provable env (Con T) :=
  second_incompleteness env ⟨ds, H⟩ (natEnv_le_of_mem H hm) hC

end Incomplete
