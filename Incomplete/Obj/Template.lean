import Incomplete.Obj.NumCert

/-!
# Instantiating the number of a fixed expression

For a fixed expression `B`, `tmplT h B j` is the number of `B` with its variable `j` replaced by
the number `h j` (`j` counting the binders passed), assembled from `numT` of `B`'s parts: variables below `j` are kept, those above
move down by one. Instantiating `numT ⌜B⌝` at the cutoff `lit j` is this template whenever the
value `a` lifted by `j` is `h j` (`instT_tmpl`), by induction on `B` through the step equations
of `instC`; for a numeral `a = litT v`, the hole is `litT v` itself (`instT_tmpl_lit`). A closed `B`
is left unchanged (`instT_closed`).

Internal modus ponens for fixed closed `A` and `B` follows: certificates of `A → B` and of `A`
give one of `B` (`certT_mp`, `jT_mp`).
-/

namespace Incomplete.Obj
open Lean4Lean
open VExpr Typing PR

/-- The number of `B` with the variable `j` replaced by the number `h j`, where `j` counts the
binders passed. -/
noncomputable def tmplT (h : Nat → VExpr) : VExpr → Nat → VExpr
  | .bvar i, j => if i < j then numT (encExpr (.bvar i)) else if i = j then h j
      else numT (encExpr (.bvar (i - 1)))
  | .sort u, _ => numT (encExpr (.sort u))
  | .const c ls, _ => numT (encExpr (.const c ls))
  | .app f a, j => tagT 7 3 (pair (tmplT h f j) (tmplT h a j))
  | .lam A b, j => tagT 7 4 (pair (tmplT h A j) (tmplT h b (j + 1)))
  | .forallE A b, j => tagT 7 5 (pair (tmplT h A j) (tmplT h b (j + 1)))
  | .proj s i e, j => tagT 7 6 (pair (numT (encName s)) (pair (numT i) (tmplT h e j)))

section
variable {env : Typing} [E : ObjEnv env] {Γ : List VExpr} {a : VExpr} {h : Nat → VExpr}

theorem tmplTTy (hh : ∀ j, Tm env Γ (h j)) : ∀ (B : VExpr) (j : Nat), Tm env Γ (tmplT h B j)
  | .bvar i, j => by
    simp only [tmplT]; split
    · otype
    · split
      · exact hh j
      · otype
  | .sort _, _ | .const _ _, _ => by simp only [tmplT]; otype
  | .app f b, j => by
    have := tmplTTy hh f j; have := tmplTTy hh b j; simp only [tmplT]; otype
  | .lam A b, j => by
    have := tmplTTy hh A j; have := tmplTTy hh b (j + 1); simp only [tmplT]; otype
  | .forallE A b, j => by
    have := tmplTTy hh A j; have := tmplTTy hh b (j + 1); simp only [tmplT]; otype
  | .proj _ _ e, j => by have := tmplTTy hh e j; simp only [tmplT]; otype

end

macro_rules | `(tactic| otype_rules) => `(tactic| ((with_reducible refine tmplTTy ?_ _ _); assumption))

section
variable {env : Typing} [E : ObjEnv env] {Γ : List VExpr} {a : VExpr} {h : Nat → VExpr}

theorem lit_eq_succ (j : Nat) : lit (j + 1) = S (lit j) := rfl

/-- **The template lemma.** Instantiating the number of `B` at `a` and the cutoff `lit j` gives
the template whose hole under `j` binders is `h j`, when that is `a` lifted by `j`. -/
theorem instT_tmpl (ha : Tm env Γ a) (hh : ∀ j, Tm env Γ (h j))
    (hl : ∀ j : Nat, Thm env Γ (liftT (lit j) a zero =ₒ h j)) :
    ∀ (B : VExpr) (j : Nat), Thm env Γ (instT (numT (encExpr B)) a (lit j) =ₒ tmplT h B j)
  | .bvar i, j => by
    simp only [tmplT]
    rcases Nat.lt_trichotomy i j with hij | rfl | hij
    · rw [ite_eq_left hij]
      orw [numT_bvar, numT_lit]
      orw [instT_bvar_lt (by otype) ha (by otype) (lit_lt hij), ← numT_lit i, ← numT_bvar i]
    · rw [ite_eq_right (Nat.lt_irrefl _), ite_eq_left rfl]
      have := hh i
      orw [numT_bvar, numT_lit, instT_bvar_eq ha (by otype), hl]
    · rw [ite_eq_right (by omega), ite_eq_right (by omega)]
      orw [numT_bvar, numT_lit, instT_bvar_gt (by otype) ha (by otype) (lit_lt hij), sub_lit,
        ← numT_lit (i - 1), ← numT_bvar (i - 1)]
  | .sort u, j => by
    simp only [tmplT]
    orw [numT_sort, instT_sort (by otype) ha (by otype)]
  | .const c ls, j => by
    simp only [tmplT]
    exact instT_const_numT c ls ha (by otype)
  | .app f b, j => by
    simp only [tmplT]
    orw [numT_app, instT_app (by otype) (by otype) ha (by otype), instT_tmpl ha hh hl f j,
      instT_tmpl ha hh hl b j]
  | .lam A b, j => by
    have ihb := instT_tmpl ha hh hl b (j + 1)
    rw [lit_eq_succ] at ihb
    simp only [tmplT]
    orw [numT_lam, instT_lam (by otype) (by otype) ha (by otype), instT_tmpl ha hh hl A j, ihb]
  | .forallE A b, j => by
    have ihb := instT_tmpl ha hh hl b (j + 1)
    rw [lit_eq_succ] at ihb
    simp only [tmplT]
    orw [numT_forallE, instT_forallE (by otype) (by otype) ha (by otype), instT_tmpl ha hh hl A j,
      ihb]
  | .proj s i e, j => by
    simp only [tmplT]
    orw [numT_proj, instT_proj (by otype) (by otype) (by otype) ha (by otype), instT_tmpl ha hh hl e j]

/-- At a numeral the hole is the numeral's number: `instT ⌜B⌝ (litT v) j` is the number of
`B[lit v]`, with `lit v` at the variable `j`. -/
theorem instT_tmpl_lit {v : VExpr} (hv : Tm env Γ v) (B : VExpr) (j : Nat) :
    Thm env Γ (instT (numT (encExpr B)) (litT v) (lit j) =ₒ tmplT (fun _ => litT v) B j) :=
  instT_tmpl (by otype) (fun _ => by otype) (fun _ => liftT_litT (by otype) zeroTy hv) B j

/-- A template without a hole is the number of its expression. -/
theorem tmplT_closed (hh : ∀ j, Tm env Γ (h j)) : ∀ (B : VExpr) (j : Nat), B.ClosedN j →
    Thm env Γ (tmplT h B j =ₒ numT (encExpr B))
  | .bvar i, j, hc => by
    have hc : i < j := hc
    simp only [tmplT, ite_eq_left hc]; orefl
  | .sort u, j, _ => by simp only [tmplT]; orefl
  | .const c ls, j, _ => by simp only [tmplT]; orefl
  | .app f b, j, hc => by
    simp only [tmplT]
    orw [numT_app, tmplT_closed hh f j hc.1, tmplT_closed hh b j hc.2]
  | .lam A b, j, hc => by
    simp only [tmplT]
    orw [numT_lam, tmplT_closed hh A j hc.1, tmplT_closed hh b (j + 1) hc.2]
  | .forallE A b, j, hc => by
    simp only [tmplT]
    orw [numT_forallE, tmplT_closed hh A j hc.1, tmplT_closed hh b (j + 1) hc.2]
  | .proj s i e, j, hc => by
    simp only [tmplT]
    orw [numT_proj, tmplT_closed hh e j hc]

/-- A closed expression's number is left unchanged by instantiation. -/
theorem instT_closed {B : VExpr} (hB : B.ClosedN) (ha : Tm env Γ a) :
    Thm env Γ (instT (numT (encExpr B)) a zero =ₒ numT (encExpr B)) := by
  have hh : ∀ j, Tm env Γ ((fun j => liftT (lit j) a zero) j) := fun _ => by otype
  have h := instT_tmpl ha hh (fun _ => Thm.refl (by otype)) B 0
  simp only [lit_zero] at h
  orw [h, tmplT_closed hh B 0 hB]

theorem numT_imp {A B : VExpr} (hB : B.ClosedN) :
    Thm env Γ (numT (encExpr (imp A B)) =ₒ tagT 7 5 (pair (numT (encExpr A)) (numT (encExpr B)))) := by
  have e : imp A B = .forallE A B := by
    show VExpr.forallE A (B.liftN 1 0) = _; rw [hB.liftN_eq (Nat.zero_le _)]
  rw [e]; exact numT_forallE A B

end

/-- The certificate of `⊢ p q : B` from `c₁ : ⊢ p : A → B` and `c₂ : ⊢ q : A`. -/
noncomputable def mpT (A B p q c₁ c₂ : VExpr) : VExpr :=
  appT zero (numT (encExpr A)) (numT (encExpr B)) p p q q c₁ c₂

@[obj_simp] theorem mpT_liftN {A B p q c₁ c₂ : VExpr} {n k : Nat} :
    (mpT A B p q c₁ c₂).liftN n k = mpT A B (p.liftN n k) (q.liftN n k) (c₁.liftN n k) (c₂.liftN n k) := by
  simp only [mpT, obj_simp]

@[obj_simp] theorem mpT_inst {A B p q c₁ c₂ e : VExpr} {k : Nat} :
    (mpT A B p q c₁ c₂).inst e k = mpT A B (p.inst e k) (q.inst e k) (c₁.inst e k) (c₂.inst e k) := by
  simp only [mpT, obj_simp]

section
variable {env : Typing} [E : ObjEnv env] {Γ : List VExpr} {A B p q c₁ c₂ : VExpr} {T : Tables}
  {R : Nat → Bool}

theorem mpTTy (hp : Tm env Γ p) (hq : Tm env Γ q) (hc₁ : Tm env Γ c₁) (hc₂ : Tm env Γ c₂) :
    Tm env Γ (mpT A B p q c₁ c₂) := by
  unfold mpT; otype

end

macro_rules | `(tactic| otype_rules) => `(tactic| ((with_reducible refine mpTTy ?_ ?_ ?_ ?_) <;> otype))

section
variable {env : Typing} [E : ObjEnv env] {Γ : List VExpr} {A B p q c₁ c₂ : VExpr} {T : Tables}
  {R : Nat → Bool}

/-- **Internal modus ponens**, for fixed `A` and closed `B`: certificates of `⊢ p : A → B` and of
`⊢ q : A` that check give one of `⊢ p q : B` that checks. -/
theorem certT_mp (hR : R 5 = true) (hB : B.ClosedN) (hp : Tm env Γ p) (hq : Tm env Γ q)
    (hc₁ : Tm env Γ c₁) (hc₂ : Tm env Γ c₂) (h₁ : Thm env Γ (certT T R c₁ =ₒ zero))
    (j₁ : Thm env Γ (jT c₁ =ₒ judgT zero p p (numT (encExpr (imp A B)))))
    (h₂ : Thm env Γ (certT T R c₂ =ₒ zero))
    (j₂ : Thm env Γ (jT c₂ =ₒ judgT zero q q (numT (encExpr A)))) :
    Thm env Γ (certT T R (mpT A B p q c₁ c₂) =ₒ zero) := by
  have j₁' : Thm env Γ (jT c₁ =ₒ judgT zero p p
      (tagT 7 5 (pair (numT (encExpr A)) (numT (encExpr B))))) := by
    orw [j₁, numT_imp hB]
  exact certT_appT zeroTy (by otype) (by otype) hp hp hq hq hc₁ hc₂ hR h₁ h₂ j₁' j₂

/-- The judgment of the modus ponens certificate. -/
theorem jT_mp (hB : B.ClosedN) (hp : Tm env Γ p) (hq : Tm env Γ q) (hc₁ : Tm env Γ c₁)
    (hc₂ : Tm env Γ c₂) : Thm env Γ (jT (mpT A B p q c₁ c₂) =ₒ
      judgT zero (tagT 7 3 (pair p q)) (tagT 7 3 (pair p q)) (numT (encExpr B))) := by
  unfold mpT
  orw [jT_appT zeroTy (by otype) (by otype) hp hp hq hq hc₁ hc₂, instT_closed hB hq]

end

/-- **Internal instantiation**, with the sentence as the number of `Q[lit k]`: for a closed
provable `∀ x : Nat, Q` there is a code `σ` with, internally, `∀ k, Prf(⌜Q[lit k]⌝, σ k)`. -/
theorem internal_inst_tmpl {envT : VEnv} {T : Tables} (hT : TablesFor envT T) (H : HasNat envT)
    {Q : VExpr} (hQ : Provable envT (all Q)) :
    ∃ σ : PR, ∀ {env : Typing} [ObjEnv env],
      Thm env [] (all (prfT T (tmplT (fun _ => litT (.bvar 0)) Q 0) (ev σ [.bvar 0]) =ₒ zero)) := by
  obtain ⟨σ, hσ⟩ := internal_inst hT H hQ
  refine ⟨σ, fun {env} _ => Thm.allI ?_⟩
  have hk := Thm.allE ((hσ (env := env)).weak0 (Γ := [nat])) (t := .bvar 0) (.bvar .zero)
  simp only [obj_simp] at hk
  have e := instT_tmpl_lit (env := env) (Γ := [nat]) (v := .bvar 0) (.bvar .zero) Q 0
  simp only [lit_zero] at e
  have : ∀ j : Nat, Tm env [nat] ((fun _ : Nat => litT (.bvar 0)) j) := fun _ => by otype
  orw [e] at hk
  exact hk

end Incomplete.Obj
