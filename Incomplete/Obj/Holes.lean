import Incomplete.Obj.Template

/-!
# Templates with several holes

For a fixed expression `B`, `tmplH hs B j` is the number of `B` with its free variables
`j, j+1, …` (at depth `j`) replaced by the numbers `hs`, and those past the holes moved down by
`hs.length`, assembled from `numT` of `B`'s parts. Lifting `B` past a hole erases it
(`tmplH_liftN_erase`) and instantiating `B` at an expression inserts that expression's template as
a hole (`tmplH_inst_insert`), both on the nose. Internally, instantiating a template whose holes
are inert at a numeral adds the numeral as a hole (`instT_tmplH_num`), and at any number leaves a
template of a lifted expression (`instT_tmplH_lift`).
-/

namespace Incomplete.Obj
open Lean4Lean
open VExpr VEnv PR

/-- The number of `B` with the variable `j + m` replaced by the number `hs[m]`, at depth `j`. -/
noncomputable def tmplH (hs : List VExpr) : VExpr → Nat → VExpr
  | .bvar i, j => if i < j then numT (encExpr (.bvar i)) else if i - j < hs.length then
      hs.getD (i - j) zero else numT (encExpr (.bvar (i - hs.length)))
  | .sort u, _ => numT (encExpr (.sort u))
  | .const c ls, _ => numT (encExpr (.const c ls))
  | .app f a, j => tagT 7 3 (pair (tmplH hs f j) (tmplH hs a j))
  | .lam A b, j => tagT 7 4 (pair (tmplH hs A j) (tmplH hs b (j + 1)))
  | .forallE A b, j => tagT 7 5 (pair (tmplH hs A j) (tmplH hs b (j + 1)))
  | .proj s i e, j => tagT 7 6 (pair (numT (encName s)) (pair (numT i) (tmplH hs e j)))

section
variable {n k : Nat} {e : VExpr}

@[obj_simp] theorem numT_liftN (m : Nat) : (numT m).liftN n k = numT m := by
  simp only [numT, ev_liftN, List.map_nil]
@[obj_simp] theorem numT_inst (m : Nat) : (numT m).inst e k = numT m := by
  simp only [numT, ev_inst, List.map_nil]

@[obj_simp] theorem tmplH_liftN (hs : List VExpr) :
    ∀ (B : VExpr) (j : Nat), (tmplH hs B j).liftN n k = tmplH (hs.map (·.liftN n k)) B j
  | .bvar i, j => by
    simp only [tmplH, List.length_map]
    split
    · simp only [obj_simp]
    · split
      · rw [getD_map (g := (·.liftN n k)) rfl]
      · simp only [obj_simp]
  | .sort _, _ | .const _ _, _ => by simp only [tmplH, obj_simp]
  | .app f a, j => by simp only [tmplH, obj_simp, tmplH_liftN hs f, tmplH_liftN hs a]
  | .lam A b, j => by simp only [tmplH, obj_simp, tmplH_liftN hs A, tmplH_liftN hs b]
  | .forallE A b, j => by simp only [tmplH, obj_simp, tmplH_liftN hs A, tmplH_liftN hs b]
  | .proj _ _ b, j => by simp only [tmplH, obj_simp, tmplH_liftN hs b]

@[obj_simp] theorem tmplH_inst (hs : List VExpr) :
    ∀ (B : VExpr) (j : Nat), (tmplH hs B j).inst e k = tmplH (hs.map (·.inst e k)) B j
  | .bvar i, j => by
    simp only [tmplH, List.length_map]
    split
    · simp only [obj_simp]
    · split
      · rw [getD_map (g := (·.inst e k)) rfl]
      · simp only [obj_simp]
  | .sort _, _ | .const _ _, _ => by simp only [tmplH, obj_simp]
  | .app f a, j => by simp only [tmplH, obj_simp, tmplH_inst hs f, tmplH_inst hs a]
  | .lam A b, j => by simp only [tmplH, obj_simp, tmplH_inst hs A, tmplH_inst hs b]
  | .forallE A b, j => by simp only [tmplH, obj_simp, tmplH_inst hs A, tmplH_inst hs b]
  | .proj _ _ b, j => by simp only [tmplH, obj_simp, tmplH_inst hs b]

end

section
variable {env : VEnv} [E : ObjEnv env] {Γ : List VExpr} {hs : List VExpr}

theorem tmplHTy (hh : Tms env Γ hs) : ∀ (B : VExpr) (j : Nat), Tm env Γ (tmplH hs B j)
  | .bvar i, j => by
    simp only [tmplH]; split
    · otype
    · split
      · exact hh.get (i - j)
      · otype
  | .sort _, _ | .const _ _, _ => by simp only [tmplH]; otype
  | .app f b, j => by
    have := tmplHTy hh f j; have := tmplHTy hh b j; simp only [tmplH]; otype
  | .lam A b, j => by
    have := tmplHTy hh A j; have := tmplHTy hh b (j + 1); simp only [tmplH]; otype
  | .forallE A b, j => by
    have := tmplHTy hh A j; have := tmplHTy hh b (j + 1); simp only [tmplH]; otype
  | .proj _ _ e, j => by have := tmplHTy hh e j; simp only [tmplH]; otype

end

macro_rules | `(tactic| otype_rules) => `(tactic| ((with_reducible refine tmplHTy ?_ _ _); otype))

/-! ### Templates as expressions -/

theorem getD_app_lt {l₁ l₂ : List VExpr} {i : Nat} (h : i < l₁.length) :
    (l₁ ++ l₂).getD i zero = l₁.getD i zero := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_app_ge {l₁ l₂ : List VExpr} {i : Nat} (h : l₁.length ≤ i) :
    (l₁ ++ l₂).getD i zero = l₂.getD (i - l₁.length) zero := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

/-- A template of an expression closed at its depth has no holes. -/
theorem tmplH_closed (hs : List VExpr) : ∀ (B : VExpr) (j : Nat), B.ClosedN j →
    tmplH hs B j = tmplH [] B j
  | .bvar i, j, hc => by
    have hc : i < j := hc
    simp only [tmplH, if_pos hc]
  | .sort _, _, _ | .const _ _, _, _ => rfl
  | .app f a, j, hc => by simp only [tmplH, tmplH_closed hs f j hc.1, tmplH_closed hs a j hc.2]
  | .lam A b, j, hc => by
    simp only [tmplH, tmplH_closed hs A j hc.1, tmplH_closed hs b (j + 1) hc.2]
  | .forallE A b, j, hc => by
    simp only [tmplH, tmplH_closed hs A j hc.1, tmplH_closed hs b (j + 1) hc.2]
  | .proj _ _ b, j, hc => by simp only [tmplH, tmplH_closed hs b j hc]

/-- **Lifting erases a hole.** -/
theorem tmplH_liftN_erase (hs₁ hs₂ : List VExpr) (y : VExpr) : ∀ (B : VExpr) (j : Nat),
    tmplH (hs₁ ++ y :: hs₂) (B.liftN 1 (j + hs₁.length)) j = tmplH (hs₁ ++ hs₂) B j
  | .bvar i, j => by
    simp only [VExpr.liftN]
    rcases Nat.lt_or_ge i (j + hs₁.length) with h1 | h1
    · rw [liftVar_lt h1]
      simp only [tmplH, List.length_append, List.length_cons]
      rcases Nat.lt_or_ge i j with h | h
      · simp only [if_pos h]
      · simp only [if_neg (show ¬ i < j by omega),
          if_pos (show i - j < hs₁.length + (hs₂.length + 1) by omega),
          if_pos (show i - j < hs₁.length + hs₂.length by omega),
          getD_app_lt (show i - j < hs₁.length by omega)]
    · rw [liftVar_le h1]
      simp only [tmplH, List.length_append, List.length_cons]
      simp only [if_neg (show ¬ 1 + i < j by omega), if_neg (show ¬ i < j by omega)]
      by_cases h2 : i - j < hs₁.length + hs₂.length
      · simp only [if_pos (show 1 + i - j < hs₁.length + (hs₂.length + 1) by omega), if_pos h2,
          getD_app_ge (show hs₁.length ≤ 1 + i - j by omega),
          getD_app_ge (show hs₁.length ≤ i - j by omega),
          show 1 + i - j - hs₁.length = (i - j - hs₁.length) + 1 by omega, List.getD_cons_succ]
      · simp only [if_neg (show ¬ 1 + i - j < hs₁.length + (hs₂.length + 1) by omega), if_neg h2,
          show 1 + i - (hs₁.length + (hs₂.length + 1)) = i - (hs₁.length + hs₂.length) by omega]
  | .sort _, _ | .const _ _, _ => rfl
  | .app f a, j => by
    simp only [VExpr.liftN, tmplH, tmplH_liftN_erase hs₁ hs₂ y f, tmplH_liftN_erase hs₁ hs₂ y a]
  | .lam A b, j => by
    have ih := tmplH_liftN_erase hs₁ hs₂ y b (j + 1)
    rw [Nat.add_right_comm] at ih
    simp only [VExpr.liftN, tmplH, tmplH_liftN_erase hs₁ hs₂ y A, ih]
  | .forallE A b, j => by
    have ih := tmplH_liftN_erase hs₁ hs₂ y b (j + 1)
    rw [Nat.add_right_comm] at ih
    simp only [VExpr.liftN, tmplH, tmplH_liftN_erase hs₁ hs₂ y A, ih]
  | .proj _ _ b, j => by simp only [VExpr.liftN, tmplH, tmplH_liftN_erase hs₁ hs₂ y b]

/-- A template of a lifted expression whose variables are all holes. -/
theorem tmplH_liftN_holes (hs₁ hs₂ : List VExpr) (j : Nat) : ∀ (e : VExpr) (d : Nat),
    e.ClosedN (hs₂.length + d) →
    tmplH (hs₁ ++ hs₂) (e.liftN (j + hs₁.length) d) (j + d) = tmplH hs₂ e d
  | .bvar i, d, hc => by
    have hc : i < hs₂.length + d := hc
    simp only [VExpr.liftN]
    rcases Nat.lt_or_ge i d with h | h
    · rw [liftVar_lt h]
      simp only [tmplH, if_pos h, if_pos (by omega : i < j + d)]
    · rw [liftVar_le h]
      simp only [tmplH, List.length_append]
      simp only [if_neg (show ¬ j + hs₁.length + i < j + d by omega), if_neg (show ¬ i < d by omega),
        if_pos (show j + hs₁.length + i - (j + d) < hs₁.length + hs₂.length by omega),
        if_pos (show i - d < hs₂.length by omega),
        getD_app_ge (show hs₁.length ≤ j + hs₁.length + i - (j + d) by omega),
        show j + hs₁.length + i - (j + d) - hs₁.length = i - d by omega]
  | .sort _, _, _ | .const _ _, _, _ => rfl
  | .app f a, d, hc => by
    simp only [VExpr.liftN, tmplH, tmplH_liftN_holes hs₁ hs₂ j f d hc.1,
      tmplH_liftN_holes hs₁ hs₂ j a d hc.2]
  | .lam A b, d, hc => by
    have ih := tmplH_liftN_holes hs₁ hs₂ j b (d + 1) hc.2
    simp only [VExpr.liftN, tmplH, tmplH_liftN_holes hs₁ hs₂ j A d hc.1]
    rw [show j + d + 1 = j + (d + 1) by omega, ih]
  | .forallE A b, d, hc => by
    have ih := tmplH_liftN_holes hs₁ hs₂ j b (d + 1) hc.2
    simp only [VExpr.liftN, tmplH, tmplH_liftN_holes hs₁ hs₂ j A d hc.1]
    rw [show j + d + 1 = j + (d + 1) by omega, ih]
  | .proj _ _ b, d, hc => by simp only [VExpr.liftN, tmplH, tmplH_liftN_holes hs₁ hs₂ j b d hc]

/-- **Instantiating inserts a hole**: the template of the expression put in. -/
theorem tmplH_inst_insert (hs₁ hs₂ : List VExpr) {e : VExpr} (he : e.ClosedN hs₂.length) :
    ∀ (B : VExpr) (j : Nat), tmplH (hs₁ ++ hs₂) (B.inst e (j + hs₁.length)) j =
      tmplH (hs₁ ++ tmplH hs₂ e 0 :: hs₂) B j
  | .bvar i, j => by
    simp only [VExpr.inst, instVar]
    rcases Nat.lt_or_ge i (j + hs₁.length) with h1 | h1
    · rw [if_pos h1]
      simp only [tmplH, List.length_append, List.length_cons]
      rcases Nat.lt_or_ge i j with h | h
      · simp only [if_pos h]
      · simp only [if_neg (show ¬ i < j by omega),
          if_pos (show i - j < hs₁.length + (hs₂.length + 1) by omega),
          if_pos (show i - j < hs₁.length + hs₂.length by omega),
          getD_app_lt (show i - j < hs₁.length by omega)]
    · rw [if_neg (show ¬ i < j + hs₁.length by omega)]
      by_cases h2 : i = j + hs₁.length
      · rw [if_pos h2]
        have := tmplH_liftN_holes hs₁ hs₂ j e 0 (by simpa using he)
        simp only [Nat.add_zero] at this
        rw [this]
        simp only [tmplH, List.length_append, List.length_cons]
        simp only [if_neg (show ¬ i < j by omega),
          if_pos (show i - j < hs₁.length + (hs₂.length + 1) by omega),
          getD_app_ge (show hs₁.length ≤ i - j by omega),
          show i - j - hs₁.length = 0 by omega, List.getD_cons_zero]
      · rw [if_neg h2]
        simp only [tmplH, List.length_append, List.length_cons]
        simp only [if_neg (show ¬ i - 1 < j by omega), if_neg (show ¬ i < j by omega)]
        by_cases h3 : i - 1 - j < hs₁.length + hs₂.length
        · simp only [if_pos h3, if_pos (show i - j < hs₁.length + (hs₂.length + 1) by omega),
            getD_app_ge (show hs₁.length ≤ i - 1 - j by omega),
            getD_app_ge (show hs₁.length ≤ i - j by omega),
            show i - j - hs₁.length = (i - 1 - j - hs₁.length) + 1 by omega, List.getD_cons_succ]
        · simp only [if_neg h3, if_neg (show ¬ i - j < hs₁.length + (hs₂.length + 1) by omega),
            show i - 1 - (hs₁.length + hs₂.length) = i - (hs₁.length + (hs₂.length + 1)) by omega]
  | .sort _, _ | .const _ _, _ => rfl
  | .app f a, j => by
    simp only [VExpr.inst, tmplH, tmplH_inst_insert hs₁ hs₂ he f, tmplH_inst_insert hs₁ hs₂ he a]
  | .lam A b, j => by
    have ih := tmplH_inst_insert hs₁ hs₂ he b (j + 1)
    rw [Nat.add_right_comm] at ih
    simp only [VExpr.inst, tmplH, tmplH_inst_insert hs₁ hs₂ he A, ih]
  | .forallE A b, j => by
    have ih := tmplH_inst_insert hs₁ hs₂ he b (j + 1)
    rw [Nat.add_right_comm] at ih
    simp only [VExpr.inst, tmplH, tmplH_inst_insert hs₁ hs₂ he A, ih]
  | .proj _ _ b, j => by simp only [VExpr.inst, tmplH, tmplH_inst_insert hs₁ hs₂ he b]

/-! ### Templates internally -/

section
variable {env : VEnv} [E : ObjEnv env] {Γ : List VExpr} {hs : List VExpr} {a : VExpr}

theorem getD_mem {l : List VExpr} {i : Nat} (h : i < l.length) : l.getD i zero ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]
  exact List.getElem_mem h

/-- A template without holes is the number of its expression. -/
theorem tmplH_nil : ∀ (B : VExpr) (j : Nat), Thm env Γ (tmplH [] B j =ₒ numT (encExpr B))
  | .bvar i, j => by
    simp only [tmplH, List.length_nil, Nat.not_lt_zero, if_false, Nat.sub_zero]
    split <;> orefl
  | .sort _, _ | .const _ _, _ => by simp only [tmplH]; orefl
  | .app f b, j => by simp only [tmplH]; orw [numT_app, tmplH_nil f j, tmplH_nil b j]
  | .lam A b, j => by simp only [tmplH]; orw [numT_lam, tmplH_nil A j, tmplH_nil b (j + 1)]
  | .forallE A b, j => by
    simp only [tmplH]; orw [numT_forallE, tmplH_nil A j, tmplH_nil b (j + 1)]
  | .proj _ _ e, j => by simp only [tmplH]; orw [numT_proj, tmplH_nil e j]

/-- A closed expression's template is its number. -/
theorem tmplH_closed_numT {B : VExpr} {j : Nat} (hB : B.ClosedN j) :
    Thm env Γ (tmplH hs B j =ₒ numT (encExpr B)) := by
  rw [tmplH_closed hs B j hB]; exact tmplH_nil B j

theorem tmplH_congr {hs' : List VExpr} (hh : Tms env Γ hs) (hh' : Tms env Γ hs')
    (hlen : hs.length = hs'.length) (h : ∀ i, Thm env Γ (hs.getD i zero =ₒ hs'.getD i zero)) :
    ∀ (B : VExpr) (j : Nat), Thm env Γ (tmplH hs B j =ₒ tmplH hs' B j)
  | .bvar i, j => by
    simp only [tmplH, hlen]
    split
    · orefl
    · split
      · exact h _
      · orefl
  | .sort _, _ | .const _ _, _ => by simp only [tmplH]; orefl
  | .app f b, j => by
    simp only [tmplH]; orw [tmplH_congr hh hh' hlen h f j, tmplH_congr hh hh' hlen h b j]
  | .lam A b, j => by
    simp only [tmplH]; orw [tmplH_congr hh hh' hlen h A j, tmplH_congr hh hh' hlen h b (j + 1)]
  | .forallE A b, j => by
    simp only [tmplH]; orw [tmplH_congr hh hh' hlen h A j, tmplH_congr hh hh' hlen h b (j + 1)]
  | .proj _ _ e, j => by simp only [tmplH]; orw [tmplH_congr hh hh' hlen h e j]

/-- Replacing one hole by an equal number. -/
theorem tmplH_congr1 {hs₁ hs₂ : List VExpr} {b : VExpr} (h₁ : Tms env Γ hs₁) (h₂ : Tms env Γ hs₂)
    (ha : Tm env Γ a) (hb : Tm env Γ b) (h : Thm env Γ (a =ₒ b)) (B : VExpr) (j : Nat) :
    Thm env Γ (tmplH (hs₁ ++ a :: hs₂) B j =ₒ tmplH (hs₁ ++ b :: hs₂) B j) := by
  have t : ∀ {x}, Tm env Γ x → Tms env Γ (hs₁ ++ x :: hs₂) := fun hx => by
    clear h; induction h₁ with
    | nil => exact .cons hx h₂
    | cons hy _ ih => exact .cons hy ih
  refine tmplH_congr (t ha) (t hb) (by simp) (fun i => ?_) B j
  rcases Nat.lt_trichotomy i hs₁.length with hi | rfl | hi
  · rw [getD_app_lt hi, getD_app_lt hi]; exact Thm.refl ((h₁.get i))
  · rw [getD_app_ge (Nat.le_refl _), getD_app_ge (Nat.le_refl _), Nat.sub_self]; exact h
  · rw [getD_app_ge (Nat.le_of_lt hi), getD_app_ge (Nat.le_of_lt hi),
      show i - hs₁.length = (i - hs₁.length - 1) + 1 by omega]
    exact Thm.refl (h₂.get _)

/-- **Instantiating the template of a lifted expression** leaves the template of the expression,
when the holes are inert. -/
theorem instT_tmplH_lift (hh : Tms env Γ hs)
    (hin : ∀ x ∈ hs, ∀ k : Nat, Thm env Γ (instT x a (lit k) =ₒ x)) (ha : Tm env Γ a) :
    ∀ (B : VExpr) (j : Nat), Thm env Γ (instT (tmplH hs (B.liftN 1 j) (j + 1)) a (lit j) =ₒ
      tmplH hs B j)
  | .bvar i, j => by
    simp only [VExpr.liftN]
    rcases Nat.lt_or_ge i j with h | h
    · rw [liftVar_lt h]
      simp only [tmplH, if_pos h, if_pos (show i < j + 1 by omega)]
      orw [numT_bvar, numT_lit]
      orw [instT_bvar_lt (by otype) ha (by otype) (lit_lt h), ← numT_lit i, ← numT_bvar i]
    · rw [liftVar_le h]
      simp only [tmplH, if_neg (show ¬ 1 + i < j + 1 by omega), if_neg (show ¬ i < j by omega),
        show 1 + i - (j + 1) = i - j by omega]
      by_cases h2 : i - j < hs.length
      · simp only [if_pos h2]
        exact hin _ (getD_mem h2) j
      · simp only [if_neg h2]
        orw [numT_bvar, numT_lit,
          instT_bvar_gt (by otype) ha (by otype) (lit_lt (show j < 1 + i - hs.length by omega)),
          sub_lit]
        rw [show 1 + i - hs.length - 1 = i - hs.length by omega]
        orw [← numT_lit (i - hs.length), ← numT_bvar (i - hs.length)]
  | .sort u, j => by
    simp only [VExpr.liftN, tmplH]
    orw [numT_sort, instT_sort (by otype) ha (by otype)]
  | .const c ls, j => by
    simp only [VExpr.liftN, tmplH]
    exact instT_const_numT c ls ha (by otype)
  | .app f b, j => by
    simp only [VExpr.liftN, tmplH]
    orw [instT_app (by otype) (by otype) ha (by otype), instT_tmplH_lift hh hin ha f j,
      instT_tmplH_lift hh hin ha b j]
  | .lam A b, j => by
    have ihb := instT_tmplH_lift hh hin ha b (j + 1)
    rw [lit_eq_succ] at ihb
    simp only [VExpr.liftN, tmplH]
    orw [instT_lam (by otype) (by otype) ha (by otype), instT_tmplH_lift hh hin ha A j, ihb]
  | .forallE A b, j => by
    have ihb := instT_tmplH_lift hh hin ha b (j + 1)
    rw [lit_eq_succ] at ihb
    simp only [VExpr.liftN, tmplH]
    orw [instT_forallE (by otype) (by otype) ha (by otype), instT_tmplH_lift hh hin ha A j, ihb]
  | .proj s i e, j => by
    simp only [VExpr.liftN, tmplH]
    orw [instT_proj (by otype) (by otype) (by otype) ha (by otype), instT_tmplH_lift hh hin ha e j]

/-- **Instantiating a template at a numeral** adds the numeral as a hole, when the holes are
inert. -/
theorem instT_tmplH_num (hh : Tms env Γ hs)
    (hin : ∀ x ∈ hs, ∀ k : Nat, Thm env Γ (instT x a (lit k) =ₒ x)) (ha : Tm env Γ a)
    (hl : ∀ k : Nat, Thm env Γ (liftT (lit k) a zero =ₒ a)) :
    ∀ (B : VExpr) (j : Nat), Thm env Γ (instT (tmplH hs B (j + 1)) a (lit j) =ₒ
      tmplH (a :: hs) B j)
  | .bvar i, j => by
    simp only [tmplH, List.length_cons]
    rcases Nat.lt_trichotomy i j with h | rfl | h
    · simp only [if_pos h, if_pos (show i < j + 1 by omega)]
      orw [numT_bvar, numT_lit]
      orw [instT_bvar_lt (by otype) ha (by otype) (lit_lt h), ← numT_lit i, ← numT_bvar i]
    · simp only [if_pos (show i < i + 1 by omega), Nat.lt_irrefl, if_false, Nat.sub_self,
        if_pos (show 0 < hs.length + 1 by omega), List.getD_cons_zero]
      orw [numT_bvar, numT_lit, instT_bvar_eq ha (by otype), hl]
    · simp only [if_neg (show ¬ i < j + 1 by omega), if_neg (show ¬ i < j by omega)]
      by_cases h2 : i - (j + 1) < hs.length
      · simp only [if_pos h2, show i - j = (i - (j + 1)) + 1 by omega,
          if_pos (show i - (j + 1) + 1 < hs.length + 1 by omega), List.getD_cons_succ]
        exact hin _ (getD_mem h2) j
      · simp only [if_neg h2, if_neg (show ¬ i - j < hs.length + 1 by omega)]
        orw [numT_bvar, numT_lit,
          instT_bvar_gt (by otype) ha (by otype) (lit_lt (show j < i - hs.length by omega)),
          sub_lit]
        rw [show i - hs.length - 1 = i - (hs.length + 1) by omega]
        orw [← numT_lit (i - (hs.length + 1)), ← numT_bvar (i - (hs.length + 1))]
  | .sort u, j => by
    simp only [tmplH]
    orw [numT_sort, instT_sort (by otype) ha (by otype)]
  | .const c ls, j => by
    simp only [tmplH]
    exact instT_const_numT c ls ha (by otype)
  | .app f b, j => by
    simp only [tmplH]
    orw [instT_app (by otype) (by otype) ha (by otype), instT_tmplH_num hh hin ha hl f j,
      instT_tmplH_num hh hin ha hl b j]
  | .lam A b, j => by
    have ihb := instT_tmplH_num hh hin ha hl b (j + 1)
    rw [lit_eq_succ] at ihb
    simp only [tmplH]
    orw [instT_lam (by otype) (by otype) ha (by otype), instT_tmplH_num hh hin ha hl A j, ihb]
  | .forallE A b, j => by
    have ihb := instT_tmplH_num hh hin ha hl b (j + 1)
    rw [lit_eq_succ] at ihb
    simp only [tmplH]
    orw [instT_forallE (by otype) (by otype) ha (by otype), instT_tmplH_num hh hin ha hl A j, ihb]
  | .proj s i e, j => by
    simp only [tmplH]
    orw [instT_proj (by otype) (by otype) (by otype) ha (by otype), instT_tmplH_num hh hin ha hl e j]

end

end Incomplete.Obj
