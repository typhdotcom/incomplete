import Incomplete.Obj.Chain
import Incomplete.LeafPR

/-!
# The fragment's bounds at symbolic certificates

`leafT c` is `leafC` at the certificate number `c`, `0` when the certificate keeps the bounds of
`BDefEq` (`Cert.leafOK`). Inside the theory: the `appDF` certificate of children within the
bounds is within them (`leafT_appT`), so are modus ponens (`leafT_mpX`) and the numeral
certificates `numCert z s k` for every `k` (`leafT_numCert`), and a closed certificate within
them is, provably, by computation (`leafT_numT`).
-/

namespace Incomplete.Obj
open Lean4Lean
open VExpr Typing PR

/-- `leafC` at the certificate number `c`. -/
noncomputable abbrev leafT (c : VExpr) : VExpr := cov leafStep c

theorem dispL_casc : ∀ k t, dispL k t =
    casc (modC 16 (var 0)) ((List.range k).map fun i => leafRule (t + i)) (num 1) t
  | 0, _ => rfl
  | k + 1, t => by
    rw [dispL, dispL_casc k (t + 1), List.range_succ_eq_map, List.map_cons, List.map_map, casc]
    simp only [Nat.add_zero, Nat.add_assoc, Nat.add_comm 1]
    rfl

theorem bnd_leafStep : bnd leafStep ≤ 2 :=
  bnd_ren_le _ _ _ fun i _ => by omega

@[obnd_le] theorem bnd_nz_le {a : PR} {m : Nat} (ha : bnd a ≤ m) : bnd (nz a) ≤ m := by
  unfold nz; obnd

@[obnd_le] theorem bnd_le1C_le {a : PR} {m : Nat} (ha : bnd a ≤ m) : bnd (le1C a) ≤ m := by
  unfold le1C leq; obnd

theorem bnd_le1Step : bnd le1Step ≤ 2 := by unfold le1Step; obnd

@[obnd_le] theorem bnd_le1At_le {a : PR} {m : Nat} (ha : bnd a ≤ m) : bnd (le1At a) ≤ m := by
  have := bnd_le1Step; unfold le1At; obnd

theorem bnd_leafRule : ∀ t, bnd (leafRule t) ≤ 2
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 => by simp only [leafRule]; obnd
  | _ + 13 => by simp only [leafRule]; obnd

theorem bnd_dispL : ∀ k t, bnd (dispL k t) ≤ 2
  | 0, _ => by simp only [dispL]; obnd
  | k + 1, t => by
    have := bnd_leafRule t; have := bnd_dispL k (t + 1)
    simp only [dispL]; obnd

section
variable {env : Typing} [E : ObjEnv env] {Γ : List VExpr}
  {g A B f f' a a' c c₁ c₂ x h : VExpr}

/-- The step at a certificate number with tag `t` runs the rule of `t`. -/
theorem ev_leafStep_tag {t : Nat} (ht : t < 16) (hx : Tm env Γ x) (hh : Tm env Γ h) :
    Thm env Γ (ev leafStep [add (mul (lit 16) x) (lit t), h] =ₒ
      ev (leafRule t) [add (mul (lit 16) x) (lit t), h]) := by
  have hl : Tms env Γ [add (mul (lit 16) x) (lit t), h] := by otype
  have e1 : ev (dispL 16 0) [add (mul (lit 16) x) (lit t), h] =
      (dispL 16 0).tr.subst fun i => valS [add (mul (lit 16) x) (lit t), h] (min i 1) :=
    (tr_closed _).subst_congr fun i hi => by
      have := bnd_dispL 16 0
      rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl
  have h1 := Thm.ofDefEq (ev_ren_df hl (fun i => min i 1) (dispL 16 0))
  rw [← e1] at h1
  refine Thm.trans (by otype) (by otype) (by otype) h1 ?_
  have hc : Thm env Γ (ev (modC 16 (var 0)) [add (mul (lit 16) x) (lit t), h] =ₒ lit (0 + t)) := by
    rw [Nat.zero_add]
    orw [ev_modC hl, ← mod_eq]
    exact mod_tag (by decide) hx (litTy t) (lit_lt ht)
  have h2 := ev_casc (c := modC 16 (var 0)) (d := num 1) hl
    ((List.range 16).map fun i => leafRule (0 + i)) 0 t (by simpa using ht) hc
  simp only [List.getElem_map, List.getElem_range, Nat.zero_add] at h2
  rw [dispL_casc]
  simpa only [Nat.zero_add] using h2

theorem leafT_eq (hc : Tm env Γ c) : Thm env Γ (leafT c =ₒ ev leafStep [c, hist leafStep c]) :=
  cov_eq bnd_leafStep hc

variable (hg : Tm env Γ g) (hA : Tm env Γ A) (hB : Tm env Γ B) (hf : Tm env Γ f)
  (hf' : Tm env Γ f') (ha : Tm env Γ a) (ha' : Tm env Γ a') (hc₁ : Tm env Γ c₁) (hc₂ : Tm env Γ c₂)
include hg hA hB hf hf' ha ha' hc₁ hc₂

/-- **`appDF` within the bounds.** -/
theorem leafT_appT (h₁ : Thm env Γ (leafT c₁ =ₒ zero)) (h₂ : Thm env Γ (leafT c₂ =ₒ zero)) :
    Thm env Γ (leafT (appT g A B f f' a a' c₁ c₂) =ₒ zero) := by
  have hJT : Tm env Γ (judgT g (tagT 7 3 (pair f a)) (tagT 7 3 (pair f' a')) (instT B a zero)) := by
    otype
  generalize hx : pair (judgT g (tagT 7 3 (pair f a)) (tagT 7 3 (pair f' a')) (instT B a zero))
    (pair A (pair B (pair f (pair f' (pair a (pair a' (pair c₁ c₂))))))) = x
  have hxT : Tm env Γ x := by subst hx; otype
  obtain ⟨-, -, -, -, -, -, -, x7, x8⟩ := tuple9 hJT hA hB hf hf' ha ha' hc₁ hc₂ hx.symm
  have happ : appT g A B f f' a a' c₁ c₂ = tagT 16 5 x := by rw [appT, hx]
  rw [happ]
  generalize hn : tagT 16 5 x = n
  have hnT : Tm env Γ n := by subst hn; otype
  generalize hH : hist leafStep n = H
  have hHT : Tm env Γ H := by subst hH; otype
  have hl : Tms env Γ [n, H] := by otype
  have hX : Thm env Γ (ev xC [n, H] =ₒ x) := by
    simp only [xC]; orw [ev_divC hl, ← div_eq]
    rw [← hn]
    exact div_tag (by decide) hxT (litTy 5) (lit_lt (by decide))
  have hF7 : Thm env Γ (ev (fldC 7 xC) [n, H] =ₒ fldT 7 x) := by orw [ev_fldC hl, hX]
  have hR8 : Thm env Γ (ev (restC 8 xC) [n, H] =ₒ restT 8 x) := by orw [ev_restC hl, hX]
  have hlt : ∀ y, Tm env Γ y → Thm env Γ (y ≤ₒ x) → Thm env Γ (y <ₒ n) := fun y hy h => by
    subst hn
    exact lt_of_le_of_lt hy hxT (by otype) h (lt_tag (t := lit 4) (by decide) hxT (litTy 4))
  have lt₁ : Thm env Γ (c₁ <ₒ n) := hlt _ hc₁ (by orw [← x7]; exact fldT_le 7 hxT)
  have lt₂ : Thm env Γ (c₂ <ₒ n) := hlt _ hc₂ (by orw [← x8]; exact restT_le 8 hxT)
  have hist₁ : Thm env Γ (ev (histAt (fldC 7 xC)) [n, H] =ₒ leafT c₁) := by
    orw [ev_histAt hnT hHT, hF7, x7]
    rw [← hH]
    exact nth_hist_lt bnd_leafStep hc₁ hnT lt₁
  have hist₂ : Thm env Γ (ev (histAt (restC 8 xC)) [n, H] =ₒ leafT c₂) := by
    orw [ev_histAt hnT hHT, hR8, x8]
    rw [← hH]
    exact nth_hist_lt bnd_leafStep hc₂ hnT lt₂
  orw [leafT_eq hnT]
  rw [hH]
  have hstep := ev_leafStep_tag (t := 5) (by decide) hxT hHT
  rw [show add (mul (lit 16) x) (lit 5) = n from hn] at hstep
  orw [hstep]
  show Thm env Γ (ev (andz (histAt (fldC 7 xC)) (histAt (restC 8 xC))) [n, H] =ₒ zero)
  exact ev_andz_zero rfl hl (by orw [hist₁, h₁]) (by orw [hist₂, h₂])

end

section
variable {env : Typing} [E : ObjEnv env] {Γ : List VExpr} {c₁ c₂ : VExpr}

/-- Modus ponens within the bounds. -/
theorem leafT_mpX (hc₁ : Tm env Γ c₁) (hc₂ : Tm env Γ c₂) (h₁ : Thm env Γ (leafT c₁ =ₒ zero))
    (h₂ : Thm env Γ (leafT c₂ =ₒ zero)) : Thm env Γ (leafT (mpX c₁ c₂) =ₒ zero) :=
  leafT_appT zeroTy (by otype) (by otype) (by otype) (by otype) (by otype) (by otype) hc₁ hc₂ h₁ h₂

/-- A closed certificate within the bounds, by computation. -/
theorem leafT_numT {c : Nat} (h : (decCert c).leafOK = true) :
    Thm env Γ (leafT (numT c) =ₒ zero) := by
  have h1 := ev_lits (env := env) (Γ := Γ) leafC [c]
  rw [leafC_computes] at h1
  simp only [List.getD_cons_zero, leafNum_eq_zero.2 h, lit_zero, List.map_cons, List.map_nil] at h1
  orw [numT_lit]; exact h1

/-- The numeral certificates are within the bounds when `z` and `s` are. -/
theorem leafT_numCert {z s : Nat} (hz : Thm env [] (leafT (numT z) =ₒ zero))
    (hs : Thm env [] (leafT (numT s) =ₒ zero)) :
    Thm env [] (∀ₒ k, leafT (numCert z s k) =ₒ zero) := by
  oind
  · orw [numCert_zero]; exact hz
  · ointro ih
    orw [numCert_succ (by otype)]
    exact leafT_appT (by otype) (by otype) (by otype) (by otype) (by otype) (by otype) (by otype)
      (by otype) (by otype) hs.weak0 ih

end

end Incomplete.Obj
