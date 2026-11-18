import Incomplete.Obj.Holes

/-!
# Chaining certificates

`mpX c₁ c₂` is the `appDF` certificate from `c₁ : ⊢ p : ∀ A, B` and `c₂ : ⊢ q : A`, with `A`,
`B`, `p` and `q` read off the children's judgments, so that a fixed code `mpP` computes it from
codes of the children. Internally, proofs of `∀ A, B` and of `A` give one of `B[q]` (`prf_mp`);
for sentences that are templates whose holes are numerals, modus ponens (`prf_mpH`) and
instantiation at a numeral (`prf_allH`) keep them templates. Instantiating a closed
`∀ x₁ … xₘ, P` at the values of codes `as` is the code `instL c as` (`prf_instL`).
-/

namespace Incomplete.Obj
open Lean4Lean
open VExpr Typing PR

/-- The `appDF` certificate from `c₁ : ⊢ p : ∀ A, B` and `c₂ : ⊢ q : A`, its parts read off the
children's judgments. -/
noncomputable def mpX (c₁ c₂ : VExpr) : VExpr :=
  appT zero (fst (div 7 (restT 3 (jT c₁)))) (snd (div 7 (restT 3 (jT c₁))))
    (fldT 1 (jT c₁)) (fldT 1 (jT c₁)) (fldT 1 (jT c₂)) (fldT 1 (jT c₂)) c₁ c₂

@[obj_simp] theorem mpX_liftN {c₁ c₂ : VExpr} {n k : Nat} :
    (mpX c₁ c₂).liftN n k = mpX (c₁.liftN n k) (c₂.liftN n k) := by
  simp only [mpX, obj_simp]

@[obj_simp] theorem mpX_inst {c₁ c₂ e : VExpr} {k : Nat} :
    (mpX c₁ c₂).inst e k = mpX (c₁.inst e k) (c₂.inst e k) := by
  simp only [mpX, obj_simp]

theorem mpXTy {env : Typing} [ObjEnv env] {Γ : List VExpr} {c₁ c₂ : VExpr} (h₁ : Tm env Γ c₁)
    (h₂ : Tm env Γ c₂) : Tm env Γ (mpX c₁ c₂) := by
  unfold mpX; otype

macro_rules | `(tactic| otype_rules) => `(tactic| ((with_reducible refine mpXTy ?_ ?_) <;> otype))

/-- The code of `mpX`. -/
def mpP (p₁ p₂ : PR) : PR :=
  appC (num 0) (fstC (divC 7 (restC 3 (childJC p₁)))) (sndC (divC 7 (restC 3 (childJC p₁))))
    (fldC 1 (childJC p₁)) (fldC 1 (childJC p₁)) (fldC 1 (childJC p₂)) (fldC 1 (childJC p₂)) p₁ p₂

/-- `∀ x₁ … xₘ, P`. -/
def allN : Nat → VExpr → VExpr
  | 0, P => P
  | m + 1, P => all (allN m P)

section
variable {env : Typing} [E : ObjEnv env] {Γ l : List VExpr} {T : Tables}

theorem ev_mpP {p₁ p₂ : PR} (hl : Tms env Γ l) :
    Thm env Γ (ev (mpP p₁ p₂) l =ₒ mpX (ev p₁ l) (ev p₂ l)) := by
  simp only [mpP, mpX]
  orw [ev_appC hl, ev_fstC hl, ev_sndC hl, ev_divC hl, ev_restC hl, ev_fldC hl, ev_fldC hl,
    ev_childJC hl, ev_childJC hl, ← div_eq]

omit E in
theorem Tms.mem {l : List VExpr} (hl : Tms env Γ l) : ∀ {y}, y ∈ l → Tm env Γ y := by
  induction hl with
  | nil => intro y h; cases h
  | cons ha _ ih =>
    intro y h
    rcases List.mem_cons.1 h with rfl | h
    · exact ha
    · exact ih h

theorem Tms.map_litT {l : List VExpr} (hl : Tms env Γ l) : Tms env Γ (l.map litT) := by
  induction hl with
  | nil => exact .nil
  | cons ha _ ih => exact .cons (evTy (.cons ha .nil)) ih

omit E in
theorem Tms.append {l l' : List VExpr} (hl : Tms env Γ l) (hl' : Tms env Γ l') :
    Tms env Γ (l ++ l') := by
  induction hl with
  | nil => exact hl'
  | cons ha _ ih => exact .cons ha ih

omit E in
theorem Tms.reverse {l : List VExpr} (hl : Tms env Γ l) : Tms env Γ l.reverse := by
  induction hl with
  | nil => exact .nil
  | cons ha _ ih => rw [List.reverse_cons]; exact ih.append (.cons ha .nil)

theorem Tms.map_ev {as : List PR} (hl : Tms env Γ l) : Tms env Γ (as.map (ev · l)) := by
  induction as with
  | nil => exact .nil
  | cons a as ih => exact .cons (evTy hl) ih

end

macro_rules | `(tactic| otype_rules) => `(tactic| ((with_reducible refine Tms.map_litT ?_); otype))
macro_rules
  | `(tactic| otype_rules) => `(tactic| ((with_reducible refine Tms.append ?_ ?_) <;> otype))
macro_rules | `(tactic| otype_rules) => `(tactic| ((with_reducible refine Tms.reverse ?_); otype))
macro_rules | `(tactic| otype_rules) => `(tactic| ((with_reducible refine Tms.map_ev ?_); otype))

section
variable {env : Typing} [E : ObjEnv env] {Γ l : List VExpr} {T : Tables}

/-- Rewriting the sentence of a proof. -/
theorem prf_congr {T : PR} {s s' c : VExpr} (hs : Tm env Γ s) (hs' : Tm env Γ s') (hc : Tm env Γ c)
    (e : Thm env Γ (s =ₒ s')) (h : Thm env Γ (prf T s c =ₒ zero)) :
    Thm env Γ (prf T s' c =ₒ zero) := by
  have := Thm.subst (M := prf T (.bvar 0) c.lift =ₒ zero) (by otype) e hs hs'
    (by simp only [obj_simp]; exact h)
  simp only [obj_simp] at this
  exact this

/-- Rewriting the certificate of a proof. -/
theorem prf_congr_c {T : PR} {s c c' : VExpr} (hs : Tm env Γ s) (hc : Tm env Γ c) (hc' : Tm env Γ c')
    (e : Thm env Γ (c =ₒ c')) (h : Thm env Γ (prf T s c =ₒ zero)) :
    Thm env Γ (prf T s c' =ₒ zero) := by
  have := Thm.subst (M := prf T s.lift (.bvar 0) =ₒ zero) (by otype) e hc hc'
    (by simp only [obj_simp]; exact h)
  simp only [obj_simp] at this
  exact this

/-- **Internal modus ponens.** Proofs `c₁` of `∀ A, B` and `c₂` of `A` give the proof `mpX c₁ c₂`
of `B` instantiated at `c₂`'s term. -/
theorem prf_mp {A B c₁ c₂ : VExpr} (hA : Tm env Γ A) (hB : Tm env Γ B) (hc₁ : Tm env Γ c₁)
    (hc₂ : Tm env Γ c₂) (h₁ : Thm env Γ (prfT T (tagT 7 5 (pair A B)) c₁ =ₒ zero))
    (h₂ : Thm env Γ (prfT T A c₂ =ₒ zero)) :
    Thm env Γ (prfT T (instT B (fldT 1 (jT c₂)) zero) (mpX c₁ c₂) =ₒ zero) := by
  obtain ⟨k₁, j₁⟩ := prfT_inv (by otype) hc₁ h₁
  obtain ⟨k₂, j₂⟩ := prfT_inv hA hc₂ h₂
  have hS : Thm env Γ (restT 3 (jT c₁) =ₒ tagT 7 5 (pair A B)) := by
    orw [j₁, restT_pair_succ (by otype) (by otype), restT_pair_succ (by otype) (by otype),
      restT_pair_succ (by otype) (by otype)]
  have eA : Thm env Γ (fst (div 7 (restT 3 (jT c₁))) =ₒ A) := by
    orw [hS, div_tag (by decide) (by otype) (litTy 5) (lit_lt (by decide)), fst_pair hA hB]
  have eB : Thm env Γ (snd (div 7 (restT 3 (jT c₁))) =ₒ B) := by
    orw [hS, div_tag (by decide) (by otype) (litTy 5) (lit_lt (by decide)), snd_pair hA hB]
  have j₁' : Thm env Γ (jT c₁ =ₒ judgT zero (fldT 1 (jT c₁)) (fldT 1 (jT c₁))
      (tagT 7 5 (pair (fst (div 7 (restT 3 (jT c₁)))) (snd (div 7 (restT 3 (jT c₁))))))) := by
    orw [eA, eB]; exact j₁
  have j₂' : Thm env Γ (jT c₂ =ₒ judgT zero (fldT 1 (jT c₂)) (fldT 1 (jT c₂))
      (fst (div 7 (restT 3 (jT c₁))))) := by
    orw [eA]; exact j₂
  have hm := certT_appT zeroTy (by otype) (by otype) (by otype) (by otype) (by otype) (by otype)
    hc₁ hc₂ rfl k₁ k₂ j₁' j₂'
  have jm := jT_appT (g := zero) (A := fst (div 7 (restT 3 (jT c₁))))
    (B := snd (div 7 (restT 3 (jT c₁)))) (f := fldT 1 (jT c₁)) (f' := fldT 1 (jT c₁))
    (a := fldT 1 (jT c₂)) (a' := fldT 1 (jT c₂)) zeroTy (by otype) (by otype) (by otype)
    (by otype) (by otype) (by otype) hc₁ hc₂
  exact prfT_of_cert (e := tagT 7 3 (pair (fldT 1 (jT c₁)) (fldT 1 (jT c₂)))) (by otype)
    (by otype) (by otype) hm (by simp only [mpX]; orw [jm, eB])

theorem litT_inert {ys : List VExpr} (hys : Tms env Γ ys) {a : VExpr} (ha : Tm env Γ a) :
    ∀ x ∈ ys.map litT, ∀ k : Nat, Thm env Γ (instT x a (lit k) =ₒ x) := by
  intro x hx k
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
  exact instT_litT ha (litTy k) (hys.mem hy)

/-- **Modus ponens at templates.** -/
theorem prf_mpH {ys : List VExpr} {P Q c₁ c₂ : VExpr} (hys : Tms env Γ ys) (hc₁ : Tm env Γ c₁)
    (hc₂ : Tm env Γ c₂) (h₁ : Thm env Γ (prfT T (tmplH (ys.map litT) (imp P Q) 0) c₁ =ₒ zero))
    (h₂ : Thm env Γ (prfT T (tmplH (ys.map litT) P 0) c₂ =ₒ zero)) :
    Thm env Γ (prfT T (tmplH (ys.map litT) Q 0) (mpX c₁ c₂) =ₒ zero) := by
  have hh : Tms env Γ (ys.map litT) := hys.map_litT
  have e : tmplH (ys.map litT) (imp P Q) 0 =
      tagT 7 5 (pair (tmplH (ys.map litT) P 0) (tmplH (ys.map litT) (Q.liftN 1 0) 1)) := rfl
  rw [e] at h₁
  have h := prf_mp (by otype) (by otype) hc₁ hc₂ h₁ h₂
  have i := instT_tmplH_lift hh (litT_inert hys (a := fldT 1 (jT c₂)) (by otype)) (by otype) Q 0
  simp only [lit_zero, Nat.zero_add] at i
  exact prf_congr (by otype) (by otype) (by otype) i h

theorem bnd_numCertC {z s : Nat} : bnd (numCertC z s) ≤ 1 := by
  have := bnd_litC; have := bnd_instC; unfold numCertC appC judgC; obnd

theorem ev_push_numCert {z s : Nat} {a : PR} (hl : Tms env Γ l) :
    Thm env Γ (ev (push a (numCertC z s)) l =ₒ numCert z s (ev a l)) := by
  orw [ev_push rfl hl]
  rw [ev_take 1 (bnd_numCertC (z := z) (s := s))]
  simp only [List.take_succ_cons, List.take_zero]
  orefl

variable {z s : Nat}
  (hz : Thm env [] (certT T (fun _ => true) (numT z) =ₒ zero))
  (jz : Thm env [] (jT (numT z) =ₒ
    judgT zero (numT (encExpr Incomplete.zero)) (numT (encExpr Incomplete.zero)) (numT (encExpr nat))))
  (hs : Thm env [] (certT T (fun _ => true) (numT s) =ₒ zero))
  (js : Thm env [] (jT (numT s) =ₒ
    judgT zero (numT (encExpr succ)) (numT (encExpr succ)) (numT (encExpr (.forallE nat nat)))))
include hz jz hs js

/-- **Instantiation at a numeral, at templates.** -/
theorem prf_allH {ys : List VExpr} {P c a : VExpr} (hys : Tms env Γ ys) (hc : Tm env Γ c)
    (ha : Tm env Γ a) (h : Thm env Γ (prfT T (tmplH (ys.map litT) (all P) 0) c =ₒ zero)) :
    Thm env Γ (prfT T (tmplH ((a :: ys).map litT) P 0) (mpX c (numCert z s a)) =ₒ zero) := by
  have hh : Tms env Γ (ys.map litT) := hys.map_litT
  have hn := Thm.allE ((numCert_c hz jz hs js).weak0 (Γ := Γ)) ha
  simp only [obj_simp] at hn
  ocases hn with h1 h2
  have hp : Thm env Γ (prfT T (numT (encExpr nat)) (numCert z s a) =ₒ zero) :=
    prfT_of_cert (by otype) (by otype) (by otype) h1 h2
  have e : tmplH (ys.map litT) (all P) 0 =
      tagT 7 5 (pair (numT (encExpr nat)) (tmplH (ys.map litT) P 1)) := rfl
  rw [e] at h
  have hm := prf_mp (by otype) (by otype) hc (by otype) h hp
  have hq : Thm env Γ (fldT 1 (jT (numCert z s a)) =ₒ litT a) := by
    orw [h2, fldT_pair_succ (by otype) (by otype), fldT_pair_zero (by otype) (by otype)]
  have i := instT_tmplH_num hh (litT_inert hys (a := litT a) (by otype)) (by otype)
    (fun k => liftT_litT (litTy k) zeroTy ha) P 0
  simp only [lit_zero, Nat.zero_add] at i
  refine prf_congr (by otype) (by otype) (by otype) ?_ hm
  orw [hq]
  exact i

end

end Incomplete.Obj
