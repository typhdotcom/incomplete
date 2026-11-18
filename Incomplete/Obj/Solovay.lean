import Incomplete.Obj.SolovayLemmas
import Incomplete.Modal.Complete

/-!
# Arithmetical completeness of GL

Solovay's theorem: if the theory proves double-negation elimination and is `halts`-sound, every
modal formula provable under every realization is a theorem of `GL`.

For `¬GL A`, a finite countermodel `M` (`Modal.GL_complete`) with a new root `0` below its worlds
`w + 1` is a Solovay frame (`solFrame`). Solovay's machine for it gives the sentences `S_a`, and
`σ p := ⋁ {S_(w+1) | w ⊩ p}`. Inside the theory, `S_(w+1)` proves `B*` when `w ⊩ B` and `¬B*`
otherwise (`truth`), so a proof of `A*` refutes `S_1`, then `S_0` (`Ss_not_prov`). That
refutation is false: the walk starts at `0` and only moves along refuted `S_b`, and every
refutation of an `S_b` the walk reaches makes it leave `b` (`halts_lv`, `HaltsSound`), an endless
climb up the finite frame (`no_refuted`).
-/

namespace Incomplete
open Lean4Lean Obj

namespace Modal.FinModel
variable {n : Nat} (M : FinModel (n + 1))

/-- `M` below a new root `0`, its worlds `w` renumbered `w + 1`. -/
def solR (a b : Nat) : Bool :=
  if hb : 1 ≤ b ∧ b ≤ n + 1 then
    if a = 0 then true
    else if ha : a ≤ n + 1 then M.R ⟨a - 1, by omega⟩ ⟨b - 1, by omega⟩ else false
  else false

theorem solR_zero {b : Nat} (h1 : 1 ≤ b) (h2 : b ≤ n + 1) : M.solR 0 b = true := by
  simp [solR, h1, h2]

theorem solR_succ (w v : Fin (n + 1)) : M.solR (w.val + 1) (v.val + 1) = M.R w v := by
  have := v.isLt; have := w.isLt
  simp only [solR, Nat.add_sub_cancel]
  rw [dif_pos (by omega), if_neg (by omega), dif_pos (by omega)]

theorem solR_spec {a b : Nat} (h : M.solR a b = true) :
    1 ≤ b ∧ b ≤ n + 1 ∧ a ≤ n + 1 ∧ (a ≠ 0 → ∃ (w v : Fin (n + 1)), a = w.val + 1 ∧
      b = v.val + 1 ∧ M.R w v = true) := by
  unfold solR at h
  split at h
  · refine ⟨by omega, by omega, ?_⟩
    split at h
    · exact ⟨by omega, fun h' => absurd ‹a = 0› h'⟩
    · split at h
      · exact ⟨by omega, fun _ => ⟨⟨a - 1, by omega⟩, ⟨b - 1, by omega⟩, by simp; omega,
          by simp; omega, h⟩⟩
      · exact absurd h Bool.false_ne_true
  · exact absurd h Bool.false_ne_true

/-- **The Solovay frame of `M`.** -/
def solFrame : SFrame where
  N := n + 1
  R := M.solR
  trans {a b c} hab hbc := by
    obtain ⟨hb1, hb2, ha, hA⟩ := M.solR_spec hab
    obtain ⟨hc1, hc2, -, hB⟩ := M.solR_spec hbc
    by_cases a0 : a = 0
    · subst a0; exact M.solR_zero hc1 hc2
    obtain ⟨w, v, rfl, rfl, hwv⟩ := hA a0
    obtain ⟨v', u, e, rfl, hvu⟩ := hB (by omega)
    obtain rfl : v = v' := Fin.ext (by omega)
    rw [solR_succ]; exact M.trans hwv hvu
  irrefl a := by
    cases h : M.solR a a
    · rfl
    · obtain ⟨h1, -, -, hA⟩ := M.solR_spec h
      obtain ⟨w, v, e1, e2, hwv⟩ := hA (by omega)
      obtain rfl : w = v := Fin.ext (by omega)
      rw [M.irrefl] at hwv; exact absurd hwv Bool.false_ne_true
  le h := by obtain ⟨-, h2, h3, -⟩ := M.solR_spec h; exact ⟨h3, h2⟩

theorem solFrame_R : (M.solFrame).R = M.solR := rfl
theorem solFrame_N : (M.solFrame).N = n + 1 := rfl

theorem mem_succL_succ (w : Fin (n + 1)) {b : Nat} :
    b ∈ (M.solFrame).succL (w.val + 1) ↔ ∃ v : Fin (n + 1), b = v.val + 1 ∧ M.R w v = true := by
  rw [SFrame.mem_succL, solFrame_R]
  constructor
  · intro h
    obtain ⟨-, -, -, hA⟩ := M.solR_spec h
    obtain ⟨w', v, e1, rfl, hwv⟩ := hA (by omega)
    obtain rfl : w = w' := Fin.ext (by omega)
    exact ⟨v, rfl, hwv⟩
  · rintro ⟨v, rfl, hv⟩; rw [solR_succ]; exact hv

end Modal.FinModel

namespace Obj

/-- The realization: `p` is the disjunction of the `S_(w+1)` at the worlds `w` forcing it. -/
def solσ (f : PR) (d : Nat) {n : Nat} (M : Modal.FinModel (n + 1)) (p : Nat) : VExpr :=
  bigOr (((List.finRange (n + 1)).filter fun v => M.V v p).map fun v => Ss f d (v.val + 1))

section
variable {env : VEnv} [E : ObjEnv env] {T : Tables} {f : PR} {d : Nat} {n : Nat}
  {M : Modal.FinModel (n + 1)}

theorem solσTy (p : Nat) : env.HasType 0 [] (solσ f d M p) (.sort .zero) := by
  unfold solσ; exact bigOrTy (props_map fun _ => SsTy _)

/-- A closed implication from a proof in the context of its premise. -/
theorem cl_intro {X Y : VExpr} (hX : env.HasType 0 [] X (.sort .zero))
    (hY : env.HasType 0 [] Y (.sort .zero)) (h : Thm env [X] Y) : Thm env [] (imp X Y) :=
  Thm.intro hX (h.cast (closedN_of_ty hY).lift_eq.symm)

theorem cl_hyp {Γ : List VExpr} {X : VExpr} (hX : env.HasType 0 [] X (.sort .zero)) :
    Thm env (X :: Γ) X :=
  (Thm.hyp .zero).cast (closedN_of_ty hX).lift_eq

theorem cl_weak {Γ : List VExpr} {X Y : VExpr} (hY : env.HasType 0 [] Y (.sort .zero))
    (h : Thm env Γ Y) : Thm env (X :: Γ) Y :=
  h.weak.cast (closedN_of_ty hY).lift_eq

/-- `neg X` in the context of `X`'s premise. -/
theorem cl_neg {Γ : List VExpr} {X : VExpr} (hX : env.HasType 0 [] X (.sort .zero))
    (h : Thm env (X :: Γ) falseS) : Thm env Γ (neg X) :=
  Thm.intro (closedTy hX) h

theorem cl_app {Γ : List VExpr} {X Y : VExpr} (h : Thm env [] (imp X Y)) (hx : Thm env Γ X) :
    Thm env Γ Y := h.weak0.mp hx

theorem cl_swap {X Y : VExpr} (hX : env.HasType 0 [] X (.sort .zero))
    (hY : env.HasType 0 [] Y (.sort .zero)) (h : Thm env [] (imp X (neg Y))) :
    Thm env [] (imp Y (neg X)) :=
  cl_intro hY (negTy hX) (cl_neg hX ((cl_app h (cl_hyp hX)).mp
    (cl_weak hY (cl_hyp (Γ := []) hY))))

theorem bigOr_cl_elim {ps : List VExpr} {Y : VExpr} (hps : Props env [] ps)
    (hY : env.HasType 0 [] Y (.sort .zero)) (h : ∀ p ∈ ps, Thm env [] (imp p Y)) :
    Thm env [] (imp (bigOr ps) Y) := by
  refine cl_intro (bigOrTy hps) hY ?_
  refine bigOr_elim (closedTy hY) (fun p hp => closedTy (hps p hp)) (cl_hyp (bigOrTy hps))
    fun p hp kp => ?_
  exact (cl_app (h p hp) (kp.cast (closedN_of_ty (hps p hp)).lift_eq)).cast
    (closedN_of_ty hY).lift_eq.symm

variable {q : Nat → PR}
  (hq : ∀ {Γ : List VExpr} (b : Nat) {r k : VExpr}, Tm env Γ r → Tm env Γ k →
    Thm env Γ (ev (q b) [r, k, lit d] =ₒ Qt f d T b k))
  (hs : ∀ {Γ : List VExpr} {k : VExpr}, Tm env Γ k →
    Thm env Γ (hT f d (S k) =ₒ ev (nextC M.solFrame q) [hT f d k, k, lit d]))
  (h0 : ∀ {Γ : List VExpr}, Thm env Γ (hT f d zero =ₒ zero))
  (hTb : TablesFor env T) (hdne : Provable env dneS)
include hq hs h0 hTb hdne

/-- **The truth lemma**: `S_(w+1)` proves `B*` when `w ⊩ B`, and `¬B*` otherwise. -/
theorem truth : ∀ (B : Modal) (w : Fin (n + 1)),
    (M.Forces w B → Thm env [] (imp (Ss f d (w.val + 1)) (B.real T (solσ f d M)))) ∧
    (¬M.Forces w B → Thm env [] (imp (Ss f d (w.val + 1)) (neg (B.real T (solσ f d M)))))
  | .var p, w => by
    have hσ := solσTy (env := env) (f := f) (d := d) (M := M) p
    refine ⟨fun h => cl_intro (SsTy _) hσ ?_, fun h => cl_swap hσ (SsTy _) ?_⟩
    · refine bigOr_intro (props_map fun _ => SsTy _) (List.mem_map_of_mem ?_) (cl_hyp (SsTy _))
      exact List.mem_filter.2 ⟨List.mem_finRange w, h⟩
    · refine bigOr_cl_elim (props_map fun _ => SsTy _) (negTy (SsTy _)) fun r hr => ?_
      obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hr
      have hvw : v.val + 1 ≠ w.val + 1 := by
        intro e
        obtain rfl : v = w := Fin.ext (by omega)
        exact h (List.mem_filter.1 hv).2
      exact cl_intro (SsTy _) (negTy (SsTy _)) (cl_neg (SsTy _)
        (Ss_disj hvw (cl_weak (SsTy _) (cl_hyp (SsTy _))) (cl_hyp (SsTy _))))
  | .bot, w => by
    refine ⟨fun h => h.elim, fun _ => cl_intro (SsTy _) (negTy falseTy) ?_⟩
    exact cl_neg falseTy (Thm.hyp .zero)
  | .imp B C, w => by
    have hσ : ∀ p, env.HasType 0 [] (solσ f d M p) (.sort .zero) := solσTy
    have hB := Modal.realTy (T := T) hσ B
    have hC := Modal.realTy (T := T) hσ C
    have ihB := truth B w
    have ihC := truth C w
    rw [Modal.real_imp hσ]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · refine cl_intro (SsTy _) (impTy hB hC) (Thm.intro (closedTy hB) ?_)
      rw [(closedN_of_ty hC).lift_eq]
      by_cases hb : M.Forces w B
      · exact cl_app (ihC.1 (h hb)) (cl_weak (SsTy _) (cl_hyp (SsTy _)))
      · exact Thm.exfalso ((cl_app (ihB.2 hb) (cl_weak (SsTy _) (cl_hyp (SsTy _)))).mp
          (cl_hyp hB)) (closedTy hC)
    · have hb : M.Forces w B := Classical.byContradiction fun hb => h fun hb' => absurd hb' hb
      have hc : ¬M.Forces w C := fun hc => h fun _ => hc
      refine cl_intro (SsTy _) (negTy (impTy hB hC)) (cl_neg (impTy hB hC) ?_)
      have hi : Thm env [imp (B.real T (solσ f d M)) (C.real T (solσ f d M)), Ss f d (w.val + 1)]
          (imp (B.real T (solσ f d M)) (C.real T (solσ f d M))) := cl_hyp (impTy hB hC)
      have hS : Thm env [imp (B.real T (solσ f d M)) (C.real T (solσ f d M)), Ss f d (w.val + 1)]
          (Ss f d (w.val + 1)) := cl_weak (SsTy _) (cl_hyp (SsTy _))
      exact (cl_app (ihC.2 hc) hS).mp (hi.mp (cl_app (ihB.1 hb) hS))
  | .box B, w => by
    have hσ : ∀ p, env.HasType 0 [] (solσ f d M p) (.sort .zero) := solσTy
    have hB := Modal.realTy (T := T) hσ B
    have hBc := closedN_of_ty hB
    rw [Modal.real_box]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have hI : Thm env [] (imp (bigOr ((M.solFrame.succL (w.val + 1)).map (Ss f d)))
          (B.real T (solσ f d M))) := by
        refine bigOr_cl_elim (props_map fun _ => SsTy _) hB fun r hr => ?_
        obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hr
        obtain ⟨v, rfl, hv⟩ := (M.mem_succL_succ w).1 hb
        exact (truth B v).1 (h v hv)
      have hP := prov_imp hTb hBc hI
      refine cl_intro (SsTy _) (ProvTy T _) (cl_app hP ?_)
      exact Ss_prov hq hs h0 hTb hdne (by omega) (by simp [Modal.FinModel.solFrame_N]; omega)
        (cl_hyp (SsTy _))
    · have : ∃ v : Fin (n + 1), M.R w v = true ∧ ¬M.Forces v B :=
        Classical.byContradiction fun hn => h fun v hv =>
          Classical.byContradiction fun hf => hn ⟨v, hv, hf⟩
      obtain ⟨v, hv, hf⟩ := this
      have hN := cl_swap (SsTy _) hB ((truth B v).2 hf)
      have hP := prov_imp hTb (closedN_of_ty (negTy (SsTy (env := env) (f := f) (d := d)
        (v.val + 1)))) hN
      refine cl_intro (SsTy _) (negTy (ProvTy T _)) (cl_neg (ProvTy T _) ?_)
      refine Ss_not_prov hq hs (i := w.val + 1) (j := v.val + 1) ?_
        (cl_weak (SsTy _) (cl_hyp (SsTy _))) (cl_app hP (cl_hyp (ProvTy T _)))
      show M.solR _ _ = true
      rw [Modal.FinModel.solR_succ]; exact hv

end

end Obj

end Incomplete
