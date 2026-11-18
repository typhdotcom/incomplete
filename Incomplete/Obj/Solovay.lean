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

/-! ### The walk never climbs forever -/

section
variable {env : VEnv} [E : ObjEnv env] {T : Tables} {K : SFrame} {d : Nat}

/-- The walk's true value at `m`, provably. -/
theorem hN_lit {Γ : List VExpr} {m a : Nat} (h : hN T K d m = a) :
    Thm env Γ (hT (hM T K) d (lit m) =ₒ lit a) := by
  have e := ev_lits (env := env) (Γ := Γ) (hM T K) [m, d]
  have ee : (hM T K).eval (fun i => [m, d].getD i 0) = hN T K d m := by
    unfold hN; congr 1; funext i; rcases i with _ | _ | i <;> rfl
  rw [ee, h] at e
  unfold hT
  exact Thm.trans (by otype) (by otype) (by otype) (fn_ev (litTy d) (litTy m)) e

/-- **No reached world is refuted**, in a `halts`-sound theory: a refutation of `S_a` for a world
`a` the walk reaches makes it leave `a` (`halts_lv`), along a refutation of the next world's
sentence (`hN_move`), and the frame is finite. -/
theorem no_refuted (hTb : TablesFor env T) (hS : HaltsSound env) (hd : d = (hM T K).code) :
    ∀ (a m : Nat), hN T K d m = a → Provable env (neg (Ss (hM T K) d a)) → False := by
  intro a m hm hr
  have hPa : Thm env [] (Pa (hM T K) d a) := by
    unfold Pa
    exact Thm.exI (by otype) (litTy m) (by simpa only [obj_simp] using hN_lit (Γ := []) hm)
  have hnS : Thm env [] (neg (Stay (hM T K) d a)) :=
    cl_neg (StayTy a) (Thm.absurd (cl_weak (negTy (SsTy a)) (hr : Thm env [] _))
      (Thm.conjI (by otype) (by otype) (cl_weak (PaTy a) hPa) (cl_hyp (StayTy a))))
  have hH : Provable env (halts (lvM T K a) d) :=
    (halts_lv (nx := nextC K (qC T)) (fun hk => hM_succ hk) hnS).provable
  obtain ⟨k, hk⟩ := hS _ _ hH
  obtain ⟨h1, h2⟩ := lvM_eval hk
  obtain ⟨hR, hc⟩ := hN_move (T := T) (K := K) (d := d) (k := k) (by rw [h1]; exact h2)
  rw [eval_negSC (hM T K) _ (by exact hd)] at hc
  have hprov : Provable env (neg (Ss (hM T K) d (hN T K d (k + 1)))) :=
    (chkNum_eq_zero hTb _).1 ⟨_, hc⟩
  have hb : hN T K d (k + 1) ∈ K.succL a := (K.mem_succL).2 (h1 ▸ hR)
  exact no_refuted hTb hS hd (hN T K d (k + 1)) (k + 1) rfl hprov
termination_by a => (K.succL a).length
decreasing_by exact succL_lt hb

end

end Obj

end Incomplete

namespace Incomplete
open Lean4Lean Obj

/-- **Arithmetical completeness of GL** (Solovay). If the theory proves double-negation
elimination and is `halts`-sound, every modal formula that `GL` does not prove has a realization
by closed propositions, with `□` read as `Prov T`, that the theory does not prove. -/
theorem GL_arith_complete (env : VEnv) (hwf : env.WF) (hext : natEnv ≤ env) {T : Tables}
    (hT : TablesFor env T) (hdne : Provable env dneS) (hS : HaltsSound env) {A : Modal}
    (h : ¬Modal.GL A) :
    ∃ σ : Nat → VExpr, (∀ n, env.HasType 0 [] (σ n) (.sort .zero)) ∧
      ¬Provable env (A.real T σ) := by
  have : ObjEnv env := ⟨hasNat_natEnv.mono hext, hwf.ordered⟩
  obtain ⟨n, M, -, -, hM0⟩ := Modal.GL_complete h
  refine ⟨solσ (hM T M.solFrame) (hM T M.solFrame).code M, fun p => solσTy p, fun hA => ?_⟩
  generalize hd : (hM T M.solFrame).code = d at hA
  have hσ : ∀ p, env.HasType 0 [] (solσ (hM T M.solFrame) d M p) (.sort .zero) := solσTy
  have hq : ∀ {Γ : List VExpr} (b : Nat) {r k : VExpr}, Tm env Γ r → Tm env Γ k →
      Thm env Γ (ev (qC T b) [r, k, lit d] =ₒ Qt (hM T M.solFrame) d T b k) :=
    fun {_} b {_ _} hr hk => hM_test hd.symm b hr hk
  have htr := (truth hq (fun hk => hM_succ hk) hM_zero hT hdne A 0).2 hM0
  have hAT := Modal.realTy (T := T) hσ A
  have hn1 : Thm env [] (neg (Ss (hM T M.solFrame) d ((0 : Fin (n + 1)).val + 1))) :=
    cl_neg (SsTy _) ((cl_app htr (cl_hyp (SsTy _))).mp (cl_weak hAT (hA : Thm env [] _)))
  have hp1 := prov_of_provable this.hasNat this.ordered hT hn1.provable
  have hn0 : Thm env [] (neg (Ss (hM T M.solFrame) d 0)) :=
    cl_neg (SsTy 0) (Ss_not_prov hq (fun hk => hM_succ hk) (i := 0)
      (j := (0 : Fin (n + 1)).val + 1)
      (M.solR_zero (b := (0 : Fin (n + 1)).val + 1) (by simp) (by simp)) (cl_hyp (SsTy 0))
      (cl_weak (ProvTy T _) (hp1 : Thm env [] _)))
  exact no_refuted hT hS hd.symm 0 0 (hN_zero d) hn0.provable

/-- **GL is the provability logic** of every `halts`-sound well-formed extension of `natEnv` that
proves double-negation elimination: a modal formula is a theorem of `GL` exactly when the theory
proves it under every realization by closed propositions, with `□` read as `Prov T`. -/
theorem GL_iff_provable (env : VEnv) (hwf : env.WF) (hext : natEnv ≤ env) {T : Tables}
    (hT : TablesFor env T) (hdne : Provable env dneS) (hS : HaltsSound env) {A : Modal} :
    Modal.GL A ↔ ∀ σ : Nat → VExpr, (∀ n, env.HasType 0 [] (σ n) (.sort .zero)) →
      Provable env (A.real T σ) :=
  ⟨fun h _ hσ => GL_sound env hwf hext hT hdne hσ h, fun h => Classical.byContradiction fun hA =>
    let ⟨σ, hσ, hn⟩ := GL_arith_complete env hwf hext hT hdne hS hA
    hn (h σ hσ)⟩

end Incomplete
