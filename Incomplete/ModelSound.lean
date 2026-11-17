import Incomplete.Model

/-!
# Soundness of the fragment for the set model

Every `BDefEq natEnv` judgment holds in the model: at any values of the context's variables in
their types, the two sides denote the same set, a member of the type. So the fragment does not
prove `False`, and it proves `halts f n` only when `f` halts on `n`.
-/

namespace Lean4Lean.Incomplete
open VExpr ZFSet

attribute [local instance] Classical.propDecidable

/-- The values `ρ` of the variables lie in their types. -/
def Sat (Γ : List VExpr) (ρ : Nat → ZS) : Prop := ∀ i A, Lookup Γ i A → ρ i ∈ interp [] A ρ

theorem Sat.cons {Γ : List VExpr} {ρ : Nat → ZS} {A : VExpr} {x : ZS} (h : Sat Γ ρ)
    (hx : x ∈ interp [] A ρ) : Sat (A :: Γ) (zcons x ρ) := by
  intro i B hl
  cases hl with
  | zero => rw [interp_lift]; exact hx
  | succ hl => rw [interp_lift]; exact h _ _ hl

theorem Sat.nil (ρ : Nat → ZS) : Sat [] ρ := fun _ _ h => nomatch h

theorem natEnv_const {c : Lean.Name} {ci : VConstant} (h : natEnv.constants c = some ci) :
    (c = ``Nat.rec ∧ ci = ⟨1, recTy⟩) ∨ (c = ``Nat.succ ∧ ci = ⟨0, .forallE nat nat⟩) ∨
      (c = ``Nat.zero ∧ ci = ⟨0, nat⟩) ∨ (c = ``Nat ∧ ci = ⟨0, .sort (.succ .zero)⟩) := by
  rw [natEnv_tables.consts] at h
  simp only [natT, tlookup] at h
  split at h
  · cases h; exact .inl ⟨‹_›, rfl⟩
  split at h
  · cases h; exact .inr (.inl ⟨‹_›, rfl⟩)
  split at h
  · cases h; exact .inr (.inr (.inl ⟨‹_›, rfl⟩))
  split at h
  · cases h; exact .inr (.inr (.inr ⟨‹_›, rfl⟩))
  · cases h

theorem natEnv_defeq {df : VDefEq} (h : natEnv.defeqs df) : df = iotaSucc ∨ df = iotaZero := by
  have := (natEnv_tables.rules df).1 h
  simpa [natT] using this

theorem map_eval_eq : ∀ {ls ls' : List VLevel}, List.Forall₂ (· ≈ ·) ls ls' →
    ls.map (VLevel.eval []) = ls'.map (VLevel.eval [])
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons h hs => by
    simp only [List.map_cons, map_eval_eq hs]; congr 1; exact congrFun h []

theorem mem_V0_of_univ {u : Nat} {x : ZS} (hu : u ≤ 1) (h : x ∈ univ u) : x ∈ V0 := by
  match u, hu with
  | 0, _ => exact V0_trans two_mem_V0 h
  | 1, _ => exact h

theorem pi_mem_univ {u v : Nat} {A : ZS} {B : ZS → ZS} (hu : u ≤ 1) (hv : v ≤ 1)
    (hA : A ∈ univ u) (hB : ∀ x ∈ A, B x ∈ univ v) : pi A B ∈ univ (Lean.Nat.imax u v) := by
  rcases (by omega : v = 0 ∨ v = 1) with rfl | rfl
  · exact pi_mem_two hB
  · have : Lean.Nat.imax u 1 = 1 := by
      unfold Lean.Nat.imax; simp only [Nat.one_ne_zero, if_false]; exact Nat.max_eq_right hu
    rw [this]
    exact pi_mem_V0 (mem_V0_of_univ hu hA) hB

/-! ### The iota rules -/

theorem motive_mem {u : Nat} {M n : ZS} (hM : M ∈ pi omega fun _ => univ u) (hn : n ∈ omega) :
    app M n ∈ univ u := app_mem_pi hM hn

theorem iotaZero_sound (u : Nat) (ρ : Nat → ZS) :
    interp [u] iotaZero.lhs ρ = interp [u] iotaZero.rhs ρ ∧
      interp [u] iotaZero.lhs ρ ∈ interp [u] iotaZero.type ρ := by
  simp only [iotaZero, VExpr.lams, VExpr.foralls, VExpr.appN, interp, recC, motiveTy, zeroTy,
    succTy, zcons_zero, zcons_succ, interp_nat, interp_zero, interp_succ, List.map_cons,
    List.map_nil, VLevel.eval, constV, if_neg (show ¬(``Nat.rec : Lean.Name) = ``Nat by decide),
    if_neg (show ¬(``Nat.rec : Lean.Name) = ``Nat.zero by decide),
    if_neg (show ¬(``Nat.rec : Lean.Name) = ``Nat.succ by decide), if_true, List.headD_cons,
    List.getD_cons_zero]
  constructor
  · refine lam_congr fun M hM => lam_congr fun z hz => lam_congr fun s hs => ?_
    rw [recV_app hM hz hs (num_mem_omega 0), natOf_num]; rfl
  · refine lam_mem_pi fun M hM => lam_mem_pi fun z hz => lam_mem_pi fun s hs => ?_
    rw [recV_app hM hz hs (num_mem_omega 0), natOf_num]; exact hz

theorem iotaSucc_sound (u : Nat) (ρ : Nat → ZS) :
    interp [u] iotaSucc.lhs ρ = interp [u] iotaSucc.rhs ρ ∧
      interp [u] iotaSucc.lhs ρ ∈ interp [u] iotaSucc.type ρ := by
  simp only [iotaSucc, VExpr.lams, VExpr.foralls, VExpr.appN, interp, recC, motiveTy, zeroTy,
    succTy, zcons_zero, zcons_succ, interp_nat, interp_zero, interp_succ, List.map_cons,
    List.map_nil, VLevel.eval, constV, if_neg (show ¬(``Nat.rec : Lean.Name) = ``Nat by decide),
    if_neg (show ¬(``Nat.rec : Lean.Name) = ``Nat.zero by decide),
    if_neg (show ¬(``Nat.rec : Lean.Name) = ``Nat.succ by decide), if_true, List.headD_cons,
    List.getD_cons_zero]
  have key : ∀ {M z s n : ZS}, M ∈ pi omega (fun _ => univ u) → z ∈ app M (num 0) →
      s ∈ (pi omega fun n => pi (app M n) fun _ => app M (app succV n)) → n ∈ omega →
      app (app (app (app (recV u) M) z) s) (app succV n) =
        app (app s n) (app (app (app (app (recV u) M) z) s) n) ∧
      app (app (app (app (recV u) M) z) s) (app succV n) ∈ app M (app succV n) := by
    intro M z s n hM hz hs hn
    obtain ⟨k, rfl⟩ := mem_omega.1 hn
    have hsn : app succV (num k) = num (k + 1) := app_succV (num_mem_omega k)
    rw [hsn, recV_app hM hz hs (num_mem_omega _), recV_app hM hz hs (num_mem_omega _),
      natOf_num, natOf_num]
    exact ⟨rfl, recN_mem hz hs (k + 1)⟩
  constructor
  · refine lam_congr fun M hM => lam_congr fun z hz => lam_congr fun s hs =>
      lam_congr fun n hn => (key hM hz hs hn).1
  · exact lam_mem_pi fun M hM => lam_mem_pi fun z hz => lam_mem_pi fun s hs =>
      lam_mem_pi fun n hn => (key hM hz hs hn).2

/-! ### Soundness -/

/-- **Soundness** of the fragment for the set model. -/
theorem BDefEq.sound {Γ : List VExpr} {e1 e2 A : VExpr} (H : BDefEq natEnv Γ e1 e2 A) :
    ∀ ρ, Sat Γ ρ → interp [] e1 ρ = interp [] e2 ρ ∧ interp [] e1 ρ ∈ interp [] A ρ := by
  induction H with
  | bvar h => exact fun ρ hρ => ⟨rfl, hρ _ _ h⟩
  | symm _ ih => exact fun ρ hρ => let ⟨e, m⟩ := ih ρ hρ; ⟨e.symm, e ▸ m⟩
  | trans _ _ ih₁ ih₂ => exact fun ρ hρ => ⟨(ih₁ ρ hρ).1.trans (ih₂ ρ hρ).1, (ih₁ ρ hρ).2⟩
  | @sortDF l l' Γ _ _ he hl =>
    intro ρ _
    have hl' : l'.eval [] = 0 := (congrFun he []).symm.trans hl
    simp only [interp, hl, hl', VLevel.eval]
    exact ⟨by first | rfl | trivial, two_mem_V0⟩
  | @constDF c ci ls ls' Γ hc _ _ hlen he _ =>
    intro ρ _
    simp only [interp, interp_instL, map_eval_eq he]
    refine ⟨by first | rfl | trivial, ?_⟩
    rcases natEnv_const hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · obtain ⟨l, hl⟩ : ∃ l, ls' = [l] := by
        have h1 : ls'.length = 1 := (List.Forall₂.length_eq he).symm.trans hlen
        match ls', h1 with | [l], _ => exact ⟨l, rfl⟩
      simp only [hl, List.map_cons, List.map_nil, constV, interp_recTy]
      simp only [show ¬(``Nat.rec : Lean.Name) = ``Nat by decide,
        show ¬(``Nat.rec : Lean.Name) = ``Nat.zero by decide,
        show ¬(``Nat.rec : Lean.Name) = ``Nat.succ by decide, if_false, if_true,
        List.headD_cons]
      exact recV_mem _
    · simp only [constV, show ¬(``Nat.succ : Lean.Name) = ``Nat by decide,
        show ¬(``Nat.succ : Lean.Name) = ``Nat.zero by decide, if_false, if_true, interp,
        interp_nat]
      exact succV_mem
    · simp only [constV, show ¬(``Nat.zero : Lean.Name) = ``Nat by decide, if_false, if_true,
        interp_nat]
      exact num_mem_omega 0
    · simp only [constV, if_true, interp, VLevel.eval, univ]
      exact omega_mem_V0
  | appDF _ _ ih₁ ih₂ =>
    intro ρ hρ
    obtain ⟨e1, m1⟩ := ih₁ ρ hρ; obtain ⟨e2, m2⟩ := ih₂ ρ hρ
    simp only [interp] at m1 ⊢
    rw [interp_inst, ← e1, ← e2]
    exact ⟨rfl, app_mem_pi m1 m2⟩
  | lamDF _ _ ih₁ ih₂ =>
    intro ρ hρ
    obtain ⟨e1, -⟩ := ih₁ ρ hρ
    simp only [interp]
    rw [← e1]
    refine ⟨lam_congr fun x hx => (ih₂ _ (hρ.cons hx)).1, lam_mem_pi fun x hx => ?_⟩
    exact (ih₂ _ (hρ.cons hx)).2
  | forallEDF _ _ _ _ hu hv ih₁ ih₂ =>
    intro ρ hρ
    obtain ⟨e1, m1⟩ := ih₁ ρ hρ
    simp only [interp] at m1 ⊢
    rw [← e1]
    refine ⟨pi_congr fun x hx => (ih₂ _ (hρ.cons hx)).1, ?_⟩
    simp only [VLevel.eval]
    exact pi_mem_univ hu hv m1 fun x hx => (ih₂ _ (hρ.cons hx)).2
  | defeqDF _ _ ih₁ ih₂ =>
    intro ρ hρ
    obtain ⟨e1, -⟩ := ih₁ ρ hρ
    obtain ⟨e2, m2⟩ := ih₂ ρ hρ
    exact ⟨e2, e1 ▸ m2⟩
  | beta _ _ ih₁ ih₂ =>
    intro ρ hρ
    obtain ⟨-, m2⟩ := ih₂ ρ hρ
    obtain ⟨-, m1⟩ := ih₁ _ (hρ.cons m2)
    simp only [interp]
    rw [app_lam m2, interp_inst, interp_inst]
    exact ⟨rfl, m1⟩
  | eta _ ih =>
    intro ρ hρ
    obtain ⟨-, m⟩ := ih ρ hρ
    simp only [interp, zcons_zero] at m ⊢
    have : (lam (interp [] _ ρ) fun x => app (interp [] _ (zcons x ρ)) x) = _ :=
      (lam_congr fun x _ => by rw [interp_lift]).trans (lam_app_of_mem_pi m)
    rw [this]
    exact ⟨rfl, m⟩
  | proofIrrel _ _ _ ih₁ ih₂ ih₃ =>
    intro ρ hρ
    obtain ⟨-, m1⟩ := ih₁ ρ hρ
    obtain ⟨-, m2⟩ := ih₂ ρ hρ
    obtain ⟨-, m3⟩ := ih₃ ρ hρ
    simp only [interp, VLevel.eval, univ] at m1
    exact ⟨(proof_eq m1 m2).trans (proof_eq m1 m3).symm, m2⟩
  | @extra df ls Γ hd _ hlen _ =>
    intro ρ _
    simp only [interp_instL]
    rcases natEnv_defeq hd with rfl | rfl
    · obtain ⟨l, rfl⟩ : ∃ l, ls = [l] := match ls, hlen with | [l], _ => ⟨l, rfl⟩
      exact iotaSucc_sound _ ρ
    · obtain ⟨l, rfl⟩ : ∃ l, ls = [l] := match ls, hlen with | [l], _ => ⟨l, rfl⟩
      exact iotaZero_sound _ ρ

/-! ### Consequences -/

theorem interp_falseS (ρ : Nat → ZS) (y : ZS) : ¬y ∈ interp [] falseS ρ := by
  intro hy
  simp only [falseS, interp, zcons_zero, VLevel.eval, univ] at hy
  have := app_mem_pi hy (mem_two.2 (.inl rfl))
  exact not_mem_empty _ this

/-- **Consistency** of the fragment: it does not prove `False`. -/
theorem bconsistent : ¬BProvable natEnv falseS := fun ⟨_, h⟩ =>
  interp_falseS (fun _ => empty) _ ((h.sound _ (Sat.nil _)).2)

/-- `isZero` of a successor numeral is `False`, in the fragment. -/
theorem bisZero_succ (j : Nat) :
    BDefEq natEnv [] (isZero (lit (j + 1))) falseS (.sort .zero) := by
  have H := hasNat_natEnv
  have henv := natEnv_ordered
  have hS := bisZeroStepT H (Γ := [])
  have hR := H.bnatRecT Inert.sort (fun _ => .sort0) btrueT hS (H.blitT j) (Γ := [])
  have h1 := H.biota_succ henv Inert.sort (fun _ => .sort0) btrueT hS (H.blitT j)
  have b1 : BDefEq natEnv [] (.app (.lam nat (.lam (.sort .zero) falseS)) (lit j))
      (.lam (.sort .zero) falseS) (.forallE (.sort .zero) (.sort .zero)) :=
    BDefEq.beta (.lamDF .sort0 bfalseT) (H.blitT j)
  have b2 : BDefEq natEnv [] (.app (.lam (.sort .zero) falseS) (natRec (.sort .zero) trueS
      (.lam nat (.lam (.sort .zero) falseS)) (lit j))) falseS (.sort .zero) :=
    BDefEq.beta bfalseT hR
  exact h1.trans ((BDefEq.appDF b1 hR).trans b2)

theorem interp_lit_inst {e : VExpr} {m : Nat} (ρ : Nat → ZS) :
    interp [] (e.inst (lit m)) ρ = interp [] e (zcons (num m) ρ) := by
  rw [interp_inst, interp_lit]

/-- **Soundness for `halts`**: the fragment proves `halts f n` only when `f` halts on `n`. -/
theorem bhaltsSound {f : PR} {n : Nat} (hp : BProvable natEnv (halts f n)) : f.Halts n := by
  have H := hasNat_natEnv
  have henv := natEnv_ordered
  obtain ⟨e, h⟩ := hp
  let ρ : Nat → ZS := fun _ => empty
  have m := (h.sound ρ (Sat.nil _)).2
  simp only [halts, interp] at m
  -- the interpretation of `notHalts f n` is empty
  have hN : ∀ x, ¬x ∈ interp [] (notHalts f n) ρ := fun x hx =>
    interp_falseS _ _ (app_mem_pi m hx)
  refine Classical.byContradiction fun hnh => hN empty ?_
  simp only [notHalts, interp, interp_nat]
  have hfc : (fn f).ClosedN := (bfnT H henv f).toIsDefEq.closedN henv trivial
  rw [← lam_eq_empty (A := omega) (f := fun _ => empty) fun _ _ => rfl]
  refine lam_mem_pi fun x hx => ?_
  obtain ⟨k, rfl⟩ := mem_omega.1 hx
  -- `isZero (f k n)` denotes `False`
  have hIZ : ∀ y, ¬y ∈ interp [] (isZero (.app (.app (fn f) (lit n)) (.bvar 0)))
      (zcons (num k) ρ) := by
    intro y hy
    rw [← interp_lit_inst, isZero_inst] at hy
    have e1 : (VExpr.app (.app (fn f) (lit n)) (.bvar 0)).inst (lit k) =
        .app (.app (fn f) (lit n)) (lit k) := by
      simp [VExpr.inst, hfc.instN_eq (Nat.zero_le _), (Inert.lit n).inst]
    rw [e1] at hy
    have hfnT : BDefEq natEnv [] (.app (.app (fn f) (lit n)) (lit k))
        (.app (.app (fn f) (lit n)) (lit k)) nat :=
      .app' (.app' (bfnT H henv f) (H.blitT n) rfl) (H.blitT k) rfl
    have hc := bisZero_congr H hfnT (bfn_adequate H henv f n k)
    obtain ⟨j, hj⟩ : ∃ j, f.eval (val2 k n) = j + 1 :=
      match hv : f.eval (val2 k n) with
      | 0 => absurd ⟨k, hv⟩ hnh
      | j + 1 => ⟨j, rfl⟩
    rw [hj] at hc
    have := ((hc.trans (bisZero_succ j)).sound ρ (Sat.nil _)).1
    rw [this] at hy
    exact interp_falseS _ _ hy
  have : interp [] (.forallE (isZero (.app (.app (fn f) (lit n)) (.bvar 0))) falseS)
      (zcons (num k) ρ) = pi (interp [] (isZero (.app (.app (fn f) (lit n)) (.bvar 0)))
        (zcons (num k) ρ)) fun x => interp [] falseS (zcons x (zcons (num k) ρ)) := rfl
  rw [← lam_eq_empty (A := interp [] (isZero (.app (.app (fn f) (lit n)) (.bvar 0)))
    (zcons (num k) ρ)) (f := fun _ => empty) fun y hy => absurd hy (hIZ y)]
  exact lam_mem_pi fun y hy => absurd hy (hIZ y)

end Lean4Lean.Incomplete
