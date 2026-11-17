import Incomplete.NatWF

/-!
# Numerals and `Nat.rec` at a constant motive

`natRec A z s n` is `Nat.rec.{1} (fun _ => A) z s n` for a closed type `A : Type`. It is typed
in any context, and computes on numerals by the iota rules.
-/

namespace Incomplete
open Lean4Lean
open VExpr VEnv

section
variable {ls : List VLevel} {e : VExpr} {n k : Nat} {σ : Subst}
@[simp] theorem nat_instL : nat.instL ls = nat := rfl
@[simp] theorem zero_instL : zero.instL ls = zero := rfl
@[simp] theorem succ_instL : succ.instL ls = succ := rfl
@[simp] theorem nat_inst : nat.inst e k = nat := rfl
@[simp] theorem zero_inst : zero.inst e k = zero := rfl
@[simp] theorem succ_inst : succ.inst e k = succ := rfl
@[simp] theorem nat_liftN : nat.liftN n k = nat := rfl
@[simp] theorem zero_liftN : zero.liftN n k = zero := rfl
@[simp] theorem succ_liftN : succ.liftN n k = succ := rfl
@[simp] theorem nat_subst : nat.subst σ = nat := rfl
@[simp] theorem zero_subst : zero.subst σ = zero := rfl
@[simp] theorem succ_subst : succ.subst σ = succ := rfl
end

def lit : Nat → VExpr
  | 0 => zero
  | n + 1 => .app succ (lit n)

def motive (A : VExpr) : VExpr := .lam nat A

def natRec (A z s n : VExpr) : VExpr :=
  .appN (.const ``Nat.rec [.succ .zero]) [motive A, z, s, n]

/-- A term that lifting, instantiation and substitution leave alone, as a closed term is. -/
structure Inert (A : VExpr) : Prop where
  liftN : ∀ n k, A.liftN n k = A
  inst : ∀ e k, A.inst e k = A
  subst : ∀ σ, A.subst σ = A

theorem Inert.nat : Inert nat := ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl⟩
theorem Inert.sort : Inert (.sort u) := ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl⟩

theorem Inert.lit : ∀ n, Inert (lit n)
  | 0 => ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl⟩
  | n + 1 => let h := Inert.lit n
    ⟨fun _ _ => by simp [Incomplete.lit, VExpr.liftN, h.liftN],
     fun _ _ => by simp [Incomplete.lit, VExpr.inst, h.inst],
     fun _ => by simp [Incomplete.lit, h.subst]⟩

theorem Inert.motive (h : Inert A) : Inert (motive A) :=
  ⟨fun _ _ => by simp [Incomplete.motive, VExpr.liftN, h.liftN],
   fun _ _ => by simp [Incomplete.motive, VExpr.inst, h.inst],
   fun _ => by simp [Incomplete.motive, VExpr.subst, h.subst]⟩

section
variable {env : VEnv} {U : Nat} {Γ : List VExpr}

theorem NatConsts.natT (H : NatConsts env) : env.HasType U Γ nat (.sort (.succ .zero)) :=
  .const' H.hNat (by simp) rfl rfl

theorem NatConsts.zeroT (H : NatConsts env) : env.HasType U Γ zero nat :=
  .const' H.hZero (by simp) rfl rfl

theorem NatConsts.succT (H : NatConsts env) : env.HasType U Γ succ (.forallE nat nat) :=
  .const' H.hSucc (by simp) rfl rfl

theorem NatConsts.litT (H : NatConsts env) : ∀ n, env.HasType U Γ (lit n) nat
  | 0 => H.zeroT
  | n + 1 => .app' H.succT (H.litT n) rfl

/-- The motive applied to anything is `A`, by beta. -/
theorem motive_app (hI : Inert A)
    (hA : ∀ Γ, env.HasType U Γ A (.sort (.succ .zero))) (hn : env.HasType U Γ n nat) :
    env.IsDefEq U Γ (.app (motive A) n) A (.sort (.succ .zero)) := by
  have := IsDefEq.beta (hA (nat :: Γ)) hn
  rwa [hI.inst] at this

/-- The `succ` minor premise's type at the motive `fun _ => A` is `Nat → A → A`. -/
theorem succMinor_conv (N : NatConsts env) (hI : Inert A)
    (hA : ∀ Γ, env.HasType U Γ A (.sort (.succ .zero))) :
    env.IsDefEq U Γ (.forallE nat (.forallE A A))
      (.forallE nat (.forallE (.app (motive A) (.bvar 0)) (.app (motive A) (.app succ (.bvar 1)))))
      (.sort (.imax (.succ .zero) (.imax (.succ .zero) (.succ .zero)))) :=
  .forallEDF N.natT <| .forallEDF (motive_app hI hA (.bvar .zero)).symm <|
    (motive_app hI hA (.app' N.succT (.bvar (.succ .zero)) rfl)).symm

theorem HasNat.natRecHeadT (H : HasNat env) (hI : Inert A)
    (hA : ∀ Γ, env.HasType U Γ A (.sort (.succ .zero)))
    (hz : env.HasType U Γ z A) (hs : env.HasType U Γ s (.forallE nat (.forallE A A))) :
    env.HasType U Γ (.appN (.const ``Nat.rec [.succ .zero]) [motive A, z, s])
      (.forallE nat (.app (motive A) (.bvar 0))) := by
  have N := H.toNatConsts
  have hM : env.HasType U Γ (motive A) (.forallE nat (.sort (.succ .zero))) :=
    .lam N.natT (hA _)
  have h0 : env.HasType U Γ (.const ``Nat.rec [.succ .zero]) (recTy.instL [.succ .zero]) :=
    .const H.hRec (by simp [VLevel.WF]) rfl
  have h1 := HasType.app h0 hM
  have hz' : env.HasType U Γ z (.app (motive A) zero) := (motive_app hI hA N.zeroT).defeq' hz
  have e1 : (VExpr.instL [.succ .zero] (.forallE zeroTy (.forallE succTy
      (.forallE nat (.app (.bvar 3) (.bvar 0)))))).inst (motive A) =
      .forallE (.app (motive A) zero) (.forallE
        (.forallE nat (.forallE (.app (motive A) (.bvar 0))
          (.app (motive A) (.app succ (.bvar 1)))))
        (.forallE nat (.app (motive A) (.bvar 0)))) := by
    simp [zeroTy, succTy, VExpr.instL, VExpr.inst, instVar, (Inert.motive hI).liftN]
  rw [e1] at h1
  have h2 := HasType.app h1 hz'
  simp only [VExpr.inst, (Inert.motive hI).inst] at h2
  have h3 := HasType.app h2 ((succMinor_conv N hI hA).defeq hs)
  simp only [VExpr.inst, (Inert.motive hI).inst] at h3
  exact h3

theorem HasNat.natRec_congr (H : HasNat env) (hI : Inert A)
    (hA : ∀ Γ, env.HasType U Γ A (.sort (.succ .zero)))
    (hz : env.HasType U Γ z A) (hs : env.HasType U Γ s (.forallE nat (.forallE A A)))
    (hn : env.IsDefEq U Γ n n' nat) :
    env.IsDefEq U Γ (natRec A z s n) (natRec A z s n') A := by
  have h4 := IsDefEq.appDF (H.natRecHeadT hI hA hz hs) hn
  simp [VExpr.inst, instVar, (Inert.motive hI).inst] at h4
  exact .defeqDF (motive_app hI hA hn.hasType.1) h4

theorem HasNat.natRecT (H : HasNat env) (hI : Inert A)
    (hA : ∀ Γ, env.HasType U Γ A (.sort (.succ .zero)))
    (hz : env.HasType U Γ z A) (hs : env.HasType U Γ s (.forallE nat (.forallE A A)))
    (hn : env.HasType U Γ n nat) : env.HasType U Γ (natRec A z s n) A :=
  H.natRec_congr hI hA hz hs hn

def motiveTy1 : VExpr := .forallE nat (.sort (.succ .zero))

/-- The arguments `motive A, z, s` for the binders of `Nat.rec.{1}`. -/
theorem HasNat.recArgs (H : HasNat env) (hI : Inert A)
    (hA : ∀ Γ, env.HasType 0 Γ A (.sort (.succ .zero)))
    (hz : env.HasType 0 [] z A) (hs : env.HasType 0 [] s (.forallE nat (.forallE A A))) :
    Ctx.SubstEq env 0 [] (Subst.id.consList [motive A, z, s]) (Subst.id.consList [motive A, z, s])
      [succTy, zeroTy, motiveTy1] := by
  have N := H.toNatConsts
  have := H.hNat; have := H.hZero; have := H.hSucc
  obtain ⟨_, t1⟩ : env.IsType 0 [] motiveTy1 := ⟨_, by unfold motiveTy1; type_tac⟩
  obtain ⟨_, t2⟩ : env.IsType 0 [motiveTy1] zeroTy := ⟨_, by unfold zeroTy motiveTy1; type_tac⟩
  obtain ⟨_, t3⟩ : env.IsType 0 [zeroTy, motiveTy1] succTy :=
    ⟨_, by unfold succTy zeroTy motiveTy1; type_tac⟩
  refine .cons (.cons (.cons .nil t1 ?_) t2 ?_) t3 ?_
  · exact HasType.lam N.natT (hA _)
  · exact (motive_app hI hA N.zeroT).defeq' hz
  · have := (succMinor_conv N hI hA).defeq hs
    show env.HasType 0 [] s _
    simpa [succTy, Subst.consList, Subst.cons, Subst.tail, VExpr.subst, Subst.lift, Subst.id,
      (Inert.motive hI).liftN, VExpr.liftN] using this

theorem HasNat.recTele (H : HasNat env) : env.IsTele 0 [] [motiveTy1, zeroTy, succTy] := by
  have := H.hNat; have := H.hZero; have := H.hSucc
  obtain ⟨_, t1⟩ : env.IsType 0 [] motiveTy1 := ⟨_, by unfold motiveTy1; type_tac⟩
  obtain ⟨_, t2⟩ : env.IsType 0 [motiveTy1] zeroTy := ⟨_, by unfold zeroTy motiveTy1; type_tac⟩
  obtain ⟨_, t3⟩ : env.IsType 0 [zeroTy, motiveTy1] succTy :=
    ⟨_, by unfold succTy zeroTy motiveTy1; type_tac⟩
  exact .cons ⟨_, t1⟩ (.cons ⟨_, t2⟩ (.cons ⟨_, t3⟩ .nil))

/-- `Nat.rec (fun _ => A) z s Nat.zero ≡ z`. -/
theorem HasNat.iota_zero (H : HasNat env) (henv : env.Ordered) (hI : Inert A)
    (hA : ∀ Γ, env.HasType 0 Γ A (.sort (.succ .zero)))
    (hz : env.HasType 0 [] z A) (hs : env.HasType 0 [] s (.forallE nat (.forallE A A))) :
    env.IsDefEq 0 [] (natRec A z s zero) z A := by
  have := H.hNat; have := H.hZero; have := H.hSucc; have := H.hRec
  have hx : env.IsDefEq 0 []
      ((VExpr.lams [motiveTy1, zeroTy, succTy]
        (.appN (.const ``Nat.rec [.succ .zero]) [.bvar 2, .bvar 1, .bvar 0, zero])).subst .id)
      (.lams [motiveTy1, zeroTy, succTy] (.bvar 1))
      ((VExpr.foralls [motiveTy1, zeroTy, succTy] (.app (.bvar 2) zero)).subst .id) := by
    rw [subst_id, subst_id]
    exact IsDefEq.extra H.hIotaZero (ls := [.succ .zero]) (by simp [VLevel.WF]) rfl
  have W := H.recArgs hI hA hz hs
  have hL : env.HasType 0 ([motiveTy1, zeroTy, succTy].reverse ++ [])
      (.appN (.const ``Nat.rec [.succ .zero]) [.bvar 2, .bvar 1, .bvar 0, zero])
      (.app (.bvar 2) zero) := by
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
      VExpr.appN]
    unfold succTy zeroTy motiveTy1; type_tac
  have hR : env.HasType 0 ([motiveTy1, zeroTy, succTy].reverse ++ []) (.bvar 1)
      (.app (.bvar 2) zero) := by
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
    unfold succTy zeroTy motiveTy1; type_tac
  have h1 := IsDefEq.appN_substT (Δ := []) (as := [motive A, z, s]) hx rfl W
  have h2 := IsDefEq.lams_beta henv (Γ₀ := []) trivial (Δ := []) (as := [motive A, z, s])
    .nil H.recTele hL rfl W
  have h3 := IsDefEq.lams_beta henv (Γ₀ := []) trivial (Δ := []) (as := [motive A, z, s])
    .nil H.recTele hR rfl W
  rw [subst_id] at h1 h2 h3
  have h := h2.symm.trans (h1.trans h3)
  simp [VExpr.subst, Subst.consList, Subst.cons, Subst.id] at h
  exact .defeqDF (motive_app hI hA H.zeroT) h

/-- `Nat.rec (fun _ => A) z s (Nat.succ n) ≡ s n (Nat.rec (fun _ => A) z s n)`. -/
theorem HasNat.iota_succ (H : HasNat env) (henv : env.Ordered) (hI : Inert A)
    (hA : ∀ Γ, env.HasType 0 Γ A (.sort (.succ .zero)))
    (hz : env.HasType 0 [] z A) (hs : env.HasType 0 [] s (.forallE nat (.forallE A A)))
    (hn : env.HasType 0 [] n nat) :
    env.IsDefEq 0 [] (natRec A z s (.app succ n)) (.app (.app s n) (natRec A z s n)) A := by
  have := H.hNat; have := H.hZero; have := H.hSucc; have := H.hRec
  have hx : env.IsDefEq 0 []
      ((VExpr.lams [motiveTy1, zeroTy, succTy, nat]
        (.appN (.const ``Nat.rec [.succ .zero]) [.bvar 3, .bvar 2, .bvar 1, .app succ (.bvar 0)])).subst .id)
      (.lams [motiveTy1, zeroTy, succTy, nat]
        (.appN (.bvar 1) [.bvar 0, .appN (.const ``Nat.rec [.succ .zero]) [.bvar 3, .bvar 2, .bvar 1, .bvar 0]]))
      ((VExpr.foralls [motiveTy1, zeroTy, succTy, nat] (.app (.bvar 3) (.app succ (.bvar 0)))).subst .id) := by
    rw [subst_id, subst_id]
    exact IsDefEq.extra H.hIotaSucc (ls := [.succ .zero]) (by simp [VLevel.WF]) rfl
  have W : Ctx.SubstEq env 0 [] (Subst.id.consList [motive A, z, s, n])
      (Subst.id.consList [motive A, z, s, n]) ([motiveTy1, zeroTy, succTy, nat].reverse ++ []) :=
    .cons (H.recArgs hI hA hz hs) H.natT hn
  have tele : env.IsTele 0 [] [motiveTy1, zeroTy, succTy, nat] := by
    obtain ⟨_, t1⟩ : env.IsType 0 [] motiveTy1 := ⟨_, by unfold motiveTy1; type_tac⟩
    obtain ⟨_, t2⟩ : env.IsType 0 [motiveTy1] zeroTy := ⟨_, by unfold zeroTy motiveTy1; type_tac⟩
    obtain ⟨_, t3⟩ : env.IsType 0 [zeroTy, motiveTy1] succTy :=
      ⟨_, by unfold succTy zeroTy motiveTy1; type_tac⟩
    exact .cons ⟨_, t1⟩ (.cons ⟨_, t2⟩ (.cons ⟨_, t3⟩ (.cons ⟨_, H.natT⟩ .nil)))
  have hL : env.HasType 0 ([motiveTy1, zeroTy, succTy, nat].reverse ++ [])
      (.appN (.const ``Nat.rec [.succ .zero]) [.bvar 3, .bvar 2, .bvar 1, .app succ (.bvar 0)])
      (.app (.bvar 3) (.app succ (.bvar 0))) := by
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
      VExpr.appN]
    unfold succTy zeroTy motiveTy1; type_tac
  have hR : env.HasType 0 ([motiveTy1, zeroTy, succTy, nat].reverse ++ [])
      (.appN (.bvar 1) [.bvar 0, .appN (.const ``Nat.rec [.succ .zero]) [.bvar 3, .bvar 2, .bvar 1, .bvar 0]])
      (.app (.bvar 3) (.app succ (.bvar 0))) := by
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
      VExpr.appN]
    unfold succTy zeroTy motiveTy1; type_tac
  have h1 := IsDefEq.appN_substT (Δ := []) (as := [motive A, z, s, n]) hx rfl W
  have h2 := IsDefEq.lams_beta henv (Γ₀ := []) trivial (Δ := []) (as := [motive A, z, s, n])
    .nil tele hL rfl W
  have h3 := IsDefEq.lams_beta henv (Γ₀ := []) trivial (Δ := []) (as := [motive A, z, s, n])
    .nil tele hR rfl W
  rw [subst_id] at h1 h2 h3
  have h := h2.symm.trans (h1.trans h3)
  simp [VExpr.subst, Subst.consList, Subst.cons, Subst.id] at h
  exact .defeqDF (motive_app hI hA (.app' H.succT hn rfl)) h

end

end Incomplete
