import Incomplete.Bounded

/-!
# `Nat.rec` at a constant motive, in the fragment

The lemmas of `Arith.lean` for `BDefEq`: `natRec A z s n` is typed and computes on numerals by
the iota rules. The iota rules are stated over binders whose types live in `Type 1`, so they are
reduced here by one beta step per argument, never typing those binders.
-/

namespace Incomplete
open Lean4Lean
open VExpr VEnv

section
variable {env : VEnv} {Γ : List VExpr}

theorem NatConsts.bnatT (H : NatConsts env) : BDefEq env Γ nat nat (.sort (.succ .zero)) :=
  .const' H.hNat (by simp) rfl (by simp) rfl

theorem NatConsts.bzeroT (H : NatConsts env) : BDefEq env Γ zero zero nat :=
  .const' H.hZero (by simp) rfl (by simp) rfl

theorem NatConsts.bsuccT (H : NatConsts env) : BDefEq env Γ succ succ (.forallE nat nat) :=
  .const' H.hSucc (by simp) rfl (by simp) rfl

theorem NatConsts.blitT (H : NatConsts env) : ∀ n, BDefEq env Γ (lit n) (lit n) nat
  | 0 => H.bzeroT
  | n + 1 => .app' H.bsuccT (H.blitT n) rfl

theorem bmotive_app {A n : VExpr} (hI : Inert A)
    (hA : ∀ Γ, BDefEq env Γ A A (.sort (.succ .zero))) (hn : BDefEq env Γ n n nat) :
    BDefEq env Γ (.app (motive A) n) A (.sort (.succ .zero)) := by
  have := BDefEq.beta (hA (nat :: Γ)) hn
  rwa [hI.inst] at this

theorem bsuccMinor_conv {A : VExpr} (N : NatConsts env) (hI : Inert A)
    (hA : ∀ Γ, BDefEq env Γ A A (.sort (.succ .zero))) :
    BDefEq env Γ (.forallE nat (.forallE A A))
      (.forallE nat (.forallE (.app (motive A) (.bvar 0)) (.app (motive A) (.app succ (.bvar 1)))))
      (.sort (.imax (.succ .zero) (.imax (.succ .zero) (.succ .zero)))) :=
  .forallEDF N.bnatT (.forallEDF (bmotive_app hI hA (.bvar .zero)).symm
    (bmotive_app hI hA (.app' N.bsuccT (.bvar (.succ .zero)) rfl)).symm (by decide) (by decide)
    (by decide) (by decide)) (by decide) (by decide) (by decide) (by decide)

theorem HasNat.bnatRecHeadT {A z s : VExpr} (H : HasNat env) (hI : Inert A)
    (hA : ∀ Γ, BDefEq env Γ A A (.sort (.succ .zero)))
    (hz : BDefEq env Γ z z A) (hs : BDefEq env Γ s s (.forallE nat (.forallE A A))) :
    BDefEq env Γ (.appN (.const ``Nat.rec [.succ .zero]) [motive A, z, s])
      (.appN (.const ``Nat.rec [.succ .zero]) [motive A, z, s])
      (.forallE nat (.app (motive A) (.bvar 0))) := by
  have N := H.toNatConsts
  have hM : BDefEq env Γ (motive A) (motive A) (.forallE nat (.sort (.succ .zero))) :=
    .lamDF N.bnatT (hA _)
  have h0 : BDefEq env Γ (.const ``Nat.rec [.succ .zero]) (.const ``Nat.rec [.succ .zero])
      (recTy.instL [.succ .zero]) :=
    .const' H.hRec (by simp [VLevel.WF]) rfl (by simp [VLevel.eval]) rfl
  have h1 := BDefEq.appDF h0 hM
  have hz' : BDefEq env Γ z z (.app (motive A) zero) := (bmotive_app hI hA N.bzeroT).defeq' hz
  have e1 : (VExpr.instL [.succ .zero] (.forallE zeroTy (.forallE succTy
      (.forallE nat (.app (.bvar 3) (.bvar 0)))))).inst (motive A) =
      .forallE (.app (motive A) zero) (.forallE
        (.forallE nat (.forallE (.app (motive A) (.bvar 0))
          (.app (motive A) (.app succ (.bvar 1)))))
        (.forallE nat (.app (motive A) (.bvar 0)))) := by
    simp [zeroTy, succTy, VExpr.instL, VExpr.inst, instVar, (Inert.motive hI).liftN]
  rw [e1] at h1
  have h2 := BDefEq.appDF h1 hz'
  simp only [VExpr.inst, (Inert.motive hI).inst] at h2
  have h3 := BDefEq.appDF h2 ((bsuccMinor_conv N hI hA).defeq hs)
  simp only [VExpr.inst, (Inert.motive hI).inst] at h3
  exact h3

theorem HasNat.bnatRec_congr {A z s n n' : VExpr} (H : HasNat env) (hI : Inert A)
    (hA : ∀ Γ, BDefEq env Γ A A (.sort (.succ .zero)))
    (hz : BDefEq env Γ z z A) (hs : BDefEq env Γ s s (.forallE nat (.forallE A A)))
    (hnT : BDefEq env Γ n n nat) (hn : BDefEq env Γ n n' nat) :
    BDefEq env Γ (natRec A z s n) (natRec A z s n') A := by
  have h4 := BDefEq.appDF (H.bnatRecHeadT hI hA hz hs) hn
  simp [VExpr.inst, instVar, (Inert.motive hI).inst] at h4
  exact .defeqDF (bmotive_app hI hA hnT) h4

theorem HasNat.bnatRecT {A z s n : VExpr} (H : HasNat env) (hI : Inert A)
    (hA : ∀ Γ, BDefEq env Γ A A (.sort (.succ .zero)))
    (hz : BDefEq env Γ z z A) (hs : BDefEq env Γ s s (.forallE nat (.forallE A A)))
    (hn : BDefEq env Γ n n nat) : BDefEq env Γ (natRec A z s n) (natRec A z s n) A :=
  H.bnatRec_congr hI hA hz hs hn hn

/-- One argument of a beta redex reached by conversion. -/
theorem bbeta_step {f A e B a : VExpr} (hf : BDefEq env Γ f (.lam A e) (.forallE A B))
    (he : BDefEq env (A::Γ) e e B) (ha : BDefEq env Γ a a A) :
    BDefEq env Γ (.app f a) (e.inst a) (B.inst a) :=
  (BDefEq.appDF hf ha).trans (.beta he ha)

end

section
variable {env : VEnv} (H : HasNat env) (henv : env.Ordered)
include H henv

def bzBody : VExpr := .appN (.const ``Nat.rec [.succ .zero]) [.bvar 2, .bvar 1, .bvar 0, zero]

/-- `Nat.rec (fun _ => A) z s Nat.zero ≡ z`. -/
theorem HasNat.biota_zero {A z s : VExpr} (hI : Inert A)
    (hA : ∀ Γ, BDefEq env Γ A A (.sort (.succ .zero)))
    (hz : BDefEq env [] z z A) (hs : BDefEq env [] s s (.forallE nat (.forallE A A))) :
    BDefEq env [] (natRec A z s zero) z A := by
  have N := H.toNatConsts
  have := H.hNat; have := H.hZero; have := H.hSucc; have := H.hRec
  have hzc : z.ClosedN := hz.toIsDefEq.closedN henv trivial
  have hsc : s.ClosedN := hs.toIsDefEq.closedN henv trivial
  have hmI := Inert.motive hI
  have E : BDefEq env [] (.lam motiveTy1 (.lam zeroTy (.lam succTy bzBody)))
      (.lam motiveTy1 (.lam zeroTy (.lam succTy (.bvar 1))))
      (.forallE motiveTy1 (.forallE zeroTy (.forallE succTy (.app (.bvar 2) zero)))) :=
    BDefEq.extra H.hIotaZero (ls := [.succ .zero]) (by simp [VLevel.WF]) rfl
      (by simp [VLevel.eval])
  have tL3 : BDefEq env [succTy, zeroTy, motiveTy1] bzBody bzBody (.app (.bvar 2) zero) := by
    unfold bzBody succTy zeroTy motiveTy1; btype_tac
  have tL2 : BDefEq env [zeroTy, motiveTy1] (.lam succTy bzBody) (.lam succTy bzBody)
      (.forallE succTy (.app (.bvar 2) zero)) := by
    unfold bzBody succTy zeroTy motiveTy1; btype_tac
  have tL1 : BDefEq env [motiveTy1] (.lam zeroTy (.lam succTy bzBody))
      (.lam zeroTy (.lam succTy bzBody))
      (.forallE zeroTy (.forallE succTy (.app (.bvar 2) zero))) := by
    unfold bzBody succTy zeroTy motiveTy1; btype_tac
  have tR3 : BDefEq env [succTy, zeroTy, motiveTy1] (.bvar 1) (.bvar 1) (.app (.bvar 2) zero) := by
    unfold succTy zeroTy motiveTy1; btype_tac
  have tR2 : BDefEq env [zeroTy, motiveTy1] (.lam succTy (.bvar 1)) (.lam succTy (.bvar 1))
      (.forallE succTy (.app (.bvar 2) zero)) := by
    unfold succTy zeroTy motiveTy1; btype_tac
  have tR1 : BDefEq env [motiveTy1] (.lam zeroTy (.lam succTy (.bvar 1)))
      (.lam zeroTy (.lam succTy (.bvar 1)))
      (.forallE zeroTy (.forallE succTy (.app (.bvar 2) zero))) := by
    unfold succTy zeroTy motiveTy1; btype_tac
  have hm : BDefEq env [] (motive A) (motive A) motiveTy1 := .lamDF N.bnatT (hA _)
  have ez : zeroTy.inst (motive A) = .app (motive A) zero := by
    simp [zeroTy, VExpr.inst]
  have hz' : BDefEq env [] z z (zeroTy.inst (motive A)) := by
    rw [ez]; exact (bmotive_app hI hA N.bzeroT).defeq' hz
  have es : (succTy.inst (motive A) 1).inst z = .forallE nat (.forallE (.app (motive A) (.bvar 0))
      (.app (motive A) (.app succ (.bvar 1)))) := by
    simp [succTy, VExpr.inst, instVar, hmI.liftN, hmI.inst]
  have hs' : BDefEq env [] s s ((succTy.inst (motive A) 1).inst z) := by
    rw [es]; exact (bsuccMinor_conv N hI hA).defeq hs
  have W1 : Ctx.InstN [] (motive A) motiveTy1 1 [zeroTy, motiveTy1] [zeroTy.inst (motive A)] := .succ .zero
  have W2 : Ctx.InstN [] (motive A) motiveTy1 2 [succTy, zeroTy, motiveTy1]
      [succTy.inst (motive A) 1, zeroTy.inst (motive A)] := .succ (.succ .zero)
  have W2' : Ctx.InstN [] z (zeroTy.inst (motive A)) 1 [succTy.inst (motive A) 1, zeroTy.inst (motive A)]
      [(succTy.inst (motive A) 1).inst z] := .succ .zero
  have l1 := bbeta_step (E.trans E.symm) tL1 hm
  have l2 := bbeta_step l1 (BDefEq.instN henv hm W1 tL2) hz'
  have l3 := bbeta_step l2 (BDefEq.instN henv hz' W2' (BDefEq.instN henv hm W2 tL3)) hs'
  have r1 := bbeta_step (E.symm.trans E) tR1 hm
  have r2 := bbeta_step r1 (BDefEq.instN henv hm W1 tR2) hz'
  have r3 := bbeta_step r2 (BDefEq.instN henv hz' W2' (BDefEq.instN henv hm W2 tR3)) hs'
  have e3 := BDefEq.appDF (BDefEq.appDF (BDefEq.appDF E hm) hz') hs'
  have h := l3.symm.trans (e3.trans r3)
  simp [bzBody, VExpr.appN, VExpr.inst, instVar, hmI.liftN, hzc.liftN_eq (Nat.zero_le _),
    hsc.liftN_eq (Nat.zero_le _), hmI.inst, hzc.instN_eq (Nat.zero_le _)] at h
  exact .defeqDF (bmotive_app hI hA N.bzeroT) h

def bsBodyL : VExpr :=
  .appN (.const ``Nat.rec [.succ .zero]) [.bvar 3, .bvar 2, .bvar 1, .app succ (.bvar 0)]
def bsBodyR : VExpr :=
  .appN (.bvar 1) [.bvar 0, .appN (.const ``Nat.rec [.succ .zero]) [.bvar 3, .bvar 2, .bvar 1, .bvar 0]]

/-- `Nat.rec (fun _ => A) z s (Nat.succ n) ≡ s n (Nat.rec (fun _ => A) z s n)`. -/
theorem HasNat.biota_succ {A z s n : VExpr} (hI : Inert A)
    (hA : ∀ Γ, BDefEq env Γ A A (.sort (.succ .zero)))
    (hz : BDefEq env [] z z A) (hs : BDefEq env [] s s (.forallE nat (.forallE A A)))
    (hn : BDefEq env [] n n nat) :
    BDefEq env [] (natRec A z s (.app succ n)) (.app (.app s n) (natRec A z s n)) A := by
  have N := H.toNatConsts
  have := H.hNat; have := H.hZero; have := H.hSucc; have := H.hRec
  have hzc : z.ClosedN := hz.toIsDefEq.closedN henv trivial
  have hsc : s.ClosedN := hs.toIsDefEq.closedN henv trivial
  have hnc : n.ClosedN := hn.toIsDefEq.closedN henv trivial
  have hmI := Inert.motive hI
  have E : BDefEq env [] (.lam motiveTy1 (.lam zeroTy (.lam succTy (.lam nat bsBodyL))))
      (.lam motiveTy1 (.lam zeroTy (.lam succTy (.lam nat bsBodyR))))
      (.forallE motiveTy1 (.forallE zeroTy (.forallE succTy (.forallE nat
        (.app (.bvar 3) (.app succ (.bvar 0))))))) :=
    BDefEq.extra H.hIotaSucc (ls := [.succ .zero]) (by simp [VLevel.WF]) rfl
      (by simp [VLevel.eval])
  have tL4 : BDefEq env [nat, succTy, zeroTy, motiveTy1] bsBodyL bsBodyL
      (.app (.bvar 3) (.app succ (.bvar 0))) := by
    unfold bsBodyL succTy zeroTy motiveTy1; btype_tac
  have tL3 : BDefEq env [succTy, zeroTy, motiveTy1] (.lam nat bsBodyL) (.lam nat bsBodyL)
      (.forallE nat (.app (.bvar 3) (.app succ (.bvar 0)))) := by
    unfold bsBodyL succTy zeroTy motiveTy1; btype_tac
  have tL2 : BDefEq env [zeroTy, motiveTy1] (.lam succTy (.lam nat bsBodyL))
      (.lam succTy (.lam nat bsBodyL))
      (.forallE succTy (.forallE nat (.app (.bvar 3) (.app succ (.bvar 0))))) := by
    unfold bsBodyL succTy zeroTy motiveTy1; btype_tac
  have tL1 : BDefEq env [motiveTy1] (.lam zeroTy (.lam succTy (.lam nat bsBodyL)))
      (.lam zeroTy (.lam succTy (.lam nat bsBodyL)))
      (.forallE zeroTy (.forallE succTy (.forallE nat (.app (.bvar 3) (.app succ (.bvar 0)))))) := by
    unfold bsBodyL succTy zeroTy motiveTy1; btype_tac
  have tR4 : BDefEq env [nat, succTy, zeroTy, motiveTy1] bsBodyR bsBodyR
      (.app (.bvar 3) (.app succ (.bvar 0))) := by
    unfold bsBodyR succTy zeroTy motiveTy1; btype_tac
  have tR3 : BDefEq env [succTy, zeroTy, motiveTy1] (.lam nat bsBodyR) (.lam nat bsBodyR)
      (.forallE nat (.app (.bvar 3) (.app succ (.bvar 0)))) := by
    unfold bsBodyR succTy zeroTy motiveTy1; btype_tac
  have tR2 : BDefEq env [zeroTy, motiveTy1] (.lam succTy (.lam nat bsBodyR))
      (.lam succTy (.lam nat bsBodyR))
      (.forallE succTy (.forallE nat (.app (.bvar 3) (.app succ (.bvar 0))))) := by
    unfold bsBodyR succTy zeroTy motiveTy1; btype_tac
  have tR1 : BDefEq env [motiveTy1] (.lam zeroTy (.lam succTy (.lam nat bsBodyR)))
      (.lam zeroTy (.lam succTy (.lam nat bsBodyR)))
      (.forallE zeroTy (.forallE succTy (.forallE nat (.app (.bvar 3) (.app succ (.bvar 0)))))) := by
    unfold bsBodyR succTy zeroTy motiveTy1; btype_tac
  have hm : BDefEq env [] (motive A) (motive A) motiveTy1 := .lamDF N.bnatT (hA _)
  have ez : zeroTy.inst (motive A) = .app (motive A) zero := by simp [zeroTy, VExpr.inst]
  have hz' : BDefEq env [] z z (zeroTy.inst (motive A)) := by
    rw [ez]; exact (bmotive_app hI hA N.bzeroT).defeq' hz
  have es : (succTy.inst (motive A) 1).inst z = .forallE nat (.forallE (.app (motive A) (.bvar 0))
      (.app (motive A) (.app succ (.bvar 1)))) := by
    simp [succTy, VExpr.inst, instVar, hmI.liftN, hmI.inst]
  have hs' : BDefEq env [] s s ((succTy.inst (motive A) 1).inst z) := by
    rw [es]; exact (bsuccMinor_conv N hI hA).defeq hs
  have en : ((nat.inst (motive A) 2).inst z 1).inst s = nat := rfl
  have hn' : BDefEq env [] n n (((nat.inst (motive A) 2).inst z 1).inst s) := by rw [en]; exact hn
  have W1 : Ctx.InstN [] (motive A) motiveTy1 1 [zeroTy, motiveTy1] [zeroTy.inst (motive A)] :=
    .succ .zero
  have W2 : Ctx.InstN [] (motive A) motiveTy1 2 [succTy, zeroTy, motiveTy1]
      [succTy.inst (motive A) 1, zeroTy.inst (motive A)] := .succ (.succ .zero)
  have W2' : Ctx.InstN [] z (zeroTy.inst (motive A)) 1 [succTy.inst (motive A) 1, zeroTy.inst (motive A)]
      [(succTy.inst (motive A) 1).inst z] := .succ .zero
  have W3 : Ctx.InstN [] (motive A) motiveTy1 3 [nat, succTy, zeroTy, motiveTy1]
      [nat.inst (motive A) 2, succTy.inst (motive A) 1, zeroTy.inst (motive A)] :=
    .succ (.succ (.succ .zero))
  have W3' : Ctx.InstN [] z (zeroTy.inst (motive A)) 2
      [nat.inst (motive A) 2, succTy.inst (motive A) 1, zeroTy.inst (motive A)]
      [(nat.inst (motive A) 2).inst z 1, (succTy.inst (motive A) 1).inst z] := .succ (.succ .zero)
  have W3'' : Ctx.InstN [] s ((succTy.inst (motive A) 1).inst z) 1
      [(nat.inst (motive A) 2).inst z 1, (succTy.inst (motive A) 1).inst z]
      [((nat.inst (motive A) 2).inst z 1).inst s] := .succ .zero
  have l1 := bbeta_step (E.trans E.symm) tL1 hm
  have l2 := bbeta_step l1 (BDefEq.instN henv hm W1 tL2) hz'
  have l3 := bbeta_step l2 (BDefEq.instN henv hz' W2' (BDefEq.instN henv hm W2 tL3)) hs'
  have l4 := bbeta_step l3 (BDefEq.instN henv hs' W3''
    (BDefEq.instN henv hz' W3' (BDefEq.instN henv hm W3 tL4))) hn'
  have r1 := bbeta_step (E.symm.trans E) tR1 hm
  have r2 := bbeta_step r1 (BDefEq.instN henv hm W1 tR2) hz'
  have r3 := bbeta_step r2 (BDefEq.instN henv hz' W2' (BDefEq.instN henv hm W2 tR3)) hs'
  have r4 := bbeta_step r3 (BDefEq.instN henv hs' W3''
    (BDefEq.instN henv hz' W3' (BDefEq.instN henv hm W3 tR4))) hn'
  have e4 := BDefEq.appDF (BDefEq.appDF (BDefEq.appDF (BDefEq.appDF E hm) hz') hs') hn'
  have h := l4.symm.trans (e4.trans r4)
  simp [bsBodyL, bsBodyR, VExpr.appN, VExpr.inst, instVar, hmI.liftN,
    hzc.liftN_eq (Nat.zero_le _), hsc.liftN_eq (Nat.zero_le _), hnc.liftN_eq (Nat.zero_le _),
    hmI.inst, hzc.instN_eq (Nat.zero_le _), hsc.instN_eq (Nat.zero_le _)] at h
  exact .defeqDF (bmotive_app hI hA (.app' N.bsuccT hn rfl)) h

end

end Incomplete
