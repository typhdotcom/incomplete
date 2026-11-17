import Incomplete.CertNat
import Lean4Lean.Theory.Typing.Meta

/-!
# The fragment with sorts `Prop` and `Type`

`BDefEq env Γ e₁ e₂ A` is `VEnv.IsDefEq env 0 Γ e₁ e₂ A` without the projection rules, where the
sorts a derivation forms or quantifies over denote at most `1`: `sortDF` only at `Prop`,
`forallEDF` only over and into `Prop` and `Type`, and the universe arguments of constants and
of the rules of `env` at most `1`. Every judgment it derives is one of `VEnv.IsDefEq env 0`.

On certificates the fragment is `Cert.leafOK`: a checked certificate whose leaves keep these
bounds and that uses no projection rule derives a `BDefEq` judgment, and every `BDefEq`
judgment has one.
-/

namespace Lean4Lean.Incomplete
open VExpr VEnv

inductive BDefEq (env : VEnv) : List VExpr → VExpr → VExpr → VExpr → Prop where
  | bvar : Lookup Γ i A → BDefEq env Γ (.bvar i) (.bvar i) A
  | symm : BDefEq env Γ e e' A → BDefEq env Γ e' e A
  | trans : BDefEq env Γ e₁ e₂ A → BDefEq env Γ e₂ e₃ A → BDefEq env Γ e₁ e₃ A
  | sortDF : l.WF 0 → l'.WF 0 → l ≈ l' → l.eval [] = 0 →
    BDefEq env Γ (.sort l) (.sort l') (.sort (.succ l))
  | constDF : env.constants c = some ci → (∀ l ∈ ls, l.WF 0) → (∀ l ∈ ls', l.WF 0) →
    ls.length = ci.uvars → List.Forall₂ (· ≈ ·) ls ls' → (∀ l ∈ ls, l.eval [] ≤ 1) →
    BDefEq env Γ (.const c ls) (.const c ls') (ci.type.instL ls)
  | appDF : BDefEq env Γ f f' (.forallE A B) → BDefEq env Γ a a' A →
    BDefEq env Γ (.app f a) (.app f' a') (B.inst a)
  | lamDF : BDefEq env Γ A A' (.sort u) → BDefEq env (A::Γ) body body' B →
    BDefEq env Γ (.lam A body) (.lam A' body') (.forallE A B)
  | forallEDF : BDefEq env Γ A A' (.sort u) → BDefEq env (A::Γ) body body' (.sort v) →
    u.WF 0 → v.WF 0 → u.eval [] ≤ 1 → v.eval [] ≤ 1 →
    BDefEq env Γ (.forallE A body) (.forallE A' body') (.sort (.imax u v))
  | defeqDF : BDefEq env Γ A B (.sort u) → BDefEq env Γ e1 e2 A → BDefEq env Γ e1 e2 B
  | beta : BDefEq env (A::Γ) e e B → BDefEq env Γ e' e' A →
    BDefEq env Γ (.app (.lam A e) e') (e.inst e') (B.inst e')
  | eta : BDefEq env Γ e e (.forallE A B) →
    BDefEq env Γ (.lam A (.app e.lift (.bvar 0))) e (.forallE A B)
  | proofIrrel : BDefEq env Γ p p (.sort .zero) → BDefEq env Γ h h p → BDefEq env Γ h' h' p →
    BDefEq env Γ h h' p
  | extra : env.defeqs df → (∀ l ∈ ls, l.WF 0) → ls.length = df.uvars →
    (∀ l ∈ ls, l.eval [] ≤ 1) →
    BDefEq env Γ (df.lhs.instL ls) (df.rhs.instL ls) (df.type.instL ls)

/-- Provability in the fragment: a closed term of the proposition. -/
def BProvable (env : VEnv) (P : VExpr) : Prop := ∃ e, BDefEq env [] e e P

theorem BDefEq.toIsDefEq {env : VEnv} {Γ e₁ e₂ A} (H : BDefEq env Γ e₁ e₂ A) :
    env.IsDefEq 0 Γ e₁ e₂ A := by
  induction H with
  | bvar h => exact .bvar h
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | sortDF h1 h2 h3 => exact .sortDF h1 h2 h3
  | constDF h1 h2 h3 h4 h5 => exact .constDF h1 h2 h3 h4 h5
  | appDF _ _ ih₁ ih₂ => exact .appDF ih₁ ih₂
  | lamDF _ _ ih₁ ih₂ => exact .lamDF ih₁ ih₂
  | forallEDF _ _ _ _ _ _ ih₁ ih₂ => exact .forallEDF ih₁ ih₂
  | defeqDF _ _ ih₁ ih₂ => exact .defeqDF ih₁ ih₂
  | beta _ _ ih₁ ih₂ => exact .beta ih₁ ih₂
  | eta _ ih => exact .eta ih
  | proofIrrel _ _ _ ih₁ ih₂ ih₃ => exact .proofIrrel ih₁ ih₂ ih₃
  | extra h1 h2 h3 => exact .extra h1 h2 h3

theorem BProvable.provable {env : VEnv} {P : VExpr} : BProvable env P → Provable env P
  | ⟨e, h⟩ => ⟨e, h.toIsDefEq⟩

/-! ### Weakening and instantiation -/

section
variable {env : VEnv} (henv : env.Ordered)
include henv

theorem BDefEq.weakN {n k Γ Γ'} (W : Ctx.LiftN n k Γ Γ') {e1 e2 A}
    (H : BDefEq env Γ e1 e2 A) : BDefEq env Γ' (e1.liftN n k) (e2.liftN n k) (A.liftN n k) := by
  induction H generalizing k Γ' with
  | bvar h => exact .bvar (h.weakN W)
  | symm _ ih => exact .symm (ih W)
  | trans _ _ ih1 ih2 => exact .trans (ih1 W) (ih2 W)
  | sortDF h1 h2 h3 h4 => exact .sortDF h1 h2 h3 h4
  | constDF h1 h2 h3 h4 h5 h6 =>
    rw [(henv.closedC h1).instL.liftN_eq (Nat.zero_le _)]
    exact .constDF h1 h2 h3 h4 h5 h6
  | appDF _ _ ih1 ih2 => exact liftN_inst_hi .. ▸ .appDF (ih1 W) (ih2 W)
  | lamDF _ _ ih1 ih2 => exact .lamDF (ih1 W) (ih2 W.succ)
  | forallEDF _ _ h1 h2 h3 h4 ih1 ih2 => exact .forallEDF (ih1 W) (ih2 W.succ) h1 h2 h3 h4
  | defeqDF _ _ ih1 ih2 => exact .defeqDF (ih1 W) (ih2 W)
  | beta _ _ ih1 ih2 =>
    exact VExpr.liftN_inst_hi .. ▸ VExpr.liftN_instN_hi .. ▸ .beta (ih1 W.succ) (ih2 W)
  | eta _ ih =>
    have := BDefEq.eta (ih W)
    simp [liftN]; rwa [← lift_liftN']
  | proofIrrel _ _ _ ih1 ih2 ih3 => exact .proofIrrel (ih1 W) (ih2 W) (ih3 W)
  | extra h1 h2 h3 h4 =>
    have ⟨⟨hA1, _⟩, hA2, hA3⟩ := henv.closed.2 h1
    rw [hA1.instL.liftN_eq (Nat.zero_le _), hA2.instL.liftN_eq (Nat.zero_le _),
      hA3.instL.liftN_eq (Nat.zero_le _)]
    exact .extra h1 h2 h3 h4

theorem BDefEq.weak {Γ e1 e2 A B} (H : BDefEq env Γ e1 e2 A) :
    BDefEq env (B::Γ) e1.lift e2.lift A.lift := H.weakN henv .one

theorem BDefEq.instN {Γ₀ e₀ A₀} (h₀ : BDefEq env Γ₀ e₀ e₀ A₀) {k Γ₁ Γ}
    (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ) {e1 e2 A} (H : BDefEq env Γ₁ e1 e2 A) :
    BDefEq env Γ (e1.inst e₀ k) (e2.inst e₀ k) (A.inst e₀ k) := by
  induction H generalizing Γ k with
  | @bvar _ i ty h =>
    dsimp [inst]
    induction W generalizing i ty with
    | zero =>
      cases h with simp [inst_lift]
      | zero => exact h₀
      | succ h => exact .bvar h
    | succ _ ih =>
      cases h with (simp; rw [Nat.add_comm, ← VExpr.liftN_instN_lo (hj := Nat.zero_le _)])
      | zero => exact .bvar .zero
      | succ h => exact (ih h).weak henv
  | symm _ ih => exact .symm (ih W)
  | trans _ _ ih1 ih2 => exact .trans (ih1 W) (ih2 W)
  | sortDF h1 h2 h3 h4 => exact .sortDF h1 h2 h3 h4
  | constDF h1 h2 h3 h4 h5 h6 =>
    rw [(henv.closedC h1).instL.instN_eq (Nat.zero_le _)]
    exact .constDF h1 h2 h3 h4 h5 h6
  | appDF _ _ ih1 ih2 => exact VExpr.inst_inst_hi .. ▸ .appDF (ih1 W) (ih2 W)
  | lamDF _ _ ih1 ih2 => exact .lamDF (ih1 W) (ih2 W.succ)
  | forallEDF _ _ h1 h2 h3 h4 ih1 ih2 => exact .forallEDF (ih1 W) (ih2 W.succ) h1 h2 h3 h4
  | defeqDF _ _ ih1 ih2 => exact .defeqDF (ih1 W) (ih2 W)
  | beta _ _ ih1 ih2 =>
    exact VExpr.inst_inst_hi .. ▸ VExpr.inst_inst_hi .. ▸ .beta (ih1 W.succ) (ih2 W)
  | eta _ ih =>
    have := BDefEq.eta (ih W)
    rw [lift, VExpr.liftN_instN_lo (hj := Nat.zero_le _), Nat.add_comm] at this
    simpa [inst]
  | proofIrrel _ _ _ ih1 ih2 ih3 => exact .proofIrrel (ih1 W) (ih2 W) (ih3 W)
  | extra h1 h2 h3 h4 =>
    have ⟨⟨hA1, _⟩, hA2, hA3⟩ := henv.closed.2 h1
    rw [hA1.instL.instN_eq (Nat.zero_le _), hA2.instL.instN_eq (Nat.zero_le _),
      hA3.instL.instN_eq (Nat.zero_le _)]
    exact .extra h1 h2 h3 h4

end

/-! ### Typing lemmas -/

section
variable {env : VEnv} {Γ : List VExpr}

theorem BDefEq.app' {f A B a B'} (h1 : BDefEq env Γ f f (.forallE A B)) (h2 : BDefEq env Γ a a A)
    (eq : B.inst a = B') : BDefEq env Γ (.app f a) (.app f a) B' := eq ▸ .appDF h1 h2

theorem forall₂_rfl : ∀ ls : List VLevel, List.Forall₂ (· ≈ ·) ls ls
  | [] => .nil
  | _ :: ls => .cons rfl (forall₂_rfl ls)

theorem BDefEq.const' {c ci ls ty'} (h1 : env.constants c = some ci) (h2 : ∀ l ∈ ls, l.WF 0)
    (h3 : ls.length = ci.uvars) (h4 : ∀ l ∈ ls, l.eval [] ≤ 1) (eq : ci.type.instL ls = ty') :
    BDefEq env Γ (.const c ls) (.const c ls) ty' :=
  eq ▸ .constDF h1 h2 h2 h3 (forall₂_rfl ls) h4

theorem BDefEq.sort0 : BDefEq env Γ (.sort .zero) (.sort .zero) (.sort (.succ .zero)) :=
  .sortDF trivial trivial rfl rfl

theorem BDefEq.lam' {A u e B} (h1 : BDefEq env Γ A A (.sort u)) (h2 : BDefEq env (A::Γ) e e B) :
    BDefEq env Γ (.lam A e) (.lam A e) (.forallE A B) := .lamDF h1 h2

theorem BDefEq.forallE' {A u B v} (h1 : BDefEq env Γ A A (.sort u))
    (h2 : BDefEq env (A::Γ) B B (.sort v)) (hu' : u.WF 0 := by decide) (hv' : v.WF 0 := by decide)
    (hu : u.eval [] ≤ 1 := by decide) (hv : v.eval [] ≤ 1 := by decide) :
    BDefEq env Γ (.forallE A B) (.forallE A B) (.sort (.imax u v)) := .forallEDF h1 h2 hu' hv' hu hv

theorem BDefEq.defeq {A B u e e'} (h1 : BDefEq env Γ A B (.sort u)) (h2 : BDefEq env Γ e e' A) :
    BDefEq env Γ e e' B := .defeqDF h1 h2

theorem BDefEq.defeq' {A B u e e'} (h1 : BDefEq env Γ A B (.sort u)) (h2 : BDefEq env Γ e e' B) :
    BDefEq env Γ e e' A := .defeqDF h1.symm h2

end

syntax "btype_tac" : tactic
macro_rules | `(tactic| btype_tac) => `(tactic|
  first
  | refine BDefEq.forallE' (u := ?_) (v := ?_) ?_ ?_ ?_ ?_ ?_ ?_ <;> [skip; skip; btype_tac; btype_tac;
      decide; decide; decide; decide]
  | exact BDefEq.sort0
  | refine BDefEq.bvar ?_; lookup_tac
  | refine BDefEq.app' (A := ?_) (B := ?_) ?_ ?_ ?_ <;> [skip; skip; btype_tac; btype_tac; exact rfl]
  | refine BDefEq.const' (ci := ?_) ?_ ?_ ?_ ?_ ?_ <;> [skip; assumption; decide; decide; decide;
      exact rfl]
  | refine BDefEq.lam' (u := ?_) ?_ ?_ <;> [skip; btype_tac; btype_tac]
)

/-! ### Certificates in the fragment -/

/-- The certificate keeps the fragment's bounds at its leaves and uses no projection rule. -/
def Cert.leafOK : Cert → Bool
  | bvar .. => true
  | symm _ c => c.leafOK
  | trans _ _ c₁ c₂ => c₁.leafOK && c₂.leafOK
  | sortDF _ l _ => decide (l.WF 0 ∧ l.eval [] = 0)
  | constDF _ _ _ ls _ => ls.all fun l => decide (l.WF 0 ∧ l.eval [] ≤ 1)
  | appDF _ _ _ _ _ _ _ c₁ c₂ => c₁.leafOK && c₂.leafOK
  | lamDF _ _ _ _ _ _ _ c₁ c₂ => c₁.leafOK && c₂.leafOK
  | forallEDF _ u v _ _ _ _ c₁ c₂ =>
    decide (u.WF 0 ∧ v.WF 0 ∧ u.eval [] ≤ 1 ∧ v.eval [] ≤ 1) && c₁.leafOK && c₂.leafOK
  | defeqDF _ _ _ _ c₁ c₂ => c₁.leafOK && c₂.leafOK
  | beta _ _ _ _ _ c₁ c₂ => c₁.leafOK && c₂.leafOK
  | eta _ _ _ _ c => c.leafOK
  | proofIrrel _ _ _ _ c₁ c₂ c₃ => c₁.leafOK && c₂.leafOK && c₃.leafOK
  | extra _ _ ls => ls.all fun l => decide (l.WF 0 ∧ l.eval [] ≤ 1)
  | projDF .. | projIota .. | projEta .. => false

theorem Cert.check_bsound {env : VEnv} {K : Deciders} (hK : K.Spec env 0) :
    ∀ c : Cert, c.check env 0 K = true → c.leafOK = true →
      BDefEq env c.j.Γ c.j.e1 c.j.e2 c.j.A := by
  intro c h hb
  induction c with
  | bvar j i =>
    simp only [check, decide_eq_true_eq] at h
    obtain ⟨h1, h2, h3⟩ := h
    show BDefEq env j.Γ j.e1 j.e2 j.A; rw [h1, h2]; exact .bvar (lookup_iff.2 h3)
  | symm j c ih =>
    simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [leafOK] at hb
    have := ih h.2 hb; rw [h.1] at this; exact .symm this
  | trans j m c₁ c₂ ih₁ ih₂ =>
    simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [leafOK, Bool.and_eq_true] at hb
    obtain ⟨⟨⟨h1, h2⟩, k1⟩, k2⟩ := h
    have a := ih₁ k1 hb.1; have b := ih₂ k2 hb.2; rw [h1] at a; rw [h2] at b; exact .trans a b
  | sortDF j l l' =>
    simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [leafOK, decide_eq_true_eq] at hb
    obtain ⟨⟨hj, w, w'⟩, e⟩ := h
    rw [Cert.j, hj]; exact .sortDF w w' ((hK.equiv l l' w w').1 e) hb.2
  | constDF j n ci ls ls' =>
    simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [leafOK, List.all_eq_true, decide_eq_true_eq] at hb
    obtain ⟨⟨hj, hc, w, w', hl⟩, e⟩ := h
    rw [Cert.j, hj]; exact .constDF hc w w' hl ((equivs_iff hK w w').1 e) fun l hl => (hb l hl).2
  | appDF j A B f f' a a' c₁ c₂ ih₁ ih₂ =>
    simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [leafOK, Bool.and_eq_true] at hb
    obtain ⟨⟨⟨hj, h1, h2⟩, k1⟩, k2⟩ := h
    have x := ih₁ k1 hb.1; have y := ih₂ k2 hb.2; rw [h1] at x; rw [h2] at y
    rw [Cert.j, hj]; exact .appDF x y
  | lamDF j u A A' b b' B c₁ c₂ ih₁ ih₂ =>
    simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [leafOK, Bool.and_eq_true] at hb
    obtain ⟨⟨⟨hj, h1, h2⟩, k1⟩, k2⟩ := h
    have x := ih₁ k1 hb.1; have y := ih₂ k2 hb.2; rw [h1] at x; rw [h2] at y
    rw [Cert.j, hj]; exact .lamDF x y
  | forallEDF j u v A A' b b' c₁ c₂ ih₁ ih₂ =>
    simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [leafOK, Bool.and_eq_true, decide_eq_true_eq] at hb
    obtain ⟨⟨⟨hj, h1, h2⟩, k1⟩, k2⟩ := h
    obtain ⟨⟨⟨hu', hv', hu, hv⟩, b1⟩, b2⟩ := hb
    have x := ih₁ k1 b1; have y := ih₂ k2 b2; rw [h1] at x; rw [h2] at y
    rw [Cert.j, hj]; exact .forallEDF x y hu' hv' hu hv
  | defeqDF j u A B c₁ c₂ ih₁ ih₂ =>
    simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [leafOK, Bool.and_eq_true] at hb
    obtain ⟨⟨⟨hj, h1, h2⟩, k1⟩, k2⟩ := h
    have x := ih₁ k1 hb.1; have y := ih₂ k2 hb.2; rw [h1] at x; rw [h2] at y
    show BDefEq env j.Γ j.e1 j.e2 j.A; rw [hj]; exact .defeqDF x y
  | beta j A e B e' c₁ c₂ ih₁ ih₂ =>
    simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [leafOK, Bool.and_eq_true] at hb
    obtain ⟨⟨⟨hj, h1, h2⟩, k1⟩, k2⟩ := h
    have x := ih₁ k1 hb.1; have y := ih₂ k2 hb.2; rw [h1] at x; rw [h2] at y
    rw [Cert.j, hj]; exact .beta x y
  | eta j e A B c ih =>
    simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [leafOK] at hb
    obtain ⟨⟨hj, h1⟩, k⟩ := h
    have x := ih k hb; rw [h1] at x
    rw [Cert.j, hj]; exact .eta x
  | proofIrrel j p q q' c₁ c₂ c₃ ih₁ ih₂ ih₃ =>
    simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [leafOK, Bool.and_eq_true] at hb
    obtain ⟨⟨⟨⟨hj, h1, h2, h3⟩, k1⟩, k2⟩, k3⟩ := h
    have x := ih₁ k1 hb.1.1; have y := ih₂ k2 hb.1.2; have z := ih₃ k3 hb.2
    rw [h1] at x; rw [h2] at y; rw [h3] at z
    rw [Cert.j, hj]; exact .proofIrrel x y z
  | extra j df ls =>
    simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [leafOK, List.all_eq_true, decide_eq_true_eq] at hb
    obtain ⟨⟨hj, w, hl⟩, e⟩ := h
    rw [Cert.j, hj]; exact .extra ((hK.defeq df).1 e) w hl fun l hl => (hb l hl).2
  | projDF | projIota | projEta => simp [leafOK] at hb

theorem Cert.check_bcomplete {env : VEnv} {K : Deciders} (hK : K.Spec env 0)
    {Γ e1 e2 A} (H : BDefEq env Γ e1 e2 A) :
    ∃ c : Cert, c.check env 0 K = true ∧ c.leafOK = true ∧ c.j = ⟨Γ, e1, e2, A⟩ := by
  induction H with
  | @bvar Γ i A h =>
    exact ⟨.bvar ⟨Γ, .bvar i, .bvar i, A⟩ i, by simp [check, lookup_iff.1 h], rfl, rfl⟩
  | @symm Γ e e' A _ ih =>
    obtain ⟨c, k, b, h⟩ := ih
    exact ⟨.symm ⟨Γ, e', e, A⟩ c, by simp [check, k, h], by simp [leafOK, b], rfl⟩
  | @trans Γ a b A c _ _ ih₁ ih₂ =>
    obtain ⟨c₁, k1, b1, h1⟩ := ih₁; obtain ⟨c₂, k2, b2, h2⟩ := ih₂
    exact ⟨.trans ⟨Γ, a, c, A⟩ b c₁ c₂, by simp [check, k1, k2, h1, h2],
      by simp [leafOK, b1, b2], rfl⟩
  | @sortDF l l' Γ w w' e hb =>
    exact ⟨.sortDF ⟨Γ, .sort l, .sort l', .sort (.succ l)⟩ l l',
      by simp [check, w, w', (hK.equiv _ _ w w').2 e], by simp [leafOK, hb, w], rfl⟩
  | @constDF n ci ls ls' Γ hc w w' hl e hb =>
    refine ⟨.constDF ⟨Γ, .const n ls, .const n ls', ci.type.instL ls⟩ n ci ls ls', ?_,
      by simpa [leafOK] using fun l hl => And.intro (w l hl) (hb l hl), rfl⟩
    simp only [check, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨trivial, hc, w, w', hl⟩, (equivs_iff hK w w').2 e⟩
  | @appDF Γ f f' A B a a' _ _ ih₁ ih₂ =>
    obtain ⟨c₁, k1, b1, h1⟩ := ih₁; obtain ⟨c₂, k2, b2, h2⟩ := ih₂
    exact ⟨.appDF ⟨Γ, .app f a, .app f' a', B.inst a⟩ A B f f' a a' c₁ c₂,
      by simp [check, k1, k2, h1, h2], by simp [leafOK, b1, b2], rfl⟩
  | @lamDF Γ A A' u b b' B _ _ ih₁ ih₂ =>
    obtain ⟨c₁, k1, b1, h1⟩ := ih₁; obtain ⟨c₂, k2, b2, h2⟩ := ih₂
    exact ⟨.lamDF ⟨Γ, .lam A b, .lam A' b', .forallE A B⟩ u A A' b b' B c₁ c₂,
      by simp [check, k1, k2, h1, h2], by simp [leafOK, b1, b2], rfl⟩
  | @forallEDF Γ A A' u b b' v _ _ hu' hv' hu hv ih₁ ih₂ =>
    obtain ⟨c₁, k1, b1, h1⟩ := ih₁; obtain ⟨c₂, k2, b2, h2⟩ := ih₂
    exact ⟨.forallEDF ⟨Γ, .forallE A b, .forallE A' b', .sort (.imax u v)⟩ u v A A' b b' c₁ c₂,
      by simp [check, k1, k2, h1, h2], by simp [leafOK, b1, b2, hu, hv, hu', hv'], rfl⟩
  | @defeqDF Γ A B u e e' _ _ ih₁ ih₂ =>
    obtain ⟨c₁, k1, b1, h1⟩ := ih₁; obtain ⟨c₂, k2, b2, h2⟩ := ih₂
    exact ⟨.defeqDF ⟨Γ, e, e', B⟩ u A B c₁ c₂, by simp [check, k1, k2, h1, h2],
      by simp [leafOK, b1, b2], rfl⟩
  | @beta A Γ e B e' _ _ ih₁ ih₂ =>
    obtain ⟨c₁, k1, b1, h1⟩ := ih₁; obtain ⟨c₂, k2, b2, h2⟩ := ih₂
    exact ⟨.beta ⟨Γ, .app (.lam A e) e', e.inst e', B.inst e'⟩ A e B e' c₁ c₂,
      by simp [check, k1, k2, h1, h2], by simp [leafOK, b1, b2], rfl⟩
  | @eta Γ e A B _ ih =>
    obtain ⟨c, k, b, h⟩ := ih
    exact ⟨.eta ⟨Γ, .lam A (.app e.lift (.bvar 0)), e, .forallE A B⟩ e A B c,
      by simp [check, k, h], by simp [leafOK, b], rfl⟩
  | @proofIrrel Γ p q q' _ _ _ ih₁ ih₂ ih₃ =>
    obtain ⟨c₁, k1, b1, h1⟩ := ih₁; obtain ⟨c₂, k2, b2, h2⟩ := ih₂
    obtain ⟨c₃, k3, b3, h3⟩ := ih₃
    exact ⟨.proofIrrel ⟨Γ, q, q', p⟩ p q q' c₁ c₂ c₃,
      by simp [check, k1, k2, k3, h1, h2, h3], by simp [leafOK, b1, b2, b3], rfl⟩
  | @extra df ls Γ hd w hl hb =>
    refine ⟨.extra ⟨Γ, df.lhs.instL ls, df.rhs.instL ls, df.type.instL ls⟩ df ls, ?_,
      by simpa [leafOK] using fun l hl => And.intro (w l hl) (hb l hl), rfl⟩
    simp only [check, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨trivial, w, hl⟩, (hK.defeq _).2 hd⟩

end Lean4Lean.Incomplete
