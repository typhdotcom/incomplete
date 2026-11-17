import Lean4Lean.Theory.Typing.Basic

/-!
# Derivation certificates

A `Cert` is a derivation tree of `VEnv.IsDefEq`, each node carrying its judgment and the data
its rule needs. `Cert.check` is a total `Bool` function that checks every node against its
children, given deciders for the environment's rules and for level equivalence. It is sound
and complete.
-/

namespace Incomplete
open Lean4Lean
open VExpr

deriving instance DecidableEq for VLevel
deriving instance DecidableEq for VExpr
deriving instance DecidableEq for VConstant
deriving instance DecidableEq for VDefEq

/-- A judgment `Γ ⊢ e1 ≡ e2 : A`. -/
structure Judg where
  Γ : List VExpr
  e1 : VExpr
  e2 : VExpr
  A : VExpr
  deriving DecidableEq

def Judg.Valid (env : VEnv) (U : Nat) (J : Judg) : Prop := env.IsDefEq U J.Γ J.e1 J.e2 J.A

def lookupTy : List VExpr → Nat → Option VExpr
  | [], _ => none
  | A :: _, 0 => some A.lift
  | _ :: Γ, i + 1 => (lookupTy Γ i).map VExpr.lift

theorem lookup_iff : ∀ {Γ i A}, Lookup Γ i A ↔ lookupTy Γ i = some A
  | [], i, A => ⟨nofun, nofun⟩
  | B :: Γ, 0, A => ⟨fun | .zero => rfl, fun h => by cases h; exact .zero⟩
  | B :: Γ, i + 1, A => by
    refine ⟨fun | .succ h => by simp [lookupTy, lookup_iff.1 h], fun h => ?_⟩
    simp only [lookupTy, Option.map_eq_some_iff] at h
    obtain ⟨_, h, rfl⟩ := h; exact .succ (lookup_iff.2 h)

inductive Cert where
  | bvar (j : Judg) (i : Nat)
  | symm (j : Judg) (c : Cert)
  | trans (j : Judg) (m : VExpr) (c₁ c₂ : Cert)
  | sortDF (j : Judg) (l l' : VLevel)
  | constDF (j : Judg) (n : Name) (ci : VConstant) (ls ls' : List VLevel)
  | appDF (j : Judg) (A B f f' a a' : VExpr) (c₁ c₂ : Cert)
  | lamDF (j : Judg) (u : VLevel) (A A' b b' B : VExpr) (c₁ c₂ : Cert)
  | forallEDF (j : Judg) (u v : VLevel) (A A' b b' : VExpr) (c₁ c₂ : Cert)
  | defeqDF (j : Judg) (u : VLevel) (A B : VExpr) (c₁ c₂ : Cert)
  | beta (j : Judg) (A e B e' : VExpr) (c₁ c₂ : Cert)
  | eta (j : Judg) (e A B : VExpr) (c : Cert)
  | proofIrrel (j : Judg) (p h h' : VExpr) (c₁ c₂ c₃ : Cert)
  | extra (j : Judg) (df : VDefEq) (ls : List VLevel)
  /-- `projDF`, with the parameter and index lists stored reversed. -/
  | projDF (j : Judg) (s : Name) (k : Nat) (ls : List VLevel) (AsR IR AsR' IR' : List VExpr)
    (u : VLevel) (e e' : VExpr) (c₁ c₂ c₃ : Cert)
  /-- `projIota`, with the parameter, field and index lists stored reversed. -/
  | projIota (j : Judg) (s : Name) (k : Nat) (ls : List VLevel) (AsR fsR IR : List VExpr)
    (c₁ c₂ c₃ : Cert)
  /-- `projEta`, with the parameter list stored reversed. -/
  | projEta (j : Judg) (s : Name) (ls : List VLevel) (AsR : List VExpr) (e : VExpr) (c₁ c₂ : Cert)
  deriving DecidableEq

def Cert.j : Cert → Judg
  | bvar j .. | symm j .. | trans j .. | sortDF j .. | constDF j .. | appDF j .. | lamDF j ..
  | forallEDF j .. | defeqDF j .. | beta j .. | eta j .. | proofIrrel j .. | extra j ..
  | projDF j .. | projIota j .. | projEta j .. => j

/-- Deciders for what a derivation in `env` at `U` level parameters consults beyond syntax. -/
structure Deciders where
  defeq : VDefEq → Bool
  equiv : VLevel → VLevel → Bool

def equivs (eq : VLevel → VLevel → Bool) : List VLevel → List VLevel → Bool
  | [], [] => true
  | a :: as, b :: bs => eq a b && equivs eq as bs
  | _, _ => false

/-- Whether a projection is allowed, decided classically: the checker code decides it for the
closed levels it meets. -/
noncomputable def projOK (d : VInductDecl) (c : VConstructor) (ls : List VLevel) (k : Nat) : Bool :=
  @decide (d.ProjAllowed c ls k) (Classical.propDecidable _)

/-- The single constructor of the `t`th type of `d`. -/
def singleCtor (d : VInductDecl) (t : Nat) : Option (VInductiveType × VConstructor) :=
  match d.types[t]? with
  | some T => match T.ctors with
    | [c] => some (T, c)
    | _ => none
  | none => none

theorem singleCtor_spec {d : VInductDecl} {t : Nat} {T : VInductiveType} {c : VConstructor}
    (h : singleCtor d t = some (T, c)) : d.types[t]? = some T ∧ T.ctors = [c] := by
  unfold singleCtor at h
  split at h
  · rename_i T' hT
    split at h
    · cases h; exact ⟨hT, ‹_›⟩
    · cases h
  · cases h

theorem singleCtor_of {d : VInductDecl} {t : Nat} {T : VInductiveType} {c : VConstructor}
    (hT : d.types[t]? = some T) (hc : T.ctors = [c]) : singleCtor d t = some (T, c) := by
  simp [singleCtor, hT, hc]

noncomputable def Cert.check (env : VEnv) (U : Nat) (K : Deciders) : Cert → Bool
  | bvar j i => decide (j.e1 = .bvar i ∧ j.e2 = .bvar i ∧ lookupTy j.Γ i = some j.A)
  | symm j c => decide (c.j = ⟨j.Γ, j.e2, j.e1, j.A⟩) && c.check env U K
  | trans j m c₁ c₂ => decide (c₁.j = ⟨j.Γ, j.e1, m, j.A⟩ ∧ c₂.j = ⟨j.Γ, m, j.e2, j.A⟩) &&
    c₁.check env U K && c₂.check env U K
  | sortDF j l l' => decide (j = ⟨j.Γ, .sort l, .sort l', .sort (.succ l)⟩ ∧ l.WF U ∧ l'.WF U) &&
    K.equiv l l'
  | constDF j n ci ls ls' => decide (j = ⟨j.Γ, .const n ls, .const n ls', ci.type.instL ls⟩ ∧
      env.constants n = some ci ∧ (∀ l ∈ ls, l.WF U) ∧ (∀ l ∈ ls', l.WF U) ∧
      ls.length = ci.uvars) && equivs K.equiv ls ls'
  | appDF j A B f f' a a' c₁ c₂ => decide (j = ⟨j.Γ, .app f a, .app f' a', B.inst a⟩ ∧
      c₁.j = ⟨j.Γ, f, f', .forallE A B⟩ ∧ c₂.j = ⟨j.Γ, a, a', A⟩) &&
    c₁.check env U K && c₂.check env U K
  | lamDF j u A A' b b' B c₁ c₂ => decide (j = ⟨j.Γ, .lam A b, .lam A' b', .forallE A B⟩ ∧
      c₁.j = ⟨j.Γ, A, A', .sort u⟩ ∧ c₂.j = ⟨A :: j.Γ, b, b', B⟩) &&
    c₁.check env U K && c₂.check env U K
  | forallEDF j u v A A' b b' c₁ c₂ =>
    decide (j = ⟨j.Γ, .forallE A b, .forallE A' b', .sort (.imax u v)⟩ ∧
      c₁.j = ⟨j.Γ, A, A', .sort u⟩ ∧ c₂.j = ⟨A :: j.Γ, b, b', .sort v⟩) &&
    c₁.check env U K && c₂.check env U K
  | defeqDF j u A B c₁ c₂ => decide (j.A = B ∧ c₁.j = ⟨j.Γ, A, B, .sort u⟩ ∧
      c₂.j = ⟨j.Γ, j.e1, j.e2, A⟩) && c₁.check env U K && c₂.check env U K
  | beta j A e B e' c₁ c₂ => decide (j = ⟨j.Γ, .app (.lam A e) e', e.inst e', B.inst e'⟩ ∧
      c₁.j = ⟨A :: j.Γ, e, e, B⟩ ∧ c₂.j = ⟨j.Γ, e', e', A⟩) &&
    c₁.check env U K && c₂.check env U K
  | eta j e A B c => decide (j = ⟨j.Γ, .lam A (.app e.lift (.bvar 0)), e, .forallE A B⟩ ∧
      c.j = ⟨j.Γ, e, e, .forallE A B⟩) && c.check env U K
  | proofIrrel j p h h' c₁ c₂ c₃ => decide (j = ⟨j.Γ, h, h', p⟩ ∧
      c₁.j = ⟨j.Γ, p, p, .sort .zero⟩ ∧ c₂.j = ⟨j.Γ, h, h, p⟩ ∧ c₃.j = ⟨j.Γ, h', h', p⟩) &&
    c₁.check env U K && c₂.check env U K && c₃.check env U K
  | extra j df ls => decide (j = ⟨j.Γ, df.lhs.instL ls, df.rhs.instL ls, df.type.instL ls⟩ ∧
      (∀ l ∈ ls, l.WF U) ∧ ls.length = df.uvars) && K.defeq df
  | projDF j s k ls AsR IR AsR' IR' u e e' c₁ c₂ c₃ =>
    match env.inducts s with
    | some (d, t) => match singleCtor d t with
      | some (T, c) => match c.fields[k]? with
        | some f => decide ((∀ l ∈ ls, l.WF U) ∧ ls.length = d.uvars ∧
            AsR.length = d.params.length ∧ IR.length = T.indices.length ∧
            AsR'.length = d.params.length ∧ IR'.length = T.indices.length ∧
            j = ⟨j.Γ, .proj s k e, .proj s k e', c.projType ls s k AsR.reverse e⟩ ∧
            c₁.j = ⟨j.Γ, .appN (.const s ls) (AsR.reverse ++ IR.reverse),
              .appN (.const s ls) (AsR'.reverse ++ IR'.reverse), .sort u⟩ ∧
            c₂.j = ⟨j.Γ, e, e', .appN (.const s ls) (AsR.reverse ++ IR.reverse)⟩ ∧
            c₃.j = ⟨j.Γ, c.projType ls s k AsR.reverse e, c.projType ls s k AsR'.reverse e',
              .sort (f.level.inst ls)⟩) && projOK d c ls k &&
          c₁.check env U K && c₂.check env U K && c₃.check env U K
        | none => false
      | none => false
    | none => false
  | projIota j s k ls AsR fsR IR c₁ c₂ c₃ =>
    match env.inducts s with
    | some (d, t) => match singleCtor d t with
      | some (T, c) => match c.fields[k]? with
        | some f => decide ((∀ l ∈ ls, l.WF U) ∧ ls.length = d.uvars ∧
            AsR.length = d.params.length ∧ fsR.length = c.fields.length ∧
            IR.length = T.indices.length ∧ fsR.reverse[k]? = some j.e2 ∧
            j = ⟨j.Γ, .proj s k (.appN (.const c.name ls) (AsR.reverse ++ fsR.reverse)), j.e2,
              c.projType ls s k AsR.reverse (.appN (.const c.name ls) (AsR.reverse ++ fsR.reverse))⟩ ∧
            c₁.j = ⟨j.Γ, .appN (.const c.name ls) (AsR.reverse ++ fsR.reverse),
              .appN (.const c.name ls) (AsR.reverse ++ fsR.reverse),
              .appN (.const s ls) (AsR.reverse ++ IR.reverse)⟩ ∧
            c₂.j = ⟨j.Γ, j.A, j.A, .sort (f.level.inst ls)⟩ ∧
            c₃.j = ⟨j.Γ, j.e2, j.e2, j.A⟩) && projOK d c ls k &&
          c₁.check env U K && c₂.check env U K && c₃.check env U K
        | none => false
      | none => false
    | none => false
  | projEta j s ls AsR e c₁ c₂ =>
    match env.inducts s with
    | some (d, t) => match singleCtor d t with
      | some (T, c) => decide (T.indices = [] ∧ d.isRec = false ∧ (∀ l ∈ ls, l.WF U) ∧
            ls.length = d.uvars ∧ AsR.length = d.params.length ∧
            j = ⟨j.Γ, e, .appN (.const c.name ls) (AsR.reverse ++ VExpr.projs s c.fields.length e),
              .appN (.const s ls) AsR.reverse⟩ ∧
            c₁.j = ⟨j.Γ, e, e, .appN (.const s ls) AsR.reverse⟩ ∧
            c₂.j = ⟨j.Γ, j.e2, j.e2, .appN (.const s ls) AsR.reverse⟩) &&
          (List.range c.fields.length).all (projOK d c ls) &&
          c₁.check env U K && c₂.check env U K
      | none => false
    | none => false

/-- `K` decides `env`'s rules and the equivalence of levels well formed at `U`. -/
structure Deciders.Spec (env : VEnv) (U : Nat) (K : Deciders) : Prop where
  defeq : ∀ df, K.defeq df = true ↔ env.defeqs df
  equiv : ∀ l l', l.WF U → l'.WF U → (K.equiv l l' = true ↔ l ≈ l')

theorem equivs_iff {env : VEnv} {U : Nat} {K : Deciders} (hK : K.Spec env U) :
    ∀ {ls ls' : List VLevel}, (∀ l ∈ ls, l.WF U) → (∀ l ∈ ls', l.WF U) →
      (equivs K.equiv ls ls' = true ↔ List.Forall₂ (· ≈ ·) ls ls')
  | [], [], _, _ => by simp [equivs]
  | [], _ :: _, _, _ => by simp [equivs]
  | _ :: _, [], _, _ => by simp [equivs]
  | a :: as, b :: bs, h, h' => by
    simp only [equivs, Bool.and_eq_true, List.forall₂_cons]
    rw [hK.equiv a b (h a (.head _)) (h' b (.head _)),
      equivs_iff hK (fun l hl => h l (.tail _ hl)) (fun l hl => h' l (.tail _ hl))]

/-- **Soundness** of the checker. -/
theorem Cert.check_sound {env : VEnv} {U : Nat} {K : Deciders} (hK : K.Spec env U) :
    ∀ c : Cert, c.check env U K = true → c.j.Valid env U := by
  intro c h
  induction c with
  | bvar j i =>
    simp only [check, decide_eq_true_eq] at h
    obtain ⟨h1, h2, h3⟩ := h
    show env.IsDefEq U j.Γ j.e1 j.e2 j.A; rw [h1, h2]; exact .bvar (lookup_iff.2 h3)
  | symm j c ih =>
    simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
    have := ih h.2; rw [h.1] at this; exact .symm this
  | trans j m c₁ c₂ ih₁ ih₂ =>
    simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨h1, h2⟩, k1⟩, k2⟩ := h
    have a := ih₁ k1; have b := ih₂ k2; rw [h1] at a; rw [h2] at b; exact .trans a b
  | sortDF j l l' =>
    simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hj, w, w'⟩, e⟩ := h
    rw [Cert.j, hj]; exact .sortDF w w' ((hK.equiv l l' w w').1 e)
  | constDF j n ci ls ls' =>
    simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hj, hc, w, w', hl⟩, e⟩ := h
    rw [Cert.j, hj]; exact .constDF hc w w' hl ((equivs_iff hK w w').1 e)
  | appDF j A B f f' a a' c₁ c₂ ih₁ ih₂ =>
    simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hj, h1, h2⟩, k1⟩, k2⟩ := h
    have x := ih₁ k1; have y := ih₂ k2; rw [h1] at x; rw [h2] at y
    rw [Cert.j, hj]; exact .appDF x y
  | lamDF j u A A' b b' B c₁ c₂ ih₁ ih₂ =>
    simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hj, h1, h2⟩, k1⟩, k2⟩ := h
    have x := ih₁ k1; have y := ih₂ k2; rw [h1] at x; rw [h2] at y
    rw [Cert.j, hj]; exact .lamDF x y
  | forallEDF j u v A A' b b' c₁ c₂ ih₁ ih₂ =>
    simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hj, h1, h2⟩, k1⟩, k2⟩ := h
    have x := ih₁ k1; have y := ih₂ k2; rw [h1] at x; rw [h2] at y
    rw [Cert.j, hj]; exact .forallEDF x y
  | defeqDF j u A B c₁ c₂ ih₁ ih₂ =>
    simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hj, h1, h2⟩, k1⟩, k2⟩ := h
    have x := ih₁ k1; have y := ih₂ k2; rw [h1] at x; rw [h2] at y
    show env.IsDefEq U j.Γ j.e1 j.e2 j.A; rw [hj]; exact .defeqDF x y
  | beta j A e B e' c₁ c₂ ih₁ ih₂ =>
    simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hj, h1, h2⟩, k1⟩, k2⟩ := h
    have x := ih₁ k1; have y := ih₂ k2; rw [h1] at x; rw [h2] at y
    rw [Cert.j, hj]; exact .beta x y
  | eta j e A B c ih =>
    simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hj, h1⟩, k⟩ := h
    have x := ih k; rw [h1] at x
    rw [Cert.j, hj]; exact .eta x
  | proofIrrel j p q q' c₁ c₂ c₃ ih₁ ih₂ ih₃ =>
    simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨hj, h1, h2, h3⟩, k1⟩, k2⟩, k3⟩ := h
    have x := ih₁ k1; have y := ih₂ k2; have z := ih₃ k3
    rw [h1] at x; rw [h2] at y; rw [h3] at z
    rw [Cert.j, hj]; exact .proofIrrel x y z
  | extra j df ls =>
    simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hj, w, hl⟩, e⟩ := h
    rw [Cert.j, hj]; exact .extra ((hK.defeq df).1 e) w hl
  | projDF j s k ls AsR IR AsR' IR' u e e' c₁ c₂ c₃ ih₁ ih₂ ih₃ =>
    rcases hs : env.inducts s with _ | ⟨⟨d, t⟩⟩ <;> simp only [check, hs, Bool.false_eq_true] at h
    rcases hsc : singleCtor d t with _ | ⟨⟨T, c⟩⟩ <;> simp only [hsc, Bool.false_eq_true] at h
    rcases hf : c.fields[k]? with _ | f <;> simp only [hf, Bool.false_eq_true] at h
    obtain ⟨hT, hc⟩ := singleCtor_spec hsc
    simp only [Bool.and_eq_true, decide_eq_true_eq, projOK] at h
    obtain ⟨⟨⟨⟨⟨w, hl, ha, hi, ha', hi', hj, h1, h2, h3⟩, hp⟩, k1⟩, k2⟩, k3⟩ := h
    have x := ih₁ k1; have y := ih₂ k2; have z := ih₃ k3
    rw [h1] at x; rw [h2] at y; rw [h3] at z
    rw [Cert.j, hj]
    exact .projDF hs hT hc hf w hl (by simpa using ha) (by simpa using hi) (by simpa using ha')
      (by simpa using hi') x y hp z
  | projIota j s k ls AsR fsR IR c₁ c₂ c₃ ih₁ ih₂ ih₃ =>
    rcases hs : env.inducts s with _ | ⟨⟨d, t⟩⟩ <;> simp only [check, hs, Bool.false_eq_true] at h
    rcases hsc : singleCtor d t with _ | ⟨⟨T, c⟩⟩ <;> simp only [hsc, Bool.false_eq_true] at h
    rcases hf : c.fields[k]? with _ | f <;> simp only [hf, Bool.false_eq_true] at h
    obtain ⟨hT, hc⟩ := singleCtor_spec hsc
    simp only [Bool.and_eq_true, decide_eq_true_eq, projOK] at h
    obtain ⟨⟨⟨⟨⟨w, hl, ha, hfl, hi, hk, hj, h1, h2, h3⟩, hp⟩, k1⟩, k2⟩, k3⟩ := h
    have x := ih₁ k1; have y := ih₂ k2; have z := ih₃ k3
    rw [h1] at x; rw [h2] at y; rw [h3] at z
    show env.IsDefEq U j.Γ j.e1 j.e2 j.A
    rw [hj] at x y z ⊢
    exact .projIota hs hT hc hf hk w hl (by simpa using ha) (by simpa using hfl) (by simpa using hi)
      x hp y z
  | projEta j s ls AsR e c₁ c₂ ih₁ ih₂ =>
    rcases hs : env.inducts s with _ | ⟨⟨d, t⟩⟩ <;> simp only [check, hs, Bool.false_eq_true] at h
    rcases hsc : singleCtor d t with _ | ⟨⟨T, c⟩⟩ <;> simp only [hsc, Bool.false_eq_true] at h
    obtain ⟨hT, hc⟩ := singleCtor_spec hsc
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
      projOK] at h
    obtain ⟨⟨⟨⟨hidx, hrec, w, hl, ha, hj, h1, h2⟩, hp⟩, k1⟩, k2⟩ := h
    have x := ih₁ k1; have y := ih₂ k2
    rw [h1] at x; rw [h2] at y
    show env.IsDefEq U j.Γ j.e1 j.e2 j.A
    rw [hj] at y ⊢
    exact .projEta hs hT hc hidx hrec w hl (by simpa using ha) hp x y


/-- **Completeness** of the checker. -/
theorem Cert.check_complete {env : VEnv} {U : Nat} {K : Deciders} (hK : K.Spec env U)
    {Γ e1 e2 A} (H : env.IsDefEq U Γ e1 e2 A) :
    ∃ c : Cert, c.check env U K = true ∧ c.j = ⟨Γ, e1, e2, A⟩ := by
  induction H with
  | @bvar Γ i A h => exact ⟨.bvar ⟨Γ, .bvar i, .bvar i, A⟩ i, by simp [check, lookup_iff.1 h], rfl⟩
  | @symm Γ e e' A _ ih =>
    obtain ⟨c, k, h⟩ := ih
    exact ⟨.symm ⟨Γ, e', e, A⟩ c, by simp [check, k, h], rfl⟩
  | @trans Γ a b A c _ _ ih₁ ih₂ =>
    obtain ⟨c₁, k1, h1⟩ := ih₁; obtain ⟨c₂, k2, h2⟩ := ih₂
    exact ⟨.trans ⟨Γ, a, c, A⟩ b c₁ c₂, by simp [check, k1, k2, h1, h2], rfl⟩
  | @sortDF l l' Γ w w' e =>
    exact ⟨.sortDF ⟨Γ, .sort l, .sort l', .sort (.succ l)⟩ l l',
      by simp [check, w, w', (hK.equiv _ _ w w').2 e], rfl⟩
  | @constDF n ci ls ls' Γ hc w w' hl e =>
    refine ⟨.constDF ⟨Γ, .const n ls, .const n ls', ci.type.instL ls⟩ n ci ls ls', ?_, rfl⟩
    simp only [check, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨trivial, hc, w, w', hl⟩, (equivs_iff hK w w').2 e⟩
  | @appDF Γ f f' A B a a' _ _ ih₁ ih₂ =>
    obtain ⟨c₁, k1, h1⟩ := ih₁; obtain ⟨c₂, k2, h2⟩ := ih₂
    exact ⟨.appDF ⟨Γ, .app f a, .app f' a', B.inst a⟩ A B f f' a a' c₁ c₂,
      by simp [check, k1, k2, h1, h2], rfl⟩
  | @lamDF Γ A A' u b b' B _ _ ih₁ ih₂ =>
    obtain ⟨c₁, k1, h1⟩ := ih₁; obtain ⟨c₂, k2, h2⟩ := ih₂
    exact ⟨.lamDF ⟨Γ, .lam A b, .lam A' b', .forallE A B⟩ u A A' b b' B c₁ c₂,
      by simp [check, k1, k2, h1, h2], rfl⟩
  | @forallEDF Γ A A' u b b' v _ _ ih₁ ih₂ =>
    obtain ⟨c₁, k1, h1⟩ := ih₁; obtain ⟨c₂, k2, h2⟩ := ih₂
    exact ⟨.forallEDF ⟨Γ, .forallE A b, .forallE A' b', .sort (.imax u v)⟩ u v A A' b b' c₁ c₂,
      by simp [check, k1, k2, h1, h2], rfl⟩
  | @defeqDF Γ A B u e e' _ _ ih₁ ih₂ =>
    obtain ⟨c₁, k1, h1⟩ := ih₁; obtain ⟨c₂, k2, h2⟩ := ih₂
    exact ⟨.defeqDF ⟨Γ, e, e', B⟩ u A B c₁ c₂, by simp [check, k1, k2, h1, h2], rfl⟩
  | @beta A Γ e B e' _ _ ih₁ ih₂ =>
    obtain ⟨c₁, k1, h1⟩ := ih₁; obtain ⟨c₂, k2, h2⟩ := ih₂
    exact ⟨.beta ⟨Γ, .app (.lam A e) e', e.inst e', B.inst e'⟩ A e B e' c₁ c₂,
      by simp [check, k1, k2, h1, h2], rfl⟩
  | @eta Γ e A B _ ih =>
    obtain ⟨c, k, h⟩ := ih
    exact ⟨.eta ⟨Γ, .lam A (.app e.lift (.bvar 0)), e, .forallE A B⟩ e A B c,
      by simp [check, k, h], rfl⟩
  | @proofIrrel Γ p q q' _ _ _ ih₁ ih₂ ih₃ =>
    obtain ⟨c₁, k1, h1⟩ := ih₁; obtain ⟨c₂, k2, h2⟩ := ih₂; obtain ⟨c₃, k3, h3⟩ := ih₃
    exact ⟨.proofIrrel ⟨Γ, q, q', p⟩ p q q' c₁ c₂ c₃,
      by simp [check, k1, k2, k3, h1, h2, h3], rfl⟩
  | @extra df ls Γ hd w hl =>
    refine ⟨.extra ⟨Γ, df.lhs.instL ls, df.rhs.instL ls, df.type.instL ls⟩ df ls, ?_, rfl⟩
    simp only [check, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨trivial, w, hl⟩, (hK.defeq _).2 hd⟩
  | @projDF s d t T c k f ls Γ As I As' I' u e e' hs hT hc hf w hl ha hi ha' hi' _ _ hp _
      ih₁ ih₂ ih₃ =>
    obtain ⟨c₁, k1, h1⟩ := ih₁; obtain ⟨c₂, k2, h2⟩ := ih₂; obtain ⟨c₃, k3, h3⟩ := ih₃
    refine ⟨.projDF ⟨Γ, .proj s k e, .proj s k e', c.projType ls s k As e⟩ s k ls As.reverse
      I.reverse As'.reverse I'.reverse u e e' c₁ c₂ c₃, ?_, rfl⟩
    simp [check, hs, singleCtor_of hT hc, hf, hl, ha, hi, ha', hi', h1, h2, h3, k1, k2, k3,
      projOK, hp]
    exact w
  | @projIota s d t T c k f fs a ls Γ As I hs hT hc hf hfs w hl ha hfl hi _ hp _ _ ih₁ ih₂ ih₃ =>
    obtain ⟨c₁, k1, h1⟩ := ih₁; obtain ⟨c₂, k2, h2⟩ := ih₂; obtain ⟨c₃, k3, h3⟩ := ih₃
    refine ⟨.projIota ⟨Γ, .proj s k (.appN (.const c.name ls) (As ++ fs)), a,
      c.projType ls s k As (.appN (.const c.name ls) (As ++ fs))⟩ s k ls As.reverse fs.reverse
      I.reverse c₁ c₂ c₃, ?_, rfl⟩
    simp [check, hs, singleCtor_of hT hc, hf, hfs, hl, ha, hfl, hi, h1, h2, h3, k1, k2, k3,
      projOK, hp]
    exact w
  | @projEta s d t T c ls Γ e As hs hT hc hidx hrec w hl ha hp _ _ ih₁ ih₂ =>
    obtain ⟨c₁, k1, h1⟩ := ih₁; obtain ⟨c₂, k2, h2⟩ := ih₂
    refine ⟨.projEta ⟨Γ, e, .appN (.const c.name ls) (As ++ VExpr.projs s c.fields.length e),
      .appN (.const s ls) As⟩ s ls As.reverse e c₁ c₂, ?_, rfl⟩
    simp [check, hs, singleCtor_of hT hc, hidx, hrec, hl, ha, h1, h2, k1, k2, projOK,
      List.all_eq_true]
    exact ⟨w, hp⟩

end Incomplete
