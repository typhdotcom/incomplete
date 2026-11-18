import Incomplete.Cert
import Incomplete.Sentences

/-!
# Provability in `natEnv` is checked by certificates

At no level parameters every level is closed, so level equivalence is decided by evaluation;
and `natEnv`'s rules are its two iota rules. `checkProof c P` therefore decides whether `c` certifies a closed proof of `P`, and
`Provable natEnv P ↔ ∃ c, checkProof c P = true`.
-/

namespace Incomplete
open Lean4Lean
open VExpr

theorem VLevel.eval_closed : ∀ {l : VLevel}, l.WF 0 → ∀ ls, l.eval ls = l.eval []
  | .zero, _, _ => rfl
  | .succ l, h, ls => by simp [VLevel.eval, eval_closed (l := l) h ls]
  | .max a b, h, ls => by simp [VLevel.eval, eval_closed h.1 ls, eval_closed h.2 ls]
  | .imax a b, h, ls => by simp [VLevel.eval, eval_closed h.1 ls, eval_closed h.2 ls]
  | .param i, h, _ => absurd h (Nat.not_lt_zero i)

def natDeciders : Deciders where
  defeq df := decide (df = iotaSucc ∨ df = iotaZero)
  equiv l l' := l.eval [] == l'.eval []

theorem natDeciders_spec : natDeciders.Spec natEnv 0 where
  defeq df := by
    simp only [natDeciders, decide_eq_true_eq]
    show _ ↔ df = iotaSucc ∨ df = iotaZero ∨ False
    simp
  equiv l l' h h' := by
    simp only [natDeciders, beq_iff_eq, VLevel.equiv_def]
    exact ⟨fun e ls => by rw [VLevel.eval_closed h, VLevel.eval_closed h', e], fun e => e []⟩
/-- `c` certifies a closed proof of `P` in `natEnv`. -/
noncomputable def checkProof (c : Cert) (P : VExpr) : Bool :=
  c.check natEnv 0 natDeciders && decide (c.j.Γ = [] ∧ c.j.e1 = c.j.e2 ∧ c.j.A = P)

/-- **Enumerability, meta-level.** Provability in `natEnv` is witnessed by checkable
certificates. -/
theorem provable_iff_cert {P : VExpr} : Provable natEnv P ↔ ∃ c, checkProof c P = true := by
  constructor
  · rintro ⟨e, h⟩
    obtain ⟨c, k, hc⟩ := Cert.check_complete natDeciders_spec h
    exact ⟨c, by simp [checkProof, k, hc]⟩
  · rintro ⟨c, h⟩
    simp only [checkProof, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨k, hΓ, he, hA⟩ := h
    have := Cert.check_sound natDeciders_spec c k
    refine ⟨c.j.e1, ?_⟩
    have : natEnv.IsDefEq 0 c.j.Γ c.j.e1 c.j.e2 c.j.A := this
    rw [hΓ, ← he, hA] at this; exact this

/-! ### Environments given by finite tables -/

/-- A finite description of an environment's constants, definitional-equality rules and
inductive blocks. -/
structure Tables where
  consts : List (Name × VConstant)
  rules : List VDefEq
  inducts : List (Name × (VInductDecl × Nat))

/-- The first entry for `m`. -/
def tlookup : List (Name × VConstant) → Name → Option VConstant
  | [], _ => none
  | (n, ci) :: r, m => if m = n then some ci else tlookup r m

/-- The first block entry for `m`. -/
def ilookup : List (Name × (VInductDecl × Nat)) → Name → Option (VInductDecl × Nat)
  | [], _ => none
  | (n, b) :: r, m => if m = n then some b else ilookup r m

/-- The environment the tables describe. -/
def Tables.env (T : Tables) : VEnv where
  constants := tlookup T.consts
  defeqs df := df ∈ T.rules
  inducts := ilookup T.inducts

def Tables.deciders (T : Tables) : Deciders where
  defeq df := decide (df ∈ T.rules)
  equiv l l' := l.eval [] == l'.eval []

/-- `T` lists `env`'s constants and inductive blocks (first entry wins) and its
definitional-equality rules. -/
structure TablesFor (env : VEnv) (T : Tables) : Prop where
  consts : ∀ n, env.constants n = tlookup T.consts n
  rules : ∀ df, env.defeqs df ↔ df ∈ T.rules
  inducts : ∀ n, env.inducts n = ilookup T.inducts n

theorem Tables.deciders_spec {env : VEnv} {T : Tables} (hT : TablesFor env T) :
    T.deciders.Spec env 0 where
  defeq df := by simp [Tables.deciders, hT.rules]
  equiv l l' h h' := by
    simp only [Tables.deciders, beq_iff_eq, VLevel.equiv_def]
    exact ⟨fun e ls => by rw [VLevel.eval_closed h, VLevel.eval_closed h', e], fun e => e []⟩

/-- Checking reads the environment only through its constants and inductive blocks. -/
theorem Cert.check_congr {env env' : VEnv} (h : ∀ n, env.constants n = env'.constants n)
    (hi : ∀ n, env.inducts n = env'.inducts n)
    (U : Nat) (K : Deciders) : ∀ c : Cert, c.check env U K = c.check env' U K := by
  intro c; induction c <;> simp_all [Cert.check]

/-- `c` certifies a closed proof of `P` in the environment of `T`. -/
noncomputable def checkProofT (T : Tables) (c : Cert) (P : VExpr) : Bool :=
  c.check T.env 0 T.deciders && decide (c.j.Γ = [] ∧ c.j.e1 = c.j.e2 ∧ c.j.A = P)

/-- **Enumerability, meta-level**, for an environment given by tables. -/
theorem provable_iff_certT {env : VEnv} {T : Tables} (hT : TablesFor env T)
    {P : VExpr} : Provable env P ↔ ∃ c, checkProofT T c P = true := by
  have hc : ∀ c : Cert, c.check T.env 0 T.deciders = c.check env 0 T.deciders :=
    Cert.check_congr (fun n => (hT.consts n).symm) (fun n => (hT.inducts n).symm) 0 _
  constructor
  · rintro ⟨e, h⟩
    obtain ⟨c, k, hk⟩ := Cert.check_complete (Tables.deciders_spec hT) h
    exact ⟨c, by simp [checkProofT, hc, k, hk]⟩
  · rintro ⟨c, h⟩
    simp only [checkProofT, Bool.and_eq_true, decide_eq_true_eq, hc] at h
    obtain ⟨k, hΓ, he, hA⟩ := h
    have : env.IsDefEq 0 c.j.Γ c.j.e1 c.j.e2 c.j.A := Cert.check_sound (Tables.deciders_spec hT) c k
    rw [hΓ, ← he, hA] at this; exact ⟨_, this⟩

/-- `natEnv`'s tables. -/
def natT : Tables where
  consts := [(``Nat.rec, ⟨1, recTy⟩), (``Nat.succ, ⟨0, .forallE nat nat⟩), (``Nat.zero, ⟨0, nat⟩),
    (``Nat, ⟨0, .sort (.succ .zero)⟩)]
  rules := [iotaSucc, iotaZero]
  inducts := [(``Nat, (natDecl, 0))]

theorem natEnv_tables : TablesFor natEnv natT := by
  refine ⟨fun m => ?_, fun df => ?_, fun m => ?_⟩
  · simp only [natEnv, envI, envR, envS, envZ, envN, withConst, VEnv.addDefEq, VEnv.empty, natT,
      tlookup]
    by_cases h1 : m = ``Nat.rec <;> by_cases h2 : m = ``Nat.succ <;> by_cases h3 : m = ``Nat.zero <;>
      by_cases h4 : m = ``Nat <;> simp_all [eq_comm]
  · show _ ∨ _ ∨ False ↔ _
    simp [natT]
  · simp only [natEnv, natT, ilookup]
    by_cases h : m = ``Nat
    · subst h; rfl
    · rw [ite_eq_right h]
      have : natDecl.types.findIdx? (·.name == m) = none := by
        rw [List.findIdx?_eq_none_iff]; simp [natDecl, Ne.symm h]
      rw [this]; rfl
end Incomplete
