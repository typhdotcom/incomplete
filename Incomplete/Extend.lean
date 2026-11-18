import Incomplete.Final
import Lean4Lean.Theory.Typing.Projection

/-!
# Every well-formed environment is checkable

Each declaration extends the tables: `VEnv.addInduct` puts the block's constants, iota rules and
types in front, and the other declarations their constants and rules. So `VEnv.WF.checkable`, and
incompleteness holds of every consistent well-formed extension of `natEnv` (`incomplete_of_wf`),
in particular of one whose declarations include `Nat`'s (`incomplete_of_wf'`).
-/

namespace Incomplete
open Lean4Lean

/-- First match in `l`, falling back to `f`. -/
def tlookupD : List (Name × VConstant) → (Name → Option VConstant) → Name → Option VConstant
  | [], f, m => f m
  | (n, ci) :: r, f, m => if m = n then some ci else tlookupD r f m

theorem tlookupD_append (l₁ l₂ : List (Name × VConstant)) (f : Name → Option VConstant) (m : Name) :
    tlookupD (l₁ ++ l₂) f m = tlookupD l₁ (tlookupD l₂ f) m := by
  induction l₁ with
  | nil => rfl
  | cons e r ih => obtain ⟨n, ci⟩ := e; simp only [List.cons_append, tlookupD, ih]

theorem tlookupD_tlookup (l t : List (Name × VConstant)) (m : Name) :
    tlookupD l (tlookup t) m = tlookup (l ++ t) m := by
  induction l with
  | nil => rfl
  | cons e r ih => obtain ⟨n, ci⟩ := e; simp only [List.cons_append, tlookupD, tlookup, ih]

theorem addConstList_constants : ∀ {env env' : VEnv} {cs : List (Name × VConstant)},
    env.addConstList cs = some env' → ∀ m, env'.constants m = tlookupD cs.reverse env.constants m
  | _, _, [], h, m => by cases h; rfl
  | env, env', (n, ci) :: cs, h, m => by
    simp only [VEnv.addConstList, List.foldlM_cons, Option.bind_eq_bind,
      Option.bind_eq_some_iff] at h
    obtain ⟨env₁, h1, h2⟩ := h
    rw [addConstList_constants h2, List.reverse_cons, tlookupD_append]
    congr 1; funext m'
    unfold VEnv.addConst at h1; split at h1 <;> cases h1
    simp only [tlookupD, eq_comm]

theorem addConstList_defeqs : ∀ {env env' : VEnv} {cs : List (Name × VConstant)},
    env.addConstList cs = some env' → env'.defeqs = env.defeqs
  | _, _, [], h => by cases h; rfl
  | env, env', (n, ci) :: cs, h => by
    simp only [VEnv.addConstList, List.foldlM_cons, Option.bind_eq_bind,
      Option.bind_eq_some_iff] at h
    obtain ⟨env₁, h1, h2⟩ := h
    rw [addConstList_defeqs h2]
    unfold VEnv.addConst at h1; split at h1 <;> cases h1; rfl

theorem addConstList_inducts : ∀ {env env' : VEnv} {cs : List (Name × VConstant)},
    env.addConstList cs = some env' → env'.inducts = env.inducts
  | _, _, [], h => by cases h; rfl
  | env, env', (n, ci) :: cs, h => by
    simp only [VEnv.addConstList, List.foldlM_cons, Option.bind_eq_bind,
      Option.bind_eq_some_iff] at h
    obtain ⟨env₁, h1, h2⟩ := h
    rw [addConstList_inducts h2]
    unfold VEnv.addConst at h1; split at h1 <;> cases h1; rfl

theorem addDefEqList_constants : ∀ (env : VEnv) (dfs : List VDefEq),
    (env.addDefEqList dfs).constants = env.constants
  | _, [] => rfl
  | env, df :: dfs => addDefEqList_constants (env.addDefEq df) dfs

theorem addDefEqList_inducts : ∀ (env : VEnv) (dfs : List VDefEq),
    (env.addDefEqList dfs).inducts = env.inducts
  | _, [] => rfl
  | env, df :: dfs => addDefEqList_inducts (env.addDefEq df) dfs

theorem addDefEqList_defeqs : ∀ (env : VEnv) (dfs : List VDefEq) (x : VDefEq),
    (env.addDefEqList dfs).defeqs x ↔ x ∈ dfs ∨ env.defeqs x
  | _, [], x => by simp [VEnv.addDefEqList]
  | env, df :: dfs, x => by
    show (VEnv.addDefEqList (env.addDefEq df) dfs).defeqs x ↔ _
    rw [addDefEqList_defeqs]
    simp only [VEnv.addDefEq, List.mem_cons]
    constructor
    · rintro (h | h | h) <;> simp_all
    · rintro ((h | h) | h) <;> simp_all

/-- The block entries for the types `l` of `d`, numbered from `i`. -/
def blockEntries (d : VInductDecl) : List VInductiveType → Nat → List (Name × (VInductDecl × Nat))
  | [], _ => []
  | T :: l, i => (T.name, (d, i)) :: blockEntries d l (i + 1)

theorem ilookup_blockEntries (d : VInductDecl) (r : List (Name × (VInductDecl × Nat))) (n : Name) :
    ∀ (l : List VInductiveType) (i : Nat), ilookup (blockEntries d l i ++ r) n =
      match l.findIdx? (·.name == n) with
      | some t => some (d, i + t)
      | none => ilookup r n
  | [], i => by simp [blockEntries]
  | T :: l, i => by
    simp only [blockEntries, List.cons_append, ilookup, List.findIdx?_cons]
    by_cases h : n = T.name
    · subst h; simp only [beq_self_eq_true, ↓reduceIte, Nat.add_zero]
    · rw [ite_eq_right h, ilookup_blockEntries d r n l (i + 1)]
      have : (T.name == n) = false := by
        rw [beq_eq_false_iff_ne]; exact fun e => h e.symm
      rw [this]; simp only [Bool.false_eq_true, ↓reduceIte]
      cases List.findIdx? (fun x => x.name == n) l with
      | none => rfl
      | some t => show some (d, i + 1 + t) = some (d, i + (t + 1)); rw [Nat.add_assoc, Nat.add_comm 1 t]

/-- The tables after adding the block `d`. -/
noncomputable def Tables.addInduct (T : Tables) (d : VInductDecl) : Tables where
  consts := d.recConsts.reverse ++ d.ctorConsts.reverse ++ d.typeConsts.reverse ++ T.consts
  rules := d.iotaRules ++ T.rules
  inducts := blockEntries d d.types 0 ++ T.inducts

theorem TablesFor.addInduct {env env' : VEnv} {T : Tables} {d : VInductDecl}
    (hT : TablesFor env T) (h : env.addInduct d = some env') : TablesFor env' (T.addInduct d) := by
  simp only [VEnv.addInduct, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨e1, h1, e2, h2, e3, h3, h4⟩ := h
  refine ⟨fun m => ?_, fun x => ?_, fun m => ?_⟩
  · have c1 : e1.constants = tlookupD d.typeConsts.reverse env.constants :=
      funext (addConstList_constants h1)
    have c2 : e2.constants = tlookupD d.ctorConsts.reverse e1.constants :=
      funext (addConstList_constants h2)
    have c3 : e3.constants = tlookupD d.recConsts.reverse e2.constants :=
      funext (addConstList_constants h3)
    have c0 : env.constants = tlookup T.consts := funext hT.consts
    have tt : ∀ l t, tlookupD l (tlookup t) = tlookup (l ++ t) := fun l t =>
      funext (tlookupD_tlookup l t)
    rw [VEnv.addBlock_constants h4, addDefEqList_constants, c3, c2, c1, c0, tt, tt, tt]
    simp [Tables.addInduct, List.append_assoc]
  · rw [VEnv.addBlock_defeqs h4, addDefEqList_defeqs, addConstList_defeqs h3,
      addConstList_defeqs h2, addConstList_defeqs h1, hT.rules]
    simp [Tables.addInduct]
  · have hi : (e3.addDefEqList d.iotaRules).inducts = env.inducts := by
      rw [addDefEqList_inducts, addConstList_inducts h3, addConstList_inducts h2,
        addConstList_inducts h1]
    unfold VEnv.addBlock at h4; split at h4 <;> cases h4
    show (match d.types.findIdx? (·.name == m) with
      | some t => some (d, t) | none => (e3.addDefEqList d.iotaRules).inducts m) = _
    simp only [Tables.addInduct, ilookup_blockEntries, Nat.zero_add]
    split
    · rfl
    · rw [hi, hT.inducts]

/-! ### Every declaration -/

theorem TablesFor.addConstList {env env' : VEnv} {T : Tables} {cs : List (Name × VConstant)}
    (hT : TablesFor env T) (h : env.addConstList cs = some env') :
    TablesFor env' { T with consts := cs.reverse ++ T.consts } := by
  refine ⟨fun m => ?_, fun x => ?_, fun m => ?_⟩
  · rw [addConstList_constants h, funext hT.consts, tlookupD_tlookup]
  · rw [addConstList_defeqs h, hT.rules]
  · rw [addConstList_inducts h, hT.inducts]

theorem TablesFor.addDefEqList {env : VEnv} {T : Tables} (dfs : List VDefEq)
    (hT : TablesFor env T) : TablesFor (env.addDefEqList dfs) { T with rules := dfs ++ T.rules } := by
  refine ⟨fun m => ?_, fun x => ?_, fun m => ?_⟩
  · rw [addDefEqList_constants, hT.consts]
  · rw [addDefEqList_defeqs, hT.rules, List.mem_append]
  · rw [addDefEqList_inducts, hT.inducts]

theorem addConst_list {env : VEnv} {n : Name} {ci : VConstant} :
    env.addConst n ci = env.addConstList [(n, ci)] := by
  simp only [VEnv.addConstList, List.foldlM_cons, List.foldlM_nil, Option.bind_eq_bind]
  cases env.addConst n ci <;> rfl

theorem TablesFor.addConst {env env' : VEnv} {T : Tables} {n : Name} {ci : VConstant}
    (hT : TablesFor env T) (h : env.addConst n ci = some env') : ∃ T', TablesFor env' T' :=
  ⟨_, hT.addConstList (addConst_list ▸ h)⟩

theorem TablesFor.addDefEq {env : VEnv} {T : Tables} (df : VDefEq) (hT : TablesFor env T) :
    ∃ T', TablesFor (env.addDefEq df) T' :=
  ⟨_, hT.addDefEqList [df]⟩

theorem TablesFor.mutualDef {env env' : VEnv} {T : Tables} {cis : List VDefVal}
    (hT : TablesFor env T) (h : env.addConsts cis = some env') :
    ∃ T', TablesFor (env'.addDefEqs cis) T' := by
  have e1 : env.addConsts cis = env.addConstList (cis.map fun ci => (ci.name, ci.toVConstant)) := by
    simp only [VEnv.addConsts, VEnv.addConstList, List.foldlM_map]
  have e2 : env'.addDefEqs cis = env'.addDefEqList (cis.map (·.toDefEq)) := by
    simp only [VEnv.addDefEqs, VEnv.addDefEqList, List.foldl_map]
  rw [e2]
  exact ⟨_, (hT.addConstList (e1 ▸ h)).addDefEqList _⟩

theorem TablesFor.empty : TablesFor .empty ⟨[], [], []⟩ :=
  ⟨fun _ => rfl, fun _ => by simp [VEnv.empty], fun _ => rfl⟩

theorem TablesFor.decl {env env' : VEnv} {D : VDecl} {T : Tables} (hT : TablesFor env T)
    (H : VDecl.WF env D env') : ∃ T', TablesFor env' T' := by
  cases H with
  | «axiom» _ h | «opaque» _ h => exact hT.addConst h
  | «def» _ h => obtain ⟨T', h'⟩ := hT.addConst h; exact h'.addDefEq _
  | mutualDef _ h _ => exact hT.mutualDef h
  | «example» => exact ⟨T, hT⟩
  | quot _ h =>
    simp only [VEnv.addQuot, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at h
    obtain ⟨_, h1, _, h2, _, h3, _, h4, rfl⟩ := h
    obtain ⟨_, t1⟩ := hT.addConst h1
    obtain ⟨_, t2⟩ := t1.addConst h2
    obtain ⟨_, t3⟩ := t2.addConst h3
    obtain ⟨_, t4⟩ := t3.addConst h4
    exact t4.addDefEq _
  | induct _ _ h => exact ⟨_, hT.addInduct h⟩

/-- **Every well-formed environment is checkable.** -/
theorem _root_.Lean4Lean.VEnv.WF.checkable {env : VEnv} (h : env.WF) : Checkable env := by
  refine ⟨?_, h.ordered⟩
  obtain ⟨ds, H⟩ := h
  induction H with
  | empty => exact ⟨_, .empty⟩
  | decl hd _ ih => obtain ⟨T, hT⟩ := ih; exact hT.decl hd

/-- **Incompleteness.** A consistent well-formed extension of `natEnv` does not prove the true
non-halting sentence `notHalts d ⌜d⌝` of some machine `d` on its own number; if the theory's
proofs of `halts` sentences are sound (`HaltsSound`), it does not refute it either. -/
theorem incomplete_of_wf (env : VEnv) (hwf : env.WF) (hext : natEnv ≤ env) (hC : Consistent env) :
    ∃ d : PR, ¬d.Halts d.code ∧ ¬Provable env (notHalts d d.code) ∧
      (HaltsSound env → ¬Provable env (halts d d.code)) :=
  incomplete_of_consistent env hext hwf.checkable hC

/-! ### Declaring `Nat` gives an extension of `natEnv` -/

theorem tlookupD_mono {f g : Name → Option VConstant} (hfg : ∀ m a, f m = some a → g m = some a) :
    ∀ (l : List (Name × VConstant)) m a, tlookupD l f m = some a → tlookupD l g m = some a
  | [], m, a, h => hfg m a h
  | (n, ci) :: r, m, a, h => by
    simp only [tlookupD] at h ⊢
    split
    · rwa [ite_eq_left ‹_›] at h
    · rw [ite_eq_right ‹_›] at h; exact tlookupD_mono hfg r m a h

/-- A block added to the empty environment is contained in it added to any environment. -/
theorem addInduct_empty_le {d : VInductDecl} {e env env' : VEnv}
    (h0 : VEnv.empty.addInduct d = some e) (h : env.addInduct d = some env') : e ≤ env' := by
  simp only [VEnv.addInduct, Option.bind_eq_bind, Option.bind_eq_some_iff] at h0 h
  obtain ⟨a1, g1, a2, g2, a3, g3, g4⟩ := h0
  obtain ⟨e1, h1, e2, h2, e3, h3, h4⟩ := h
  have cs : ∀ {x x1 x2 x3 : VEnv},
      x.addConstList d.typeConsts = some x1 → x1.addConstList d.ctorConsts = some x2 →
      x2.addConstList d.recConsts = some x3 → ∀ m,
      x3.constants m = tlookupD d.recConsts.reverse (tlookupD d.ctorConsts.reverse
        (tlookupD d.typeConsts.reverse x.constants)) m := by
    intro x x1 x2 x3 k1 k2 k3 m
    rw [addConstList_constants k3, funext (addConstList_constants k2),
      funext (addConstList_constants k1)]
  refine ⟨fun {m a} hm => ?_, fun {x} hx => ?_, fun {m b} hm => ?_⟩
  · rw [VEnv.addBlock_constants g4, addDefEqList_constants, cs g1 g2 g3] at hm
    rw [VEnv.addBlock_constants h4, addDefEqList_constants, cs h1 h2 h3]
    exact tlookupD_mono (tlookupD_mono (tlookupD_mono (fun _ _ e => by cases e) _) _) _ m a hm
  · rw [VEnv.addBlock_defeqs g4, addDefEqList_defeqs] at hx
    rw [VEnv.addBlock_defeqs h4, addDefEqList_defeqs]
    refine hx.imp_right fun e => ?_
    rw [addConstList_defeqs g3, addConstList_defeqs g2, addConstList_defeqs g1] at e
    exact e.elim
  · have hi : (e3.addDefEqList d.iotaRules).inducts = env.inducts := by
      rw [addDefEqList_inducts, addConstList_inducts h3, addConstList_inducts h2,
        addConstList_inducts h1]
    unfold VEnv.addBlock at g4 h4
    split at g4 <;> cases g4
    split at h4 <;> cases h4
    revert hm
    show (match d.types.findIdx? (·.name == m) with
      | some t => some (d, t) | none => (a3.addDefEqList d.iotaRules).inducts m) = _ →
      (match d.types.findIdx? (·.name == m) with
      | some t => some (d, t) | none => (e3.addDefEqList d.iotaRules).inducts m) = _
    split
    · exact id
    · rw [addDefEqList_inducts, addConstList_inducts g3, addConstList_inducts g2,
        addConstList_inducts g1]
      exact fun e => by cases e

/-- A well-formed environment whose declarations include `Nat`'s extends `natEnv`. -/
theorem natEnv_le_of_mem {ds : List VDecl} {env : VEnv} (H : env.WF' ds)
    (hm : .induct natDecl ∈ ds) : natEnv ≤ env := by
  induction H with
  | empty => simp at hm
  | decl hd _ ih =>
    rcases List.mem_cons.1 hm with rfl | hm
    · cases hd with | induct _ _ h => exact addInduct_empty_le addInduct_natDecl h
    · exact (ih hm).trans hd.le

/-- **Incompleteness**, for a consistent well-formed environment that declares `Nat`. -/
theorem incomplete_of_wf' {ds : List VDecl} {env : VEnv} (H : env.WF' ds)
    (hm : .induct natDecl ∈ ds) (hC : Consistent env) :
    ∃ d : PR, ¬d.Halts d.code ∧ ¬Provable env (notHalts d d.code) ∧
      (HaltsSound env → ¬Provable env (halts d d.code)) :=
  incomplete_of_wf env ⟨ds, H⟩ (natEnv_le_of_mem H hm) hC

/-! ### `natEnv`, and a definition over it -/

/-- **Incompleteness of `natEnv`.** -/
theorem natEnv_incomplete_of_consistent (hC : Consistent natEnv) :
    ∃ d : PR, ¬d.Halts d.code ∧ ¬Provable natEnv (notHalts d d.code) ∧
      (HaltsSound natEnv → ¬Provable natEnv (halts d d.code)) :=
  incomplete_of_wf natEnv natEnv_wf VEnv.LE.rfl hC

/-- `two : Nat := Nat.succ (Nat.succ Nat.zero)`. -/
def twoDef : VDefVal := ⟨⟨⟨0, nat⟩, `two⟩, lit 2⟩

def twoEnv : VEnv := (withConst natEnv `two ⟨0, nat⟩).addDefEq twoDef.toDefEq

theorem twoEnv_wf : twoEnv.WF := by
  obtain ⟨ds, h⟩ := natEnv_wf
  refine ⟨_, .decl (.def ?_ (addConst_eq rfl)) h⟩
  exact hasNat_natEnv.toNatConsts.litT 2

theorem natEnv_le_twoEnv : natEnv ≤ twoEnv :=
  (VEnv.addConst_le (addConst_eq (env := natEnv) (n := `two) (ci := ⟨0, nat⟩) rfl)).trans
    VEnv.addDefEq_le

theorem twoEnv_incomplete_of_consistent (hC : Consistent twoEnv) :
    ∃ d : PR, ¬d.Halts d.code ∧ ¬Provable twoEnv (notHalts d d.code) ∧
      (HaltsSound twoEnv → ¬Provable twoEnv (halts d d.code)) :=
  incomplete_of_wf twoEnv twoEnv_wf natEnv_le_twoEnv hC

end Incomplete
