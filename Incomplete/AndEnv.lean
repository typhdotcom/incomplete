import Incomplete.EqEnv

/-!
# `natEnv` with `And`

`andDecl` is Lean's `And : Prop → Prop → Prop` with `And.intro`, a structure with two proof
fields, so all three projection rules apply to it; `andEnv` adds it to `natEnv`.
-/

namespace Lean4Lean.Incomplete
open VExpr VEnv

def andTyE : VExpr := .forallE (.sort .zero) (.forallE (.sort .zero) (.sort .zero))
def introTyE : VExpr := .forallE (.sort .zero) (.forallE (.sort .zero) (.forallE (.bvar 1)
  (.forallE (.bvar 1) (.appN (.const ``And []) [.bvar 3, .bvar 2]))))

def introC : VConstructor :=
  ⟨``And.intro, introTyE, [⟨.bvar 1, .zero, none⟩, ⟨.bvar 1, .zero, none⟩], []⟩
def andT : VInductiveType := ⟨``And, andTyE, [], [introC], none⟩
def andDecl : VInductDecl := ⟨0, [.sort .zero, .sort .zero], .zero, [andT], false, true, false, []⟩

/-- The binders of `And.rec` up to its minor premise. -/
def andRecBinders : List VExpr :=
  [.sort .zero, .sort .zero,
    .forallE (.appN (.const ``And []) [.bvar 1, .bvar 0]) (.sort (.param 0)),
    .forallE (.bvar 2) (.forallE (.bvar 2)
      (.app (.bvar 2) (.appN (.const ``And.intro []) [.bvar 4, .bvar 3, .bvar 1, .bvar 0])))]

def andRecTy : VExpr :=
  .foralls andRecBinders (.forallE (.appN (.const ``And []) [.bvar 3, .bvar 2]) (.app (.bvar 2) (.bvar 0)))

def andIntroApp : VExpr := .appN (.const ``And.intro []) [.bvar 5, .bvar 4, .bvar 1, .bvar 0]

def andIota : VDefEq where
  uvars := 1
  lhs := .lams (andRecBinders ++ [.bvar 3, .bvar 3])
    (.appN (.const ``And.rec [.param 0]) [.bvar 5, .bvar 4, .bvar 3, .bvar 2, andIntroApp])
  rhs := .lams (andRecBinders ++ [.bvar 3, .bvar 3]) (.appN (.bvar 2) [.bvar 1, .bvar 0])
  type := .foralls (andRecBinders ++ [.bvar 3, .bvar 3]) (.app (.bvar 3) andIntroApp)

theorem andDecl_largeElim : andDecl.LargeElim := rfl

theorem andDecl_recConsts : andDecl.recConsts = [(``And.rec, ⟨1, andRecTy⟩)] := by
  simp only [VInductDecl.recConsts, VInductDecl.recUVars, VInductDecl.recLevels,
    VInductDecl.motiveLevel, if_pos andDecl_largeElim]
  rfl

theorem andDecl_iotaRules : andDecl.iotaRules = [andIota] := by
  simp only [VInductDecl.iotaRules, VInductDecl.recUVars, VInductDecl.recLevels,
    VInductDecl.motiveLevel, if_pos andDecl_largeElim]
  rfl

def andEnvT : VEnv := withConst natEnv ``And ⟨0, andTyE⟩
def andEnvC : VEnv := withConst andEnvT ``And.intro ⟨0, introTyE⟩
def andEnvR : VEnv := withConst andEnvC ``And.rec ⟨1, andRecTy⟩
def andEnvI : VEnv := andEnvR.addDefEq andIota

def andEnv : VEnv :=
  { andEnvI with inducts := fun n => match andDecl.types.findIdx? (·.name == n) with
    | some t => some (andDecl, t)
    | none => andEnvI.inducts n }

theorem addInduct_andDecl : natEnv.addInduct andDecl = some andEnv := by
  simp only [VEnv.addInduct, andDecl_recConsts, andDecl_iotaRules, Option.bind_eq_bind]
  rfl

theorem and_typeConsts_add : natEnv.addConstList andDecl.typeConsts = some andEnvT := rfl
theorem and_ctorConsts_add : andEnvT.addConstList andDecl.ctorConsts = some andEnvC := rfl
theorem and_recConsts_add : andEnvC.addConstList andDecl.recConsts = some andEnvR := by
  rw [andDecl_recConsts]; rfl

theorem andRecTy_wf : VConstant.WF andEnvC ⟨1, andRecTy⟩ := by
  have : andEnvC.constants ``And = some ⟨0, andTyE⟩ := rfl
  have : andEnvC.constants ``And.intro = some ⟨0, introTyE⟩ := rfl
  unfold VConstant.WF andRecTy andRecBinders
  simp only [VExpr.foralls, VExpr.appN]
  exact ⟨_, by unfold andTyE introTyE at *; type_tac⟩

theorem andIota_wf : andIota.WF andEnvR := by
  have : andEnvR.constants ``And = some ⟨0, andTyE⟩ := rfl
  have : andEnvR.constants ``And.intro = some ⟨0, introTyE⟩ := rfl
  have : andEnvR.constants ``And.rec = some ⟨1, andRecTy⟩ := rfl
  unfold andIota andRecBinders andIntroApp andRecTy andTyE introTyE at *
  constructor <;> simp only [VExpr.lams, VExpr.foralls, VExpr.appN, List.cons_append,
    List.nil_append] at * <;> type_tac

theorem andDecl_generatedWF : andDecl.GeneratedWF natEnv := by
  intro envT envC envR hT hC hR
  cases hT.symm.trans and_typeConsts_add
  cases hC.symm.trans and_ctorConsts_add
  cases hR.symm.trans and_recConsts_add
  rw [andDecl_recConsts, andDecl_iotaRules]
  refine ⟨fun p hp => ?_, fun df hdf => ?_⟩
  · simp only [List.mem_singleton] at hp; subst hp; exact andRecTy_wf
  · simp only [List.mem_singleton] at hdf; subst hdf; exact andIota_wf

theorem keptLiftBy_zero_inv (P : Nat → Prop) (A : VExpr) :
    VConstructor.strippedTypeBy P 0 A = A := by
  simp [VConstructor.strippedTypeBy, VConstructor.keptLiftBy, Lift.inv]

theorem introTy_binders {ps Ds : List VExpr} {B : VExpr} (h : introTyE = .foralls (ps ++ Ds) B)
    (hl : ps.length = 2) : ∀ (k : Nat) (D : VExpr), Ds[k]? = some D → D = .bvar 1 := by
  rcases ps with _ | ⟨p1, _ | ⟨p2, _ | ⟨p3, ps⟩⟩⟩ <;> simp at hl
  intro k D hD
  rcases Ds with _ | ⟨D1, _ | ⟨D2, _ | ⟨D3, Ds⟩⟩⟩
  · simp at hD
  · simp only [introTyE, List.cons_append, List.nil_append, VExpr.foralls, forallE.injEq] at h
    rcases k with _ | k <;> simp at hD; exact hD ▸ h.2.2.1.symm
  · simp only [introTyE, List.cons_append, List.nil_append, VExpr.foralls, forallE.injEq] at h
    rcases k with _ | _ | k <;> simp at hD
    · exact hD ▸ h.2.2.1.symm
    · exact hD ▸ h.2.2.2.1.symm
  · simp [introTyE, VExpr.foralls, VExpr.appN] at h

theorem andDecl_wf : andDecl.WF natEnv where
  nonempty := by simp [andDecl]
  level := trivial
  params := .cons ⟨_, HasType.sort (show VLevel.WF 0 .zero by decide)⟩
    (.cons ⟨_, HasType.sort (show VLevel.WF 0 .zero by decide)⟩ .nil)
  types T hT := by
    simp only [andDecl, List.mem_singleton] at hT; subst hT
    exact ⟨⟨_, by unfold andT andTyE; type_tac⟩, rfl⟩
  indices T hT := by
    simp only [andDecl, VInductDecl.allTypes, List.append_nil, List.mem_singleton] at hT
    subst hT; exact .nil
  aux T hT := by simp [andDecl] at hT
  ctors env' h' T hT := by
    cases h'.symm.trans and_typeConsts_add
    have : andEnvT.constants ``And = some ⟨0, andTyE⟩ := rfl
    simp only [andDecl, VInductDecl.allTypes, List.append_nil, List.mem_singleton] at hT
    subst hT
    refine ⟨⟨.nil, ⟨_, by unfold andT andTyE; type_tac⟩⟩, fun c hc => ?_⟩
    simp only [andT, List.mem_singleton] at hc; subst hc
    have h1 : andEnvT.HasType 0 [.sort .zero, .sort .zero] (.bvar 1) (.sort .zero) :=
      HasType.bvar (.succ .zero)
    have h2 : andEnvT.HasType 0 [.bvar 1, .sort .zero, .sort .zero] (.bvar 1) (.sort .zero) :=
      HasType.bvar (.succ .zero)
    have h0 : andEnvT.HasType 0 [.sort .zero, .sort .zero] (.bvar 0) (.sort .zero) :=
      HasType.bvar .zero
    refine ⟨⟨_, by unfold introC introTyE andTyE at *; type_tac⟩,
      ⟨[.sort .zero, .sort .zero], [.bvar 1, .bvar 1], rfl,
        .cons ⟨_, HasType.sort (show VLevel.WF 0 .zero by decide)⟩
          (.cons ⟨_, HasType.sort (show VLevel.WF 0 .zero by decide)⟩ .nil),
        .cons ⟨_, h1⟩ h1 trivial ⟨.zero, h1, .inl rfl⟩ (fun _ => .none ⟨_, h1⟩ rfl) trivial
          (.cons ⟨_, h2⟩ h2 trivial ⟨.zero, h2, .inl rfl⟩ (fun _ => .none ⟨_, h2⟩ rfl) trivial .nil),
        fun k D f hD hf j hs => ?_, fun P k hk _ => ?_⟩, ⟨rfl, rfl⟩,
      fun ps Ds B hc hl k D f hD hf => ?_⟩
    · rcases k with _ | _ | k <;> simp [introC] at hD hf <;> subst hD hf <;> exact hs
    · have hk' : k = 0 ∨ k = 1 := by simp [introC] at hk; omega
      rcases hk' with rfl | rfl
      · refine ⟨fun f hf => ?_, fun D f hD hf _ => ?_⟩
        · simp only [introC, List.getElem?_cons_zero, Option.some.injEq] at hf
          subst hf
          simp only [VConstructor.keptFieldsBy, List.range_zero, List.filter_nil, List.map_nil,
            List.reverse_nil, List.nil_append, keptLiftBy_zero_inv]
          exact h1
        · simp only [introC, List.getElem?_cons_zero, Option.some.injEq] at hD hf
          subst hD hf
          simp only [VConstructor.keptFieldsBy, List.range_zero, List.filter_nil, List.map_nil,
            List.reverse_nil, List.nil_append, keptLiftBy_zero_inv]
          exact ⟨_, h1⟩
      · have key : ∀ f : VField, introC.fields[1]? = some f →
            andEnvT.HasType 0 ((introC.keptFieldsBy P 1).reverse ++ [.sort .zero, .sort .zero])
              (VConstructor.strippedTypeBy P 1 f.type) (.sort f.level) := by
          intro f hf
          simp only [introC, List.getElem?_cons_succ, List.getElem?_cons_zero,
            Option.some.injEq] at hf
          subst hf
          by_cases hP : P 0
          · simp [VConstructor.keptFieldsBy, VConstructor.strippedTypeBy,
              VConstructor.keptLiftBy, hP, Lift.inv]
            exact h0
          · simp [VConstructor.keptFieldsBy, VConstructor.strippedTypeBy,
              VConstructor.keptLiftBy, hP, Lift.inv, introC]
            exact h2
        refine ⟨key, fun D f hD hf _ => ?_⟩
        simp only [introC, List.getElem?_cons_succ, List.getElem?_cons_zero,
          Option.some.injEq] at hD hf
        subst hD
        have := key f (by simp [introC, hf])
        rw [← hf] at this ⊢
        exact ⟨_, this⟩
    · have := introTy_binders hc hl k D hD
      rcases k with _ | _ | k <;> simp [introC] at hf <;> subst hf this <;> exact .refl
  isRec _ T hT c hc f hf := by
    simp only [andDecl, VInductDecl.allTypes, List.append_nil, List.mem_singleton] at hT
    subst hT; simp only [andT, List.mem_singleton] at hc; subst hc
    simp only [introC, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl <;> rfl
  largeElim _ := .inr ⟨andT, rfl, rfl, .inr ⟨introC, rfl, fun k f hf hz => by
    rcases k with _ | _ | k <;> simp [introC] at hf <;> subst hf <;> exact absurd rfl hz⟩⟩

theorem andEnv_wf : andEnv.WF := by
  obtain ⟨ds, h⟩ := natEnv_wf
  exact ⟨_, .decl (.induct andDecl_wf andDecl_generatedWF addInduct_andDecl) h⟩

theorem natEnv_le_andEnv : natEnv ≤ andEnv := VEnv.addInduct_le addInduct_andDecl

/-- **Incompleteness of `natEnv` with `And`.** -/
theorem andEnv_incomplete_of_consistent (hC : Consistent andEnv) :
    ∃ d : PR, ¬d.Halts d.code ∧ ¬Provable andEnv (notHalts d d.code) ∧
      (HaltsSound andEnv → ¬Provable andEnv (halts d d.code)) :=
  incomplete_of_wf andEnv andEnv_wf natEnv_le_andEnv hC

end Lean4Lean.Incomplete
