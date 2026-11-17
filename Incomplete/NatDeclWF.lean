import Incomplete.NatWF
import Lean4Lean.Theory.Typing.Env

/-!
# `natEnv` is well formed

`natDecl` passes `VInductDecl.WF` in the empty environment, and what `addInduct` generates from
it is well typed, so `natEnv` is a `VEnv.WF` environment: the one-declaration development
`[.induct natDecl]`.
-/

namespace Lean4Lean.Incomplete
open VExpr VEnv

private theorem natT' {env : VEnv} (h : env.constants ``Nat = some ⟨0, .sort (.succ .zero)⟩) :
    env.HasType 0 Γ nat (.sort (.succ .zero)) :=
  .const' h (by simp) rfl rfl

theorem typeConsts_add : VEnv.empty.addConstList natDecl.typeConsts = some envN := rfl
theorem ctorConsts_add : envN.addConstList natDecl.ctorConsts = some envS := rfl
theorem recConsts_add : envS.addConstList natDecl.recConsts = some envR := by
  rw [natDecl_recConsts]; rfl

theorem natDecl_wf : natDecl.WF .empty where
  nonempty := by simp [natDecl]
  level := trivial
  params := .nil
  types T hT := by
    simp only [natDecl, List.mem_singleton] at hT; subst hT
    exact ⟨⟨_, HasType.sort trivial⟩, rfl⟩
  indices T hT := by
    simp only [natDecl, VInductDecl.allTypes, List.append_nil, List.mem_singleton] at hT
    subst hT; exact .nil
  aux T hT := by simp [natDecl] at hT
  ctors env' h' T hT := by
    have e : env' = envN := Option.some.inj (h'.symm.trans typeConsts_add)
    subst e
    have hN : envN.constants ``Nat = some ⟨0, .sort (.succ .zero)⟩ := rfl
    simp only [natDecl, VInductDecl.allTypes, List.append_nil, List.mem_singleton] at hT
    subst hT
    refine ⟨⟨.nil, ⟨_, HasType.sort trivial⟩⟩, fun c hc => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · refine ⟨⟨_, natT' hN⟩, ⟨[], [], rfl, .nil, .nil, by simp, fun P k hk => by simp at hk⟩,
        ⟨rfl, rfl⟩, fun ps Ds B _ _ k D f _ hf => by simp at hf⟩
    · refine ⟨⟨_, HasType.forallE (natT' hN) (natT' hN)⟩,
        ⟨[], [nat], rfl, .nil, ?_, ?_, ?_⟩, ⟨rfl, rfl⟩, ?_⟩
      · refine .cons ⟨_, natT' hN⟩ (natT' hN) trivial ⟨_, natT' hN, .inr (VLevel.le_refl _)⟩
          (fun _ => .app (T := natDecl.types[0]) (j := 0) rfl rfl ⟨_, natT' hN⟩ rfl)
          ⟨_, rfl, rfl, ⟨_, natT' hN⟩, rfl, rfl⟩ .nil
      · intro k D f hD hf j h
        cases k with
        | zero => simp at hD hf; subst hD hf; exact h
        | succ k => simp at hf
      · intro P k hk _
        have : k = 0 := by simpa using hk
        subst this
        refine ⟨fun f hf => ?_, fun D f hD hf _ => ?_⟩
        · simp at hf; subst hf; exact natT' hN
        · simp at hD hf; subst hD hf; exact ⟨_, natT' hN⟩
      · intro ps Ds B e hl k D f hD hf
        cases ps with
        | cons => simp [natDecl] at hl
        | nil =>
          cases k with
          | succ k => simp at hf
          | zero =>
            cases Ds with
            | nil => simp at hD
            | cons D' Ds =>
              simp at e hD hf; subst hD hf; rw [← e.1]; exact .refl
  isRec h := by simp [natDecl] at h
  largeElim _ := .inl fun _ => Nat.succ_ne_zero _

theorem natDecl_generatedWF : natDecl.GeneratedWF .empty := by
  intro envT envC envR hT hC hR
  cases hT.symm.trans typeConsts_add
  cases hC.symm.trans ctorConsts_add
  cases hR.symm.trans recConsts_add
  rw [natDecl_recConsts]
  refine ⟨fun p hp => ?_, fun df hdf => ?_⟩
  · simp only [List.mem_singleton] at hp; subst hp; exact natConsts_envS.recTy
  · have hRc : NatConsts envR := natConsts_envS.mono (addConst_le (addConst_eq rfl))
    rw [natDecl_iotaRules] at hdf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hdf
    rcases hdf with rfl | rfl
    · exact iotaZero_wf hRc rfl
    · exact iotaSucc_wf hRc rfl

/-- `natEnv` is the environment of the one-declaration development `[.induct natDecl]`. -/
theorem natEnv_wf : natEnv.WF :=
  ⟨_, .decl (.induct natDecl_wf natDecl_generatedWF addInduct_natDecl) .empty⟩

end Lean4Lean.Incomplete
