import Incomplete.Obj.Chaitin
import Incomplete.BProvLogic

/-!
# Chaitin's incompleteness theorem

Descriptions are functional: codes with the same number compute the same function
(`PR.eval_eq_of_code`, through the consistency of the fragment of `clEnv`), so each code
describes at most one number (`describes_unique`). Hence for every `L` at most `L + 1` numbers
are not `L`-complex (`not_complex_length_le`), and every number from some point on is
(`isComplex_eventually`); every number has a description (`describes_exists`). `Complex L n`
expresses `IsComplex L n`: in a consistent theory a proof of it makes it true
(`complex_true_of_provable`), and a description `c ≤ L` of `n` refutes it (`complex_refute`).

Chaitin's theorem: a consistent well-formed extension of `natEnv` proves `Complex L n` for no
`n`, at `L` the code of Chaitin's machine for its checker (`chaitin`); the same holds with no
hypotheses for the fragment of `clEnv` (`chaitin_unconditional`).
-/

namespace Incomplete
open Lean4Lean Obj PR

/-! ### Descriptions -/

/-- Codes with the same number compute the same function. -/
theorem PR.eval_eq_of_code {f g : PR} (h : f.code = g.code) (k x : Nat) :
    f.eval (val2 k x) = g.eval (val2 k x) := by
  have hfg : fn f = fn g := encExpr_inj h
  refine Classical.byContradiction fun hne => clEnv_bconsistent ?_
  have h1 := fn_lit (env := bounded clEnv) (Γ := []) f x k
  have h2 := fn_lit (env := bounded clEnv) (Γ := []) g x k
  rw [hfg] at h1
  exact (lit_ne hne).mp (Thm.trans (by otype) (by otype) (by otype)
    (Thm.symm (by otype) (by otype) h1) h2)

theorem PR.Outputs.unique {f : PR} {x n n' : Nat} (h : f.Outputs x n) (h' : f.Outputs x n') :
    n = n' := by
  obtain ⟨k, hk, hmin, rfl⟩ := h
  obtain ⟨k', hk', hmin', rfl⟩ := h'
  rcases Nat.lt_trichotomy k k' with hlt | rfl | hlt
  · exact absurd hk (hmin' k hlt)
  · rfl
  · exact absurd hk' (hmin k' hlt)

/-- **Each code describes at most one number.** -/
theorem describes_unique {c n n' : Nat} (h : Describes c n) (h' : Describes c n') : n = n' := by
  obtain ⟨f, hf, ho⟩ := h
  obtain ⟨g, hg, ⟨k, hk, hmin, hn⟩⟩ := h'
  have e : ∀ j, g.eval (val2 j c) = f.eval (val2 j c) :=
    fun j => PR.eval_eq_of_code (hg.trans hf.symm) j c
  exact ho.unique ⟨k, (e k) ▸ hk, fun j hj => (e j) ▸ hmin j hj, hn⟩

/-- The machine that outputs `n` at once: its first zero is `⟨n, 0⟩`. -/
def constM (n : Nat) : PR := eqz (var 0) (num (PR.pair n 0))

theorem constM_outputs (n x : Nat) : (constM n).Outputs x n := by
  refine ⟨PR.pair n 0, (eval_eqz _ _ _).2 (by simp [val2, eval_var]), fun j hj h => ?_, unpair1_pair _ _⟩
  have := (eval_eqz _ _ _).1 h
  simp [val2, eval_var] at this
  omega

/-- **Every number has a description.** -/
theorem describes_exists (n : Nat) : ∃ c, Describes c n :=
  ⟨(constM n).code, constM n, rfl, constM_outputs n _⟩

/-- **At most `L + 1` numbers are not `L`-complex.** -/
theorem not_complex_length_le (L : Nat) (ns : List Nat) (hnd : ns.Nodup)
    (hns : ∀ n ∈ ns, ¬IsComplex L n) : ns.length ≤ L + 1 := by
  have hd : ∀ n, ∃ c, n ∈ ns → c ≤ L ∧ Describes c n := fun n => by
    by_cases hn : n ∈ ns
    · obtain ⟨c, hc, hD⟩ : ∃ c, c ≤ L ∧ Describes c n :=
        Classical.byContradiction fun h => hns n hn fun c hc hD => h ⟨c, hc, hD⟩
      exact ⟨c, fun _ => ⟨hc, hD⟩⟩
    · exact ⟨0, fun h => absurd h hn⟩
  let g : Nat → Nat := fun n => Classical.choose (hd n)
  have hg : ∀ n ∈ ns, g n ≤ L ∧ Describes (g n) n := fun n hn => Classical.choose_spec (hd n) hn
  have hnd' : (ns.map g).Nodup := by
    unfold List.Nodup
    rw [List.pairwise_map]
    exact hnd.imp_of_mem fun ha hb hab e =>
      hab (describes_unique (hg _ ha).2 (e ▸ (hg _ hb).2))
  have hsub : ns.map g ⊆ List.range (L + 1) := fun c hc => by
    obtain ⟨n, hn, rfl⟩ := List.mem_map.1 hc
    exact List.mem_range.2 (Nat.lt_succ_of_le (hg n hn).1)
  simpa using hnd'.length_le_of_subset hsub

/-- **All but finitely many numbers are `L`-complex.** -/
theorem isComplex_eventually (L : Nat) : ∃ N, ∀ n, N ≤ n → IsComplex L n := by
  suffices h : ∀ m, ∃ N, ∀ n, N ≤ n → ∀ c < m, ¬Describes c n by
    obtain ⟨N, hN⟩ := h (L + 1)
    exact ⟨N, fun n hn c hc => hN n hn c (Nat.lt_succ_of_le hc)⟩
  intro m
  induction m with
  | zero => exact ⟨0, fun _ _ _ hc => absurd hc (Nat.not_lt_zero _)⟩
  | succ m ih =>
    obtain ⟨N, hN⟩ := ih
    by_cases h : ∃ n₀, Describes m n₀
    · obtain ⟨n₀, h₀⟩ := h
      refine ⟨max N (n₀ + 1), fun n hn c hc hD => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hc with hc | rfl
      · exact hN n (Nat.le_trans (Nat.le_max_left _ _) hn) c hc hD
      · have := describes_unique h₀ hD
        have := Nat.le_trans (Nat.le_max_right _ _) hn
        omega
    · refine ⟨N, fun n hn c hc hD => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hc with hc | rfl
      · exact hN n hn c hc hD
      · exact h ⟨n, hD⟩

/-! ### The sentence expresses complexity -/

section
variable {env : Typing} [E : ObjEnv env]

/-- A description `c ≤ L` of `n` refutes `Complex L n`. -/
theorem complex_refute {L n c : Nat} (hc : c ≤ L) (h : Describes c n) :
    Thm env [] (¬ₒ (Complex L n)) := by
  obtain ⟨f, hf, ho⟩ := h
  have hcl := (closedN_of_ty (complexTy (env := env) L n)).liftN_eq (n := 1) (Nat.zero_le 0)
  exact Thm.introH (complexTy L n) fun hC => by
    simp only [VExpr.lift, hcl] at hC
    exact
    Thm.absurd (complex_elim hc hf hC) (descS_of_outputs ho)

end

theorem complex_true_of_provable (env : VEnv) (hwf : env.WF) (hext : natEnv ≤ env)
    (hC : Consistent env) {L n : Nat} (h : Provable env (Complex L n)) : IsComplex L n :=
  have : ObjEnv env := .full (hasNat_natEnv.mono hext) hwf.ordered
  complex_true (env := env) hC h

/-! ### Chaitin's theorem -/

/-- **Chaitin's incompleteness theorem.** For every consistent well-formed extension of
`natEnv` and tables `T` for it, there is an `L` such that `Complex L n` is a closed proposition
for every `n`, true for all but at most `L + 1` numbers `n`, so for all `n` from some `N` on,
and provable for none. -/
theorem chaitin (env : VEnv) (hwf : env.WF) (hext : natEnv ≤ env) {T : Tables}
    (hT : TablesFor env T) (hC : Consistent env) :
    ∃ L, (∀ n, env.HasType 0 [] (Complex L n) (.sort .zero)) ∧
      (∀ ns : List Nat, ns.Nodup → (∀ n ∈ ns, ¬IsComplex L n) → ns.length ≤ L + 1) ∧
      (∃ N, ∀ n, N ≤ n → IsComplex L n) ∧ ∀ n, ¬Provable env (Complex L n) := by
  have : ObjEnv env := .full (hasNat_natEnv.mono hext) hwf.ordered
  refine ⟨(chaitinM (chkT T)).code, fun n => complexTy (env := env) _ n,
    not_complex_length_le _, isComplex_eventually _, chaitin_core (env := env) (fun ρ => eval_chkT ρ)
      (fun P k h => (chkNum_eq_zero hT P).1 ⟨k, h⟩) (fun P h => (chkNum_eq_zero hT P).2 h) hC⟩

/-- **Chaitin's theorem for the fragment of `clEnv`**, with no hypotheses. -/
theorem chaitin_unconditional :
    ∃ L, (∀ n, BDefEq clEnv [] (Complex L n) (Complex L n) (.sort .zero)) ∧
      (∀ ns : List Nat, ns.Nodup → (∀ n ∈ ns, ¬IsComplex L n) → ns.length ≤ L + 1) ∧
      (∃ N, ∀ n, N ≤ n → IsComplex L n) ∧ ∀ n, ¬BProvable clEnv (Complex L n) :=
  ⟨(chaitinM (bchkT clT)).code, fun n => complexTy (env := bounded clEnv) _ n,
    not_complex_length_le _, isComplex_eventually _, chaitin_core (env := bounded clEnv) (bchkT_computes clT)
      bchk_sound (fun _ h => bchkNum_complete clEnv_tables h) clEnv_bconsistent⟩

end Incomplete
