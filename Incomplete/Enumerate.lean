import Incomplete.CertNat
import Incomplete.Encode
import Incomplete.Main

/-!
# From the certificate checker to the diagonal machine

`DiagEnumerable natEnv` follows from two computability facts about concrete total functions:
a code deciding `checkProof` on numbered certificates and sentences (`CheckDecidable`), and a
code computing the number of the diagonal sentence `notHalts f ⌜f⌝` from `⌜f⌝`
(`DiagComputable`). The diagonal machine runs the second and feeds its result to the first.
-/

namespace Lean4Lean.Incomplete
open PR (pair)

/-- Some code checks proofs: given the number of a sentence `Q` in variable `0` and any number
`k` in variable `1`, it returns `0` only if `Q` is provable, and for a provable `Q` some `k`
makes it return `0`. -/
def CheckDecidable (env : VEnv) : Prop :=
  ∃ G : PR, (∀ Q k ρ, G.eval (vcons (encExpr Q) (vcons k ρ)) = 0 → Provable env Q) ∧
    ∀ Q, Provable env Q → ∃ k, ∀ ρ, G.eval (vcons (encExpr Q) (vcons k ρ)) = 0

/-- The number of `notHalts f n` as a function of the number of `fn f` and of `n`. -/
def diagNum (x n : Nat) : Nat :=
  7 * pair (encExpr nat) (7 * pair
      (7 * pair (encExpr (.appN (.const ``Nat.rec [.succ .zero])
        [motive (.sort .zero), trueS, .lam nat (.lam (.sort .zero) falseS)]))
        (7 * pair (7 * pair x (encExpr (lit n)) + 3) (encExpr (.bvar 0)) + 3) + 3)
      (encExpr falseS) + 5) + 5

theorem diagNum_code (f : PR) (n : Nat) : diagNum f.code n = encExpr (notHalts f n) := by
  simp only [diagNum, PR.code, notHalts, isZero, natRec, VExpr.appN, encExpr]

/-- Some code computes the number of `notHalts f ⌜f⌝` from `⌜f⌝` in variable `1`. -/
def DiagComputable : Prop :=
  ∃ N : PR, ∀ ρ : Val, N.eval ρ = diagNum (ρ 1) (ρ 1)

theorem diagEnumerable_of {env : VEnv} (hG : CheckDecidable env) (hN : DiagComputable) :
    DiagEnumerable env := by
  obtain ⟨G, hG1, hG2⟩ := hG; obtain ⟨N, hN⟩ := hN
  refine ⟨.push N G, fun f => ?_⟩
  have key : ∀ k, PR.eval (.push N G) (val2 k f.code) =
      G.eval (vcons (encExpr (notHalts f f.code)) (vcons k (vcons f.code fun _ => 0))) := by
    intro k
    rw [PR.eval, hN, show val2 k f.code 1 = f.code by simp only [val2, vcons_succ, vcons_zero],
      diagNum_code]; rfl
  simp only [PR.Halts, key]
  exact ⟨fun ⟨k, hk⟩ => hG1 _ _ _ hk, fun h => let ⟨k, hk⟩ := hG2 _ h; ⟨k, hk _⟩⟩

/-- **Incompleteness**, from the two computability facts and consistency. -/
theorem incomplete' {env : VEnv} (H : HasNat env) (henv : env.Ordered) (hG : CheckDecidable env)
    (hN : DiagComputable) (hC : Consistent env) :
    ∃ d : PR, ¬d.Halts d.code ∧ ¬Provable env (notHalts d d.code) ∧
      (HaltsSound env → ¬Provable env (halts d d.code)) :=
  incomplete H henv (diagEnumerable_of hG hN) hC

end Lean4Lean.Incomplete
