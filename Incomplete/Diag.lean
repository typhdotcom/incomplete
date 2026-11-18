import Incomplete.PRLib
import Incomplete.Enumerate

/-!
# The diagonal sentence is computable

Codes for constants in binary, a code for the number of the numeral `lit n`, and from them the
code `diagC` for `diagNum`: `DiagComputable` holds.
-/

namespace Incomplete
open Lean4Lean
open PR

/-- The number of the numeral `lit (ρ 0)`. -/
def litC : PR :=
  prec (numC (encExpr Incomplete.zero)) (tagC 7 3 (cpair (numC (encExpr Incomplete.succ)) (var 0)))

theorem litC_computes : Computes1 litC (fun n => encExpr (lit n)) := by
  intro ρ
  show recNat ((numC (encExpr Incomplete.zero)).eval (tl ρ))
    (fun y r => (tagC 7 3 (cpair (numC (encExpr Incomplete.succ)) (var 0))).eval
      (vcons r (vcons y (tl ρ)))) (ρ 0) = _
  generalize ρ 0 = y
  induction y with
  | zero => rw [eval_numC]; rfl
  | succ y ih => rw [recNat_succ, ih]; simp [eval_var, lit, encExpr]

def diagC : PR :=
  tagC 7 5 (cpair (numC (encExpr nat)) (tagC 7 5 (cpair
    (tagC 7 3 (cpair (numC (encExpr (.appN (.const ``Nat.rec [.succ .zero])
      [motive (.sort .zero), trueS, .lam nat (.lam (.sort .zero) falseS)])))
      (tagC 7 3 (cpair (tagC 7 3 (cpair (var 1) (push (var 1) litC)))
        (numC (encExpr (.bvar 0)))))))
    (numC (encExpr falseS)))))

theorem eval_diagC (ρ : Val) : diagC.eval ρ = diagNum (ρ 1) (ρ 1) := by
  simp only [diagC, eval_tagC, eval_cpair, eval_numC, eval_var, eval_push litC_computes]
  rfl

theorem diagComputable : DiagComputable := ⟨diagC, eval_diagC⟩

/-- **Incompleteness**, from consistency and the checkability of proofs. -/
theorem incomplete_of_check {env : VEnv} (H : HasNat env) (henv : env.Ordered)
    (hG : CheckDecidable env) (hC : Consistent env) :
    ∃ d : PR, ¬d.Halts d.code ∧ ¬Provable env (notHalts d d.code) ∧
      (HaltsSound env → ¬Provable env (halts d d.code)) :=
  incomplete' H henv hG diagComputable hC

end Incomplete
