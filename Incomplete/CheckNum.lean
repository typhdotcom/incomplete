import Incomplete.Enumerate

/-!
# Proof checking on numbers

Since the numberings are bijective, proof checking is a function of two numbers: `chkNum m k` is
`0` when the certificate numbered `k` proves the sentence numbered `m`. `CheckDecidable` follows
once a code computes it. `chkNumFor R` checks only certificates whose rules (by tag, in the
order of `Cert`'s constructors) are in `R`; for `R` all rules it is `chkNum`.
-/

namespace Incomplete
open Lean4Lean

def Cert.tag : Cert → Nat
  | .bvar .. => 0 | .symm .. => 1 | .trans .. => 2 | .sortDF .. => 3 | .constDF .. => 4
  | .appDF .. => 5 | .lamDF .. => 6 | .forallEDF .. => 7 | .defeqDF .. => 8 | .beta .. => 9
  | .eta .. => 10 | .proofIrrel .. => 11 | .extra .. => 12 | .projDF .. => 13
  | .projIota .. => 14 | .projEta .. => 15

/-- Every node of `c` uses a rule in `R`. -/
def Cert.usesOnly (R : Nat → Bool) : Cert → Bool
  | c@(.bvar ..) | c@(.sortDF ..) | c@(.constDF ..) | c@(.extra ..) => R c.tag
  | c@(.symm _ c₁) | c@(.eta _ _ _ _ c₁) => R c.tag && c₁.usesOnly R
  | c@(.trans _ _ c₁ c₂) | c@(.appDF _ _ _ _ _ _ _ c₁ c₂) | c@(.lamDF _ _ _ _ _ _ _ c₁ c₂)
  | c@(.forallEDF _ _ _ _ _ _ _ c₁ c₂) | c@(.defeqDF _ _ _ _ c₁ c₂) | c@(.beta _ _ _ _ _ c₁ c₂) =>
    R c.tag && c₁.usesOnly R && c₂.usesOnly R
  | c@(.proofIrrel _ _ _ _ c₁ c₂ c₃) | c@(.projDF _ _ _ _ _ _ _ _ _ _ _ c₁ c₂ c₃)
  | c@(.projIota _ _ _ _ _ _ _ c₁ c₂ c₃) =>
    R c.tag && c₁.usesOnly R && c₂.usesOnly R && c₃.usesOnly R
  | c@(.projEta _ _ _ _ _ c₁ c₂) => R c.tag && c₁.usesOnly R && c₂.usesOnly R

theorem Cert.usesOnly_all : ∀ c : Cert, c.usesOnly (fun _ => true) = true := by
  intro c; induction c <;> simp_all [Cert.usesOnly]

/-- `0` when the certificate numbered `k`, using only rules in `R`, proves the sentence numbered
`m`. -/
noncomputable def chkNumFor (T : Tables) (R : Nat → Bool) (m k : Nat) : Nat :=
  if (decCert k).usesOnly R && checkProofT T (decCert k) (decExpr m) then 0 else 1

/-- Some code checks certificates using rules in `R`. -/
def ChkComputableFor (T : Tables) (R : Nat → Bool) : Prop := ∃ G : PR, PR.Computes2 G (chkNumFor T R)

/-- Proof checking by a code for the certificates using rules in `R`, when those suffice. -/
theorem checkDecidable_of_chkFor {env : VEnv} {T : Tables} (hT : TablesFor env T) {R : Nat → Bool}
    (hR : ∀ c : Cert, c.check T.env 0 T.deciders = true → c.usesOnly R = true)
    (h : ChkComputableFor T R) : CheckDecidable env := by
  obtain ⟨G, hG⟩ := h
  refine ⟨G, fun Q k ρ hk => ?_, fun Q hQ => ?_⟩
  · rw [hG] at hk
    simp only [vcons_zero, vcons_succ, chkNumFor, decExpr_enc] at hk
    split at hk
    · rename_i hh
      simp only [Bool.and_eq_true] at hh
      exact (provable_iff_certT hT).2 ⟨_, hh.2⟩
    · cases hk
  · obtain ⟨c, hc⟩ := (provable_iff_certT hT).1 hQ
    refine ⟨encCert c, fun ρ => ?_⟩
    rw [hG]
    have hu := hR c (by simp only [checkProofT, Bool.and_eq_true] at hc; exact hc.1)
    simp [chkNumFor, decExpr_enc, decCert_enc, hc, hu]

theorem checkDecidable_of_chk {env : VEnv} {T : Tables} (hT : TablesFor env T)
    (h : ChkComputableFor T fun _ => true) : CheckDecidable env :=
  checkDecidable_of_chkFor hT (fun c _ => Cert.usesOnly_all c) h

end Incomplete
