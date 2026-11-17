import Incomplete.Cert
import Incomplete.PRLib

/-!
# Numbering certificates bijectively

Every number is the code of exactly one name, level, expression, judgment and certificate. A type
with `k` constructors that all take data codes constructor `t` with data `p` as `k * p + t`; one
with a constant constructor first sends it to `0` and shifts the rest by one. Several fields are
Cantor-paired, and strings are numerals in bijective base `Char.numCodePoints`.

Bijectivity is what lets a machine check numbers instead of objects: there are no junk numbers,
and two objects are equal exactly when their numbers are.
-/

namespace Lean4Lean.Incomplete
open PR (pair unpair1 unpair2 pair_unpair unpair1_pair unpair2_pair unpair1_le unpair2_le)

abbrev p1 := unpair1
abbrev p2 := unpair2

theorem tag_mod {k t p : Nat} (h : t < k) : (k * p + t) % k = t := by
  rw [Nat.mul_add_mod]; exact Nat.mod_eq_of_lt h
theorem tag_div {k t p : Nat} (h : t < k) : (k * p + t) / k = p := by
  rw [Nat.mul_add_div (by omega), Nat.div_eq_of_lt h, Nat.add_zero]

theorem pair_ext_eq (x : Nat) : pair (p1 x) (p2 x) = x := pair_unpair x

/-! ### Lists -/

def encList (e : α → Nat) : List α → Nat
  | [] => 0
  | a :: l => pair (e a) (encList e l) + 1

def decList (d : Nat → α) : Nat → List α
  | 0 => []
  | n + 1 => d (p1 n) :: decList d (p2 n)
termination_by n => n
decreasing_by exact Nat.lt_succ_of_le (unpair2_le n)

theorem decList_enc {e : α → Nat} {d : Nat → α} (h : ∀ a, d (e a) = a) :
    ∀ l, decList d (encList e l) = l
  | [] => by simp [encList, decList]
  | a :: l => by simp [encList, decList, h, decList_enc h l]

theorem encList_dec {e : α → Nat} {d : Nat → α} (h : ∀ n, e (d n) = n) :
    ∀ n, encList e (decList d n) = n
  | 0 => by simp [decList, encList]
  | n + 1 => by
    have := encList_dec h (p2 n)
    rw [decList, encList, h, this, pair_ext_eq]
termination_by n => n
decreasing_by exact Nat.lt_succ_of_le (unpair2_le n)

theorem decList_eq_nil {d : Nat → α} {n : Nat} : decList d n = [] ↔ n = 0 := by
  cases n <;> simp [decList]

/-! ### Strings and names -/

def encChars : List Char → Nat
  | [] => 0
  | c :: l => c.ordinal.val + Char.numCodePoints * encChars l + 1

def decChars : Nat → List Char
  | 0 => []
  | n + 1 => Char.ofOrdinal ⟨n % Char.numCodePoints, Nat.mod_lt _ (by decide)⟩ ::
    decChars (n / Char.numCodePoints)
termination_by n => n
decreasing_by exact Nat.lt_succ_of_le (Nat.div_le_self _ _)

theorem decChars_enc : ∀ l, decChars (encChars l) = l
  | [] => by simp [encChars, decChars]
  | c :: l => by
    have hc := c.ordinal.isLt
    rw [encChars, decChars]
    have e1 : (c.ordinal.val + Char.numCodePoints * encChars l) % Char.numCodePoints =
        c.ordinal.val := by rw [Nat.add_mul_mod_self_left]; exact Nat.mod_eq_of_lt hc
    have e2 : (c.ordinal.val + Char.numCodePoints * encChars l) / Char.numCodePoints =
        encChars l := by
      rw [Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt hc, Nat.zero_add]
    simp only [e1, e2, decChars_enc l]
    congr; exact Char.ofOrdinal_ordinal

theorem encChars_dec : ∀ n, encChars (decChars n) = n
  | 0 => by simp [decChars, encChars]
  | n + 1 => by
    rw [decChars, encChars, encChars_dec (n / Char.numCodePoints), Char.ordinal_ofOrdinal]
    have := Nat.div_add_mod n Char.numCodePoints
    simp only; omega
termination_by n => n
decreasing_by exact Nat.lt_succ_of_le (Nat.div_le_self _ _)

def encString (s : String) : Nat := encChars s.toList
def decString (n : Nat) : String := String.ofList (decChars n)

theorem decString_enc (s : String) : decString (encString s) = s := by
  simp [decString, encString, decChars_enc, String.ofList_toList]
theorem encString_dec (n : Nat) : encString (decString n) = n := by
  simp [decString, encString, String.toList_ofList, encChars_dec]

def encName : Name → Nat
  | .anonymous => 0
  | .str p s => 2 * pair (encName p) (encString s) + 1
  | .num p n => 2 * pair (encName p) n + 2

def decName : Nat → Name
  | 0 => .anonymous
  | n + 1 =>
    if n % 2 = 0 then .str (decName (p1 (n / 2))) (decString (p2 (n / 2)))
    else .num (decName (p1 (n / 2))) (p2 (n / 2))
termination_by n => n
decreasing_by
  all_goals exact Nat.lt_succ_of_le (Nat.le_trans (unpair1_le _) (Nat.div_le_self _ _))

theorem decName_enc : ∀ n, decName (encName n) = n
  | .anonymous => by simp [encName, decName]
  | .str p s => by
    rw [encName, decName]
    have h1 : 2 * pair (encName p) (encString s) % 2 = 0 := by omega
    have h2 : 2 * pair (encName p) (encString s) / 2 = pair (encName p) (encString s) := by omega
    simp [h1, h2, decName_enc p, decString_enc]
  | .num p k => by
    rw [encName, show 2 * pair (encName p) k + 2 = (2 * pair (encName p) k + 1) + 1 by omega,
      decName]
    have h1 : (2 * pair (encName p) k + 1) % 2 = 1 := by omega
    have h2 : (2 * pair (encName p) k + 1) / 2 = pair (encName p) k := by omega
    simp [h1, h2, decName_enc p]

theorem encName_dec : ∀ n, encName (decName n) = n
  | 0 => by simp [decName, encName]
  | n + 1 => by
    rw [decName]
    have := encName_dec (p1 (n / 2))
    split
    · rw [encName, this, encString_dec, pair_ext_eq]; omega
    · rw [encName, this, pair_ext_eq]; omega
termination_by n => n
decreasing_by
  all_goals exact Nat.lt_succ_of_le (Nat.le_trans (unpair1_le _) (Nat.div_le_self _ _))

/-! ### Levels -/

def encLevel : VLevel → Nat
  | .zero => 0
  | .succ l => 4 * encLevel l + 1
  | .max a b => 4 * pair (encLevel a) (encLevel b) + 2
  | .imax a b => 4 * pair (encLevel a) (encLevel b) + 3
  | .param i => 4 * i + 4

def decLevel : Nat → VLevel
  | 0 => .zero
  | n + 1 =>
    if n % 4 = 0 then .succ (decLevel (n / 4))
    else if n % 4 = 1 then .max (decLevel (p1 (n / 4))) (decLevel (p2 (n / 4)))
    else if n % 4 = 2 then .imax (decLevel (p1 (n / 4))) (decLevel (p2 (n / 4)))
    else .param (n / 4)
termination_by n => n
decreasing_by
  all_goals first
    | exact Nat.lt_succ_of_le (Nat.div_le_self _ _)
    | exact Nat.lt_succ_of_le (Nat.le_trans (unpair1_le _) (Nat.div_le_self _ _))
    | exact Nat.lt_succ_of_le (Nat.le_trans (unpair2_le _) (Nat.div_le_self _ _))

theorem decLevel_enc : ∀ l, decLevel (encLevel l) = l
  | .zero => by simp [encLevel, decLevel]
  | .succ l => by
    rw [encLevel, decLevel]; simp [Nat.mul_mod_right, decLevel_enc l]
  | .max a b => by
    rw [encLevel, show 4 * pair (encLevel a) (encLevel b) + 2 =
      (4 * pair (encLevel a) (encLevel b) + 1) + 1 by rfl, decLevel]
    simp [tag_div, decLevel_enc a, decLevel_enc b]
  | .imax a b => by
    rw [encLevel, show 4 * pair (encLevel a) (encLevel b) + 3 =
      (4 * pair (encLevel a) (encLevel b) + 2) + 1 by rfl, decLevel]
    simp [tag_div, decLevel_enc a, decLevel_enc b]
  | .param i => by
    rw [encLevel, show 4 * i + 4 = (4 * i + 3) + 1 by rfl, decLevel]
    simp [tag_div]

theorem encLevel_dec : ∀ n, encLevel (decLevel n) = n
  | 0 => by simp [decLevel, encLevel]
  | n + 1 => by
    have hd := Nat.div_add_mod n 4
    have hm := Nat.mod_lt n (show 4 > 0 by decide)
    rw [decLevel]
    split
    · rw [encLevel, encLevel_dec (n / 4)]; omega
    split
    · rw [encLevel, encLevel_dec, encLevel_dec, pair_ext_eq]; omega
    split
    · rw [encLevel, encLevel_dec, encLevel_dec, pair_ext_eq]; omega
    · rw [encLevel]; omega
termination_by n => n
decreasing_by
  all_goals first
    | exact Nat.lt_succ_of_le (Nat.div_le_self _ _)
    | exact Nat.lt_succ_of_le (Nat.le_trans (unpair1_le _) (Nat.div_le_self _ _))
    | exact Nat.lt_succ_of_le (Nat.le_trans (unpair2_le _) (Nat.div_le_self _ _))

/-! ### Expressions -/

theorem div_lt_of_mod {k n : Nat} (hk : 1 < k) (h : ¬n % k = 0) : n / k < n :=
  Nat.div_lt_self (Nat.pos_of_ne_zero fun e => h (by simp [e])) hk

@[simp] theorem tag0_mod {k p : Nat} : (k * p) % k = 0 := Nat.mul_mod_right _ _
@[simp] theorem tag0_div {k p : Nat} (h : 0 < k) : (k * p) / k = p := Nat.mul_div_cancel_left _ h

def encExpr : VExpr → Nat
  | .bvar i => 7 * i
  | .sort u => 7 * encLevel u + 1
  | .const c ls => 7 * pair (encName c) (encList encLevel ls) + 2
  | .app f a => 7 * pair (encExpr f) (encExpr a) + 3
  | .lam A b => 7 * pair (encExpr A) (encExpr b) + 4
  | .forallE A b => 7 * pair (encExpr A) (encExpr b) + 5
  | .proj s i e => 7 * pair (encName s) (pair i (encExpr e)) + 6

def decExpr (n : Nat) : VExpr :=
  if h0 : n % 7 = 0 then .bvar (n / 7)
  else if n % 7 = 1 then .sort (decLevel (n / 7))
  else if n % 7 = 2 then .const (decName (p1 (n / 7))) (decList decLevel (p2 (n / 7)))
  else if n % 7 = 3 then .app (decExpr (p1 (n / 7))) (decExpr (p2 (n / 7)))
  else if n % 7 = 4 then .lam (decExpr (p1 (n / 7))) (decExpr (p2 (n / 7)))
  else if n % 7 = 5 then .forallE (decExpr (p1 (n / 7))) (decExpr (p2 (n / 7)))
  else .proj (decName (p1 (n / 7))) (p1 (p2 (n / 7))) (decExpr (p2 (p2 (n / 7))))
termination_by n
decreasing_by
  all_goals first
    | exact Nat.lt_of_le_of_lt (unpair1_le _) (div_lt_of_mod (by decide) h0)
    | exact Nat.lt_of_le_of_lt (unpair2_le _) (div_lt_of_mod (by decide) h0)
    | exact Nat.lt_of_le_of_lt (Nat.le_trans (unpair2_le _) (unpair2_le _))
        (div_lt_of_mod (by decide) h0)

theorem decExpr_enc : ∀ e, decExpr (encExpr e) = e
  | .bvar i => by rw [encExpr, decExpr]; simp
  | .sort u => by rw [encExpr, decExpr]; simp [tag_div, decLevel_enc]
  | .const c ls => by
    rw [encExpr, decExpr]
    simp [tag_div, decName_enc, decList_enc decLevel_enc]
  | .app f a => by rw [encExpr, decExpr]; simp [tag_div, decExpr_enc f, decExpr_enc a]
  | .lam f a => by rw [encExpr, decExpr]; simp [tag_div, decExpr_enc f, decExpr_enc a]
  | .forallE f a => by
    rw [encExpr, decExpr]; simp [tag_div, decExpr_enc f, decExpr_enc a]
  | .proj s i e => by
    rw [encExpr, decExpr]; simp [tag_div, decName_enc, decExpr_enc e]

theorem encExpr_dec (n : Nat) : encExpr (decExpr n) = n := by
  have hd := Nat.div_add_mod n 7
  have hm := Nat.mod_lt n (show 7 > 0 by decide)
  rw [decExpr]
  split
  · rw [encExpr]; omega
  rename_i h0
  have hl := div_lt_of_mod (by decide) h0
  have i1 := encExpr_dec (p1 (n / 7)); have i2 := encExpr_dec (p2 (n / 7))
  split
  · rw [encExpr, encLevel_dec]; omega
  split
  · rw [encExpr, encName_dec, encList_dec encLevel_dec, pair_ext_eq]; omega
  split
  · rw [encExpr, i1, i2, pair_ext_eq]; omega
  split
  · rw [encExpr, i1, i2, pair_ext_eq]; omega
  split
  · rw [encExpr, i1, i2, pair_ext_eq]; omega
  · have i3 := encExpr_dec (p2 (p2 (n / 7)))
    rw [encExpr, encName_dec, i3, pair_ext_eq, pair_ext_eq]; omega
termination_by n
decreasing_by
  all_goals first
    | exact Nat.lt_of_le_of_lt (unpair1_le _) hl
    | exact Nat.lt_of_le_of_lt (unpair2_le _) hl
    | exact Nat.lt_of_le_of_lt (Nat.le_trans (unpair2_le _) (unpair2_le _)) hl

theorem encExpr_inj {e e' : VExpr} (h : encExpr e = encExpr e') : e = e' := by
  rw [← decExpr_enc e, h, decExpr_enc]

theorem encExpr_eq_iff {e e' : VExpr} : encExpr e = encExpr e' ↔ e = e' :=
  ⟨encExpr_inj, (· ▸ rfl)⟩

/-! ### Tuples, judgments and certificates -/

/-- The tuple `x` with its first `i` fields dropped. -/
def rest : Nat → Nat → Nat
  | 0, x => x
  | i + 1, x => rest i (p2 x)

/-- The `i`th field of the tuple `x`. -/
def fld (i x : Nat) : Nat := p1 (rest i x)

@[simp] theorem rest_zero (x : Nat) : rest 0 x = x := rfl
@[simp] theorem rest_succ_pair (i a b : Nat) : rest (i + 1) (pair a b) = rest i b := by
  simp [rest]
@[simp] theorem fld_zero_pair (a b : Nat) : fld 0 (pair a b) = a := by simp [fld]
@[simp] theorem fld_succ_pair (i a b : Nat) : fld (i + 1) (pair a b) = fld i b := by
  simp [fld]

theorem rest_le : ∀ i x, rest i x ≤ x
  | 0, _ => Nat.le_refl _
  | i + 1, x => Nat.le_trans (rest_le i _) (unpair2_le x)

theorem fld_le (i x : Nat) : fld i x ≤ x := Nat.le_trans (unpair1_le _) (rest_le i x)

/-- Reassembling a tuple from its fields. -/
theorem pair_fld_rest (i x : Nat) : pair (fld i x) (rest (i + 1) x) = rest i x := by
  induction i generalizing x with
  | zero => exact pair_ext_eq x
  | succ i ih => exact ih (p2 x)

def encJudg (J : Judg) : Nat :=
  pair (encList encExpr J.Γ) (pair (encExpr J.e1) (pair (encExpr J.e2) (encExpr J.A)))

def decJudg (x : Nat) : Judg :=
  ⟨decList decExpr (fld 0 x), decExpr (fld 1 x), decExpr (fld 2 x), decExpr (rest 3 x)⟩

theorem decJudg_enc (J : Judg) : decJudg (encJudg J) = J := by
  simp [encJudg, decJudg, decList_enc decExpr_enc, decExpr_enc]

theorem encJudg_dec (x : Nat) : encJudg (decJudg x) = x := by
  simp only [encJudg, decJudg, encList_dec encExpr_dec, encExpr_dec]
  rw [pair_fld_rest 2, pair_fld_rest 1, pair_fld_rest 0]; rfl

def encConst (ci : VConstant) : Nat := pair ci.uvars (encExpr ci.type)
def decConst (x : Nat) : VConstant := ⟨p1 x, decExpr (p2 x)⟩
theorem decConst_enc (ci : VConstant) : decConst (encConst ci) = ci := by
  simp [encConst, decConst, decExpr_enc]
theorem encConst_dec (x : Nat) : encConst (decConst x) = x := by
  simp [encConst, decConst, encExpr_dec, pair_ext_eq]

def encDefEq (df : VDefEq) : Nat :=
  pair df.uvars (pair (encExpr df.lhs) (pair (encExpr df.rhs) (encExpr df.type)))
def decDefEq (x : Nat) : VDefEq :=
  ⟨fld 0 x, decExpr (fld 1 x), decExpr (fld 2 x), decExpr (rest 3 x)⟩
theorem decDefEq_enc (df : VDefEq) : decDefEq (encDefEq df) = df := by
  simp [encDefEq, decDefEq, decExpr_enc]
theorem encDefEq_dec (x : Nat) : encDefEq (decDefEq x) = x := by
  simp only [encDefEq, decDefEq, encExpr_dec]
  rw [pair_fld_rest 2, pair_fld_rest 1, pair_fld_rest 0]; rfl

def encCert : Cert → Nat
  | .bvar j i => 16 * pair (encJudg j) (i) + 0
  | .symm j c => 16 * pair (encJudg j) (encCert c) + 1
  | .trans j m c₁ c₂ => 16 * pair (encJudg j) (pair (encExpr m) (pair (encCert c₁) (encCert c₂))) + 2
  | .sortDF j l l' => 16 * pair (encJudg j) (pair (encLevel l) (encLevel l')) + 3
  | .constDF j n ci ls ls' => 16 * pair (encJudg j) (pair (encName n) (pair (encConst ci) (pair (encList encLevel ls) (encList encLevel ls')))) + 4
  | .appDF j A B f f' a a' c₁ c₂ => 16 * pair (encJudg j) (pair (encExpr A) (pair (encExpr B) (pair (encExpr f) (pair (encExpr f') (pair (encExpr a) (pair (encExpr a') (pair (encCert c₁) (encCert c₂)))))))) + 5
  | .lamDF j u A A' b b' B c₁ c₂ => 16 * pair (encJudg j) (pair (encLevel u) (pair (encExpr A) (pair (encExpr A') (pair (encExpr b) (pair (encExpr b') (pair (encExpr B) (pair (encCert c₁) (encCert c₂)))))))) + 6
  | .forallEDF j u v A A' b b' c₁ c₂ => 16 * pair (encJudg j) (pair (encLevel u) (pair (encLevel v) (pair (encExpr A) (pair (encExpr A') (pair (encExpr b) (pair (encExpr b') (pair (encCert c₁) (encCert c₂)))))))) + 7
  | .defeqDF j u A B c₁ c₂ => 16 * pair (encJudg j) (pair (encLevel u) (pair (encExpr A) (pair (encExpr B) (pair (encCert c₁) (encCert c₂))))) + 8
  | .beta j A e B e' c₁ c₂ => 16 * pair (encJudg j) (pair (encExpr A) (pair (encExpr e) (pair (encExpr B) (pair (encExpr e') (pair (encCert c₁) (encCert c₂)))))) + 9
  | .eta j e A B c => 16 * pair (encJudg j) (pair (encExpr e) (pair (encExpr A) (pair (encExpr B) (encCert c)))) + 10
  | .proofIrrel j p h h' c₁ c₂ c₃ => 16 * pair (encJudg j) (pair (encExpr p) (pair (encExpr h) (pair (encExpr h') (pair (encCert c₁) (pair (encCert c₂) (encCert c₃)))))) + 11
  | .extra j df ls => 16 * pair (encJudg j) (pair (encDefEq df) (encList encLevel ls)) + 12
  | .projDF j s k ls AsR IR AsR' IR' u e e' c₁ c₂ c₃ => 16 * pair (encJudg j) (pair (encName s) (pair (k) (pair (encList encLevel ls) (pair (encList encExpr AsR) (pair (encList encExpr IR) (pair (encList encExpr AsR') (pair (encList encExpr IR') (pair (encLevel u) (pair (encExpr e) (pair (encExpr e') (pair (encCert c₁) (pair (encCert c₂) (encCert c₃))))))))))))) + 13
  | .projIota j s k ls AsR fsR IR c₁ c₂ c₃ => 16 * pair (encJudg j) (pair (encName s) (pair (k) (pair (encList encLevel ls) (pair (encList encExpr AsR) (pair (encList encExpr fsR) (pair (encList encExpr IR) (pair (encCert c₁) (pair (encCert c₂) (encCert c₃))))))))) + 14
  | .projEta j s ls AsR e c₁ c₂ => 16 * pair (encJudg j) (pair (encName s) (pair (encList encLevel ls) (pair (encList encExpr AsR) (pair (encExpr e) (pair (encCert c₁) (encCert c₂)))))) + 15

def decCert (n : Nat) : Cert :=
  let x := n / 16
  if h0 : n % 16 = 0 then .bvar (decJudg (fld 0 x)) ((rest 1 x))
  else if n % 16 = 1 then .symm (decJudg (fld 0 x)) (decCert (rest 1 x))
  else if n % 16 = 2 then .trans (decJudg (fld 0 x)) (decExpr (fld 1 x)) (decCert (fld 2 x)) (decCert (rest 3 x))
  else if n % 16 = 3 then .sortDF (decJudg (fld 0 x)) (decLevel (fld 1 x)) (decLevel (rest 2 x))
  else if n % 16 = 4 then .constDF (decJudg (fld 0 x)) (decName (fld 1 x)) (decConst (fld 2 x)) (decList decLevel (fld 3 x)) (decList decLevel (rest 4 x))
  else if n % 16 = 5 then .appDF (decJudg (fld 0 x)) (decExpr (fld 1 x)) (decExpr (fld 2 x)) (decExpr (fld 3 x)) (decExpr (fld 4 x)) (decExpr (fld 5 x)) (decExpr (fld 6 x)) (decCert (fld 7 x)) (decCert (rest 8 x))
  else if n % 16 = 6 then .lamDF (decJudg (fld 0 x)) (decLevel (fld 1 x)) (decExpr (fld 2 x)) (decExpr (fld 3 x)) (decExpr (fld 4 x)) (decExpr (fld 5 x)) (decExpr (fld 6 x)) (decCert (fld 7 x)) (decCert (rest 8 x))
  else if n % 16 = 7 then .forallEDF (decJudg (fld 0 x)) (decLevel (fld 1 x)) (decLevel (fld 2 x)) (decExpr (fld 3 x)) (decExpr (fld 4 x)) (decExpr (fld 5 x)) (decExpr (fld 6 x)) (decCert (fld 7 x)) (decCert (rest 8 x))
  else if n % 16 = 8 then .defeqDF (decJudg (fld 0 x)) (decLevel (fld 1 x)) (decExpr (fld 2 x)) (decExpr (fld 3 x)) (decCert (fld 4 x)) (decCert (rest 5 x))
  else if n % 16 = 9 then .beta (decJudg (fld 0 x)) (decExpr (fld 1 x)) (decExpr (fld 2 x)) (decExpr (fld 3 x)) (decExpr (fld 4 x)) (decCert (fld 5 x)) (decCert (rest 6 x))
  else if n % 16 = 10 then .eta (decJudg (fld 0 x)) (decExpr (fld 1 x)) (decExpr (fld 2 x)) (decExpr (fld 3 x)) (decCert (rest 4 x))
  else if n % 16 = 11 then .proofIrrel (decJudg (fld 0 x)) (decExpr (fld 1 x)) (decExpr (fld 2 x)) (decExpr (fld 3 x)) (decCert (fld 4 x)) (decCert (fld 5 x)) (decCert (rest 6 x))
  else if n % 16 = 12 then .extra (decJudg (fld 0 x)) (decDefEq (fld 1 x)) (decList decLevel (rest 2 x))
  else if n % 16 = 13 then .projDF (decJudg (fld 0 x)) (decName (fld 1 x)) ((fld 2 x)) (decList decLevel (fld 3 x)) (decList decExpr (fld 4 x)) (decList decExpr (fld 5 x)) (decList decExpr (fld 6 x)) (decList decExpr (fld 7 x)) (decLevel (fld 8 x)) (decExpr (fld 9 x)) (decExpr (fld 10 x)) (decCert (fld 11 x)) (decCert (fld 12 x)) (decCert (rest 13 x))
  else if n % 16 = 14 then .projIota (decJudg (fld 0 x)) (decName (fld 1 x)) ((fld 2 x)) (decList decLevel (fld 3 x)) (decList decExpr (fld 4 x)) (decList decExpr (fld 5 x)) (decList decExpr (fld 6 x)) (decCert (fld 7 x)) (decCert (fld 8 x)) (decCert (rest 9 x))
  else .projEta (decJudg (fld 0 x)) (decName (fld 1 x)) (decList decLevel (fld 2 x)) (decList decExpr (fld 3 x)) (decExpr (fld 4 x)) (decCert (fld 5 x)) (decCert (rest 6 x))
termination_by n
decreasing_by
  all_goals first
    | exact Nat.lt_of_le_of_lt (fld_le _ _) (div_lt_of_mod (by decide) h0)
    | exact Nat.lt_of_le_of_lt (rest_le _ _) (div_lt_of_mod (by decide) h0)

theorem decCert_enc (c : Cert) : decCert (encCert c) = c := by
  induction c with
  | bvar j i  =>
    rw [encCert, decCert]; simp [tag_div, decJudg_enc]
  | symm j c ihc =>
    rw [encCert, decCert]; simp [tag_div, decJudg_enc, ihc]
  | trans j m c₁ c₂ ihc₁ ihc₂ =>
    rw [encCert, decCert]; simp [tag_div, decExpr_enc, decJudg_enc, ihc₁, ihc₂]
  | sortDF j l l'  =>
    rw [encCert, decCert]; simp [tag_div, decJudg_enc, decLevel_enc]
  | constDF j n ci ls ls'  =>
    rw [encCert, decCert]; simp [tag_div, decConst_enc, decJudg_enc, decList_enc decLevel_enc, decName_enc]
  | appDF j A B f f' a a' c₁ c₂ ihc₁ ihc₂ =>
    rw [encCert, decCert]; simp [tag_div, decExpr_enc, decJudg_enc, ihc₁, ihc₂]
  | lamDF j u A A' b b' B c₁ c₂ ihc₁ ihc₂ =>
    rw [encCert, decCert]; simp [tag_div, decExpr_enc, decJudg_enc, decLevel_enc, ihc₁, ihc₂]
  | forallEDF j u v A A' b b' c₁ c₂ ihc₁ ihc₂ =>
    rw [encCert, decCert]; simp [tag_div, decExpr_enc, decJudg_enc, decLevel_enc, ihc₁, ihc₂]
  | defeqDF j u A B c₁ c₂ ihc₁ ihc₂ =>
    rw [encCert, decCert]; simp [tag_div, decExpr_enc, decJudg_enc, decLevel_enc, ihc₁, ihc₂]
  | beta j A e B e' c₁ c₂ ihc₁ ihc₂ =>
    rw [encCert, decCert]; simp [tag_div, decExpr_enc, decJudg_enc, ihc₁, ihc₂]
  | eta j e A B c ihc =>
    rw [encCert, decCert]; simp [tag_div, decExpr_enc, decJudg_enc, ihc]
  | proofIrrel j p h h' c₁ c₂ c₃ ihc₁ ihc₂ ihc₃ =>
    rw [encCert, decCert]; simp [tag_div, decExpr_enc, decJudg_enc, ihc₁, ihc₂, ihc₃]
  | extra j df ls  =>
    rw [encCert, decCert]; simp [tag_div, decDefEq_enc, decJudg_enc, decList_enc decLevel_enc]
  | projDF j s k ls AsR IR AsR' IR' u e e' c₁ c₂ c₃ ihc₁ ihc₂ ihc₃ =>
    rw [encCert, decCert]; simp [tag_div, decExpr_enc, decJudg_enc, decLevel_enc, decList_enc decExpr_enc, decList_enc decLevel_enc, decName_enc, ihc₁, ihc₂, ihc₃]
  | projIota j s k ls AsR fsR IR c₁ c₂ c₃ ihc₁ ihc₂ ihc₃ =>
    rw [encCert, decCert]; simp [tag_div, decJudg_enc, decList_enc decExpr_enc, decList_enc decLevel_enc, decName_enc, ihc₁, ihc₂, ihc₃]
  | projEta j s ls AsR e c₁ c₂ ihc₁ ihc₂ =>
    rw [encCert, decCert]; simp [tag_div, decExpr_enc, decJudg_enc, decList_enc decExpr_enc, decList_enc decLevel_enc, decName_enc, ihc₁, ihc₂]

theorem encCert_dec (n : Nat) : encCert (decCert n) = n := by
  have hd := Nat.div_add_mod n 16
  have hm := Nat.mod_lt n (show 16 > 0 by decide)
  rw [decCert]
  by_cases h0 : n % 16 = 0
  · rw [dif_pos h0]; rw [encCert, encJudg_dec, pair_fld_rest 0]; simp only [rest_zero]; omega
  rw [dif_neg h0]
  have hl := div_lt_of_mod (by decide) h0
  by_cases h1 : n % 16 = 1
  · rw [if_pos h1]; rw [encCert, encJudg_dec, encCert_dec (rest 1 (n / 16)), pair_fld_rest 0]; simp only [rest_zero]; omega
  rw [if_neg h1]
  by_cases h2 : n % 16 = 2
  · rw [if_pos h2]; rw [encCert, encJudg_dec, encExpr_dec, encCert_dec (fld 2 (n / 16)), encCert_dec (rest 3 (n / 16)), pair_fld_rest 2, pair_fld_rest 1, pair_fld_rest 0]; simp only [rest_zero]; omega
  rw [if_neg h2]
  by_cases h3 : n % 16 = 3
  · rw [if_pos h3]; rw [encCert, encJudg_dec, encLevel_dec, encLevel_dec, pair_fld_rest 1, pair_fld_rest 0]; simp only [rest_zero]; omega
  rw [if_neg h3]
  by_cases h4 : n % 16 = 4
  · rw [if_pos h4]; rw [encCert, encJudg_dec, encName_dec, encConst_dec, encList_dec encLevel_dec, encList_dec encLevel_dec, pair_fld_rest 3, pair_fld_rest 2, pair_fld_rest 1, pair_fld_rest 0]; simp only [rest_zero]; omega
  rw [if_neg h4]
  by_cases h5 : n % 16 = 5
  · rw [if_pos h5]; rw [encCert, encJudg_dec, encExpr_dec, encExpr_dec, encExpr_dec, encExpr_dec, encExpr_dec, encExpr_dec, encCert_dec (fld 7 (n / 16)), encCert_dec (rest 8 (n / 16)), pair_fld_rest 7, pair_fld_rest 6, pair_fld_rest 5, pair_fld_rest 4, pair_fld_rest 3, pair_fld_rest 2, pair_fld_rest 1, pair_fld_rest 0]; simp only [rest_zero]; omega
  rw [if_neg h5]
  by_cases h6 : n % 16 = 6
  · rw [if_pos h6]; rw [encCert, encJudg_dec, encLevel_dec, encExpr_dec, encExpr_dec, encExpr_dec, encExpr_dec, encExpr_dec, encCert_dec (fld 7 (n / 16)), encCert_dec (rest 8 (n / 16)), pair_fld_rest 7, pair_fld_rest 6, pair_fld_rest 5, pair_fld_rest 4, pair_fld_rest 3, pair_fld_rest 2, pair_fld_rest 1, pair_fld_rest 0]; simp only [rest_zero]; omega
  rw [if_neg h6]
  by_cases h7 : n % 16 = 7
  · rw [if_pos h7]; rw [encCert, encJudg_dec, encLevel_dec, encLevel_dec, encExpr_dec, encExpr_dec, encExpr_dec, encExpr_dec, encCert_dec (fld 7 (n / 16)), encCert_dec (rest 8 (n / 16)), pair_fld_rest 7, pair_fld_rest 6, pair_fld_rest 5, pair_fld_rest 4, pair_fld_rest 3, pair_fld_rest 2, pair_fld_rest 1, pair_fld_rest 0]; simp only [rest_zero]; omega
  rw [if_neg h7]
  by_cases h8 : n % 16 = 8
  · rw [if_pos h8]; rw [encCert, encJudg_dec, encLevel_dec, encExpr_dec, encExpr_dec, encCert_dec (fld 4 (n / 16)), encCert_dec (rest 5 (n / 16)), pair_fld_rest 4, pair_fld_rest 3, pair_fld_rest 2, pair_fld_rest 1, pair_fld_rest 0]; simp only [rest_zero]; omega
  rw [if_neg h8]
  by_cases h9 : n % 16 = 9
  · rw [if_pos h9]; rw [encCert, encJudg_dec, encExpr_dec, encExpr_dec, encExpr_dec, encExpr_dec, encCert_dec (fld 5 (n / 16)), encCert_dec (rest 6 (n / 16)), pair_fld_rest 5, pair_fld_rest 4, pair_fld_rest 3, pair_fld_rest 2, pair_fld_rest 1, pair_fld_rest 0]; simp only [rest_zero]; omega
  rw [if_neg h9]
  by_cases h10 : n % 16 = 10
  · rw [if_pos h10]; rw [encCert, encJudg_dec, encExpr_dec, encExpr_dec, encExpr_dec, encCert_dec (rest 4 (n / 16)), pair_fld_rest 3, pair_fld_rest 2, pair_fld_rest 1, pair_fld_rest 0]; simp only [rest_zero]; omega
  rw [if_neg h10]
  by_cases h11 : n % 16 = 11
  · rw [if_pos h11]; rw [encCert, encJudg_dec, encExpr_dec, encExpr_dec, encExpr_dec, encCert_dec (fld 4 (n / 16)), encCert_dec (fld 5 (n / 16)), encCert_dec (rest 6 (n / 16)), pair_fld_rest 5, pair_fld_rest 4, pair_fld_rest 3, pair_fld_rest 2, pair_fld_rest 1, pair_fld_rest 0]; simp only [rest_zero]; omega
  rw [if_neg h11]
  by_cases h12 : n % 16 = 12
  · rw [if_pos h12]; rw [encCert, encJudg_dec, encDefEq_dec, encList_dec encLevel_dec, pair_fld_rest 1, pair_fld_rest 0]; simp only [rest_zero]; omega
  rw [if_neg h12]
  by_cases h13 : n % 16 = 13
  · rw [if_pos h13]; rw [encCert, encJudg_dec, encName_dec, encList_dec encLevel_dec, encList_dec encExpr_dec, encList_dec encExpr_dec, encList_dec encExpr_dec, encList_dec encExpr_dec, encLevel_dec, encExpr_dec, encExpr_dec, encCert_dec (fld 11 (n / 16)), encCert_dec (fld 12 (n / 16)), encCert_dec (rest 13 (n / 16)), pair_fld_rest 12, pair_fld_rest 11, pair_fld_rest 10, pair_fld_rest 9, pair_fld_rest 8, pair_fld_rest 7, pair_fld_rest 6, pair_fld_rest 5, pair_fld_rest 4, pair_fld_rest 3, pair_fld_rest 2, pair_fld_rest 1, pair_fld_rest 0]; simp only [rest_zero]; omega
  rw [if_neg h13]
  by_cases h14 : n % 16 = 14
  · rw [if_pos h14]; rw [encCert, encJudg_dec, encName_dec, encList_dec encLevel_dec, encList_dec encExpr_dec, encList_dec encExpr_dec, encList_dec encExpr_dec, encCert_dec (fld 7 (n / 16)), encCert_dec (fld 8 (n / 16)), encCert_dec (rest 9 (n / 16)), pair_fld_rest 8, pair_fld_rest 7, pair_fld_rest 6, pair_fld_rest 5, pair_fld_rest 4, pair_fld_rest 3, pair_fld_rest 2, pair_fld_rest 1, pair_fld_rest 0]; simp only [rest_zero]; omega
  rw [if_neg h14]
  rw [encCert, encJudg_dec, encName_dec, encList_dec encLevel_dec, encList_dec encExpr_dec, encExpr_dec, encCert_dec (fld 5 (n / 16)), encCert_dec (rest 6 (n / 16)), pair_fld_rest 5, pair_fld_rest 4, pair_fld_rest 3, pair_fld_rest 2, pair_fld_rest 1, pair_fld_rest 0]; simp only [rest_zero]; omega
termination_by n
decreasing_by
  all_goals first
    | exact Nat.lt_of_le_of_lt (fld_le _ _) hl
    | exact Nat.lt_of_le_of_lt (rest_le _ _) hl

theorem encCert_inj {c c' : Cert} (h : encCert c = encCert c') : c = c' := by
  rw [← decCert_enc c, h, decCert_enc]

end Lean4Lean.Incomplete
