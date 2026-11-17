import Incomplete.Rules2

/-!
# The rules that read the environment: `constDF` and `extra`

For an environment given by tables, a constant's or rule's conditions are checked entry by
entry. Level lists are handled by codes for their length, closedness and pointwise
equivalence, and instantiating a fixed term at a numbered level list is a template whose holes
read that list (`tmplE`).
-/

namespace Incomplete
open Lean4Lean
open PR

attribute [local simp] eval_eqz eval_succ

variable {T : Tables}

/-! ### Level lists -/

theorem unpair_zero : unpair1 0 = 0 ∧ unpair2 0 = 0 := by
  have h : pair 0 0 = 0 := by simp [pair, tri]
  exact ⟨by simpa [h] using unpair1_pair 0 0, by simpa [h] using unpair2_pair 0 0⟩

theorem nthN_histN' (F : Nat → Nat → Nat) {n c : Nat} (h : c < n + 1) :
    nthN (histN F (n + 1)) (n - c) = cov F c := by
  have := nthN_histN F (n + 1) c h; simpa using this

theorem nthN_encList (ls : List VLevel) (i : Nat) :
    nthN (encList encLevel ls) i = encLevel (ls.getD i .zero) := by
  induction ls generalizing i with
  | nil =>
    have : ∀ i, iterTl 0 i = 0 := fun i => by
      induction i with
      | zero => rfl
      | succ i ih => simp [iterTl, ih, tlN, unpair_zero]
    simp [nthN, this, hdN, unpair_zero, encLevel, encList]
  | cons a ls ih =>
    cases i with
    | zero => simp [nthN, iterTl, hdN, encList]
    | succ i =>
      rw [nthN, iterTl_succ']
      simpa [tlN, encList, nthN] using ih i

def lenStep : PR := ifz (var 0) (num 0) (PR.succ (histAt (sndC (leq (var 0) (num 1)))))
def lenF (n h : Nat) : Nat := lenStep.eval (val2 n h)
theorem lenStep_computes : Computes2 lenStep lenF := by
  intro ρ; simp [lenF, lenStep, val2, eval_var]

theorem lenF_eq : ∀ ls : List VLevel, cov lenF (encList encLevel ls) = ls.length
  | [] => by rw [cov, lenF]; simp [lenStep, val2, eval_var, encList]
  | a :: ls => by
    rw [cov, lenF]
    simp only [lenStep, val2, eval_ifz, eval_var, vcons_zero, vcons_succ, eval_num, eval_succ,
      eval_histAt, eval_sndC, eval_leq, encList, Nat.add_sub_cancel, unpair2_pair,
      Nat.add_one_ne_zero, if_false]
    rw [nthN_histN' _ (by have := pair_ge_right (encLevel a) (encList encLevel ls); omega),
      lenF_eq ls]
    rfl

/-- The length of the level list numbered by the value of `L`. -/
def lenAt (L : PR) : PR := push L (covC lenStep)

@[simp] theorem eval_lenAt (L : PR) (ρ : Val) :
    (lenAt L).eval ρ = (decList decLevel (L.eval ρ)).length := by
  rw [lenAt, eval_push (covC_computes lenStep_computes), ← lenF_eq,
    encList_dec encLevel_dec]

def allStep : PR :=
  ifz (var 0) (num 0) (andz (notz (levAt (fstC (leq (var 0) (num 1)))))
    (histAt (sndC (leq (var 0) (num 1)))))
def allF (n h : Nat) : Nat := allStep.eval (val2 n h)
theorem allStep_computes : Computes2 allStep allF := by
  intro ρ; simp [allF, allStep, val2, eval_var]

theorem allF_eq : ∀ ls : List VLevel,
    cov allF (encList encLevel ls) = if ∀ l ∈ ls, l.WF 0 then 0 else 1
  | [] => by rw [cov, allF]; simp [allStep, val2, eval_var, encList]
  | a :: ls => by
    rw [cov, allF]
    simp only [allStep, val2, eval_ifz, eval_var, vcons_zero, vcons_succ, eval_num, eval_andz,
      eval_notz, eval_levAt, eval_fstC, eval_histAt, eval_sndC, eval_leq, encList,
      Nat.add_sub_cancel, unpair1_pair, unpair2_pair, Nat.add_one_ne_zero, if_false]
    rw [nthN_histN' _ (by have := pair_ge_right (encLevel a) (encList encLevel ls); omega),
      allF_eq ls]
    simp only [levNum, decLevel_enc, List.mem_cons, forall_eq_or_imp]
    by_cases h1 : a.WF 0 <;> by_cases h2 : ∀ l ∈ ls, l.WF 0 <;> simp [h1, h2]

/-- `0` exactly when every level of the list numbered by the value of `L` is closed. -/
def allAt (L : PR) : PR := push L (covC allStep)

@[simp] theorem eval_allAt (L : PR) (ρ : Val) :
    (allAt L).eval ρ = 0 ↔ ∀ l ∈ decList decLevel (L.eval ρ), l.WF 0 := by
  rw [allAt, eval_push (covC_computes allStep_computes), ← encList_dec encLevel_dec (L.eval ρ),
    allF_eq, decList_enc decLevel_enc]
  split <;> simp_all

/-- Pointwise equality of closed values, as `levNum` sees it. -/
def eqvL : List VLevel → List VLevel → Bool
  | [], [] => true
  | a :: as, b :: bs => (levNum (encLevel a) == levNum (encLevel b)) && eqvL as bs
  | _, _ => false

def eqvStep : PR :=
  let L := fstC (var 0)
  let L' := sndC (var 0)
  ifz L (ifz L' (num 0) (num 1)) <| ifz L' (num 1) <|
  andz (eqz (levAt (fstC (leq L (num 1)))) (levAt (fstC (leq L' (num 1)))))
    (histAt (cpair (sndC (leq L (num 1))) (sndC (leq L' (num 1)))))
def eqvF (n h : Nat) : Nat := eqvStep.eval (val2 n h)
theorem eqvStep_computes : Computes2 eqvStep eqvF := by
  intro ρ; simp [eqvF, eqvStep, val2, eval_var]

theorem eqvF_eq : ∀ ls ls' : List VLevel,
    cov eqvF (pair (encList encLevel ls) (encList encLevel ls')) = if eqvL ls ls' then 0 else 1
  | [], [] => by rw [cov, eqvF]; simp [eqvStep, val2, eval_var, encList, eqvL]
  | [], _ :: _ => by rw [cov, eqvF]; simp [eqvStep, val2, eval_var, encList, eqvL]
  | _ :: _, [] => by rw [cov, eqvF]; simp [eqvStep, val2, eval_var, encList, eqvL]
  | a :: ls, b :: ls' => by
    rw [cov, eqvF]
    simp only [eqvStep, val2, eval_ifz, eval_var, vcons_zero, vcons_succ, eval_num, eval_andz,
      eval_eqz, eval_levAt, eval_fstC, eval_histAt, eval_sndC, eval_leq, eval_cpair, encList,
      Nat.add_sub_cancel, unpair1_pair, unpair2_pair, Nat.add_one_ne_zero, if_false]
    rw [nthN_histN _ _ _ (by
      have := pair_ge_right (encLevel a) (encList encLevel ls)
      have := pair_ge_right (encLevel b) (encList encLevel ls')
      exact pair_lt_pair (by omega)), eqvF_eq ls ls']
    by_cases h1 : levNum (encLevel a) = levNum (encLevel b) <;> by_cases h2 : eqvL ls ls' <;>
      simp [eqvL, h1, h2]

/-- `0` exactly when the level lists numbered by the values of `L` and `L'` agree pointwise. -/
def eqvAt (L L' : PR) : PR := push (cpair L L') (covC eqvStep)

@[simp] theorem eval_eqvAt (L L' : PR) (ρ : Val) :
    (eqvAt L L').eval ρ = 0 ↔ eqvL (decList decLevel (L.eval ρ)) (decList decLevel (L'.eval ρ)) := by
  rw [eqvAt, eval_push (covC_computes eqvStep_computes), eval_cpair,
    ← encList_dec encLevel_dec (L.eval ρ), ← encList_dec encLevel_dec (L'.eval ρ), eqvF_eq,
    decList_enc decLevel_enc, decList_enc decLevel_enc]
  split <;> simp_all

theorem levNum_ne_zero {n : Nat} : levNum n ≠ 0 ↔ (decLevel n).WF 0 := by
  unfold levNum; split <;> simp_all

theorem equivs_eqvL : ∀ ls ls' : List VLevel, (∀ l ∈ ls, l.WF 0) → (∀ l ∈ ls', l.WF 0) →
    equivs T.deciders.equiv ls ls' = eqvL ls ls'
  | [], [], _, _ => rfl
  | [], _ :: _, _, _ | _ :: _, [], _, _ => rfl
  | a :: ls, b :: ls', h, h' => by
    simp only [equivs, eqvL]
    rw [equivs_eqvL ls ls' (fun l hl => h l (.tail _ hl)) (fun l hl => h' l (.tail _ hl))]
    congr 1
    simp [Tables.deciders, levNum, decLevel_enc, h a (.head _), h' b (.head _)]

/-! ### Templates -/

def tmplL (x : PR) : VLevel → PR
  | .zero => num 0
  | .succ l => tagC 4 1 (tmplL x l)
  | .max a b => tagC 4 2 (cpair (tmplL x a) (tmplL x b))
  | .imax a b => tagC 4 3 (cpair (tmplL x a) (tmplL x b))
  | .param i => nthC x (numC i)

theorem eval_tmplL (x : PR) (ρ : Val) :
    ∀ l : VLevel, (tmplL x l).eval ρ = encLevel (l.inst (decList decLevel (x.eval ρ)))
  | .zero => rfl
  | .succ l => by simp [tmplL, eval_tmplL x ρ l, VLevel.inst, encLevel]
  | .max a b => by simp [tmplL, eval_tmplL x ρ a, eval_tmplL x ρ b, VLevel.inst, encLevel]
  | .imax a b => by simp [tmplL, eval_tmplL x ρ a, eval_tmplL x ρ b, VLevel.inst, encLevel]
  | .param i => by
    simp only [tmplL, eval_nthC, eval_numC, VLevel.inst]
    conv => lhs; rw [← encList_dec encLevel_dec (x.eval ρ)]
    rw [nthN_encList]

def tmplLs (x : PR) : List VLevel → PR
  | [] => num 0
  | l :: ls => PR.succ (cpair (tmplL x l) (tmplLs x ls))

theorem eval_tmplLs (x : PR) (ρ : Val) :
    ∀ ls : List VLevel, (tmplLs x ls).eval ρ =
      encList encLevel (ls.map (VLevel.inst (decList decLevel (x.eval ρ))))
  | [] => rfl
  | l :: ls => by simp [tmplLs, eval_tmplL, eval_tmplLs x ρ ls, encList]

/-- A code for the number of `e.instL (decList decLevel x)`. -/
def tmplE (x : PR) : VExpr → PR
  | .bvar i => numC (7 * i)
  | .sort u => tagC 7 1 (tmplL x u)
  | .const c us => tagC 7 2 (cpair (numC (encName c)) (tmplLs x us))
  | .app f a => tagC 7 3 (cpair (tmplE x f) (tmplE x a))
  | .lam A b => tagC 7 4 (cpair (tmplE x A) (tmplE x b))
  | .forallE A b => tagC 7 5 (cpair (tmplE x A) (tmplE x b))
  | .proj s i e => tagC 7 6 (cpair (numC (encName s)) (cpair (numC i) (tmplE x e)))

theorem eval_tmplE (x : PR) (ρ : Val) :
    ∀ e : VExpr, (tmplE x e).eval ρ = encExpr (e.instL (decList decLevel (x.eval ρ)))
  | .bvar i => by simp [tmplE, VExpr.instL, encExpr]
  | .sort u => by simp [tmplE, VExpr.instL, encExpr, eval_tmplL]
  | .const c us => by simp [tmplE, VExpr.instL, encExpr, eval_tmplLs]
  | .app f a => by simp [tmplE, VExpr.instL, encExpr, eval_tmplE x ρ f, eval_tmplE x ρ a]
  | .lam f a => by simp [tmplE, VExpr.instL, encExpr, eval_tmplE x ρ f, eval_tmplE x ρ a]
  | .forallE f a => by simp [tmplE, VExpr.instL, encExpr, eval_tmplE x ρ f, eval_tmplE x ρ a]
  | .proj s i e => by simp [tmplE, VExpr.instL, encExpr, eval_tmplE x ρ e]

theorem decName_eq_iff (n : Nat) (c : Name) : decName n = c ↔ n = encName c :=
  ⟨fun h => by rw [← h, encName_dec], fun h => by rw [h, decName_enc]⟩

theorem decConst_eq_iff (n : Nat) (c : VConstant) : decConst n = c ↔ n = encConst c :=
  ⟨fun h => by rw [← h, encConst_dec], fun h => by rw [h, decConst_enc]⟩

theorem decDefEq_eq_iff (n : Nat) (c : VDefEq) : decDefEq n = c ↔ n = encDefEq c :=
  ⟨fun h => by rw [← h, encDefEq_dec], fun h => by rw [h, decDefEq_enc]⟩

/-! ### `constDF` -/

@[simp] theorem ite01_eq_zero {P : Prop} [Decidable P] : ((if P then (0 : Nat) else 1) = 0) ↔ P := by
  split <;> simp_all

theorem decCert_constDF {n : Nat} (h : n % 16 = 4) :
    decCert n = .constDF (decJudg (fld 0 (n / 16))) (decName (fld 1 (n / 16)))
      (decConst (fld 2 (n / 16))) (decList decLevel (fld 3 (n / 16)))
      (decList decLevel (rest 4 (n / 16))) := by
  rw [decCert]; simp [h]

/-- The judgment of `constDF`, as numbers. -/
def constJ (jn N LS LS' A : Nat) : Prop :=
  jn = pair (fld 0 jn) (pair (7 * pair N LS + 2) (pair (7 * pair N LS' + 2) A))

instance (jn N LS LS' A : Nat) : Decidable (constJ jn N LS LS' A) := by
  unfold constJ; exact inferInstance

theorem constJ_iff (jn N LS LS' : Nat) (A : VExpr) :
    decJudg jn = ⟨(decJudg jn).Γ, .const (decName N) (decList decLevel LS),
      .const (decName N) (decList decLevel LS'), A⟩ ↔ constJ jn N LS LS' (encExpr A) := by
  rw [decJudg_eq_iff]; simp [constJ, encJudg, encExpr, encName_dec, encList_dec encLevel_dec]

/-- `constDF`'s conditions for the table entry `ci`, when the name matches. -/
def constEntryOK (ci : VConstant) (jn N CI LS LS' : Nat) : Bool :=
  decide (CI = encConst ci ∧ (decList decLevel LS).length = ci.uvars ∧
    (∀ l ∈ decList decLevel LS, l.WF 0) ∧ (∀ l ∈ decList decLevel LS', l.WF 0) ∧
    eqvL (decList decLevel LS) (decList decLevel LS') = true ∧
    constJ jn N LS LS' (encExpr (ci.type.instL (decList decLevel LS))))

/-- `constDF`'s conditions against a constant table, first matching name first. -/
def constOK : List (Name × VConstant) → (jn N CI LS LS' : Nat) → Bool
  | [], _, _, _, _, _ => false
  | (n, ci) :: r, jn, N, CI, LS, LS' =>
    if N = encName n then constEntryOK ci jn N CI LS LS' else constOK r jn N CI LS LS'

theorem constEntry_eq (ci : VConstant) (jn N CI LS LS' : Nat) :
    (decide (decJudg jn = ⟨(decJudg jn).Γ, .const (decName N) (decList decLevel LS),
        .const (decName N) (decList decLevel LS'),
        (decConst CI).type.instL (decList decLevel LS)⟩ ∧
      some ci = some (decConst CI) ∧ (∀ l ∈ decList decLevel LS, l.WF 0) ∧
      (∀ l ∈ decList decLevel LS', l.WF 0) ∧
      (decList decLevel LS).length = (decConst CI).uvars) &&
      equivs T.deciders.equiv (decList decLevel LS) (decList decLevel LS')) =
    constEntryOK ci jn N CI LS LS' := by
  unfold constEntryOK
  by_cases hc : CI = encConst ci
  · have hc' : decConst CI = ci := (decConst_eq_iff _ _).2 hc
    simp only [hc', constJ_iff]
    apply Bool.eq_iff_iff.2
    simp only [Bool.and_eq_true, decide_eq_true_eq, hc, true_and]
    constructor
    · rintro ⟨⟨hj, hw, hw', hl⟩, he⟩
      exact ⟨hl, hw, hw', (equivs_eqvL _ _ hw hw') ▸ he, hj⟩
    · rintro ⟨hl, hw, hw', he, hj⟩
      exact ⟨⟨hj, hw, hw', hl⟩, (equivs_eqvL (T := T) _ _ hw hw') ▸ he⟩
  · have : some ci ≠ some (decConst CI) := fun e =>
      hc ((decConst_eq_iff _ _).1 (Option.some.inj e).symm)
    simp [this, hc]

theorem constOK_eq (tbl : List (Name × VConstant)) (jn N CI LS LS' : Nat) :
    (decide (decJudg jn = ⟨(decJudg jn).Γ, .const (decName N) (decList decLevel LS),
        .const (decName N) (decList decLevel LS'),
        (decConst CI).type.instL (decList decLevel LS)⟩ ∧
      tlookup tbl (decName N) = some (decConst CI) ∧ (∀ l ∈ decList decLevel LS, l.WF 0) ∧
      (∀ l ∈ decList decLevel LS', l.WF 0) ∧
      (decList decLevel LS).length = (decConst CI).uvars) &&
      equivs T.deciders.equiv (decList decLevel LS) (decList decLevel LS')) =
    constOK tbl jn N CI LS LS' := by
  induction tbl with
  | nil => simp [tlookup, constOK]
  | cons e r ih =>
    obtain ⟨n, ci⟩ := e
    simp only [tlookup, constOK]
    by_cases h : N = encName n
    · simp only [if_pos ((decName_eq_iff _ _).2 h), if_pos h]; exact constEntry_eq ci jn N CI LS LS'
    · simp only [if_neg (fun e => h ((decName_eq_iff _ _).1 e)), if_neg h]; exact ih

theorem certNum_constDF {R : Nat → Bool} (hR : R 4 = true) {n : Nat} (h : n % 16 = 4) :
    certNum T R n = if constOK T.consts (fld 0 (n / 16)) (fld 1 (n / 16)) (fld 2 (n / 16))
      (fld 3 (n / 16)) (rest 4 (n / 16)) then 0 else 1 := by
  rw [certNum, decCert_constDF h, ← constOK_eq (T := T)]
  simp only [Cert.usesOnly, Cert.check, Cert.tag, hR, Bool.true_and, decJudg_Γ]
  rfl

def constHdC (A : PR) : PR :=
  eqz jC (judgC (fldC 0 jC) (tagC 7 2 (cpair (fldC 1 xC) (fldC 3 xC)))
    (tagC 7 2 (cpair (fldC 1 xC) (restC 4 xC))) A)

def constEntryC (ci : VConstant) : PR :=
  andz (eqz (fldC 2 xC) (numC (encConst ci))) <|
  andz (eqz (lenAt (fldC 3 xC)) (numC ci.uvars)) <|
  andz (allAt (fldC 3 xC)) <| andz (allAt (restC 4 xC)) <|
  andz (eqvAt (fldC 3 xC) (restC 4 xC)) (constHdC (tmplE (fldC 3 xC) ci.type))

theorem eval_constEntryC (ci : VConstant) (ρ : Val) : (constEntryC ci).eval ρ =
    if constEntryOK ci (fld 0 (ρ 0 / 16)) (fld 1 (ρ 0 / 16)) (fld 2 (ρ 0 / 16)) (fld 3 (ρ 0 / 16))
      (rest 4 (ρ 0 / 16)) then 0 else 1 := by
  simp only [constEntryC, constHdC, constEntryOK, eval_andz, eval_eqz, eval_fldC, eval_restC,
    eval_xC, eval_jC, eval_numC, eval_lenAt, eval_allAt, eval_eqvAt, eval_judgC, eval_tagC,
    eval_cpair, eval_tmplE, ite01_eq_zero]
  exact ite_iff (by rw [decide_eq_true_eq]; exact Iff.rfl) _ _

def constDFC : List (Name × VConstant) → PR
  | [] => num 1
  | (n, ci) :: r => ifz (eqz (fldC 1 xC) (numC (encName n))) (constEntryC ci) (constDFC r)

theorem eval_constDFC (ρ : Val) : ∀ tbl : List (Name × VConstant), (constDFC tbl).eval ρ =
    if constOK tbl (fld 0 (ρ 0 / 16)) (fld 1 (ρ 0 / 16)) (fld 2 (ρ 0 / 16)) (fld 3 (ρ 0 / 16))
      (rest 4 (ρ 0 / 16)) then 0 else 1
  | [] => by simp [constDFC, constOK]
  | (n, ci) :: r => by
    simp only [constDFC, constOK, eval_ifz, eval_eqz, eval_fldC, eval_xC, eval_numC]
    split
    · rw [eval_constEntryC]
    · exact eval_constDFC ρ r

theorem constDFC_spec {R : Nat → Bool} (hR : R 4 = true) {ρ : Val} (h : ρ 0 % 16 = 4)
    (_ : HistOK T R ρ) : (constDFC T.consts).eval ρ = certNum T R (ρ 0) := by
  rw [certNum_constDF hR h, eval_constDFC]

/-! ### `extra` -/

theorem decCert_extra {n : Nat} (h : n % 16 = 12) :
    decCert n = .extra (decJudg (fld 0 (n / 16))) (decDefEq (fld 1 (n / 16)))
      (decList decLevel (rest 2 (n / 16))) := by
  rw [decCert]; simp [h]

/-- The judgment of `extra` for the rule `d`, as numbers. -/
def extraJ (jn : Nat) (d : VDefEq) (LS : Nat) : Prop :=
  jn = pair (fld 0 jn) (pair (encExpr (d.lhs.instL (decList decLevel LS)))
    (pair (encExpr (d.rhs.instL (decList decLevel LS)))
      (encExpr (d.type.instL (decList decLevel LS)))))

instance (jn : Nat) (d : VDefEq) (LS : Nat) : Decidable (extraJ jn d LS) := by
  unfold extraJ; exact inferInstance

def extraEntryOK (d : VDefEq) (jn LS : Nat) : Bool :=
  decide ((decList decLevel LS).length = d.uvars ∧ (∀ l ∈ decList decLevel LS, l.WF 0) ∧
    extraJ jn d LS)

def extraOK : List VDefEq → (jn DF LS : Nat) → Bool
  | [], _, _, _ => false
  | d :: r, jn, DF, LS => if DF = encDefEq d then extraEntryOK d jn LS else extraOK r jn DF LS

theorem extraOK_eq (rules : List VDefEq) (jn DF LS : Nat) :
    (decide (decJudg jn = ⟨(decJudg jn).Γ, (decDefEq DF).lhs.instL (decList decLevel LS),
        (decDefEq DF).rhs.instL (decList decLevel LS), (decDefEq DF).type.instL (decList decLevel LS)⟩ ∧
      (∀ l ∈ decList decLevel LS, l.WF 0) ∧ (decList decLevel LS).length = (decDefEq DF).uvars) &&
      decide (decDefEq DF ∈ rules)) = extraOK rules jn DF LS := by
  induction rules with
  | nil => simp [extraOK]
  | cons d r ih =>
    simp only [extraOK]
    by_cases h : DF = encDefEq d
    · simp only [if_pos h, (decDefEq_eq_iff _ _).2 h]
      unfold extraEntryOK
      apply Bool.eq_iff_iff.2
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.mem_cons, true_or, and_true]
      rw [decJudg_eq_iff]
      exact ⟨fun ⟨a, b, c⟩ => ⟨c, b, by simpa [extraJ, encJudg] using a⟩,
        fun ⟨c, b, a⟩ => ⟨by simpa [extraJ, encJudg] using a, b, c⟩⟩
    · have hd : decDefEq DF ≠ d := fun e => h ((decDefEq_eq_iff _ _).1 e)
      simp only [if_neg h, ← ih]
      simp [hd]

theorem certNum_extra {R : Nat → Bool} (hR : R 12 = true) {n : Nat} (h : n % 16 = 12) :
    certNum T R n = if extraOK T.rules (fld 0 (n / 16)) (fld 1 (n / 16)) (rest 2 (n / 16))
      then 0 else 1 := by
  rw [certNum, decCert_extra h, ← extraOK_eq]
  simp only [Cert.usesOnly, Cert.check, Cert.tag, hR, Bool.true_and, decJudg_Γ, Tables.deciders]
  rfl

def extraEntryC (d : VDefEq) : PR :=
  andz (eqz (lenAt (restC 2 xC)) (numC d.uvars)) <| andz (allAt (restC 2 xC)) <|
  eqz jC (judgC (fldC 0 jC) (tmplE (restC 2 xC) d.lhs) (tmplE (restC 2 xC) d.rhs)
    (tmplE (restC 2 xC) d.type))

theorem eval_extraEntryC (d : VDefEq) (ρ : Val) : (extraEntryC d).eval ρ =
    if extraEntryOK d (fld 0 (ρ 0 / 16)) (rest 2 (ρ 0 / 16)) then 0 else 1 := by
  simp only [extraEntryC, extraEntryOK, eval_andz, eval_eqz, eval_restC, eval_xC, eval_jC,
    eval_fldC, eval_numC, eval_lenAt, eval_allAt, eval_judgC, eval_tmplE, decide_eq_true_eq,
    ite01_eq_zero]
  exact ite_iff Iff.rfl _ _

def extraC : List VDefEq → PR
  | [] => num 1
  | d :: r => ifz (eqz (fldC 1 xC) (numC (encDefEq d))) (extraEntryC d) (extraC r)

theorem eval_extraC (ρ : Val) : ∀ rules : List VDefEq, (extraC rules).eval ρ =
    if extraOK rules (fld 0 (ρ 0 / 16)) (fld 1 (ρ 0 / 16)) (rest 2 (ρ 0 / 16)) then 0 else 1
  | [] => by simp [extraC, extraOK]
  | d :: r => by
    simp only [extraC, extraOK, eval_ifz, eval_eqz, eval_fldC, eval_xC, eval_numC]
    split
    · rw [eval_extraEntryC]
    · exact eval_extraC ρ r

theorem extraC_spec {R : Nat → Bool} (hR : R 12 = true) {ρ : Val} (h : ρ 0 % 16 = 12)
    (_ : HistOK T R ρ) : (extraC T.rules).eval ρ = certNum T R (ρ 0) := by
  rw [certNum_extra hR h, eval_extraC]

end Incomplete
