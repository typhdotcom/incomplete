import Incomplete.ListPR

/-!
# The projection rules

`projEta`, `projIota` and `projDF` read the inductive-block table. Whether a projection is
allowed is decided at the closed levels a certificate supplies, by evaluating the block's and the
fields' levels there.
-/

namespace Lean4Lean.Incomplete
open PR VExpr

attribute [local simp] eval_eqz eval_succ

variable {T : Tables}

/-! ### Closed levels and allowed projections -/

theorem inst_closed {ls : List VLevel} (h : ∀ l ∈ ls, l.WF 0) : ∀ l : VLevel, (l.inst ls).WF 0
  | .zero => trivial
  | .succ l => inst_closed h l
  | .max a b | .imax a b => ⟨inst_closed h a, inst_closed h b⟩
  | .param i => by
    simp only [VLevel.inst, List.getD_eq_getElem?_getD]
    cases hi : ls[i]? with
    | none => trivial
    | some l => exact h l (List.mem_of_getElem? hi)

theorem neverZero_closed {l : VLevel} (h : l.WF 0) : l.IsNeverZero ↔ l.eval [] ≠ 0 :=
  ⟨fun hn => hn [], fun hn ls => by rw [VLevel.eval_closed h]; exact hn⟩

theorem equiv_zero_closed {l : VLevel} (h : l.WF 0) : l ≈ .zero ↔ l.eval [] = 0 :=
  ⟨fun e => by have := congrFun e []; simpa [VLevel.eval] using this,
   fun e => funext fun ls => by rw [VLevel.eval_closed h]; simpa [VLevel.eval] using e⟩

theorem levNum_inst {ls : List VLevel} (h : ∀ l ∈ ls, l.WF 0) (l : VLevel) :
    levNum (encLevel (l.inst ls)) = 1 ↔ (l.inst ls).eval [] = 0 := by
  simp [levNum, decLevel_enc, inst_closed h l]

/-- `0` exactly when the level `l` at the level list numbered by `LS` has value `0`. -/
def zeroC (LS : PR) (l : VLevel) : PR := eqz (levAt (tmplL LS l)) (num 1)

theorem eval_zeroC {LS : PR} {ρ : Val} {ls : List VLevel} (hL : LS.eval ρ = encList encLevel ls)
    (h : ∀ l ∈ ls, l.WF 0) (l : VLevel) :
    (zeroC LS l).eval ρ = 0 ↔ l.inst ls ≈ .zero := by
  rw [zeroC, eval_eqz, eval_levAt, eval_num, eval_tmplL, hL, decList_enc decLevel_enc,
    levNum_inst h, equiv_zero_closed (inst_closed h l)]

open Classical in
/-- The conditions on the earlier fields `j < m` for projecting the `k`th. -/
noncomputable def earlierC (LS : PR) (c : VConstructor) (k : Nat) : Nat → PR
  | 0 => num 0
  | j + 1 => andz (earlierC LS c k j) <|
    match c.fields[j]? with
    | some f => if c.Unused k j then num 0 else zeroC LS f.level
    | none => num 0

/-- `0` exactly when the `k`th projection is allowed at the level list numbered by `LS`. -/
noncomputable def paC (LS : PR) (d : VInductDecl) (c : VConstructor) (k : Nat) : PR :=
  ifz (zeroC LS d.level)
    (andz (match c.fields[k]? with | some f => zeroC LS f.level | none => num 0) (earlierC LS c k k))
    (num 0)

theorem eval_earlierC {LS : PR} {ρ : Val} {ls : List VLevel} (hL : LS.eval ρ = encList encLevel ls)
    (h : ∀ l ∈ ls, l.WF 0) (c : VConstructor) (k : Nat) : ∀ m, (earlierC LS c k m).eval ρ = 0 ↔
      ∀ j < m, ∀ f, c.fields[j]? = some f → f.level.inst ls ≈ .zero ∨ c.Unused k j
  | 0 => by simp [earlierC]
  | m + 1 => by
    rw [earlierC, eval_andz, ite01_eq_zero, eval_earlierC hL h c k m]
    constructor
    · rintro ⟨h1, h2⟩ j hj f hf
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · exact h1 j hj f hf
      · rw [hf] at h2; simp only at h2
        split at h2
        · exact .inr ‹_›
        · exact .inl ((eval_zeroC hL h _).1 h2)
    · intro H
      refine ⟨fun j hj f hf => H j (by omega) f hf, ?_⟩
      cases hf : c.fields[m]? with
      | none => rfl
      | some f =>
        simp only
        split
        · rfl
        · rename_i hu
          exact (eval_zeroC hL h _).2 ((H m (by omega) f hf).resolve_right hu)

theorem eval_paC {LS : PR} {ρ : Val} {ls : List VLevel} (hL : LS.eval ρ = encList encLevel ls)
    (h : ∀ l ∈ ls, l.WF 0) (d : VInductDecl) (c : VConstructor) (k : Nat) :
    (paC LS d c k).eval ρ = 0 ↔ d.ProjAllowed c ls k := by
  have hz := eval_zeroC hL h d.level
  have hnz : ¬(d.level.inst ls).IsNeverZero ↔ d.level.inst ls ≈ .zero := by
    rw [neverZero_closed (inst_closed h _), equiv_zero_closed (inst_closed h _)]; omega
  rw [paC, eval_ifz, VInductDecl.ProjAllowed, hnz]
  by_cases hd : (zeroC LS d.level).eval ρ = 0
  · rw [if_pos hd, eval_andz, ite01_eq_zero, eval_earlierC hL h c k k]
    have hd' := hz.1 hd
    constructor
    · rintro ⟨h1, h2⟩ _
      refine ⟨fun f hf => ?_, h2⟩
      rw [hf] at h1; exact (eval_zeroC hL h _).1 h1
    · intro H
      obtain ⟨h1, h2⟩ := H hd'
      refine ⟨?_, h2⟩
      cases hf : c.fields[k]? with
      | none => rfl
      | some f => exact (eval_zeroC hL h _).2 (h1 f hf)
  · rw [if_neg hd]
    exact ⟨fun _ e => absurd (hz.2 e) hd, fun _ => rfl⟩

/-- `0` exactly when every projection `k < m` is allowed. -/
noncomputable def allPaC (LS : PR) (d : VInductDecl) (c : VConstructor) : Nat → PR
  | 0 => num 0
  | m + 1 => andz (allPaC LS d c m) (paC LS d c m)

theorem eval_allPaC {LS : PR} {ρ : Val} {ls : List VLevel} (hL : LS.eval ρ = encList encLevel ls)
    (h : ∀ l ∈ ls, l.WF 0) (d : VInductDecl) (c : VConstructor) : ∀ m,
    (allPaC LS d c m).eval ρ = 0 ↔ ∀ k < m, d.ProjAllowed c ls k
  | 0 => by simp [allPaC]
  | m + 1 => by
    rw [allPaC, eval_andz, ite01_eq_zero, eval_allPaC hL h d c m, eval_paC hL h]
    constructor
    · rintro ⟨h1, h2⟩ k hk
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
      · exact h1 k hk
      · exact h2
    · intro H; exact ⟨fun k hk => H k (by omega), H m (by omega)⟩

@[simp] theorem decExpr_const_num (a b : Nat) :
    decExpr (7 * pair a b + 2) = .const (decName a) (decList decLevel b) := by
  rw [decExpr]; simp [tag_div]

theorem decList_decExpr_eq_iff {a : Nat} {L : List VExpr} : decList decExpr a = L ↔ a = encList encExpr L :=
  ⟨fun h => by rw [← h, encList_dec encExpr_dec], fun h => by rw [h, decList_enc decExpr_enc]⟩

/-! ### `projEta` -/

theorem decCert_projEta {n : Nat} (h : n % 16 = 15) :
    decCert n = .projEta (decJudg (fld 0 (n / 16))) (decName (fld 1 (n / 16)))
      (decList decLevel (fld 2 (n / 16))) (decList decExpr (fld 3 (n / 16)))
      (decExpr (fld 4 (n / 16))) (decCert (fld 5 (n / 16))) (decCert (rest 6 (n / 16))) := by
  rw [decCert]; simp [h]

/-- The `projEta` conditions for the type `T'` of `d` with single constructor `c`. -/
def etaCond (T : Tables) (R : Nat → Bool) (d : VInductDecl) (T' : VInductiveType)
    (c : VConstructor) (x : Nat) : Prop :=
  let j := decJudg (fld 0 x)
  let s := decName (fld 1 x)
  let ls := decList decLevel (fld 2 x)
  let AsR := decList decExpr (fld 3 x)
  let e := decExpr (fld 4 x)
  (T'.indices = [] ∧ d.isRec = false ∧ (∀ l ∈ ls, l.WF 0) ∧ ls.length = d.uvars ∧
    AsR.length = d.params.length ∧
    j = ⟨j.Γ, e, .appN (.const c.name ls) (AsR.reverse ++ VExpr.projs s c.fields.length e),
      .appN (.const s ls) AsR.reverse⟩ ∧
    (decCert (fld 5 x)).j = ⟨j.Γ, e, e, .appN (.const s ls) AsR.reverse⟩ ∧
    (decCert (rest 6 x)).j = ⟨j.Γ, j.e2, j.e2, .appN (.const s ls) AsR.reverse⟩) ∧
  (∀ k < c.fields.length, d.ProjAllowed c ls k) ∧
  certNum T R (fld 5 x) = 0 ∧ certNum T R (rest 6 x) = 0

def etaCondT (T : Tables) (R : Nat → Bool) (x : Nat) : Prop :=
  match ilookup T.inducts (decName (fld 1 x)) with
  | some (d, t) => match singleCtor d t with
    | some (T', c) => etaCond T R d T' c x
    | none => False
  | none => False

open Classical in
theorem certNum_projEta {R : Nat → Bool} (hR : R 15 = true) {n : Nat} (h : n % 16 = 15) :
    certNum T R n = if etaCondT T R (n / 16) then 0 else 1 := by
  rw [certNum, decCert_projEta h]
  refine ite_iff ?_ _ _
  simp only [Cert.usesOnly, Cert.check, Cert.tag, hR, Bool.true_and, etaCondT, Tables.env]
  generalize ilookup T.inducts (decName (fld 1 (n / 16))) = o
  rcases o with _ | ⟨⟨d, t⟩⟩
  · simp
  simp only
  generalize singleCtor d t = o
  rcases o with _ | ⟨⟨T', c⟩⟩
  · simp
  simp only [etaCond, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    projOK, childOK]
  exact ⟨fun ⟨⟨u1, u2⟩, ⟨⟨D, pa⟩, k1⟩, k2⟩ => ⟨D, pa, ⟨u1, k1⟩, u2, k2⟩,
    fun ⟨D, pa, ⟨u1, k1⟩, u2, k2⟩ => ⟨⟨u1, u2⟩, ⟨⟨D, pa⟩, k1⟩, k2⟩⟩

/-- The length of the expression list numbered by the value of `L`. -/
def lenE (L : PR) : PR := lenAt L

@[simp] theorem eval_lenE (L : PR) (ρ : Val) :
    (lenE L).eval ρ = (decList decExpr (L.eval ρ)).length := eval_lenAt' L ρ

/-- `const n ls` for the name numbered by `N` and the level list numbered by `LS`. -/
def constNC (N LS : PR) : PR := tagC 7 2 (cpair N LS)

@[simp] theorem eval_constNC (N LS : PR) (ρ : Val) :
    (constNC N LS).eval ρ = encExpr (.const (decName (N.eval ρ)) (decList decLevel (LS.eval ρ))) := by
  simp [constNC, encExpr, encName_dec, encList_dec encLevel_dec]

open Classical in
noncomputable def etaEntryC (d : VInductDecl) (T' : VInductiveType) (c : VConstructor) : PR :=
  let N := fldC 1 xC
  let LS := fldC 2 xC
  let AR := fldC 3 xC
  let E := fldC 4 xC
  let Z := appRP (constNC N LS) AR
  let Y := appRP (appRP (constNC (numC (encName c.name)) LS) AR)
    (projsP (numC c.fields.length) N E (num 0))
  if T'.indices = [] ∧ d.isRec = false then
    andz (allAt LS) <| andz (eqz (lenAt LS) (numC d.uvars)) <|
    andz (eqz (lenE AR) (numC d.params.length)) <|
    andz (eqz jC (judgC (fldC 0 jC) E Y Z)) <|
    andz (eqz (childJC (fldC 5 xC)) (judgC (fldC 0 jC) E E Z)) <|
    andz (eqz (childJC (restC 6 xC)) (judgC (fldC 0 jC) (fldC 2 jC) (fldC 2 jC) Z)) <|
    andz (allPaC LS d c c.fields.length) <| andz (histAt (fldC 5 xC)) (histAt (restC 6 xC))
  else num 1

theorem eq_ite01 {n : Nat} {P : Prop} [Decidable P] (h1 : n ≤ 1) (h2 : n = 0 ↔ P) :
    n = if P then 0 else 1 := by
  split <;> rename_i hp
  · exact h2.2 hp
  · have := mt h2.1 hp; omega

theorem andz_le (a b : PR) (ρ : Val) : (andz a b).eval ρ ≤ 1 := by
  rw [eval_andz]; split <;> omega

theorem eval_andz_zero (a b : PR) (ρ : Val) :
    (andz a b).eval ρ = 0 ↔ a.eval ρ = 0 ∧ b.eval ρ = 0 := by
  rw [eval_andz]; exact ite01_eq_zero

open Classical in
theorem eval_etaEntryC {R : Nat → Bool} {ρ : Val} (h : ρ 0 % 16 = 15) (hv : HistOK T R ρ)
    (d : VInductDecl) (T' : VInductiveType) (c : VConstructor) :
    (etaEntryC d T' c).eval ρ = if etaCond T R d T' c (ρ 0 / 16) then 0 else 1 := by
  unfold etaEntryC
  split
  · rename_i hf
    refine eq_ite01 (andz_le _ _ _) ?_
    generalize hx : ρ 0 / 16 = x
    have hxx : xC.eval ρ = x := by rw [eval_xC, hx]
    have hlt5 : fld 5 x < ρ 0 := hx ▸ fld_lt (by omega) 5
    have hlt6 : rest 6 x < ρ 0 := hx ▸ rest_lt (by omega) 6
    have hLS : (fldC 2 xC).eval ρ = encList encLevel (decList decLevel (fld 2 x)) := by
      rw [eval_fldC, hxx, encList_dec encLevel_dec]
    have hZ : (appRP (constNC (fldC 1 xC) (fldC 2 xC)) (fldC 3 xC)).eval ρ =
        encExpr (.appN (.const (decName (fld 1 x)) (decList decLevel (fld 2 x)))
          (decList decExpr (fld 3 x)).reverse) := by
      simp only [eval_appRP, eval_constNC, eval_fldC, hxx, decExpr_enc]
    have hY : (appRP (appRP (constNC (numC (encName c.name)) (fldC 2 xC)) (fldC 3 xC))
        (projsP (numC c.fields.length) (fldC 1 xC) (fldC 4 xC) (num 0))).eval ρ =
        encExpr (.appN (.const c.name (decList decLevel (fld 2 x)))
          ((decList decExpr (fld 3 x)).reverse ++
            VExpr.projs (decName (fld 1 x)) c.fields.length (decExpr (fld 4 x)))) := by
      rw [eval_appRP, eval_projsP _ _ _ _ ρ (decName (fld 1 x)) (decExpr (fld 4 x)) []
        (by rw [eval_fldC, hxx, encName_dec]) (by rw [eval_fldC, hxx, encExpr_dec]) rfl]
      simp only [eval_appRP, eval_constNC, eval_fldC, eval_numC, hxx, decExpr_enc, decName_enc,
        List.append_nil, decList_enc decExpr_enc, List.reverse_reverse, VExpr.appN_append]
    have c4 : (eqz jC (judgC (fldC 0 jC) (fldC 4 xC) (appRP (appRP (constNC (numC (encName c.name))
        (fldC 2 xC)) (fldC 3 xC)) (projsP (numC c.fields.length) (fldC 1 xC) (fldC 4 xC) (num 0)))
        (appRP (constNC (fldC 1 xC) (fldC 2 xC)) (fldC 3 xC)))).eval ρ = 0 ↔
        decJudg (fld 0 x) = ⟨(decJudg (fld 0 x)).Γ, decExpr (fld 4 x),
          .appN (.const c.name (decList decLevel (fld 2 x)))
            ((decList decExpr (fld 3 x)).reverse ++
              VExpr.projs (decName (fld 1 x)) c.fields.length (decExpr (fld 4 x))),
          .appN (.const (decName (fld 1 x)) (decList decLevel (fld 2 x)))
            (decList decExpr (fld 3 x)).reverse⟩ := by
      rw [eval_eqz, eval_judgC, hY, hZ, decJudg_eq_iff, encJudg_mk', decJudg_Γ, encList_decList,
        encExpr_dec]
      simp only [eval_jC, eval_fldC, hx, hxx]
    have c5 : (eqz (childJC (fldC 5 xC)) (judgC (fldC 0 jC) (fldC 4 xC) (fldC 4 xC)
        (appRP (constNC (fldC 1 xC) (fldC 2 xC)) (fldC 3 xC)))).eval ρ = 0 ↔
        (decCert (fld 5 x)).j = ⟨(decJudg (fld 0 x)).Γ, decExpr (fld 4 x), decExpr (fld 4 x),
          .appN (.const (decName (fld 1 x)) (decList decLevel (fld 2 x)))
            (decList decExpr (fld 3 x)).reverse⟩ := by
      rw [eval_eqz, eval_judgC, hZ, childJ_iff, encJudg_mk', decJudg_Γ, encList_decList,
        encExpr_dec]
      simp only [eval_jC, eval_childJC, eval_fldC, hx, hxx]
    have c6 : (eqz (childJC (restC 6 xC)) (judgC (fldC 0 jC) (fldC 2 jC) (fldC 2 jC)
        (appRP (constNC (fldC 1 xC) (fldC 2 xC)) (fldC 3 xC)))).eval ρ = 0 ↔
        (decCert (rest 6 x)).j = ⟨(decJudg (fld 0 x)).Γ, (decJudg (fld 0 x)).e2,
          (decJudg (fld 0 x)).e2, .appN (.const (decName (fld 1 x)) (decList decLevel (fld 2 x)))
            (decList decExpr (fld 3 x)).reverse⟩ := by
      rw [eval_eqz, eval_judgC, hZ, childJ_iff, encJudg_mk', decJudg_Γ, decJudg_e2, encList_decList,
        encExpr_dec]
      simp only [eval_jC, eval_childJC, eval_fldC, eval_restC, hx, hxx]
    have k5 : (histAt (fldC 5 xC)).eval ρ = certNum T R (fld 5 x) := by
      rw [eval_histAt, eval_fldC, hxx, hv _ hlt5]
    have k6 : (histAt (restC 6 xC)).eval ρ = certNum T R (rest 6 x) := by
      rw [eval_histAt, eval_restC, hxx, hv _ hlt6]
    simp only [eval_andz_zero, eval_allAt, hLS, decList_enc decLevel_enc, eval_eqz, eval_lenAt,
      eval_lenE, eval_numC, eval_fldC, hxx, c4, c5, c6, k5, k6, etaCond]
    by_cases hw : ∀ l ∈ decList decLevel (fld 2 x), l.WF 0
    · rw [eval_allPaC hLS hw]
      exact ⟨fun ⟨u1, u2, u3, u4, u5, u6, u7, u8, u9⟩ => ⟨⟨hf.1, hf.2, u1, u2, u3, u4, u5, u6⟩,
        u7, u8, u9⟩, fun ⟨⟨_, _, u1, u2, u3, u4, u5, u6⟩, u7, u8, u9⟩ =>
        ⟨u1, u2, u3, u4, u5, u6, u7, u8, u9⟩⟩
    · exact ⟨fun ⟨u1, _⟩ => absurd u1 hw, fun ⟨⟨_, _, u1, _⟩, _⟩ => absurd u1 hw⟩
  · rename_i hf
    rw [eval_num, if_neg]
    rintro ⟨⟨h1, h2, -⟩, -⟩; exact hf ⟨h1, h2⟩

/-! ### Dispatch on the block table and the field index -/

def indTabC (entry : VInductDecl → Nat → PR) : List (Name × (VInductDecl × Nat)) → PR
  | [] => num 1
  | (n, (d, t)) :: r => ifz (eqz (fldC 1 xC) (numC (encName n))) (entry d t) (indTabC entry r)

theorem eval_indTabC (entry : VInductDecl → Nat → PR) (ρ : Val) :
    ∀ tbl, (indTabC entry tbl).eval ρ =
      match ilookup tbl (decName (fld 1 (ρ 0 / 16))) with
      | some (d, t) => (entry d t).eval ρ
      | none => 1
  | [] => by simp [indTabC, ilookup]
  | (n, (d, t)) :: r => by
    simp only [indTabC, ilookup, eval_ifz, eval_eqz, eval_fldC, eval_xC, eval_numC]
    by_cases h : fld 1 (ρ 0 / 16) = encName n
    · rw [if_pos h, if_pos (by rw [h, decName_enc])]
    · rw [if_neg h, if_neg (by rintro rfl; exact h (encName_dec _).symm)]
      exact eval_indTabC entry ρ r

def ctorEnt (g : VInductDecl → VInductiveType → VConstructor → PR) (d : VInductDecl) (t : Nat) : PR :=
  match singleCtor d t with
  | some (T', c) => g d T' c
  | none => num 1

def fieldTab (g : Nat → VField → PR) : List VField → Nat → PR
  | [], _ => num 1
  | f :: fs, i => ifz (eqz (fldC 2 xC) (numC i)) (g i f) (fieldTab g fs (i + 1))

theorem eval_fieldTab (g : Nat → VField → PR) (ρ : Val) : ∀ fs i, (fieldTab g fs i).eval ρ =
    if i ≤ fld 2 (ρ 0 / 16) then
      (match fs[fld 2 (ρ 0 / 16) - i]? with
      | some f => (g (fld 2 (ρ 0 / 16)) f).eval ρ
      | none => 1)
    else 1
  | [], i => by simp [fieldTab]
  | f :: fs, i => by
    simp only [fieldTab, eval_ifz, eval_eqz, eval_fldC, eval_xC, eval_numC]
    by_cases h : fld 2 (ρ 0 / 16) = i
    · rw [if_pos h, if_pos (by omega), h, Nat.sub_self]; rfl
    · rw [if_neg h, eval_fieldTab g ρ fs (i + 1)]
      by_cases h' : i + 1 ≤ fld 2 (ρ 0 / 16)
      · rw [if_pos h', if_pos (by omega), show fld 2 (ρ 0 / 16) - i = (fld 2 (ρ 0 / 16) - (i + 1)) + 1
          by omega, List.getElem?_cons_succ]
      · rw [if_neg h', if_neg (by omega)]

theorem eval_fieldTab0 (g : Nat → VField → PR) (ρ : Val) (fs : List VField) :
    (fieldTab g fs 0).eval ρ = match fs[fld 2 (ρ 0 / 16)]? with
      | some f => (g (fld 2 (ρ 0 / 16)) f).eval ρ
      | none => 1 := by
  rw [eval_fieldTab, if_pos (Nat.zero_le _), Nat.sub_zero]

/-! ### Shared rewriting -/

theorem j_decJudg' (k : Nat) : (decCert k).j = decJudg (fld 0 (k / 16)) := by
  rw [← j_dec, decJudg_enc]

@[simp] theorem eval_projsP' (k S E R0 : PR) (ρ : Val) :
    (projsP k S E R0).eval ρ = encList encExpr ((VExpr.projs (decName (S.eval ρ)) (k.eval ρ)
      (decExpr (E.eval ρ))).reverse ++ decList decExpr (R0.eval ρ)) :=
  eval_projsP k S E R0 ρ _ _ _ (encName_dec _).symm (encExpr_dec _).symm
    (encList_dec encExpr_dec _).symm

theorem eqzJ (J G A B C : PR) (ρ : Val) : (eqz J (judgC G A B C)).eval ρ = 0 ↔
    decJudg (J.eval ρ) = ⟨decList decExpr (G.eval ρ), decExpr (A.eval ρ), decExpr (B.eval ρ),
      decExpr (C.eval ρ)⟩ := by
  rw [eval_eqz, eval_judgC, decJudg_eq_iff, encJudg_mk]

@[simp] theorem decExpr_proj_num (a b c : Nat) :
    decExpr (7 * pair a (pair b c) + 6) = .proj (decName a) b (decExpr c) := by
  rw [decExpr]; simp [tag_div]

@[simp] theorem decExpr_sort_num (a : Nat) : decExpr (7 * a + 1) = .sort (decLevel a) := by
  rw [decExpr]; simp [tag_div]

theorem decExpr_substNum (a R k : Nat) :
    decExpr (substNum a R k) = (decExpr a).subst ((listS (decList decExpr R)).liftN k) :=
  decExpr_enc _

theorem projType_eq {c : VConstructor} {k : Nat} {f : VField} (hf : c.fields[k]? = some f)
    (ls : List VLevel) (s : Name) (AsR : List VExpr) (e : VExpr) :
    c.projType ls s k AsR.reverse e =
      (f.type.instL ls).subst ((listS ((VExpr.projs s k e).reverse ++ AsR)).liftN 0) := by
  have := projType_num c ls s k AsR e
  rw [hf] at this
  have := congrArg decExpr this
  rwa [decExpr_enc, decExpr_substNum, decExpr_enc, decList_enc decExpr_enc] at this

/-- The value of `R.reverse[k]?` for a list of length `n > k`, read off its number. -/
theorem getElem?_reverse_iff {L : List VExpr} {n k : Nat} (hn : L.length = n) (hk : k < n)
    (y : VExpr) : L.reverse[k]? = some y ↔ nthN (encList encExpr L) (n - 1 - k) = encExpr y := by
  subst hn
  rw [List.getElem?_reverse hk, List.getElem?_eq_getElem (by omega), nthN_encList_lt _ _ _ (by omega),
    Option.some.injEq]
  exact ⟨fun h => by rw [h], fun h => by rw [← decExpr_enc L[_], h, decExpr_enc]⟩

/-! ### `projIota` -/

theorem decCert_projIota {n : Nat} (h : n % 16 = 14) :
    decCert n = .projIota (decJudg (fld 0 (n / 16))) (decName (fld 1 (n / 16))) (fld 2 (n / 16))
      (decList decLevel (fld 3 (n / 16))) (decList decExpr (fld 4 (n / 16)))
      (decList decExpr (fld 5 (n / 16))) (decList decExpr (fld 6 (n / 16)))
      (decCert (fld 7 (n / 16))) (decCert (fld 8 (n / 16))) (decCert (rest 9 (n / 16))) := by
  rw [decCert]; simp [h]

def iotaCond (T : Tables) (R : Nat → Bool) (d : VInductDecl) (T' : VInductiveType)
    (c : VConstructor) (k : Nat) (f : VField) (x : Nat) : Prop :=
  let j := decJudg (fld 0 x)
  let s := decName (fld 1 x)
  let ls := decList decLevel (fld 3 x)
  let AsR := decList decExpr (fld 4 x)
  let fsR := decList decExpr (fld 5 x)
  let IR := decList decExpr (fld 6 x)
  ((∀ l ∈ ls, l.WF 0) ∧ ls.length = d.uvars ∧
    AsR.length = d.params.length ∧ fsR.length = c.fields.length ∧
    IR.length = T'.indices.length ∧ fsR.reverse[k]? = some j.e2 ∧
    j = ⟨j.Γ, .proj s k (.appN (.const c.name ls) (AsR.reverse ++ fsR.reverse)), j.e2,
      c.projType ls s k AsR.reverse (.appN (.const c.name ls) (AsR.reverse ++ fsR.reverse))⟩ ∧
    (decCert (fld 7 x)).j = ⟨j.Γ, .appN (.const c.name ls) (AsR.reverse ++ fsR.reverse),
      .appN (.const c.name ls) (AsR.reverse ++ fsR.reverse),
      .appN (.const s ls) (AsR.reverse ++ IR.reverse)⟩ ∧
    (decCert (fld 8 x)).j = ⟨j.Γ, j.A, j.A, .sort (f.level.inst ls)⟩ ∧
    (decCert (rest 9 x)).j = ⟨j.Γ, j.e2, j.e2, j.A⟩) ∧ d.ProjAllowed c ls k ∧
  certNum T R (fld 7 x) = 0 ∧ certNum T R (fld 8 x) = 0 ∧ certNum T R (rest 9 x) = 0

def iotaCondT (T : Tables) (R : Nat → Bool) (x : Nat) : Prop :=
  match ilookup T.inducts (decName (fld 1 x)) with
  | some (d, t) => match singleCtor d t with
    | some (T', c) => match c.fields[fld 2 x]? with
      | some f => iotaCond T R d T' c (fld 2 x) f x
      | none => False
    | none => False
  | none => False

open Classical in
theorem certNum_projIota {R : Nat → Bool} (hR : R 14 = true) {n : Nat} (h : n % 16 = 14) :
    certNum T R n = if iotaCondT T R (n / 16) then 0 else 1 := by
  rw [certNum, decCert_projIota h]
  refine ite_iff ?_ _ _
  simp only [Cert.usesOnly, Cert.check, Cert.tag, hR, Bool.true_and, iotaCondT, Tables.env]
  generalize ilookup T.inducts (decName (fld 1 (n / 16))) = o
  rcases o with _ | ⟨⟨d, t⟩⟩
  · simp
  simp only
  generalize singleCtor d t = o
  rcases o with _ | ⟨⟨T', c⟩⟩
  · simp
  simp only
  generalize c.fields[fld 2 (n / 16)]? = o
  rcases o with _ | f
  · simp
  simp only [iotaCond, Bool.and_eq_true, decide_eq_true_eq, projOK, childOK]
  exact ⟨fun ⟨⟨⟨u1, u2⟩, u3⟩, ⟨⟨⟨D, pa⟩, k1⟩, k2⟩, k3⟩ => ⟨D, pa, ⟨u1, k1⟩, ⟨u2, k2⟩, u3, k3⟩,
    fun ⟨D, pa, ⟨u1, k1⟩, ⟨u2, k2⟩, u3, k3⟩ => ⟨⟨⟨u1, u2⟩, u3⟩, ⟨⟨⟨D, pa⟩, k1⟩, k2⟩, k3⟩⟩

open Classical in
noncomputable def iotaEntryC (d : VInductDecl) (T' : VInductiveType) (c : VConstructor) (k : Nat)
    (f : VField) : PR :=
  let N := fldC 1 xC
  let LS := fldC 3 xC
  let AR := fldC 4 xC
  let FS := fldC 5 xC
  let IRc := fldC 6 xC
  let G := fldC 0 jC
  let X := appRP (appRP (constNC (numC (encName c.name)) LS) AR) FS
  let PT := substP (tmplE LS f.type) (projsP (numC k) N X AR) (num 0)
  andz (allAt LS) <| andz (eqz (lenAt LS) (numC d.uvars)) <|
  andz (eqz (lenE AR) (numC d.params.length)) <| andz (eqz (lenE FS) (numC c.fields.length)) <|
  andz (eqz (lenE IRc) (numC T'.indices.length)) <|
  andz (eqz (nthC FS (numC (c.fields.length - 1 - k))) (fldC 2 jC)) <|
  andz (eqz jC (judgC G (tagC 7 6 (cpair N (cpair (numC k) X))) (fldC 2 jC) PT)) <|
  andz (eqz (childJC (fldC 7 xC)) (judgC G X X (appRP (appRP (constNC N LS) AR) IRc))) <|
  andz (eqz (childJC (fldC 8 xC)) (judgC G (restC 3 jC) (restC 3 jC)
    (tagC 7 1 (tmplL LS f.level)))) <|
  andz (eqz (childJC (restC 9 xC)) (judgC G (fldC 2 jC) (fldC 2 jC) (restC 3 jC))) <|
  andz (paC LS d c k) <| andz (histAt (fldC 7 xC)) <| andz (histAt (fldC 8 xC)) (histAt (restC 9 xC))

/-- The rewriting that turns a projection rule's code conditions into its certificate conditions. -/
macro "proj_simp" : tactic => `(tactic| (simp only [eval_andz_zero, eqzJ]; simp only [eval_andz_zero, eval_allAt, eval_eqz, eval_lenAt,
  eval_lenE, eval_numC, eval_fldC, eval_restC, eval_xC, eval_jC, eval_childJC, eval_nthC, eqzJ,
  eval_appRP, eval_constNC, eval_projsP', eval_substP, eval_tmplE, eval_tmplL, eval_tagC, eval_cpair,
  eval_num, decExpr_enc, decLevel_enc, decName_enc, decList_enc decExpr_enc, decList_enc decLevel_enc,
  decExpr_const_num, decExpr_proj_num, decExpr_sort_num, decExpr_substNum, encName_dec, encExpr_dec,
  encList_dec encExpr_dec, encList_dec encLevel_dec, j_decJudg', decJudg_Γ, decJudg_e1, decJudg_e2,
  decJudg_A, VExpr.appN_append, List.reverse_reverse, List.append_nil]))

open Classical in
theorem eval_iotaEntryC {R : Nat → Bool} {ρ : Val} (h : ρ 0 % 16 = 14) (hv : HistOK T R ρ)
    (d : VInductDecl) (T' : VInductiveType) (c : VConstructor) (k : Nat) (f : VField)
    (hf : c.fields[k]? = some f) :
    (iotaEntryC d T' c k f).eval ρ = if iotaCond T R d T' c k f (ρ 0 / 16) then 0 else 1 := by
  unfold iotaEntryC
  refine eq_ite01 (andz_le _ _ _) ?_
  have hk : k < c.fields.length := (List.getElem?_eq_some_iff.1 hf).1
  generalize hx : ρ 0 / 16 = x
  have hxx : xC.eval ρ = x := by rw [eval_xC, hx]
  have hLS : (fldC 3 xC).eval ρ = encList encLevel (decList decLevel (fld 3 x)) := by
    rw [eval_fldC, hxx, encList_dec encLevel_dec]
  have k7 : (histAt (fldC 7 xC)).eval ρ = certNum T R (fld 7 x) := by
    rw [eval_histAt, eval_fldC, hxx, hv _ (hx ▸ fld_lt (by omega) 7)]
  have k8 : (histAt (fldC 8 xC)).eval ρ = certNum T R (fld 8 x) := by
    rw [eval_histAt, eval_fldC, hxx, hv _ (hx ▸ fld_lt (by omega) 8)]
  have k9 : (histAt (restC 9 xC)).eval ρ = certNum T R (rest 9 x) := by
    rw [eval_histAt, eval_restC, hxx, hv _ (hx ▸ rest_lt (by omega) 9)]
  have hn : ∀ L : Nat, (decList decExpr L).length = c.fields.length →
      ((decList decExpr L).reverse[k]? = some (decExpr (fld 2 (fld 0 x))) ↔
        nthN L (c.fields.length - 1 - k) = fld 2 (fld 0 x)) := fun L hL => by
    rw [getElem?_reverse_iff hL hk, encList_dec encExpr_dec, encExpr_dec]
  by_cases hw : ∀ l ∈ decList decLevel (fld 3 x), l.WF 0
  · rw [eval_andz_zero, eval_andz_zero, eval_andz_zero, eval_andz_zero, eval_andz_zero,
      eval_andz_zero, eval_andz_zero, eval_andz_zero, eval_andz_zero, eval_andz_zero,
      eval_andz_zero, eval_andz_zero, eval_andz_zero, eval_paC hLS hw, k7, k8, k9]
    simp only [iotaCond, projType_eq hf]
    proj_simp
    simp only [hx]
    constructor
    · rintro ⟨u1, u2, u3, u4, u5, u6, u7, u8, u9, u10, u11, u12, u13, u14⟩
      exact ⟨⟨u1, u2, u3, u4, u5, (hn _ u4).2 u6, u7, u8, u9, u10⟩, u11, u12, u13, u14⟩
    · rintro ⟨⟨u1, u2, u3, u4, u5, u6, u7, u8, u9, u10⟩, u11, u12, u13, u14⟩
      exact ⟨u1, u2, u3, u4, u5, (hn _ u4).1 u6, u7, u8, u9, u10, u11, u12, u13, u14⟩
  · rw [eval_andz_zero, eval_allAt, eval_fldC, hxx]
    exact ⟨fun ⟨u1, _⟩ => absurd u1 hw, fun ⟨⟨u1, _⟩, _⟩ => absurd u1 hw⟩

/-! ### `projDF` -/

theorem decCert_projDF {n : Nat} (h : n % 16 = 13) :
    decCert n = .projDF (decJudg (fld 0 (n / 16))) (decName (fld 1 (n / 16))) (fld 2 (n / 16))
      (decList decLevel (fld 3 (n / 16))) (decList decExpr (fld 4 (n / 16)))
      (decList decExpr (fld 5 (n / 16))) (decList decExpr (fld 6 (n / 16)))
      (decList decExpr (fld 7 (n / 16))) (decLevel (fld 8 (n / 16))) (decExpr (fld 9 (n / 16)))
      (decExpr (fld 10 (n / 16))) (decCert (fld 11 (n / 16))) (decCert (fld 12 (n / 16)))
      (decCert (rest 13 (n / 16))) := by
  rw [decCert]; simp [h]

def dfCond (T : Tables) (R : Nat → Bool) (d : VInductDecl) (T' : VInductiveType)
    (c : VConstructor) (k : Nat) (f : VField) (x : Nat) : Prop :=
  let j := decJudg (fld 0 x)
  let s := decName (fld 1 x)
  let ls := decList decLevel (fld 3 x)
  let AsR := decList decExpr (fld 4 x)
  let IR := decList decExpr (fld 5 x)
  let AsR' := decList decExpr (fld 6 x)
  let IR' := decList decExpr (fld 7 x)
  let u := decLevel (fld 8 x)
  let e := decExpr (fld 9 x)
  let e' := decExpr (fld 10 x)
  ((∀ l ∈ ls, l.WF 0) ∧ ls.length = d.uvars ∧
    AsR.length = d.params.length ∧ IR.length = T'.indices.length ∧
    AsR'.length = d.params.length ∧ IR'.length = T'.indices.length ∧
    j = ⟨j.Γ, .proj s k e, .proj s k e', c.projType ls s k AsR.reverse e⟩ ∧
    (decCert (fld 11 x)).j = ⟨j.Γ, .appN (.const s ls) (AsR.reverse ++ IR.reverse),
      .appN (.const s ls) (AsR'.reverse ++ IR'.reverse), .sort u⟩ ∧
    (decCert (fld 12 x)).j = ⟨j.Γ, e, e', .appN (.const s ls) (AsR.reverse ++ IR.reverse)⟩ ∧
    (decCert (rest 13 x)).j = ⟨j.Γ, c.projType ls s k AsR.reverse e,
      c.projType ls s k AsR'.reverse e', .sort (f.level.inst ls)⟩) ∧ d.ProjAllowed c ls k ∧
  certNum T R (fld 11 x) = 0 ∧ certNum T R (fld 12 x) = 0 ∧ certNum T R (rest 13 x) = 0

def dfCondT (T : Tables) (R : Nat → Bool) (x : Nat) : Prop :=
  match ilookup T.inducts (decName (fld 1 x)) with
  | some (d, t) => match singleCtor d t with
    | some (T', c) => match c.fields[fld 2 x]? with
      | some f => dfCond T R d T' c (fld 2 x) f x
      | none => False
    | none => False
  | none => False

open Classical in
theorem certNum_projDF {R : Nat → Bool} (hR : R 13 = true) {n : Nat} (h : n % 16 = 13) :
    certNum T R n = if dfCondT T R (n / 16) then 0 else 1 := by
  rw [certNum, decCert_projDF h]
  refine ite_iff ?_ _ _
  simp only [Cert.usesOnly, Cert.check, Cert.tag, hR, Bool.true_and, dfCondT, Tables.env]
  generalize ilookup T.inducts (decName (fld 1 (n / 16))) = o
  rcases o with _ | ⟨⟨d, t⟩⟩
  · simp
  simp only
  generalize singleCtor d t = o
  rcases o with _ | ⟨⟨T', c⟩⟩
  · simp
  simp only
  generalize c.fields[fld 2 (n / 16)]? = o
  rcases o with _ | f
  · simp
  simp only [dfCond, Bool.and_eq_true, decide_eq_true_eq, projOK, childOK]
  exact ⟨fun ⟨⟨⟨u1, u2⟩, u3⟩, ⟨⟨⟨D, pa⟩, k1⟩, k2⟩, k3⟩ => ⟨D, pa, ⟨u1, k1⟩, ⟨u2, k2⟩, u3, k3⟩,
    fun ⟨D, pa, ⟨u1, k1⟩, ⟨u2, k2⟩, u3, k3⟩ => ⟨⟨⟨u1, u2⟩, u3⟩, ⟨⟨⟨D, pa⟩, k1⟩, k2⟩, k3⟩⟩

open Classical in
noncomputable def dfEntryC (d : VInductDecl) (T' : VInductiveType) (c : VConstructor) (k : Nat)
    (f : VField) : PR :=
  let N := fldC 1 xC
  let LS := fldC 3 xC
  let AR := fldC 4 xC
  let IRc := fldC 5 xC
  let AR' := fldC 6 xC
  let IR' := fldC 7 xC
  let E := fldC 9 xC
  let E' := fldC 10 xC
  let G := fldC 0 jC
  let S := appRP (appRP (constNC N LS) AR) IRc
  let S' := appRP (appRP (constNC N LS) AR') IR'
  let PT := substP (tmplE LS f.type) (projsP (numC k) N E AR) (num 0)
  let PT' := substP (tmplE LS f.type) (projsP (numC k) N E' AR') (num 0)
  andz (allAt LS) <| andz (eqz (lenAt LS) (numC d.uvars)) <|
  andz (eqz (lenE AR) (numC d.params.length)) <| andz (eqz (lenE IRc) (numC T'.indices.length)) <|
  andz (eqz (lenE AR') (numC d.params.length)) <| andz (eqz (lenE IR') (numC T'.indices.length)) <|
  andz (eqz jC (judgC G (tagC 7 6 (cpair N (cpair (numC k) E)))
    (tagC 7 6 (cpair N (cpair (numC k) E'))) PT)) <|
  andz (eqz (childJC (fldC 11 xC)) (judgC G S S' (tagC 7 1 (fldC 8 xC)))) <|
  andz (eqz (childJC (fldC 12 xC)) (judgC G E E' S)) <|
  andz (eqz (childJC (restC 13 xC)) (judgC G PT PT' (tagC 7 1 (tmplL LS f.level)))) <|
  andz (paC LS d c k) <| andz (histAt (fldC 11 xC)) <| andz (histAt (fldC 12 xC))
    (histAt (restC 13 xC))

open Classical in
theorem eval_dfEntryC {R : Nat → Bool} {ρ : Val} (h : ρ 0 % 16 = 13) (hv : HistOK T R ρ)
    (d : VInductDecl) (T' : VInductiveType) (c : VConstructor) (k : Nat) (f : VField)
    (hf : c.fields[k]? = some f) :
    (dfEntryC d T' c k f).eval ρ = if dfCond T R d T' c k f (ρ 0 / 16) then 0 else 1 := by
  unfold dfEntryC
  refine eq_ite01 (andz_le _ _ _) ?_
  generalize hx : ρ 0 / 16 = x
  have hxx : xC.eval ρ = x := by rw [eval_xC, hx]
  have hLS : (fldC 3 xC).eval ρ = encList encLevel (decList decLevel (fld 3 x)) := by
    rw [eval_fldC, hxx, encList_dec encLevel_dec]
  have k11 : (histAt (fldC 11 xC)).eval ρ = certNum T R (fld 11 x) := by
    rw [eval_histAt, eval_fldC, hxx, hv _ (hx ▸ fld_lt (by omega) 11)]
  have k12 : (histAt (fldC 12 xC)).eval ρ = certNum T R (fld 12 x) := by
    rw [eval_histAt, eval_fldC, hxx, hv _ (hx ▸ fld_lt (by omega) 12)]
  have k13 : (histAt (restC 13 xC)).eval ρ = certNum T R (rest 13 x) := by
    rw [eval_histAt, eval_restC, hxx, hv _ (hx ▸ rest_lt (by omega) 13)]
  by_cases hw : ∀ l ∈ decList decLevel (fld 3 x), l.WF 0
  · rw [eval_andz_zero, eval_andz_zero, eval_andz_zero, eval_andz_zero, eval_andz_zero,
      eval_andz_zero, eval_andz_zero, eval_andz_zero, eval_andz_zero, eval_andz_zero,
      eval_andz_zero, eval_andz_zero, eval_andz_zero, eval_paC hLS hw, k11, k12, k13]
    simp only [dfCond, projType_eq hf]
    proj_simp
    simp only [hx]
    constructor
    · rintro ⟨u1, u2, u3, u4, u5, u6, u7, u8, u9, u10, u11, u12, u13, u14⟩
      exact ⟨⟨u1, u2, u3, u4, u5, u6, u7, u8, u9, u10⟩, u11, u12, u13, u14⟩
    · rintro ⟨⟨u1, u2, u3, u4, u5, u6, u7, u8, u9, u10⟩, u11, u12, u13, u14⟩
      exact ⟨u1, u2, u3, u4, u5, u6, u7, u8, u9, u10, u11, u12, u13, u14⟩
  · rw [eval_andz_zero, eval_allAt, eval_fldC, hxx]
    exact ⟨fun ⟨u1, _⟩ => absurd u1 hw, fun ⟨⟨u1, _⟩, _⟩ => absurd u1 hw⟩

/-! ### The rule codes -/

noncomputable def projEtaC (T : Tables) : PR := indTabC (ctorEnt etaEntryC) T.inducts

noncomputable def projIotaC (T : Tables) : PR :=
  indTabC (ctorEnt fun d T' c => fieldTab (iotaEntryC d T' c) c.fields 0) T.inducts

noncomputable def projDFC (T : Tables) : PR :=
  indTabC (ctorEnt fun d T' c => fieldTab (dfEntryC d T' c) c.fields 0) T.inducts

open Classical in
theorem projEtaC_spec {R : Nat → Bool} (hR : R 15 = true) {ρ : Val} (h : ρ 0 % 16 = 15)
    (hv : HistOK T R ρ) : (projEtaC T).eval ρ = certNum T R (ρ 0) := by
  rw [certNum_projEta hR h, projEtaC, eval_indTabC]
  rcases hl : ilookup T.inducts (decName (fld 1 (ρ 0 / 16))) with _ | ⟨⟨d, t⟩⟩
  · rw [if_neg (by simp [etaCondT, hl])]
  simp only [ctorEnt]
  rcases hs : singleCtor d t with _ | ⟨⟨T', c⟩⟩
  · rw [if_neg (by simp [etaCondT, hl, hs])]; rfl
  · exact (eval_etaEntryC h hv d T' c).trans (ite_iff (by simp only [etaCondT, hl, hs]) _ _)

open Classical in
theorem projIotaC_spec {R : Nat → Bool} (hR : R 14 = true) {ρ : Val} (h : ρ 0 % 16 = 14)
    (hv : HistOK T R ρ) : (projIotaC T).eval ρ = certNum T R (ρ 0) := by
  rw [certNum_projIota hR h, projIotaC, eval_indTabC]
  rcases hl : ilookup T.inducts (decName (fld 1 (ρ 0 / 16))) with _ | ⟨⟨d, t⟩⟩
  · rw [if_neg (by simp [iotaCondT, hl])]
  simp only [ctorEnt]
  rcases hs : singleCtor d t with _ | ⟨⟨T', c⟩⟩
  · rw [if_neg (by simp [iotaCondT, hl, hs])]; rfl
  simp only [eval_fieldTab0]
  rcases hf : c.fields[fld 2 (ρ 0 / 16)]? with _ | f
  · rw [if_neg (by simp [iotaCondT, hl, hs, hf])]
  · exact (eval_iotaEntryC h hv d T' c _ f hf).trans
      (ite_iff (by simp only [iotaCondT, hl, hs, hf]) _ _)

open Classical in
theorem projDFC_spec {R : Nat → Bool} (hR : R 13 = true) {ρ : Val} (h : ρ 0 % 16 = 13)
    (hv : HistOK T R ρ) : (projDFC T).eval ρ = certNum T R (ρ 0) := by
  rw [certNum_projDF hR h, projDFC, eval_indTabC]
  rcases hl : ilookup T.inducts (decName (fld 1 (ρ 0 / 16))) with _ | ⟨⟨d, t⟩⟩
  · rw [if_neg (by simp [dfCondT, hl])]
  simp only [ctorEnt]
  rcases hs : singleCtor d t with _ | ⟨⟨T', c⟩⟩
  · rw [if_neg (by simp [dfCondT, hl, hs])]; rfl
  simp only [eval_fieldTab0]
  rcases hf : c.fields[fld 2 (ρ 0 / 16)]? with _ | f
  · rw [if_neg (by simp [dfCondT, hl, hs, hf])]
  · exact (eval_dfEntryC h hv d T' c _ f hf).trans
      (ite_iff (by simp only [dfCondT, hl, hs, hf]) _ _)

end Lean4Lean.Incomplete
