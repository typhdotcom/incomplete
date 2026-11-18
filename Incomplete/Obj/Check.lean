import Incomplete.Obj.Fields

/-!
# The checker's step reads two variables

`bnd (certStep T R) ≤ 2` for all tables and rule sets: every rule's code is composed from
`PRLib`'s combinators over variables `0` and `1`, the table rules by induction over the tables
and the templates over their terms, and the projection rules are clamped. So course-of-values
recursion over the step unfolds at symbolic numbers (`Obj.Cov`).
-/

namespace Incomplete.Obj
open Lean4Lean
open PR

section
variable {a b c d L L' x : PR} {m : Nat}

@[obnd_le] theorem bnd_andz_le (ha : bnd a ≤ m) (hb : bnd b ≤ m) : bnd (andz a b) ≤ m := by
  unfold andz ifz; obnd
@[obnd_le] theorem bnd_notz_le (ha : bnd a ≤ m) : bnd (notz a) ≤ m := by unfold notz ifz; obnd
@[obnd_le] theorem bnd_judgC_le (ha : bnd a ≤ m) (hb : bnd b ≤ m) (hc : bnd c ≤ m) (hd : bnd d ≤ m) :
    bnd (judgC a b c d) ≤ m := by unfold judgC; obnd
@[obnd_le] theorem bnd_restC_le : ∀ (i : Nat) {a : PR}, bnd a ≤ m → bnd (restC i a) ≤ m
  | 0, _, h => h
  | i + 1, _, h => bnd_restC_le i (bnd_sndC_le h)
@[obnd_le] theorem bnd_fldC_le (i : Nat) (h : bnd a ≤ m) : bnd (fldC i a) ≤ m :=
  bnd_fstC_le (bnd_restC_le i h)
@[obnd_le] theorem bnd_histAt_le (h : bnd c ≤ m) (hm : 2 ≤ m) : bnd (histAt c) ≤ m := by
  unfold histAt; obnd
@[obnd_le] theorem bnd_childJC_le (h : bnd c ≤ m) : bnd (childJC c) ≤ m :=
  bnd_fldC_le 0 (bnd_divC_le h)
@[obnd_le] theorem bnd_xC (hm : 1 ≤ m) : bnd xC ≤ m := bnd_divC_le (bnd_var_le hm)
@[obnd_le] theorem bnd_jC (hm : 1 ≤ m) : bnd jC ≤ m := bnd_fldC_le 0 (bnd_xC hm)

end

theorem bnd_levStep : bnd levStep ≤ 2 := by unfold levStep mulP maxP addP; obnd
theorem bnd_lookStep : bnd lookStep ≤ 2 := by unfold lookStep; have := bnd_liftC; obnd
theorem bnd_lenStep : bnd lenStep ≤ 2 := by unfold lenStep; obnd
theorem bnd_instC : bnd instC ≤ 3 := by
  unfold instC; refine bnd_comp2_le (bnd_const_le bnd_covPC_instStep) ?_ ?_ <;> obnd

section
variable {a b c x : PR} {m : Nat}

@[obnd_le] theorem bnd_levAt_le (h : bnd a ≤ m) : bnd (levAt a) ≤ m := by
  unfold levAt levC; have := bnd_levStep; obnd
theorem bnd_allStep : bnd allStep ≤ 2 := by unfold allStep; obnd
theorem bnd_eqvStep : bnd eqvStep ≤ 2 := by unfold eqvStep; obnd
@[obnd_le] theorem bnd_lenAt_le (h : bnd a ≤ m) : bnd (lenAt a) ≤ m := by
  unfold lenAt; have := bnd_lenStep; obnd
@[obnd_le] theorem bnd_allAt_le (h : bnd a ≤ m) : bnd (allAt a) ≤ m := by
  unfold allAt; have := bnd_allStep; obnd
@[obnd_le] theorem bnd_eqvAt_le (h : bnd a ≤ m) (h' : bnd b ≤ m) : bnd (eqvAt a b) ≤ m := by
  unfold eqvAt; have := bnd_eqvStep; obnd
@[obnd_le] theorem bnd_lookC_le (hm : 2 ≤ m) : bnd lookC ≤ m := by
  unfold lookC; have := bnd_lookStep; obnd
@[obnd_le] theorem bnd_liftP_le (h1 : bnd a ≤ m) (h2 : bnd b ≤ m) (h3 : bnd c ≤ m) :
    bnd (liftP a b c) ≤ m := by unfold liftP; have := bnd_liftC; obnd
@[obnd_le] theorem bnd_instP_le (h1 : bnd a ≤ m) (h2 : bnd b ≤ m) (h3 : bnd c ≤ m) :
    bnd (instP a b c) ≤ m := by unfold instP; have := bnd_instC; obnd

@[obnd_le] theorem bnd_tmplL_le (h : bnd x ≤ m) : ∀ l : VLevel, bnd (tmplL x l) ≤ m
  | .zero => bnd_num_le _ _
  | .succ l => by have := bnd_tmplL_le h l; simp only [tmplL]; obnd
  | .max a b => by
    have := bnd_tmplL_le h a; have := bnd_tmplL_le h b; simp only [tmplL]; obnd
  | .imax a b => by
    have := bnd_tmplL_le h a; have := bnd_tmplL_le h b; simp only [tmplL]; obnd
  | .param i => by simp only [tmplL]; obnd

@[obnd_le] theorem bnd_tmplLs_le (h : bnd x ≤ m) : ∀ ls : List VLevel, bnd (tmplLs x ls) ≤ m
  | [] => bnd_num_le _ _
  | l :: ls => by
    have := bnd_tmplL_le h l; have := bnd_tmplLs_le h ls; simp only [tmplLs]; obnd

@[obnd_le] theorem bnd_tmplE_le (h : bnd x ≤ m) : ∀ e : VExpr, bnd (tmplE x e) ≤ m
  | .bvar _ => bnd_numC_le _ _
  | .sort u => by have := bnd_tmplL_le h u; simp only [tmplE]; obnd
  | .const _ us => by have := bnd_tmplLs_le h us; simp only [tmplE]; obnd
  | .app f a => by
    have := bnd_tmplE_le h f; have := bnd_tmplE_le h a; simp only [tmplE]; obnd
  | .lam f a => by
    have := bnd_tmplE_le h f; have := bnd_tmplE_le h a; simp only [tmplE]; obnd
  | .forallE f a => by
    have := bnd_tmplE_le h f; have := bnd_tmplE_le h a; simp only [tmplE]; obnd
  | .proj _ _ e => by have := bnd_tmplE_le h e; simp only [tmplE]; obnd

end

theorem bnd_constEntryC (ci : VConstant) : bnd (constEntryC ci) ≤ 2 := by
  unfold constEntryC constHdC; obnd

theorem bnd_constDFC : ∀ tbl : List (Name × VConstant), bnd (constDFC tbl) ≤ 2
  | [] => bnd_num_le _ _
  | (_, ci) :: r => by
    have := bnd_constEntryC ci; have := bnd_constDFC r; simp only [constDFC]; obnd

theorem bnd_extraEntryC (d : VDefEq) : bnd (extraEntryC d) ≤ 2 := by
  unfold extraEntryC; obnd

theorem bnd_extraC : ∀ rules : List VDefEq, bnd (extraC rules) ≤ 2
  | [] => bnd_num_le _ _
  | d :: r => by
    have := bnd_extraEntryC d; have := bnd_extraC r; simp only [extraC]; obnd

theorem bnd_clampC (c : PR) : bnd (clampC c) ≤ 2 :=
  bnd_ren_le c _ 2 fun i _ => by omega

theorem bnd_ruleC (T : Tables) (t : Nat) : bnd (ruleC T t) ≤ 2 := by
  match t with
  | 0 => unfold ruleC bvarC; obnd
  | 1 => unfold ruleC symmC; obnd
  | 2 => unfold ruleC transC; obnd
  | 3 => unfold ruleC sortDFC; obnd
  | 4 => exact bnd_constDFC _
  | 5 => unfold ruleC appDFC; have := bnd_instC; obnd
  | 6 => unfold ruleC lamDFC; obnd
  | 7 => unfold ruleC forallEDFC; obnd
  | 8 => unfold ruleC defeqDFC; obnd
  | 9 => unfold ruleC betaC; have := bnd_instC; obnd
  | 10 => unfold ruleC etaC; have := bnd_liftC; obnd
  | 11 => unfold ruleC proofIrrelC; obnd
  | 12 => exact bnd_extraC _
  | 13 => exact bnd_clampC _
  | 14 => exact bnd_clampC _
  | 15 => exact bnd_clampC _
  | _ + 16 => exact bnd_num_le _ _

theorem bnd_dispC (T : Tables) (R : Nat → Bool) : ∀ k t, bnd (dispC T R k t) ≤ 2
  | 0, _ => bnd_num_le _ _
  | k + 1, t => by
    have h1 : bnd (if R t then ruleC T t else num 1) ≤ 2 := by
      split
      · exact bnd_ruleC T t
      · exact bnd_num_le _ _
    have h2 := bnd_dispC T R k (t + 1)
    simp only [dispC]; obnd

/-- **The checker's step reads two variables.** -/
theorem bnd_certStep (T : Tables) (R : Nat → Bool) : bnd (certStep T R) ≤ 2 := bnd_dispC T R 16 0

theorem bnd_certC (T : Tables) (R : Nat → Bool) : bnd (certC T R) ≤ 1 := by
  have := bnd_certStep T R; unfold certC; obnd

theorem bnd_chkC (T : Tables) (R : Nat → Bool) : bnd (chkC T R) ≤ 2 := by
  have := bnd_certC T R; unfold chkC concC; obnd

end Incomplete.Obj
