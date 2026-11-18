import Incomplete.Obj.Graph

/-!
# Internal Σ₁-completeness

Every code has, at every arity, a code `τ` proving its graph internally (`ok_exists`): by
induction on the code, instantiating a closed graph lemma at the arguments and values and
chaining it with the certificates of the parts by modus ponens; for `prec`, by induction on the
recursion argument inside the theory.
-/

namespace Incomplete.Obj
open Lean4Lean
open VExpr Typing PR

/-- The certificate of a closed `∀ x₁ … xₘ, P` numbered `c`, instantiated at the codes `as`. -/
def instC (z s c : Nat) (as : List PR) : PR :=
  as.foldl (fun c a => mpP c (push a (numCertC z s))) (numC c)

theorem valF_succ_eq (f : PR) (n : Nat) :
    ((valF (.succ f) n).liftN 1 1).inst (S (.bvar 0)) 0 =
      (ev (.succ f) (args 1 n) =ₒ S (.bvar 0)) := by
  simp only [valF, obj_simp, args_map_liftN 1 n (k := 1) (by omega),
    args_map_inst 1 n (k := 0) _ (by omega)]

theorem valF_lift0 (f : PR) (n : Nat) :
    (valF f n).liftN 1 0 = (ev f (args 2 n) =ₒ .bvar 1) := by
  simp only [valF, obj_simp, args_map_liftN 1 n (k := 0) (by omega)]

theorem valF_lift1 (f : PR) (n : Nat) :
    (valF f n).liftN 1 1 = (ev f (args 2 n) =ₒ .bvar 0) := by
  simp only [valF, obj_simp, args_map_liftN 1 n (k := 1) (by omega)]

/-- Skipping variable `1`. -/
def skip1 : Nat → Nat
  | 0 => 0
  | i + 1 => i + 2

/-- The value of `prec g h` at the step's predecessor and other arguments. -/
def precR (g h : PR) : PR := ren Nat.succ (.prec g h)

/-- The certificate code of `prec g h` at `0`. -/
def precZ (z s c : Nat) (n : Nat) (g τg : PR) : PR := mpP (instC z s c (argC 0 n ++ [g])) τg

/-- The certificate code of `prec g h` at a successor, from the one at its predecessor. -/
def precS (z s c : Nat) (n : Nat) (g h τh : PR) : PR :=
  mpP (mpP (instC z s c (argC 2 n ++ [var 1, precR g h, .push (precR g h) (ren skip1 h)])) (var 0))
    (.push (precR g h) (ren skip1 τh))

theorem valS_skip1 (a b : VExpr) (l : List VExpr) (i : Nat) :
    valS (a :: b :: l) (skip1 i) = valS (a :: l) i := by
  cases i <;> simp [skip1, valS]

theorem valS_succ (a : VExpr) (l : List VExpr) (i : Nat) :
    valS (a :: l) (Nat.succ i) = valS l i := by
  simp [valS]

theorem tmplH_zero (hs : List VExpr) : tmplH hs zero 0 = numT (encExpr zero) := rfl

theorem valF_prec0_eq (g h : PR) (n : Nat) :
    (valF (.prec g h) (n + 1)).inst zero 1 = (ev (.prec g h) (zero :: args 1 n) =ₒ .bvar 0) := by
  simp only [valF, args, obj_simp, args_map_inst 1 n (k := 1) _ (Nat.le_refl 1)]

theorem valF_precS_eq (g h : PR) (n : Nat) :
    (((valF (.prec g h) (n + 1)).liftN 1 2).inst (S (.bvar 0)) 1).liftN 1 1 =
      (ev (.prec g h) (S (.bvar 2) :: args 3 n) =ₒ .bvar 0) := by
  simp only [valF, args, obj_simp, args_map_liftN 2 n (k := 2) (Nat.le_refl 2),
    args_map_inst 2 n (k := 1) _ (by omega), args_map_liftN 2 n (k := 1) (by omega)]

theorem getD_map_litT {xs : List VExpr} {i : Nat} (h : i < xs.length) :
    (xs.map litT).getD i zero = litT (xs.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h,
    Option.map_some, Option.getD_some]

section
variable {env : Typing} [E : ObjEnv env] {Γ : List VExpr} {T : Tables}

/-- A closed theorem has a certificate proving it, internally. -/
theorem closed_prf (hT : TablesFor env.env T) {P : VExpr} (h : Thm env [] P) :
    ∃ c : Nat, ∀ {Γ : List VExpr}, Thm env Γ (prfT T (tmplH [] P 0) (numT c) =ₒ zero) := by
  obtain ⟨e, c, hc⟩ := provable_cert hT h.toFull
  refine ⟨c, fun {Γ} => ?_⟩
  have h1 := prfT_of_cert (T := T) (s := numT (encExpr P)) (e := numT (encExpr e)) (by otype)
    (by otype) (by otype) (hc (env := env) (Γ := Γ)).1 (hc (env := env) (Γ := Γ)).2
  exact prf_congr (by otype) (by otype) (by otype)
    (Thm.symm (by otype) (by otype) (tmplH_nil P 0)) h1

/-! ### Graph lemmas, pointwise -/

theorem gp_succ {f : PR} {xs : List VExpr} {v : VExpr} (hx : Tms env Γ xs) (hv : Tm env Γ v) :
    Thm env Γ (imp (ev f xs =ₒ v) (ev (.succ f) xs =ₒ S v)) := by
  ointro h
  orw [h]

theorem gp_push {h g : PR} {xs : List VExpr} {y z : VExpr} (hx : Tms env Γ xs) (hy : Tm env Γ y)
    (hz : Tm env Γ z) :
    Thm env Γ (imp (ev h xs =ₒ y) (imp (ev g (y :: xs) =ₒ z) (ev (.push h g) xs =ₒ z))) := by
  ointro h1
  ointro h2
  olift h1
  orw [ev_push (f := .push h g) rfl (by otype), h1]
  exact h2

theorem gp_prec0 {g h : PR} {xs : List VExpr} {v : VExpr} (hx : Tms env Γ xs) (hv : Tm env Γ v) :
    Thm env Γ (imp (ev g xs =ₒ v) (ev (.prec g h) (zero :: xs) =ₒ v)) := by
  ointro h1
  orw [ev_prec_zero (f := .prec g h) rfl (by otype)]
  exact h1

theorem gp_precS {g h : PR} {xs : List VExpr} {t r r' : VExpr} (hx : Tms env Γ xs)
    (ht : Tm env Γ t) (hr : Tm env Γ r) (hr' : Tm env Γ r') :
    Thm env Γ (imp (ev (.prec g h) (t :: xs) =ₒ r)
      (imp (ev h (r :: t :: xs) =ₒ r') (ev (.prec g h) (S t :: xs) =ₒ r'))) := by
  ointro h1
  ointro h2
  olift h1
  orw [ev_prec_succ (f := .prec g h) rfl (by otype) (by otype), h1]
  exact h2

theorem ev_ren_eq {f : PR} {l l' : List VExpr} (ρ : Nat → Nat) (hl : Tms env Γ l)
    (h : ∀ i, valS l (ρ i) = valS l' i) : Thm env Γ (ev (ren ρ f) l =ₒ ev f l') := by
  have e := ev_ren_df hl ρ f
  have : (fun i => valS l (ρ i)) = valS l' := funext h
  rw [this] at e
  exact .ofDefEq e

theorem ev_nil_eq (f : PR) : ev f [] = ev f [zero] := by
  unfold ev; congr 1; funext i; cases i <;> rfl

theorem litT_congr {a b : VExpr} (ha : Tm env Γ a) (hb : Tm env Γ b) (h : Thm env Γ (a =ₒ b)) :
    Thm env Γ (litT a =ₒ litT b) := by
  orw [h]

theorem ev_precS {Γ L : List VExpr} {z s c n : Nat} {g h τh : PR} (hL : Tms env Γ L) :
    Thm env Γ (ev (precS z s c n g h τh) L =ₒ mpX (mpX (ev (instC z s c (argC 2 n ++
      [var 1, precR g h, .push (precR g h) (ren skip1 h)])) L) (L.getD 0 zero))
      (ev (.push (precR g h) (ren skip1 τh)) L)) := by
  have : Tm env Γ (L.getD 0 zero) := hL.get 0
  unfold precS
  orw [ev_mpP hL, ev_mpP hL]

theorem EqN_closed {a b : VExpr} (ha : Tm env [] a) (hb : Tm env [] b) : (a =ₒ b).ClosedN :=
  (EqNTy ha hb).closedN.1

variable {z s : Nat}
  (hz : Thm env [] (certT T (fun _ => true) (numT z) =ₒ zero))
  (jz : Thm env [] (jT (numT z) =ₒ
    judgT zero (numT (encExpr Incomplete.zero)) (numT (encExpr Incomplete.zero)) (numT (encExpr nat))))
  (hs : Thm env [] (certT T (fun _ => true) (numT s) =ₒ zero))
  (js : Thm env [] (jT (numT s) =ₒ
    judgT zero (numT (encExpr succ)) (numT (encExpr succ)) (numT (encExpr (.forallE nat nat)))))
include hz jz hs js

/-- A closed `∀ x₁ … xₘ, P` instantiated at the values of codes. -/
theorem prf_instC {Γ l : List VExpr} {c : Nat} {P : VExpr} (as : List PR) (hl : Tms env Γ l)
    (hc : Thm env Γ (prfT T (tmplH [] (allN as.length P) 0) (numT c) =ₒ zero)) :
    Thm env Γ (prfT T (tmplH ((as.map (ev · l)).reverse.map litT) P 0) (ev (instC z s c as) l)
      =ₒ zero) := by
  have := prf_instL hz jz hs js as (ys := []) (c := numC c) hl .nil (by rw [ev_numC_ctx]; exact hc)
  unfold instC
  simpa only [List.append_nil] using this

variable (hT : TablesFor env.env T)
include hT

omit hz jz hs js in
/-- A code that is `0` at arity `n`. -/
theorem ok_zeroLike {f : PR} {n : Nat} (hf : ∀ xs : List VExpr, xs.length = n → ev f xs = zero)
    (hA : valF f n = (zero =ₒ .bvar 0)) : ∃ τ, Ok env T f n τ := by
  obtain ⟨c, hc⟩ := closed_prf hT (P := zero =ₒ zero) (Thm.refl zeroTy)
  refine ⟨numC c, fun {Γ xs} hxs hlen => ?_⟩
  unfold okF
  rw [hf xs hlen, hA, ev_numC_ctx]
  have h1 : Thm env Γ (prfT T (tmplH [] (zero =ₒ zero) 0) (numT c) =ₒ zero) := hc
  rw [← tmplH_closed (xs.map litT) _ 0 (EqN_closed (env := env) zeroTy zeroTy)] at h1
  have e1 := tmplH_inst_insert [] (xs.map litT) (e := zero) trivial (zero =ₒ .bvar 0) 0
  simp only [obj_simp, List.nil_append, List.length_nil, Nat.add_zero] at e1
  rw [e1] at h1
  refine prf_congr (by otype) (by otype) (by otype) ?_ h1
  exact tmplH_congr1 (hs₁ := []) .nil hxs.map_litT (by otype) (by otype)
    (Thm.symm (by otype) (by otype) litT_zero) _ _

/-- A variable inside the arguments. -/
theorem ok_var {i n : Nat} (hi : i < n) : ∃ τ, Ok env T (var i) n τ := by
  obtain ⟨c, hc⟩ := closed_prf hT (P := allN n (.bvar i =ₒ .bvar i))
    (allN_intro n (Γ := []) (Thm.refl (bvar_rep hi)))
  refine ⟨instC z s c (argC 0 n), fun {Γ xs} hxs hlen => ?_⟩
  have h1 := prf_instC hz jz hs js (argC 0 n) hxs (by rw [length_argC]; exact hc)
  rw [argC_ev 0 n xs (by omega), List.drop_zero] at h1
  have e1 : (VExpr.bvar (1 + i) =ₒ .bvar 0).inst (.bvar i) 0 = (.bvar i =ₒ .bvar i) := by
    simp only [EqN_inst, VExpr.inst, instVar, if_neg (show ¬ 1 + i < 0 by omega),
      if_neg (show ¬ 1 + i = 0 by omega), Nat.lt_irrefl, if_false, if_true,
      show 1 + i - 1 = i by omega, liftN_zero]
  have e2 := tmplH_inst_insert [] (xs.map litT) (e := .bvar i)
    (show i < (xs.map litT).length by simp [hlen, hi]) (.bvar (1 + i) =ₒ .bvar 0) 0
  simp only [List.nil_append, List.length_nil, Nat.add_zero, e1] at e2
  rw [e2] at h1
  have e3 : tmplH (xs.map litT) (.bvar i) 0 = litT (xs.getD i zero) := by
    simp only [tmplH, Nat.not_lt_zero, if_false, Nat.sub_zero, List.length_map,
      if_pos (show i < xs.length by omega), getD_map_litT (show i < xs.length by omega)]
  rw [e3] at h1
  unfold okF valF
  simp only [ev_var, args_getD, if_pos hi, List.map_cons]
  exact h1

theorem ok_succ {f τf : PR} {n : Nat} (hf : Ok env T f n τf) : ∃ τ, Ok env T (.succ f) n τ := by
  obtain ⟨c, hc⟩ := closed_prf hT (P := allN (n + 1) (imp (valF f n) (ev (.succ f) (args 1 n) =ₒ
    S (.bvar 0)))) (allN_intro (env := env) (n + 1) (Γ := [])
      (gp_succ (argsTy (by omega)) (bvar_rep (by omega))))
  refine ⟨mpP (instC z s c (argC 0 n ++ [f])) τf, fun {Γ xs} hxs hlen => ?_⟩
  have h1 := prf_instC hz jz hs js (argC 0 n ++ [f]) hxs
    (by rw [List.length_append, length_argC]; exact hc)
  have e0 : ((argC 0 n ++ [f]).map (ev · xs)).reverse = ev f xs :: xs := by
    simp only [List.map_append, List.reverse_append, List.map_cons, List.map_nil,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append,
      argC_ev 0 n xs (by omega), List.drop_zero]
  rw [e0] at h1
  have h2 := prf_mpH (Γ := Γ) (.cons (evTy hxs) hxs) (by otype) (by otype) h1 (hf hxs hlen)
  have h3 := prf_congr_c (by otype) (by otype) (by otype)
    (Thm.symm (by otype) (by otype) (ev_mpP hxs)) h2
  rw [← valF_succ_eq] at h3
  have e2 := tmplH_inst_insert [] ((ev f xs :: xs).map litT) (e := S (.bvar 0))
    (show (S (.bvar 0)).ClosedN _ from ⟨trivial, Nat.succ_pos _⟩) ((valF (.succ f) n).liftN 1 1) 0
  simp only [List.nil_append, List.length_nil, Nat.add_zero] at e2
  rw [e2] at h3
  simp only [List.map_cons] at h3
  have e3 := tmplH_liftN_erase [tmplH (litT (ev f xs) :: xs.map litT) (S (.bvar 0)) 0]
    (xs.map litT) (litT (ev f xs)) (valF (.succ f) n) 0
  simp only [List.length_singleton, Nat.zero_add, List.singleton_append] at e3
  rw [e3] at h3
  have ew : tmplH (litT (ev f xs) :: xs.map litT) (S (.bvar 0)) 0 =
      tagT 7 3 (pair (numT (encExpr succ)) (litT (ev f xs))) := by
    simp only [S, tmplH, List.length_cons, Nat.lt_irrefl, if_false, Nat.sub_self,
      Nat.zero_lt_succ, if_true, List.getD_cons_zero]
    rfl
  rw [ew] at h3
  unfold okF
  refine prf_congr (by otype) (by otype) (by otype) ?_ h3
  exact tmplH_congr1 (hs₁ := []) .nil hxs.map_litT (by otype) (by otype)
    (Thm.symm (by otype) (by otype) (litT_succ (evTy hxs))) _ _

theorem ok_push {h g τh τg : PR} {n : Nat} (hh : Ok env T h n τh) (hg : Ok env T g (n + 1) τg) :
    ∃ τ, Ok env T (.push h g) n τ := by
  obtain ⟨c, hc⟩ := closed_prf hT (P := allN (n + 2) (imp (ev h (args 2 n) =ₒ .bvar 1)
      (imp (valF g (n + 1)) (ev (.push h g) (args 2 n) =ₒ .bvar 0))))
    (allN_intro (env := env) (n + 2) (Γ := [])
      (gp_push (argsTy (by omega)) (bvar_rep (by omega)) (bvar_rep (by omega))))
  refine ⟨mpP (mpP (instC z s c (argC 0 n ++ [h, .push h g])) τh) (.push h τg),
    fun {Γ xs} hxs hlen => ?_⟩
  have h1 := prf_instC hz jz hs js (argC 0 n ++ [h, .push h g]) hxs
    (by rw [List.length_append, length_argC]; exact hc)
  have e0 : ((argC 0 n ++ [h, .push h g]).map (ev · xs)).reverse =
      ev (.push h g) xs :: ev h xs :: xs := by
    simp only [List.map_append, List.reverse_append, List.map_cons, List.map_nil,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
      argC_ev 0 n xs (by omega), List.drop_zero]
  rw [e0] at h1
  simp only [List.map_cons] at h1
  have hy : Tm env Γ (ev h xs) := evTy hxs
  have hz' : Tm env Γ (ev g (ev h xs :: xs)) := evTy (.cons hy hxs)
  have h1 := prf_congr (by otype) (by otype) (by otype)
    (tmplH_congr1 (hs₁ := []) .nil (.cons (by otype) hxs.map_litT) (by otype) (by otype)
      (litT_congr (by otype) hz' (ev_push (f := .push h g) rfl hxs)) _ 0) h1
  have p1 := hh hxs hlen
  unfold okF at p1
  have e1 := tmplH_liftN_erase [] ((ev h xs :: xs).map litT) (litT (ev g (ev h xs :: xs)))
    (valF h n) 0
  simp only [List.nil_append, List.length_nil, Nat.add_zero, valF_lift0, List.map_cons] at e1
  simp only [List.map_cons] at p1
  rw [← e1] at p1
  have h2 := prf_mpH (ys := ev g (ev h xs :: xs) :: ev h xs :: xs) (.cons hz' (.cons hy hxs))
    (by otype) (by otype) h1 p1
  have p2 := hg (.cons hy hxs) (by simp [hlen])
  unfold okF at p2
  have h3 := prf_mpH (ys := ev g (ev h xs :: xs) :: ev h xs :: xs) (.cons hz' (.cons hy hxs))
    (by otype) (by otype) h2 p2
  rw [← valF_lift1] at h3
  have e3 := tmplH_liftN_erase [litT (ev g (ev h xs :: xs))] (xs.map litT) (litT (ev h xs))
    (valF (.push h g) n) 0
  simp only [List.length_singleton, Nat.zero_add, List.singleton_append] at e3
  simp only [List.map_cons] at h3
  rw [e3] at h3
  have h4 := prf_congr (by otype) (by otype) (by otype)
    (tmplH_congr1 (hs₁ := []) .nil hxs.map_litT (by otype) (by otype)
      (litT_congr hz' (by otype)
        (Thm.symm (by otype) hz' (ev_push (f := .push h g) rfl hxs))) _ 0) h3
  unfold okF
  simp only [List.map_cons]
  refine prf_congr_c (by otype) (by otype) (by otype) ?_ h4
  orw [ev_mpP hxs, ev_mpP hxs, ev_push (f := .push h τg) rfl hxs]

omit hT in
/-- The step of `prec g h`: from a proof `cp` of its graph at `t`, `precS` proves it at `S t`. -/
theorem prec_step {g h τh : PR} {n cₛ : Nat} (hh : Ok env T h (n + 2) τh)
    (hcₛ : ∀ {Γ : List VExpr}, Thm env Γ (prfT T (tmplH [] (allN (n + 3)
      (imp (ev (.prec g h) (args 2 (n + 1)) =ₒ .bvar 1)
        (imp (valF h (n + 2)) (ev (.prec g h) (S (.bvar 2) :: args 3 n) =ₒ .bvar 0)))) 0)
      (numT cₛ) =ₒ zero))
    {cp t : VExpr} {xs : List VExpr} (hcp : Tm env Γ cp) (ht : Tm env Γ t) (hxs : Tms env Γ xs)
    (hlen : xs.length = n)
    (ih : Thm env Γ (prfT T (tmplH (litT (ev (.prec g h) (t :: xs)) :: litT t :: xs.map litT)
      (valF (.prec g h) (n + 1)) 0) cp =ₒ zero)) :
    Thm env Γ (prfT T (tmplH (litT (ev (.prec g h) (S t :: xs)) :: litT (S t) :: xs.map litT)
      (valF (.prec g h) (n + 1)) 0) (ev (precS z s cₛ n g h τh) (cp :: t :: xs)) =ₒ zero) := by
  have hr : Tm env Γ (ev (.prec g h) (t :: xs)) := evTy (.cons ht hxs)
  have hr' : Tm env Γ (ev h (ev (.prec g h) (t :: xs) :: t :: xs)) :=
    evTy (.cons hr (.cons ht hxs))
  have hL : Tms env Γ (cp :: t :: xs) := .cons hcp (.cons ht hxs)
  -- the step lemma at `[r', r, t, xs]`, with `r` and `r'` the values of `prec g h` and `h`
  have h1 := prf_instC hz jz hs js (argC 2 n ++ [var 1, precR g h,
      .push (precR g h) (ren skip1 h)]) hL
    (by rw [List.length_append, length_argC]; exact hcₛ)
  have e0 : ((argC 2 n ++ [var 1, precR g h, .push (precR g h) (ren skip1 h)]).map
      (ev · (cp :: t :: xs))).reverse = ev (.push (precR g h) (ren skip1 h)) (cp :: t :: xs) ::
      ev (precR g h) (cp :: t :: xs) :: t :: xs := by
    simp only [List.map_append, List.reverse_append, List.map_cons, List.map_nil,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
      argC_ev 2 n _ (show (cp :: t :: xs).length = 2 + n by simp only [List.length_cons]; omega),
      List.drop_succ_cons, List.drop_zero, ev_var, List.getD_cons_succ, List.getD_cons_zero]
  rw [e0] at h1
  simp only [List.map_cons] at h1
  have hRL : Tm env Γ (ev (precR g h) (cp :: t :: xs)) := evTy hL
  have eR : Thm env Γ (ev (precR g h) (cp :: t :: xs) =ₒ ev (.prec g h) (t :: xs)) :=
    ev_ren_eq Nat.succ hL (valS_succ _ _)
  have eRh : Thm env Γ (ev (.push (precR g h) (ren skip1 h)) (cp :: t :: xs) =ₒ
      ev h (ev (.prec g h) (t :: xs) :: t :: xs)) := by
    orw [ev_push (f := .push (precR g h) (ren skip1 h)) rfl hL,
      ev_ren_eq (f := h) skip1 (.cons hRL hL) (l' := ev (precR g h) (cp :: t :: xs) :: t :: xs)
        (valS_skip1 _ _ _), eR]
  generalize hP : (imp (ev (.prec g h) (args 2 (n + 1)) =ₒ .bvar 1)
    (imp (valF h (n + 2)) (ev (.prec g h) (S (.bvar 2) :: args 3 n) =ₒ .bvar 0))) = P at h1
  have E1 : Thm env Γ (tmplH (litT (ev (.push (precR g h) (ren skip1 h)) (cp :: t :: xs)) ::
      litT (ev (precR g h) (cp :: t :: xs)) :: litT t :: xs.map litT) P 0 =ₒ
      tmplH (litT (ev h (ev (.prec g h) (t :: xs) :: t :: xs)) ::
        litT (ev (precR g h) (cp :: t :: xs)) :: litT t :: xs.map litT) P 0) :=
    tmplH_congr1 (hs₁ := []) .nil (.cons (by otype) (.cons (by otype) hxs.map_litT))
      (by otype) (by otype) (litT_congr (by otype) hr' eRh) _ 0
  have E2 : Thm env Γ (tmplH (litT (ev h (ev (.prec g h) (t :: xs) :: t :: xs)) ::
      litT (ev (precR g h) (cp :: t :: xs)) :: litT t :: xs.map litT) P 0 =ₒ
      tmplH (litT (ev h (ev (.prec g h) (t :: xs) :: t :: xs)) ::
        litT (ev (.prec g h) (t :: xs)) :: litT t :: xs.map litT) P 0) :=
    tmplH_congr1 (hs₁ := [litT (ev h (ev (.prec g h) (t :: xs) :: t :: xs))])
      (.cons (by otype) .nil) (.cons (by otype) hxs.map_litT) (by otype) (by otype)
      (litT_congr hRL hr eR) _ 0
  have h1 := prf_congr (by otype) (by otype) (by otype) E2
    (prf_congr (by otype) (by otype) (by otype) E1 h1)
  subst hP
  generalize hr'e : ev h (ev (.prec g h) (t :: xs) :: t :: xs) = r' at h1 hr'
  generalize hre : ev (.prec g h) (t :: xs) = r at h1 hr ih hr'e
  -- modus ponens with the proof at `t`, then with `h`'s at `[r, t, xs]`
  have e5 : tmplH (litT r' :: litT r :: litT t :: xs.map litT)
      (ev (.prec g h) (args 2 (n + 1)) =ₒ .bvar 1) 0 =
      tmplH (litT r :: litT t :: xs.map litT) (valF (.prec g h) (n + 1)) 0 := by
    rw [← valF_lift0]
    exact tmplH_liftN_erase [] _ _ _ 0
  rw [← e5] at ih
  have h2 := prf_mpH (ys := r' :: r :: t :: xs) (.cons hr' (.cons hr (.cons ht hxs)))
    (by otype) (by otype) h1 ih
  have p2 := hh (.cons hr (.cons ht hxs)) (by simp only [List.length_cons]; omega)
  unfold okF at p2
  simp only [List.map_cons] at p2
  rw [hr'e] at p2
  have h3 := prf_mpH (ys := r' :: r :: t :: xs) (.cons hr' (.cons hr (.cons ht hxs)))
    (by otype) (by otype) h2 p2
  simp only [List.map_cons] at h3
  -- the conclusion at `S t`
  have e6 : tmplH (litT r' :: litT r :: litT t :: xs.map litT)
      (ev (.prec g h) (S (.bvar 2) :: args 3 n) =ₒ .bvar 0) 0 =
      tmplH (litT r' :: tmplH (litT t :: xs.map litT) (S (.bvar 0)) 0 :: xs.map litT)
        (valF (.prec g h) (n + 1)) 0 := by
    rw [← valF_precS_eq]
    rw [show ∀ B, tmplH (litT r' :: litT r :: litT t :: xs.map litT) (B.liftN 1 1) 0 =
      tmplH (litT r' :: litT t :: xs.map litT) B 0 from
        fun B => tmplH_liftN_erase [litT r'] _ _ B 0]
    rw [show tmplH (litT r' :: litT t :: xs.map litT)
        (((valF (.prec g h) (n + 1)).liftN 1 2).inst (S (.bvar 0)) 1) 0 =
      tmplH (litT r' :: tmplH (litT t :: xs.map litT) (S (.bvar 0)) 0 :: litT t ::
        xs.map litT) ((valF (.prec g h) (n + 1)).liftN 1 2) 0 from
        tmplH_inst_insert [litT r'] (litT t :: xs.map litT) (e := S (.bvar 0))
          ⟨trivial, Nat.succ_pos _⟩ _ 0]
    exact tmplH_liftN_erase [litT r', _] _ _ _ 0
  rw [e6] at h3
  have ew : tmplH (litT t :: xs.map litT) (S (.bvar 0)) 0 =
      tagT 7 3 (pair (numT (encExpr succ)) (litT t)) := by
    simp only [S, tmplH, List.length_cons, Nat.lt_irrefl, if_false, Nat.sub_self,
      Nat.zero_lt_succ, if_true, List.getD_cons_zero]
    rfl
  rw [ew] at h3
  have E8 : Thm env Γ (tmplH (litT r' :: tagT 7 3 (pair (numT (encExpr succ)) (litT t)) ::
      xs.map litT) (valF (.prec g h) (n + 1)) 0 =ₒ
      tmplH (litT r' :: litT (S t) :: xs.map litT) (valF (.prec g h) (n + 1)) 0) :=
    tmplH_congr1 (hs₁ := [litT r']) (.cons (by otype) .nil) hxs.map_litT (by otype)
      (by otype) (Thm.symm (by otype) (by otype) (litT_succ ht)) _ 0
  have hS : Tm env Γ (ev (.prec g h) (S t :: xs)) := evTy (.cons (STy ht) hxs)
  have eS : Thm env Γ (ev (.prec g h) (S t :: xs) =ₒ r') := by
    rw [← hr'e, ← hre]; exact ev_prec_succ (f := .prec g h) rfl hxs ht
  have E9 : Thm env Γ (tmplH (litT r' :: litT (S t) :: xs.map litT) (valF (.prec g h) (n + 1)) 0 =ₒ
      tmplH (litT (ev (.prec g h) (S t :: xs)) :: litT (S t) :: xs.map litT)
        (valF (.prec g h) (n + 1)) 0) :=
    tmplH_congr1 (hs₁ := []) .nil (.cons (by otype) hxs.map_litT) (by otype) (by otype)
      (litT_congr hr' hS (Thm.symm hS hr' eS)) _ 0
  have h4 := prf_congr (by otype) (by otype) (by otype) E9
    (prf_congr (by otype) (by otype) (by otype) E8 h3)
  refine prf_congr_c (by otype) (by otype) (by otype) ?_ h4
  rw [← hre]
  orw [ev_precS hL, ev_push (f := .push (precR g h) (ren skip1 τh)) rfl hL,
    ev_ren_eq (f := τh) skip1 (.cons hRL hL) (l' := ev (precR g h) (cp :: t :: xs) :: t :: xs)
      (valS_skip1 _ _ _), eR]

theorem ok_prec {g h τg τh : PR} {n : Nat} (hg : Ok env T g n τg) (hh : Ok env T h (n + 2) τh) :
    ∃ τ, Ok env T (.prec g h) (n + 1) τ := by
  obtain ⟨c₀, hc₀⟩ := closed_prf hT (P := allN (n + 1) (imp (valF g n)
      (ev (.prec g h) (zero :: args 1 n) =ₒ .bvar 0)))
    (allN_intro (env := env) (n + 1) (Γ := []) (gp_prec0 (argsTy (by omega)) (bvar_rep (by omega))))
  obtain ⟨cₛ, hcₛ⟩ := closed_prf hT (P := allN (n + 3)
      (imp (ev (.prec g h) (args 2 (n + 1)) =ₒ .bvar 1)
        (imp (valF h (n + 2)) (ev (.prec g h) (S (.bvar 2) :: args 3 n) =ₒ .bvar 0))))
    (allN_intro (env := env) (n + 3) (Γ := []) (gp_precS (argsTy (by omega)) (bvar_rep (by omega))
      (bvar_rep (by omega)) (bvar_rep (by omega))))
  refine ⟨.prec (precZ z s c₀ n g τg) (precS z s cₛ n g h τh), okF_ind ?_ ?_⟩
  · intro Γ xs hxs hlen
    have h1 := prf_instC hz jz hs js (argC 0 n ++ [g]) hxs
      (by rw [List.length_append, length_argC]; exact hc₀)
    have e0 : ((argC 0 n ++ [g]).map (ev · xs)).reverse = ev g xs :: xs := by
      simp only [List.map_append, List.reverse_append, List.map_cons, List.map_nil,
        List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append,
        argC_ev 0 n xs (by omega), List.drop_zero]
    rw [e0] at h1
    have p := hg hxs hlen
    unfold okF at p
    have h2 := prf_mpH (ys := ev g xs :: xs) (.cons (evTy hxs) hxs) (by otype) (by otype) h1 p
    rw [← valF_prec0_eq] at h2
    have e1 := tmplH_inst_insert [litT (ev g xs)] (xs.map litT) (e := zero) trivial
      (valF (.prec g h) (n + 1)) 0
    simp only [List.singleton_append, List.length_singleton, Nat.zero_add] at e1
    simp only [List.map_cons] at h2
    rw [e1] at h2
    have ez : tmplH (xs.map litT) zero 0 = numT (encExpr zero) := rfl
    rw [ez] at h2
    have e3 : Thm env Γ (tmplH (litT (ev g xs) :: numT (encExpr zero) :: xs.map litT)
        (valF (.prec g h) (n + 1)) 0 =ₒ tmplH (litT (ev g xs) :: litT zero :: xs.map litT)
        (valF (.prec g h) (n + 1)) 0) :=
      tmplH_congr1 (hs₁ := [litT (ev g xs)]) (.cons (by otype) .nil) hxs.map_litT (by otype)
        (by otype) (Thm.symm (by otype) (by otype) litT_zero) _ 0
    have h3 := prf_congr (by otype) (by otype) (by otype) e3 h2
    have e4 : Thm env Γ (tmplH (litT (ev g xs) :: litT zero :: xs.map litT)
        (valF (.prec g h) (n + 1)) 0 =ₒ tmplH (litT (ev (.prec g h) (zero :: xs)) :: litT zero ::
          xs.map litT) (valF (.prec g h) (n + 1)) 0) :=
      tmplH_congr1 (hs₁ := []) .nil (.cons (by otype) hxs.map_litT) (by otype) (by otype)
        (litT_congr (by otype) (by otype) (Thm.symm (by otype) (by otype)
          (ev_prec_zero (f := .prec g h) rfl hxs))) _ 0
    have h4 := prf_congr (by otype) (by otype) (by otype) e4 h3
    unfold okF
    simp only [List.map_cons]
    refine prf_congr_c (by otype) (by otype) (by otype) ?_ h4
    orw [ev_prec_zero rfl hxs]
    rw [precZ]
    orw [ev_mpP hxs]
  · intro Γ t xs ht hxs hlen ih
    unfold okF at ih ⊢
    simp only [List.map_cons] at ih ⊢
    have h := prec_step hz jz hs js hh hcₛ (evTy (.cons ht hxs)) ht hxs hlen ih
    refine prf_congr_c (by otype) (by otype) (by otype) ?_ h
    orw [ev_prec_succ rfl hxs ht]

omit hz jz hs js hT in
theorem ok_prec_nil {g h τ : PR} (h1 : Ok env T (.prec g h) 1 τ) : Ok env T (.prec g h) 0 τ := by
  intro Γ xs hxs hlen
  obtain rfl : xs = [] := List.eq_nil_of_length_eq_zero hlen
  have p := h1 (Γ := Γ) (.cons zeroTy .nil) rfl
  unfold okF at p ⊢
  simp only [List.map_cons, List.map_nil] at p ⊢
  have eA : valF (.prec g h) 0 = (valF (.prec g h) 1).inst zero 1 := by
    simp only [valF, args, obj_simp]; rw [ev_nil_eq]
  rw [eA, ev_nil_eq (.prec g h), ev_nil_eq τ]
  have E : Thm env Γ (tmplH [litT (ev (.prec g h) [zero]), litT zero] (valF (.prec g h) 1) 0 =ₒ
      tmplH [litT (ev (.prec g h) [zero]), numT (encExpr zero)] (valF (.prec g h) 1) 0) :=
    tmplH_congr1 (hs₁ := [litT (ev (.prec g h) [zero])]) (.cons (by otype) .nil) .nil (by otype)
      (by otype) litT_zero _ 0
  have e : tmplH [litT (ev (.prec g h) [zero])] ((valF (.prec g h) 1).inst zero 1) 0 =
      tmplH [litT (ev (.prec g h) [zero]), numT (encExpr zero)] (valF (.prec g h) 1) 0 := by
    rw [← tmplH_zero []]
    exact tmplH_inst_insert [litT (ev (.prec g h) [zero])] [] (e := zero) trivial _ 0
  rw [e]
  exact prf_congr (by otype) (by otype) (by otype) E p

/-- **Internal Σ₁-completeness.** Every code has, at every arity, a code proving its graph
internally. -/
theorem ok_exists : ∀ (f : PR) (n : Nat), ∃ τ, Ok env T f n τ := by
  intro f
  induction f with
  | zero => intro n; exact ok_zeroLike hT (fun _ _ => rfl) rfl
  | var i =>
    intro n
    by_cases hi : i < n
    · exact ok_var hz jz hs js hT hi
    · refine ok_zeroLike hT (fun xs hl => ?_) ?_
      · rw [ev_var, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega), Option.getD_none]
      · simp only [valF, ev_var, args_getD, if_neg hi]
  | succ f ih => intro n; exact ok_succ hz jz hs js hT (ih n).choose_spec
  | push h g ihh ihg =>
    intro n; exact ok_push hz jz hs js hT (ihh n).choose_spec (ihg (n + 1)).choose_spec
  | prec g h ihg ihh =>
    intro n
    cases n with
    | zero =>
      obtain ⟨τ, hτ⟩ := ok_prec hz jz hs js hT (ihg 0).choose_spec (ihh 2).choose_spec
      exact ⟨τ, ok_prec_nil hτ⟩
    | succ n => exact ok_prec hz jz hs js hT (ihg n).choose_spec (ihh (n + 2)).choose_spec

end

end Incomplete.Obj
