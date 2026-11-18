import Incomplete.PR

/-!
# A library of primitive recursive codes

Renaming of variables, composition, numerals, addition, triangular numbers and pairing, each
with its `eval` lemma.
-/

namespace Incomplete
namespace PR

/-- A renaming under one more bound variable. -/
def liftR (σ : Nat → Nat) : Nat → Nat
  | 0 => 0
  | i + 1 => σ i + 1

/-- `ren σ f` reads variable `σ i` where `f` reads `i`. -/
def ren : (Nat → Nat) → PR → PR
  | _, zero => zero
  | σ, var i => var (σ i)
  | σ, succ f => succ (ren σ f)
  | σ, push h g => push (ren σ h) (ren (liftR σ) g)
  | σ, prec g h =>
    push (var (σ 0)) (prec (ren (fun i => σ (i + 1)) g) (ren (liftR (liftR fun i => σ (i + 1))) h))

theorem eval_ren : ∀ (f : PR) (σ : Nat → Nat) (ρ : Val), (ren σ f).eval ρ = f.eval (ρ ∘ σ)
  | zero, _, _ => rfl
  | var _, _, _ => rfl
  | succ f, σ, ρ => by simp [ren, eval, eval_ren f]
  | push h g, σ, ρ => by
    simp only [ren, eval, eval_ren h, eval_ren g]
    congr 1; funext i; cases i <;> rfl
  | prec g h, σ, ρ => by
    simp only [ren, eval, eval_ren g, eval_ren h]
    congr 1; funext y r; congr 1; funext i
    rcases i with _ | _ | i <;> rfl

/-- `g` with its variables `0` and `1` set to the values of `a` and `b`. -/
def comp2 (g a b : PR) : PR :=
  push a (push (ren Nat.succ b) (ren (fun | 0 => 1 | 1 => 0 | i => i) g))

def Computes2 (g : PR) (F : Nat → Nat → Nat) : Prop := ∀ ρ, g.eval ρ = F (ρ 0) (ρ 1)
def Computes1 (g : PR) (F : Nat → Nat) : Prop := ∀ ρ, g.eval ρ = F (ρ 0)

theorem eval_comp2 {g : PR} {F} (hg : Computes2 g F) (a b : PR) (ρ : Val) :
    (comp2 g a b).eval ρ = F (a.eval ρ) (b.eval ρ) := by
  simp only [comp2, eval, eval_ren]; rw [hg]; rfl

theorem eval_push {g : PR} {F} (hg : Computes1 g F) (a : PR) (ρ : Val) :
    (push a g).eval ρ = F (a.eval ρ) := hg _

def num : Nat → PR
  | 0 => zero
  | n + 1 => succ (num n)

@[simp] theorem eval_num (n : Nat) (ρ : Val) : (num n).eval ρ = n := by
  induction n <;> simp [num, eval, *]

theorem eval_var (i : Nat) (ρ : Val) : (var i).eval ρ = ρ i := rfl
theorem eval_succ (f : PR) (ρ : Val) : (succ f).eval ρ = f.eval ρ + 1 := rfl

theorem recNat_succ (z : Nat) (sf : Nat → Nat → Nat) (y : Nat) :
    recNat z sf (y + 1) = sf y (recNat z sf y) := rfl

def addC : PR := prec (var 0) (succ (var 0))

theorem addC_computes : Computes2 addC (· + ·) := by
  intro ρ
  show recNat (ρ 1) (fun _ r => r + 1) (ρ 0) = ρ 0 + ρ 1
  generalize ρ 0 = y
  induction y with
  | zero => simp [recNat]
  | succ y ih => rw [recNat_succ, ih]; omega

/-- Product `ρ 0 * ρ 1`. -/
def mulC : PR := prec zero (comp2 addC (var 0) (var 2))

theorem mulC_computes : Computes2 mulC (· * ·) := by
  intro ρ
  show recNat 0 (fun y r => (comp2 addC (var 0) (var 2)).eval (vcons r (vcons y (tl ρ)))) (ρ 0) =
    ρ 0 * ρ 1
  generalize ρ 0 = y
  induction y with
  | zero => simp [recNat]
  | succ y ih =>
    rw [recNat_succ, eval_comp2 addC_computes, ih]; simp [eval_var, Nat.succ_mul]

def triC : PR := prec zero (comp2 addC (var 0) (succ (var 1)))

theorem triC_computes : Computes1 triC tri := by
  intro ρ
  show recNat 0 (fun y r => (comp2 addC (var 0) (succ (var 1))).eval (vcons r (vcons y (tl ρ))))
    (ρ 0) = tri (ρ 0)
  generalize ρ 0 = y
  induction y with
  | zero => rfl
  | succ y ih =>
    rw [recNat_succ, eval_comp2 addC_computes, ih, tri_succ]; rfl

def pairC : PR := comp2 addC (push addC triC) (var 1)

theorem pairC_computes : Computes2 pairC pair := by
  intro ρ
  rw [pairC, eval_comp2 addC_computes, eval_push triC_computes, addC_computes]; rfl

/-- The pair of the values of `a` and `b`. -/
def cpair (a b : PR) : PR := comp2 pairC a b

@[simp] theorem eval_cpair (a b : PR) (ρ : Val) :
    (cpair a b).eval ρ = pair (a.eval ρ) (b.eval ρ) := eval_comp2 pairC_computes a b ρ

def Computes3 (g : PR) (F : Nat → Nat → Nat → Nat) : Prop := ∀ ρ, g.eval ρ = F (ρ 0) (ρ 1) (ρ 2)

/-- `g` with its variables `0`, `1` and `2` set to the values of `a`, `b` and `c`. -/
def comp3 (g a b c : PR) : PR :=
  push a (push (ren Nat.succ b) (push (ren (· + 2) c)
    (ren (fun | 0 => 2 | 1 => 1 | 2 => 0 | i => i) g)))

theorem eval_comp3 {g : PR} {F} (hg : Computes3 g F) (a b c : PR) (ρ : Val) :
    (comp3 g a b c).eval ρ = F (a.eval ρ) (b.eval ρ) (c.eval ρ) := by
  simp only [comp3, eval, eval_ren]; rw [hg]; rfl

/-- Predecessor of variable `0`. -/
def predC : PR := prec zero (var 1)

theorem predC_computes : Computes1 predC (· - 1) := by
  intro ρ; show recNat 0 (fun y _ => y) (ρ 0) = ρ 0 - 1
  cases ρ 0 <;> rfl

/-- Truncated subtraction `ρ 0 - ρ 1`. -/
def subC : PR := comp2 (prec (var 0) (push (var 0) predC)) (var 1) (var 0)

theorem subC_computes : Computes2 subC (· - ·) := by
  have : Computes2 (prec (var 0) (push (var 0) predC)) (fun a b => b - a) := by
    intro ρ
    show recNat (ρ 1) (fun _ r => (push (var 0) predC).eval (vcons r (vcons _ (tl ρ)))) (ρ 0) =
      ρ 1 - ρ 0
    generalize ρ 0 = y
    induction y with
    | zero => rfl
    | succ y ih => rw [recNat_succ, eval_push predC_computes, eval_var, vcons_zero, ih]; omega
  intro ρ; rw [subC, eval_comp2 this]; rfl

/-- `if ρ 0 = 0 then ρ 1 else ρ 2`. -/
def selC : PR := prec (var 0) (var 3)

theorem selC_computes : Computes3 selC (fun x a b => if x = 0 then a else b) := by
  intro ρ; show recNat (ρ 1) (fun _ _ => ρ 2) (ρ 0) = _
  cases ρ 0 <;> rfl

/-- `if c = 0 then a else b`, on codes. -/
def ifz (c a b : PR) : PR := comp3 selC c a b

@[simp] theorem eval_ifz (c a b : PR) (ρ : Val) :
    (ifz c a b).eval ρ = if c.eval ρ = 0 then a.eval ρ else b.eval ρ :=
  eval_comp3 selC_computes c a b ρ

/-- `0` exactly when `a ≤ b`. -/
def leq (a b : PR) : PR := comp2 subC a b

@[simp] theorem eval_leq (a b : PR) (ρ : Val) : (leq a b).eval ρ = a.eval ρ - b.eval ρ :=
  eval_comp2 subC_computes a b ρ

/-- `0` exactly when `a = b`. -/
def eqz (a b : PR) : PR := comp2 addC (leq a b) (leq b a)

theorem eval_eqz (a b : PR) (ρ : Val) : (eqz a b).eval ρ = 0 ↔ a.eval ρ = b.eval ρ := by
  rw [eqz, eval_comp2 addC_computes, eval_leq, eval_leq]; omega

/-! ### Unpairing -/

/-- The largest `s` with `tri s ≤ n`. -/
def triRoot : Nat → Nat
  | 0 => 0
  | n + 1 => if tri (triRoot n + 1) ≤ n + 1 then triRoot n + 1 else triRoot n

theorem triRoot_spec : ∀ n, tri (triRoot n) ≤ n ∧ n < tri (triRoot n + 1)
  | 0 => ⟨Nat.le_refl _, by decide⟩
  | n + 1 => by
    have ⟨h1, h2⟩ := triRoot_spec n
    simp only [triRoot]
    split <;> rename_i h
    · refine ⟨h, ?_⟩; rw [tri_succ (triRoot n + 1)]; omega
    · omega

theorem tri_mono {s t : Nat} (h : s ≤ t) : tri s ≤ tri t := by
  rcases Nat.lt_or_eq_of_le h with h | rfl
  · exact Nat.le_trans (by rw [tri_succ]; omega) (tri_le h)
  · exact Nat.le_refl _

theorem triRoot_eq {n s : Nat} (h1 : tri s ≤ n) (h2 : n < tri (s + 1)) : triRoot n = s := by
  have ⟨k1, k2⟩ := triRoot_spec n
  rcases Nat.lt_trichotomy (triRoot n) s with l | e | l
  · have := tri_mono (show triRoot n + 1 ≤ s by omega); omega
  · exact e
  · have := tri_mono (show s + 1 ≤ triRoot n by omega); omega

theorem triRoot_pair (a b : Nat) : triRoot (pair a b) = a + b :=
  triRoot_eq (by unfold pair; omega) (by unfold pair; rw [tri_succ]; omega)

def unpair2 (n : Nat) : Nat := n - tri (triRoot n)
def unpair1 (n : Nat) : Nat := triRoot n - unpair2 n

@[simp] theorem unpair1_pair (a b : Nat) : unpair1 (pair a b) = a := by
  simp only [unpair1, unpair2, triRoot_pair]; unfold pair; omega
@[simp] theorem unpair2_pair (a b : Nat) : unpair2 (pair a b) = b := by
  simp only [unpair2, triRoot_pair]; unfold pair; omega

theorem pair_unpair (n : Nat) : pair (unpair1 n) (unpair2 n) = n := by
  have ⟨h1, h2⟩ := triRoot_spec n
  rw [tri_succ] at h2
  have e : unpair1 n + unpair2 n = triRoot n := by simp only [unpair1, unpair2]; omega
  unfold pair; rw [e]; simp only [unpair2]; omega

theorem unpair2_le (n : Nat) : unpair2 n ≤ n := Nat.sub_le _ _

theorem unpair1_le (n : Nat) : unpair1 n ≤ n := by
  conv => rhs; rw [← pair_unpair n]
  unfold pair; have := tri_mono (Nat.le_refl (unpair1 n + unpair2 n))
  have : unpair1 n + unpair2 n ≤ tri (unpair1 n + unpair2 n) := by
    generalize unpair1 n + unpair2 n = s
    induction s with
    | zero => exact Nat.le_refl _
    | succ s ih => rw [tri_succ]; omega
  omega

/-- A pair with a nonzero first component is above its second. -/
theorem unpair2_lt {n : Nat} (h : unpair1 n ≠ 0) : unpair2 n < n := by
  have := unpair1_le n
  conv => rhs; rw [← pair_unpair n]
  unfold pair
  have : unpair1 n + unpair2 n ≤ tri (unpair1 n + unpair2 n) := by
    generalize unpair1 n + unpair2 n = s
    induction s with
    | zero => exact Nat.le_refl _
    | succ s ih => rw [tri_succ]; omega
  omega

def triRootC : PR :=
  prec zero (ifz (leq (push (PR.succ (var 0)) triC) (PR.succ (var 1)))
    (PR.succ (var 0)) (var 0))

theorem triRootC_computes : Computes1 triRootC triRoot := by
  intro ρ
  show recNat 0 (fun y r => (ifz (leq (push (PR.succ (var 0)) triC) (PR.succ (var 1)))
    (PR.succ (var 0)) (var 0)).eval (vcons r (vcons y (tl ρ)))) (ρ 0) = _
  generalize ρ 0 = y
  induction y with
  | zero => rfl
  | succ y ih =>
    rw [recNat_succ, ih]
    simp only [eval_ifz, eval_leq, eval_push triC_computes, eval_succ, eval_var, vcons_zero,
      vcons_succ, triRoot]
    by_cases h : tri (triRoot y + 1) ≤ y + 1
    · rw [ite_eq_left (by omega), ite_eq_left h]
    · rw [ite_eq_right (by omega), ite_eq_right h]

/-- The components of the pair `a`. -/
def fstC (a : PR) : PR := comp2 subC (push a triRootC) (sndC a)
where sndC (a : PR) : PR := comp2 subC a (push (push a triRootC) triC)

def sndC (a : PR) : PR := fstC.sndC a

@[simp] theorem eval_sndC (a : PR) (ρ : Val) : (sndC a).eval ρ = unpair2 (a.eval ρ) := by
  simp only [sndC, fstC.sndC, eval_comp2 subC_computes, eval_push triC_computes,
    eval_push triRootC_computes]; rfl

@[simp] theorem eval_fstC (a : PR) (ρ : Val) : (fstC a).eval ρ = unpair1 (a.eval ρ) := by
  simp only [fstC, eval_comp2 subC_computes, eval_push triRootC_computes]
  rw [← sndC, eval_sndC]; rfl

/-! ### Course-of-values recursion

A list is `0` or `pair head tail + 1`. `histN F n` lists `cov F (n-1), …, cov F 0`, and
`cov F n` is `F n (histN F n)`: `F` sees every earlier value. -/

def histN (F : Nat → Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => pair (F n (histN F n)) (histN F n) + 1

def cov (F : Nat → Nat → Nat) (n : Nat) : Nat := F n (histN F n)

def tlN (L : Nat) : Nat := unpair2 (L - 1)
def hdN (L : Nat) : Nat := unpair1 (L - 1)

def iterTl (L : Nat) : Nat → Nat
  | 0 => L
  | i + 1 => tlN (iterTl L i)

theorem iterTl_succ' (L : Nat) : ∀ i, iterTl L (i + 1) = iterTl (tlN L) i
  | 0 => rfl
  | i + 1 => by rw [iterTl, iterTl_succ' L i]; rfl

/-- The `i`th entry of a list. -/
def nthN (L i : Nat) : Nat := hdN (iterTl L i)

theorem nthN_histN (F : Nat → Nat → Nat) :
    ∀ n j, j < n → nthN (histN F n) (n - 1 - j) = cov F j
  | n + 1, j, h => by
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | rfl
    · rw [show n + 1 - 1 - j = (n - 1 - j) + 1 by omega, nthN, iterTl_succ']
      have := nthN_histN F n j h
      simpa [tlN, histN, nthN] using this
    · simp [nthN, iterTl, hdN, histN, cov]

theorem histN_eq (F : Nat → Nat → Nat) (n : Nat) :
    histN F (n + 1) = pair (cov F n) (histN F n) + 1 := rfl

def histC (step : PR) : PR := prec (num 0) (PR.succ (cpair (comp2 step (var 1) (var 0)) (var 0)))

theorem histC_computes {step : PR} {F} (hs : Computes2 step F) : Computes1 (histC step) (histN F) := by
  intro ρ
  show recNat 0 (fun y r => (PR.succ (cpair (comp2 step (var 1) (var 0)) (var 0))).eval
    (vcons r (vcons y (tl ρ)))) (ρ 0) = _
  generalize ρ 0 = y
  induction y with
  | zero => rfl
  | succ y ih =>
    rw [recNat_succ, ih, eval_succ, eval_cpair, eval_comp2 hs]; rfl

/-- Course-of-values recursion on variable `0`. -/
def covC (step : PR) : PR := comp2 step (var 0) (histC step)

theorem covC_computes {step : PR} {F} (hs : Computes2 step F) : Computes1 (covC step) (cov F) := by
  intro ρ; rw [covC, eval_comp2 hs, histC_computes hs]; rfl

def iterC : PR := prec (var 0) (sndC (leq (var 0) (num 1)))

theorem iterC_computes : Computes2 iterC (fun i L => iterTl L i) := by
  intro ρ
  show recNat (ρ 1) (fun y r => (sndC (leq (var 0) (num 1))).eval (vcons r (vcons y (tl ρ))))
    (ρ 0) = _
  generalize ρ 0 = y
  induction y with
  | zero => rfl
  | succ y ih => rw [recNat_succ, ih, eval_sndC, eval_leq]; rfl

/-- The `i`th entry of the list `L`. -/
def nthC (L i : PR) : PR := fstC (leq (comp2 iterC i L) (num 1))

@[simp] theorem eval_nthC (L i : PR) (ρ : Val) : (nthC L i).eval ρ = nthN (L.eval ρ) (i.eval ρ) := by
  rw [nthC, eval_fstC, eval_leq, eval_comp2 iterC_computes]; rfl

@[simp] theorem tag0_div' {k p : Nat} (h : 0 < k) : (k * p) / k = p := Nat.mul_div_cancel_left _ h
@[simp] theorem tag0_mod' {k p : Nat} : (k * p) % k = 0 := Nat.mul_mod_right _ _

/-! ### Division by a constant -/

/-- `pair (ρ 0 / k) (ρ 0 % k)`. -/
def dmC (k : Nat) : PR :=
  prec (cpair (num 0) (num 0))
    (ifz (eqz (PR.succ (sndC (var 0))) (num k)) (cpair (PR.succ (fstC (var 0))) (num 0))
      (cpair (fstC (var 0)) (PR.succ (sndC (var 0)))))

theorem dmC_computes {k : Nat} (hk : 0 < k) : Computes1 (dmC k) (fun y => pair (y / k) (y % k)) := by
  intro ρ
  show recNat ((cpair (num 0) (num 0)).eval (tl ρ)) (fun y r =>
    (ifz (eqz (PR.succ (sndC (var 0))) (num k)) (cpair (PR.succ (fstC (var 0))) (num 0))
      (cpair (fstC (var 0)) (PR.succ (sndC (var 0))))).eval (vcons r (vcons y (tl ρ)))) (ρ 0) = _
  generalize ρ 0 = y
  induction y with
  | zero => simp [recNat]
  | succ y ih =>
    rw [recNat_succ, ih, eval_ifz]; dsimp only
    have hd := Nat.div_add_mod y k
    have hm := Nat.mod_lt y hk
    by_cases h : y % k + 1 = k
    · have e0 := (eval_eqz (PR.succ (sndC (var 0))) (num k)
        (vcons (pair (y / k) (y % k)) (vcons y (tl ρ)))).2 (by simp [eval_var, eval_succ, h])
      rw [ite_eq_left e0]
      simp only [eval_cpair, eval_succ, eval_fstC, eval_var, vcons_zero, unpair1_pair, eval_num]
      have e : y + 1 = k * (y / k + 1) := by rw [Nat.mul_add]; omega
      rw [e, tag0_div' hk, tag0_mod']
    · have e0 : (eqz (PR.succ (sndC (var 0))) (num k)).eval
          (vcons (pair (y / k) (y % k)) (vcons y (tl ρ))) ≠ 0 := fun e =>
        h (by simpa [eval_var, eval_succ] using (eval_eqz _ _ _).1 e)
      rw [ite_eq_right e0]
      simp only [eval_cpair, eval_succ, eval_fstC, eval_sndC, eval_var, vcons_zero,
        unpair1_pair, unpair2_pair]
      have e : y + 1 = k * (y / k) + (y % k + 1) := by omega
      have hl : y % k + 1 < k := by omega
      rw [e, Nat.mul_add_div hk, Nat.div_eq_of_lt hl, Nat.mul_add_mod, Nat.mod_eq_of_lt hl]
      rfl

def divC (k : Nat) (a : PR) : PR := fstC (push a (dmC k))
def modC (k : Nat) (a : PR) : PR := sndC (push a (dmC k))

@[simp] theorem eval_divC {k : Nat} (hk : 0 < k) (a : PR) (ρ : Val) :
    (divC k a).eval ρ = a.eval ρ / k := by
  simp [divC, eval_push (dmC_computes hk)]
@[simp] theorem eval_modC {k : Nat} (hk : 0 < k) (a : PR) (ρ : Val) :
    (modC k a).eval ρ = a.eval ρ % k := by
  simp [modC, eval_push (dmC_computes hk)]

/-- `k * a + t`. -/
def tagC (k t : Nat) (a : PR) : PR := comp2 addC (comp2 mulC (num k) a) (num t)

@[simp] theorem eval_tagC (k t : Nat) (a : PR) (ρ : Val) :
    (tagC k t a).eval ρ = k * a.eval ρ + t := by
  simp [tagC, eval_comp2 addC_computes, eval_comp2 mulC_computes, eval_num]


/-! ### Course-of-values recursion with a parameter -/

/-- The history of `F p` up to variable `0`, for the parameter `p` in variable `1`. -/
def histPC (step : PR) : PR :=
  prec (num 0) (PR.succ (cpair (comp3 step (var 2) (var 1) (var 0)) (var 0)))

theorem histPC_eval {step : PR} {F : Nat → Nat → Nat → Nat} (hs : Computes3 step F) (ρ : Val) :
    (histPC step).eval ρ = histN (F (ρ 1)) (ρ 0) := by
  show recNat 0 (fun y r => (PR.succ (cpair (comp3 step (var 2) (var 1) (var 0)) (var 0))).eval
    (vcons r (vcons y (tl ρ)))) (ρ 0) = _
  generalize ρ 0 = y
  induction y with
  | zero => rfl
  | succ y ih =>
    rw [recNat_succ, ih, eval_succ, eval_cpair, eval_comp3 hs]; rfl

/-- Course-of-values recursion on variable `0` with the parameter in variable `1`. -/
def covPC (step : PR) : PR := comp3 step (var 1) (var 0) (histPC step)

theorem covPC_computes {step : PR} {F : Nat → Nat → Nat → Nat} (hs : Computes3 step F) :
    Computes2 (covPC step) (fun n p => cov (F p) n) := by
  intro ρ; rw [covPC, eval_comp3 hs, histPC_eval hs]; rfl

/-- The value of variable `ρ i` named for readability in steps of three variables. -/
def val3 (a b c : Nat) : Val := vcons a (vcons b (vcons c fun _ => 0))

/-- `min a b`. -/
def minP (a b : PR) : PR := leq a (leq a b)

@[simp] theorem eval_minP (a b : PR) (ρ : Val) : (minP a b).eval ρ = min (a.eval ρ) (b.eval ρ) := by
  simp [minP]; omega

theorem pair_lt_pair {a b a' b' : Nat} (h : a + b < a' + b') : pair a b < pair a' b' := by
  unfold pair
  have := tri_le h
  rw [tri_succ] at this; omega

/-- Twice the value of `a`. -/
def dblC (a : PR) : PR := comp2 addC a a

/-- The constant `n`, built in binary. -/
def numC (n : Nat) : PR :=
  if n = 0 then .zero
  else if n % 2 = 0 then dblC (numC (n / 2)) else PR.succ (dblC (numC (n / 2)))
termination_by n
decreasing_by all_goals omega

@[simp] theorem eval_numC (n : Nat) (ρ : Val) : (numC n).eval ρ = n := by
  rw [numC]
  split
  · subst_vars; rfl
  have ih := eval_numC (n / 2) ρ
  split <;> simp only [dblC, eval_succ, eval_comp2 addC_computes, ih] <;> omega
termination_by n
decreasing_by omega


end PR
end Incomplete
