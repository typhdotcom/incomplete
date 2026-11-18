import Incomplete.Modal.Complete

/-!
# Letterless formulas and the level tower

A letterless formula has no variables. `lvl n A` evaluates `A` at level `n` of the tower on `ω`:
`□B` holds at level `n` when `B` holds at every level `m < n`.

`Kripke.forces_iff_lvl`: on a model with a height `ht` (`IsHeight`), a letterless formula is
forced at `w` iff it holds at level `ht w`. Every `FinModel` has such a height (`FinModel.height`,
the length of the longest `R`-chain above a world), so forcing of letterless formulas depends only
on the height (`FinModel.forces_iff_lvl`).

`GL_iff_lvl`: `GL ⊢ A` iff `A` holds at every level. `lvl_eq_lim`: `lvl n A` is constant,
`lim A`, from the box depth `bd A` on; so `dec A`, which checks the levels `n ≤ bd A`, decides `GL`
on letterless formulas (`GL_iff_dec`).

`not_iGL_dne_box`: the letterless `GL` theorem `¬¬□⊥ → □⊥` is not a theorem of `iGL`.
-/

namespace Incomplete
namespace Modal

/-- `A` has no variables. -/
def Letterless : Modal → Prop
  | var _ => False
  | bot => True
  | imp A B => Letterless A ∧ Letterless B
  | box A => Letterless A

/-- The value of `A` at level `n`: `□B` holds at `n` when `B` holds at every `m < n`. Variables
are `false`. -/
def lvl (n : Nat) : Modal → Bool
  | var _ => false
  | bot => false
  | imp A B => !lvl n A || lvl n B
  | box A => decide (∀ m, m < n → lvl m A = true)

@[simp] theorem lvl_bot (n : Nat) : lvl n bot = false := rfl
theorem lvl_imp (n : Nat) (A B : Modal) : lvl n (imp A B) = (!lvl n A || lvl n B) := rfl
theorem lvl_box (n : Nat) (A : Modal) :
    lvl n (box A) = decide (∀ m, m < n → lvl m A = true) := rfl

theorem lvl_imp_eq_true {n : Nat} {A B : Modal} :
    lvl n (imp A B) = true ↔ (lvl n A = true → lvl n B = true) := by
  rw [lvl_imp]; cases lvl n A <;> simp

theorem lvl_box_eq_true {n : Nat} {A : Modal} :
    lvl n (box A) = true ↔ ∀ m, m < n → lvl m A = true := by
  rw [lvl_box]; exact decide_eq_true_iff

/-- Box depth. -/
def bd : Modal → Nat
  | var _ | bot => 0
  | imp A B => max (bd A) (bd B)
  | box A => bd A + 1

/-- **Stabilisation.** From the box depth on, the level value is constant. -/
theorem lvl_eq_of_bd_le : ∀ (A : Modal) {n : Nat}, bd A ≤ n → lvl n A = lvl (bd A) A
  | var _, _, _ | bot, _, _ => rfl
  | imp A B, n, h => by
    have hA : bd A ≤ bd (imp A B) := Nat.le_max_left _ _
    have hB : bd B ≤ bd (imp A B) := Nat.le_max_right _ _
    simp only [bd] at h hA hB ⊢
    rw [lvl_imp, lvl_imp, lvl_eq_of_bd_le A (Nat.le_trans hA h), lvl_eq_of_bd_le B (Nat.le_trans hB h),
      lvl_eq_of_bd_le A hA, lvl_eq_of_bd_le B hB]
  | box A, n, h => by
    simp only [bd] at h ⊢
    rw [lvl_box, lvl_box, decide_eq_decide]
    have st : ∀ m, bd A ≤ m → lvl m A = lvl (bd A) A := fun m hm => lvl_eq_of_bd_le A hm
    constructor
    · intro hl m hm; exact hl m (by omega)
    · intro hl m hm
      if hm' : m < bd A + 1 then exact hl m hm'
      else rw [st m (by omega)]; exact hl _ (by omega)

/-- The eventual value of `A`. -/
def lim (A : Modal) : Bool := lvl (bd A) A

theorem lvl_eq_lim {A : Modal} {n : Nat} (h : bd A ≤ n) : lvl n A = lim A :=
  lvl_eq_of_bd_le A h

/-- Checks the levels `n ≤ bd A`. -/
def dec (A : Modal) : Bool := (List.range (bd A + 1)).all fun n => lvl n A

theorem dec_iff {A : Modal} : dec A = true ↔ ∀ n, lvl n A = true := by
  simp only [dec, List.all_eq_true, List.mem_range]
  constructor
  · intro h n
    if hn : n < bd A + 1 then exact h n hn
    else rw [lvl_eq_of_bd_le A (by omega)]; exact h _ (by omega)
  · exact fun h n _ => h n

theorem lim_box {A : Modal} : lim (box A) = dec A := by
  rw [Bool.eq_iff_iff, dec_iff, lim, bd, lvl_box_eq_true]
  constructor
  · intro h n
    if hn : n < bd A + 1 then exact h n hn
    else rw [lvl_eq_of_bd_le A (by omega)]; exact h _ (by omega)
  · exact fun h n _ => h n

theorem lim_imp {A B : Modal} : lim (imp A B) = (!lim A || lim B) := by
  simp only [lim, bd, lvl_imp]
  rw [lvl_eq_of_bd_le A (Nat.le_max_left _ _), lvl_eq_of_bd_le B (Nat.le_max_right _ _)]

/-- A height for `R`: it drops along `R`, and the successors of `w` take every smaller value. -/
structure IsHeight {α : Type} (R : α → α → Prop) (ht : α → Nat) : Prop where
  lt : ∀ w w', R w w' → ht w' < ht w
  surj : ∀ w k, k < ht w → ∃ w', R w w' ∧ ht w' = k

namespace Kripke
variable {α : Type} (M : Kripke α)

/-- **Height lemma.** A letterless formula is forced at `w` iff it holds at level `ht w`. -/
theorem forces_iff_lvl {ht : α → Nat} (hR : IsHeight M.R ht) :
    ∀ {A : Modal}, Letterless A → ∀ w, (M.Forces w A ↔ lvl (ht w) A = true)
  | var _, h, _ => h.elim
  | bot, _, w => by simp [Forces]
  | imp A B, h, w => by
    rw [lvl_imp_eq_true, ← forces_iff_lvl hR (A := A) h.1, ← forces_iff_lvl hR (A := B) h.2]; rfl
  | box A, h, w => by
    rw [lvl_box_eq_true]
    constructor
    · intro hf m hm
      obtain ⟨v, hv, rfl⟩ := hR.surj w m hm
      exact (forces_iff_lvl hR (A := A) h v).1 (hf v hv)
    · intro hl v hv
      exact (forces_iff_lvl hR (A := A) h v).2 (hl _ (hR.lt w v hv))

end Kripke

theorem foldr_max_ge {α : Type} (f : α → Nat) :
    ∀ {l : List α} {x : α}, x ∈ l → f x ≤ (l.map f).foldr max 0
  | _ :: _, _, .head _ => Nat.le_max_left _ _
  | _ :: _, _, .tail _ h => Nat.le_trans (foldr_max_ge f h) (Nat.le_max_right _ _)

theorem foldr_max_mem {α : Type} (f : α → Nat) :
    ∀ l : List α, (l.map f).foldr max 0 = 0 ∨ ∃ x ∈ l, (l.map f).foldr max 0 = f x
  | [] => .inl rfl
  | a :: l => by
    simp only [List.map_cons, List.foldr_cons]
    rcases Nat.le_total (f a) ((l.map f).foldr max 0) with h | h
    · rw [Nat.max_eq_right h]
      rcases foldr_max_mem f l with h' | ⟨x, hx, e⟩
      · exact .inl h'
      · exact .inr ⟨x, .tail _ hx, e⟩
    · rw [Nat.max_eq_left h]; exact .inr ⟨a, .head _, rfl⟩

namespace FinModel
variable {n : Nat} (M : FinModel n)

/-- The height of `w`: `0` without successors, else one more than the largest height of a
successor; the length of the longest `R`-chain starting at `w`. -/
noncomputable def height : Fin n → Nat :=
  M.wf.fix fun w ih =>
    ((List.finRange n).map fun v => if h : M.R w v = true then ih v h + 1 else 0).foldr max 0

theorem height_eq (w : Fin n) : M.height w =
    ((List.finRange n).map fun v => if M.R w v = true then M.height v + 1 else 0).foldr max 0 := by
  unfold height
  rw [WellFounded.fix_eq]
  congr 2

theorem height_lt {w v : Fin n} (h : M.R w v = true) : M.height v < M.height w := by
  have := foldr_max_ge (fun v => if M.R w v = true then M.height v + 1 else 0)
    (List.mem_finRange v)
  rw [← height_eq] at this
  simp only [h, if_true] at this
  omega

theorem isHeight : IsHeight M.toKripke.R M.height where
  lt _ _ h := M.height_lt h
  surj := by
    intro w
    induction w using M.wf.induction with
    | _ w ih =>
    intro k hk
    rcases foldr_max_mem (fun v => if M.R w v = true then M.height v + 1 else 0)
      (List.finRange n) with h | ⟨v, -, e⟩
    · rw [← height_eq] at h; omega
    · rw [← height_eq] at e
      split at e
      · rename_i hv
        if hk' : k = M.height v then exact ⟨v, hv, hk'.symm⟩
        else
          obtain ⟨u, hu, rfl⟩ := ih v hv k (by omega)
          exact ⟨u, M.trans hv hu, rfl⟩
      · omega

/-- **Height lemma** for finite models. -/
theorem forces_iff_lvl {A : Modal} (hA : Letterless A) (w : Fin n) :
    M.Forces w A ↔ lvl (M.height w) A = true :=
  M.toKripke.forces_iff_lvl M.isHeight hA w

/-- Forcing of a letterless formula depends only on the height of the world. -/
theorem forces_congr_height {m : Nat} (M' : FinModel m) {A : Modal} (hA : Letterless A)
    {w : Fin n} {w' : Fin m} (h : M.height w = M'.height w') : M.Forces w A ↔ M'.Forces w' A := by
  rw [M.forces_iff_lvl hA, M'.forces_iff_lvl hA, h]

/-- The chain `0 < 1 < … < n - 1`, each world seeing the smaller ones. -/
def chain (n : Nat) : FinModel n where
  R a b := decide (b < a)
  V _ _ := false
  trans h1 h2 := by simp only [decide_eq_true_eq] at *; omega
  irrefl a := by simp

theorem chain_isHeight (n : Nat) : IsHeight (chain n).toKripke.R Fin.val where
  lt _ _ h := by simpa [toKripke, chain, Fin.lt_def] using h
  surj w k hk := ⟨⟨k, by omega⟩, by simpa [toKripke, chain, Fin.lt_def] using hk, rfl⟩

end FinModel

/-- **GL on letterless formulas is the level tower.** -/
theorem GL_iff_lvl {A : Modal} (hA : Letterless A) : GL A ↔ ∀ n, lvl n A = true := by
  rw [GL_iff]
  constructor
  · intro h n
    have := (FinModel.chain (n + 1)).toKripke.forces_iff_lvl (FinModel.chain_isHeight _) hA
      ⟨n, by omega⟩
    exact this.1 (h _ _ _)
  · intro h m M w
    exact (M.forces_iff_lvl hA w).2 (h _)

/-- **Decision procedure.** `GL` derivability of a letterless formula is the Boolean `dec A`. -/
theorem GL_iff_dec {A : Modal} (hA : Letterless A) : GL A ↔ dec A = true :=
  (GL_iff_lvl hA).trans dec_iff.symm

instance decLetterless : (A : Modal) → Decidable (Letterless A)
  | var _ => isFalse id
  | bot => isTrue trivial
  | imp A B => @instDecidableAnd _ _ (decLetterless A) (decLetterless B)
  | box A => decLetterless A

/-- `□ⁿ⊥`. -/
def boxBot : Nat → Modal
  | 0 => bot
  | n + 1 => box (boxBot n)

theorem boxBot_letterless : ∀ n, Letterless (boxBot n)
  | 0 => trivial
  | n + 1 => boxBot_letterless n

theorem lvl_boxBot : ∀ (n k : Nat), lvl k (boxBot n) = decide (k < n)
  | 0, k => by simp [boxBot]
  | n + 1, k => by
    rw [Bool.eq_iff_iff, boxBot, lvl_box_eq_true, decide_eq_true_iff]
    simp only [lvl_boxBot n, decide_eq_true_eq]
    constructor
    · intro h; if hk : k < n + 1 then exact hk else exact absurd (h n (by omega)) (by omega)
    · intro h m hm; omega

theorem bd_boxBot : ∀ n, bd (boxBot n) = n
  | 0 => rfl
  | n + 1 => congrArg (· + 1) (bd_boxBot n)

theorem lim_boxBot (n : Nat) : lim (boxBot n) = false := by
  rw [lim, lvl_boxBot, bd_boxBot]; simp

/-- `□ⁿ⁺¹⊥ → □ⁿ⊥` is eventually true but fails at level `n`, so `GL` does not prove it. -/
theorem boxBot_succ_imp (n : Nat) : lim (imp (boxBot (n + 1)) (boxBot n)) = true ∧
    ¬GL (imp (boxBot (n + 1)) (boxBot n)) := by
  refine ⟨by rw [lim_imp, lim_boxBot, lim_boxBot]; rfl, fun h => ?_⟩
  have := (GL_iff_lvl (A := imp (boxBot (n + 1)) (boxBot n))
    ⟨boxBot_letterless (n + 1), boxBot_letterless n⟩).1 h n
  rw [lvl_imp, lvl_boxBot, lvl_boxBot] at this
  simp at this

/-- Implication of the three-element chain `0 < 1 < 2`. -/
def himp (a b : Fin 3) : Fin 3 := if a ≤ b then 2 else b
/-- `□0 = 1`, `□1 = □2 = 2`. -/
def hbox (a : Fin 3) : Fin 3 := if a = 0 then 1 else 2

/-- `A` valued in the three-element `iGL` algebra, variables at `0`. -/
def hv : Modal → Fin 3
  | var _ | bot => 0
  | imp A B => himp (hv A) (hv B)
  | box A => hbox (hv A)

theorem hv_iGL {A : Modal} (h : iGL A) : hv A = 2 := by
  induction h with
  | k1 A B => exact (by decide : ∀ a b : Fin 3, himp a (himp b a) = 2) _ _
  | s A B C =>
    exact (by decide : ∀ a b c : Fin 3,
      himp (himp a (himp b c)) (himp (himp a b) (himp a c)) = 2) _ _ _
  | efq A => exact (by decide : ∀ a : Fin 3, himp 0 a = 2) _
  | dne _ h => exact absurd h (by decide)
  | k A B =>
    exact (by decide : ∀ a b : Fin 3, himp (hbox (himp a b)) (himp (hbox a) (hbox b)) = 2) _ _
  | loeb A => exact (by decide : ∀ a : Fin 3, himp (hbox (himp (hbox a) a)) (hbox a) = 2) _
  | mp _ _ ih1 ih2 =>
    exact (by decide : ∀ a b : Fin 3, himp a b = 2 → a = 2 → b = 2) _ _ ih1 ih2
  | nec _ ih => show hbox _ = 2; rw [ih]; rfl

/-- `¬¬□⊥ → □⊥` is a theorem of `GL` but not of `iGL`. -/
theorem not_iGL_dne_box : GL (imp (neg (neg (box bot))) (box bot)) ∧
    ¬iGL (imp (neg (neg (box bot))) (box bot)) :=
  ⟨(GL_iff_dec (by decide)).2 (by decide),
    fun h => absurd (hv_iGL h) (by decide)⟩

end Modal
end Incomplete
