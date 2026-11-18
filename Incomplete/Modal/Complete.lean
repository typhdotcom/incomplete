import Incomplete.Modal.Kripke
import Incomplete.Modal.Deduction

/-!
# Completeness of GL for finite rooted models

`GL_complete`: a formula `A` that `GL` does not prove fails at the root `0` of some
`FinModel (n + 1)` in which `0` sees every other world and the valuation is false off the
variables of `A`. With `FinModel.GL_sound`, `GL_iff`: `GL ⊢ A` iff `A` is forced at every world
of every finite transitive irreflexive model.

Worlds are the subsets `X` of the subformulas `S` of `A` whose literals `lits S X` (each `D ∈ S`
if `D ∈ X`, `¬D` otherwise) are consistent. `X` sees `Y` (`Rel`) when every `□C ∈ X ∩ S` has
`C, □C ∈ Y` and some `□D ∈ S` is in `Y \ X`; `box_witness` supplies the successor refuting
`□B ∉ X`, using Löb's axiom and 4. The model consists of a world `X₀` refuting `A` followed by
its successors.
-/

namespace Incomplete
namespace Modal

deriving instance DecidableEq for Modal

/-- The subformulas of a formula. -/
def sub : Modal → List Modal
  | var n => [var n]
  | bot => [bot]
  | imp A B => imp A B :: (sub A ++ sub B)
  | box A => box A :: sub A

theorem mem_sub_self : ∀ A : Modal, A ∈ sub A
  | var _ | bot | imp _ _ | box _ => .head _

theorem sub_trans {D E : Modal} : ∀ {A : Modal}, D ∈ sub E → E ∈ sub A → D ∈ sub A
  | var _, h, hE | bot, h, hE => by
    simp only [sub, List.mem_singleton] at hE; subst hE; exact h
  | imp A B, h, hE => by
    simp only [sub, List.mem_cons, List.mem_append] at hE ⊢
    rcases hE with rfl | hE | hE
    · simpa [sub] using h
    · exact .inr (.inl (sub_trans h hE))
    · exact .inr (.inr (sub_trans h hE))
  | box A, h, hE => by
    simp only [sub, List.mem_cons] at hE ⊢
    rcases hE with rfl | hE
    · simpa [sub] using h
    · exact .inr (sub_trans h hE)

theorem imp_mem_sub {A B C : Modal} (h : imp B C ∈ sub A) : B ∈ sub A ∧ C ∈ sub A :=
  ⟨sub_trans (by simp [sub, mem_sub_self]) h, sub_trans (by simp [sub, mem_sub_self]) h⟩

theorem box_mem_sub {A B : Modal} (h : box B ∈ sub A) : B ∈ sub A :=
  sub_trans (by simp [sub, mem_sub_self]) h

/-- All sublists, one per choice of members. -/
def subs {α : Type} : List α → List (List α)
  | [] => [[]]
  | a :: l => (subs l).map (a :: ·) ++ subs l

theorem filter_mem_subs {α : Type} (p : α → Bool) : ∀ l : List α, l.filter p ∈ subs l
  | [] => .head _
  | a :: l => by
    simp only [List.filter_cons, subs, List.mem_append, List.mem_map]
    split
    · exact .inl ⟨_, filter_mem_subs p l, rfl⟩
    · exact .inr (filter_mem_subs p l)

theorem mem_of_mem_subs {α : Type} : ∀ {l Y : List α}, Y ∈ subs l → ∀ x ∈ Y, x ∈ l
  | [], Y, h, x, hx => by simp [subs] at h; subst h; nomatch hx
  | a :: l, Y, h, x, hx => by
    simp only [subs, List.mem_append, List.mem_map] at h
    rcases h with ⟨Z, hZ, rfl⟩ | h
    · rcases List.mem_cons.1 hx with rfl | hx
      · exact .head _
      · exact .tail _ (mem_of_mem_subs hZ x hx)
    · exact .tail _ (mem_of_mem_subs h x hx)

section
variable (S : List Modal)

/-- The literals of `X` over `S`: `D` for `D ∈ X`, `¬D` for `D ∉ X`. -/
def lits (X : List Modal) : List Modal := S.map fun D => if D ∈ X then D else neg D

/-- `X` is a world over `S`: its literals are consistent. -/
def MCS (X : List Modal) : Prop := Con (lits S X)

/-- Accessibility between worlds over `S`. -/
def Rel (X Y : List Modal) : Prop :=
  (∀ C, box C ∈ S → box C ∈ X → C ∈ Y ∧ box C ∈ Y) ∧ ∃ D, box D ∈ S ∧ box D ∉ X ∧ box D ∈ Y

variable {S}

theorem Rel.trans {X Y Z : List Modal} (h1 : Rel S X Y) (h2 : Rel S Y Z) : Rel S X Z :=
  ⟨fun C hS hX => h2.1 C hS (h1.1 C hS hX).2,
    let ⟨D, hS, hX, hY⟩ := h1.2; ⟨D, hS, hX, (h2.1 D hS hY).2⟩⟩

theorem Rel.irrefl {X : List Modal} (h : Rel S X X) : False :=
  let ⟨_, _, hX, hX'⟩ := h.2; hX hX'

theorem der_pos {X : List Modal} {D : Modal} (hS : D ∈ S) (hX : D ∈ X) : Der (lits S X) D :=
  .hyp (List.mem_map.2 ⟨D, hS, by simp [hX]⟩)

theorem der_neg {X : List Modal} {D : Modal} (hS : D ∈ S) (hX : D ∉ X) :
    Der (lits S X) (neg D) :=
  .hyp (List.mem_map.2 ⟨D, hS, by simp [hX]⟩)

theorem MCS.mem_of_der {X : List Modal} {D : Modal} (hX : MCS S X) (hS : D ∈ S)
    (h : Der (lits S X) D) : D ∈ X :=
  Classical.byContradiction fun hn => hX (h.absurd (der_neg hS hn))

theorem MCS.bot {X : List Modal} (hX : MCS S X) (hS : bot ∈ S) : bot ∉ X :=
  fun h => hX (der_pos hS h)

theorem MCS.imp {X : List Modal} {B C : Modal} (hX : MCS S X) (hS : imp B C ∈ S) (hB : B ∈ S)
    (hC : C ∈ S) : imp B C ∈ X ↔ (B ∈ X → C ∈ X) := by
  refine ⟨fun h hb => hX.mem_of_der hC (.mp (der_pos hS h) (der_pos hB hb)), fun h => ?_⟩
  refine hX.mem_of_der hS ?_
  by_cases hb : B ∈ X
  · exact .mp (.ax (.k1 _ _)) (der_pos hC (h hb))
  · exact .deduction (Der.absurd (.hyp (.head _)) ((der_neg hB hb).mono fun _ => .tail _))

end

/-- Extending a consistent `Γ` by a literal of each formula in `L`. -/
theorem extend : ∀ (L : List Modal) {Γ : List Modal}, Con Γ →
    ∃ p : Modal → Bool, Con (L.map (fun D => if p D then D else neg D) ++ Γ)
  | [], _, h => ⟨fun _ => true, h⟩
  | B :: L, Γ, h => by
    obtain ⟨p, hp⟩ := extend L h
    by_cases hB : B ∈ L
    · refine ⟨p, fun h' => hp (h'.mono fun x hx => ?_)⟩
      rcases List.mem_cons.1 hx with rfl | hx
      · exact List.mem_append_left _ (List.mem_map_of_mem hB)
      · exact hx
    · have hq (b : Bool) : L.map (fun D => if (if D = B then b else p D) = true then D else neg D)
          = L.map fun D => if p D then D else neg D :=
        List.map_congr_left fun D hD => by
          rw [ite_eq_right (show D ≠ B from fun e => hB (e ▸ hD))]
      rcases con_or hp B with h' | h'
      · refine ⟨fun D => if D = B then true else p D, ?_⟩
        rw [List.map_cons, hq]; simpa using h'
      · refine ⟨fun D => if D = B then false else p D, ?_⟩
        rw [List.map_cons, hq]; simpa using h'

theorem extend_sub (S : List Modal) {Γ : List Modal} (h : Con Γ) :
    ∃ Y ∈ subs S, MCS S Y ∧ (∀ D ∈ Γ, D ∈ S → D ∈ Y) ∧ (∀ D, neg D ∈ Γ → D ∈ S → D ∉ Y) := by
  obtain ⟨p, hp⟩ := extend S h
  have hl : lits S (S.filter p) = S.map fun D => if p D then D else neg D :=
    List.map_congr_left fun D hD => by simp [List.mem_filter, hD]
  rw [← hl] at hp
  refine ⟨_, filter_mem_subs p S, fun h => hp (h.mono fun _ => List.mem_append_left _), ?_, ?_⟩
  · intro D hD hS
    refine Classical.byContradiction fun hn => hp ?_
    exact Der.absurd (.hyp (List.mem_append_right _ hD))
      ((der_neg hS hn).mono fun _ => List.mem_append_left _)
  · intro D hD hS hY
    exact hp (Der.absurd ((der_pos hS hY).mono fun _ => List.mem_append_left _)
      (.hyp (List.mem_append_right _ hD)))

/-- The boxed members of `X` in `S`, unboxed. -/
def unboxes (S X : List Modal) : List Modal :=
  S.filterMap fun
    | box C => if box C ∈ X then some C else none
    | _ => none

theorem mem_unboxes {S X : List Modal} {C : Modal} :
    C ∈ unboxes S X ↔ box C ∈ S ∧ box C ∈ X := by
  simp only [unboxes, List.mem_filterMap]
  constructor
  · rintro ⟨E, hE, h⟩
    cases E <;> simp at h
    obtain ⟨h1, rfl⟩ := h; exact ⟨hE, h1⟩
  · rintro ⟨hS, hX⟩
    exact ⟨_, hS, by simp [hX]⟩

/-- **Successor witness**: a world `X` without `□B` sees a world without `B`. -/
theorem box_witness {S X : List Modal} {B : Modal} (hcl : ∀ C, box C ∈ S → C ∈ S)
    (hX : MCS S X) (hS : box B ∈ S) (hB : box B ∉ X) :
    ∃ Y ∈ subs S, MCS S Y ∧ Rel S X Y ∧ B ∉ Y := by
  let Cs := unboxes S X
  have hcon : Con (neg B :: box B :: (Cs ++ Cs.map box)) := by
    intro h
    have h1 := (Der.dne (Der.deduction h)).deduction.box
    have h2 := Der.mp (.ax (.loeb B)) h1
    refine hX (Der.absurd (Der.cut h2 fun x hx => ?_) (der_neg hS hB))
    simp only [List.map_append, List.map_map, List.mem_append, List.mem_map,
      Function.comp] at hx
    rcases hx with ⟨C, hC, rfl⟩ | ⟨C, hC, rfl⟩
    · exact der_pos (mem_unboxes.1 hC).1 (mem_unboxes.1 hC).2
    · exact .mp (.ax (GL_four C)) (der_pos (mem_unboxes.1 hC).1 (mem_unboxes.1 hC).2)
  obtain ⟨Y, hY, hm, hpos, hneg⟩ := extend_sub S hcon
  refine ⟨Y, hY, hm, ⟨fun C hCS hCX => ?_, B, hS, hB, hpos _ (by simp) hS⟩,
    hneg B (.head _) (hcl B hS)⟩
  have hC : C ∈ Cs := mem_unboxes.2 ⟨hCS, hCX⟩
  exact ⟨hpos C (by simp [hC]) (hcl C hCS), hpos (box C) (by simp [hC]) hCS⟩

open Classical in
/-- **Completeness of GL**: an unprovable formula fails at the root `0` of a finite transitive
irreflexive model in which `0` sees every other world, with valuation false off the variables of
the formula. -/
theorem GL_complete {A : Modal} (h : ¬GL A) :
    ∃ (n : Nat) (M : FinModel (n + 1)), M.Rooted ∧ (∀ i k, M.V i k = true → var k ∈ sub A) ∧
      ¬M.Forces 0 A := by
  let S := sub A
  have hcl : ∀ C, box C ∈ S → C ∈ S := fun _ => box_mem_sub
  have h0 : Con [neg A] := fun h' => h (.mp (.dne A rfl) (Der.deduction h').of_nil)
  obtain ⟨X₀, hX₀, hm₀, -, hneg₀⟩ := extend_sub S h0
  have hA : A ∉ X₀ := hneg₀ A (.head _) (mem_sub_self A)
  let ws := (subs S).filter fun Y => decide (MCS S Y ∧ Rel S X₀ Y)
  let w : Fin (ws.length + 1) → List Modal := fun i =>
    if h : i.1 = 0 then X₀ else ws[i.1 - 1]'(by have := i.2; omega)
  have hw0 : w 0 = X₀ := by simp [w]
  have hws : ∀ i, w i ∈ subs S ∧ MCS S (w i) ∧ (i ≠ 0 → Rel S X₀ (w i)) := by
    intro i
    by_cases h : i.1 = 0
    · have : i = 0 := Fin.ext h
      subst this
      exact hw0 ▸ ⟨hX₀, hm₀, fun h => (h rfl).elim⟩
    · have hm := List.getElem_mem (l := ws) (n := i.1 - 1) (by have := i.2; omega)
      have hwi : w i = ws[i.1 - 1]'(by have := i.2; omega) := dite_eq_right h
      rw [hwi]
      simp only [ws, List.mem_filter, decide_eq_true_eq] at hm
      exact ⟨hm.1, hm.2.1, fun _ => hm.2.2⟩
  have hall : ∀ Y ∈ subs S, MCS S Y → Rel S X₀ Y → ∃ i, w i = Y := by
    intro Y hY hm hr
    have : Y ∈ ws := List.mem_filter.2 ⟨hY, by simp [hm, hr]⟩
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 this
    exact ⟨⟨j + 1, by omega⟩, by simp [w]⟩
  let M : FinModel (ws.length + 1) :=
    { R := fun i j => decide (Rel S (w i) (w j))
      V := fun i k => decide (var k ∈ w i)
      trans := fun h1 h2 => decide_eq_true ((of_decide_eq_true h1).trans (of_decide_eq_true h2))
      irrefl := fun _ => decide_eq_false fun h => h.irrefl }
  have truth : ∀ D, D ∈ S → ∀ i, M.Forces i D ↔ D ∈ w i := by
    intro D
    induction D with
    | var k => intro _ i; exact decide_eq_true_iff
    | bot => intro hS i; exact iff_of_false id ((hws i).2.1.bot hS)
    | imp B C ihB ihC =>
      intro hS i
      have ⟨hB, hC⟩ := imp_mem_sub hS
      rw [(hws i).2.1.imp hS hB hC]
      exact imp_congr (ihB hB i) (ihC hC i)
    | box B ih =>
      intro hS i
      have hB := box_mem_sub hS
      show (∀ j, M.R i j = true → M.Forces j B) ↔ _
      constructor
      · intro hf
        refine Classical.byContradiction fun hn => ?_
        obtain ⟨Y, hY, hm, hr, hBY⟩ := box_witness hcl (hws i).2.1 hS hn
        have hr0 : Rel S X₀ Y := by
          by_cases hi : i = 0
          · subst hi; rwa [hw0] at hr
          · exact ((hws i).2.2 hi).trans hr
        obtain ⟨j, rfl⟩ := hall Y hY hm hr0
        exact hBY ((ih hB j).1 (hf j (decide_eq_true hr)))
      · intro hb j hj
        exact (ih hB j).2 ((of_decide_eq_true hj).1 B hS hb).1
  refine ⟨ws.length, M, fun i hi => ?_, fun i k hk => ?_, fun hf => hA ?_⟩
  · exact decide_eq_true (hw0 ▸ (hws i).2.2 hi)
  · exact mem_of_mem_subs (hws i).1 _ (of_decide_eq_true hk)
  · rw [← hw0]; exact (truth A (mem_sub_self A) 0).1 hf

/-- `GL ⊢ A` iff `A` is forced at every world of every finite transitive irreflexive model. -/
theorem GL_iff {A : Modal} : GL A ↔ ∀ (n : Nat) (M : FinModel n) (w : Fin n), M.Forces w A := by
  refine ⟨fun h n M w => M.GL_sound h w, fun h => Classical.byContradiction fun hA => ?_⟩
  obtain ⟨n, M, -, -, hM⟩ := GL_complete hA
  exact hM (h _ M 0)

end Modal
end Incomplete
