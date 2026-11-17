import Incomplete.ZF

/-!
# A universe of small sets

`V0 : ZFSet.{1}` is the set of the sets of `ZFSet.{0}`, embedded by `lift`. Its members are the
sets of members of `V0` indexed by a type in `Type`, so it is closed under the constructions
of `ZF.lean`; in particular under `pi`, which makes it a model of the object theory's `Type`.
-/

namespace Incomplete

attribute [local instance] Classical.propDecidable

namespace PSet

def lift : PSet.{0} → PSet.{1}
  | mk α A => mk (ULift α) fun a => lift (A a.down)

theorem lift_equiv : ∀ {x y : PSet.{0}}, Equiv x y → Equiv (lift x) (lift y)
  | mk α A, mk β B, h => by
    obtain ⟨αβ, βα⟩ := equiv_mk.1 h
    refine equiv_mk.2 ⟨fun a => ?_, fun b => ?_⟩
    · obtain ⟨b, hb⟩ := αβ a.down; exact ⟨⟨b⟩, lift_equiv hb⟩
    · obtain ⟨a, ha⟩ := βα b.down; exact ⟨⟨a⟩, lift_equiv ha⟩

end PSet

namespace ZFSet

noncomputable def lift (s : ZFSet.{0}) : ZFSet.{1} := mk (PSet.lift s.out)

theorem lift_mk (p : PSet.{0}) : lift (mk p) = mk (PSet.lift p) :=
  mk_eq.2 (PSet.lift_equiv (mk_eq.1 (mk_out (mk p))))

theorem mem_lift {s : ZFSet.{0}} {z : ZFSet.{1}} : z ∈ lift s ↔ ∃ t ∈ s, z = lift t := by
  rw [← mk_out s, lift_mk]
  generalize s.out = p
  obtain ⟨α, A⟩ := p
  rw [← mk_out z]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨mk (A a.down), ⟨a.down, PSet.Equiv.refl _⟩, by rw [lift_mk]; exact mk_eq.2 ha⟩
  · rintro ⟨t, ht, e⟩
    rw [← mk_out t] at e ht
    obtain ⟨a, ha⟩ := (mem_mk.1 ht : PSet.Mem _ _)
    refine ⟨⟨a⟩, ?_⟩
    rw [lift_mk] at e
    exact (mk_eq.1 e).trans (PSet.lift_equiv ha)

noncomputable def V0 : ZFSet.{1} := ofFn lift

theorem mem_V0 {x : ZFSet.{1}} : x ∈ V0 ↔ ∃ s, x = lift s := mem_ofFn

/-- `x`'s members are indexed by a type in `Type`. -/
def Small (x : ZFSet.{1}) : Prop := ∃ (α : Type) (f : α → ZFSet.{1}), ∀ y, y ∈ x ↔ ∃ a, y = f a

theorem mem_V0_iff {x : ZFSet.{1}} : x ∈ V0 ↔ (∀ y ∈ x, y ∈ V0) ∧ Small x := by
  constructor
  · intro h
    obtain ⟨s, rfl⟩ := mem_V0.1 h
    refine ⟨fun y hy => ?_, ⟨s.Idx, fun i => lift (s.elt i), fun y => ?_⟩⟩
    · obtain ⟨t, _, rfl⟩ := mem_lift.1 hy; exact mem_V0.2 ⟨t, rfl⟩
    · rw [mem_lift]
      constructor
      · rintro ⟨t, ht, rfl⟩; obtain ⟨i, rfl⟩ := mem_iff.1 ht; exact ⟨i, rfl⟩
      · rintro ⟨i, rfl⟩; exact ⟨_, elt_mem _ _, rfl⟩
  · rintro ⟨h, α, f, hf⟩
    have hs : ∀ a, ∃ t, f a = lift t := fun a => mem_V0.1 (h _ ((hf _).2 ⟨a, rfl⟩))
    refine mem_V0.2 ⟨ofFn fun a => (hs a).choose, ext fun z => ?_⟩
    rw [hf, mem_lift]
    constructor
    · rintro ⟨a, rfl⟩; exact ⟨_, mem_ofFn.2 ⟨a, rfl⟩, (hs a).choose_spec⟩
    · rintro ⟨t, ht, rfl⟩
      obtain ⟨a, rfl⟩ := mem_ofFn.1 ht
      exact ⟨a, ((hs a).choose_spec).symm⟩

theorem V0_trans {x y : ZFSet.{1}} (hx : x ∈ V0) (hy : y ∈ x) : y ∈ V0 :=
  (mem_V0_iff.1 hx).1 y hy

theorem small_of_mem {x : ZFSet.{1}} (hx : x ∈ V0) : Small x := (mem_V0_iff.1 hx).2

theorem mem_V0_of {x : ZFSet.{1}} (h : ∀ y ∈ x, y ∈ V0) (hs : Small x) : x ∈ V0 :=
  mem_V0_iff.2 ⟨h, hs⟩

theorem empty_mem_V0 : (empty : ZFSet.{1}) ∈ V0 :=
  mem_V0_of (fun y h => absurd h (not_mem_empty _)) ⟨PEmpty, PEmpty.elim, fun y => by simp; exact fun x => x.elim⟩

theorem pair_mem_V0 {a b : ZFSet.{1}} (ha : a ∈ V0) (hb : b ∈ V0) : pair a b ∈ V0 :=
  mem_V0_of (fun y hy => by rcases mem_pair.1 hy with rfl | rfl <;> assumption)
    ⟨Bool, fun i => if i then a else b, fun y => by
      rw [mem_pair]
      constructor
      · rintro (rfl | rfl)
        · exact ⟨true, rfl⟩
        · exact ⟨false, rfl⟩
      · rintro ⟨_ | _, rfl⟩ <;> simp⟩

theorem single_mem_V0 {a : ZFSet.{1}} (ha : a ∈ V0) : single a ∈ V0 := pair_mem_V0 ha ha

theorem kpair_mem_V0 {a b : ZFSet.{1}} (ha : a ∈ V0) (hb : b ∈ V0) : kpair a b ∈ V0 :=
  pair_mem_V0 (single_mem_V0 ha) (pair_mem_V0 ha hb)

theorem sep_mem_V0 {x : ZFSet.{1}} (hx : x ∈ V0) (P : ZFSet.{1} → Prop) : sep x P ∈ V0 := by
  obtain ⟨α, f, hf⟩ := small_of_mem hx
  refine mem_V0_of (fun y hy => V0_trans hx (mem_sep.1 hy).1)
    ⟨{a : α // P (f a)}, fun a => f a.1, fun y => ?_⟩
  rw [mem_sep, hf]
  constructor
  · rintro ⟨⟨a, rfl⟩, hp⟩; exact ⟨⟨a, hp⟩, rfl⟩
  · rintro ⟨⟨a, hp⟩, rfl⟩; exact ⟨⟨a, rfl⟩, hp⟩

theorem sub_mem_V0 {x y : ZFSet.{1}} (hx : x ∈ V0) (h : ∀ z ∈ y, z ∈ x) : y ∈ V0 := by
  have : y = sep x (· ∈ y) := ext fun z => by rw [mem_sep]; exact ⟨fun hz => ⟨h z hz, hz⟩, And.right⟩
  rw [this]; exact sep_mem_V0 hx _

theorem sUnion_mem_V0 {x : ZFSet.{1}} (hx : x ∈ V0) : sUnion x ∈ V0 := by
  obtain ⟨α, f, hf⟩ := small_of_mem hx
  have hs : ∀ a, Small (f a) := fun a => small_of_mem (V0_trans hx ((hf _).2 ⟨a, rfl⟩))
  refine mem_V0_of (fun y hy => ?_) ⟨Σ a, (hs a).choose, fun p => (hs p.1).choose_spec.choose p.2,
    fun y => ?_⟩
  · obtain ⟨z, hz, hyz⟩ := mem_sUnion.1 hy; exact V0_trans (V0_trans hx hz) hyz
  · rw [mem_sUnion]
    constructor
    · rintro ⟨z, hz, hyz⟩
      obtain ⟨a, rfl⟩ := (hf z).1 hz
      obtain ⟨b, rfl⟩ := ((hs a).choose_spec.choose_spec y).1 hyz
      exact ⟨⟨a, b⟩, rfl⟩
    · rintro ⟨⟨a, b⟩, rfl⟩
      exact ⟨f a, (hf _).2 ⟨a, rfl⟩, ((hs a).choose_spec.choose_spec _).2 ⟨b, rfl⟩⟩

theorem powerset_mem_V0 {x : ZFSet.{1}} (hx : x ∈ V0) : powerset x ∈ V0 := by
  obtain ⟨α, f, hf⟩ := small_of_mem hx
  refine mem_V0_of (fun y hy => sub_mem_V0 hx (mem_powerset.1 hy))
    ⟨α → Prop, fun S => sep x fun z => ∃ a, S a ∧ z = f a, fun y => ?_⟩
  rw [mem_powerset]
  constructor
  · intro h
    refine ⟨fun a => f a ∈ y, ext fun z => ?_⟩
    rw [mem_sep]
    constructor
    · intro hz
      obtain ⟨a, rfl⟩ := (hf z).1 (h z hz)
      exact ⟨h _ hz, a, hz, rfl⟩
    · rintro ⟨-, a, ha, rfl⟩; exact ha
  · rintro ⟨S, rfl⟩ z hz; exact (mem_sep.1 hz).1

theorem lam_mem_V0 {A : ZFSet.{1}} {f : ZFSet.{1} → ZFSet.{1}} (hA : A ∈ V0)
    (hf : ∀ x ∈ A, f x ∈ V0) : lam A f ∈ V0 := by
  obtain ⟨α, g, hg⟩ := small_of_mem hA
  have hs : ∀ a, Small (f (g a)) := fun a => small_of_mem (hf _ ((hg _).2 ⟨a, rfl⟩))
  refine mem_V0_of (fun z hz => ?_) ⟨Σ a, (hs a).choose,
    fun p => kpair (g p.1) ((hs p.1).choose_spec.choose p.2), fun z => ?_⟩
  · obtain ⟨x, hx, y, hy, rfl⟩ := mem_lam.1 hz
    exact kpair_mem_V0 (V0_trans hA hx) (V0_trans (hf x hx) hy)
  · rw [mem_lam]
    constructor
    · rintro ⟨x, hx, y, hy, rfl⟩
      obtain ⟨a, rfl⟩ := (hg x).1 hx
      obtain ⟨b, rfl⟩ := ((hs a).choose_spec.choose_spec y).1 hy
      exact ⟨⟨a, b⟩, rfl⟩
    · rintro ⟨⟨a, b⟩, rfl⟩
      exact ⟨g a, (hg _).2 ⟨a, rfl⟩, _, ((hs a).choose_spec.choose_spec _).2 ⟨b, rfl⟩, rfl⟩

/-- **`V0` is closed under dependent products.** -/
theorem pi_mem_V0 {A : ZFSet.{1}} {B : ZFSet.{1} → ZFSet.{1}} (hA : A ∈ V0)
    (hB : ∀ x ∈ A, B x ∈ V0) : pi A B ∈ V0 := by
  have hT : lam A (fun x => sUnion (B x)) ∈ V0 :=
    lam_mem_V0 hA fun x hx => sUnion_mem_V0 (hB x hx)
  refine sub_mem_V0 (powerset_mem_V0 hT) fun F hF => ?_
  rw [mem_powerset]
  obtain ⟨f, hf, rfl⟩ := mem_pi.1 hF
  intro z hz
  obtain ⟨x, hx, y, hy, rfl⟩ := mem_lam.1 hz
  exact mem_lam.2 ⟨x, hx, y, mem_sUnion.2 ⟨f x, hf x hx, hy⟩, rfl⟩

theorem two_mem_V0 : (two : ZFSet.{1}) ∈ V0 :=
  pair_mem_V0 empty_mem_V0 (single_mem_V0 empty_mem_V0)

theorem num_mem_V0 : ∀ n, (num n : ZFSet.{1}) ∈ V0
  | 0 => empty_mem_V0
  | n + 1 => single_mem_V0 (num_mem_V0 n)

theorem omega_mem_V0 : (omega : ZFSet.{1}) ∈ V0 :=
  mem_V0_of (fun y hy => by obtain ⟨n, rfl⟩ := mem_omega.1 hy; exact num_mem_V0 n)
    ⟨Nat, num, fun _ => mem_omega⟩

end ZFSet

end Incomplete
