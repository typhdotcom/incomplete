/-!
# Well-founded sets

`ZFSet.{u}` is the type of sets whose members are indexed by types in `Type u`, up to
extensional equality: the quotient of well-founded trees `PSet.{u}` by bisimilarity. A set is
`ofFn f` for its members `f`, and the constructions the model of the object theory uses
(pairs, unions, separation, power sets, functions as sets of pairs, dependent products) are
built that way.
-/

namespace Incomplete

universe u

attribute [local instance] Classical.propDecidable

inductive PSet : Type (u + 1)
  | mk (α : Type u) (A : α → PSet)

namespace PSet

def Ty : PSet.{u} → Type u | mk α _ => α
def Fn : (x : PSet.{u}) → x.Ty → PSet.{u} | mk _ A => A

def Equiv (x y : PSet.{u}) : Prop :=
  PSet.rec (motive := fun _ => PSet.{u} → Prop)
    (fun _ _ eqv y => match y with
      | mk _ B => (∀ a, ∃ b, eqv a (B b)) ∧ (∀ b, ∃ a, eqv a (B b))) x y

theorem equiv_mk {α β : Type u} {A : α → PSet.{u}} {B : β → PSet.{u}} :
    Equiv (mk α A) (mk β B) ↔ (∀ a, ∃ b, Equiv (A a) (B b)) ∧ (∀ b, ∃ a, Equiv (A a) (B b)) :=
  Iff.rfl

theorem Equiv.refl (x : PSet.{u}) : Equiv x x := by
  induction x with
  | mk α A ih => exact equiv_mk.2 ⟨fun a => ⟨a, ih a⟩, fun a => ⟨a, ih a⟩⟩

theorem Equiv.euc {x : PSet.{u}} : ∀ {y z : PSet.{u}}, Equiv x y → Equiv z y → Equiv x z := by
  induction x with
  | mk α A ih =>
    intro y z h1 h2
    obtain ⟨β, B⟩ := y; obtain ⟨γ, C⟩ := z
    obtain ⟨αβ, βα⟩ := equiv_mk.1 h1; obtain ⟨γβ, βγ⟩ := equiv_mk.1 h2
    refine equiv_mk.2 ⟨fun a => ?_, fun c => ?_⟩
    · obtain ⟨b, ab⟩ := αβ a; obtain ⟨c, cb⟩ := βγ b; exact ⟨c, ih a ab cb⟩
    · obtain ⟨b, cb⟩ := γβ c; obtain ⟨a, ab⟩ := βα b; exact ⟨a, ih a ab cb⟩

theorem Equiv.symm {x y : PSet.{u}} (h : Equiv x y) : Equiv y x := (Equiv.refl y).euc h

theorem Equiv.trans {x y z : PSet.{u}} (h1 : Equiv x y) (h2 : Equiv y z) : Equiv x z :=
  h1.euc h2.symm

instance setoid : Setoid PSet.{u} := ⟨Equiv, Equiv.refl, Equiv.symm, Equiv.trans⟩

def Mem (y x : PSet.{u}) : Prop := ∃ b, Equiv x (y.Fn b)

theorem Mem.congr_left {x x' y : PSet.{u}} (h : Equiv x x') : Mem y x → Mem y x'
  | ⟨b, hb⟩ => ⟨b, h.symm.trans hb⟩

theorem Mem.congr_right {x y y' : PSet.{u}} (h : Equiv y y') : Mem y x → Mem y' x := by
  obtain ⟨β, B⟩ := y; obtain ⟨γ, C⟩ := y'
  rintro ⟨b, hb⟩
  obtain ⟨c, hc⟩ := (equiv_mk.1 h).1 b
  exact ⟨c, hb.trans hc⟩

theorem ext {x y : PSet.{u}} (h : ∀ z, Mem x z ↔ Mem y z) : Equiv x y := by
  obtain ⟨α, A⟩ := x; obtain ⟨β, B⟩ := y
  refine equiv_mk.2 ⟨fun a => ?_, fun b => ?_⟩
  · obtain ⟨b, hb⟩ := (h (A a)).1 ⟨a, Equiv.refl _⟩; exact ⟨b, hb⟩
  · obtain ⟨a, ha⟩ := (h (B b)).2 ⟨b, Equiv.refl _⟩; exact ⟨a, ha.symm⟩

end PSet

def ZFSet : Type (u + 1) := Quotient PSet.setoid.{u}

namespace ZFSet

def mk (x : PSet.{u}) : ZFSet.{u} := Quotient.mk _ x

theorem mk_eq {x y : PSet.{u}} : mk x = mk y ↔ PSet.Equiv x y :=
  ⟨Quotient.exact, fun h => Quotient.sound h⟩

noncomputable def out (x : ZFSet.{u}) : PSet.{u} := Classical.choose (Quotient.exists_rep x)

theorem mk_out (x : ZFSet.{u}) : mk x.out = x := Classical.choose_spec (Quotient.exists_rep x)

def Mem (x y : ZFSet.{u}) : Prop :=
  Quotient.liftOn₂ x y (fun a b => PSet.Mem a b) fun _ _ _ _ h1 h2 =>
    propext ⟨fun h => (h.congr_right h1).congr_left h2,
      fun h => (h.congr_right (Setoid.symm h1)).congr_left (Setoid.symm h2)⟩

instance : Membership ZFSet.{u} ZFSet.{u} := ⟨Mem⟩

theorem mem_mk {x y : PSet.{u}} : mk y ∈ mk x ↔ PSet.Mem x y := Iff.rfl

theorem ext {x y : ZFSet.{u}} (h : ∀ z, z ∈ x ↔ z ∈ y) : x = y := by
  induction x using Quotient.inductionOn with | h a =>
  induction y using Quotient.inductionOn with | h b =>
  exact Quotient.sound (PSet.ext fun z => h (mk z))

/-- The index type of `x`'s members, and its members. -/
noncomputable def Idx (x : ZFSet.{u}) : Type u := x.out.Ty
noncomputable def elt (x : ZFSet.{u}) (i : x.Idx) : ZFSet.{u} := mk (x.out.Fn i)

theorem mem_iff {x y : ZFSet.{u}} : y ∈ x ↔ ∃ i, y = x.elt i := by
  unfold elt Idx
  have hx := mk_out x; have hy := mk_out y
  generalize x.out = p at hx ⊢
  generalize y.out = q at hy
  subst hx hy
  show PSet.Mem p q ↔ ∃ i, mk q = mk (p.Fn i)
  simp only [mk_eq]; rfl

theorem elt_mem (x : ZFSet.{u}) (i : x.Idx) : x.elt i ∈ x := mem_iff.2 ⟨i, rfl⟩

/-- The set of the `f a`. -/
noncomputable def ofFn {α : Type u} (f : α → ZFSet.{u}) : ZFSet.{u} :=
  mk (PSet.mk α fun a => (f a).out)

theorem mem_ofFn {α : Type u} {f : α → ZFSet.{u}} {y : ZFSet.{u}} :
    y ∈ ofFn f ↔ ∃ a, y = f a := by
  have hy := mk_out y
  generalize y.out = q at hy; subst hy
  show PSet.Mem _ q ↔ _
  constructor
  · rintro ⟨a, ha⟩; exact ⟨a, by rw [← mk_out (f a)]; exact mk_eq.2 ha⟩
  · rintro ⟨a, ha⟩; exact ⟨a, mk_eq.1 (ha.trans (mk_out (f a)).symm)⟩

/-! ### Constructions -/

noncomputable def empty : ZFSet.{u} := ofFn (PEmpty.elim : PEmpty.{u + 1} → ZFSet.{u})

@[simp] theorem not_mem_empty (y : ZFSet.{u}) : ¬y ∈ empty := by
  rw [empty, mem_ofFn]; rintro ⟨⟨⟩, _⟩

noncomputable def pair (a b : ZFSet.{u}) : ZFSet.{u} :=
  ofFn fun i : ULift.{u} Bool => if i.down then a else b

@[simp] theorem mem_pair {a b y : ZFSet.{u}} : y ∈ pair a b ↔ y = a ∨ y = b := by
  rw [pair, mem_ofFn]
  constructor
  · rintro ⟨⟨_ | _⟩, h⟩ <;> simp_all
  · rintro (h | h)
    · exact ⟨⟨true⟩, by simp [h]⟩
    · exact ⟨⟨false⟩, by simp [h]⟩

noncomputable def single (a : ZFSet.{u}) : ZFSet.{u} := pair a a

@[simp] theorem mem_single {a y : ZFSet.{u}} : y ∈ single a ↔ y = a := by simp [single]

noncomputable def sUnion (x : ZFSet.{u}) : ZFSet.{u} :=
  ofFn fun p : Σ i : x.Idx, (x.elt i).Idx => (x.elt p.1).elt p.2

@[simp] theorem mem_sUnion {x y : ZFSet.{u}} : y ∈ sUnion x ↔ ∃ z ∈ x, y ∈ z := by
  rw [sUnion, mem_ofFn]
  constructor
  · rintro ⟨⟨i, j⟩, rfl⟩; exact ⟨_, elt_mem _ _, elt_mem _ _⟩
  · rintro ⟨z, hz, hy⟩
    obtain ⟨i, rfl⟩ := mem_iff.1 hz
    obtain ⟨j, rfl⟩ := mem_iff.1 hy
    exact ⟨⟨i, j⟩, rfl⟩

noncomputable def sep (x : ZFSet.{u}) (P : ZFSet.{u} → Prop) : ZFSet.{u} :=
  ofFn fun i : {i : x.Idx // P (x.elt i)} => x.elt i.1

@[simp] theorem mem_sep {x y : ZFSet.{u}} {P : ZFSet.{u} → Prop} :
    y ∈ sep x P ↔ y ∈ x ∧ P y := by
  rw [sep, mem_ofFn]
  constructor
  · rintro ⟨⟨i, hi⟩, rfl⟩; exact ⟨elt_mem _ _, hi⟩
  · rintro ⟨hy, hp⟩
    obtain ⟨i, rfl⟩ := mem_iff.1 hy
    exact ⟨⟨i, hp⟩, rfl⟩

noncomputable def powerset (x : ZFSet.{u}) : ZFSet.{u} :=
  ofFn fun S : x.Idx → Prop => ofFn fun i : {i // S i} => x.elt i.1

@[simp] theorem mem_powerset {x y : ZFSet.{u}} : y ∈ powerset x ↔ ∀ z ∈ y, z ∈ x := by
  rw [powerset, mem_ofFn]
  constructor
  · rintro ⟨S, rfl⟩ z hz
    obtain ⟨⟨i, _⟩, rfl⟩ := mem_ofFn.1 hz
    exact elt_mem _ _
  · intro h
    refine ⟨fun i => x.elt i ∈ y, ext fun z => ?_⟩
    rw [mem_ofFn]
    constructor
    · intro hz
      obtain ⟨i, rfl⟩ := mem_iff.1 (h z hz)
      exact ⟨⟨i, hz⟩, rfl⟩
    · rintro ⟨⟨i, hi⟩, rfl⟩; exact hi

/-! ### Ordered pairs -/

noncomputable def kpair (a b : ZFSet.{u}) : ZFSet.{u} := pair (single a) (pair a b)

theorem single_eq_single {a b : ZFSet.{u}} (h : single a = single b) : a = b := by
  have : a ∈ single b := h ▸ mem_single.2 rfl
  exact mem_single.1 this

theorem single_eq_pair {a b c : ZFSet.{u}} (h : single a = pair b c) : b = a ∧ c = a := by
  have hb : b ∈ single a := h ▸ mem_pair.2 (.inl rfl)
  have hc : c ∈ single a := h ▸ mem_pair.2 (.inr rfl)
  exact ⟨mem_single.1 hb, mem_single.1 hc⟩

theorem kpair_inj {a b c d : ZFSet.{u}} (h : kpair a b = kpair c d) : a = c ∧ b = d := by
  have h1 : single a ∈ kpair c d := h ▸ mem_pair.2 (.inl rfl)
  have hac : a = c := by
    rcases mem_pair.1 h1 with h1 | h1
    · exact single_eq_single h1
    · exact ((single_eq_pair h1).1).symm
  refine ⟨hac, ?_⟩
  rw [← hac] at h
  have h2 : pair a b ∈ kpair a d := h ▸ mem_pair.2 (.inr rfl)
  have h3 : pair a d ∈ kpair a b := h ▸ mem_pair.2 (.inr rfl)
  by_cases hb : b = a
  · subst hb
    rcases mem_pair.1 h3 with h3 | h3
    · exact ((single_eq_pair h3.symm).2).symm
    · exact ((single_eq_pair h3.symm).2).symm
  · rcases mem_pair.1 h2 with h2 | h2
    · exact absurd (single_eq_pair h2.symm).2 hb
    · have hd : b ∈ pair a d := h2 ▸ mem_pair.2 (.inr rfl)
      rcases mem_pair.1 hd with hd | hd
      · exact absurd hd hb
      · exact hd

/-! ### Functions as sets of pairs -/

/-- The function `x ↦ f x` on `A`, as the set of pairs `(x, y)` with `y ∈ f x`: a function
into propositions is empty. -/
noncomputable def lam (A : ZFSet.{u}) (f : ZFSet.{u} → ZFSet.{u}) : ZFSet.{u} :=
  ofFn fun p : Σ i : A.Idx, (f (A.elt i)).Idx => kpair (A.elt p.1) ((f (A.elt p.1)).elt p.2)

theorem mem_lam {A z : ZFSet.{u}} {f : ZFSet.{u} → ZFSet.{u}} :
    z ∈ lam A f ↔ ∃ x ∈ A, ∃ y ∈ f x, z = kpair x y := by
  rw [lam, mem_ofFn]
  constructor
  · rintro ⟨⟨i, j⟩, rfl⟩; exact ⟨_, elt_mem _ _, _, elt_mem _ _, rfl⟩
  · rintro ⟨x, hx, y, hy, rfl⟩
    obtain ⟨i, rfl⟩ := mem_iff.1 hx
    obtain ⟨j, rfl⟩ := mem_iff.1 hy
    exact ⟨⟨i, j⟩, rfl⟩

theorem lam_congr {A : ZFSet.{u}} {f g : ZFSet.{u} → ZFSet.{u}} (h : ∀ x ∈ A, f x = g x) :
    lam A f = lam A g :=
  ext fun z => by
    simp only [mem_lam]
    exact ⟨fun ⟨x, hx, y, hy, e⟩ => ⟨x, hx, y, h x hx ▸ hy, e⟩,
      fun ⟨x, hx, y, hy, e⟩ => ⟨x, hx, y, (h x hx).symm ▸ hy, e⟩⟩

/-- Application: the `y` with `(x, y) ∈ F`. -/
noncomputable def app (F x : ZFSet.{u}) : ZFSet.{u} := sep (sUnion (sUnion F)) fun y => kpair x y ∈ F

theorem mem_app {F x y : ZFSet.{u}} : y ∈ app F x ↔ kpair x y ∈ F := by
  rw [app, mem_sep]
  refine ⟨And.right, fun h => ⟨?_, h⟩⟩
  exact mem_sUnion.2 ⟨pair x y, mem_sUnion.2 ⟨kpair x y, h, mem_pair.2 (.inr rfl)⟩,
    mem_pair.2 (.inr rfl)⟩

theorem app_lam {A x : ZFSet.{u}} {f : ZFSet.{u} → ZFSet.{u}} (hx : x ∈ A) :
    app (lam A f) x = f x :=
  ext fun y => by
    rw [mem_app, mem_lam]
    constructor
    · rintro ⟨x', _, y', hy', e⟩
      obtain ⟨rfl, rfl⟩ := kpair_inj e
      exact hy'
    · intro hy; exact ⟨x, hx, y, hy, rfl⟩

/-- The dependent product: the functions on `A` with values in `B`. -/
noncomputable def pi (A : ZFSet.{u}) (B : ZFSet.{u} → ZFSet.{u}) : ZFSet.{u} :=
  ofFn fun g : (i : A.Idx) → (B (A.elt i)).Idx => lam A fun x =>
    if h : ∃ i, A.elt i = x then (B (A.elt h.choose)).elt (g h.choose) else empty

theorem mem_pi {A F : ZFSet.{u}} {B : ZFSet.{u} → ZFSet.{u}} :
    F ∈ pi A B ↔ ∃ f : ZFSet.{u} → ZFSet.{u}, (∀ x ∈ A, f x ∈ B x) ∧ F = lam A f := by
  rw [pi, mem_ofFn]
  constructor
  · rintro ⟨g, rfl⟩
    refine ⟨_, fun x hx => ?_, rfl⟩
    have h : ∃ i, A.elt i = x := (mem_iff.1 hx).imp fun _ e => e.symm
    rw [dif_pos h]
    have key : ∀ y, y = x → ∀ j : (B y).Idx, (B y).elt j ∈ B x := by
      intro y hy j; subst hy; exact elt_mem _ _
    exact key _ h.choose_spec _
  · rintro ⟨f, hf, rfl⟩
    have hi : ∀ i, ∃ j, f (A.elt i) = (B (A.elt i)).elt j := fun i =>
      mem_iff.1 (hf _ (elt_mem _ _))
    refine ⟨fun i => (hi i).choose, lam_congr fun x hx => ?_⟩
    have h : ∃ i, A.elt i = x := (mem_iff.1 hx).imp fun _ e => e.symm
    rw [dif_pos h, ← (hi h.choose).choose_spec, h.choose_spec]

theorem app_mem_pi {A F x : ZFSet.{u}} {B : ZFSet.{u} → ZFSet.{u}} (hF : F ∈ pi A B)
    (hx : x ∈ A) : app F x ∈ B x := by
  obtain ⟨f, hf, rfl⟩ := mem_pi.1 hF
  rw [app_lam hx]; exact hf x hx

theorem lam_app_of_mem_pi {A F : ZFSet.{u}} {B : ZFSet.{u} → ZFSet.{u}} (hF : F ∈ pi A B) :
    lam A (app F) = F := by
  obtain ⟨f, _, rfl⟩ := mem_pi.1 hF
  exact lam_congr fun x hx => app_lam hx

theorem lam_mem_pi {A : ZFSet.{u}} {B f : ZFSet.{u} → ZFSet.{u}} (hf : ∀ x ∈ A, f x ∈ B x) :
    lam A f ∈ pi A B := mem_pi.2 ⟨f, hf, rfl⟩

theorem pi_congr {A : ZFSet.{u}} {B B' : ZFSet.{u} → ZFSet.{u}} (h : ∀ x ∈ A, B x = B' x) :
    pi A B = pi A B' :=
  ext fun F => by
    simp only [mem_pi]
    exact ⟨fun ⟨f, hf, e⟩ => ⟨f, fun x hx => h x hx ▸ hf x hx, e⟩,
      fun ⟨f, hf, e⟩ => ⟨f, fun x hx => (h x hx).symm ▸ hf x hx, e⟩⟩

/-! ### Truth values -/

/-- The propositions: `empty` is false and `single empty` true; a proof is `empty`. -/
noncomputable def two : ZFSet.{u} := pair empty (single empty)

theorem mem_two {p : ZFSet.{u}} : p ∈ two ↔ p = empty ∨ p = single empty := mem_pair

theorem proof_eq {p h : ZFSet.{u}} (hp : p ∈ two) (hh : h ∈ p) : h = empty := by
  rcases mem_two.1 hp with rfl | rfl
  · exact absurd hh (not_mem_empty _)
  · exact mem_single.1 hh

theorem lam_eq_empty {A : ZFSet.{u}} {f : ZFSet.{u} → ZFSet.{u}} (h : ∀ x ∈ A, f x = empty) :
    lam A f = empty :=
  ext fun z => by
    simp only [mem_lam, not_mem_empty, iff_false]
    rintro ⟨x, hx, y, hy, -⟩
    rw [h x hx] at hy; exact not_mem_empty _ hy

/-- **Impredicativity**: a product of propositions is a proposition. -/
theorem pi_mem_two {A : ZFSet.{u}} {B : ZFSet.{u} → ZFSet.{u}} (h : ∀ x ∈ A, B x ∈ two) :
    pi A B ∈ two := by
  by_cases hall : ∀ x ∈ A, empty ∈ B x
  · refine mem_two.2 (.inr (ext fun F => ?_))
    rw [mem_single, mem_pi]
    constructor
    · rintro ⟨f, hf, rfl⟩; exact lam_eq_empty fun x hx => proof_eq (h x hx) (hf x hx)
    · rintro rfl
      exact ⟨fun _ => empty, hall, (lam_eq_empty fun _ _ => rfl).symm⟩
  · refine mem_two.2 (.inl (ext fun F => ?_))
    simp only [not_mem_empty, iff_false, mem_pi]
    rintro ⟨f, hf, -⟩
    refine hall fun x hx => ?_
    have := hf x hx
    rwa [proof_eq (h x hx) this] at this

theorem pi_eq_single_empty {A : ZFSet.{u}} {B : ZFSet.{u} → ZFSet.{u}} (h : ∀ x ∈ A, B x ∈ two)
    (hP : empty ∈ pi A B) : ∀ x ∈ A, empty ∈ B x := by
  intro x hx
  have := app_mem_pi hP hx
  rwa [show app empty x = empty from ext fun y => by simp [mem_app]] at this

/-! ### Numerals -/

noncomputable def num : Nat → ZFSet.{u}
  | 0 => empty
  | n + 1 => single (num n)

theorem num_inj : ∀ {m n : Nat}, (num m : ZFSet.{u}) = num n → m = n
  | 0, 0, _ => rfl
  | 0, n + 1, h => absurd (h ▸ mem_single.2 rfl : num n ∈ (num 0 : ZFSet.{u})) (not_mem_empty _)
  | m + 1, 0, h => absurd (h ▸ mem_single.2 rfl : num m ∈ (num 0 : ZFSet.{u})) (not_mem_empty _)
  | m + 1, n + 1, h => congrArg (· + 1) (num_inj (single_eq_single h))

noncomputable def omega : ZFSet.{u} := ofFn fun n : ULift.{u} Nat => num n.down

theorem mem_omega {x : ZFSet.{u}} : x ∈ omega ↔ ∃ n, x = num n := by
  rw [omega, mem_ofFn]
  exact ⟨fun ⟨n, h⟩ => ⟨n.down, h⟩, fun ⟨n, h⟩ => ⟨⟨n⟩, h⟩⟩

theorem num_mem_omega (n : Nat) : (num n : ZFSet.{u}) ∈ omega := mem_omega.2 ⟨n, rfl⟩

end ZFSet

end Incomplete
