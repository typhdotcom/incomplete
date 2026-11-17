import Incomplete.ZFUniv
import Incomplete.BSigma

/-!
# A set model of `natEnv` at `Prop` and `Type`

`interp ζ e ρ` is the set `e` denotes at the level values `ζ` and the values `ρ` of its free
variables: `Prop` is `two`, `Type` is the universe `V0`, a sort above is empty; `Nat` is `omega`,
`λ` and `∀` are `lam` and `pi`, and `Nat.rec` is recursion on the numeral's value. Lifting,
substitution and level instantiation commute with it.
-/

namespace Lean4Lean.Incomplete
open VExpr ZFSet

attribute [local instance] Classical.propDecidable

abbrev ZS := ZFSet.{1}

noncomputable def univ : Nat → ZS
  | 0 => two
  | 1 => V0
  | _ => empty

def zcons (x : ZS) (ρ : Nat → ZS) : Nat → ZS
  | 0 => x
  | i + 1 => ρ i

@[simp] theorem zcons_zero (x : ZS) (ρ : Nat → ZS) : zcons x ρ 0 = x := rfl
@[simp] theorem zcons_succ (x : ZS) (ρ : Nat → ZS) (i : Nat) : zcons x ρ (i + 1) = ρ i := rfl

noncomputable def natOf (n : ZS) : Nat := if h : ∃ k, n = num k then h.choose else 0

theorem natOf_num (k : Nat) : natOf (num k : ZS) = k := by
  have h : ∃ j, (num k : ZS) = num j := ⟨k, rfl⟩
  rw [natOf, dif_pos h]; exact (num_inj h.choose_spec).symm

noncomputable def recN (z s : ZS) : Nat → ZS
  | 0 => z
  | k + 1 => app (app s (num k)) (recN z s k)

noncomputable def succV : ZS := lam omega single

theorem app_succV {n : ZS} (hn : n ∈ omega) : app succV n = single n := app_lam hn

noncomputable def recV (u : Nat) : ZS :=
  lam (pi omega fun _ => univ u) fun M =>
  lam (app M (num 0)) fun z =>
  lam (pi omega fun n => pi (app M n) fun _ => app M (app succV n)) fun s =>
  lam omega fun n => recN z s (natOf n)

noncomputable def constV (c : Lean.Name) (ls : List Nat) : ZS :=
  if c = ``Nat then omega else if c = ``Nat.zero then num 0 else if c = ``Nat.succ then succV
  else if c = ``Nat.rec then recV (ls.headD 0) else empty

noncomputable def interp (ζ : List Nat) : VExpr → (Nat → ZS) → ZS
  | .bvar i, ρ => ρ i
  | .sort l, _ => univ (l.eval ζ)
  | .const c ls, _ => constV c (ls.map (VLevel.eval ζ))
  | .app f a, ρ => app (interp ζ f ρ) (interp ζ a ρ)
  | .lam A b, ρ => lam (interp ζ A ρ) fun x => interp ζ b (zcons x ρ)
  | .forallE A B, ρ => pi (interp ζ A ρ) fun x => interp ζ B (zcons x ρ)
  | .proj .., _ => empty

section
variable {ζ : List Nat}

theorem interp_liftN (n : Nat) : ∀ (e : VExpr) (k : Nat) (ρ : Nat → ZS),
    interp ζ (e.liftN n k) ρ = interp ζ e fun i => ρ (liftVar n i k)
  | .bvar i, k, ρ => rfl
  | .sort _, _, _ | .const .., _, _ | .proj .., _, _ => rfl
  | .app f a, k, ρ => by simp only [liftN, interp, interp_liftN n f, interp_liftN n a]
  | .lam A b, k, ρ | .forallE A b, k, ρ => by
    simp only [liftN, interp, interp_liftN n A, interp_liftN n b]
    congr 1; funext x; congr 1; funext i
    cases i <;> simp [liftVar_zero, liftVar_succ]

theorem interp_lift (e : VExpr) (x : ZS) (ρ : Nat → ZS) :
    interp ζ e.lift (zcons x ρ) = interp ζ e ρ := by
  rw [VExpr.lift, interp_liftN]; congr 1; funext i; simp [liftVar, Nat.add_comm 1 i]

theorem interp_subst : ∀ (e : VExpr) (σ : Subst) (ρ : Nat → ZS),
    interp ζ (e.subst σ) ρ = interp ζ e fun i => interp ζ (σ i) ρ
  | .bvar i, σ, ρ => rfl
  | .sort _, _, _ | .const .., _, _ | .proj .., _, _ => rfl
  | .app f a, σ, ρ => by simp only [subst, interp, interp_subst f, interp_subst a]
  | .lam A b, σ, ρ | .forallE A b, σ, ρ => by
    simp only [subst, interp, interp_subst A, interp_subst b]
    congr 1; funext x; congr 1; funext i
    cases i with
    | zero => rfl
    | succ i => exact interp_lift _ _ _

theorem interp_inst (e a : VExpr) (ρ : Nat → ZS) :
    interp ζ (e.inst a) ρ = interp ζ e (zcons (interp ζ a ρ) ρ) := by
  rw [inst_eq, interp_subst]; congr 1; funext i
  cases i <;> rfl

theorem interp_instL (ls : List VLevel) : ∀ (e : VExpr) (ρ : Nat → ZS),
    interp ζ (e.instL ls) ρ = interp (ls.map (VLevel.eval ζ)) e ρ
  | .bvar _, _ | .proj .., _ => rfl
  | .sort l, _ => by simp only [instL, interp, VLevel.eval_inst]
  | .const c us, _ => by simp only [instL, interp, List.map_map]; congr 2; funext l
                         exact VLevel.eval_inst
  | .app f a, ρ => by simp only [instL, interp, interp_instL ls f, interp_instL ls a]
  | .lam A b, ρ | .forallE A b, ρ => by
    simp only [instL, interp, interp_instL ls A, interp_instL ls b]

end

/-! ### The constants -/

@[simp] theorem interp_nat {ζ ρ} : interp ζ nat ρ = omega := by simp [interp, nat, constV]
@[simp] theorem interp_zero {ζ ρ} : interp ζ zero ρ = num 0 := by simp [interp, zero, constV]
@[simp] theorem interp_succ {ζ ρ} : interp ζ succ ρ = succV := by simp [interp, succ, constV]

theorem interp_lit {ζ ρ} : ∀ n, interp ζ (lit n) ρ = num n
  | 0 => interp_zero
  | n + 1 => by
    simp only [lit, interp, interp_succ, interp_lit n]
    exact app_succV (num_mem_omega n)

theorem succV_mem : succV ∈ pi omega fun _ => omega :=
  lam_mem_pi fun x hx => by
    obtain ⟨n, rfl⟩ := mem_omega.1 hx; exact num_mem_omega (n + 1)

theorem recN_mem {M z s : ZS} (hz : z ∈ app M (num 0))
    (hs : s ∈ pi omega fun n => pi (app M n) fun _ => app M (app succV n)) :
    ∀ k, recN z s k ∈ app M (num k)
  | 0 => hz
  | k + 1 => by
    have h1 := app_mem_pi hs (num_mem_omega k)
    have h2 := app_mem_pi h1 (recN_mem hz hs k)
    rwa [app_succV (num_mem_omega k)] at h2

/-- The type of `Nat.rec` at `u`, as a set. -/
noncomputable def recTyV (u : Nat) : ZS :=
  pi (pi omega fun _ => univ u) fun M =>
  pi (app M (num 0)) fun _ =>
  pi (pi omega fun n => pi (app M n) fun _ => app M (app succV n)) fun _ =>
  pi omega fun n => app M n

theorem interp_recTy (u : Nat) (ρ : Nat → ZS) : interp [u] recTy ρ = recTyV u := by
  simp [recTy, motiveTy, zeroTy, succTy, interp, recTyV, VLevel.eval, constV, nat, zero, succ]

theorem recV_mem (u : Nat) : recV u ∈ recTyV u := by
  refine lam_mem_pi fun M hM => lam_mem_pi fun z hz => lam_mem_pi fun s hs =>
    lam_mem_pi fun n hn => ?_
  obtain ⟨k, rfl⟩ := mem_omega.1 hn
  rw [natOf_num]; exact recN_mem hz hs k

theorem recV_app {u : Nat} {M z s n : ZS} (hM : M ∈ pi omega fun _ => univ u)
    (hz : z ∈ app M (num 0)) (hs : s ∈ pi omega fun n => pi (app M n) fun _ => app M (app succV n))
    (hn : n ∈ omega) : app (app (app (app (recV u) M) z) s) n = recN z s (natOf n) := by
  rw [recV, app_lam hM, app_lam hz, app_lam hs, app_lam hn]

end Lean4Lean.Incomplete
