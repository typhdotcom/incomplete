State: COMPLETE
Turn: none
Candidate: xoxunolxrqqpppyutwzzqrwmtuxsvkwt / 455a5958306bfead092ff9b68bb79b41e030455e

# Provability-logic soundness review

## Objective and meaning

Review the internal derivability conditions D2 and D3, formalized Löb,
arithmetical soundness of GL and its intuitionistic fragment, and the FairBot
corollary, for the actual arithmetized certificate checker.

The candidate comprises the three commits after `ea2463e4`, adding
`Incomplete/Obj/Derivability.lean`, `Incomplete/Obj/GL.lean`, their public
imports, README statements, and version `0.6.0`. This accepts the delivered
soundness milestone toward the user's announced Solovay target. It does not
certify arithmetical completeness; the README explicitly says that result is
not proved.

## Accepted foundation

- The formal judgment and upstream/fork dependencies remain as documented in
  `README.md`. These are results about that specification; they establish no
  kernel implementation correctness.
- Preserve the accepted Gödel–Kleene, Rosser, second incompleteness, Löb,
  omega-inconsistent-context and bounded unconditional results. Their
  statements and axiom constraints are unchanged.
- `Prov T P` is the object proposition asserting an impredicatively encoded
  existential witness for `chkT T` accepting a certificate of `P`, distinct
  from the host predicate `Provable env P`.
- The full object theory is intuitionistic. Classical GL soundness explicitly
  requires `Provable env dneS`. The intuitionistic fragment, derivability
  conditions, formalized Löb and FairBot require neither this premise nor
  consistency or halting soundness.
- The source and axiom constraints in `AGENTS.md` remain in force.

## Verdict

Accepted. No blocking finding was identified. This review is complete, and
no worker action remains for the submitted milestone.

D2 combines two existential certificates using the existing internal modus
ponens construction, preserving the closed-conclusion condition. D3 supplies
the proved graph lemma for `provM` to internal completeness: a primitive
recursive transformer takes a certificate of `P` to a certificate of
`Prov T P`. Existential elimination and introduction then establish the
object implication, without extracting a host witness from a proof.

Formalized Löb applies the accepted Löb rule to
`X → Prov T P`, where `X := Prov T (Prov T P → P)`. D3 supplies `Prov T X` from
`X`, and two D2 applications establish the required reflection premise. The
public theorem matches the displayed modal Löb axiom.

The Hilbert system includes the stated propositional and modal axioms and
rules. Realizations send atoms to closed propositions, which makes the raw
`forallE` translation of implication agree with object implication. The
soundness induction handles every constructor; its DNE case uses the explicit
object-theory premise, and necessitation applies D1 only to a closed theorem.
The intuitionistic instance discharges the impossible classical case.

FairBot uses the assumed object equivalences to obtain the two implications
from provability. D3, D2 and Löb prove the first proposition, after which D1
and the other implication prove the second. Its claim is conditional on
those equivalences; it does not assert construction of programs or fixed
points. The README accurately states the public assumptions and the absence
of an arithmetical completeness result.

## Current drawers

None. D1 remains closed; the accepted hypothesis-search fix is unchanged.

## Verification

- `nix develop -c lake build` passed (135 jobs).
- Independently re-elaborated both new source modules with
  `lake env lean --trust=0`; both passed without warnings.
- A separate `lake env lean --trust=0` audit passed for all 21 README headline
  theorems, plus `Obj.sigma_prov`, `Obj.prov_mp_ctx`, `Obj.prov_prov`,
  `Obj.loeb_int`, and `Modal.deriv_sound`. Each reports exactly
  `[propext, Classical.choice, Quot.sound]`.
- Disposable probes checked explicit public hypotheses, translation of closed
  implication, the exact realization of the modal Löb axiom through both
  formalized Löb and intuitionistic soundness, and the classical DNE path.
- An independently checked terminal-world interpretation of the Hilbert
  calculus rules out derivations of bottom and `□p → p` in GL. A three-element
  Heyting-chain interpretation rules out DNE in the intuitionistic fragment,
  checking that the two calculus settings remain distinct.
- Source inspection found no proof holes, native decision proofs, custom
  axiom declarations, or unsafe definitions in the new modules.
- `nix flake check` passed. Existing warnings in unchanged modules remain
  nonblocking. Disposable probes were removed after use.
