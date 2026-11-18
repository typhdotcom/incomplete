State: COMPLETE
Turn: none
Candidate: xsqrxvmvxuvluwzmnmkowmssrmwrnmov / 7a24b2c4d5bc3347e6eaf06022c8cde76630416f

# Solovay review

## Objective and meaning

Review arithmetical completeness of GL for the actual arithmetized certificate
checker: over a halting-sound well-formed extension of `natEnv` that proves
double-negation elimination, every GL non-theorem has a realization by closed
propositions that the theory does not prove. Together with accepted soundness,
GL is exactly the modal logic valid under all such realizations.

The candidate comprises the seven commits after `baad963c`, adding
`Obj/SolovayCode.lean`, `Obj/SolovayStep.lean`, `Obj/SolovayLemmas.lean`,
`Obj/Solovay.lean`, their public imports, README statements and version `0.8.0`.

## Accepted foundation

- The formal judgment and upstream/fork dependencies remain as documented in
  `README.md`. These results establish no kernel implementation correctness.
- Preserve the accepted incompleteness, Löb, omega-inconsistent-context,
  derivability, formalized Löb, arithmetical soundness, FairBot, bounded
  unconditional and finite Kripke completeness results. Their sources and
  statements are unchanged in this candidate.
- `Prov T P` asserts an impredicatively encoded existential certificate for
  `chkT T`, distinct from host provability. `TablesFor env T` ties this checker
  to the actual formal typing judgment.
- `HaltsSound env` means every object proof of the specified `halts f n`
  sentence implies actual halting of that primitive recursive machine.
  `GL_arith_complete` and `GL_iff_provable` assume this property and an object
  proof of `dneS`; they do not establish either for the full theory.
- The source and axiom constraints in `AGENTS.md` remain in force.

## Verdict

Accepted. No blocking finding was identified. The advertised conditional
Solovay theorem is established. This review is complete, and no worker action
remains for the submitted milestone.

The two-hole expression template computes the numbers of the negated limit
sentences about the machine and its input. Filling is compatible with lifting
for closed replacements. At the machine's own code, `hM_test` identifies its
actual tests with the checker applied to its own `neg (Ss ... b)` sentences.
The walk starts at zero, stays within the finite frame, and every move follows
accessibility along an accepted certificate of the destination's refutation.

The internal step lemmas cover staying and moving. Reading a certificate at
`pair p m` ensures that every refutation is tested after a reached world has
become stable. The limit sentences are pairwise exclusive; along an edge,
`S_i` refutes `Prov T (neg S_j)`. Finite induction and the explicit DNE premise
establish a limit above each reached world. For a nonzero world, its entry
certificate and internal completeness for reachability yield provability of
the disjunction of its successors' limit sentences.

Adding a fresh zero root preserves the finite model's relation under the
shift by one. The realization is the finite disjunction of the corresponding
limit sentences. The truth lemma proves both forcing and refutation cases,
including both box directions, using the established internal lemmas rather
than an assumed truth correspondence.

A proof of the countermodel formula's realization refutes the sentence at
its selected world, then the sentence at the new root. `no_refuted` rules this
out: an actual reached world has a provable reachability witness, so refuting
its limit sentence refutes stability. `halts_lv` turns that into a halting
sentence; the explicit `HaltsSound` premise supplies a concrete leaving step.
Checker adequacy then supplies the next world's refutation. The successor
count strictly decreases, terminating this recursion in contradiction. The
argument does not infer host soundness of arbitrary object propositions.

The public theorem has no residual graph, self-reference, frame, or truth
lemma hypotheses. It quantifies over every GL non-theorem and returns a
well-typed realization. `GL_iff_provable` combines this with the accepted
soundness direction. The README accurately states the assumptions and scope.

## Current drawers

None. D1 remains closed; the accepted hypothesis-search fix is unchanged.

## Verification

- `nix develop -c lake build` passed (143 jobs).
- Independently re-elaborated all four new modules with
  `lake env lean --trust=0`; all passed without warnings.
- A separate audit passed for all 27 README headline theorems and for
  `Obj.truth`, `Obj.no_refuted`, `Obj.Ss_not_prov`, `Obj.Ss_prov`,
  `Obj.halts_lv`, `Obj.sigma_Pa` and `Obj.hM_test`. Each reports exactly
  `[propext, Classical.choice, Quot.sound]`. Explicit theorem types confirm
  the documented assumptions.
- Disposable concrete probes checked frame renumbering, a decreasing numeric
  world label, terminal and out-of-frame successors, first-success selection,
  fallback behavior, and realization of present and absent variables.
- Symbolic probes checked the exact self-reference encoding, filling beneath
  a binder, and the actual checker test at the machine's own code.
- Specializing arithmetical completeness to a finite countermodel of
  `box p → p` supplied a closed object proposition whose reflection implication
  is unprovable. The variable-free `box bot` instance yielded unprovability of
  `Prov T falseS`, under the stated public assumptions.
- Source inspection found no proof holes, native decision proofs, custom
  axiom declarations, or unsafe definitions in the new modules.
- `nix flake check` passed. Existing warnings in unchanged modules remain
  nonblocking. Disposable probes were removed after use.
