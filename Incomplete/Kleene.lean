/-!
# Kleene's incompleteness argument, abstractly

Machines `C` run on inputs `I`, and `⌜c⌝ : I` is a machine's own code as an input. A proof
system proves sentences `halts c i` and `notHalts c i`. If it proves every true `halts`
sentence, never proves both of a pair, and its proofs of `notHalts c ⌜c⌝` are enumerated by a
machine `d`, then `notHalts d ⌜d⌝` is true and unprovable. If it is moreover sound for `halts`
sentences, it does not prove `halts d ⌜d⌝` either.

The diagonal is Lawvere's: `d` describes the anti-diagonal of "`c` halts on `⌜c⌝`", so it cannot
answer about itself.
-/

namespace Incomplete

theorem kleene {C I S : Type} (quote : C → I) (Halts : C → I → Prop) (Provable : S → Prop)
    (halts notHalts : C → I → S)
    (complete : ∀ c i, Halts c i → Provable (halts c i))
    (consistent : ∀ c i, Provable (halts c i) → Provable (notHalts c i) → False)
    (enum : ∃ d, ∀ c, Halts d (quote c) ↔ Provable (notHalts c (quote c))) :
    ∃ d, ¬Halts d (quote d) ∧ ¬Provable (notHalts d (quote d)) ∧
      ((∀ c i, Provable (halts c i) → Halts c i) → ¬Provable (halts d (quote d))) := by
  obtain ⟨d, hd⟩ := enum
  have hn : ¬Provable (notHalts d (quote d)) := fun h =>
    consistent _ _ (complete _ _ ((hd d).2 h)) h
  exact ⟨d, fun h => hn ((hd d).1 h), hn, fun sound h => hn ((hd d).1 (sound _ _ h))⟩

end Incomplete
