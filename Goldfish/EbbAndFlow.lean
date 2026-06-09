import Goldfish.EbbAndFlow.Basic
import Goldfish.EbbAndFlow.GadgetSpec
import Goldfish.EbbAndFlow.External
import Goldfish.EbbAndFlow.Proposition2
import Goldfish.EbbAndFlow.Proposition4
import Goldfish.EbbAndFlow.Lemma6
import Goldfish.EbbAndFlow.Healing
import Goldfish.EbbAndFlow.Theorem7

/-!
# Partial synchrony / ebb-and-flow (paper App. D)

The accountability-gadget overlay giving Goldfish its ebb-and-flow property
(Def. 4) under `(1/3, 3∆)`-compliance in the partially synchronous sleepy model:
Propositions 2–5, Lemmas 6–9 and Theorem 7.

* `Goldfish.EbbAndFlow.Basic` — the `Gadget` interface (`ch_acc`/`ch_ava`
  ledgers, checkpoints, iterations, partial-synchrony times) and the
  safe/live-after-`R` security predicates.
* `Goldfish.EbbAndFlow.External` — external [61] accountability-gadget axioms,
  including the imported Propositions 3 and 5.
-/
