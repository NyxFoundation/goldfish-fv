import Goldfish.Basic
import Goldfish.Protocol
import Goldfish.Axioms
import Goldfish.Ledger
import Goldfish.SynchronousSecurity
import Goldfish.FastConfirmation
import Goldfish.EbbAndFlow
import Goldfish.Probabilistic

/-!
# Goldfish

Machine-checked formalization of the *Goldfish* Ethereum consensus protocol
(IACR ePrint 2022/1171). See `README.md` for the proof
discipline (`axiom` / hypothesis threading, never `sorry`) and the dependency
graph.

* `Goldfish.Basic` — block-tree prefix order, `(γ,τ)`-compliance, negligibility.
* `Goldfish.Protocol` — the abstract `Execution` data and `Spec` interface.
* `Goldfish.Axioms` — probabilistic good events (Lem. 1 / 4, Prop. 1).
* `Goldfish.Ledger` — the confirmed-ledger layer (`ch^id_r`, Def. 1 safety/liveness).
* `Goldfish.SynchronousSecurity` — synchronous security, paper App. B: Lem. 2–3,
  Thm. 1–3 under `(1/2, 3∆)`-compliance.
* `Goldfish.FastConfirmation` — fast confirmation, paper App. C: Lem. 5, Thm. 4–6
  under `(1/2, 4∆)`-compliance.
* `Goldfish.EbbAndFlow` — partial synchrony / ebb-and-flow, paper App. D: Prop. 2–5,
  Lem. 6–9, Thm. 7 under `(1/3, 3∆)`-compliance with the accountability gadget.
* `Goldfish.Probabilistic` — measure-theoretic foundation (paper App. G) for
  replacing the good-event axioms: the `Lottery` model and the
  Chernoff/Hoeffding honest-majority concentration bound.
-/
