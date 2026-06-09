import Goldfish.Basic
import Goldfish.Protocol
import Goldfish.Axioms
import Goldfish.Ledger
import Goldfish.SynchronousSecurity
import Goldfish.FastConfirmation

/-!
# Goldfish

Machine-checked formalization of the *Goldfish* Ethereum consensus protocol
(IACR ePrint 2022/1171). See `docs/formalization-strategy.md` for the proof
discipline (`axiom` / hypothesis threading, never `sorry`) and the dependency
graph; each numbered statement is tracked by a GitHub issue.

* `Goldfish.Basic` — block-tree prefix order, `(γ,τ)`-compliance, negligibility.
* `Goldfish.Protocol` — the abstract `Execution` data and `Spec` interface.
* `Goldfish.Axioms` — probabilistic good events (Lem. 1 / 4, Prop. 1).
* `Goldfish.Ledger` — the confirmed-ledger layer (`ch^id_r`, Def. 1 safety/liveness).
* `Goldfish.SynchronousSecurity` — synchronous security, paper App. B: Lem. 2–3,
  Thm. 1–3 under `(1/2, 3∆)`-compliance.
-/
