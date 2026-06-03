import Goldfish.FastConfirmation.Spec4Delta
import Goldfish.FastConfirmation.Ledger4Delta
import Goldfish.FastConfirmation.Lemma5
import Goldfish.FastConfirmation.Theorem4
import Goldfish.FastConfirmation.Theorem5
import Goldfish.FastConfirmation.Theorem6

/-!
# Fast confirmation (paper App. C)

Fast confirmation and security under `(1/2, 4∆)`-compliance:
Lemma 5, Theorems 4–6.

* `Goldfish.FastConfirmation.Spec4Delta` — abstract 4∆ protocol spec (`Spec4Δ`).
* `Goldfish.FastConfirmation.Ledger4Delta` — confirmed ledger `Ledger4Δ` + `TxModel4Δ` for the 4∆ regime.
* `Goldfish.FastConfirmation.Lemma5` — fast-confirmed block ⇒ honest validators
  vote for a descendant next slot.
* `Goldfish.FastConfirmation.Theorem4` — fast-confirmed block stays in every
  honest chain (`B ⪯ forkChoice`).
* `Goldfish.FastConfirmation.Theorem5` — safety with fast confirmations.
* `Goldfish.FastConfirmation.Theorem6` — liveness with `Tconf = Θ(κ)` and
  optimistic fast confirmation.
-/
