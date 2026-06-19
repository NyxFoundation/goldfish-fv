import Goldfish.Ledger

/-!
# Ebb-and-flow base layer (paper App. D)

The partial-synchrony / accountability-gadget analysis (Thm. 7, Lem. 6–9,
Prop. 2–5) needs vocabulary the synchronous-security and fast-confirmation layers
do not have:

* **Partial synchrony** — a global stabilization time `GST` (after which honest
  messages are delivered within `∆`) and a global awake time `GAT`.
* **The accountability gadget** (App. D.2) — a BFT overlay that periodically
  *checkpoints* blocks. Honest validators proceed through *iterations*; in each
  iteration a checkpoint proposal may become checkpointed once enough accepting
  gadget votes appear on the overlay ledger `LOG_bft`. Timing is governed by
  `Tchkpt` (slots between iterations), `Ttmout` (iteration timeout) and `Tbft`
  (BFT confirmation time).
* **Two ledgers** — the available ledger `ch_ava` (the κ-deep Goldfish output)
  and the accountable final-prefix ledger `ch_acc` (the checkpointed prefix).
  By construction `ch_acc ⪯ ch_ava` (the *Prefix* clause of Def. 4).

Following Barrier 3 of `README.md`, these mechanics are an
**abstract interface**: `Gadget` bundles the observable data, `GadgetSpec`
(added per proof) bundles the protocol-mechanic bridges, and the external [61]
accountability-gadget theorems are declared as axioms in
`Goldfish.EbbAndFlow.External`. No operational model of Alg. 4–6 is built.
-/

namespace Goldfish

variable {Block Validator : Type*} [BlockTree Block]

/-- Observable data of the accountability gadget running on top of an
`Execution` (paper App. D.2). Layered on `Execution` exactly as `Ledger` is.

`checkpointed id r B` means validator `id` observes block `B` to be checkpointed
in its view at round `r`. `entersIter id c r` means `id` enters accountability
iteration `c` at round `r`. `acceptingVotes B c r` means more than `2n/3`
validators have, by round `r`, cast accepting gadget votes for `B` as the
iteration-`c` checkpoint on `LOG_bft` (the premise of the BFT liveness/safety
results of [61]). `chava`/`chacc` are the available and accountable ledgers. -/
structure Gadget (E : Execution Block Validator) where
  /-- Global stabilization time: after `GST`, honest messages are delivered
  within `∆`. -/
  GST : Round
  /-- Global awake time: after `GAT`, the honest awake set is stable. -/
  GAT : Round
  /-- Slots the gadget waits between iterations (`Tchkpt = Θ(κ)`). -/
  Tchkpt : ℕ
  /-- Iteration timeout. -/
  Ttmout : ℕ
  /-- BFT-overlay confirmation time (`LOG_bft` latency). -/
  Tbft : ℕ
  /-- `checkpointed id r B`: `id` observes `B` checkpointed in its view at `r`. -/
  checkpointed : Validator → Round → Block → Prop
  /-- `entersIter id c r`: `id` enters accountability iteration `c` at round `r`. -/
  entersIter : Validator → ℕ → ℕ → Prop
  /-- `acceptingVotes B c r`: more than `2n/3` validators have cast accepting
  gadget votes for `B` as the iteration-`c` checkpoint by round `r`. -/
  acceptingVotes : Block → ℕ → Round → Prop
  /-- The available ledger `ch_ava` (κ-deep Goldfish output). -/
  chava : Validator → Round → Block
  /-- The accountable final-prefix ledger `ch_acc` (checkpointed prefix). -/
  chacc : Validator → Round → Block
  /-- **Prefix** (Def. 4): `ch_acc` is always a prefix of `ch_ava`, by
  construction of the two ledgers. -/
  chacc_le_chava : ∀ {id : Validator} {r : Round}, chacc id r ≤ chava id r

namespace Gadget

variable {E : Execution Block Validator} (G : Gadget E)

/-- `max(GST, GAT)`: the round after which the network is both synchronous and
the honest awake set has stabilized. -/
def maxGAS : Round := max G.GST G.GAT

/-- Recency window `Trcnt = ∆ + Ttmout + Tbft` (Lem. 8). -/
def Trcnt : ℕ := E.Δ + G.Ttmout + G.Tbft

/-- A ledger function is **safe after round `R`** (Def. 1): any two ledger
outputs by awake honest validators at rounds `≥ R` are consistent. (`G` fixes
the ambient execution `E`; the predicate itself depends only on `E`.) -/
def SafeAfter (_G : Gadget E) (f : Validator → Round → Block) (R : Round) : Prop :=
  ∀ {r r' : Round} {id id' : Validator}, R ≤ r → R ≤ r' →
    E.awakeHonest id r → E.awakeHonest id' r' →
      BlockTree.Consistent (f id r) (f id' r')

/-- A ledger function is **live after round `R` with confirmation time `Tconf`**
(Def. 1), relative to a transaction model: a transaction received at a round
`≥ R` appears in every awake honest ledger output within `Tconf` rounds. -/
def LiveAfter (_G : Gadget E) (TX : TxModel E) (f : Validator → Round → Block)
    (R Tconf : ℕ) : Prop :=
  ∀ {tx : TX.Tx} {r : Round}, R ≤ r → TX.received tx r →
    ∀ {r' : Round} {id : Validator}, r + Tconf ≤ r' → E.awakeHonest id r' →
      TX.mem tx (f id r')

/-- A ledger function is **secure after round `R`** (safe and live, Def. 1). -/
def SecureAfter (G : Gadget E) (TX : TxModel E) (f : Validator → Round → Block)
    (R Tconf : ℕ) : Prop :=
  G.SafeAfter f R ∧ G.LiveAfter TX f R Tconf

end Gadget

end Goldfish
