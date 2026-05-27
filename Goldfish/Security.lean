import Goldfish.Protocol

/-!
# Goldfish — the confirmed-ledger layer

The numbered statements about *security* (Def. 1) talk about the output ledger
`ch^id_r`: the κ-deep confirmed prefix of a validator's canonical chain
(`ch⌈κ`, Alg. 2, l. 29). This layer adds an abstract `Ledger` assignment — the
ledger function plus the confirmation-rule facts relating it to the GHOST-Eph
fork choice — on top of the `Execution`/`Spec` interface, and the Def. 1
`Safe`/`Live` predicates.

As with `Spec`, the confirmation rule is an abstract interface (Barrier 3): an
operational κ-truncation model can discharge these fields later without changing
the theorem statements.
-/

namespace Goldfish

variable {Block Validator : Type*} [BlockTree Block]

/-- A confirmed-ledger assignment for an execution at confirmation depth `κ`.

`chain id r` is the ledger `ch^id_r` output by `id` at round `r`. The fields
record the consequences of the κ-deep confirmation rule (Alg. 2, l. 29) that the
security theorems use. -/
structure Ledger (E : Execution Block Validator) (κ : ℕ) where
  /-- `ch^id_r`: the ledger output by validator `id` at round `r`. -/
  chain : Validator → Round → Block
  /-- **κ-deep confirmation.** If a block `B` proposed at slot `t` is a prefix of
  the fork choice of every awake honest eligible voter at every later slot (the
  stability conclusion of Theorem 1), then from round `3∆(t+κ)+2∆` onward `B` is
  a prefix of every awake honest validator's ledger. -/
  confirmed_of_stable :
    ∀ {B : Block} {t : Slot},
      (∀ t' : Slot, t < t' → ∀ id : Validator, E.awakeHonest id (E.voteRound t') →
        E.eligibleVote id t' → B ≤ E.forkChoice id (E.voteRound t')) →
      ∀ {r : Round} {id : Validator}, 3 * E.Δ * (t + κ) + 2 * E.Δ ≤ r →
        E.awakeHonest id r → B ≤ chain id r
  /-- **Ledger is κ-deep in the own canonical chain** (`ch⌈κ`, Alg. 2, l. 29):
  a validator's ledger is a prefix of its own fork choice. -/
  chain_le_forkChoice :
    ∀ {r : Round} {id : Validator}, E.awakeHonest id r → chain id r ≤ E.forkChoice id r
  /-- **Confirmed blocks are canonical-stable forward** (reorg resilience at the
  confirmation depth): a block already in some awake honest validator's ledger at
  round `r` is a prefix of every awake honest validator's fork choice at every
  round `r' ≥ r`. This is the κ-deep common-prefix consequence of `confirmed_of_stable`
  + Theorem 3, taken as the confirmation-rule interface here. -/
  confirmed_persists :
    ∀ {r r' : Round} {id id' : Validator}, r ≤ r' →
      E.awakeHonest id r → E.awakeHonest id' r' →
        chain id r ≤ E.forkChoice id' r'

namespace Ledger

variable {E : Execution Block Validator} {κ : ℕ}

/-- **Safety** (Def. 1). Any two ledgers output by awake honest validators are
consistent (one is a prefix of the other). -/
def Safe (L : Ledger E κ) : Prop :=
  ∀ {r r' : Round} {id id' : Validator},
    E.awakeHonest id r → E.awakeHonest id' r' →
      BlockTree.Consistent (L.chain id r) (L.chain id' r')

/-- Safety holds for every confirmed-ledger assignment. Both ledgers are prefixes
of the later validator's fork choice — one by `confirmed_persists`, the other by
`chain_le_forkChoice` — hence consistent, since ancestors of a common block form
a chain (`BlockTree.consistent_of_le_of_le`). -/
theorem safe (L : Ledger E κ) : L.Safe := by
  intro r r' id id' h h'
  rcases le_total r r' with hrr | hrr
  · exact BlockTree.consistent_of_le_of_le
      (L.confirmed_persists hrr h h') (L.chain_le_forkChoice h')
  · exact (BlockTree.consistent_of_le_of_le
      (L.confirmed_persists hrr h' h) (L.chain_le_forkChoice h)).symm

end Ledger

/-- Transaction layer for the liveness statement: a transaction type, monotone
chain-membership, receipt by an awake honest validator, and the honest-proposer
inclusion rule. Abstract (Barrier 3). -/
structure TxModel (E : Execution Block Validator) where
  /-- Transactions. -/
  Tx : Type*
  /-- `mem tx B`: `tx` is included in the chain ending at block `B`. -/
  mem : Tx → Block → Prop
  /-- Membership is monotone along the prefix order: a transaction in a chain
  stays in every extension. -/
  mem_mono : ∀ {tx : Tx} {B B' : Block}, mem tx B → B ≤ B' → mem tx B'
  /-- `received tx r`: `tx` was received by some awake honest validator by round
  `r`. -/
  received : Tx → Round → Prop
  /-- **Honest proposers include pending transactions** (Alg. 2, ll. 7, 29): if
  `tx` was received by round `r`, then any recognized leader of a slot whose
  proposal round `3∆t` is at or after `r` includes `tx` in its proposed block. -/
  leader_includes :
    ∀ {tx : Tx} {r : Round} {lead : Validator} {t : Slot},
      received tx r → E.leader lead t → r ≤ E.slotStart t → mem tx (E.proposalBlock lead t)

/-- **Liveness** (Def. 1) with confirmation time `Tconf` (in rounds). A
transaction received by round `r` is included in every awake honest validator's
ledger from round `r + Tconf` on. -/
def TxModel.Live {E : Execution Block Validator} {κ : ℕ}
    (TX : TxModel E) (L : Ledger E κ) (Tconf : ℕ) : Prop :=
  ∀ {tx : TX.Tx} {r : Round}, TX.received tx r →
    ∀ {r' : Round} {id : Validator}, r + Tconf ≤ r' → E.awakeHonest id r' →
      TX.mem tx (L.chain id r')

end Goldfish
