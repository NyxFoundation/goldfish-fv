import Goldfish.Protocol

/-!
# Fast-confirmation ledger layer (4∆ regime)

`FastLedger` mirrors `Ledger` for the 4∆-slot regime of Track B.
`confirmed_of_stable` uses `fastVoteRound` and the `4∆(t+κ)+2∆` confirmation
boundary. Safety (`FastLedger.safe`) follows by the same proof as `Ledger.safe`.

`FastTxModel` is the transaction model for the 4∆ regime: `leader_includes` uses
`fastSlotStart` instead of `slotStart`.
-/

namespace Goldfish

variable {Block Validator : Type*} [BlockTree Block]

/-- Confirmed-ledger assignment for the `(1/2, 4∆)` regime at depth `κ`. -/
structure FastLedger (E : Execution Block Validator) (κ : ℕ) where
  /-- `ch^id_r`: ledger output by `id` at round `r`. -/
  chain : Validator → Round → Block
  /-- **κ-deep confirmation (4∆ regime)**. If `B` is a stable prefix of the
  fork choice of every awake honest eligible voter at every `fastVoteRound t'`
  with `t' > t` (Theorem 4's conclusion), then from round `4∆(t+κ)+2∆` onward
  `B` is a prefix of every awake honest validator's ledger. -/
  confirmed_of_stable :
    ∀ {B : Block} {t : Slot},
      (∀ t' : Slot, t < t' → ∀ id : Validator,
        E.awakeHonest id (E.fastVoteRound t') → E.eligibleVote id t' →
        B ≤ E.forkChoice id (E.fastVoteRound t')) →
      ∀ {r : Round} {id : Validator},
        4 * E.Δ * (t + κ) + 2 * E.Δ ≤ r → E.awakeHonest id r → B ≤ chain id r
  /-- Ledger is a prefix of the validator's own fork choice. -/
  chain_le_forkChoice :
    ∀ {r : Round} {id : Validator}, E.awakeHonest id r → chain id r ≤ E.forkChoice id r
  /-- Confirmed blocks are stable forward: a block already in some awake honest
  validator's ledger at round `r` is a prefix of every awake honest validator's
  fork choice at every round `r' ≥ r`. -/
  confirmed_persists :
    ∀ {r r' : Round} {id id' : Validator}, r ≤ r' →
      E.awakeHonest id r → E.awakeHonest id' r' →
        chain id r ≤ E.forkChoice id' r'

namespace FastLedger

variable {E : Execution Block Validator} {κ : ℕ}

/-- **Safety** (Def. 1 in the 4∆ regime). Any two ledgers output by awake honest
validators are consistent. -/
def Safe (FL : FastLedger E κ) : Prop :=
  ∀ {r r' : Round} {id id' : Validator},
    E.awakeHonest id r → E.awakeHonest id' r' →
      BlockTree.Consistent (FL.chain id r) (FL.chain id' r')

/-- Safety holds for every `FastLedger` assignment — same proof as `Ledger.safe`. -/
theorem safe (FL : FastLedger E κ) : FL.Safe := by
  intro r r' id id' h h'
  rcases le_total r r' with hrr | hrr
  · exact BlockTree.consistent_of_le_of_le
      (FL.confirmed_persists hrr h h') (FL.chain_le_forkChoice h')
  · exact (BlockTree.consistent_of_le_of_le
      (FL.confirmed_persists hrr h' h) (FL.chain_le_forkChoice h)).symm

end FastLedger

/-- Transaction model for the 4∆ regime. `leader_includes` uses `fastSlotStart`. -/
structure FastTxModel (E : Execution Block Validator) where
  /-- Transactions. -/
  Tx : Type*
  /-- `mem tx B`: `tx` is included in the chain ending at `B`. -/
  mem : Tx → Block → Prop
  /-- Membership is monotone along the prefix order. -/
  mem_mono : ∀ {tx : Tx} {B B' : Block}, mem tx B → B ≤ B' → mem tx B'
  /-- `received tx r`: `tx` was received by some awake honest validator by round `r`. -/
  received : Tx → Round → Prop
  /-- **Honest proposers include pending transactions** (4∆ regime): if `tx` was
  received by round `r`, any recognized leader at slot `t` with `4∆t ≥ r`
  includes `tx`. -/
  leader_includes :
    ∀ {tx : Tx} {r : Round} {lead : Validator} {t : Slot},
      received tx r → E.leader lead t → r ≤ E.fastSlotStart t →
        mem tx (E.proposalBlock lead t)

/-- **Liveness** with confirmation time `Tconf` (rounds) in the 4∆ regime. -/
def FastTxModel.Live {E : Execution Block Validator} {κ : ℕ}
    (TX : FastTxModel E) (FL : FastLedger E κ) (Tconf : ℕ) : Prop :=
  ∀ {tx : TX.Tx} {r : Round}, TX.received tx r →
    ∀ {r' : Round} {id : Validator}, r + Tconf ≤ r' → E.awakeHonest id r' →
      TX.mem tx (FL.chain id r')

end Goldfish
