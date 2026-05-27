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

namespace Ledger

variable {E : Execution Block Validator} {κ : ℕ}

/-- **Safety** (Def. 1). Any two ledgers output by awake honest validators are
consistent (one is a prefix of the other). -/
def Safe (L : Ledger E κ) : Prop :=
  ∀ {r r' : Round} {id id' : Validator},
    E.awakeHonest id r → E.awakeHonest id' r' →
      BlockTree.Consistent (L.chain id r) (L.chain id' r')

end Ledger

end Goldfish
