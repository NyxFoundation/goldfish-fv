import Goldfish.EbbAndFlow.GadgetSpec
import Goldfish.SynchronousSecurity.Theorem1

/-!
# Proposition 2 — checkpointing does not alter the GHOST-Eph fork choice

> **Proposition 2.** Suppose a `(1/2, 3∆)`-compliant execution of Goldfish in the
> synchronous sleepy model. If a block `B` is observed to be checkpointed by an
> honest validator for the first time at some round `r`, then `B` is in the common
> prefix of the chains identified in Alg. 2, ll. 8, 22, 28 right before round `r`
> by all awake honest validators (and stays so).

The paper's proof: a checkpointed block was confirmed `κ` slots deep in an honest
view, hence — since honest validators start the fork choice at genesis and an
honest leader exists each window (Lemma 1) — it lies in the prefix of a
recognized honest leader's proposal `P*.B`; by Theorem 1 that proposal is a
prefix of every awake honest validator's fork choice ever after, so checkpointing
leaves the fork choice unchanged.

Here the "anchored to an honest proposal" step is the gadget mechanic
`GadgetSpec.proposal_of_checkpointed`, and the *stability* of `P*.B` is exactly
`theorem1` (which threads Lemma 1's `HonestMajorityPerSlot`).
-/

namespace Goldfish

variable {Block Validator : Type*} [BlockTree Block] {E : Execution Block Validator}

/-- **Proposition 2.** A block `B` first checkpointed in an honest view at round
`r` sits in the common prefix of the fork-choice chains of all awake honest
eligible voters at the vote round of every slot after the anchoring slot `t` —
i.e. checkpointing does not change the GHOST-Eph fork choice. -/
theorem proposition2 {G : Gadget E} (S : Spec E) (GS : GadgetSpec G)
    (hmaj : HonestMajorityPerSlot E)
    {idv : Validator} {r : Round} {B : Block} (hchk : G.checkpointed idv r B) :
    ∃ t : Slot, ∀ t' : Slot, t < t' → ∀ id' : Validator,
      E.awakeHonest id' (E.voteRound t') → E.eligibleVote id' t' →
        B ≤ E.forkChoice id' (E.voteRound t') := by
  obtain ⟨lead, t, hlead, hBle⟩ := GS.proposal_of_checkpointed hchk
  exact ⟨t, fun t' ht' id' hawake helig =>
    hBle.trans (theorem1 S hmaj hlead t' ht' id' hawake helig)⟩

end Goldfish
