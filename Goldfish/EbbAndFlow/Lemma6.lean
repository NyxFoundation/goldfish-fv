import Goldfish.EbbAndFlow.Proposition2
import Goldfish.SynchronousSecurity.Theorem2

/-!
# Lemma 6 — security of `ch_ava` under synchrony

> **Lemma 6** (Safety and liveness of `ch_ava` under synchrony). Suppose a
> `(1/2, 3∆)`-compliant execution of Goldfish in the synchronous sleepy model.
> Then, w.o.p., the available ledger `ch_ava` satisfies `1/2`-safety and
> `1/2`-liveness at all times.

The paper's one-line proof: by Proposition 2 checkpointing does not alter the
fork-choice rule, so if honest validators started the fork choice from genesis at
every round (instead of the latest checkpoint) they would obtain the same
execution. Hence `ch_ava` *is* the checkpoint-independent κ-deep Goldfish
ledger, and its security follows from Theorem 2.

We carry that Proposition 2 consequence as the hypothesis `hchava` (`ch_ava`
coincides with the genesis-based confirmed ledger `L`) and transport Theorem 2's
safety and liveness across it.
-/

namespace Goldfish

variable {Block Validator : Type*} [BlockTree Block] {E : Execution Block Validator}

/-- **Lemma 6.** Given Lemma 1's good events and the Proposition 2 consequence
that `ch_ava` is the genesis-based κ-deep Goldfish ledger `L`, the available
ledger is safe and live (at all times, i.e. after round `0`) with confirmation
time `(2κ+2)·3∆`. -/
theorem lemma6 {G : Gadget E} {κ : ℕ} (S : Spec E) (L : Ledger E κ) (TX : TxModel E)
    (hmaj : HonestMajorityPerSlot E) (hwin : HonestLeaderEveryWindow E κ)
    (hchava : ∀ {id : Validator} {r : Round}, G.chava id r = L.chain id r) :
    G.SafeAfter G.chava 0 ∧ G.LiveAfter TX G.chava 0 ((2 * κ + 2) * (3 * E.Δ)) := by
  obtain ⟨hsafe, hlive⟩ := theorem2 S L TX hmaj hwin
  refine ⟨?_, ?_⟩
  · intro r r' id id' _ _ hawake hawake'
    rw [hchava, hchava]
    exact hsafe hawake hawake'
  · intro tx r _ hrecv r' id hr' hawake
    rw [hchava]
    exact hlive hrecv hr' hawake

end Goldfish
