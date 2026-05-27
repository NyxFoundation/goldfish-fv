import Goldfish.SynchronousSecurity.Theorem1
import Goldfish.Security

/-!
# Theorem 3 — reorg resilience

> **Theorem 3** (Reorg resilience, IACR 2022/1171). Suppose a `(1/2, 3∆)`-compliant
> execution of Goldfish in the synchronous sleepy network model, and validator
> `id` with proposal `P*` is recognized as the leader of a slot `t` by all awake
> honest validators at round `3∆t + ∆`. Then, w.o.p.,
> `∃ r', ∀ r ≥ r', ∀ id : P*.B ⪯ ch^id_r`. In particular `r' = 3∆(t + κ) + 2∆`
> satisfies this.

Directly from **Theorem 1** (the leader's block `P*.B` is a stable prefix of the
canonical chain at all later slots) through the κ-deep confirmation rule
(`Ledger.confirmed_of_stable`): once `P*.B` has been canonical for `κ` slots it
enters every awake honest validator's ledger and never leaves. Lemma 1's good
event is threaded as a hypothesis.
-/

namespace Goldfish

variable {Block Validator : Type*} [BlockTree Block] {E : Execution Block Validator} {κ : ℕ}

/-- **Theorem 3.** With `r' = 3∆(t + κ) + 2∆`, the recognized honest leader's
block `P*.B` is a prefix of every awake honest validator's ledger at every round
`r ≥ r'` — it is never reorged out. -/
theorem theorem3 (S : Spec E) (L : Ledger E κ)
    (hmaj : HonestMajorityPerSlot E) {lead : Validator} {t : Slot}
    (hlead : E.leader lead t) :
    ∀ {r : Round} {id : Validator},
      3 * E.Δ * (t + κ) + 2 * E.Δ ≤ r → E.awakeHonest id r →
      E.proposalBlock lead t ≤ L.chain id r := by
  intro r id hr hawake
  exact L.confirmed_of_stable (theorem1 S hmaj hlead) hr hawake

end Goldfish
