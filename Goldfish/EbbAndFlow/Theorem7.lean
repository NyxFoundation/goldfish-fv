import Goldfish.EbbAndFlow.Lemma6
import Goldfish.EbbAndFlow.Healing

/-!
# Theorem 7 — the ebb-and-flow property (Def. 4)

> **Theorem 7.** Goldfish combined with accountability gadgets (App. D.2)
> satisfies the ebb-and-flow property of Def. 4.

Def. 4 has three clauses for the two ledgers `ch_acc ⪯ ch_ava`:

* **P1** — the accountable, final-prefix ledger `ch_acc` is accountably safe and
  (after healing) live under partial synchrony;
* **P2** — the available ledger `ch_ava` is secure (safe and live) whenever the
  network is synchronous and a `1/2` honest majority is awake;
* **Prefix** — `ch_acc` is always a prefix of `ch_ava`.

The proof assembles the ebb-and-flow results: P1's safety is `[61, Thm. 3]`
(`ext61_accountableSafety`) and its liveness is `lemma7` fed the healing security
of `lemma9`; P2 is `lemma6`; Prefix is the `Gadget` construction
`chacc_le_chava`.
-/

namespace Goldfish

variable {Block Validator : Type*} [BlockTree Block] {E : Execution Block Validator}

/-- **The ebb-and-flow property (Def. 4)** for the ledger pair `ch_acc ⪯ ch_ava`:
`ch_acc` is accountably safe and live-after-healing (`Theal`, `Tacc`), `ch_ava`
is secure under synchrony (`Tava`), and `ch_acc` is always a prefix of `ch_ava`. -/
structure EbbAndFlowProperty (G : Gadget E) (TX : TxModel E) (Tava Theal Tacc : ℕ) : Prop where
  /-- **P1 (safety).** `ch_acc` is accountably safe ([61, Thm. 3]). -/
  acc_safe : G.SafeAfter G.chacc 0
  /-- **P1 (liveness).** `ch_acc` is live after the healing round `Theal` with
  confirmation time `Tacc = Θ(κ²)`. -/
  acc_live : G.LiveAfter TX G.chacc Theal Tacc
  /-- **P2 (safety).** `ch_ava` is safe under synchrony. -/
  ava_safe : G.SafeAfter G.chava 0
  /-- **P2 (liveness).** `ch_ava` is live under synchrony with confirmation time
  `Tava = (2κ+2)·3∆`. -/
  ava_live : G.LiveAfter TX G.chava 0 Tava
  /-- **Prefix.** `ch_acc` is always a prefix of `ch_ava`. -/
  prefix_acc_ava : ∀ {id : Validator} {r : Round}, G.chacc id r ≤ G.chava id r

/-- **Theorem 7.** Goldfish with the accountability gadget satisfies the
ebb-and-flow property of Def. 4. The hypotheses are the partial-synchrony ingredients:
Lemma 1's good events (`hmaj`, `hwin`), the Proposition 2 identity that `ch_ava`
is the genesis-based ledger `L` (`hchava`), recency (Lemma 8, `hrecency`) and the
two operational gadget liveness events (`healing_liveness`, `accountable_liveness`)
of Lemmas 9 and 7. -/
theorem theorem7 {κ : ℕ} {G : Gadget E} (S : Spec E) (L : Ledger E κ) (TX : TxModel E)
    (Tacc : ℕ)
    (hmaj : HonestMajorityPerSlot E) (hwin : HonestLeaderEveryWindow E κ)
    (hchava : ∀ {id : Validator} {r : Round}, G.chava id r = L.chain id r)
    (hrecency : ∀ {idc : Validator} {r : Round} {B : Block},
      G.checkpointed idc r B → G.maxGAS < r → G.Recent L B r)
    (healing_liveness :
      HonestLeaderEveryWindow E κ →
      (∀ {idc : Validator} {r : Round} {B : Block},
        G.checkpointed idc r B → G.maxGAS < r → G.Recent L B r) →
      (∀ {id : Validator} {r r' : Round} {B B' : Block},
        G.checkpointed id r B → G.checkpointed id r' B' → r ≤ r' → r' < r + G.Tchkpt → B = B') →
      G.LiveAfter TX G.chava (G.maxGAS + E.Δ + 2 * G.Tchkpt) (G.Tchkpt + G.Ttmout + G.Tbft))
    (accountable_liveness :
      G.SecureAfter TX G.chava (G.maxGAS + E.Δ + 2 * G.Tchkpt)
        (G.Tchkpt + G.Ttmout + G.Tbft) →
      (∀ {id id' : Validator} {r r' : Round} {B B' : Block},
        G.checkpointed id r B → G.checkpointed id' r' B' → BlockTree.Consistent B B') →
      G.LiveAfter TX G.chacc (G.maxGAS + E.Δ + 2 * G.Tchkpt) Tacc) :
    EbbAndFlowProperty G TX ((2 * κ + 2) * (3 * E.Δ)) (G.maxGAS + E.Δ + 2 * G.Tchkpt) Tacc := by
  -- P2: ch_ava security under synchrony (Lemma 6)
  obtain ⟨ava_safe, ava_live⟩ := lemma6 S L TX hmaj hwin hchava
  -- Lemma 9: ch_ava heals under partial synchrony
  have hheal := lemma9 L TX ava_safe hwin hrecency healing_liveness
  exact
    { acc_safe := ext61_accountableSafety G
      acc_live := lemma7 TX (G.maxGAS + E.Δ + 2 * G.Tchkpt) Tacc hheal accountable_liveness
      ava_safe := ava_safe
      ava_live := ava_live
      prefix_acc_ava := G.chacc_le_chava }

end Goldfish
