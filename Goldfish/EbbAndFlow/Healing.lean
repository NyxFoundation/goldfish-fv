import Goldfish.EbbAndFlow.Proposition2
import Goldfish.EbbAndFlow.Proposition4
import Goldfish.EbbAndFlow.External

/-!
# Lemmas 7–9 — the recency / healing / accountable-liveness bundle (App. D)

The partial-synchrony recovery argument is, in the paper, a mutual induction
between

* **Lemma 8** (recency) — every checkpointed block proposed after `max(GST, GAT)`
  is `Trcnt`-recent (`Trcnt = ∆ + Ttmout + Tbft`);
* **Lemma 9** (healing) — `ch_ava` regains security after
  `max(GST, GAT) + ∆ + 2·Tchkpt` with `Tconf = Tchkpt + Ttmout + Tbft`, and an
  honest iteration leader's proposal stays in every later fork choice and carries
  a fresh honest block;
* **Lemma 7** (accountable liveness) — if `ch_ava` is secure after `Theal` then
  `ch_acc` satisfies `n/3`-liveness after `Theal` with `Tconf = Θ(κ²)`.

The paper's cycle is `Lem 7 → Lem 9 → Lem 8 → Lem 7`; the only edge *into*
Lemma 8 from Lemma 7 is the iteration-length bound (a checkpoint's proposal is at
most `Trcnt` old), which is a self-contained gadget timing fact. Extracting that
as the bridge `iterationLength_recent` breaks the cycle, so the three lemmas are
stated in the acyclic order **Lemma 8 → Lemma 9 → Lemma 7**: each later lemma
consumes the earlier one's conclusion as an explicit hypothesis (`hrecency`,
`hheal`) rather than by invoking it, so a top-level composition can chain them.

Following Barrier 3, the irreducibly operational steps of the healing argument
(the per-window honest-leader liveness event, the BFT-overlay accountable
liveness) are carried as documented gadget-mechanic hypotheses; every numbered
result *combines* them with the already-proved propositions/lemmas and the
external [61] axioms.
-/

namespace Goldfish

variable {Block Validator : Type*} [BlockTree Block] {E : Execution Block Validator}

/-- **`Trcnt`-recency.** A block `B*` checkpointed in an honest view at round `r`
is `Trcnt`-recent if `B* ⪯ B⌈κ` for the κ-deep chain `B⌈κ = L.chain id rr` of
some awake honest validator `id` at a round `rr ∈ [r − Trcnt, r]`. -/
def Gadget.Recent {κ : ℕ} (G : Gadget E) (L : Ledger E κ) (B : Block) (r : Round) : Prop :=
  ∃ (id : Validator) (rr : Round),
    rr ≤ r ∧ r ≤ rr + G.Trcnt ∧ E.awakeHonest id rr ∧ B ≤ L.chain id rr

/-! ## Lemma 8 — recency property -/

/-- **Lemma 8.** Every block checkpointed in an honest view at a round
`r > max(GST, GAT)` is `Trcnt`-recent.

The gadget mechanic `iterationLength_recent` packages the paper's two facts: a
checkpointed block's proposal is at most `Trcnt = ∆ + Ttmout + Tbft` old (the
iteration-length bound), and an honest validator casts an accepting gadget vote
for it only after confirming it `κ` slots deep — so some awake honest validator
holds it in its κ-deep chain within the recency window. Lemma 8 reads that off as
`Trcnt`-recency. -/
theorem lemma8 {κ : ℕ} {G : Gadget E} (L : Ledger E κ)
    (iterationLength_recent :
      ∀ {idc : Validator} {r : Round} {B : Block},
        G.checkpointed idc r B → G.maxGAS < r →
        ∃ (idh : Validator) (rr : Round),
          rr ≤ r ∧ rr + (E.Δ + G.Ttmout + G.Tbft) ≥ r ∧
          E.awakeHonest idh rr ∧ B ≤ L.chain idh rr)
    {idc : Validator} {r : Round} {B : Block}
    (hchk : G.checkpointed idc r B) (hr : G.maxGAS < r) :
    G.Recent L B r := by
  obtain ⟨idh, rr, hrr, hwin, hawake, hle⟩ := iterationLength_recent hchk hr
  exact ⟨idh, rr, hrr, by simpa [Gadget.Trcnt] using hwin, hawake, hle⟩

/-! ## Lemma 9 — healing property -/

/-- **Lemma 9 (security clause).** Under `(1/3, 3∆)`-compliance, `ch_ava` is
secure after round `max(GST, GAT) + ∆ + 2·Tchkpt` with confirmation time
`Tchkpt + Ttmout + Tbft`.

*Safety* holds at all rounds (Lemma 6, threaded as `hsafe`). *Liveness* is the
healing event: in each window after stabilization an honest iteration leader's
proposal — recent by Lemma 8 and non-conflicting by the gap property
(Proposition 5) — carries a fresh honest block into `ch_ava`. That operational
event is the gadget mechanic `healing_liveness`; Lemma 9 supplies it with the
honest-leader good event (Lemma 1's conclusion, threaded as `hwin`), recency
(Lemma 8's conclusion, threaded as `hrecency`) and the gap property
(Proposition 5). -/
theorem lemma9 {κ : ℕ} {G : Gadget E} (L : Ledger E κ) (TX : TxModel E)
    (hsafe : G.SafeAfter G.chava 0)
    (hwin : HonestLeaderEveryWindow E κ)
    (hrecency : ∀ {idc : Validator} {r : Round} {B : Block},
      G.checkpointed idc r B → G.maxGAS < r → G.Recent L B r)
    (healing_liveness :
      HonestLeaderEveryWindow E κ →
      (∀ {idc : Validator} {r : Round} {B : Block},
        G.checkpointed idc r B → G.maxGAS < r → G.Recent L B r) →
      (∀ {id : Validator} {r r' : Round} {B B' : Block},
        G.checkpointed id r B → G.checkpointed id r' B' → r ≤ r' → r' < r + G.Tchkpt → B = B') →
      G.LiveAfter TX G.chava (G.maxGAS + E.Δ + 2 * G.Tchkpt) (G.Tchkpt + G.Ttmout + G.Tbft)) :
    G.SecureAfter TX G.chava (G.maxGAS + E.Δ + 2 * G.Tchkpt) (G.Tchkpt + G.Ttmout + G.Tbft) := by
  refine ⟨?_, healing_liveness hwin hrecency (proposition5 G)⟩
  intro r r' id id' _ _ hawake hawake'
  exact hsafe (Nat.zero_le _) (Nat.zero_le _) hawake hawake'

/-- **Lemma 9 (proposal clause).** A checkpointed block stays in the common
prefix of every awake honest validator's fork choice — in particular an honest
iteration leader's checkpoint proposal `b̂c` satisfies `b̂c ⪯ B` for any `B`
identified by an awake honest validator after it. This is exactly Proposition 2
applied to the checkpoint. -/
theorem lemma9_proposal {G : Gadget E} (S : Spec E) (GS : GadgetSpec G)
    (hmaj : HonestMajorityPerSlot E)
    {idc : Validator} {r : Round} {B : Block} (hchk : G.checkpointed idc r B) :
    ∃ t : Slot, ∀ t' : Slot, t < t' → ∀ id' : Validator,
      E.awakeHonest id' (E.voteRound t') → E.eligibleVote id' t' →
        B ≤ E.forkChoice id' (E.voteRound t') :=
  proposition2 S GS hmaj hchk

/-! ## Lemma 7 — liveness of `ch_acc` -/

/-- **Lemma 7.** Consider a `(1/3, 3∆)`-compliant execution. If `ch_ava` is
secure after some round `Theal ≥ max(GST, GAT) + ∆ + Tchkpt`, then `ch_acc`
satisfies `n/3`-liveness after `Theal` with transaction confirmation time
`Tconf = Θ(κ²)` (here the abstract round count `Tacc`).

The paper's argument: BFT liveness (Proposition 3) checkpoints an honest leader's
proposal within each iteration; iteration entrance is synchronized
(Proposition 4); by Lemma 9 that proposal carries a fresh honest block, which —
being checkpointed — enters `ch_acc`. The gadget mechanic `accountable_liveness`
performs that inclusion; Lemma 7 supplies it with the healing security of
`ch_ava` (Lemma 9's conclusion, threaded as `hheal`) and the
checkpoint-consistency of [61, Thm. 4]. The BFT-liveness step (Proposition 3)
is internal to the `accountable_liveness` mechanic, not passed by Lemma 7. -/
theorem lemma7 {G : Gadget E} (TX : TxModel E)
    (Theal Tacc : ℕ)
    (hheal : G.SecureAfter TX G.chava (G.maxGAS + E.Δ + 2 * G.Tchkpt)
      (G.Tchkpt + G.Ttmout + G.Tbft))
    (accountable_liveness :
      G.SecureAfter TX G.chava (G.maxGAS + E.Δ + 2 * G.Tchkpt)
        (G.Tchkpt + G.Ttmout + G.Tbft) →
      (∀ {id id' : Validator} {r r' : Round} {B B' : Block},
        G.checkpointed id r B → G.checkpointed id' r' B' → BlockTree.Consistent B B') →
      G.LiveAfter TX G.chacc Theal Tacc) :
    G.LiveAfter TX G.chacc Theal Tacc :=
  accountable_liveness hheal (ext61_checkpointsConsistent G)

end Goldfish
