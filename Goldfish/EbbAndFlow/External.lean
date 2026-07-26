import Goldfish.EbbAndFlow.Basic

/-!
# External [61] accountability-gadget results, and the imported Propositions 3 & 5

The partial-synchrony / ebb-and-flow proofs (Thm. 7, Lem. 6–9) build on the
accountability-gadget theorems of Neu–Tas–Tse [61]. Goldfish imports these with
**no proof in the Goldfish paper**, so they are declared here as permanent
axioms over the `Gadget` interface (now that the `ch_acc`/`ch_ava` ledgers,
checkpoints and partial-synchrony times exist; cf. the deferral note in
`Goldfish.Axioms`).

Two of the Goldfish propositions *are* such imported results and live here:

* **Proposition 3** (= [61, Prop. 2]) — BFT-overlay `n/3`-liveness.
* **Proposition 5** (gap property, analogue of [61, Prop. 4]).

The remaining external facts used only inside larger proofs — `[61, Thm. 3]`
(accountable safety of `ch_acc`) — are declared alongside. `[61, Thm. 3/4]`
facts specific to a single proof are introduced in that proof's module.
-/

namespace Goldfish

variable {Block Validator : Type*} [BlockTree Block] {E : Execution Block Validator}

/-! ## Proposition 3 — BFT-overlay `n/3`-liveness ([61, Prop. 2])

> **Proposition 3** ([61, Prop. 2]). The BFT protocol satisfies `n/3`-liveness
> after `max(GST, GAT)` with transaction confirmation time `Tbft < ∞`.

Imported from [61] with no Goldfish-paper proof. The usable content of BFT
liveness for the gadget: once more than `2n/3` accepting gadget votes for a
checkpoint exist on `LOG_bft` at a round at or after `max(GST, GAT)`, the block
is checkpointed in every awake honest validator's view within `Tbft` rounds. -/
axiom proposition3 (G : Gadget E) :
    ∀ {B : Block} {c : ℕ} {r : Round}, G.maxGAS ≤ r → G.acceptingVotes B c r →
      ∀ {id : Validator}, E.awakeHonest id (r + G.Tbft) → G.checkpointed id (r + G.Tbft) B

/-! ## Proposition 5 — gap property (analogue of [61, Prop. 4])

> **Proposition 5** (Gap property). For a `(1/3, 3∆)`-compliant execution, given
> any round interval of size `Tchkpt`, no more than a single block can be
> checkpointed in the interval in the view of any honest validator.

Imported from [61] with no Goldfish-paper proof: honest validators wait
`Tchkpt` rounds after seeing a non-`⊥` checkpoint before voting for the next
iteration's proposal, and cannot see two conflicting checkpoints for one
iteration. Stated as: two checkpoints observed by one honest validator within a
`Tchkpt`-window coincide. -/
axiom proposition5 (G : Gadget E) :
    ∀ {id : Validator} {r r' : Round} {B B' : Block},
      G.checkpointed id r B → G.checkpointed id r' B' →
      r ≤ r' → r' < r + G.Tchkpt → B = B'

/-! ## [61, Prop. 3] — BFT-overlay agreement (safety + synchronous delivery)

The safety of the BFT overlay (`f < n/3`) together with synchronous message
delivery after `max(GST, GAT)`: accepting gadget votes that appear in one honest
validator's `LOG_bft` by round `r` appear in *every* honest validator's
`LOG_bft` by round `max(max(GST, GAT), r) + ∆`. This is the [61, Prop. 3] content
the Goldfish paper imports to prove iteration synchronization (Proposition 4). -/
axiom ext61_bftAgreement (G : Gadget E) :
    ∀ {B : Block} {c : ℕ} {r : Round}, G.acceptingVotes B c r →
      G.acceptingVotes B c (max G.maxGAS r + E.Δ)

/-! ## [61, Thm. 3] — accountable safety of `ch_acc`

> By [61, Thm. 3], `ch_acc` provides accountable safety with resilience `n/3`
> except with probability `negl(λ)` in the partially synchronous sleepy model.

Used by Theorem 7 (the `P1` safety clause). Stated as safety of
`ch_acc` at all rounds. -/
axiom ext61_accountableSafety (G : Gadget E) : G.SafeAfter G.chacc 0

/-! ## [61, Thm. 4] — no two honest-observed checkpoints conflict

> As the execution is `(1/3, 3∆)`-compliant, w.o.p. no two checkpoints observed
> by awake honest validators conflict (used in the proof of Lemma 7 / Lemma 9).

The accountable-safety consequence specialised to checkpoints: any two blocks
checkpointed in awake honest views are consistent (one is a prefix of the
other). -/
axiom ext61_checkpointsConsistent (G : Gadget E) :
    ∀ {id id' : Validator} {r r' : Round} {B B' : Block},
      G.checkpointed id r B → G.checkpointed id' r' B' → BlockTree.Consistent B B'

end Goldfish
