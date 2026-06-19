import Goldfish.Protocol

/-!
# Goldfish — declared axioms

Two kinds of facts are declared (never proved with `sorry`):

* **Probabilistic good events** — the conclusions of Lemma 1, Lemma 4 and
  Proposition 1. These hold *with overwhelming probability* via VRF
  pseudorandomness + Chernoff bounds (paper App. G). They are declared as
  axioms so the deterministic dependents can proceed by threading the good
  event as a hypothesis; the measure-theoretic proof replacing each axiom is
  developed separately.

* **External [61] results** — Neu–Tas–Tse accountability-gadget theorems used by
  the partial-synchrony / ebb-and-flow proofs (Thm. 7, Lem. 6–9, Prop. 2–5).
  These cannot be *stated* faithfully until that section's vocabulary (the
  `ch_acc`/`ch_ava` ledgers, partial synchrony, `GST`/`GAT`) is modelled, so
  they are declared in `Goldfish.EbbAndFlow.External` over the `Gadget`
  interface — alongside those base types — rather than here. See
  `README.md` §"External reference [61]".
-/

namespace Goldfish

variable {Block Validator : Type*} [BlockTree Block]

/-! ## Good-event predicates -/

/-- Honest-majority good event (conclusion of Lemma 1 / Lemma 4): in every slot,
adversary validators eligible to vote are strictly fewer than awake honest
validators eligible to vote. -/
def HonestMajorityPerSlot (E : Execution Block Validator) : Prop :=
  ∀ t : Slot, E.advEligible t < E.honEligible t

/-- Honest-leader good event (conclusion of Lemma 1 / Lemma 4): every slot
interval of length `κ` contains a slot whose leader is an honest validator
recognized by all awake honest validators at its vote round. -/
def HonestLeaderEveryWindow (E : Execution Block Validator) (κ : ℕ) : Prop :=
  ∀ t : Slot, ∃ s : Slot, t ≤ s ∧ s < t + κ ∧
    ∃ lead : Validator, E.honestAt lead (E.voteRound s) ∧ E.leader lead s

/-! ## Lemma 1 — VRF lottery good event under `(1/2, 3∆)`-compliance

Declared as an axiom; the measure-theoretic Chernoff proof that replaces it is
developed separately and does **not** block dependents. -/

/-- **Lemma 1** (IACR 2022/1171, Lem. 1). For a `(1/2, 3∆)`-compliant execution,
w.o.p. every slot has an honest eligible-voter majority and every `κ`-window has
a recognized honest leader. -/
axiom lemma1 (E : Execution Block Validator) {ε : ℝ} {n₀ κ : ℕ}
    (hκ : 0 < κ) (hcomp : E.Compliant (1 / 2) ε n₀) :
    HonestMajorityPerSlot E ∧ HonestLeaderEveryWindow E κ

/-! ## Lemma 4 — VRF lottery good event under `(1/2, 4∆)`-compliance

The `(1/2, 4∆)`-compliance analogue of Lemma 1 for the fast-confirmation
proofs (same conclusion shape; the slot→round timing uses `4∆` instead of `3∆`).
Declared as an axiom; the replacing proof is developed separately. -/

/-- **Lemma 4** (IACR 2022/1171, Lem. 4). For a `(1/2, 4∆)`-compliant execution,
w.o.p. every slot has an honest eligible-voter majority and every `κ`-window has
a recognized honest leader. -/
axiom lemma4 (E : Execution Block Validator) {ε : ℝ} {n₀ κ : ℕ}
    (hκ : 0 < κ) (hcomp : E.Compliant (1 / 2) ε n₀) :
    HonestMajorityPerSlot E ∧ HonestLeaderEveryWindow E κ

/-! ## Proposition 1 — eligible-voter count bounds (Chernoff)

Declared as an axiom; the replacing proof is developed separately. -/

/-- **Proposition 1** (IACR 2022/1171, Prop. 1). With `T_hor = poly(κ)`, w.o.p. at
most `voterUB = (1+ε)·n·thr_v` validators are eligible to vote at any slot; and
under `(1/2, 4∆)`-compliance, w.o.p. adversary eligible voters are fewer than
`advUB = ½·n·thr_v` at every slot. -/
axiom proposition1 (E : Execution Block Validator) {ε : ℝ} {n₀ : ℕ}
    (voterUB advUB : ℝ) (hcomp : E.Compliant (1 / 2) ε n₀) :
    (∀ t : Slot, (E.eligibleVoters t : ℝ) ≤ voterUB) ∧
      (∀ t : Slot, (E.advEligible t : ℝ) < advUB)

end Goldfish
