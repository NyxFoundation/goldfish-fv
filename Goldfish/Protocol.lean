import Goldfish.Basic

/-!
# Goldfish — abstract protocol interface

Per Barrier 3 of `docs/formalization-strategy.md`, we do **not** implement
Algorithms 1–6 operationally. Instead the GHOST-Eph fork choice, the slot/round
structure and the voting rule are captured by an abstract interface: an
`Execution` of observable data plus a `Spec` bundling the protocol's defining
behaviour as hypotheses. Every Track-A/B theorem is then *derived* from `Spec`.

An executable model can later replace `Spec` (discharging its fields) without
changing any theorem statement.
-/

namespace Goldfish

/-- The observable data of a Goldfish execution over a block tree `Block` and a
validator type `Validator`.

The dynamic predicates are indexed by rounds/slots; `adv`/`hon` are the awake
adversary/honest counts of Def. 2, and `honEligible`/`advEligible` are the
eligible-voter counts whose comparison is the conclusion of Lemma 1. The
`outvotes` predicate abstracts the GHOST-Eph vote tally (see `Spec`). -/
structure Execution (Block Validator : Type*) [BlockTree Block] where
  /-- Network delay bound `∆`; one slot spans `3∆` rounds. -/
  Δ : ℕ
  /-- `∆` is positive. -/
  Δ_pos : 0 < Δ
  /-- Number of adversary validators awake at a round (`A_r`). -/
  adv : Round → ℕ
  /-- Number of honest validators awake at a round (`H_r`). -/
  hon : Round → ℕ
  /-- # honest validators awake at round `3∆t+∆` and eligible to vote at slot `t`
  (the honest side of Lemma 1's count). -/
  honEligible : Slot → ℕ
  /-- # adversary validators at round `3∆(t+1)+∆` eligible to vote at slot `t`
  (the adversary side of Lemma 1's count). -/
  advEligible : Slot → ℕ
  /-- Total # validators eligible to vote at slot `t` (bounded above by
  `(1+ε)·n·thr_v` in Proposition 1). -/
  eligibleVoters : Slot → ℕ
  /-- `awake id r`: validator `id` is non-asleep at round `r`. -/
  awake : Validator → Round → Prop
  /-- `honestAt id r`: `id` is honest at round `r`. Corruption is monotone
  (honest → adversary only); not enforced here, used as a premise. -/
  honestAt : Validator → Round → Prop
  /-- `eligibleVote id t`: `id` won the vote lottery for slot `t`. -/
  eligibleVote : Validator → Slot → Prop
  /-- `eligiblePropose id t`: `id` won the proposer lottery for slot `t`. -/
  eligiblePropose : Validator → Slot → Prop
  /-- `votesFor id t B`: honest `id` casts its slot-`t` vote for block `B`. -/
  votesFor : Validator → Slot → Block → Prop
  /-- `leader id t`: `id` is recognized as slot-`t` leader by all awake honest
  validators at round `3∆t+∆` (Alg. 2, l. 16). -/
  leader : Validator → Slot → Prop
  /-- The block `id` proposes for slot `t` (`P*.B` when `id` is the leader). -/
  proposalBlock : Validator → Slot → Block
  /-- GHOST-Eph fork-choice output: the canonical-chain tip in `id`'s view at
  round `r` (Alg. 2, ll. 8/22/28). -/
  forkChoice : Validator → Round → Block
  /-- `outvotes id r t B`: in `id`'s view (bvtree) at round `r`, the descendants
  of `B` carry, at every fork-choice level, strictly more slot-`t` votes than any
  block conflicting with `B`. This is the GHOST-Eph majority condition of
  Alg. 3, l. 7, kept abstract here. -/
  outvotes : Validator → Round → Slot → Block → Prop

namespace Execution

variable {Block Validator : Type*} [BlockTree Block] (E : Execution Block Validator)

/-- First round of slot `t`: `3∆t`. -/
def slotStart (t : Slot) : Round := 3 * E.Δ * t

/-- Vote round of slot `t`: `3∆t + ∆`, when awake honest validators cast votes
and the leader of slot `t` is recognized (Alg. 2, ll. 16, 22). -/
def voteRound (t : Slot) : Round := 3 * E.Δ * t + E.Δ

/-- `id` is awake and honest at round `r`. -/
def awakeHonest (id : Validator) (r : Round) : Prop := E.awake id r ∧ E.honestAt id r

/-- `id` casts its slot-`t` vote for some descendant of `B`. -/
def votesForDescendant (id : Validator) (t : Slot) (B : Block) : Prop :=
  ∃ B', B ≤ B' ∧ E.votesFor id t B'

theorem votesForDescendant.of_votesFor {E : Execution Block Validator}
    {id : Validator} {t : Slot} {B : Block} (h : E.votesFor id t B) :
    E.votesForDescendant id t B :=
  ⟨B, le_rfl, h⟩

/-- This execution is `(γ,τ)`-compliant (Def. 2) with parameters `γ, ε, n₀`. -/
def Compliant (γ ε : ℝ) (n₀ : ℕ) : Prop := Goldfish.Compliant E.adv E.hon γ ε n₀

end Execution

/-- The abstract protocol specification: the defining behaviour of GHOST-Eph,
the voting rule, leader recognition and synchronous message delivery, stated as
hypotheses. Track-A/B theorems are derived from `Spec` together with the
probabilistic good events declared in `Goldfish.Axioms`.

Every field is a protocol *mechanic* (a consequence of Alg. 1–6 and synchrony),
never a consequence of a numbered lemma — so deriving the numbered lemmas from
`Spec` is non-circular. -/
structure Spec {Block Validator : Type*} [BlockTree Block]
    (E : Execution Block Validator) : Prop where
  /-- **Voting rule** (Alg. 2, l. 22). An awake honest validator eligible to vote
  at slot `t` votes for the block its GHOST-Eph fork choice returns at the slot's
  vote round `3∆t+∆`. -/
  vote_forkChoice :
    ∀ {id : Validator} {t : Slot},
      E.awakeHonest id (E.voteRound t) → E.eligibleVote id t →
        E.votesFor id t (E.forkChoice id (E.voteRound t))
  /-- **GHOST-Eph engine** (recursive majority, Alg. 3, l. 7). If from `id`'s view
  at round `r` the descendants of `B` outvote every conflicting block among the
  relevant slot-`t` votes, then `id`'s fork choice at `r` is a descendant of
  `B`. -/
  forkChoice_of_outvotes :
    ∀ {id : Validator} {r : Round} {t : Slot} {B : Block},
      E.outvotes id r t B → B ≤ E.forkChoice id r
  /-- **Leader recognition** (Alg. 2, ll. 16, 19). When the honest leader `lead`
  of slot `t` is recognized by all awake honest validators, every awake honest
  validator merges the proposal into its bvtree and its slot-`t` vote-round fork
  choice is the leader's proposed block `P*.B`. -/
  forkChoice_of_leader :
    ∀ {lead id : Validator} {t : Slot},
      E.leader lead t → E.awakeHonest id (E.voteRound t) →
        E.forkChoice id (E.voteRound t) = E.proposalBlock lead t
  /-- **Synchrony + honest-majority bridge** (Alg. 2, l. 19; synchronous
  delivery). If at slot `t` every awake honest validator eligible to vote at `t`
  voted for a descendant of `B`, and honest eligible voters outnumber adversary
  eligible voters at `t` (the conclusion of Lemma 1), then any honest validator
  awake at the next vote round and eligible at slot `t+1` sees `B`'s descendants
  outvote every conflicting block. -/
  outvotes_of_honest_majority :
    ∀ {id : Validator} {t : Slot} {B : Block},
      E.advEligible t < E.honEligible t →
      (∀ {v : Validator}, E.awakeHonest v (E.voteRound t) → E.eligibleVote v t →
        E.votesForDescendant v t B) →
      E.awakeHonest id (E.voteRound (t + 1)) → E.eligibleVote id (t + 1) →
        E.outvotes id (E.voteRound (t + 1)) t B

end Goldfish
