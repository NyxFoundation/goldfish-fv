import Goldfish.Protocol
import Goldfish.Axioms

/-!
# Abstract spec for the 4∆ regime (`Spec4Δ`)

`Spec4Δ` is the analogue of `Spec` for the `(1/2, 4∆)`-compliance regime of
Track B. It adds 4∆-specific protocol mechanics on top of the
timing-independent `forkChoice_of_outvotes` (shared with `Spec`):

* `fast_vote_forkChoice` — voting rule at `fastVoteRound`
* `fast_forkChoice_of_leader` — leader recognition at `fastVoteRound`
* `fast_outvotes_of_honest_majority` — synchrony + honest-majority bridge for
  4∆ timing (used in Lemma 3's analogue within Theorem 4's induction)
* `outvotes_of_fast_confirm` — if `id*` fast confirms `B` at slot `t`, then
  every honest eligible voter at `fastVoteRound (t+1)` sees `B`'s descendants
  outvote conflicting blocks (the key mechanic for Lemma 5)
* `confirms_of_honest_votes` — if all honest eligible voters voted for `B` at
  `fastVoteRound t`, any validator awake at `fastConfirmRound t` fast confirms
  `B` (used in Theorem 6's optimistic fast-confirm clause)
-/

namespace Goldfish

/-- Abstract specification for the 4∆-regime protocol. -/
structure Spec4Δ {Block Validator : Type*} [BlockTree Block]
    (E : Execution Block Validator) : Prop where
  /-- **GHOST-Eph engine** (Alg. 3, l. 7) — timing-independent: if `id`'s view
  at any round `r` shows `B`'s descendants outvoting every conflicting block,
  then `id`'s fork choice at `r` is a descendant of `B`. -/
  forkChoice_of_outvotes :
    ∀ {id : Validator} {r : Round} {t : Slot} {B : Block},
      E.outvotes id r t B → B ≤ E.forkChoice id r
  /-- **Voting rule at 4∆ round** (Alg. 2, l. 22). At `fastVoteRound t` an
  awake honest eligible validator votes for its fork-choice output. -/
  fast_vote_forkChoice :
    ∀ {id : Validator} {t : Slot},
      E.awakeHonest id (E.fastVoteRound t) → E.eligibleVote id t →
        E.votesFor id t (E.forkChoice id (E.fastVoteRound t))
  /-- **Leader recognition at 4∆ round** (Alg. 2, ll. 16, 19). When the honest
  leader `lead` of slot `t` is recognized by all awake honest validators, any
  awake honest validator's fork choice at `fastVoteRound t` equals `P*.B`. -/
  fast_forkChoice_of_leader :
    ∀ {lead id : Validator} {t : Slot},
      E.leader lead t → E.awakeHonest id (E.fastVoteRound t) →
        E.forkChoice id (E.fastVoteRound t) = E.proposalBlock lead t
  /-- **Synchrony + honest-majority bridge (4∆ timing)**. If at slot `t` every
  awake honest eligible voter voted for a descendant of `B` (at `fastVoteRound
  t`), and honest eligible voters outnumber adversary eligible voters, then any
  honest eligible voter at `fastVoteRound (t+1)` sees `B`'s descendants
  outvote every conflicting block. -/
  fast_outvotes_of_honest_majority :
    ∀ {id : Validator} {t : Slot} {B : Block},
      E.advEligible t < E.honEligible t →
      (∀ {v : Validator}, E.awakeHonest v (E.fastVoteRound t) → E.eligibleVote v t →
        E.votesForDescendant v t B) →
      E.awakeHonest id (E.fastVoteRound (t + 1)) → E.eligibleVote id (t + 1) →
        E.outvotes id (E.fastVoteRound (t + 1)) t B
  /-- **Fast confirmation propagates**. If `idc` fast confirmed `B` at slot `t`
  (i.e., `idc` saw > `(3/4+ε/2)·n·thr_v` votes for `B` and broadcast `B` with
  those votes at round `4∆t+2∆`), then by synchrony any honest eligible voter
  at `fastVoteRound (t+1)` sees `B`'s descendants outvote conflicting blocks. -/
  outvotes_of_fast_confirm :
    ∀ {idc id : Validator} {t : Slot} {B : Block},
      E.fastConfirms idc t B →
      E.awakeHonest id (E.fastVoteRound (t + 1)) → E.eligibleVote id (t + 1) →
        E.outvotes id (E.fastVoteRound (t + 1)) t B
  /-- **Fast confirmation from honest votes**. If all awake honest eligible
  voters at `fastVoteRound t` voted for `B`, then any validator awake at
  `fastConfirmRound t` fast confirms `B`. This captures the vote-counting
  argument (Prop. 1 + synchrony) for the optimistic fast-confirm clause of
  Theorem 6. -/
  confirms_of_honest_votes :
    ∀ {idc : Validator} {t : Slot} {B : Block},
      (∀ v : Validator, E.awakeHonest v (E.fastVoteRound t) → E.eligibleVote v t →
        E.votesFor v t B) →
      E.awakeHonest idc (E.fastConfirmRound t) →
        E.fastConfirms idc t B

end Goldfish
