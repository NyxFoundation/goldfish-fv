import Goldfish.Protocol
import Goldfish.Axioms

/-!
# Lemma 3 — vote persistence

> **Lemma 3** (IACR 2022/1171). Suppose a `(1/2, 3∆)`-compliant execution of
> Goldfish in the synchronous sleepy network model. Consider a slot `t` where all
> honest validators awake at round `3∆t + ∆` and eligible to vote at slot `t`
> vote for a descendant of `B`. Then, w.o.p., all honest validators awake at round
> `3∆(t + 1) + ∆` and eligible to vote at slot `t + 1` vote for a descendant of
> `B`.

The "w.o.p." comes solely from Lemma 1's honest-majority good event, threaded in
here as the hypothesis `HonestMajorityPerSlot E` (so the lemma is *fully proved*:
"good event ⇒ persistence"). The deterministic core is the paper's argument: by
synchrony every honest validator's later bvtree contains the previous slot's
honest votes, which (by the majority) outvote any conflicting block, so GHOST-Eph
returns a descendant of `B` and the validator votes for it. Those steps are the
`Spec` fields `outvotes_of_honest_majority`, `forkChoice_of_outvotes` and
`vote_forkChoice`.
-/

namespace Goldfish

variable {Block Validator : Type*} [BlockTree Block] {E : Execution Block Validator}

/-- **Lemma 3.** Given Lemma 1's honest-majority good event, if at slot `t` every
awake honest eligible voter votes for a descendant of `B`, then at slot `t + 1`
every awake honest eligible voter again votes for a descendant of `B`. -/
theorem lemma3 (S : Spec E) {t : Slot} {B : Block}
    (hmaj : HonestMajorityPerSlot E)
    (hprev : ∀ v : Validator, E.awakeHonest v (E.voteRound t) → E.eligibleVote v t →
      E.votesForDescendant v t B) :
    ∀ id : Validator, E.awakeHonest id (E.voteRound (t + 1)) → E.eligibleVote id (t + 1) →
      E.votesForDescendant id (t + 1) B := by
  intro id hawake helig
  have hout := S.outvotes_of_honest_majority (hmaj t) (fun {v} => hprev v) hawake helig
  exact ⟨_, S.forkChoice_of_outvotes hout, S.vote_forkChoice hawake helig⟩

end Goldfish
