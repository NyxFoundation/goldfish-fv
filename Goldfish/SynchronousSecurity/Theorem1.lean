import Goldfish.SynchronousSecurity.Lemma2
import Goldfish.SynchronousSecurity.Lemma3

/-!
# Theorem 1 — an honest leader's proposal stays in every awake honest chain

> **Theorem 1** (IACR 2022/1171). Suppose a `(1/2, 3∆)`-compliant execution of
> Goldfish in the synchronous sleepy network model, and validator `id` with
> proposal `P*` is recognized as the leader of a slot `t` by all awake honest
> validators at round `3∆t + ∆`. Then, w.o.p., `P*.B ⪯ B` for any `B` identified
> in Alg. 2, ll. 8, 22, 28 by any awake honest validator in any round
> `r ≥ 3∆t + 2∆`.

The paper proves, by induction from Lemmas 1–3, that w.o.p. for all `t' ≥ t`
every awake honest eligible voter votes for a descendant of `P*.B`; the fork
choice then returns a descendant of `P*.B` at the later rounds.

We thread Lemma 1's good event (`HonestMajorityPerSlot`) as a hypothesis. The
induction `all_votes_descendant` has base case Lemma 2 and inductive step
Lemma 3. The conclusion is rendered at the level of the abstract `forkChoice`:
the leader's block is a prefix of every awake honest validator's canonical chain
at the vote round of every later slot. (A finer round model would index the three
GHOST-Eph invocations of ll. 8/22/28 separately; they are the same statement
about `forkChoice`.)
-/

namespace Goldfish

variable {Block Validator : Type*} [BlockTree Block] {E : Execution Block Validator}

/-- The induction at the heart of Theorem 1: from Lemmas 2 and 3, for every slot
`t' ≥ t` all awake honest eligible voters vote for a descendant of the recognized
leader's block `P*.B`. -/
theorem all_votes_descendant (S : Spec E) {lead : Validator} {t : Slot}
    (hmaj : HonestMajorityPerSlot E) (hlead : E.leader lead t) :
    ∀ t' : Slot, t ≤ t' → ∀ id : Validator,
      E.awakeHonest id (E.voteRound t') → E.eligibleVote id t' →
      E.votesForDescendant id t' (E.proposalBlock lead t) := by
  intro t' ht'
  induction t', ht' using Nat.le_induction with
  | base =>
    intro id hawake helig
    exact Execution.votesForDescendant.of_votesFor (lemma2 S hlead hawake helig)
  | succ n _ ih => exact lemma3 S hmaj ih

/-- **Theorem 1.** Given Lemma 1's good event, if `lead` is the recognized leader
of slot `t`, then `P*.B = proposalBlock lead t` is a prefix of the fork choice of
every awake honest eligible voter at the vote round of every later slot. -/
theorem theorem1 (S : Spec E) {lead : Validator} {t : Slot}
    (hmaj : HonestMajorityPerSlot E) (hlead : E.leader lead t) :
    ∀ t' : Slot, t < t' → ∀ id : Validator,
      E.awakeHonest id (E.voteRound t') → E.eligibleVote id t' →
      E.proposalBlock lead t ≤ E.forkChoice id (E.voteRound t') := by
  intro t' ht' id hawake helig
  rcases t' with _ | s
  · exact absurd ht' (Nat.not_lt_zero t)
  · have hprev := all_votes_descendant S hmaj hlead s (Nat.lt_succ_iff.mp ht')
    have hout := S.outvotes_of_honest_majority (hmaj s) (fun {v} => hprev v) hawake helig
    exact S.forkChoice_of_outvotes hout

end Goldfish
