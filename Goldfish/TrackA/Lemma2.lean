import Goldfish.Protocol

/-!
# Lemma 2 — honest recognized leader ⇒ all awake honest eligible voters vote for `P*.B`

> **Lemma 2** (IACR 2022/1171). Suppose an execution of Goldfish in the
> synchronous sleepy network model, and validator `id*` with proposal `P*` is
> recognized as leader of a slot `t` by all awake honest validators at round
> `3∆t + ∆` (Alg. 2, l. 16). Then, all honest validators awake at round `3∆t + ∆`
> and eligible to vote at `t` vote for `P*.B` at `t`.

Deterministic (no probabilistic premise). The paper's proof is the bvtree-merge
argument: recognition forces every awake honest validator's bvtree to become
`T' ∪ {P*.B}`, after which GHOST-Eph returns `P*.B`, so the voter votes for it.
Both steps are protocol mechanics, captured here by the `Spec` fields
`forkChoice_of_leader` (recognition ⇒ fork choice is `P*.B`) and
`vote_forkChoice` (the voting rule). The lemma is their composition.
-/

namespace Goldfish

variable {Block Validator : Type*} [BlockTree Block] {E : Execution Block Validator}

/-- **Lemma 2.** If `lead` is the recognized leader of slot `t`, then every
validator awake and honest at the vote round `3∆t+∆` and eligible to vote at `t`
casts its slot-`t` vote for the leader's proposed block `P*.B`. -/
theorem lemma2 (S : Spec E) {lead id : Validator} {t : Slot}
    (hlead : E.leader lead t)
    (hawake : E.awakeHonest id (E.voteRound t))
    (helig : E.eligibleVote id t) :
    E.votesFor id t (E.proposalBlock lead t) := by
  have hvote := S.vote_forkChoice hawake helig
  rwa [S.forkChoice_of_leader hlead hawake] at hvote

end Goldfish
