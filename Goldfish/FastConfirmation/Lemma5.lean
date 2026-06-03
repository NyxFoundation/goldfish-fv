import Goldfish.FastConfirmation.FastSpec

/-!
# Lemma 5 — fast-confirmed block ⇒ honest validators vote for a descendant next slot

> **Lemma 5** (IACR 2022/1171). Suppose the Goldfish execution is
> `(1/2, 4∆)`-compliant in the synchronous sleepy network model, and an honest
> validator `idc` fast confirms a block `B` at slot `t`. Then, w.o.p., all honest
> validators awake at round `4∆(t+1)+∆` and eligible to vote at slot `t+1` vote
> for a descendant of `B` at slot `t+1`.

The fast-confirmation broadcast at round `4∆t+2∆` reaches every honest validator
by `4∆(t+1)+∆` (synchrony). By the `outvotes_of_fast_confirm` mechanic in
`FastSpec`, any honest eligible voter at `fastVoteRound (t+1)` sees `B`'s
descendants outvote conflicting blocks; the voting rule then delivers the
`votesForDescendant` conclusion. No `sorry`.
-/

namespace Goldfish

variable {Block Validator : Type*} [BlockTree Block] {E : Execution Block Validator}

/-- **Lemma 5.** If `idc` fast confirmed `B` at slot `t`, then every honest
validator awake and eligible at `fastVoteRound (t+1)` votes for a descendant
of `B`. -/
theorem lemma5 (FS : FastSpec E) {idc id : Validator} {t : Slot} {B : Block}
    (hfc : E.fastConfirms idc t B)
    (hawake : E.awakeHonest id (E.fastVoteRound (t + 1)))
    (helig : E.eligibleVote id (t + 1)) :
    E.votesForDescendant id (t + 1) B := by
  have hout := FS.outvotes_of_fast_confirm hfc hawake helig
  exact ⟨_, FS.forkChoice_of_outvotes hout, FS.fast_vote_forkChoice hawake helig⟩

end Goldfish
