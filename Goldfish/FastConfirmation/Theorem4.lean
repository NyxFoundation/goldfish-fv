import Goldfish.FastConfirmation.Lemma5

/-!
# Theorem 4 — fast-confirmed block stays in every honest chain

> **Theorem 4** (IACR 2022/1171). Suppose the Goldfish execution is
> `(1/2, 4∆)`-compliant, and an honest validator `idc` fast confirms a block `B`
> at slot `t`. Then, w.o.p., `B ⪯ B'` for any `B'` identified in Alg. 2,
> ll. 8, 22, 28 by any awake honest validator at any round `r ≥ 4∆(t+1)+∆`.

The proof mirrors Theorem 1. **Base case**: Lemma 5 provides the slot `t+1`
voting claim. **Inductive step**: `FastSpec.fast_outvotes_of_honest_majority`
(the 4∆ analogue of Lemma 3's persistence argument) propagates the vote claim
one slot forward. The helper `all_votes_fast` proves by induction that for all
`t' ≥ t+1` every honest eligible voter votes for a descendant of `B`. Theorem 4
then extracts `B ≤ forkChoice` from that via one more `fast_outvotes_of_honest_majority`
+ `forkChoice_of_outvotes`. No `sorry`.
-/

namespace Goldfish

variable {Block Validator : Type*} [BlockTree Block] {E : Execution Block Validator}

/-- Induction workhorse: from Lemma 5 (base) and `fast_outvotes_of_honest_majority`
(step), for all `t' ≥ t+1` every awake honest eligible voter votes for a
descendant of `B`. -/
private theorem all_votes_fast (FS : FastSpec E) {idc : Validator} {t : Slot} {B : Block}
    (hmaj : HonestMajorityPerSlot E)
    (hfc : E.fastConfirms idc t B) :
    ∀ t' : Slot, t + 1 ≤ t' → ∀ id : Validator,
      E.awakeHonest id (E.fastVoteRound t') → E.eligibleVote id t' →
      E.votesForDescendant id t' B := by
  intro t' ht'
  induction t', ht' using Nat.le_induction with
  | base => exact fun id hawake helig => lemma5 FS hfc hawake helig
  | succ n _ ih =>
    intro id hawake helig
    have hout := FS.fast_outvotes_of_honest_majority (hmaj n) (fun {v} => ih v) hawake helig
    exact ⟨_, FS.forkChoice_of_outvotes hout, FS.fast_vote_forkChoice hawake helig⟩

/-- **Theorem 4.** Given `HonestMajorityPerSlot` (Lemma 4's good event), if
`idc` fast confirmed `B` at slot `t`, then `B` is a prefix of the fork choice
of every awake honest eligible voter at `fastVoteRound t'` for every `t' > t`. -/
theorem theorem4 (FS : FastSpec E) {idc : Validator} {t : Slot} {B : Block}
    (hmaj : HonestMajorityPerSlot E)
    (hfc : E.fastConfirms idc t B) :
    ∀ t' : Slot, t < t' → ∀ id : Validator,
      E.awakeHonest id (E.fastVoteRound t') → E.eligibleVote id t' →
      B ≤ E.forkChoice id (E.fastVoteRound t') := by
  intro t' ht' id hawake helig
  rcases t' with _ | s
  · exact absurd ht' (Nat.not_lt_zero t)
  · -- ht' : t < s + 1, i.e. t ≤ s. Split on t < s vs t = s.
    rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp ht') with hs | rfl
    · -- t < s: all_votes_fast gives votes at s, then majority → fork choice at s+1
      have hprev := all_votes_fast FS hmaj hfc s (Nat.succ_le_of_lt hs)
      have hout :=
        FS.fast_outvotes_of_honest_majority (hmaj s) (fun {v} => hprev v) hawake helig
      exact FS.forkChoice_of_outvotes hout
    · -- t = s: t' = t + 1; use outvotes_of_fast_confirm directly
      exact FS.forkChoice_of_outvotes (FS.outvotes_of_fast_confirm hfc hawake helig)

end Goldfish
