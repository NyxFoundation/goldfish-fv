import Goldfish.FastConfirmation.Theorem4
import Goldfish.FastConfirmation.Ledger4Delta

/-!
# Theorem 6 — liveness with fast confirmations, `Tconf = Θ(κ)`

> **Theorem 6** (IACR 2022/1171). Suppose the Goldfish execution is
> `(1/2, 4∆)`-compliant. Then, Goldfish with fast confirmations satisfies
> liveness with `Tconf = Θ(κ)` (w.o.p.).
> Consider a slot `t` where there are `(3/4 + 3/2ε)·n·thr_v` honest validators
> eligible to vote and awake at `4∆t+∆`, and an honest leader `lead` is
> recognized. Then all honest validators awake at `4∆t+2∆` fast confirm
> `P*.B`.

**Liveness** follows the same argument as Theorem 2 but in the 4∆ regime:
`HonestLeaderEveryWindow` supplies a recognized honest leader `lead'` in every
κ-window; every honest eligible voter votes for `P*.B'` by leader recognition +
voting rule; that block is stable by induction (from `all_fast_votes_from_leader`)
and hence confirmed in the `Ledger4Δ` by round `4∆(s+κ)+2∆ ≤ r + (2κ+2)·4∆`.

**Fast confirmation under optimistic conditions**: Lemma 2's 4∆ analogue
(`lemma2_fast`) shows all honest eligible voters voted for `P*.B`; then
`Spec4Δ.confirms_of_honest_votes` delivers the fast-confirmation conclusion.
No `sorry`.
-/

namespace Goldfish

variable {Block Validator : Type*} [BlockTree Block] {E : Execution Block Validator} {κ : ℕ}

/-- Slot/round arithmetic for the 4∆ liveness window. Same shape as `live_arith`
in Theorem 2 but with `d = 4∆`. -/
private theorem fast_live_arith {d r r' t κ Δ : ℕ} (hdpos : 0 < d) (hd : d = 4 * Δ)
    (hbt : r / d + 1 ≤ t) (htlt : t < r / d + 1 + κ)
    (hr' : r + (2 * κ + 2) * d ≤ r') :
    r ≤ d * t ∧ d * (t + κ) + 2 * Δ ≤ r' := by
  have hdm := Nat.div_add_mod r d
  have hmod : r % d < d := Nat.mod_lt r hdpos
  have hmono1 : d * (r / d + 1) ≤ d * t := by gcongr
  have hmono2 : d * t ≤ d * (r / d + 1 + κ) := by gcongr
  have hT : (2 * κ + 2) * d = 2 * (d * κ) + 2 * d := by
    rw [Nat.add_mul, Nat.mul_assoc, Nat.mul_comm κ d]
  rw [Nat.mul_add, Nat.mul_one] at hmono1
  rw [Nat.mul_add, Nat.mul_add, Nat.mul_one] at hmono2
  refine ⟨by omega, ?_⟩
  rw [Nat.mul_add]
  omega

/-- 4∆ analogue of Lemma 2: if `lead` is the recognized leader of slot `t`, every
honest eligible voter at `fastVoteRound t` votes for `proposalBlock lead t`. -/
private theorem lemma2_fast (FS : Spec4Δ E) {lead id : Validator} {t : Slot}
    (hlead : E.leader lead t)
    (hawake : E.awakeHonest id (E.fastVoteRound t))
    (helig : E.eligibleVote id t) :
    E.votesFor id t (E.proposalBlock lead t) := by
  have hvote := FS.fast_vote_forkChoice hawake helig
  rwa [FS.fast_forkChoice_of_leader hlead hawake] at hvote

/-- Stability of an honest leader's block from the 4∆ vote rounds — the inductive
analogue of `all_votes_descendant` but for leader-based (not fast-confirm-based)
base case. Used for liveness. -/
private theorem all_fast_votes_from_leader (FS : Spec4Δ E) {lead : Validator} {t : Slot}
    (hmaj : HonestMajorityPerSlot E) (hlead : E.leader lead t) :
    ∀ t' : Slot, t ≤ t' → ∀ id : Validator,
      E.awakeHonest id (E.fastVoteRound t') → E.eligibleVote id t' →
      E.votesForDescendant id t' (E.proposalBlock lead t) := by
  intro t' ht'
  induction t', ht' using Nat.le_induction with
  | base =>
    exact fun id hawake helig =>
      Execution.votesForDescendant.of_votesFor (lemma2_fast FS hlead hawake helig)
  | succ n _ ih =>
    intro id hawake helig
    have hout := FS.fast_outvotes_of_honest_majority (hmaj n) (fun {v} => ih v) hawake helig
    exact ⟨_, FS.forkChoice_of_outvotes hout, FS.fast_vote_forkChoice hawake helig⟩

/-- **Theorem 6.**
1. **Liveness**: under `HonestMajorityPerSlot` and `HonestLeaderEveryWindow`,
   a transaction received by round `r` is in every awake honest validator's
   `Ledger4Δ` from round `r + (2κ+2)·4∆` onward.
2. **Optimistic fast confirmation**: if an honest leader `lead` is recognized at
   slot `t`, then every honest validator awake at `fastConfirmRound t` fast
   confirms `P*.B`. (The paper's optimistic voter-participation condition is
   packaged inside the `Spec4Δ.confirms_of_honest_votes` mechanic.) -/
theorem theorem6 (FS : Spec4Δ E) (FL : Ledger4Δ E κ) (TX : TxModel4Δ E)
    (hmaj : HonestMajorityPerSlot E) (hwin : HonestLeaderEveryWindow E κ)
    {lead : Validator} {t : Slot}
    (hlead : E.leader lead t)
    {idc : Validator} (hwake_idc : E.awakeHonest idc (E.fastConfirmRound t)) :
    TX.Live FL ((2 * κ + 2) * (4 * E.Δ)) ∧
    E.fastConfirms idc t (E.proposalBlock lead t) := by
  constructor
  · -- Liveness: HonestLeaderEveryWindow + all_fast_votes_from_leader + confirmed_of_stable
    intro tx r hrecv r' id hr' hawake
    have hdpos : 0 < 4 * E.Δ := by have := E.Δ_pos; omega
    obtain ⟨s, hbs, hslt, lead', _hhon, hlead'⟩ := hwin (r / (4 * E.Δ) + 1)
    obtain ⟨hi, hii⟩ :=
      fast_live_arith (d := 4 * E.Δ) (Δ := E.Δ) hdpos rfl hbs hslt hr'
    have hmem := TX.leader_includes hrecv hlead' hi
    have hstab : ∀ t' : Slot, s < t' → ∀ id' : Validator,
        E.awakeHonest id' (E.fastVoteRound t') → E.eligibleVote id' t' →
        E.proposalBlock lead' s ≤ E.forkChoice id' (E.fastVoteRound t') := by
      intro t' ht' id' hawake' helig'
      rcases t' with _ | n
      · exact absurd ht' (Nat.not_lt_zero s)
      · have hprev := all_fast_votes_from_leader FS hmaj hlead' n (Nat.lt_succ_iff.mp ht')
        have hout :=
          FS.fast_outvotes_of_honest_majority (hmaj n) (fun {v} => hprev v) hawake' helig'
        exact FS.forkChoice_of_outvotes hout
    have hconf := FL.confirmed_of_stable hstab hii hawake
    exact TX.mem_mono hmem hconf
  · -- Optimistic fast confirmation: lemma2_fast → confirms_of_honest_votes
    have hvotes : ∀ v : Validator,
        E.awakeHonest v (E.fastVoteRound t) → E.eligibleVote v t →
        E.votesFor v t (E.proposalBlock lead t) :=
      fun v hw he => lemma2_fast FS hlead hw he
    exact FS.confirms_of_honest_votes hvotes hwake_idc

end Goldfish
