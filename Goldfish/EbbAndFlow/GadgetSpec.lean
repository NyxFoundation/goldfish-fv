import Goldfish.EbbAndFlow.Basic

/-!
# `GadgetSpec` — accountability-gadget protocol mechanics

`GadgetSpec G` bundles the defining behaviour of the accountability gadget
(Alg. 4–6) as hypotheses, exactly as `Spec`/`Spec4Δ` do for the core protocol
(Barrier 3 of `README.md`). Every ebb-and-flow statement is
*derived* from `GadgetSpec` together with the external [61] axioms and the
probabilistic good events; an operational gadget model can discharge these
fields later without changing any statement.

Fields are introduced as the proofs need them; each is a gadget *mechanic*
(a consequence of the iteration / checkpoint / gadget-vote rules), never a
consequence of a numbered Goldfish statement, so the derivations stay
non-circular.
-/

namespace Goldfish

/-- Protocol-mechanic bridges of the accountability gadget over a `Gadget`
interface. -/
structure GadgetSpec {Block Validator : Type*} [BlockTree Block]
    {E : Execution Block Validator} (G : Gadget E) : Prop where
  /-- **Iteration-advance rule** (Alg. 5/6). A validator that, by round `r`, sees
  more than `2n/3` accepting gadget votes for an iteration-`c` checkpoint `B`
  enters iteration `c+1` at round `r`. -/
  entersIter_succ_of_acceptingVotes :
    ∀ {B : Block} {c : ℕ} {r : Round} {id : Validator},
      G.acceptingVotes B c r → E.awakeHonest id r → G.entersIter id (c + 1) r
  /-- **Iteration-advance witness** (Alg. 5/6, converse). A validator enters
  iteration `c+1` only after it has, by that round, seen enough accepting gadget
  votes for *some* iteration-`c` checkpoint. -/
  acceptingVotes_of_entersIter_succ :
    ∀ {c : ℕ} {r : Round} {id : Validator},
      G.entersIter id (c + 1) r → ∃ B : Block, G.acceptingVotes B c r
  /-- **Checkpoints anchor to honest proposals** (Alg. 4, l. 9 + the κ-deep
  confirmation rule). Honest validators send an accepting gadget vote only for a
  block confirmed `κ` slots deep, and such a block lies in the prefix of the
  block proposed by the recognized honest leader of its window (the honest leader
  exists w.o.p. by Lemma 1). Hence every checkpointed block is a prefix of some
  recognized leader's proposal `P*.B`. The *stability* of that proposal is then
  supplied by Theorem 1, not by this field. -/
  proposal_of_checkpointed :
    ∀ {id : Validator} {r : Round} {B : Block},
      G.checkpointed id r B →
        ∃ (lead : Validator) (t : Slot), E.leader lead t ∧ B ≤ E.proposalBlock lead t

end Goldfish
