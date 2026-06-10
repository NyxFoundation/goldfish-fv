import Goldfish.EbbAndFlow.Basic

/-!
# `GadgetSpec` — accountability-gadget protocol mechanics

`GadgetSpec G` bundles the defining behaviour of the accountability gadget
(Alg. 4–6) as hypotheses, exactly as `Spec`/`Spec4Δ` do for the core protocol
(Barrier 3 of `docs/formalization-strategy.md`). Every Track-C statement is
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

end Goldfish
