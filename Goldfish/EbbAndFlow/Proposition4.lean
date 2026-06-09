import Goldfish.EbbAndFlow.GadgetSpec
import Goldfish.EbbAndFlow.External

/-!
# Proposition 4 — iteration synchronization (analogue of [61, Prop. 3])

> **Proposition 4.** Consider a `(1/3, 3∆)`-compliant execution of Goldfish in
> the partially synchronous sleepy model. Suppose a block from iteration `c` was
> checkpointed in the view of an honest validator at round `r`. Then every honest
> validator enters iteration `c + 1` by round `max(GST, GAT, r) + ∆`.
>
> Moreover, once entrance times have synchronized (after
> `max(GST, GAT) + ∆ + Tchkpt`), if an honest validator enters an iteration at a
> round `r ≥ max(GST, GAT) + ∆ + Tchkpt`, every honest validator enters that
> iteration by `r + ∆`.

The Goldfish paper derives this from the proof of [61, Prop. 3]. Here the [61]
content is isolated in `ext61_bftAgreement` (BFT safety + synchronous delivery:
gadget votes seen by one honest validator are seen by all within `∆` after
`max(GST, GAT)`); the iteration-advance rule is the `GadgetSpec` mechanic
`entersIter_succ_of_acceptingVotes`. Proposition 4 combines the two.
-/

namespace Goldfish

variable {Block Validator : Type*} [BlockTree Block] {E : Execution Block Validator}

/-- **Proposition 4, part 1.** If a block `B` from iteration `c` is checkpointed
in an honest view at round `r` — witnessed by more than `2n/3` accepting gadget
votes (`acceptingVotes B c r`) — then every honest validator awake at round
`max(GST, GAT, r) + ∆` has entered iteration `c + 1` by that round. -/
theorem proposition4_enters_succ (G : Gadget E) (GS : GadgetSpec G)
    {B : Block} {c : ℕ} {r : Round} (hvotes : G.acceptingVotes B c r)
    {id : Validator} (hawake : E.awakeHonest id (max G.maxGAS r + E.Δ)) :
    G.entersIter id (c + 1) (max G.maxGAS r + E.Δ) :=
  GS.entersIter_succ_of_acceptingVotes (ext61_bftAgreement G hvotes) hawake

/-- **Proposition 4, part 2 (synchronization).** After entrance times have
synchronized (`max(GST, GAT) + ∆ + Tchkpt ≤ r`), if an honest validator enters
iteration `c + 1` at round `r`, then every honest validator awake at round
`r + ∆` enters iteration `c + 1` by round `r + ∆`. -/
theorem proposition4_sync (G : Gadget E) (GS : GadgetSpec G)
    {c : ℕ} {r : Round} {id : Validator}
    (hr : G.maxGAS + E.Δ + G.Tchkpt ≤ r) (henter : G.entersIter id (c + 1) r)
    {id' : Validator} (hawake : E.awakeHonest id' (r + E.Δ)) :
    G.entersIter id' (c + 1) (r + E.Δ) := by
  obtain ⟨B, hvotes⟩ := GS.acceptingVotes_of_entersIter_succ henter
  -- `omega` does not see through the `Round` abbreviation for these projection
  -- atoms (cf. `live_arith`'s ℕ-typed pattern), so chain `Nat.le_add_right`.
  have hle : G.maxGAS ≤ r :=
    (Nat.le_add_right G.maxGAS E.Δ).trans ((Nat.le_add_right _ G.Tchkpt).trans hr)
  have hmax : max G.maxGAS r = r := max_eq_right hle
  have hagree : G.acceptingVotes B c (r + E.Δ) := by
    have := ext61_bftAgreement G hvotes
    rwa [hmax] at this
  exact GS.entersIter_succ_of_acceptingVotes hagree hawake

end Goldfish
