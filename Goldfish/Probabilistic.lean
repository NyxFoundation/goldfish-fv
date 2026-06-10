import Goldfish.Probabilistic.Basic

/-!
# Probabilistic layer (paper App. G)

The measure-theoretic foundation that the Phase-2 issues (#23–#25) build on to
replace the Phase-1 good-event axioms (`lemma1`, `lemma4`, `proposition1`) with
proofs from the VRF-lottery randomness.

* `Goldfish.Probabilistic.Basic` — the `Lottery` probability model and
  `Lottery.honest_majority_bound`, the Chernoff/Hoeffding concentration estimate
  underlying Lemma 1's `HonestMajorityPerSlot` good event.
-/
