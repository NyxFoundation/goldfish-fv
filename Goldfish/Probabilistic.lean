import Goldfish.Probabilistic.Basic

/-!
# Probabilistic layer (paper App. G)

The measure-theoretic foundation for replacing the good-event axioms
(`lemma1`, `lemma4`, `proposition1`) with proofs from the VRF-lottery randomness.

* `Goldfish.Probabilistic.Basic` — the `Lottery` probability model and
  `Lottery.honest_majority_bound`, the Chernoff/Hoeffding concentration estimate
  underlying Lemma 1's `HonestMajorityPerSlot` good event.
-/
