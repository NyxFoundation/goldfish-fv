import Goldfish.Probabilistic.Basic
import Goldfish.Probabilistic.CountBound

/-!
# Probabilistic layer (paper App. G)

The measure-theoretic foundation for replacing the good-event axioms
(`lemma1`, `lemma4`, `proposition1`) with proofs from the VRF-lottery randomness.

* `Goldfish.Probabilistic.Basic` — the `Lottery` probability model and
  `Lottery.honest_majority_bound`, the Chernoff/Hoeffding concentration estimate
  underlying Lemma 1's `HonestMajorityPerSlot` good event.
* `Goldfish.Probabilistic.CountBound` — the `CountLottery` model and the
  upper-tail estimates (`upper_tail_bound`, `exceeds_bound_union`) underlying
  Proposition 1's eligible-voter count bounds.
-/
