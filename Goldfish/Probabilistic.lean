import Goldfish.Probabilistic.Basic
import Goldfish.Probabilistic.CountBound
import Goldfish.Probabilistic.LeaderWindow

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
* `Goldfish.Probabilistic.LeaderWindow` — the `LeaderLottery` model and the
  window bounds (`window_fail_bound`, `no_leader_window_union_bound`)
  underlying Lemma 4's `HonestLeaderEveryWindow` good event (its
  honest-majority half is covered by the timing-agnostic `Lottery` model).
-/
