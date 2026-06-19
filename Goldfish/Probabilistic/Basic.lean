import Mathlib.Probability.Moments.SubGaussian
import Goldfish.Basic

/-!
# Probabilistic foundation — the Chernoff core of Lemma 1 (paper App. G)

The probabilistic "w.o.p." facts of Goldfish (Lemma 1 / Lemma 4 / Proposition 1)
are declared as deterministic good-event axioms in `Goldfish.Axioms` and threaded
as hypotheses. This layer replaces those axioms with measure-theoretic proofs
from the VRF-lottery randomness.

This module is the **foundation** for that replacement: it models the per-slot
eligibility lottery as a probability space and proves the central concentration
estimate — that the adversary eligible-voter count exceeds the honest count only
with exponentially small probability. This is the Chernoff/Hoeffding core
underlying Lemma 1's `HonestMajorityPerSlot` good event.

It does **not** yet discharge the `lemma1` axiom: that additionally requires
(i) constructing the counts as sums of independent per-validator Bernoulli
eligibility indicators (Mathlib's `measure_sum_ge_le_of_iIndepFun` +
`hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`), and (ii) a union bound over
the polynomially-many slots of the horizon to land in `Negligible`. Those steps
build directly on `honest_majority_bound` below.

We write expectations as explicit Bochner integrals `∫ ω, X ω ∂μ` rather than the
scoped `μ[X]` notation, which is ambiguous with list `GetElem` here.
-/

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

namespace Goldfish

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- A **per-slot eligibility lottery**. Over a probability space `(Ω, μ)` it
carries, for each slot, the honest and adversary eligible-voter counts as
*independent* random variables whose centered versions are *sub-Gaussian* (with
parameters `cHon`, `cAdv`), and whose means satisfy the strict gap guaranteed by
`(1/2, 3∆)`-compliance: the expected adversary count is below the expected honest
count at every slot.

These are exactly the hypotheses that the VRF lottery supplies (each count is a
sum of bounded independent indicators, hence sub-Gaussian by Hoeffding's lemma,
and the compliance bound forces the mean gap). Abstracting them here lets the
concentration estimate be proved once, independently of the indicator
construction. -/
structure Lottery (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] where
  /-- Honest eligible-voter count at a slot. -/
  honCount : Slot → Ω → ℝ
  /-- Adversary eligible-voter count at a slot. -/
  advCount : Slot → Ω → ℝ
  /-- Sub-Gaussian parameter of the honest count. -/
  cHon : ℝ≥0
  /-- Sub-Gaussian parameter of the adversary count. -/
  cAdv : ℝ≥0
  /-- The centered honest count is sub-Gaussian. -/
  hon_subG : ∀ t : Slot,
    HasSubgaussianMGF (fun ω => honCount t ω - ∫ x, honCount t x ∂μ) cHon μ
  /-- The centered adversary count is sub-Gaussian. -/
  adv_subG : ∀ t : Slot,
    HasSubgaussianMGF (fun ω => advCount t ω - ∫ x, advCount t x ∂μ) cAdv μ
  /-- At each slot the honest and adversary counts are independent. -/
  indep : ∀ t : Slot, IndepFun (honCount t) (advCount t) μ
  /-- `(1/2, 3∆)`-compliance: the expected adversary count is strictly below the
  expected honest count at every slot. -/
  mean_gap : ∀ t : Slot, (∫ ω, advCount t ω ∂μ) < ∫ ω, honCount t ω ∂μ

namespace Lottery

variable [IsProbabilityMeasure μ] (L : Lottery Ω μ)

/-- **Honest-majority concentration (Chernoff core of Lemma 1).** At every slot
the probability of an adversary eligible-voter majority — the honest count
failing to exceed the adversary count — decays exponentially in the squared mean
gap `(E[honCount] − E[advCount])²`:
`P(honCount ≤ advCount) ≤ exp(−(E[advCount] − E[honCount])² / (2 (cHon + cAdv)))`.

Immediate from Hoeffding's two-sided bound for independent sub-Gaussian variables
(`HasSubgaussianMGF.measureReal_le_le_exp`) applied to the centered counts. -/
theorem honest_majority_bound (t : Slot) :
    μ.real {ω | L.honCount t ω ≤ L.advCount t ω} ≤
      exp (-((∫ ω, L.advCount t ω ∂μ) - ∫ ω, L.honCount t ω ∂μ) ^ 2
        / (2 * (L.cHon + L.cAdv))) :=
  HasSubgaussianMGF.measureReal_le_le_exp (L.hon_subG t) (L.adv_subG t)
    (L.indep t) (le_of_lt (L.mean_gap t))

end Lottery

end Goldfish
