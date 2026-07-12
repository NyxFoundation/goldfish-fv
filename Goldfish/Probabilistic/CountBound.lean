import Mathlib.Probability.Moments.SubGaussian
import Goldfish.Basic

/-!
# Eligible-voter count bounds — the Chernoff core of Proposition 1 (paper App. G)

Proposition 1 (IACR 2022/1171) claims that w.o.p. the number of validators
eligible to vote at any slot of a `poly(κ)` horizon stays below
`voterUB = (1+ε)·n·thr_v`, and (under `(1/2, 4∆)`-compliance) that the adversary
eligible-voter count stays below `advUB = ½·n·thr_v`. Both halves are *upper-tail*
concentration statements about a per-slot eligible-voter count.

This module proves that core. A `CountLottery` abstracts a per-slot count random
variable whose centered version is sub-Gaussian — exactly what the VRF lottery
supplies, since each count is a sum of bounded independent per-validator
eligibility indicators (Hoeffding's lemma). The one-sided sub-Gaussian tail bound
(`HasSubgaussianMGF.measure_ge_le`) then gives the per-slot exponential decay,
and a union bound over the polynomially-sized horizon gives the `w.o.p.` shape.

Both halves of Proposition 1 are instances: apply the horizon bound to the total
eligible count with `UB = voterUB` and to the adversary eligible count with
`UB` strictly below `advUB` (a count below `UB` is in particular `< advUB`).

As in `Goldfish.Probabilistic.Basic`, expectations are written as explicit
Bochner integrals `∫ ω, X ω ∂μ` (the scoped `μ[X]` notation clashes with list
`GetElem`).
-/

open MeasureTheory ProbabilityTheory Real

open scoped NNReal ENNReal

namespace Goldfish

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- A **per-slot eligible-voter count lottery**. Over a probability space
`(Ω, μ)` it carries, for each slot, an eligible-voter count random variable
whose centered version is sub-Gaussian with parameter `c`.

This is what the VRF lottery supplies: the count is a sum of bounded independent
per-validator Bernoulli eligibility indicators, hence sub-Gaussian by
Hoeffding's lemma. Abstracting it here lets the upper-tail estimate of
Proposition 1 be proved once, for the total count and the adversary count
alike. -/
structure CountLottery (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] where
  /-- Eligible-voter count at a slot. -/
  count : Slot → Ω → ℝ
  /-- Sub-Gaussian parameter of the count. -/
  c : ℝ≥0
  /-- The centered count is sub-Gaussian. -/
  subG : ∀ t : Slot,
    HasSubgaussianMGF (fun ω => count t ω - ∫ x, count t x ∂μ) c μ

namespace CountLottery

variable [IsProbabilityMeasure μ] (L : CountLottery Ω μ)

/-- **Per-slot upper-tail bound (Chernoff core of Proposition 1).** The count
exceeds its mean by a margin `g ≥ 0` with probability at most
`exp (−g² / (2c))`. Immediate from the one-sided sub-Gaussian tail bound
applied to the centered count. -/
theorem upper_tail_bound (t : Slot) {g : ℝ} (hg : 0 ≤ g) :
    μ.real {ω | (∫ x, L.count t x ∂μ) + g ≤ L.count t ω} ≤
      exp (-g ^ 2 / (2 * L.c)) := by
  have hset : {ω | (∫ x, L.count t x ∂μ) + g ≤ L.count t ω}
      = {ω | g ≤ L.count t ω - ∫ x, L.count t x ∂μ} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    constructor <;> intro h <;> linarith
  rw [hset]
  exact (L.subG t).measure_ge_le hg

/-- **Per-slot bound-exceedance estimate.** If the target upper bound `UB` sits
at least a margin `g` above the mean, the count reaches `UB` with probability at
most `exp (−g² / (2c))`. This is the per-slot form of both halves of
Proposition 1 (`UB = voterUB` for the total count, `UB` below `advUB` for the
adversary count). -/
theorem exceeds_bound (t : Slot) {UB g : ℝ} (hg : 0 ≤ g)
    (hUB : (∫ x, L.count t x ∂μ) + g ≤ UB) :
    μ.real {ω | UB ≤ L.count t ω} ≤ exp (-g ^ 2 / (2 * L.c)) := by
  refine le_trans (measureReal_mono ?_) (L.upper_tail_bound t hg)
  intro ω hω
  exact le_trans hUB hω

/-- **Horizon union bound (the `w.o.p.` shape of Proposition 1).** If at every
slot of a finite horizon `H` the slot's upper bound `UB t` sits at least a
uniform margin `g` above the mean count, then the probability that the count
reaches its bound at *some* slot of the horizon is at most
`|H| · exp (−g² / (2c))`. With `g` growing like the security parameter and `|H|`
polynomial, this is negligible — Proposition 1's `w.o.p.` claim. -/
theorem exceeds_bound_union (H : Finset Slot) (UB : Slot → ℝ) {g : ℝ}
    (hg : 0 ≤ g) (hUB : ∀ t ∈ H, (∫ x, L.count t x ∂μ) + g ≤ UB t) :
    μ.real {ω | ∃ t ∈ H, UB t ≤ L.count t ω} ≤
      H.card * exp (-g ^ 2 / (2 * L.c)) := by
  have hset : {ω | ∃ t ∈ H, UB t ≤ L.count t ω}
      = ⋃ t ∈ H, {ω | UB t ≤ L.count t ω} := by
    ext ω; simp
  rw [hset]
  refine (measureReal_biUnion_finset_le H _).trans ?_
  calc ∑ t ∈ H, μ.real {ω | UB t ≤ L.count t ω}
      ≤ ∑ _t ∈ H, exp (-g ^ 2 / (2 * L.c)) :=
        Finset.sum_le_sum fun t ht => L.exceeds_bound t hg (hUB t ht)
    _ = H.card * exp (-g ^ 2 / (2 * L.c)) := by
        rw [Finset.sum_const, nsmul_eq_mul]

end CountLottery

end Goldfish
