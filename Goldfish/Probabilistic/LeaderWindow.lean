import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Real
import Goldfish.Basic

/-!
# Honest-leader window bounds — the probabilistic core of Lemma 4 (paper App. G)

Lemma 4 (IACR 2022/1171) claims two good events for `(1/2, 4∆)`-compliant
executions: `HonestMajorityPerSlot` and `HonestLeaderEveryWindow`. The
honest-majority half is the same concentration estimate as Lemma 1 — the
`Lottery` model of `Goldfish.Probabilistic.Basic` is timing-agnostic (`3∆` vs
`4∆` only changes how the `mean_gap` hypothesis is justified), so
`Lottery.honest_majority_bound` and its union bounds already cover it.

This module proves the *leader* half. The per-slot VRF leader lotteries are
independent, and in each slot the event that no honest leader is recognized has
probability at most some `q < 1` (an honest awake validator wins the leader
lottery and is recognized with constant probability). A `LeaderLottery`
abstracts exactly that: independent per-slot failure events with a uniform
probability ceiling. The probability that an entire `κ`-slot window fails is
then the product of the per-slot probabilities — at most `q ^ κ`, exponentially
small in the security parameter — and a union bound over the polynomially many
windows of the horizon gives the `w.o.p.` shape of `HonestLeaderEveryWindow`.
-/

open MeasureTheory ProbabilityTheory

open scoped NNReal ENNReal

namespace Goldfish

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- A **per-slot leader lottery**. Over a probability space `(Ω, μ)` it carries,
for each slot, the *failure* event that no honest leader is recognized in that
slot. The events are independent across slots (fresh VRF evaluations) and each
has probability at most `q`.

The paper's leader lottery supplies these hypotheses with `q < 1`: in every
slot, with probability bounded away from zero, an awake honest validator wins
the leader lottery and its block is recognized by all awake honest validators at
the vote round. -/
structure LeaderLottery (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] where
  /-- Event that slot `t` has no recognized honest leader. -/
  noHonestLeader : Slot → Set Ω
  /-- Each failure event is measurable. -/
  measurable : ∀ t : Slot, MeasurableSet (noHonestLeader t)
  /-- The failure events of distinct slots are independent. -/
  indep : iIndepSet noHonestLeader μ
  /-- Per-slot failure probability ceiling. -/
  q : ℝ≥0
  /-- No slot fails with probability above `q`. -/
  fail_prob : ∀ t : Slot, μ.real (noHonestLeader t) ≤ q

namespace LeaderLottery

variable [IsProbabilityMeasure μ] (L : LeaderLottery Ω μ)

/-- **Window failure bound (probabilistic core of Lemma 4).** The probability
that *every* slot of the window `[t, t+κ)` lacks a recognized honest leader is
at most `q ^ κ`: by independence the window failure probability is the product
of the per-slot failure probabilities. With `q < 1` and `κ` the security
parameter, this is exponentially small — the per-window content of
`HonestLeaderEveryWindow`. -/
theorem window_fail_bound (t : Slot) (κ : ℕ) :
    μ.real (⋂ s ∈ Finset.Ico t (t + κ), L.noHonestLeader s) ≤ L.q ^ κ := by
  have hprod : μ (⋂ s ∈ Finset.Ico t (t + κ), L.noHonestLeader s)
      = ∏ s ∈ Finset.Ico t (t + κ), μ (L.noHonestLeader s) :=
    L.indep.meas_biInter _
  have hreal : μ.real (⋂ s ∈ Finset.Ico t (t + κ), L.noHonestLeader s)
      = ∏ s ∈ Finset.Ico t (t + κ), μ.real (L.noHonestLeader s) := by
    rw [measureReal_def, hprod, ENNReal.toReal_prod]
    rfl
  rw [hreal]
  calc ∏ s ∈ Finset.Ico t (t + κ), μ.real (L.noHonestLeader s)
      ≤ ∏ _s ∈ Finset.Ico t (t + κ), (L.q : ℝ) :=
        Finset.prod_le_prod (fun s _ => measureReal_nonneg)
          (fun s _ => L.fail_prob s)
    _ = L.q ^ κ := by
        rw [Finset.prod_const, Nat.card_Ico, Nat.add_sub_cancel_left]

/-- **Horizon union bound (the `w.o.p.` shape of Lemma 4's leader half).** The
probability that *some* window `[t, t+κ)` with `t` in a finite horizon `H` has
no recognized honest leader in any of its slots is at most `|H| · q ^ κ`. With
`q < 1`, `κ` the security parameter and `|H|` polynomial, this is negligible —
so `HonestLeaderEveryWindow` holds w.o.p. over the horizon. -/
theorem no_leader_window_union_bound (H : Finset Slot) (κ : ℕ) :
    μ.real {ω | ∃ t ∈ H, ∀ s ∈ Finset.Ico t (t + κ), ω ∈ L.noHonestLeader s} ≤
      H.card * L.q ^ κ := by
  have hset : {ω | ∃ t ∈ H, ∀ s ∈ Finset.Ico t (t + κ), ω ∈ L.noHonestLeader s}
      = ⋃ t ∈ H, ⋂ s ∈ Finset.Ico t (t + κ), L.noHonestLeader s := by
    ext ω; simp
  rw [hset]
  refine (measureReal_biUnion_finset_le H _).trans ?_
  calc ∑ t ∈ H, μ.real (⋂ s ∈ Finset.Ico t (t + κ), L.noHonestLeader s)
      ≤ ∑ _t ∈ H, (L.q : ℝ) ^ κ :=
        Finset.sum_le_sum fun t _ => L.window_fail_bound t κ
    _ = H.card * L.q ^ κ := by
        rw [Finset.sum_const, nsmul_eq_mul]

end LeaderLottery

end Goldfish
