import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Independence.InfinitePi
import Goldfish.Basic
import Goldfish.Probabilistic.CountBound
import Goldfish.Probabilistic.LeaderWindow

/-!
# The concrete Bernoulli lottery model — instantiating the Chernoff layer

The abstract concentration machinery of the probabilistic layer
(`Goldfish.Probabilistic.Basic` / `CountBound` / `LeaderWindow`) takes
sub-Gaussianity and independence as *hypotheses*. This module builds the
concrete product-measure lottery the VRF idealization promises and **discharges
those hypotheses**, so that the good-event bound behind the `lemma1` / `lemma4`
axioms becomes a real theorem about an explicit probability space.

## The probability space

* **Eligibility lottery** `eligLot V thr hthr`: the product-Bernoulli measure
  `Measure.infinitePi` on `(Slot × V) → Bool`, where coordinate `(t, v)` records
  whether validator `v` is eligible to vote at slot `t` (an independent
  `Bernoulli thr` draw — `thr` is the paper's per-slot voting threshold
  `thr_v`). A fixed adversarial subset `A : Finset V` splits every slot's count
  into `advEligibleCount A t` (sum of indicators over `A`) and
  `honEligibleCount A t` (over `Aᶜ`).
* **Leader lottery** `leaderLot p hp`: the product-Bernoulli measure on
  `Slot → Bool`, coordinate `t` recording whether slot `t` has an honest leader
  recognized by all awake honest validators (probability `p ≥ p₀ > 0`).

## What is proved (`sorry`-free, no new axioms)

* `diff_count_subG` — the centered count `advCount − honCount` is sub-Gaussian
  with the **explicit** parameter `c = |V| / 4`: each per-validator signed
  indicator lies in an interval of length `1`, hence is sub-Gaussian with
  `c = 1/4` by Hoeffding's lemma (`hasSubgaussianMGF_of_mem_Icc`), and the
  per-slot coordinates are independent (`iIndepFun_infinitePi`), so the
  parameters add. This discharges the `subG` hypothesis of `CountLottery`.
* `honest_majority_horizon_bound` — consuming the `Compliant (1/2) ε n₀`
  fields, the probability that *some* slot of a finite horizon `H` has an
  adversarial eligible-voter majority is at most
  `|H| · exp (−g² / (2c))` with the **explicit** margin `g = ε · thr · n₀` and
  `c = |V| / 4`.
* `leaderLottery` — the `LeaderLottery` interface instantiated on
  `leaderLot p hp` with `q = 1 − p` (independence of the per-slot failure
  events proved from the product structure), and
  `no_honest_leader_window_bound` — the probability that some `κ`-window of the
  horizon has no honest leader is at most `|H| · (1 − p₀)^κ`.
* `lemma1_good_event_bound` — the capstone: on the product of the two lotteries
  the conjunction `HonestMajorityPerSlot ∧ HonestLeaderEveryWindow` (read over
  the finite horizon `H`) fails with probability at most
  `|H| · exp (−(ε·thr·n₀)² / (2·|V|/4)) + |H| · (1 − p₀)^κ`.

With `n₀ = Θ(κ)` and `|H| = poly(κ)` this shape is negligible in `κ`
(`Goldfish.Negligible`), which is exactly the `w.o.p.` claim of Lemma 1 / 4.

## What remains between this theorem and the `lemma1` axiom

See the docstring of `lemma1_good_event_bound`; in brief: (i) VRF
pseudorandomness justifying the iid Bernoulli model, (ii) identifying the
abstract `Execution` data with the sampled outcome, (iii) the finite-horizon
reading of the axiom's unbounded `∀ t : Slot` quantifier, and (iv) the static
awake-set simplification. These are model-instantiation gaps, not missing
mathematics: every probabilistic estimate is proved here.
-/

open MeasureTheory ProbabilityTheory Real Function

open scoped NNReal ENNReal

namespace Goldfish

/-! ## The eligibility lottery -/

/-- **The eligibility lottery.** The product-Bernoulli measure over all
`(slot, validator)` pairs: coordinate `(t, v)` is an independent
`Bernoulli thr` draw recording whether validator `v` is eligible to vote at
slot `t`. -/
noncomputable def eligLot (V : Type*) (thr : ℝ≥0) (hthr : thr ≤ 1) :
    Measure ((Slot × V) → Bool) :=
  Measure.infinitePi fun _ => (PMF.bernoulli thr hthr).toMeasure

instance eligLot_isProb (V : Type*) (thr : ℝ≥0) (hthr : thr ≤ 1) :
    IsProbabilityMeasure (eligLot V thr hthr) := by
  unfold eligLot; infer_instance

/-- The per-coordinate eligibility draws are independent. -/
theorem eligLot_iIndepFun (V : Type*) (thr : ℝ≥0) (hthr : thr ≤ 1) :
    iIndepFun (fun (i : Slot × V) (ω : (Slot × V) → Bool) => ω i)
      (eligLot V thr hthr) := by
  unfold eligLot
  exact iIndepFun_infinitePi (X := fun _ => id) fun _ => measurable_id

/-- A single coordinate is eligible with probability `thr`. -/
theorem eligLot_eval_true {V : Type*} (thr : ℝ≥0) (hthr : thr ≤ 1) (i : Slot × V) :
    eligLot V thr hthr (eval i ⁻¹' {true}) = thr := by
  unfold eligLot
  rw [(measurePreserving_eval_infinitePi
      (fun _ : Slot × V => (PMF.bernoulli thr hthr).toMeasure) i).measure_preimage
      ((measurableSet_singleton _).nullMeasurableSet),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  simp [PMF.bernoulli_apply]

section EligCounts

variable {V : Type*} [Fintype V] [DecidableEq V] (thr : ℝ≥0) (hthr : thr ≤ 1)

/-- Number of adversarial validators (the set `A`) eligible to vote at slot
`t`, as a random count over the eligibility lottery. -/
noncomputable def advEligibleCount (A : Finset V) (t : Slot)
    (ω : (Slot × V) → Bool) : ℝ :=
  ∑ v ∈ A, if ω (t, v) then 1 else 0

/-- Number of honest validators (the complement of `A`) eligible to vote at
slot `t`, as a random count over the eligibility lottery. -/
noncomputable def honEligibleCount (A : Finset V) (t : Slot)
    (ω : (Slot × V) → Bool) : ℝ :=
  ∑ v ∈ Aᶜ, if ω (t, v) then 1 else 0

omit [Fintype V] [DecidableEq V] in
private lemma measurableSet_evalTrue (i : Slot × V) :
    MeasurableSet (eval i ⁻¹' {true} : Set ((Slot × V) → Bool)) :=
  measurable_pi_apply i (measurableSet_singleton true)

omit [Fintype V] [DecidableEq V] in
private lemma ind_eq_indicator (i : Slot × V) :
    (fun ω : (Slot × V) → Bool => if ω i then (1 : ℝ) else 0)
      = Set.indicator (eval i ⁻¹' {true} : Set ((Slot × V) → Bool))
          fun _ => (1 : ℝ) := by
  funext ω
  by_cases hb : ω i <;> simp [eval, hb]

omit [Fintype V] [DecidableEq V] in
private lemma integrable_ind (i : Slot × V) :
    Integrable (fun ω => if ω i then (1 : ℝ) else 0) (eligLot V thr hthr) := by
  rw [ind_eq_indicator]
  exact (integrable_const (1 : ℝ)).indicator (measurableSet_evalTrue i)

omit [Fintype V] [DecidableEq V] in
private lemma integral_ind (i : Slot × V) :
    ∫ ω, (if ω i then (1 : ℝ) else 0) ∂ eligLot V thr hthr = thr := by
  rw [ind_eq_indicator, integral_indicator_const (1 : ℝ) (measurableSet_evalTrue i),
    smul_eq_mul, mul_one, measureReal_def, eligLot_eval_true thr hthr i,
    ENNReal.coe_toReal]

omit [Fintype V] [DecidableEq V] in
/-- Expected adversarial eligible-voter count: `|A| · thr`. -/
theorem integral_advEligibleCount (A : Finset V) (t : Slot) :
    ∫ ω, advEligibleCount A t ω ∂ eligLot V thr hthr = (A.card : ℝ) * thr := by
  simp only [advEligibleCount]
  rw [integral_finset_sum A fun v _ => integrable_ind thr hthr (t, v),
    Finset.sum_congr rfl fun v _ => integral_ind thr hthr (t, v),
    Finset.sum_const, nsmul_eq_mul]

/-- Expected honest eligible-voter count: `|Aᶜ| · thr`. -/
theorem integral_honEligibleCount (A : Finset V) (t : Slot) :
    ∫ ω, honEligibleCount A t ω ∂ eligLot V thr hthr = (Aᶜ.card : ℝ) * thr := by
  simp only [honEligibleCount]
  rw [integral_finset_sum Aᶜ fun v _ => integrable_ind thr hthr (t, v),
    Finset.sum_congr rfl fun v _ => integral_ind thr hthr (t, v),
    Finset.sum_const, nsmul_eq_mul]

omit [Fintype V] [DecidableEq V] in
private lemma integrable_advEligibleCount (A : Finset V) (t : Slot) :
    Integrable (fun ω => advEligibleCount A t ω) (eligLot V thr hthr) :=
  integrable_finset_sum A fun v _ => integrable_ind thr hthr (t, v)

private lemma integrable_honEligibleCount (A : Finset V) (t : Slot) :
    Integrable (fun ω => honEligibleCount A t ω) (eligLot V thr hthr) :=
  integrable_finset_sum Aᶜ fun v _ => integrable_ind thr hthr (t, v)

private lemma integral_count_diff (A : Finset V) (t : Slot) :
    ∫ ω, (advEligibleCount A t ω - honEligibleCount A t ω) ∂ eligLot V thr hthr
      = (A.card : ℝ) * thr - (Aᶜ.card : ℝ) * thr := by
  rw [integral_sub (integrable_advEligibleCount thr hthr A t)
      (integrable_honEligibleCount thr hthr A t),
    integral_advEligibleCount thr hthr A t, integral_honEligibleCount thr hthr A t]

/-! ### Sub-Gaussianity of the count difference (Hoeffding's lemma)

Each per-validator eligibility indicator, signed `+1` for adversarial and `−1`
for honest validators and centered at its mean, takes values in an interval of
length `1`, hence is sub-Gaussian with parameter `1/4` by Hoeffding's lemma.
The per-slot coordinates are independent, so the parameters add up to
`|V| / 4` for the centered count difference `advCount − honCount`. -/

omit [Fintype V] [DecidableEq V] in
private lemma signed_ind_subG (i : Slot × V) (s : ℝ) (hs : s = 1 ∨ s = -1) :
    HasSubgaussianMGF (fun ω => s * (if ω i then (1 : ℝ) else 0) - s * thr)
      (1 / 4) (eligLot V thr hthr) := by
  have hmeas : Measurable (fun ω : (Slot × V) → Bool =>
      s * (if ω i then (1 : ℝ) else 0)) :=
    (Measurable.of_discrete (f := fun b : Bool => s * (if b then (1 : ℝ) else 0))).comp
      (measurable_pi_apply i)
  have hint : (∫ ω, s * (if ω i then (1 : ℝ) else 0) ∂ eligLot V thr hthr)
      = s * thr := by
    rw [integral_const_mul, integral_ind thr hthr i]
  obtain rfl | rfl := hs
  · have hbnd : ∀ ω : (Slot × V) → Bool,
        (1 : ℝ) * (if ω i then (1 : ℝ) else 0) ∈ Set.Icc (0 : ℝ) 1 := by
      intro ω
      by_cases hb : ω i <;> simp [hb]
    have h := hasSubgaussianMGF_of_mem_Icc (μ := eligLot V thr hthr)
      hmeas.aemeasurable (ae_of_all _ hbnd)
    rw [hint] at h
    have hc : ((‖(1 : ℝ) - 0‖₊ / 2) ^ 2 : ℝ≥0) = 1 / 4 := by
      rw [sub_zero, nnnorm_one]
      refine NNReal.coe_injective ?_
      push_cast
      norm_num
    rwa [hc] at h
  · have hbnd : ∀ ω : (Slot × V) → Bool,
        (-1 : ℝ) * (if ω i then (1 : ℝ) else 0) ∈ Set.Icc (-1 : ℝ) 0 := by
      intro ω
      by_cases hb : ω i <;> simp [hb]
    have h := hasSubgaussianMGF_of_mem_Icc (μ := eligLot V thr hthr)
      hmeas.aemeasurable (ae_of_all _ hbnd)
    rw [hint] at h
    have hc : ((‖(0 : ℝ) - -1‖₊ / 2) ^ 2 : ℝ≥0) = 1 / 4 := by
      rw [zero_sub, nnnorm_neg, nnnorm_neg, nnnorm_one]
      refine NNReal.coe_injective ?_
      push_cast
      norm_num
    rwa [hc] at h

/-- The signed, centered per-validator eligibility indicator at slot `t`:
`+ (1_{elig} − thr)` for adversarial validators, `− (1_{elig} − thr)` for
honest ones. Its sum over all validators is the centered count difference. -/
private noncomputable def signedInd (A : Finset V) (t : Slot) (v : V)
    (ω : (Slot × V) → Bool) : ℝ :=
  (if v ∈ A then (1 : ℝ) else -1) * (if ω (t, v) then (1 : ℝ) else 0)
    - (if v ∈ A then (1 : ℝ) else -1) * thr

omit [Fintype V] in
private lemma signedInd_iIndepFun (A : Finset V) (t : Slot) :
    iIndepFun (signedInd thr A t) (eligLot V thr hthr) := by
  have h1 : iIndepFun (fun (v : V) (ω : (Slot × V) → Bool) => ω (t, v))
      (eligLot V thr hthr) :=
    (eligLot_iIndepFun V thr hthr).precomp (g := fun v : V => (t, v))
      fun v w h => congrArg Prod.snd h
  have h2 := h1.comp
    (fun v (b : Bool) => (if v ∈ A then (1 : ℝ) else -1) * (if b then (1 : ℝ) else 0)
      - (if v ∈ A then (1 : ℝ) else -1) * thr)
    fun _ => Measurable.of_discrete
  exact h2

omit [Fintype V] in
private lemma signedInd_subG (A : Finset V) (t : Slot) (v : V) :
    HasSubgaussianMGF (signedInd thr A t v) (1 / 4) (eligLot V thr hthr) := by
  by_cases hv : v ∈ A
  · refine (signed_ind_subG thr hthr (t, v) 1 (Or.inl rfl)).congr
      (ae_of_all _ fun ω => ?_)
    simp [signedInd, hv]
  · refine (signed_ind_subG thr hthr (t, v) (-1) (Or.inr rfl)).congr
      (ae_of_all _ fun ω => ?_)
    simp [signedInd, hv]

private lemma sum_signed (A : Finset V) (f : V → ℝ) :
    ∑ v, (if v ∈ A then (1 : ℝ) else -1) * f v
      = ∑ v ∈ A, f v - ∑ v ∈ Aᶜ, f v := by
  have h1 : ∑ v ∈ A, (if v ∈ A then (1 : ℝ) else -1) * f v = ∑ v ∈ A, f v :=
    Finset.sum_congr rfl fun v hv => by rw [if_pos hv, one_mul]
  have h2 : ∑ v ∈ Aᶜ, (if v ∈ A then (1 : ℝ) else -1) * f v = -∑ v ∈ Aᶜ, f v := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun v hv => by
      rw [if_neg (Finset.mem_compl.mp hv), neg_one_mul]
  rw [← Finset.sum_add_sum_compl A fun v => (if v ∈ A then (1 : ℝ) else -1) * f v,
    h1, h2]
  ring

/-- **Sub-Gaussianity of the eligible-count difference.** The centered
`advEligibleCount − honEligibleCount` at any slot is sub-Gaussian with the
explicit parameter `c = |V| / 4`: it is the sum of `|V|` independent centered
indicators, each in an interval of length `1` (Hoeffding's lemma gives `1/4`
per validator, and independence adds the parameters). -/
theorem diff_count_subG (A : Finset V) (t : Slot) :
    HasSubgaussianMGF
      (fun ω => (advEligibleCount A t ω - honEligibleCount A t ω)
        - ∫ x, (advEligibleCount A t x - honEligibleCount A t x)
            ∂ eligLot V thr hthr)
      ((Fintype.card V : ℝ≥0) / 4) (eligLot V thr hthr) := by
  have hsum := HasSubgaussianMGF.sum_of_iIndepFun
    (signedInd_iIndepFun thr hthr A t) (c := fun _ => (1 : ℝ≥0) / 4)
    (s := Finset.univ) fun v _ => signedInd_subG thr hthr A t v
  have hcard : (∑ _v : V, ((1 : ℝ≥0) / 4)) = (Fintype.card V : ℝ≥0) / 4 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one_div]
  rw [hcard] at hsum
  refine hsum.congr (ae_of_all _ fun ω => ?_)
  rw [integral_count_diff thr hthr A t]
  simp only [signedInd, advEligibleCount, honEligibleCount]
  rw [Finset.sum_sub_distrib, sum_signed, sum_signed, Finset.sum_const,
    Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]

/-- The eligible-count difference packaged as a `CountLottery`, with the
explicit sub-Gaussian parameter `c = |V| / 4`. -/
noncomputable def eligCountLottery (A : Finset V) :
    CountLottery ((Slot × V) → Bool) (eligLot V thr hthr) where
  count t ω := advEligibleCount A t ω - honEligibleCount A t ω
  c := (Fintype.card V : ℝ≥0) / 4
  subG t := diff_count_subG thr hthr A t

/-- **The compliance mean gap.** The `(1/2, ·)`-compliance fields for the
static split `adv ≡ |A|`, `hon ≡ |Aᶜ|` force the expected honest count to
exceed the expected adversarial count by at least `g = ε · thr · n₀`. -/
private lemma mean_gap_of_compliant {A : Finset V} {ε : ℝ} {n₀ : ℕ}
    (hcomp : Compliant (fun _ => A.card) (fun _ => Aᶜ.card) (1 / 2) ε n₀) :
    ε * thr * n₀ ≤ (thr : ℝ) * ((Aᶜ.card : ℝ) - (A.card : ℝ)) := by
  have hfrac := hcomp.frac_bound 0
  have hlb := hcomp.honest_lb 0
  have hε := hcomp.eps_pos
  have ha : (0 : ℝ) ≤ (A.card : ℝ) := Nat.cast_nonneg _
  have hn0 : (0 : ℝ) ≤ (n₀ : ℝ) := Nat.cast_nonneg _
  have hh : (0 : ℝ) < (Aᶜ.card : ℝ) := lt_of_le_of_lt (by positivity) hlb
  have hpos : (0 : ℝ) < (A.card : ℝ) + (Aᶜ.card : ℝ) := by linarith
  have h1 : (A.card : ℝ) ≤ (1 / 2 - ε) * ((A.card : ℝ) + (Aᶜ.card : ℝ)) :=
    (div_le_iff₀ hpos).mp hfrac
  have hkey : ε * (n₀ : ℝ) ≤ (Aᶜ.card : ℝ) - (A.card : ℝ) := by
    nlinarith [mul_nonneg hε.le ha, mul_lt_mul_of_pos_left hlb hε]
  have hthr' : (0 : ℝ) ≤ (thr : ℝ) := thr.coe_nonneg
  calc ε * (thr : ℝ) * (n₀ : ℝ) = (thr : ℝ) * (ε * (n₀ : ℝ)) := by ring
    _ ≤ (thr : ℝ) * ((Aᶜ.card : ℝ) - (A.card : ℝ)) :=
        mul_le_mul_of_nonneg_left hkey hthr'

/-- **Honest-majority good event over a finite horizon.** If the static
validator split is `(1/2, ε, n₀)`-compliant — the fields of
`Compliant (1/2) ε n₀` consumed with the constant awake counts
`adv ≡ |A|`, `hon ≡ |Aᶜ|` — then the probability that *some* slot of the
finite horizon `H` fails to have an honest eligible-voter majority is at most
`|H| · exp (−g² / (2c))` with the **explicit constants**

* margin `g = ε · thr · n₀` (from the compliance mean gap), and
* sub-Gaussian parameter `c = |V| / 4` (Hoeffding, one `1/4` per validator).

This is the honest-majority half of Lemma 1 / Lemma 4's good event, proved —
not axiomatized — for the Bernoulli product lottery. -/
theorem honest_majority_horizon_bound (A : Finset V) {ε : ℝ} {n₀ : ℕ}
    (hcomp : Compliant (fun _ => A.card) (fun _ => Aᶜ.card) (1 / 2) ε n₀)
    (H : Finset Slot) :
    (eligLot V thr hthr).real
        {ω | ∃ t ∈ H, honEligibleCount A t ω ≤ advEligibleCount A t ω} ≤
      H.card * exp (-(ε * thr * n₀) ^ 2 / (2 * ((Fintype.card V : ℝ) / 4))) := by
  have hg : 0 ≤ ε * (thr : ℝ) * (n₀ : ℝ) := by
    have hε := hcomp.eps_pos
    positivity
  have hub : ∀ t ∈ H,
      (∫ x, (advEligibleCount A t x - honEligibleCount A t x)
        ∂ eligLot V thr hthr) + ε * (thr : ℝ) * (n₀ : ℝ) ≤ (fun _ : Slot => (0 : ℝ)) t := by
    intro t _
    rw [integral_count_diff thr hthr A t]
    have := mean_gap_of_compliant thr hcomp
    simp only
    nlinarith
  have key := (eligCountLottery thr hthr A).exceeds_bound_union H
    (fun _ => (0 : ℝ)) hg hub
  have hset : {ω : (Slot × V) → Bool |
        ∃ t ∈ H, (0 : ℝ) ≤ advEligibleCount A t ω - honEligibleCount A t ω}
      = {ω | ∃ t ∈ H, honEligibleCount A t ω ≤ advEligibleCount A t ω} := by
    ext ω
    exact exists_congr fun t => and_congr_right fun _ => sub_nonneg
  have hc : (((Fintype.card V : ℝ≥0) / 4 : ℝ≥0) : ℝ) = (Fintype.card V : ℝ) / 4 := by
    push_cast
    ring
  calc (eligLot V thr hthr).real
          {ω | ∃ t ∈ H, honEligibleCount A t ω ≤ advEligibleCount A t ω}
      = (eligLot V thr hthr).real {ω : (Slot × V) → Bool |
          ∃ t ∈ H, (0 : ℝ) ≤ advEligibleCount A t ω - honEligibleCount A t ω} := by
        rw [hset]
    _ ≤ H.card * exp (-(ε * thr * n₀) ^ 2
          / (2 * (((Fintype.card V : ℝ≥0) / 4 : ℝ≥0) : ℝ))) := key
    _ = H.card * exp (-(ε * thr * n₀) ^ 2 / (2 * ((Fintype.card V : ℝ) / 4))) := by
        rw [hc]

end EligCounts

/-! ## The leader lottery -/

/-- **The leader lottery.** The product-Bernoulli measure over all slots:
coordinate `t` is an independent `Bernoulli p` draw recording whether slot `t`
has an honest leader recognized by all awake honest validators at its vote
round. -/
noncomputable def leaderLot (p : ℝ≥0) (hp : p ≤ 1) : Measure (Slot → Bool) :=
  Measure.infinitePi fun _ => (PMF.bernoulli p hp).toMeasure

instance leaderLot_isProb (p : ℝ≥0) (hp : p ≤ 1) :
    IsProbabilityMeasure (leaderLot p hp) := by
  unfold leaderLot; infer_instance

/-- The per-slot leader draws are independent. -/
theorem leaderLot_iIndepFun (p : ℝ≥0) (hp : p ≤ 1) :
    iIndepFun (fun (t : Slot) (ω : Slot → Bool) => ω t) (leaderLot p hp) := by
  unfold leaderLot
  exact iIndepFun_infinitePi (X := fun _ => id) fun _ => measurable_id

/-- A single slot misses (no recognized honest leader) with probability
`1 − p`. -/
theorem leaderLot_miss (p : ℝ≥0) (hp : p ≤ 1) (t : Slot) :
    leaderLot p hp (eval t ⁻¹' {false}) = 1 - (p : ℝ≥0∞) := by
  unfold leaderLot
  rw [(measurePreserving_eval_infinitePi
      (fun _ : Slot => (PMF.bernoulli p hp).toMeasure) t).measure_preimage
      ((measurableSet_singleton _).nullMeasurableSet),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  simp [PMF.bernoulli_apply]

private lemma iIndep_of_le {ι Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {m m' : ι → MeasurableSpace Ω} (h : iIndep m' μ) (hle : ∀ i, m i ≤ m' i) :
    iIndep m μ := by
  rw [iIndep_iff] at h ⊢
  intro S f hf
  exact h S fun i hi => hle i _ (hf i hi)

/-- The per-slot miss events are independent (as sets): each generates a
σ-algebra below the corresponding coordinate σ-algebra, and the coordinates
are independent under the product measure. -/
theorem leaderLot_iIndepSet (p : ℝ≥0) (hp : p ≤ 1) :
    iIndepSet (fun t : Slot => eval t ⁻¹' ({false} : Set Bool)) (leaderLot p hp) := by
  rw [iIndepSet_iff_iIndep]
  have h := leaderLot_iIndepFun p hp
  rw [iIndepFun_iff_iIndep] at h
  refine iIndep_of_le h fun t => ?_
  refine MeasurableSpace.generateFrom_le ?_
  rintro s hs
  rw [Set.mem_singleton_iff] at hs
  subst hs
  exact ⟨{false}, measurableSet_singleton _, rfl⟩

/-- The concrete Bernoulli leader lottery, instantiating the abstract
`LeaderLottery` interface of `Goldfish.Probabilistic.LeaderWindow` with the
explicit failure ceiling `q = 1 − p`. -/
noncomputable def leaderLottery (p : ℝ≥0) (hp : p ≤ 1) :
    LeaderLottery (Slot → Bool) (leaderLot p hp) where
  noHonestLeader t := eval t ⁻¹' {false}
  measurable t := measurable_pi_apply t (measurableSet_singleton false)
  indep := leaderLot_iIndepSet p hp
  q := 1 - p
  fail_prob t := by
    rw [measureReal_def, leaderLot_miss p hp t,
      ENNReal.toReal_sub_of_le (by exact_mod_cast hp) ENNReal.one_ne_top,
      ENNReal.toReal_one, ENNReal.coe_toReal, NNReal.coe_sub hp,
      NNReal.coe_one]

/-- **Honest-leader window good event over a finite horizon.** With per-slot
honest-leader probability `p ≥ p₀`, the probability that *some* window
`[t, t+κ)` with `t` in the finite horizon `H` has no recognized honest leader
is at most `|H| · (1 − p₀)^κ`. Instantiates the proved
`LeaderLottery.no_leader_window_union_bound` on the concrete Bernoulli
lottery. -/
theorem no_honest_leader_window_bound (p : ℝ≥0) (hp : p ≤ 1) {p₀ : ℝ}
    (hle : p₀ ≤ p) (H : Finset Slot) (κ : ℕ) :
    (leaderLot p hp).real
        {ω | ∃ t ∈ H, ∀ s ∈ Finset.Ico t (t + κ), ω s = false} ≤
      H.card * (1 - p₀) ^ κ := by
  have key := (leaderLottery p hp).no_leader_window_union_bound H κ
  have hq : (leaderLottery p hp).q = 1 - p := rfl
  rw [hq] at key
  refine le_trans key ?_
  have hq' : ((1 - p : ℝ≥0) : ℝ) ≤ 1 - p₀ := by
    rw [NNReal.coe_sub hp]
    simp only [NNReal.coe_one]
    linarith
  have hqn : (0 : ℝ) ≤ ((1 - p : ℝ≥0) : ℝ) := NNReal.coe_nonneg _
  have hcard : (0 : ℝ) ≤ (H.card : ℝ) := Nat.cast_nonneg _
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hqn hq' κ) hcard

/-! ## The capstone: Lemma 1's good event as a theorem -/

/-- **The good-event bound behind `axiom lemma1` (and `lemma4`), as a proved
theorem.** On the product of the eligibility and leader lotteries, the
probability that the finite-horizon reading of
`HonestMajorityPerSlot ∧ HonestLeaderEveryWindow` **fails** — some slot of the
horizon `H` lacks an honest eligible-voter majority, or some `κ`-window
anchored in `H` lacks a recognized honest leader — is at most

`|H| · exp (−(ε·thr·n₀)² / (2·(|V|/4))) + |H| · (1 − p₀)^κ`.

All constants are explicit: margin `g = ε·thr·n₀` from the compliance fields,
sub-Gaussian parameter `c = |V|/4` from Hoeffding's lemma, and per-window miss
probability `(1 − p₀)^κ` from independence. With `n₀ = Θ(κ)` and
`|H| = poly(κ)` the bound is negligible in `κ` (`Goldfish.Negligible`) — the
`w.o.p.` shape of Lemma 1 / Lemma 4.

### What remains between this theorem and discharging `axiom lemma1`

`lemma1` (`Goldfish.Axioms`) concludes the good events for an abstract
`Execution`. The residual gap is model instantiation, not probability:

1. **VRF pseudorandomness ⇒ iid Bernoulli.** In the protocol, eligibility and
   leadership are determined by VRF evaluations; that these are
   computationally indistinguishable from the independent `Bernoulli thr` /
   `Bernoulli p` draws modeled here is the cryptographic idealization
   (paper App. G) and is inherently outside a probability-only formalization.
2. **Execution semantics.** `E.honEligible`, `E.advEligible` and `E.leader`
   are abstract data of an `Execution`; identifying them with the sampled
   outcome `ω` of this product space (a probabilistic semantics for
   executions) is the same Barrier-1 idealization documented in `README.md`.
3. **Quantifier over slots.** `HonestMajorityPerSlot` quantifies over *all*
   `t : Slot`. Under any iid model an infinite horizon fails almost surely,
   so the axiom's unbounded quantifier must be read over the execution's
   `poly(κ)` horizon `T_hor` (as the paper does); this theorem provides the
   bound for every finite horizon `H`.
4. **Static awake split.** The `Compliant` fields are consumed with constant
   awake counts `adv ≡ |A|`, `hon ≡ |Aᶜ|`; the paper's per-round awake sets
   and `τ`-mildly-adaptive corruption vary over time. Round-varying splits
   would reuse the same per-slot machinery with slot-dependent `A t`.
5. **Cross-lottery independence.** Eligibility and leadership are modeled on
   a product space (independent); in the protocol both derive from the same
   VRF keys at distinct inputs, and their independence is again part of the
   pseudorandomness idealization. -/
theorem lemma1_good_event_bound {V : Type*} [Fintype V] [DecidableEq V]
    (thr p : ℝ≥0) (hthr : thr ≤ 1) (hp : p ≤ 1) (A : Finset V)
    {ε p₀ : ℝ} {n₀ : ℕ}
    (hcomp : Compliant (fun _ => A.card) (fun _ => Aᶜ.card) (1 / 2) ε n₀)
    (hle : p₀ ≤ p) (H : Finset Slot) (κ : ℕ) :
    ((eligLot V thr hthr).prod (leaderLot p hp)).real
        {ω | (∃ t ∈ H, honEligibleCount A t ω.1 ≤ advEligibleCount A t ω.1) ∨
          ∃ t ∈ H, ∀ s ∈ Finset.Ico t (t + κ), ω.2 s = false} ≤
      H.card * exp (-(ε * thr * n₀) ^ 2 / (2 * ((Fintype.card V : ℝ) / 4)))
        + H.card * (1 - p₀) ^ κ := by
  have hdecomp :
      {ω : ((Slot × V) → Bool) × (Slot → Bool) |
          (∃ t ∈ H, honEligibleCount A t ω.1 ≤ advEligibleCount A t ω.1) ∨
            ∃ t ∈ H, ∀ s ∈ Finset.Ico t (t + κ), ω.2 s = false}
        = ({ω | ∃ t ∈ H, honEligibleCount A t ω ≤ advEligibleCount A t ω}
              ×ˢ Set.univ)
          ∪ (Set.univ
              ×ˢ {ω | ∃ t ∈ H, ∀ s ∈ Finset.Ico t (t + κ), ω s = false}) := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_prod, Set.mem_univ,
      and_true, true_and]
  rw [hdecomp]
  refine le_trans (measureReal_union_le _ _) ?_
  rw [measureReal_prod_prod, measureReal_prod_prod, probReal_univ, probReal_univ,
    mul_one, one_mul]
  exact add_le_add (honest_majority_horizon_bound thr hthr A hcomp H)
    (no_honest_leader_window_bound p hp hle H κ)

end Goldfish
