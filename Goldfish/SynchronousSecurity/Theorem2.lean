import Goldfish.SynchronousSecurity.Theorem1
import Goldfish.Ledger

/-!
# Theorem 2 — Goldfish security (safety & liveness), `Tconf = 2κ+2` slots

> **Theorem 2** (Security, IACR 2022/1171). Suppose a `(1/2, 3∆)`-compliant
> execution of Goldfish in the synchronous sleepy network model. Then, w.o.p.,
> Goldfish is secure with transaction confirmation time `Tconf = 2κ + 2` slots.

*Safety* is purely the confirmed-ledger common-prefix property (`Ledger.safe`):
two ledgers are both prefixes of the later validator's fork choice, hence
consistent. *Liveness* follows the paper: a transaction received by round `r` is
included by the recognized honest leader of some slot in the next `κ`-window
(Lemma 1's `HonestLeaderEveryWindow`), that block is stable (Theorem 1) and
confirmed within `κ` further slots (`confirmed_of_stable`), so it lands in every
awake honest validator's ledger by round `r + (2κ+2)·3∆`.

Lemma 1's two good events are threaded as the hypotheses `HonestMajorityPerSlot`
and `HonestLeaderEveryWindow`.
-/

namespace Goldfish

variable {Block Validator : Type*} [BlockTree Block] {E : Execution Block Validator} {κ : ℕ}

/-- The slot/round arithmetic of the liveness window. With `d = 3∆` and the
recognized leader at a slot `t ∈ [r/d + 1, r/d + 1 + κ)`: its proposal round
`d·t` is at or after `r`, and its confirmation round `d·(t+κ) + 2∆` is at or
before `r + (2κ+2)·d`. -/
private theorem live_arith {d r r' t κ Δ : ℕ} (hdpos : 0 < d) (hd : d = 3 * Δ)
    (hbt : r / d + 1 ≤ t) (htlt : t < r / d + 1 + κ)
    (hr' : r + (2 * κ + 2) * d ≤ r') :
    r ≤ d * t ∧ d * (t + κ) + 2 * Δ ≤ r' := by
  have hdm := Nat.div_add_mod r d
  have hmod : r % d < d := Nat.mod_lt r hdpos
  have hmono1 : d * (r / d + 1) ≤ d * t := by gcongr
  have hmono2 : d * t ≤ d * (r / d + 1 + κ) := by gcongr
  have hT : (2 * κ + 2) * d = 2 * (d * κ) + 2 * d := by
    rw [Nat.add_mul, Nat.mul_assoc, Nat.mul_comm κ d]
  rw [Nat.mul_add, Nat.mul_one] at hmono1
  rw [Nat.mul_add, Nat.mul_add, Nat.mul_one] at hmono2
  refine ⟨by omega, ?_⟩
  rw [Nat.mul_add]
  omega

/-- **Theorem 2 (Security).** For every confirmed-ledger assignment with a
transaction model, Goldfish is safe (Def. 1) and live with confirmation time
`Tconf = (2κ+2)·3∆` rounds (i.e. `2κ+2` slots), given Lemma 1's good events. -/
theorem theorem2 (S : Spec E) (L : Ledger E κ) (TX : TxModel E)
    (hmaj : HonestMajorityPerSlot E) (hwin : HonestLeaderEveryWindow E κ) :
    L.Safe ∧ TX.Live L ((2 * κ + 2) * (3 * E.Δ)) := by
  refine ⟨L.safe, ?_⟩
  intro tx r hrecv r' id hr' hawake
  have hdpos : 0 < 3 * E.Δ := by have := E.Δ_pos; omega
  obtain ⟨t, hbt, htlt, _lead, _hhon, hlead⟩ := hwin (r / (3 * E.Δ) + 1)
  obtain ⟨hi, hii⟩ := live_arith (d := 3 * E.Δ) (Δ := E.Δ) hdpos rfl hbt htlt hr'
  have hmem := TX.leader_includes hrecv hlead hi
  have hconf := L.confirmed_of_stable (theorem1 S hmaj hlead) hii hawake
  exact TX.mem_mono hmem hconf

end Goldfish
