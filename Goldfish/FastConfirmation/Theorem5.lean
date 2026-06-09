import Goldfish.FastConfirmation.Theorem4
import Goldfish.FastConfirmation.Ledger4Delta

/-!
# Theorem 5 — safety with fast confirmations

> **Theorem 5** (IACR 2022/1171). Suppose the Goldfish execution is
> `(1/2, 4∆)`-compliant. Then, Goldfish with fast confirmations satisfies safety
> (w.o.p.).

Safety (`Ledger4Δ.safe`) holds for any `Ledger4Δ` assignment. The meaningful
content here is that a fast-confirmed block `B` enters every awake honest
validator's ledger from round `4∆(t+κ)+2∆` onward: Theorem 4 gives stability
of `B` in the fork choice, and `Ledger4Δ.confirmed_of_stable` confirms it at
depth `κ`. No `sorry`.
-/

namespace Goldfish

variable {Block Validator : Type*} [BlockTree Block] {E : Execution Block Validator} {κ : ℕ}

/-- **Theorem 5.** Under `(1/2, 4∆)`-compliance:
1. Safety: any two `Ledger4Δ` outputs are consistent.
2. Fast-confirmation stability: a fast-confirmed block `B` is a prefix of every
   awake honest validator's ledger from round `4∆(t+κ)+2∆` onward. -/
theorem theorem5 (FS : Spec4Δ E) (FL : Ledger4Δ E κ)
    (hmaj : HonestMajorityPerSlot E) {idc : Validator} {t : Slot} {B : Block}
    (hfc : E.fastConfirms idc t B) :
    FL.Safe ∧
    ∀ {r : Round} {id : Validator},
      4 * E.Δ * (t + κ) + 2 * E.Δ ≤ r → E.awakeHonest id r → B ≤ FL.chain id r := by
  exact ⟨FL.safe, FL.confirmed_of_stable (theorem4 FS hmaj hfc)⟩

end Goldfish
