import Mathlib.Order.Preorder.Chain
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Data.Real.Basic

/-!
# Goldfish — basic types and the data layer

Core types shared by every numbered statement of *Goldfish* (IACR ePrint
2022/1171): the block-tree prefix order `⪯`, slots and rounds, the
`(γ,τ)`-compliance predicate (Def. 2), and the `Negligible` abstraction that
isolates the probabilistic core (Lem. 1/4, Prop. 1); `w.o.p.` remains prose
shorthand for "except with probability `negl(κ) + negl(λ)`".

Protocol mechanics (GHOST-Eph fork choice, voting) are an abstract interface in
`Goldfish.Protocol` (Barrier 3 of `README.md`); the
probabilistic good events and the external [61] results are declared in
`Goldfish.Axioms`.
-/

namespace Goldfish

/-- Protocol rounds. One Goldfish slot spans `3∆` rounds (`4∆` with fast
confirmation). -/
abbrev Round := ℕ

/-- Protocol slots. -/
abbrev Slot := ℕ

/-! ## Block tree -/

/-- The carrier of blocks, ordered by the ancestor / prefix relation `⪯`.

`a ≤ b` (read `a ⪯ b`) means the chain ending at `a` is a prefix of the chain
ending at `b` — equivalently `a` is an ancestor of, or equal to, `b`. Genesis is
the global minimum `⊥`, and the set of ancestors of any block is a chain (the
tree property: a block has a single linear history). -/
class BlockTree (Block : Type*) extends PartialOrder Block, OrderBot Block where
  /-- The set of ancestors of any block is totally ordered (the tree property). -/
  ancestors_isChain : ∀ b : Block, IsChain (· ≤ ·) {a : Block | a ≤ b}

namespace BlockTree

variable {Block : Type*} [BlockTree Block]

/-- Genesis block `B₀`: the global minimum of the prefix order. -/
abbrev genesis : Block := ⊥

@[simp] theorem genesis_le (b : Block) : (genesis : Block) ≤ b := bot_le

/-- Two blocks are *consistent* if one is a prefix of the other (they lie on a
common chain). -/
def Consistent (a b : Block) : Prop := a ≤ b ∨ b ≤ a

/-- Two blocks *conflict* if neither is a prefix of the other. -/
def Conflicts (a b : Block) : Prop := ¬ Consistent a b

@[refl] theorem Consistent.rfl (a : Block) : Consistent a a := Or.inl le_rfl

theorem Consistent.symm {a b : Block} (h : Consistent a b) : Consistent b a := Or.symm h

theorem consistent_comm {a b : Block} : Consistent a b ↔ Consistent b a :=
  ⟨Consistent.symm, Consistent.symm⟩

/-- Genesis is consistent with every block. -/
theorem consistent_genesis (b : Block) : Consistent (genesis : Block) b :=
  Or.inl (genesis_le b)

/-- Any two ancestors of a common block are consistent (the tree property,
unpacked from `ancestors_isChain`). This is the workhorse for GHOST-Eph
reasoning: blocks on the path to a common descendant never conflict. -/
theorem consistent_of_le_of_le {a b c : Block} (ha : a ≤ c) (hb : b ≤ c) :
    Consistent a b := by
  rcases eq_or_ne a b with rfl | hne
  · exact Consistent.rfl a
  · exact ancestors_isChain c ha hb hne

/-- `B ≤ B'` always implies the two are consistent. -/
theorem consistent_of_le {a b : Block} (h : a ≤ b) : Consistent a b := Or.inl h

end BlockTree

/-! ## `(γ,τ)`-compliance (Def. 2) -/

/-- `(γ,τ)`-compliance, key-evolving-primitives form (Def. 2): in every round the
adversary fraction `A_r / (A_r + H_r)` is at most `γ - ε`, and strictly more than
`γ·n₀ = Θ(κ)` honest validators are awake.

Here `adv r = A_r` and `hon r = H_r`. The `τ`-round mildly-adaptive corruption
delay of Def. 2 affects *which* validators count as eligible at a slot; it is
threaded through the probabilistic good event of Lemma 1 rather than this purely
arithmetic predicate. -/
structure Compliant (adv hon : Round → ℕ) (γ ε : ℝ) (n₀ : ℕ) : Prop where
  /-- The slack `ε` is strictly positive. -/
  eps_pos : 0 < ε
  /-- The adversary fraction is at most `γ - ε` in every round. -/
  frac_bound : ∀ r : Round, (adv r : ℝ) / (adv r + hon r) ≤ γ - ε
  /-- Strictly more than `γ·n₀` honest validators are awake in every round. -/
  honest_lb : ∀ r : Round, (γ : ℝ) * n₀ < hon r

/-! ## Negligibility / overwhelming probability -/

/-- A real-valued sequence is *negligible* (`negl`) if it eventually decays
faster than every inverse polynomial in the security parameter.

The w.o.p. error terms throughout the paper are negligible; the composition API
(e.g. `negl(κ) + negl(λ)` is negligible) belongs to the probabilistic layer
that replaces the good-event axioms. -/
def Negligible (f : ℕ → ℝ) : Prop :=
  ∀ c : ℕ, ∃ N : ℕ, ∀ n ≥ N, |f n| < 1 / (n : ℝ) ^ c

end Goldfish
