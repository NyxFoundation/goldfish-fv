---
title: Goldfish Lean 4 Formalization Strategy
last_updated: 2026-05-27
tags:
  - lean4
  - formal-verification
  - goldfish
  - consensus
---

# Goldfish Lean 4 Formalization Strategy

This document records *how* the Goldfish consensus protocol (IACR ePrint
2022/1171) is being formalized in Lean 4, the technical barriers we hit, and the
explicit policy decision for each. The 21 numbered statements of the paper
(Theorem 1–7, Lemma 1–9, Proposition 1–5) are each tracked by a GitHub issue;
this file is the cross-cutting reference those issues link back to.

The statement texts and proofs live in [`notes/paper-statements.md`](../notes/paper-statements.md)
and the per-statement segments in [`notes/_segments/`](../notes/_segments/).

## Proof discipline: `sorry` vs `axiom` vs hypothesis threading

These three are **not** interchangeable. The project uses the latter two and
never the first.

| Mechanism | Meaning | Soundness | Use in this project |
|---|---|---|---|
| `sorry` | Placeholder for an omitted proof; compiles but Lean warns and every downstream proof is tainted. | ✗ Not a proof; technical debt. | **Never.** |
| `axiom` | A proposition *declared* true without proof — a deliberate, explicit assumption. | ✓ Sound relative to the assumption being a genuine external/idealized fact. | For external [61] results and for the probabilistic good events (temporarily). |
| Hypothesis threading | The good event is taken as an explicit *premise* of the theorem. | ✓ The theorem is fully proved: "good event ⇒ conclusion". | Default for all deterministic consensus reasoning. |

Concretely, a deterministic theorem takes the probabilistic conclusion of
Lemma 1/4 or Proposition 1 as a hypothesis and is then proved with **no `sorry`
and no local axiom**:

```lean
theorem goldfish_security
    (h : HonestMajorityPerSlot exec) :   -- conclusion of Lemma 1, threaded in
    Safe exec.ch_ava ∧ Live exec.ch_ava := by
  ...  -- fully discharged
```

The probabilistic fact "the good event holds with overwhelming probability" is
isolated into Lemma 1/4 and Proposition 1, declared as `axiom` for now (see
below), and proved later via measure theory in a dedicated Phase 2 issue.

## Barriers and decisions

### 1. Probability (`w.o.p.` / Chernoff)

`w.o.p.` ("with overwhelming probability", i.e. except with probability
`negl(κ) + negl(λ)`) appears throughout. The probabilistic core is exactly
**Lemma 1, Lemma 4 and Proposition 1** (VRF-lottery + Chernoff bounds giving an
honest majority among eligible voters and an upper bound on voter count). Every
other statement is deterministic *given* those conclusions.

Concentration inequalities (Chernoff/Hoeffding) are **not in core Mathlib**;
they exist only in specialized libraries (e.g. `lean-stat-learning-theory`).
Proving them from measure theory is research-level work.

**Decision.** Thread the good event as a hypothesis into the deterministic
theorems (fully proved). Declare Lemma 1 / Lemma 4 / Proposition 1 as `axiom`
(label `needs-axiom`). A statement issue closes at **Phase 1** — the axiom is
declared and dependents can proceed. The measure-theoretic proof that replaces
the axiom is tracked in a separate **Phase 2 follow-up issue** (label `phase2`),
so it never blocks dependency closure.

### 2. External reference [61] (Ebb-and-Flow)

Theorem 7, Lemma 7, Lemma 9 and Propositions 3–5 rely on results from the
accountability-gadget paper [61] (Neu, Tas, Tse — *The Availability-Accountability
Dilemma and its Resolution via Accountability Gadgets*,
[ePrint 2021/628](https://eprint.iacr.org/2021/628) / [arXiv:2105.06075](https://arxiv.org/abs/2105.06075)).
Goldfish's Lemmas 7–9 and Propositions 3–5 are stated as analogues of that
paper's Thm 4 / Lem 1 / Thm 5 and Prop 2 / 3 / 4. Formalizing [61] is out of
scope.

**Decision.** Declare each imported [61] result as an `axiom` with a source
comment in a central module (see Non-issue prerequisites). Statements whose
proof depends on those axioms carry the `external-ref` label.

### 3. Protocol mechanics (GHOST-Eph, slots, voting)

The notes deliberately omit Algorithms 1–6, but the theorem statements need the
fork-choice rule, slot structure and voting behaviour.

**Decision (MVP).** Do not implement the algorithms operationally. Provide
fork-choice / slot / voting behaviour as an **abstract interface (a structure or
typeclass of hypotheses)** and derive the theorems from it. An executable model
can replace the interface later without changing the theorem statements.

### 4. Track C cyclic dependency

In Track C the proof dependencies form a cycle: **Lemma 7 → Lemma 9 → Lemma 8 →
Lemma 7** (the healing argument is a mutual induction).

**Decision.** Prove the three as one simultaneous induction and close them
together from a single PR. Their DoD omits the "all dependency issues closed"
requirement *for the in-bundle edges*; out-of-bundle dependencies (Lemma 1,
Proposition 4, Propositions 3/5, the [61] axioms) must still be resolved.

## Track structure and dependency graph

Three layers, built in order. Track A is self-contained; B and C depend on A.

- **Track A — synchronous core:** Thm 1–3, Lem 1–3. Reorg resilience + security
  under `(1/2, 3∆)`-compliance.
- **Track B — fast confirmation:** Thm 4–6, Lem 4–5, Prop 1. `(1/2, 4∆)`.
- **Track C — partial synchrony / ebb-and-flow:** Thm 7, Lem 6–9, Prop 2–5.
  `(1/3, 3∆)`, accountability gadget overlay.

Dependency adjacency list (`X ← {…}` means X's proof depends on …; `[61,*]`
are external axioms):

```
Thm1 ← {Lem1, Lem2, Lem3}
Thm2 ← {Lem1, Thm1}
Thm3 ← {Thm1}
Thm4 ← {Lem3, Lem4, Lem5}
Thm5 ← {Thm2, Thm4}
Thm6 ← {Thm2, Lem2}
Thm7 ← {Lem6, Lem7, Lem9, [61,Thm3]}

Lem1 ← {}              (axiom; probabilistic)
Lem2 ← {}              (deterministic)
Lem3 ← {Lem1}
Lem4 ← {}              (axiom; probabilistic)
Lem5 ← {Prop1}
Lem6 ← {Prop2, Thm2}
Lem7 ← {Prop3, Prop4, Lem9, [61,Thm4]}     ┐
Lem8 ← {Lem7}                               │ cyclic bundle
Lem9 ← {Lem1, Prop4, Lem8, Prop5, [61,Thm3]}┘

Prop1 ← {}             (axiom; probabilistic)
Prop2 ← {Lem1, Thm1}
Prop3 ← {[61,Prop2]}   (axiom; no paper proof)
Prop4 ← {[61,Prop3]}
Prop5 ← {[61,Prop4]}   (axiom; no paper proof)
```

## Non-issue prerequisites (Lean scaffolding)

The following are **not** tracked by per-statement issues; they are prerequisite
scaffolding assumed by every statement issue. They will be introduced together
(separately from the statement issues) and live at these paths:

| Path | Contents | Status |
|---|---|---|
| `lakefile.toml`, `lean-toolchain` | Lake build config; toolchain pinned to `leanprover/lean4:v4.29.0`, depends on Mathlib `v4.29.0`. | ✅ in place |
| `Goldfish/Basic.lean` | Core types: the `BlockTree` prefix partial order `⪯` (genesis `⊥`, ancestors-form-a-chain tree property), `Consistent`/`Conflicts`, the `(γ,τ)`-`Compliant` predicate (Def. 2), `Negligible` (`negl`). | ✅ in place |
| `Goldfish/Protocol.lean` | Abstract interface: the `Execution` data (slots/rounds, awake/honest/eligible predicates, counts, fork choice, votes) and the `Spec` structure of GHOST-Eph / voting / leader-recognition / synchrony hypotheses (Barrier 3). | ✅ in place |
| `Goldfish/Axioms.lean` | Declared axioms: probabilistic good events Lemma 1 / Lemma 4 / Proposition 1 (`HonestMajorityPerSlot`, `HonestLeaderEveryWindow`, eligible-voter bounds). | ✅ in place |

**`BlockVoteTree` / `Merge` / `Children` / `Votes`.** Rather than model bvtrees
operationally, the GHOST-Eph vote tally is abstracted by the `Execution.outvotes`
predicate and the `Spec` fields that relate it to the fork choice (Barrier 3). An
operational bvtree model can refine this later without changing theorem
statements.

**External [61] axioms deferred.** `[61, Thm 3]`, `[61, Thm 4]`, `[61, Prop 2/3/4]`
are **not** declared in `Goldfish/Axioms.lean` yet. They cannot be *stated*
faithfully before Track C's vocabulary (the `chacc`/`chava` ledgers, partial
synchrony, `GST`/`GAT`) exists, and declaring vacuous placeholders would violate
the no-placeholder discipline. They are introduced together with the Track C base
types, each with a source comment.

Reference pattern for project layout: [`Koukyosyumei/PoL`](https://github.com/Koukyosyumei/PoL)
(Apache-2.0, Lake, `Consensus/` module layout).
