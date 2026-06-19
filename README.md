# goldfish-fv

A Lean 4 formalization of the **Goldfish** Ethereum consensus protocol (IACR ePrint 2022/1171). The paper's 21 numbered statements (Theorem 1–7, Lemma 1–9, Proposition 1–5) are formalized here. This README documents the proof discipline, the barriers and the decision for each, the dependency graph, and the Lean module layout.
Build toward a formalization of the Goldfish safety and liveness results, using the paper's numbered statements as the specification target.

## Source

Francesco D'Amato, Joachim Neu, Ertem Nusret Tas, David Tse — *Goldfish: No More Attacks on Ethereum?!*

- IACR ePrint: <https://eprint.iacr.org/2022/1171>
- arXiv: <https://arxiv.org/abs/2209.03255> (v4, 2023-12-30)
- Published at Financial Cryptography 2024

Algorithms 1–6, Figure 7, and the prose sections of the paper are intentionally omitted — they are protocol pseudocode and commentary rather than statements to formalize.

## Barriers and decisions

### 1. Probability (`w.o.p.` / Chernoff)

`w.o.p.` ("with overwhelming probability", i.e. except with probability `negl(κ) + negl(λ)`) appears throughout. The probabilistic core is exactly **Lemma 1, Lemma 4 and Proposition 1** (VRF-lottery + Chernoff bounds giving an honest majority among eligible voters and an upper bound on voter count). Every other statement is deterministic *given* those conclusions.

Concentration inequalities (Chernoff/Hoeffding) are **not in core Mathlib**; they exist only in specialized libraries (e.g. `lean-stat-learning-theory`). Proving them from measure theory is research-level work.

**Decision.** Thread the good event as a hypothesis into the deterministic theorems (fully proved), and declare Lemma 1 / Lemma 4 / Proposition 1 as `axiom`. Dependents can then proceed immediately. The measure-theoretic proof that replaces each axiom is developed separately, so it never blocks the deterministic proofs.

### 2. External reference [61] (Ebb-and-Flow)

Theorem 7, Lemma 7, Lemma 9 and Propositions 3–5 rely on results from the accountability-gadget paper [61] (Neu, Tas, Tse — *The Availability-Accountability Dilemma and its Resolution via Accountability Gadgets*, [ePrint 2021/628](https://eprint.iacr.org/2021/628) / [arXiv:2105.06075](https://arxiv.org/abs/2105.06075)). Goldfish's Lemmas 7–9 and Propositions 3–5 are stated as analogues of that paper's Thm 4 / Lem 1 / Thm 5 and Prop 2 / 3 / 4. Formalizing [61] is out of scope.

**Decision.** Declare each imported [61] result as an `axiom` with a source comment in a central module (see Module layout).

### 3. Protocol mechanics (GHOST-Eph, slots, voting)

The formalization deliberately omits Algorithms 1–6, but the theorem statements need the fork-choice rule, slot structure and voting behaviour.

**Decision.** Do not implement the algorithms operationally. Provide fork-choice / slot / voting behaviour as an **abstract interface (a structure or typeclass of hypotheses)** and derive the theorems from it. An executable model can replace the interface later without changing the theorem statements.

### 4. Ebb-and-flow cyclic dependency

In the partial-synchrony / ebb-and-flow proofs the dependencies form a cycle: **Lemma 7 → Lemma 9 → Lemma 8 → Lemma 7** (the healing argument is a mutual induction).

**Decision.** Prove the three together as one simultaneous induction. The cyclic dependencies among them are discharged by the joint induction rather than one at a time; the out-of-bundle dependencies (Lemma 1, Proposition 4, Propositions 3/5, the [61] axioms) must still be resolved separately.

## Proof layers and dependency graph

Three layers, built in order. The synchronous-security layer is self-contained; fast confirmation and partial synchrony / ebb-and-flow each depend on it.

- **Synchronous security** (`Goldfish.SynchronousSecurity`): Thm 1–3, Lem 1–3. Reorg resilience + security under `(1/2, 3∆)`-compliance.
- **Fast confirmation** (`Goldfish.FastConfirmation`): Thm 4–6, Lem 4–5, Prop 1. `(1/2, 4∆)`-compliance.
- **Partial synchrony / ebb-and-flow** (`Goldfish.EbbAndFlow`): Thm 7, Lem 6–9, Prop 2–5. `(1/3, 3∆)`-compliance, accountability gadget overlay.

Dependency adjacency list (`X ← {…}` means X's proof depends on …; `[61,*]` are external axioms):

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
