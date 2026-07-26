# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project

Lean 4 (v4.29.0, Mathlib v4.29.0) formalization of the *Goldfish* Ethereum consensus protocol (IACR ePrint 2022/1171). The specification target is exactly the paper's 21 numbered statements (Theorem 1–7, Lemma 1–9, Proposition 1–5); Algorithms 1–6 and prose are intentionally out of scope. `README.md` is the authoritative design document — it records the four barriers, the decision taken for each, and the full dependency graph (Mermaid) between statements. Consult it before adding or restructuring proofs.

## Commands

```bash
lake exe cache get     # fetch prebuilt Mathlib oleans — run before the first build
lake build             # build the whole Goldfish library
lake build Goldfish.FastConfirmation.Lemma5   # build a single module (fastest check while editing)
```

There is no test suite, linter, or CI config; `lake build` succeeding is the correctness check.

## Proof discipline (non-negotiable)

- **Never `sorry`.** Every statement is either fully proved or declared as an `axiom` under the policy below. Module docstrings assert "No `sorry`" — keep that true.
- **Axioms are allowed in exactly two places:**
  - `Goldfish/Axioms.lean` — probabilistic good events (Lemma 1, Lemma 4, Proposition 1 conclusions, which hold w.o.p. via VRF lottery + Chernoff). Deterministic dependents take the good event as a hypothesis (`HonestMajorityPerSlot`, `HonestLeaderEveryWindow`, …) rather than invoking probability.
  - `Goldfish/EbbAndFlow/External.lean` — results imported from ref [61] (Neu–Tas–Tse accountability gadgets, ePrint 2021/628), each with a source comment. Formalizing [61] is out of scope.
  - Do not introduce axioms anywhere else.
- **`Goldfish/Probabilistic/`** is the separate track that replaces the good-event axioms with real measure-theoretic proofs (the `Lottery` model, Chernoff/Hoeffding bounds — paper App. G). It must never block or be depended on by the deterministic proofs.
- `autoImplicit` is off project-wide (`lakefile.toml`); bind all variables explicitly.

## Architecture

The protocol is **not implemented operationally**. `Goldfish/Protocol.lean` defines an abstract interface:

- `Execution` — observable data of a run: `Δ`, awake/honest/eligible counts, `votesFor`, `leader`, `forkChoice`, `outvotes`, `fastConfirms`, plus slot↔round arithmetic (`slotStart`/`voteRound` for the 3∆ regime, `fastSlotStart`/`fastVoteRound`/`fastConfirmRound` for 4∆).
- `Spec` — the protocol's defining behaviour bundled as hypotheses over an `Execution`. All theorems are derived from `Spec`; an executable model could later discharge its fields without changing any theorem statement.

Three proof layers, built in order (each maps to a paper appendix; per-statement files are named `TheoremN.lean` / `LemmaN.lean` / `PropositionN.lean`):

1. `Goldfish/SynchronousSecurity/` — Thm 1–3, Lem 2–3 under `(1/2, 3∆)`-compliance (App. B). Self-contained.
2. `Goldfish/FastConfirmation/` — Thm 4–6, Lem 5 under `(1/2, 4∆)`-compliance (App. C). Has its own `Spec4Δ` and `Ledger4Delta` for the 4∆ timing regime.
3. `Goldfish/EbbAndFlow/` — Thm 7, Lem 6–9, Prop 2–5 under `(1/3, 3∆)`-compliance with the accountability-gadget overlay (`Gadget`, `GadgetSpec`) (App. D). Lemmas 7/8/9 are cyclically dependent and must be proved as one simultaneous induction (`Healing.lean`).

Supporting modules: `Basic.lean` (block-tree prefix order, `(γ,τ)`-compliance, negligibility), `Ledger.lean` (confirmed-ledger layer, Def. 1 safety/liveness). Umbrella files (`Goldfish.lean`, `Goldfish/EbbAndFlow.lean`, …) just re-export; add new modules to the matching umbrella import list.

## Conventions

- One numbered statement per file; the module docstring names the paper statement it formalizes and states its dependency shape.
- Before adding a dependency between statements, check the README dependency graph — an edge `A → B` means A's proof depends on B. Update the Mermaid graph if the structure changes.
- Branches follow `feat/`, `docs/`, `refactor/` prefixes; work merges to `main` via PR (repo: NyxFoundation/goldfish-fv).
