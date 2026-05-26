# goldfish-fv

Formal-verification notes and reference material for the **Goldfish** Ethereum
consensus protocol.

## Source

Francesco D'Amato, Joachim Neu, Ertem Nusret Tas, David Tse —
*Goldfish: No More Attacks on Ethereum?!*

- IACR ePrint: <https://eprint.iacr.org/2022/1171>
- arXiv: <https://arxiv.org/abs/2209.03255> (v4, 2023-12-30)
- Published at Financial Cryptography 2024

> The source PDF is **not** committed to this repository. Download it from the
> links above and place it at `2022-1171.pdf` if you want the local copy that
> the notes reference.

## Contents

- `notes/paper-statements.md` — every numbered Definition, Lemma, Theorem and
  Proposition from the paper, each with its proof as it appears in the appendix,
  plus a glossary of recurring notation.
- `notes/_segments/` — the same statements split into one file per item
  (`definition_*`, `lemma_*`, `theorem_*`, `proposition_*`), each containing the
  statement text and its proof with source line references.

Algorithms 1–6, Figure 7, and the prose sections of the paper are intentionally
omitted — they are protocol pseudocode and commentary rather than statements to
formalize.

## Goal

Build toward a machine-checked formalization of the Goldfish safety and
liveness results, using these extracted statements as the specification target.
