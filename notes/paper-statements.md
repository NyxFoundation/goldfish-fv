# Goldfish — paper statements and proofs (reference)

> **Source.** Francesco D'Amato, Joachim Neu, Ertem Nusret Tas, David Tse —
> *Goldfish: No More Attacks on Ethereum?!* IACR ePrint 2022/1171,
> arXiv 2209.03255 v4 (2023-12-30), Financial Cryptography 2024.
>
> Local PDF: `2022-1171.pdf` (46 pp). Extracted with `pymupdf`.
>
> This file lists every numbered Definition, Lemma, Theorem and
> Proposition from the paper, with each proof as it appears in the
> appendix. Statements that the paper duplicates between the main body
> and the appendix (Theorems 1–3, Lemmas 1–3) appear here in the
> appendix form, because that is where the formal proof lives.
> Definitions 5–6 are the paper's informal cryptographic preliminaries.
>
> Algorithms 1–6, Figure 7, and prose from §1, §3, §5, §A, §D.2 prose,
> §E, and §F are deliberately omitted — they are protocol pseudocode and
> commentary, not statements to formalize.

## Notation

A small glossary of recurring symbols, so each statement below can be read
without flipping back to §2 of the paper.

| Symbol | Meaning |
|---|---|
| `κ` | Security parameter; confirmation latency in Goldfish is `O(κ)` slots. |
| `∆` | Network delay bound under synchrony (in rounds). One Goldfish slot is `3∆` rounds (`4∆` with fast confirmation). |
| `λ` | Cryptographic security parameter (for signatures, VRFs). |
| `n`, `n_0` | Total number of validators / lower bound on awake honest validators. |
| `A_r`, `H_r` | Number of adversary / honest validators awake at round `r`. |
| `β` | Adversary fraction `A_r / (A_r + H_r-τ)` (resp. `A_r / (A_r + H_r)` with key-evolving primitives). |
| `f`, `f̄` | Adversary count and its bound; a protocol is `f̄`-safe / `f̄`-live iff it is safe/live whenever `f < f̄`. |
| `ε`, `ϵ` | Constants `> 0`; β stays strictly below `½ − ε` or `⅓ − ε` in compliant executions. |
| `w.o.p.` | "with overwhelming probability" — i.e. except with probability `negl(κ) + negl(λ)`. |
| `negl(·)` | A negligible function. |
| `B_0` | The genesis block. |
| `ch`, `ch'` | Ledgers (chains of transactions). `ch ⪯ ch'` means `ch` is a prefix of `ch'`. |
| `ch^id_r` | Ledger output by validator `id` at round `r`. |
| `ch_ava`, `ch_acc` | Available ledger (Goldfish) / accountable final prefix ledger (overlay gadget). |
| `ch⌈κ` | The prefix of `ch` obtained by truncating the last `κ` blocks (the standard κ-deep confirmation rule). |
| `B.id`, `B.t`, `B.h`, `B.txs`, `B.ϱ`, `B.σ` | Producer id, slot, parent-hash, transactions, VRF proof, and signature of a block `B`. |
| `v.id`, `v.t`, `v.h`, `v.ϱ`, `v.σ` | Same fields for a vote `v` (over a block hash `v.h`). |
| `P.B`, `P.T`, `P.σ` | A proposal's block, its block-vote-tree (bvtree), and its signature. |
| `T`, `T '`, `bvtree`, `B*`, `T *` | Block-vote-tree / buffer at a validator. `T ∪ T '` and `Merge(T, T ')` are explicit set/merge operations. |
| `Children(T, B)`, `Votes(T, B, t)` | Sub-routines used by GHOST-Eph; see Algorithm 3. |
| `GHOST-Eph(T, t)` | Vote-expiring GHOST fork choice; only votes from slot `t` count. |
| `(γ, τ)-compliant` | Execution where `β ≤ γ − ε` for all rounds, with a `τ`-round corruption delay (Def. 2). The proofs typically take `γ = ½` and `τ = 3∆` for §B/§C, and `γ = ⅓` for §D. |
| `GST`, `GAT` | Global Stabilisation Time (network) and Global Awake Time (participation) from the sleepy model. |
| `T_hor`, `T_conf`, `T_chkpt`, `T_tmout`, `T_bft`, `T_rcnt`, `T_heal` | Execution horizon, confirmation latency, checkpoint interval, timeout, BFT-overlay confirmation, recency window, healing time. |
| `Wins`, `Open`, `Prio`, `Vrf.Eval`, `Vrf.Verify` | VRF-based lottery interface (Algorithm 1, Definition 6). |
| `thr_b`, `thr_v` | Block-production / vote lottery thresholds (Algorithm 1). |
| `Sig.Gen`, `Sig.Sign`, `Sig.Verify` | Digital-signature scheme (Definition 5). |
| `LOG_bft` | Output ledger of the partially-synchronous BFT protocol underlying the accountability gadget. |

Recurring abbreviations: `Def.`, `Lem.`, `Thm.`, `Prop.`, `Alg.`, `Eq.`, `Sec.`, `App.`, `ll.` (lines), `iff`, `s.t.`, `cf.`, `i.e.`, `e.g.`, `w.r.t.`, `resp.`

PDF-extraction caveats — the text below is preserved verbatim, with two known artifacts inherited from the paper PDF:
- Subscripts and superscripts are line-broken at column boundaries, e.g. `ch^id_r` is written as `chid
r`. Read these as one symbol.
- Numerator/denominator of small fractions are split across lines: `½` appears as `( 1
2, ...)`. Likewise `⅓` and `¾`.

## Definitions

### Definition 1 — §2, p. 7 — Security

**Statement.**

```
Definition 1 (Security). Let ch ⪯ch′ express that ledger ch is a prefix of
(or the same as) ledger ch′. A consensus protocol, where at round r validator id
outputs ledger chid
r , is secure with transaction confirmation time Tconf, iff w.o.p.:
– Safety: ∀r, r′ : ∀honest id, id′ awake at r, r′ : (chid
r ⪯chid′
r′ ) ∨(chid′
r′ ⪯chid
r ).
– Liveness: If transaction tx was received by some awake honest validator by
r, then ∀r′ ≥r + Tconf : ∀honest id awake at r′ : tx ∈chid
r′.
The protocol satisfies ¯f-safety ( ¯f-liveness) if it is safe (live) if f < ¯f. It
satisfies 1/2-safety (1/2-liveness) if it is safe (live) if β < 1/2−ε for some ε > 0.
```

### Definition 2 — §B.1, p. 22 — (γ, τ)-compliant executions

**Statement.**

```
Definition 2. In the absence of key-evolving cryptographic primitives (signa-
tures and VRFs), an execution is (γ, τ)-compliant iff:
– ∀r:
Ar
Ar+Hr−τ ≤β < γ −ϵ.
– The corruption is mildly adaptive: If the adversary decides to corrupt an
honest validator at round r, then the validator becomes adversary no earlier
than at round r + τ.
With key-evolving primitives, an execution is compliant iff:
– ∀r:
Ar
Ar+Hr ≤β < γ −ϵ.
Moreover, in both cases, Hr > γn0 = Θ(κ) for all rounds r, and the time horizon
Thor of the protocol execution satisfies Thor = poly(κ).
```

### Definition 3 — §D.1, p. 30 — Security (overlay-gadget setting)

**Statement.**

```
Definition 3 (Security). Let Tconf be a polynomial function of the security
parameter κ. A state machine replication protocol that outputs a ledger ch is
secure after time Tsec, and has transaction confirmation time Tconf, iff:
Safety: For any two rounds r, r′ ≥Tsec, and any two honest validators i, j awake
at rounds r and r′, respectively, either chi
r ⪯chj
r′ or chj
r′ ⪯chi
r.
Liveness: If a transaction has been received by some awake honest validator by
some round r ≥Tsec, then for any round r′ ≥r + Tconf and any honest validator
i awake at round r′, the transaction will be included in chi
r′.
The protocol satisfies ¯f-safety ( ¯f-liveness) if it satisfies safety (liveness) as
long as the number of adversary validators f stays below ¯f for all rounds. It
satisfies 1/2-safety (1/2-liveness) if it satisfies safety (liveness) if the fraction of
adversary validators β is bounded above away from 1/2 for all rounds.
```

### Definition 4 — §D.1, p. 31 — Ebb-and-flow formulation [60,61]

**Statement.**

```
Definition 4 (Ebb-and-flow formulation [60,61]).
1. (P1: Accountability and finality) Under a partially synchronous network
in the sleepy model, the accountable final prefix ledger chacc has accountable
[Figure 7 and Algorithm 5 interleave here in the PDF; P1 continues:]
safety resilience n/3 at all times, (except w.p. negl(λ)), and there exists a
constant C such that chacc provides n/3-liveness with confirmation time Tconf
after round max(GST, GAT) + C · κ (w.o.p.).
2. (P2: Dynamic availability) Under a synchronous network in the sleepy
model ( i.e., for GST = 0), the available ledger chava provides 1/2-safety and
1/2-liveness at all times (w.o.p.).
3. (Prefix) For each honest id and round r, chid
acc,r ⪯chid
ava,r.
```

### Definition 5 — §G.1, p. 43 — Digital signature scheme (informal)

**Statement.**

```
Definition 5 (Informal, cf. [9,38]). A signature scheme Sig = (Gen, Sign, Verify)
consists of probabilistic poly-time (PPT) algorithms so that:
– (ssk, spk) ←Sig.Gen(1λ) creates a secret/public key pair.
– σ ←Sig.Sign(ssk, m) creates a signature on a message.
– {0, 1} ←Sig.Verify(spk, m, σ) verifies a signature.
– Correctness: With overwhelming probability, for all messages,
Sig.Verify(spk, m, Sig.Sign(ssk, m)) = 1.
– Security (existential unforgeability): An adversary with access to spk
and to a signing oracle Sig.Sign(ssk, .) cannot produce a valid (m, σ) other
than via the oracle.
```

### Definition 6 — §G.2, p. 43 — Verifiable random function (informal)

**Statement.**

```
Definition 6 (Informal, cf. [27, Sec. 3.2, Fig. 2], [20, 28]). A verifiable
random function (VRF) scheme Vrf = (Gen, Eval, Verify) consists of PPT algo-
rithms so that:
– (vsk, vpk) ←Vrf.Gen(1λ) samples a VRF with associated secret/public key
pair for evaluation/verification.
– (y, π) ←Vrf.Eval(vsk, x) obtains the output y of the VRF at input x, and the
evaluation proof π.
– {0, 1} ←Vrf.Verify(vpk, x, (y, π)) verifies an evaluation.

– Correctness: With overwhelming probability, for all inputs,
Vrf.Verify(vpk, x, Vrf.Eval(vsk, x)) = 1.
– Uniqueness: Per input x, there is only one output y: if
Vrf.Verify(vpk, x, (y, π)) = 1 for (y, π) = (y1, π1) and (y, π) = (y2, π2), then
y1 = y2.
– ‘Pseudorandomness’: Conceptually, the VRF behaves like a random or-
acle that is unpredictable ( i.e., without knowledge of vsk, the VRF output
cannot be distinguished from a random string) and verifiable ( i.e., given
vpk, an alleged output of the VRF can be verified). For a formal definition,
see [27, Sec. 3.2, Fig. 2].
```

## Lemmas

### Lemma 1 — §B.2, p. 23

**Statement.**

```
Lemma 1. Suppose the Goldfish execution is ( 1
2, 3∆)-compliant. Then, w.o.p.,
for every slot t, adversary validators at round 3∆(t + 1) + ∆eligible to vote at
slot t are less than honest validators awake at round 3∆t + ∆and eligible to
vote at slot t. Also w.o.p., all slot intervals of length κ have at least one slot t
where an honest validator is recognized as the slot t leader by all awake honest
validators at round 3∆t + ∆.8
Lem. 1’s proof uses correctness, uniqueness and pseudorandomness of VRF-
based lotteries along with Chernoff bounds.
```

**Proof.**

```
Proof of Lem. 1. By the pseudorandomness property of the VRF-based lottery
(App. G), for any given slot t and validators id1 and id2, id1 ̸= id2,
Pr
h
Winslv((id, t), Openlv
id1(t))
i
= thrv
(1)
Pr
h
Winslb((id, t), Openlb
id1(t))
i
= thrb
(2)
Pr
h
Prio(Openlb
id1(t)) < Prio(Openlb
id2(t))
i
= 1
2,
(3)
where lv = (vote, thrv) and lb = (block, thrb) are the lotteries, and Openlv
id1(t),
Openlb
id1(t), Openlb
id2(t), and Openlv)
id2(t) are independent random variables.
We first consider the protocol without key-evolving primitives. By the unique-
ness property of the lottery (App. G), w.o.p., for all validators id and slots t,
the ticket (id, t) can be opened at most one unique opening (Alg. 2, l. 20). Let
˜Ht denote the number of honest validators awake at round 3∆t + ∆and eligi-
ble to vote at slot t. Let ˜At denote the number of adversary validators at round
3∆(t+1)+∆that are eligible to vote at slot t. Recall that Ar and Hr denote the
number of adversary and honest validators awake at round r respectively (note
that the honest validators have been awake since the closest round 3∆t + 2∆
same as or preceding r). Let nt = H3∆t+∆+ A3∆(t+1)+∆≥n0 = Θ(κ).
By the pseudorandomness property, the adversary cannot predict in advance
which honest validators will become eligible to vote or propose at a given slot.
Moreover, if the adversary decides to corrupt the honest validators eligible to
vote at a slot t after learning their identities at round 3∆t + ∆, it takes over 3∆
rounds for the corruption to take effect, implying that these validators cannot
be counted as part of ˜At. Hence, as
Ar
Ar+Hr−3∆≤β < 1
2 −ϵ for all rounds r,
w.o.p.,
E[ ˜Ht] = H3∆t+∆thrv ≥(1
2 + ϵ)ntthrv
E[ ˜At] = A3∆(t+1)+∆thrv ≤(1
2 −ϵ)ntthrv
By a Chernoff bound,
Pr

˜Ht < 1
2ntthrv

≤e−
ϵ2
1+2ϵ ntthrv
8 The proposer-lottery threshold thrb can be tuned following Algorand [33, Appendix-
B.1] so that each slot has at least one eligible proposer.

Pr

˜At > 1
2ntthrv

≤e−
ϵ2
1+3ϵ ntthrv.
Thus, at any given slot t, ˜Ht > ˜At, except with probability
2 exp (−
ϵ2
1 + 3ϵn0thrv).
By a union bound, every slot t has more honest validators awake at round 3∆t+∆
and eligible to vote at slot t than adversary validators at round 3∆(t + 1) + ∆,
eligible to vote at slot t (and more than 1
2n0thrv such honest validators), except
with probability
2Thor exp

−
ϵ2
1 + 3ϵn0thrv

+ negl(λ) = negl(κ) + negl(λ),
since n0 = Θ(κ) and Thor = Θ(κ). By the same reasoning, w.o.p., every slot t
has more honest validators awake and eligible to propose for slot t at round 3∆t
than adversary validators at round 3∆t + ∆, eligible to propose for slot t.
Finally, for any given slot t, each valid slot t proposal broadcast within rounds
[3∆t, 3∆t + ∆] has the same probability of achieving the minimum precedence
up to terms negligible in λ.9 Now, at a slot t, if an honest validator’s proposal
achieves the minimum precedence among the valid slot t proposals broadcast by
∆rounds into the slot, then that validator is identified as the slot leader by all
honest validators awake at round 3∆t + ∆. Taking a fixed t ≥κ, the probability
that no awake honest validator’s proposal has the minimum precedence among
the valid slot s proposals broadcast by ∆rounds into the slot, during the slots
s ∈[t −κ, t], is upper bounded by 2−κ + negl(κ) + negl(λ). Union bounding over
all Thor many such intervals, we find that w.o.p., all slot intervals of length κ
have at least one slot t, where an honest validator is identified as the slot leader
by all awake honest validators at round 3∆t + ∆.
Now with key-evolving primitives, we define ˜Ht = H3∆t+∆and ˜At = A3∆t+∆.
Similarly, we define nt = H3∆t+∆+A3∆t+∆≥n0 = Θ(κ). In this case,
Ar
Ar+Hr ≤
β < 1
2 −ϵ for all rounds r. Note that the adversary cannot predict in advance
which honest validators will become eligible to vote or propose at a given slot
due to the pseudorandomness property of the lottery. Moreover, if the adversary
corrupts the honest validators eligible to vote at a slot t after learning their
identities at round 3∆t+∆, it cannot make these validators broadcast new valid
votes for slot t since the keys for slot t would have been evolved prior to adversary
corrruption (i.e., these corrupted validators cannot be counted as part of ˜At).
Hence, the number of valid slot t votes adversary validators can broadcast by
round 3∆(t + 1) + ∆is upper bounded by the number of adversary validators at
round 3∆t+∆that are eligible to vote at slot t. Finally, by the same calculations
as above, every slot t has more honest validators eligible to vote and awake at
round 3∆t + ∆than the adversary validators at round 3∆(t + 1) + ∆eligible
to vote at slot t (and more than 1
2n0thrv such honest validators), except with
9 We assume that poly(κ) negl(λ) = negl(λ).

probability
2Thor exp

−
ϵ2
1 + 3ϵn0thrv

+ negl(λ) = negl(κ) + negl(λ).
Similarly, w.o.p., every slot t has more honest validators awake and eligible
to propose for slot t at round 3∆t than adversary validators at round 3∆t +
∆eligible to propose for slot t. Thus, via the same argument, w.o.p., all slot
intervals of length κ have at least one slot t, where an honest validator is identified
as the slot leader by all awake honest validators at round 3∆t + ∆.
```

### Lemma 2 — §B.3, p. 25

**Statement.**

```
Lemma 2. Suppose an execution of Goldfish in the synchronous sleepy network
model, and validator id∗with proposal P ∗is recognized as leader of a slot t by
all awake honest validators at round 3∆t + ∆(Alg. 2, l. 16). Then, all honest
validators awake at round 3∆t + ∆and eligible to vote at t vote for P ∗.B at t.
```

**Proof.**

```
Proof. Let T ′ = P ∗.T , and B∗and T ∗denote the buffer and bvtree of
id∗at round 3∆t. Since id∗is honest, it must have broadcast P ∗at round
3∆t with bvtree T ′ = Merge(T ∗, B∗) and a new block P ∗.B with parent
GHOST-Eph(T ′, t −1) (Alg. 2, ll. 7, 8, 12).
By synchrony, any message that a non-asleep honest validator id could have
added to its bvtree Tid by 3∆(t −1) + 2∆, is received by id∗by 3∆t, and thus
in T ′. As awake honest validators do not update their bvtrees and no honest
validators turn awake in the interval (3∆(t −1) + 2∆, 3∆t + ∆), for any honest
validator id awake at round 3∆t + ∆, Tid ⊆T ′ prior to Alg. 2, l. 19.
Since id∗is recognized as the leader of slot t by all awake honest validators at
round 3∆t + ∆, at that round, each awake honest validator id merges its bvtree
with T ′ ∪{P ∗.B} (Alg. 2, l. 19) and reaches Tid = T ′ ∪{P ∗.B}. Consequently,
each honest validator id awake at round 3∆t+∆and eligible to vote at slot t votes
for P ∗.B due to the recursive structure of the GHOST-Eph rule (Alg. 3).
```

### Lemma 3 — §B.3, p. 25

**Statement.**

```
Lemma 3. Suppose a ( 1
2, 3∆)-compliant execution of Goldfish in the syn-
chronous sleepy network model. Consider a slot t where all honest validators
awake at round 3∆t + ∆and eligible to vote at slot t, vote for a descendant of
B. Then, w.o.p., all honest validators awake at round 3∆(t + 1) + ∆and eligible
to vote at slot t + 1, vote for a descendant of B.
```

**Proof.**

```
Proof. By Lem. 1, w.o.p., for every slot t, the number of adversary validators
at round 3∆(t + 1) + ∆and eligible to vote at slot t is less than the number of
honest validators awake at round 3∆t + ∆and eligible to vote at slot t.
Let t be a slot such that all honest validators awake at round 3∆t + ∆and
eligible to vote at t voted for a descendant of B. Pick any honest validator id
awake at round 3∆(t+1)+∆and eligible to vote at slot t+1. Since id must have
been awake at least since round 3∆t+2∆, its bvtree at round 3∆t+2∆contains
all votes broadcast by honest validators awake at round 3∆t + ∆and eligible to
vote at slot t (Alg. 2, l. 19). The same is true for its bvtree at round 3∆(t+1)+∆,
even after id merges its bvtree with that of any proposal (Alg. 2, l. 7). Moreover,
the number of honest validators awake at round 3∆t + ∆and eligible to vote at
slot t is greater than the number of adversary validators at round 3∆(t + 1) + ∆
that are eligible to vote at slot t.
Consequently, upon invoking the GHOST-Eph fork-choice rule at round
3∆(t+1)+∆(Alg. 2, l. 22), id observes that at every iteration of the fork choice
(Alg. 3, l. 7), blocks consistent with B have more votes than blocks conflicting
with B. Thus, at round 3∆(t + 1) + ∆, fork choice returns a descendant of B,
and id votes for it.
```

### Lemma 4 — §C, p. 27

**Statement.**

```
Lemma 4. Suppose the Goldfish execution is ( 1
2, 4∆)-compliant. Then, w.o.p.,
for every slot t, the number of adversary validators at round 4∆(t + 1) + ∆,
eligible to vote at slot t, is less than the number of honest validators, awake at
round 4∆t + ∆and eligible to vote at slot t. Also w.o.p., all slot intervals of
length κ have at least one slot t, where an honest validator is identified as the
slot leader by all awake honest validators at round 4∆t + ∆.
```

**Proof.**

```
Proof of Lem. 4 is analogous to the proof of Lem. 1, and follows from the
same arguments using ( 1
2, 4∆)-compliant executions.
```

### Lemma 5 — §C, p. 27

**Statement.**

```
Lemma 5. Suppose the Goldfish execution is ( 1
2, 4∆)-compliant in the syn-
chronous sleepy network model, and an honest validator id∗fast confirms a block
B at slot t. Then, w.o.p, all honest validators awake at round 4∆(t+1)+∆and
eligible to vote at slot t + 1, vote for a descendant of B at slot t + 1.
```

**Proof.**

```
Proof of Lem. 5. By Prop. 1, w.o.p., the number of adversary validators at round
4∆(t + 1) + ∆, eligible to vote at slot t, is less than 1
2n thrv. An eligible awake
honest validator sends a single slot t vote at round 4∆t + ∆, implying that over
( 3
4 + ϵ
2)n thrv −1
2n thrv = ( 1
4 + ϵ
2)n thrv validators broadcast a single slot t vote
by round 4∆(t+1)+∆, and that is for a descendant of B. By Prop. 1, w.o.p., for
all slots t, there can be at most (1 + ϵ)n thrv validators that are eligible to vote
at t. Hence, the number of valid slot t votes for the descendants of any block B′
conflicting with B must be less than (1+ϵ)n thrv −( 1
4 + ϵ
2)n thrv = ( 3
4 + ϵ
2)n thrv
at any given round. The validator id∗broadcasts B and over ( 3
4 + ϵ
2)n thrv valid
votes for it (in pieces) at round 4∆t+2∆. Each honest validator, awake at round
4∆(t+1)+∆and eligible to vote at slot t+1, observes these votes in its bvtree at
the round of voting (Alg. 4, l. 11). Upon invoking the GHOST-Eph fork-choice
rule at any of the rounds 4∆t + 3∆, 4∆(t + 1) or 4∆(t + 1) + ∆(Alg. 2, ll. 8,
22, 28), for any awake honest validator id with bvtree T ′, Votes(T ′, B, t) >
Votes(T ′, B′, t) for any block B′ conflicting with B. This implies that all honest
validators, awake at round 4∆(t + 1) + ∆and eligible to vote at slot t + 1 all
vote for B or one of its descendants at slot t + 1.
```

### Lemma 6 — §D.4, p. 35 — Safety and liveness of ch_ava under synchrony

**Statement.**

```
Lemma 6 (Safety and liveness of chava under synchrony). Suppose a
( 1
2, 3∆)-compliant execution of Goldfish in the synchronous sleepy network model
of Sec. 2. Then, w.o.p., the available ledger chava satisfies 1/2-safety and 1/2-
liveness (at all times).
```

**Proof.**

```
Proof. By Prop. 2, checkpointing of blocks does not alter the fork-choice rule at
Alg. 5, l. 2 for any awake honest validator. Concretely, if the honest validators
started the fork-choice rule from the genesis block at all rounds instead of the
latest checkpoint in view, then they would end up with the same execution.
Thus, the security of chava follows from Thm. 2.
```

### Lemma 7 — §D.5, p. 36 — Liveness of ch_acc (analogue of Thm. 4 of [61])

**Statement.**

```
Lemma 7 (Liveness of chacc, analogue of Thm. 4 of [61]). Consider a
( 1
3, 3∆)-compliant execution of Goldfish in the partially synchronous sleepy net-
work model of Sec. 2. Suppose chava is secure (safe and live) after some round
Theal ≥max(GST, GAT) + ∆+ Tchkpt. Then, w.o.p., chacc satisfies n/3-liveness
after round Theal with transaction confirmation time Tconf = Θ(κ2).
```

**Proof.**

```
Proof of Lem. 7 follows from the proof of [61, Thm. 4].
Proof. By Prop. 3, LOGbft is live with transaction confirmation time Tbft after
max(GST, GAT), a fact we will use subsequently.
Let c′ be the largest iteration such that a block B was checkpointed in the
view of some honest validator before max(GAT, GST) (Let c′ = 0 and B be the
genesis block if there does not exist such an iteration). Then, by Prop. 4, entrance
times of the honest validators to subsequent iterations become synchronized by
round max(GAT, GST) + ∆+ Tchkpt: If an honest validator enters an iteration
c > c′ at some round r ≥max(GAT, GST) + ∆+ Tchkpt, every honest validator
enters iteration c by round r + ∆.
Suppose an iteration c > c′ has an honest iteration leader L(c), which sends
a checkpoint proposal, denoted by ˆbc, at some round r > Theal + Tchkpt. The
proposal ˆbc is received by every honest validator by round r + ∆. Since the
entrance times of the validators are synchronized by Theal ≥max(GST, GAT) +
∆+Tchkpt, every honest validator sends a gadget vote by round r+∆. By Lem. 9,
ˆbc ⪯B⌈κ for any B identified in Alg. 2, ll. 8, 22, 28 by any awake honest validator
after r. Moreover, ˆbc is a descendant all of the checkpoints seen by the honest
validators until then. Consequently, at iteration c, every honest validator sends
a gadget vote accepting ˆbc by round r + ∆, all of which appear within LOGbft
in the view of every honest validator by round r + ∆+ Tbft. Thus, ˆbc becomes
checkpointed in the view of every honest validator by round r + ∆+ Tbft. (Here,
we assume that Ttmout was chosen large enough for Ttmout > ∆+ Tbft to hold.)
Since r > Theal +Tchkpt, by Lem. 9, ˆbc contains at least one honest block since
an earlier checkpointed block in its prefix from before iteration c. This implies
that the prefix of ˆbc contains at least one fresh honest block that enters chacc by
round r + ∆+ Tbft.
Next, we show that an adversary leader cannot make an iteration last longer
than ∆+ Ttmout + Tbft for any honest validator after the initial Tchkpt period
elapsed. Indeed, if an honest validator id enters an iteration c at round r−Tchkpt,
by round r + Ttmout, either it sees a block (potentially ⊥) become checkpointed
for iteration c, or it sends a reject vote for iteration c. In the first case, every
honest validator sees a block checkpointed for iteration c by round at most
r + Ttmout + ∆. In the second case, rejecting gadget votes from over 2n/3 > n/3
validators appear in LOGbft in the view of every honest validator by round at
most r + Ttmout + ∆+ Tbft. Hence, a new checkpoint, potentially ⊥, is output in
the view of every honest validator by round r + Ttmout + ∆+ Tbft.
Finally, we observe that except with probability (1/3)κ, there exists a check-
point iteration with an honest leader within κ consecutive iterations. Since an
iteration lasts at most max(∆+ Ttmout + Tbft, ∆+ Tchkpt + Tbft) ≤∆+ Tchkpt +

Ttmout+Tbft = Θ(κ) rounds, and a new checkpoint containing a fresh honest block
in its prefix appears when an iteration has an honest leader (Lem. 9), w.o.p., any
transaction received by an honest validator at round t appears within chacc in the
view of every honest validator by round at most t+κ(∆+Ttmout +Tbft +Tchkpt).
Hence, via a union bound over the total number of iterations (which is a poly-
nomial in κ), we observe that if chava satisfies security after some round Theal,
then w.o.p., chacc satisfies liveness after Theal with a transaction confirmation
time Tconf = Θ(κ2).
The latency expression Tconf = Θ(κ2) stated in Lem. 7 is a worst-case latency
to guarantee that an honest block enters the accountable, final prefix ledger chacc
with overwhelming probability. In the expression, the first κ term comes from the
requirement to have Tchkpt = Θ(κ) slots in between the accountability gadget
iterations, and the second κ term comes from the fact that it takes Θ(κ) iterations
for the accountability gadget to have an honest iteration leader except with
probability negl(κ). The accountability gadget protocol asks honest validators
to wait for Tchkpt = Θ(κ) slots in between iterations to ensure the security of
the protocol, reasons for which will be evident in the proof of Lem. 9.
Unlike the worst-case latency, the expected latency for an honest block to
enter chacc after chava regains its security would be Θ(κ) as each checkpointing
iteration has an honest leader with probability at least 2/3. In this context, the
latency of Θ(κ) is purely due to the requirement to have Tchkpt = Θ(κ) slots
in between the accountability gadget iterations. Here, waiting for Tchkpt slots in
between iterations guarantees the inclusion of a new honest block in chava, which
in turn appears in the prefix of the next checkpoint, implying a liveness event
whenever there is an honest iteration leader.
Lem. 7 requires the available ledger chava to eventually regain security under
partial synchrony when there are less than n/3 adversary validators. Towards
this goal, we first analyze the gap and recency properties, the core properties
that must be satisfied by the accountability gadget for recovery of security of
chava. The gap property states that the blocks are checkpointed sufficiently apart
in time, controlled by the parameter Tchkpt:
```

### Lemma 8 — §D.5, p. 38 — Recency property (analogue of Lem. 1 of [61])

**Statement.**

```
Lemma 8 (Recency property, analogue of Lem. 1 of [61]). Consider
a ( 1
3, 3∆)-compliant execution of Goldfish in the partially synchronous sleepy
network model of Sec. 2. Every checkpointed block proposed after max(GST, GAT)
is Trcnt-recent for Trcnt = ∆+ Ttmout + Tbft.
```

**Proof.**

```
Proof. By the proof of Lem. 7, if a block B proposed after max(GST, GAT)
is checkpointed in the view of an honest validator at some round r, it should
have been proposed after round r −(∆+ Ttmout + Tbft). Moreover, over 2n/3
validators must have sent accepting gadget votes for B by round r. Let id denote
such an honest validator. It would vote for B only after it sees the checkpoint
proposal for iteration c, i.e., after round r −Trcnt = r −(∆+ Ttmout + Tbft),
and only if the proposal is confirmed in its view. Hence, B must be κ slots
deep in the chain returned at Alg. 2, l. 28 by validator id at some round within
[r −Trcnt, r]. This concludes the proof that every checkpointed block proposed
after max(GST, GAT) is Trcnt-recent.
```

### Lemma 9 — §D.5, p. 38 — Healing property (analogue of Thm. 5 of [61])

**Statement.**

```
Lemma 9 (Healing property, analogue of Thm. 5 of [61]). Consider a
( 1
3, 3∆)-compliant execution of Goldfish in the partially synchronous sleepy net-
work model of Sec. 2. Then, chava is secure with transaction confirmation time
Tchkpt + Ttmout + Tbft = Θ(κ) after round max(GAT, GST) + ∆+ 2Tchkpt.
Moreover, for the iteration proposal ˆbc of an honest iteration leader broadcast
at round r, it holds that ˆbc ⪯B⌈κ for any B identified in Alg. 2, ll. 8, 22, 28 by
any awake honest validator after r, and ˆbc contains a fresh honest block that is
not in the prefix of any checkpoint from before iteration c.
```

**Proof.**

```
Proof of Lem. 9 is different from the proof of [61, Thm. 5] since the account-
ability gadget is applied to a longest chain protocol in [61], whereas it is applied
to Goldfish in our case. Therefore, the full proof is presented below.
Proof. By [61, Thm. 3], chacc provides accountable safety with resilience n/3 ex-
cept with probability negl(λ) in the partially synchronous sleepy network model.
As the execution is ( 1
3, 3∆)-compliant, w.o.p., no two checkpoints observed by
awake honest validators conflict.
Let c be the largest iteration such that a block B was checkpointed in the
view of some honest validator before max(GAT, GST). (Let c = 0 and B be the
genesis block if there does not exist such an iteration.) Then, by Prop. 4, if an
honest validator enters an iteration c′ > c at some round r ≥max(GAT, GST) +
∆+Tchkpt, every honest validator enters iteration c by round r+∆. Let c′ be the
first iteration such that the first honest validator to enter c′ enters it after round
max(GAT, GST)+∆+Tchkpt (e.g., at some round r such that max(GAT, GST)+
∆+ Tchkpt < r < max(GAT, GST) + ∆+ 2Tchkpt). Then, all honest validators
enter iteration c′ and agree on the last checkpointed block within ∆rounds.
Subsequently, the honest validators wait for Tchkpt rounds before casting any
gadget vote for a checkpoint proposal of iteration c′, during which no block can
be checkpointed (Prop. 5, gap property).
By Lem. 1, w.o.p., the slot interval of length κ starting after round r + ∆
contains a slot t with an honest leader and proposal P ∗. After round r ≥GST,

all messages broadcast by honest validators are received by all honest validators
within ∆rounds. As honest validators agree on the last checkpointed block
during the interval [r + ∆, r + Tchkpt], by the absence of new checkpoints, the
GHOST-Eph fork-choice rule starts at the same last checkpointed block for all
honest validators during the interval (Alg. 3, l. 2). Then, by Lem. 1, w.o.p.,
P ∗.B ⪯B for any B identified in Alg. 2, ll. 8, 22, 28 by any awake honest
validator in any round after 3∆t+2∆, until at least a new block is checkpointed
in the view of an honest validator.
By Lem. 8 (recency property), the next block checkpointed in the view of
an honest validator (which happens earliest at some iteration c′′ ≥c′ and round
r′ ≥r + Tchkpt by Prop. 5, the gap property) must have been confirmed by
some honest validator id at some round within [r′ −Trcnt, r′], where r′ −Trcnt ≥
r + 6∆κ + 4∆. Hence, the new checkpointed block is κ slots deep in the chains
identified in Alg. 2, ll. 8, 22, 28 by id, and is a descendant of P ∗.B. This implies
P ∗.B ⪯B for any B identified in Alg. 2, ll. 8, 22, 28 by any awake honest
validator in any round after 3∆t + 2∆indefinitely.
Note that if the iteration leader was honest, for its proposal ˆbc broadcast at
some round r′′, it holds that ˆbc ⪯B⌈κ for any B identified in Alg. 2, ll. 8, 22, 28
by any awake honest validator after round r. Moreover, P ∗.B ⪯ˆbc, implying
that honest checkpoint proposals contain fresh honest blocks in their prefixes.
Finally, we extend the above argument to future checkpoints by induction.
Let Bn denote the sequence of checkpointed blocks, ordered by their iteration
numbers cn ≥c′, c1 = c′′. The rounds rn, at which the blocks Bn are first
checkpointed in the view of an honest validator satisfy the relation rn+1 ≥
rn + Tchkpt and r1 = r′′. Via the inductive assumption and the reasoning above,
w.o.p., in each interval [rn+∆, rn+1−Trcnt], there exists a slot tn with an honest
leader and proposal Pn such that Pn.B ⪯B for any B identified in Alg. 2, ll. 8,
22, 28 by any awake honest validator in any round after 3∆tn + 2∆indefinitely.
Hence, for a sufficiently large confirmation time exceeding the maximum possible
iteration length (i.e., Tconf ≥Tchkpt+Ttmout+Tbft), these honest blocks imply the
security of the Goldfish protocol after round max(GAT, GST) + ∆+ 2Tchkpt.
Thm. 1 holds for the honest blocks proposed in intervals [rn+∆, rn+1−Trcnt]
as all honest validators agree on the latest checkpoint during these intervals.
```

## Theorems

### Theorem 1 — §B.3, p. 25 — Safety from honest-leader proposal

**Statement.**

```
Theorem 1. Suppose a ( 1
2, 3∆)-compliant execution of Goldfish in the syn-
chronous sleepy network model of Sec. 2, and validator id with proposal P ∗is
recognized as the leader of a slot t by all awake honest validators at round 3∆t+∆
(Alg. 2, l. 16). Then, w.o.p., P ∗.B ⪯B for any B identified in Alg. 2, ll. 8,
22, 28 by any awake honest validator in any round r ≥3∆t + 2∆.
```

**Proof.**

```
Proof of Thm. 1. From Lems. 1, 2 and 3, it follows by induction that w.o.p., for
all t′ ≥t, all honest validators awake at round 3∆t′ + ∆and eligible to vote at
slot t′, vote for a descendant of P ∗.B.
By synchrony, the honest votes of slot t′ reach all honest validators awake
at 3∆t′ + 2∆by then, when they also merge the votes into their bvtrees. The
number of honest validators awake at round 3∆t′ +∆and eligible to vote at slot
t′ is greater than the number of adversary validators by round 3∆(t′+1)+∆that
are eligible to vote at slot t′ (by Lem. 1). Upon invoking the GHOST-Eph rule of
Alg. 2, ll. 8, 22, 28 at 3∆t′ + 2∆, 3∆(t′ + 1) and 3∆(t′ + 1) + ∆, respectively, an
awake honest validator id (who must have been awake since at least 3∆t′ + 2∆,
due to the joining procedure) observes that at every iteration of the fork choice
(Alg. 3, l. 7), blocks consistent with P ∗.B have more votes than blocks conflicting
with P ∗.B. Thus, id’s fork choice reaches a descendant of P ∗.B.
```

### Theorem 2 — §B.3, p. 25 — Security (T_conf = 2κ + 2 slots)

**Statement.**

```
Theorem 2 (Security). Suppose a ( 1
2, 3∆)-compliant execution of Goldfish in
the synchronous sleepy network model. Then, w.o.p., Goldfish is secure with
transaction confirmation time Tconf = 2κ + 2 slots.
```

**Proof.**

```
Proof of Thm. 2. By Lem. 1, w.o.p., all slot intervals of length κ have at least one
slot t, where an honest validator with proposal P ∗is recognized as the slot leader
by all awake honest validators at round 3∆t + ∆, and, by Thm. 1, P ∗.B ⪯B
for any B identified in Alg. 2, ll. 8, 22, 28 by any awake honest validator in any
r ≥3∆t + 2∆.
Liveness. A transaction tx is input to an honest validator at some round r. At
most 6∆rounds (i.e., 2 slots) later the transaction is propagated to all honest
validators and we have reached the beginning of a slot t0. For the next κ slots all
honest proposers will include tx if they extend a tip whose chain does not include
tx yet. By the earlier argument, one of these proposals will be an ancestor of
any B identified in Alg. 2, ll. 8, 22, 28 by any awake honest validator in any
r′ ≥3∆(t0 + κ) + 2∆. From κ slots later onwards, all awake honest validators
include the transaction in their ledger (Alg. 2, l. 29). Thus, Goldfish is live with

Tconf = 2κ + 2 slots.
Safety. Pick any two honest validators id1 and id2, and two slots t1 and t2 ≥
t1. By the earlier argument, there exists a block B′ proposed (by an honest
validator) at some slot t′ ∈[t1 −κ, t1] such that B′ ⪯B for any B identified
in Alg. 2, ll. 8, 22, 28 by any awake honest validator in any r′ ≥3∆t′ + 2∆.
As t′ ≥t1 −κ but by Goldfish’s confirmation rule blocks in chid1
t1 are from no
later than t1 −κ, chid1
t1 ⪯B. Similarly, if t′ ≥t2 −κ, then chid2
t2 ⪯B; otherwise,
B ⪯chid2
t2 . In both cases, either chid1
t1 ⪯chid2
t2 or chid2
t2 ⪯chid1
t1 .
```

### Theorem 3 — §B.3, p. 25 — Reorg resilience

**Statement.**

```
Theorem 3 (Reorg resilience). Suppose a ( 1
2, 3∆)-compliant execution of
Goldfish in the synchronous sleepy network model, and validator id with pro-
posal P ∗is recognized as the leader of a slot t by all awake honest validators at
round 3∆t + ∆(Alg. 2, l. 16). Then, w.o.p., ∃r′ : ∀r ≥r′ : ∀id: P ∗.B ⪯chid
r ,
where chid
r denotes Goldfish’s ledger at validator id and round r. In particular,
r′ = 3∆(t + κ) + 2∆satisfies the above.
We first prove Thms. 2 and 3 from Thm. 1 and Lem. 1. Then, we prove
Thm. 1 from the subsequent Lems. 1, 2 and 3.
```

**Proof.**

```
Proof of Thm. 3. By Thm. 1, P ∗.B ⪯B for any B identified in Alg. 2, ll. 8,
22, 28 by any awake honest validator in any r ≥3∆t + 2∆. From κ slots
later onwards, all awake honest validators include the transaction in their ledger
(Alg. 2, l. 29).
```

### Theorem 4 — §C, p. 27 — Safety with fast confirmation

**Statement.**

```
Theorem 4. Suppose the Goldfish execution is ( 1
2, 4∆)-compliant in the syn-
chronous sleepy network model, and an honest validator id∗fast confirms a block
B at slot t. Then, w.o.p., B ⪯B for any B identified in Alg. 2, ll. 8, 22, 28 by
any awake honest validator in any round r ≥4∆(t + 1) + ∆.
```

**Proof.**

```
Proof of Thm. 4. Follows by Lems. 4, 5 and 3, by the same inductive argument
used in the proof of Thm. 1, in that case following from Lems. 1, 2 and 3. Here,
Lem. 4 is the analogue of Lem. 1 with the new slot structure, and Lem. 5 provides
the base case, substituting Lem. 2.
```

### Theorem 5 — §C, p. 28 — Security with fast confirmation

**Statement.**

```
Theorem 5. Suppose the Goldfish execution is ( 1
2, 4∆)-compliant. Then, Gold-
fish with fast confirmations satisfies safety (w.o.p.).
```

**Proof.**

```
Proof of Thm. 5. If an honest validator fast confirms a block B at slot t, then
B is in the canonical GHOST-Eph chain of every awake honest validator at all
slots larger than t by Thm. 4. Therefore, B is in the κ-slots-deep prefix of the
canonical GHOST-Eph chains of all awake honest validators at slot t + κ, and
thus confirmed by them with the standard confirmation rule. Therefore, Thm. 2
implies the safety of the protocol.
In ( 1
2, 4∆)-compliant executions, we automatically get liveness of Goldfish
with fast confirmations from the liveness of the standard confirmation rule, since
fast confirmation is not needed for a block to be confirmed. Under optimistic
conditions, liveness of fast confirmations holds as well. We prove that a block
within an honest, valid proposal is immediately fast confirmed within the same
slot by the awake honest validators, if there are over ( 3
4 + 3
2ϵ)n awake, honest
validators at the voting time of the given slot, implying the liveness of fast
confirmations under optimistic conditions.
```

### Theorem 6 — §C, p. 28 — Reorg resilience and fast-confirmation liveness

**Statement.**

```
Theorem 6. Suppose the Goldfish execution is ( 1
2, 4∆)-compliant. Then, Gold-
fish with fast confirmations satisfies liveness with Tconf = Θ(κ) (w.o.p.).
Consider a slot t, such that there are ( 3
4 + 3
2ϵ)n thrv honest validators eligible
to vote at slot t and awake at round 4∆t+∆. Suppose an honest validator id with
proposal P ∗is recognized as the leader of a slot t by all awake honest validators
at round 4∆t + ∆(Alg. 2, l. 16). Then all honest validators awake at round
4∆t + 2∆fast confirm P ∗.B in Alg. 4, l. 9.
Liveness is stated below and follows from Thm. 2 and fast confirmation from
Lem. 2.
```

**Proof.**

```
Proof of Thm. 6. Proof of liveness follows from Thm. 2.
For the second part of the proof, by Lem. 2, all of eligible and awake honest
validators vote for P ∗.B at slot t. Then, the buffer of any honest validator awake
at round 4∆t + 2∆contains at least ( 3
4 + ϵ
2)n thrv votes (by Chernoff bound) for
the block P ∗.B, implying that all honest validators awake at rounds 4∆t + 2∆
fast confirm P ∗.B at the respective slots.
```

### Theorem 7 — §D.2, p. 33 — Ebb-and-flow property

**Statement.**

```
Theorem 7 (Ebb-and-flow property). Goldfish combined with accountability
gadgets (cf. App. D.2) satisfies the ebb-and-flow property of Def. 4.
```

**Proof.**

```
Proof of Thm. 7. We first show the property P1, namely, the accountable safety
and liveness of the accountable, final prefix ledger chacc under partial synchrony
in the sleepy model. By [61, Thm. 3], chacc provides accountable safety with
resilience n/3 except with probability negl(λ) under partial synchrony in the
sleepy model. By Lem. 9, under the same model, the available ledger chava is
secure after round max(GAT, GST) + ∆+ 2Tchkpt. Using this fact and Lem. 7,
we can state that, w.o.p., chacc satisfies liveness after round max(GAT, GST) +
∆+ 2Tchkpt with transaction confirmation time Tconf = Θ(κ2).
Finally, the property P2 follows from Lem. 6, and Prefix follows by construc-

tion of the ledgers chacc and chava. This concludes the proof of the ebb-and-flow
property.
```

## Propositions

### Proposition 1 — §C, p. 27 — At most O(n thr_v) eligible voters per slot

**Statement.**

```
Proposition 1. Suppose Thor = poly(κ). Then, w.o.p., there can be at most
(1 + ϵ)n thrv validators that are eligible to vote at any given slot. If the Goldfish
execution is ( 1
2, 4∆)-compliant, then, w.o.p., for all slots t, the number of ad-
versary validators at round 4∆(t + 1) + ∆, eligible to vote at slot t, is less than
1
2n thrv.
```

**Proof.**

```
Proof follows from a Chernoff bound.
```

### Proposition 2 — §D.4, p. 35

**Statement.**

```
Proposition 2. Suppose a ( 1
2, 3∆)-compliant execution of Goldfish in the syn-
chronous sleepy network model of Sec. 2. If a block B is observed to be check-
pointed by an honest validator for the first time at some round r, then B is in
the common prefix of the chains identified in Alg. 2, ll. 8, 22, 28 right before
round r by all awake honest validators.
```

**Proof.**

```
Proof. Since the execution is ( 1
2, 3∆)-compliant, for a block to become check-
pointed, at least one honest validator must have sent an accepting gadget vote
for that block. Let Bi denote the sequence of checkpointed blocks listed in the
order of the rounds ri at which, an awake honest validator observed Bi to be
checkpointed for the first time. Proof is by induction on these blocks’ indices.
Induction Hypothesis.
Bi is in the common prefix of the chains identified in
Alg. 2, ll. 8, 22, 28 right before round ri by all awake honest validators, and
stays so until at least round ri+1.
Base Case. Since an honest validator sends an accepting gadget vote only for a
confirmed block (i.e., κ slots deep), B1 must have been confirmed by an honest
validator at some slot t1 before round r1. As all honest validators start the fork-
choice at the genesis block prior to r1 and B1 is confirmed in an honest view, it
is in the prefix of a block proposed by an honest leader by Lem. 1 and Thm. 1.
Hence, B1 is in the common prefix of the chains identified in Alg. 2, ll. 8, 22, 28
right before round r1 by all awake honest validators. It also stays in the common
prefix until at least round r2.
Inductive Step.
By the induction hypothesis, checkpointing of the blocks
B1, . . . , Bi−1 does not alter the fork-choice rule at Alg. 5, l. 2 for any awake
honest validator. Hence, by the same reasoning above, Bi is in the common
prefix of the chains identified in Alg. 2, ll. 8, 22, 28 right before round ri by all
awake honest validators, and stays so until at least round ri+2.
```

### Proposition 3 — §D.5, p. 36 — (Prop. 2 of [61]) BFT n/3-liveness

**Statement.**

```
Proposition 3 (Prop. 2 of [61]). The BFT protocol satisfies n/3-liveness
after max(GST, GAT) with transaction confirmation time Tbft < ∞.
```

### Proposition 4 — §D.5, p. 36 — (Prop. 3 of [61])

**Statement.**

```
Proposition 4 (Prop. 3 of [61]). Consider a ( 1
3, 3∆)-compliant execution
of Goldfish in the partially synchronous sleepy network model of Sec. 2. Sup-
pose a block from iteration c was checkpointed in the view of an honest valida-
tor at round r. Then, every honest validator enters iteration c + 1 by round
max(GST, GAT, r) + ∆.
Let c′ be the largest iteration such that a block B was checkpointed in the
view of some honest validator before max(GAT, GST). (Let c′ = 0 and B be the
genesis block if there does not exist such an iteration.) If an honest validator
enters an iteration c′′ > c′ at some round r ≥max(GAT, GST) + ∆+ Tchkpt,
every honest validator enters iteration c′′ by round r + ∆.
```

**Proof.**

```
Proof of Prop. 4 follows from the proof of [61, Prop. 3].
Proof. Suppose a block B from iteration c was checkpointed in the view of an
honest validator id at round r. Then, there are over 2n/3 accepting gadget votes
for B from iteration c on LOGr
bft,id, the output ledger of the BFT protocol in id’s
view at round r. All gadget votes and BFT protocol messages observed by id by
round r are delivered to all other honest validators by round max(GST, GAT, r)+
∆. Hence, by the safety of the BFT protocol when f < n/3, for any honest
validator id′, the ledger LOGr
bft,id is the same as or a prefix of the ledger observed
by id′ at round max(GST, GAT, r) + ∆. Thus, for any honest validator id′, there
are over 2n/3 accepting gadget votes for B from iteration c on LOGbft at round
max(GST, GAT, r)+∆. This implies every honest validator enters iteration c+1
by round max(GST, GAT, r) + ∆.
Finally, by the reasoning above, all honest validators enter iteration c′ + 1
by round max(GAT, GST) + ∆. Thus, entrance time of the honest validators
to subsequent iterations have become synchronized by round max(GAT, GST) +
∆+ Tchkpt: If an honest validator enters an iteration c′′ > c′ at some round
r ≥max(GAT, GST) + ∆+ Tchkpt, every honest validator enters iteration c′′ by
round r + ∆. Similarly, if a block from iteration c′′ is first checkpointed in the
view of an honest validator at some round after max(GAT, GST) + ∆+ Tchkpt,
then it is checkpointed in the view of all honest validators within ∆rounds.
```

### Proposition 5 — §D.5, p. 38 — Gap property (analogue of Prop. 4 of [61])

**Statement.**

```
Proposition 5 (Gap property, analogue of Prop. 4 of [61]). Consider
a ( 1
3, 3∆)-compliant execution of Goldfish in the partially synchronous sleepy
network model of Sec. 2. Given any round interval of size Tchkpt, no more than a
single block can be checkpointed in the interval in the view of any honest validator.
```

**Proof.**

```
Proof of Prop. 5 follows from the fact that upon observing a new checkpoint
that is not ⊥for an iteration, honest validators wait for Tchkpt rounds before
sending gadget votes for the checkpoint proposal of the next iteration, and there
cannot be two conflicting checkpoints for the same iteration in the view of any
honest validator.
As in [61] and [69], we state that a block B∗checkpointed at iteration c and
round r > max(GST, GAT) in the view of an honest validator id is Trcnt-recent if
B∗⪯B⌈κ for B identified in Alg. 2, l. 28 by id′ at some round within [r−Trcnt, r].
Then, we can express the recency property as follows:
```

