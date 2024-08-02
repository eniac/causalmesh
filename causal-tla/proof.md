
Lemma 1:

$$
\forall (k, v) \in S_i.\textit{C-Cache}, \forall j, \\
S_j.\textit{C-Cache}[k].vc \ge v.vc \lor v.vc \in S_j.\textit{I-Cache}[k]
$$

Lemma 1 says a write $w$ in cache server's C-Cache implies on other servers it's either merged into C-Cache or exists in I-Cache.

Proof.

When $i = j$, it is trivial. w.l.o.g., let $i$ be 2 and $j$ be 1.

$(k, vc)$ has two sources
1. if Someone writes $w$ to $S_1$, and get passed $S_1.\textit{I-Cache} \to S_2.\textit{C-Cache}$,
      then it must either exist in $S_1.\textit{I-Cache}$ or get merged into $S_1.\textit{C-Cache}$.
2. it's integrated from $S_2.\textit{I-Cache} \to S_2.\textit{C-Cache}$, then it must be
      read by some clients other than its writer. As a client reads from C-Cache, $w$ has been
      propagated to all cache servers, including $S_1$.

Lemma 2

$$
\forall w \in S_i.\textit{I-Cache} \cup S_i.\textit{C-Cache}, \forall w' \in w.deps,
S_i.\textit{C-Cache}[w'.key].vc \ge w'.vc \lor w' \in S_i.\textit{I-Cache}
$$

Lemma 2 says during integration, all dependencies can be found.

Proof.

$w'$ has two sources

 1. $w$ and $w'$ are written by the same client. If $w$ is come from predecessor, as the channel between servers are FIFO, $w'$ must arrive before $w$. If $w$ is from client, as the client piggybacks its own writes after migration. $w'$ is always available on the new server.
2. $w$ and $w'$ have different writers. To be in $w.deps$, $w'$ or some write depends on it must be read, which implies $w'$ have been propagated to all servers, including $S_i$.

Lemma 3

A cache server's C-Cache is a cut

Proof.

We prove this by induction.
Base Case: C-Cache is initially empty, so it's a cut.
Inductive step: Assume C-Cache is a strict causal cut. C-Cache changes when

1. it receives a read from client
2. it receives a write from predecessor and it's the tail
In both cases, it integrates the dependencies, according to Lemma 2,  C-Cache is still a cut.

Theorem 1

Read transaction returns causally-consistent view of multiple keys.

Proof.

Directly from Lemma 3 and client logic.

Definition

$S \cap C$ is defined as a subset of $S$ that only consists of keys and dependencies that overlap with $C$'s deps.

Theorem 2

When a client $C$ tries to read from $S_i$, $(S_i \cap C) \cup C.local$ is a cut and it covers $C.local \cup C.deps$.

Proof.

According to Lemma 3, $(S_i \cap C)$ is a cut. After merging with $C.local$, it remains a cut. As $S_i$ integrates clients' dependencies upon read requests, the cut always covers $C.local \cup C.deps$.
