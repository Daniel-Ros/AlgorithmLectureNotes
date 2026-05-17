#import "settings/mstyle.typ": *
#import algorithmic: algorithm-figure, style-algorithm
#show: style-algorithm

#show: conf.with(
  handout: false,
  subtitle: [Minimum Set-Cover],
)

#title-slide()

= The Minimum Set-Cover Problem

== Hypergraphs

#definition[
  *Hypergraph*

  By a *hypergraph* we mean an ordered pair $H := (V, cal(E))$ with $cal(E) subset.eq cal(P)(V)$.

  - If all members of $cal(E)$ are *pairs*, then $H$ is called a *graph*
  - Members of $cal(E)$ are called *hyper-edges*
]

#place(
    dx: 45%,
    dy: 5%,
    figure(image("figures/ASC1.png", width: 50%),)
  )

#pause

*FYI:* If $|e| = k$ for all $e in cal(E)$, then $H$ is called *$k$-uniform*.

#h(2em) $sbullet$ A graph is a *2-uniform* hypergraph.

== The Problem

#problem[
  *Minimum Set-Cover (SC)*

  *Instance:* A hypergraph $H := (V, cal(E))$.

  *Goal:* A subset $C subset.eq cal(E)$ such that $union.big_(e in C) e = V$, minimising $|C|$.

  *Put another way:* We seek a minimum *hyper-edge-cover* of $H$.
]

#pause

- Recall: for graphs, the minimum *edge-cover* problem is in $P$.
- The minimum SC problem is *NP-complete* #h(1fr) (we return to this below)

== Some Examples

- *Example 1:* $n$ elements in a single row. One hyperedge covers all $=>$ *optimal solution has size 1*.

#pause

- *Example 2:* A $3 times 6$ grid of elements.

  The highlighted (yellow) column-covering hyperedges form a cover of size $6$.

  The *optimal solution uses these columns*.

== Min SC is NPC

$"VC" := {(G, k) : tau(G) <= k}$ #h(2em) $"SC" := {(H, k) : H "has a hyper-edge cover of size" <= k}$

*Claim:* $"VC" <=_P "SC"$.

#pause

For each $u in V(G)$, define: $S_u := {e in cal(E)(G) : u in e}$.

Given $(G, n)$, define a hypergraph $H$ by:
$ V(H) := cal(E)(G), quad cal(E)(H) := {S_u : u in V(G)} $

#pause

#question[
  *H.W.* Complete the argument.
]

= Greedy Algorithm for Minimum Set-Cover

== The Algorithm

*Notation:* For a set-system $A$, write $union.big A := union.big_(e in A) e$.

#algorithm-figure(
  [Greedy-SC],
  vstroke: .5pt + luma(200),
  {
    import algorithmic: *
    Assign([$A$], [$emptyset$])
    While([$union.big A != V$], {
      Assign([$e$], [$arg max{|e without union.big A| : e in cal(E)}$])
      Assign([$A$], [$A union {e}$])
    })
    Return([$A$])
  }
)

#pause

#question[
  What is the approximation ratio of the greedy algorithm?
]

== Analysis Setup

Set $m := max{|e| : e in cal(E)}$ — the size of the *largest* hyperedge. Trivially $m <= |V(H)| = n$.

#pause

#theorem[
  The greedy algorithm is an $O(ln m)$-approximation for minimum set-cover.
]

#pause

#observation[
  Size of the cover output $=$ \# iterations greedy performs.
]

*Define:* $A_i$ = greedy solution at the *beginning* of the $i$-th iteration.
- Greedy transitions $A_i -> A_{i+1}$ during iteration $i$
- \# new vxs covered $= |union.big A_{i+1}| - |union.big A_i|$ #h(0.5em) (all from $V(H) without union.big A_i$)

== Key Observation

Let $"OPT"$ = size of an optimal cover. An optimal solution $P := {e_1, dots, e_"OPT"}$ contains $e_j$ s.t.:
$ |e_j inter (V(H) without union.big A_i)| >= (|V(H) without union.big A_i|) / "OPT" $

#pause

Since $A_i$ is constructed *greedily*:

#observation[
  $forall i in NN: quad |union.big A_{i+1}| - |union.big A_i| >= (|V(H) without union.big A_i|) / "OPT"$
]

#pause

*Q:* Once $A_{i+1}$ is defined, how many vxs are left to cover?

$
|V(H) without union.big A_{i+1}| &= |V(H)| - |union.big A_{i+1}| \
&<= |V(H)| - |union.big A_i| - (|V(H) without union.big A_i|) / "OPT" \
&= (1 - 1/"OPT") |V(H) without union.big A_i|
$

#pause

#observation[
  $|V(H) without union.big A_{i+1}| <= (1 - 1/"OPT") |V(H) without union.big A_i|$

  After each iteration, the \# of left-over vxs reduces by a factor of $(1 - 1\/"OPT")$.
]

== Recursive Pattern

Set $U_i := V(H) without union.big A_i$ (left-over vxs at iter $i$), $U_0 = V(H)$:
$ |U_{i+1}| <= (1 - 1/"OPT") |U_i| $

By induction: $forall k >= 0$:
$ |U_k| <= (1 - 1/"OPT")^k dot n <= exp(-k / "OPT") dot n $

#pause

The sequence $U_0, U_1, dots$ reaches zero when $exp(-i/"OPT") dot n < 1$, i.e.\ $i > "OPT" dot ln n$.

*After $"OPT" dot ln n$ iterations, all of $V(H)$ is covered.*

#pause

Recalling that size of greedy sol $=$ \# iterations:

#theorem[
  $"size of greedy sol" <= (ln n) dot "OPT"$ #h(0.5em) — an $O(ln n)$-approximation.
]

== Tightening to $O(ln m)$

*Subtlety:* The theorem asserts $O(ln m)$ but we got $O(ln n)$. Since $n$ and $m$ can differ greatly, we refine.

#pause

Choose $i^*$ as the last iteration where $"OPT" <= |U_{i^*}|$.
- After $i^*$ iters: $|U_{i^*+1}| < "OPT"$ — at most $"OPT" - 1$ more iterations needed
- So: $"size of greedy sol" <= (i^* + 1) + ("OPT" - 1) = i^* + "OPT"$

#pause

*Estimating $i^*$:* Since $"OPT" <= |U_{i^*}| <= exp(-i^*\/"OPT") dot n$:
$ exp(i^* \/ "OPT") <= n/"OPT" quad ==> quad i^* <= "OPT" dot ln(n/"OPT") $

$==>$ $"size of greedy sol" <= "OPT" dot ln(n/"OPT") + "OPT" = (1 + ln(n/"OPT")) dot "OPT"$

#pause

#observation[
  $m = max{|e| : e in cal(E)} >= n/"OPT"$ since every optimal solution must contain a hyperedge of size $>= n\/"OPT"$.
]

$ therefore quad "size of greedy sol" <= (1 + ln m) dot "OPT" = O(ln m) dot "OPT". quad square $

= Minimum Cost Set-Cover

== The Weighted Problem

#problem[
  *Minimum Cost Set-Cover*

  *Instance:* A hypergraph $H$; a cost function $c: cal(E)(H) -> RR_(>=0)$.

  *Goal:* An edge-cover $C subset.eq cal(E)(H)$ of $H$ minimising $display(sum_(e in C) c(e))$.
]

#pause

The cardinality greedy *fails* for the cost/weight version. Can we still learn from it?

== Reformulating the Greedy Choice

Consider the $i$-th iteration (with $V(H) without union.big A_i != emptyset$).

The cardinality greedy picks $e in cal(E)(H) without A_i$ maximising:
$ (|e without union.big A_i|) / (|V(H) without union.big A_i|) = ("# new vxs covered by" e) / ("# left-over vxs") $

#pause

*For weighted:* minimise avg cost per uncovered vx — *not well-defined* since $e without union.big A_i$ need not be a hyperedge and $c(e without union.big A_i)$ may not be defined.

#pause

*Back to cardinality:* For $e in cal(E)(H) without A_i$, consider $1 \/ |e without union.big A_i|$.
- The *smaller* this ratio, the *more* new elements $e$ covers.

*For weighted:* $c(e) \/ |e without union.big A_i|$ — distribute cost $c(e)$ among newly covered vxs. This is *amortisation!*

== Effectiveness

#definition[
  *Effectiveness*

  Let $U subset.eq V(H)$ and $e in cal(E)(H)$. Define:
  $ "eff"_U (e) := cases(
    infinity & "if" e subset.eq U,
    display(c(e) / |e without U|) quad & "otherwise"
  ) $
  to be the *effectiveness* of $e$ with respect to $U$.
]

== Weighted Greedy Algorithm

#algorithm-figure(
  [Greedy-Cost-SC],
  vstroke: .5pt + luma(200),
  {
    import algorithmic: *
    Assign([$A$], [$emptyset$])
    While([$union.big A != V$], {
      Assign([$e$], [$arg min{"eff"_(union.big A)(e) : e in cal(E)(H)}$])
      Assign([$A$], [$A union {e}$])
    })
    Return([$A$])
  }
)

#pause

#theorem[
  The greedy algorithm above forms an $O(ln n)$-approximation for minimum cost set-cover.
]

== Example: Greedy vs Optimal

$H$: hyperedges $e_1, dots, e_n$ (each covering one distinct element) and $e_{n+1}$ (covering all), with:
$ c(e_i) = 1/(n+1-i) quad (i=1,dots,n), quad c(e_{n+1}) = 1 + epsilon, quad epsilon > 0 $

*Optimal:* take $e_{n+1}$ only, cost $= 1 + epsilon$.

#pause

*Greedy (step 1, $A = emptyset$):*
$"eff"_emptyset(e_i) = c(e_i)\/1, quad "eff"_emptyset(e_{n+1}) = (1+epsilon)\/n$ $arrow.r e_1$ chosen (eff $= 1\/n$, the smallest).

*Greedy (step 2, $A = {e_1}$):*
$"eff"_({e_1})(e_2) = 1\/(n-1), quad "eff"_({e_1})(e_{n+1}) = (1+epsilon)\/(n-1)$ $arrow.r e_2$ chosen. $dots$

*Greedy selects $e_1, e_2, dots, e_n$* with total cost:
$ sum_(i=1)^n c(e_i) = sum_(i=1)^n 1/(n+1-i) = H_n approx ln n quad ("OPT" = 1 + epsilon) $

= Analysis of Weighted Greedy

== Basic Intuition

#theorem[*Lemma*
  Let $P$ be an optimal cover with cost $"OPT"$. Then $exists e in P$ such that $c(e)\/|e| <= "OPT"\/n$.
]

#proof[
  Suppose $c(e)\/|e| > "OPT"\/n$ for all $e in P$. Then:
  $ "OPT" = sum_(e in P) c(e) > sum_(e in P) |e| dot "OPT"/n = "OPT"/n dot sum_(e in P) |e| >= "OPT"/n dot n = "OPT". quad. $
  The last step uses $sum_(e in P) |e| >= |union.big_(e in P) e| = n$ since $P$ covers all $n$ vxs. $square$
]

#pause

*Amortised perspective:*

#observation[
  $exists e in P$ covering covering its vxs at amortised cost $<= "OPT"\/n$ *per vertex*.
]

== Amortised Perspective on the Greedy

This argument persists at *later stages*. Let $P$ = optimal cover, $A_i$ = current greedy cover. Define:
$ T := {e in P : e without union.big A_i != emptyset} $

All hyperedges in $P$ that would cover *new* vxs if added.

- Only members of $T$ are relevant to the greedy: $"eff"_(union.big A_i)(e) < infinity$ iff $e in T$
- $V(H) without union.big A_i subset.eq union.big T$ #h(1em) #tr[(exercise: proof by contradiction)]

#pause

#theorem[*Key Lemma*
  $exists e in T$ s.t. $"eff"_(union.big A_i)(e) = c(e) \/ |e without union.big A_i| <= "OPT" \/ |V(H) without union.big A_i|$.
]

*Proof.* Suppose not. Then:
$
"OPT" >= sum_(e in T) c(e) &> "OPT"/|V(H) without union.big A_i| dot sum_(e in T) |e without union.big A_i| \
&>= "OPT"/|V(H) without union.big A_i| dot |V(H) without union.big A_i| = "OPT". quad square
$

The last inequality: $sum_(e in T) |e without union.big A_i| >= |union.big T without union.big A_i| = |V(H) without union.big A_i|$.

== Amortised Cost Tracking

Augment the greedy to assign a *price* to each vertex when first covered:

#algorithm-figure(
  [Greedy-Cost-SC (augmented)],
  vstroke: .5pt + luma(200),
  {
    import algorithmic: *
    Assign([$A$], [$emptyset$])
    While([$union.big A != V$], {
      Assign([$e$], [$arg min{"eff"_(union.big A)(e) : e in cal(E)(H)}$])
      For([each $v in e without union.big A$], {
        Line([Set $alpha(v) := "eff"_(union.big A)(e)$])
      })
      Assign([$A$], [$A union {e}$])
    })
    Return([$A$])
  }
)

*Reformulation:* Choose $e in cal(E)(H)$ whose avg cost per *newly covered* element is least.

== Cost $=$ Sum of $alpha$-values

#theorem[*Lemma*
  $"cost of greedy sol" = sum_(v in V) alpha(v)$.
]

*Proof.* Let $A = {e_1, dots, e_k}$ be the greedy sol; $A_j = {e_1, dots, e_{j-1}}$ the partial sol at step $j$.

$
sum_(e in A) c(e) = sum_(j=1)^k c(e_j) = sum_(j=1)^k sum_(v in e_j without union.big A_j) underbrace(c(e_j) / |e_j without union.big A_j|, = alpha(v)) = sum_(v in V) alpha(v). quad square
$

== Approximation Ratio

#theorem[
  The weighted greedy algorithm is an $O(ln n)$-approximation.
]

*Proof.* Order $V = {v_1, v_2, dots, v_n}$ by the order greedy covers them.

When $v_i$ is covered at iteration $j$, there are $>= n - i + 1$ uncovered vxs. By the *Key Lemma*:
$ alpha(v_i) = "eff"_(union.big A_j)(e_j) <= "OPT" / |V(H) without union.big A_j| <= "OPT" / (n - i + 1) $

#pause

Therefore, using the *Cost Lemma*:
$
"cost of greedy sol" = sum_(v in V) alpha(v) = sum_(i=1)^n alpha(v_i) <= "OPT" sum_(i=1)^n 1/(n-i+1) = "OPT" dot H_n
$

where $H_n = sum_(i=1)^n 1\/i approx ln n$ is the $n$-th *Harmonic number*. $quad square$
