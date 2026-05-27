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

#place(
    dx: 5%,
    dy: 7%,
    figure(image("figures/ASC2.png", width: 40%),)
  )


== The Problem

#problem[
  *Minimum Set-Cover (SC)*

  *Instance:* A hypergraph $H := (V, cal(E))$.

  *Goal:* A subset $C subset.eq cal(E)$ such that $union.big_(e in C) e = V$, minimising $|C|$.

  *Put another way:* We seek a minimum *hyper-edge-cover* of $H$.
]

#pause

- Recall: for graphs, the minimum *edge-cover* problem is in $P$. #h(1fr) #tr[#set text(size: 0.9em) 
(Find maximum matching and extend greedily)]
- The minimum SC problem is *NP-complete* #h(1fr) (we return to this below)

== Some Examples

#place(
    dx: 25%,
    dy: 0%,
    figure(image("figures/ASC3.png", width: 50%),)
  )

== Min SC is NPC

$underbrace("VC" := {(G, k) : tau(G) <= k}, "min vertex cover problem")$ #h(2em) $"SC" := {(H, k) : H "has a hyper-edge cover of size" <= k}$

*Claim:* $"VC" reduction "SC"$.

#pause

For each $u in V(G)$, define: $S_u := {e in E(G) : u in e}$.

Given $(G, n)$, define a hypergraph $H$ by:
$ V(H) := E(G), quad cal(E)(H) := {S_u : u in V(G)} $


#place(
    dx: 25%,
    dy: 15%,
    figure(image("figures/ASC4.png", width: 55%),)
  )

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
      Assign([$e$], [$arg max{|e without union.big A| : e in cal(E)}$ #h(1fr) #tr[(hyper-edge covering the most new vxs)]])
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

Set $m := max{|e| : e in cal(E)}$ — the size of the *largest* hyperedge. #h(1fr) #tr[Trivially $m <= |V(H)| = n$.]

#pause

#theorem[
  The greedy algorithm is an $O(ln m)$-approximation for minimum set-cover.
]

#pause

#observation[
  Size of the cover output $=$ \# iterations greedy performs.
]

*Define:* $A_i$ = greedy solution at the *beginning* of the $i$-th iteration.
- Greedy transitions $A_i -> A_(i+1)$ during iteration $i$.
- \# new vxs covered $= |union.big A_(i+1)| - |union.big A_i|$. #h(1fr) #tr[(all from $V(H) without union.big A_i$)]

== Key Observation

#v(10pt)
Let $"OPT"$ = size of an optimal cover. 

#claim[
  An optimal solution $P := {e_1, dots, e_"OPT"}$ contains $e_j$ s.t.:
  $ |e_j inter (V(H) without union.big A_i)| >= (|V(H) without union.big A_i|) / "OPT" $
]
*Proof (By contradiction):*
- Assume no such $e_j$ exists
#v(-10pt) 
$ ==> forall e in cal(E): |e_j inter (V(H) without union.big A_i)| < (|V(H) without union.big A_i|) / "OPT" $
#v(-20pt)
Then,
$
  underbrace( #[$|V(H)| = |cup.big P|$], P "cover all of H") < "OPT" dot (|V(H) without union.big A_i|) / "OPT" = 
  underbrace(|V(H) without union.big A_i| <= |V(H)|, (V(H) without union.big A_i) subset.eq V(H)).
$

== Key Observation

Since $A_i$ is constructed *greedily*:

#observation[
  $forall i in NN: quad |union.big A_(i+1)| - |union.big A_i| >= (|V(H) without union.big A_i|) / "OPT"$
]

#pause

*Q:* Once $A_(i+1)$ is defined, how many vxs are left to cover?

$
|V(H) without union.big A_(i+1)| &= |V(H)| - |union.big A_(i+1)| \
&<= |V(H)| - |union.big A_i| - (|V(H) without union.big A_i|) / "OPT" \
&= (1 - 1/"OPT") |V(H) without union.big A_i|
$

#pause

#observation[
  $|V(H) without union.big A_(i+1)| <= (1 - 1/"OPT") |V(H) without union.big A_i|$

  After each iteration, the \# of left-over vxs reduces by a factor of $(1 - 1\/"OPT")$.
]

== Recursive Pattern

- Set $U_i := V(H) without union.big A_i$ #h(1fr) #tr[(left-over vxs at iter $i$)] 
- Intially $U_0 = V(H)$:
#v(-10pt)
$ |U_(i+1)| <= (1 - 1/"OPT") |U_i| $
#v(-10pt)
By induction: $forall k >= 0$:
#v(-10pt)
$ |U_k| <= (1 - 1/"OPT")^k dot |U_0| <= exp(-k / "OPT") dot n $

#pause

The sequence $U_0, U_1, dots$ reaches zero when $exp(-i/"OPT") dot n < 1$. \

i.e. #h(1fr) $i > "OPT" dot ln n$. #h(1fr) 
#v(-5pt)
*After $"OPT" dot ln n$ iterations, all of $V(H)$ is covered.*
#v(-5pt)

#place(
    dx: 77%,
    dy: -48%,
    figure(image("figures/ASC5.png", width: 25%),)
  )
#pause

Recalling that size of greedy sol $=$ \# iterations:
#v(-5pt)
#theorem[
  $"size of greedy sol" <= (ln n) dot "OPT"$ #h(0.5em) — an $O(ln n)$-approximation.
]

== Tightening to $O(ln m)$

*Subtlety:* The theorem asserts $O(ln m)$ but we got $O(ln n)$. Since $n$ and $m$ can differ greatly, we refine.

#pause
#v(-10pt)
Choose $i^*$ as the last iteration where $"OPT" <= |U_(i^*)|$.
- After $i^*$ iters: $|U_(i^*+1)| < "OPT"$.  #h(1fr) #tr[(Cover the rest using at most $"OPT" - 1$ hyper-edges)]
- So: $"size of greedy sol" <= (i^* + 1) + ("OPT" - 1) = i^* + "OPT".$

#pause

#v(-8pt)
*Estimating $i^*$:*
#v(-15pt)
  $ #tr[OPT $<=$] |U_(i^*)| <= (1-1/"OPT")^(i^*) dot |U_(0)|#tr[$<= exp(-i^*\/"OPT") dot n$]. $

#v(-10pt)
$ exp(i^* \/ "OPT") <= n/"OPT" quad ==> quad i^* <= "OPT" dot ln(n/"OPT"). $

$==>$ $"size of greedy sol" <= "OPT" dot ln(n/"OPT") + "OPT" = (1 + ln(n/"OPT")) dot "OPT"$.


#place(
    dx: 80%,
    dy: -48%,
    figure(image("figures/ASC6.png", width: 25%),)
  )
#pause

#[
  #set text(size: 0.7952em)
#observation[
  $m = max{|e| : e in cal(E)} >= n/"OPT"$ since every optimal solution must contain a hyperedge of size $>= n\/"OPT"$.
]
]

$ quad "size of greedy sol" <= (1 + ln m) dot "OPT" = O(ln m) dot "OPT". quad square $

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
#v(-10pt)
$ (|e without union.big A_i|) / (|V(H) without union.big A_i|) = ("# new vxs covered by" e) / ("# left-over vxs") $

#pause

*For weighted:* we would want an edge $e in cal(E)(H) without A_i$ maximising:
#v(-10pt)
$ ("\"cost\" of new vxs covered by" e) / ("\"cost\" of vxs left-over") $ 
#v(-55pt) #h(1fr) #tr[(not well-defined)]
#v(20pt)


#pause

*Back to cardinality:* For $e in cal(E)(H) without A_i$, consider $1 \/ |e without union.big A_i|$.
- The *smaller* this ratio, the *more* new elements $e$ covers.

*For weighted:* $c(e) \/ |e without union.big A_i|$ — distribute cost $c(e)$ among newly covered vxs. #h(1fr) #tr[(This is amortisation!)]
Pick $e in cal(E)(H) without A_i$ minimising
$ (c(e)) / (|e without union.big A_i|) = ("cost of" e) / ("# vxs covered by" e) $

== Weighted Greedy Algorithm

#set text(size: 1em)

#definition[
  *Effectiveness*
  #v(-10pt)
  Let $U subset.eq V(H)$ and $e in cal(E)(H)$. Define:
    #v(-50pt)
  #h(2fr) $"eff"_U (e) := cases(
    infinity & "if" e subset.eq U,
    display((c(e)) / (|e without U|)) quad & "otherwise"
  ) $ #h(1fr)
    #v(-20pt)
  to be the *effectiveness* of $e$ with respect to $U$.
]
  #v(-10pt)
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

#place(
    dx: -5%,
    dy: 0%,
    figure(image("figures/ASC7.png", width: 60%),)
  )



#pause

#place(
  dx: 57%,
  dy: 0%,
  [
    #block(width: 45%)[
      #set text(size: 0.8em)
      *Greedy (step 1, $A = emptyset$):*
      - $"eff"_emptyset(e_i) = c(e_i)\/1$. 
      - $"eff"_emptyset(e_(n+1)) = (1+epsilon)\/n$. \
        $==> e_1$ chosen. #h(1fr)  #tr[(eff $= 1\/n$, the smallest)]

      *Greedy (step 2, $A = {e_1}$):*
      - $"eff"_({e_1})(e_i) = c(e_i)\/1$ 
      - $ "eff"_({e_1})(e_(n+1)) = (1+epsilon)\/(n-1)$\
       $==> e_2$ chosen. #h(1fr)  #tr[(eff $= 1/(n-1)$, the smallest)]
       
       $dots$

      *Greedy selects $e_1, e_2, dots, e_n$* with total cost:
      $ sum_(i=1)^n c(e_i) = sum_(i=1)^n 1/(n+1-i) = sum_(j=1)^n 1/j approx ln n quad ("OPT" = 1 + epsilon) $
    ]
  ]
)

= Analysis of Weighted Greedy

== Basic Intuition

#claim[
  Let $P$ be an optimal cover with cost $"OPT"$. Then $exists e in P$ such that $c(e)\/|e| <= "OPT"\/n$.
]

#proof[
  Suppose $c(e)\/|e| > "OPT"\/n$ for all $e in P$. Then:
  $ "OPT" = sum_(e in P) c(e) > sum_(e in P) |e| dot "OPT"/n = underbrace("OPT"/n dot sum_(e in P) |e| >= "OPT"/n dot n, #[
    $ sum_(e in P) |e| >= |union.big_(e in P) e| = n$ \  $P$ covers all $n$ vxs.
  ]) = "OPT". quad. $
]

#pause

*Amortised perspective:*

#observation[
  $exists e in P$ covering its vxs at amortised cost $<= "OPT"\/n$ *per vertex*.
]

== Amortised Perspective on the Greedy
#set text(size: 0.95em)
#observation[
  $exists e in P$ covering its vxs at amortised cost $<= "OPT"\/n$ *per vertex*.
]

This argument persists at *later stages*. Let $P$ = optimal cover, $A_i$ = current greedy cover. Define:

#h(6fr) $T := {e in P : e without union.big A_i != emptyset} $ #h(1fr) #tr(s: 0.8)[(All hyper-edges in $P$ that cover "new" vertices)]


#v(-4pt)
- Only members of $T$ are relevant to the greedy: $"eff"_(union.big A_i)(e) < infinity$ iff $e in T$
- $(V(H) without union.big A_i) subset.eq union.big T$ #h(1fr) #tr(s: 0.8)[(exercise: proof by contradiction, i.e. remaining vertices are covered by $T$.)]
#lemma(title: "Key Claim")[
  #set text(size: 0.9em)
  $exists e in T$ s.t. 
  #v(-15pt)
  $ "eff"_(union.big A_i)(e) = c(e) / (|e without union.big A_i|) <= "OPT" / (|V(H) without union.big A_i|). $
  #v(-5pt)
]
#pagebreak()
#lemma(title: "Key Claim")[
  #set text(size: 0.9em)
  $exists e in T$ s.t. 
  #v(-15pt)
  $ "eff"_(union.big A_i)(e) = c(e) / (|e without union.big A_i|) <= "OPT" / (|V(H) without union.big A_i|). $
  #v(-5pt)
]<lemma:key>
#v(-10pt)
*Proof.* Suppose not. Then:
#v(-10pt)
$
"OPT" >= sum_(e in T) c(e) &> "OPT"/ (|V(H) without union.big A_i|) dot sum_(e in T) |e without union.big A_i| \
&underbrace(>= "OPT"/(|V(H) without union.big A_i|) dot |V(H) without union.big A_i|, #[
  $sum_(e in T) |e without union.big A_i| >= |union.big (T without union.big A_i)| = |V(H) without union.big A_i|$
]) = "OPT". quad square
$

// The last inequality: $sum_(e in T) |e without union.big A_i| >= |union.big T without union.big A_i| = |V(H) without union.big A_i|$.

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

#lemma(title: "Cost")[
  $"cost of greedy sol" = sum_(v in V) alpha(v)$.
]<lemma:cost>

*Proof.* Let $A = {e_1, dots, e_k}$ be the greedy sol; $A_j = {e_1, dots, e_(j)}$ the partial sol at step $j$.

$
sum_(e in A) c(e) = sum_(j=1)^k c(e_j) = sum_(j=1)^k sum_(v in e_j without union.big A_j) underbrace(c(e_j) / (|e_j without union.big A_j|), = alpha(v)) = sum_(v in V) alpha(v). quad square
$

== Approximation Ratio

#theorem[
  The weighted greedy algorithm is an $O(ln n)$-approximation.
]

*Proof.* Order $V = {v_1, v_2, dots, v_n}$ by the order the greedy covers them.

When $v_i$ is covered at iteration $j$, there are $>= n - i + 1$ uncovered vxs. By *@lemma:key*:
$ alpha(v_i) = "eff"_(union.big A_j)(e_j) <= "OPT" / (|V(H) without union.big A_j|) <= "OPT" / (n - i + 1). $

#pause

Therefore, using *@lemma:cost*
$
"cost of greedy sol" = sum_(v in V) alpha(v) = sum_(i=1)^n alpha(v_i) <= "OPT" dot sum_(i=1)^n 1/(n-i+1) = "OPT" dot H_n.
$

where $H_n = sum_(i=1)^n 1\/i approx ln n$ is the $n$-th *Harmonic number*. $quad square$
