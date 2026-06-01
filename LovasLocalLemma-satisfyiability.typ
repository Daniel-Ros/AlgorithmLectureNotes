#import "settings/mstyle.typ": *
#import algorithmic: algorithm-figure, style-algorithm
#show: style-algorithm

#show: conf.with(
  handout: false,
  subtitle: [Satisfiability via the Lovász Local Lemma],
)

#title-slide()

= CNF Formulae with Few Repeating Variables

== Setup

By a *$k$-CNF formula* we mean:
$ underbrace((x_1 or x_2 or x_3 dots), = k) and underbrace((overline(x)_6 or x_2 or overline(x)_15 dots), = k) and dots $

Each clause has exactly $k$ literals.

#pause

#theorem[*Lemma*
  Let $phi$ be a $k$-CNF formula. If no variable of $phi$ appears in more than $2^k \/ 4k$ clauses, then $phi$ is satisfiable.
]

== Proof: Setup

Let $m$ = \# clauses of $phi$.

- Assign each variable of $phi$ a value from ${0,1}$ *u.a.r.* and independently.
- For $i in [m]$, define:
$ cal(E)_i := "the event that clause" i "is unsatisfied" $

We seek to prove $PP[inter.big_(i in [m]) overline(cal(E)_i)] > 0$ by appealing to the *Lovász local lemma*.

#pause

#let LLL = theorem[*(Symmetric Local Lemma)*
  Let $cal(E)_1, ..., cal(E)_n$ be events s.t.:
  1. *(Symmetry)* $PP[cal(E)_i] <= p$ for all $i in [n]$
  2. *(Limited dependency)* $Delta(D(cal(E)_1,...,cal(E)_n)) <= d$
  3. *(Bound)* $e dot p dot (d+1) <= 1$ #h(1fr) #tr[(Or $4 dot p dot d <= 1$)]

  Then $PP[inter.big_(i=1)^n overline(cal(E)_i)] > 0$.
]

#LLL

== Proof: Dependency Graph
#[
#set text(0.78em)
*Define* a graph $D$ s.t.:
- $V(D) := {cal(E)_i : i in [m]}$
- $E(D) :=$ place edge $(cal(E)_i, cal(E)_j)$ if clauses $i$ and $j$ *share common variables*

#pause

Event $cal(E)_i$ is mutually independent of all $cal(E)_j$ where clauses $i$ and $j$ have *no common variables* $=>$ $D$ is a dependency graph.

#pause

*Bounding $Delta(D)$:*
- Each variable appears in at most $2^(k)\/(4k)$ clauses; a clause has $<= k$ distinct variables. 
$ Delta(D) = arg max_(C) sum_(x in C) [\# "number of clauses that" x "lies in"] <= k dot 2^(k) / (4k) = 2^(k - 2) $

*Bounding $p$:*
$ PP[cal(E)_i] <= 1 / 2^k quad forall i in [m] $
since each clause has $k$ literals.

*Checking the LLL condition:*
$ 4 dot p dot d <= 4 dot 1/2^k dot 2^(k-2) = 4/4 <= 1 $

By the Lovász local lemma: $PP[inter.big_(i=1)^m overline(cal(E)_i)] > 0$. $square$
]
= A Randomised Algorithm

== Drawback & Goal

#observation[
  The Lovász local lemma offers *existential* results only.
]

#pause

We are interested in *manipulating* the local lemma to obtain *constructive* results.

#pause

*Previous result:* If every variable appears in $underbrace(<= 2^(alpha k), #[say $alpha <= 1$])$ clauses, then $phi$ is satisfiable.

*Question:* For such a $phi$, can we *find* a satisfying assignment?

== Main Theorem

A *two-phase approach* is proposed:

#definition[
  *Phase I:* A partial random assignment is sampled.

  *Prove:* With positive prob, the partial assignment extends into a satisfying assignment.
]

#definition[
  *Phase II:* a.a.s. a certain dependency graph on events related to *deferred* variables has only *small* connected components.

  Used to find a satisfying assignment via *brute-force*.
]

#pause
#v(-10pt)
#theorem[
  For all sufficiently large even $k in NN$ fixed, $exists alpha := alpha(k)$ s.t.:

  $phi$ := $k$-CNF formula with $m$ clauses, every variable appearing in $<= 2^(alpha k)$ clauses.

  Then a satisfying assignment for $phi$ can be found in *expected poly time* in $m$.
]

== Setup & Assumptions

*Throughout:*
- $phi$ is $k$-CNF, $k >= 20$ fixed.
- Variables $x_1, ..., x_lambda$; Clauses $C_1, ..., C_m$.
- Each variable appears in $<= 2^(alpha k)$ clauses.
- $alpha > 0$ to be determined later.

#pause

*Assumptions*:
- No clause contains a *complementary pair* of literals
- No clause contains *repeating* literals

// #tr[We can pad clauses with duplicates by swapping $(x_1 or x_1 or ...)$ by $(x_1 or y_1 or...) and(x_1 or overline(y_1) or...)$]

#observation[
  $forall$ clause: $\#$ literals $=$ $\#$ variables.
]

= Phase I: Partial Random Assignment

== The Algorithm

Assign values to *some* of $x_1, ..., x_lambda$:

#algorithm-figure(
  [Phase-I],
  vstroke: .5pt + luma(200),
  {
    import algorithmic: *
    For([each $x_i$ in $x_1, ..., x_lambda$ sequentially], {
      Line([*if* $x_i$ lies in no unsatisfied clause with precisely $k\/2$ assigned variables *then*])
      Line([#h(2em) Assign $x_i$ a value from ${0,1}$ u.a.r., independently])
      Line([*else* do not assign $x_i$ any value; proceed to next variable])
    })
  }
)

#pause

#definition[
  *Dangerous clause:* A clause $C$ is *dangerous* if precisely $k\/2$ of its literals have been assigned a value, yet $C$ remains unsatisfied.

  *Deferred variable:* A variable not assigned a value by Phase I.

  *Surviving clause:* A clause that is unsatisfied by the partial Phase I assignment.
]

== Surviving Clauses

#[
  #set text(size: 0.863em)
*Key structural facts:*

#v(-10pt)
- A surviving clause *always* has $<= k\/2$ fixed variables.

#v(-8pt)
  *Proof:* Suppose $C$ has $> k\/2$ fixed vars. Then at some earlier point $C$ had *exactly* $k\/2$ fixed vars while still unsatisfied — so $C$ was *dangerous* at that moment. But once dangerous, no further variables of $C$ are ever assigned. Contradiction. $square$

#pause

#v(-5pt)
#observation[
  If $C$ is a surviving clause then it has at least $k\/2$ *deferred* variables.
]

*Proof:* By definition every unassigned variable is deferred. Since $f <= k\/2$ (proved above), $C$ has $k - f >= k\/2$ deferred variables. $square$
]
= Extendability into a Satisfying Assignment

== The Lemma

#lemma[
  For all even sufficiently large fixed $k in NN$, $exists alpha > 0$ s.t. there is an assignment to the deferred variables satisfying *all* surviving clauses.
]

*Proof.* We apply the local lemma.

*Source of randomness* (not the Phase I assignment!): Assign each *deferred* variable a value u.a.r. from ${0,1}$ independently.

For a surviving clause $C$, define:
$ cal(E)_C := C "not satisfied by the random assignment" $

== Dependency Graph for Deferred Variables

#[
  #set text(size: 0.865em)
*Define* graph $D$:
- $V(D) = {cal(E)_C : C "a surviving clause"}$
- $cal(E)_C$ and $cal(E)_(C')$ adjacent if $C$ and $C'$ share a common *deferred* variable
- $D$ is a dependency graph (same argument as before)

#place(
  dx: 63%,
  dy: -20%,
  block(width: 42%)[
    #set text(size: 0.64em)
    #LLL
  ]
)

#pause


*Bounding $PP[cal(E)_C]$:* Since $C$ has $>= k\/2$ deferred vars:
$ PP[cal(E)_C] <= 2^(-k\/2) $

*Bounding $Delta(D)$:*
- Each deferred var in $C$ lies in $<= 2^(alpha k)$ other surviving clauses
- $C$ has $<= k$ deferred variables
$ Delta(D) <= k dot 2^(alpha k) $

#pause

*LLL condition:*
$ 4 dot Delta(D) dot p <= e dot k dot 2^(alpha k) dot 2^(-k\/2) = k dot 2^(alpha k + 2 - k\/2) <= 1 $
for $k$ sufficiently large and $alpha$ sufficiently small.

Local lemma asserts: $PP[inter.big_(C "surv.") overline(cal(E)_C)] > 0$. $square$



]
= Component Sizes

== The Plan

Let $D$ be the dependency graph from the last proof.

#v(-10pt)
- A connected component of $D$ defines a *sub-formula* of $phi$
- $phi$ has $m$ clauses $=>$ at most $m$ components/sub-formulae

#pause
#v(-10pt)
#observation[
  If all components have size $O(log m)$, then at most $O(k log m)$ variables are involved.

  If $phi$ is satisfiable, a brute-force search over all $2^(O(k log m)) = m^(O(k))$ options finds a satisfying assignment.
]

*Current goal:* Use Phase I to prove that a.a.s.\ all components of $D$ are "small".

#lemma[*(Component Size):*
  $forall k$ as before $exists alpha = alpha(k) > 0$ and $C := C(k,alpha) > 0$ s.t. a.a.s. all components of $D$ have size $<= C ln m$.
]

== A Second Graph $D'$

Introduce a *deterministic* auxiliary graph $D'$:
- $V(D') :=$ *all* clauses of $phi$ (not just surviving ones)
- $C$ and $C'$ adjacent if they share common variables
- A vertex $C$ of $D'$ is a vertex of $D$ iff $C$ survived Phase I

#pause

Since $D subset.eq D'$:
$ Delta(D) <= Delta(D') <= k dot 2^(alpha k) =: Delta $

*Why $D'$?* To analyse components of $D$, it suffices to analyse which subgraphs of $D'$ survive Phase I.

== 4-Trees
#[
  #set text(size: 0.93em)
#definition[
  *$4$-tree of $R$:* Let $R$ be a connected subgraph of $D'$. A *$4$-tree* of $R$ is a rooted tree $S$ (need not be a subgraph of $R$) satisfying:
  1. $V(S) subset.eq V(R)$
  2. Any two nodes of $S$ are at distance $>= 4$ in $D'$
  3. Two nodes are adjacent in $S$ if their $D'$-distance is *precisely* $4$
  4. Every vertex of $R$ is either in $S$ or at distance $<= 3$ from $S$ in $R$
]

#pause

#claim[*Claim A*
  Let $S$ be a $4$-tree of some connected subgraph $R$ of $D'$. Then:
  $ PP[V(S) subset.eq V(D)] <= ((Delta+1) dot 2^(-k\/2))^(v(S)) $
]

#claim[*Claim B*
  Let $R$ be a connected subgraph of $D'$, $S$ a $u$-tree of $R$ of *maximum size*. Then:
  $ v(S) >= v(R) \/ Delta^3 $
]
]
== Using Claims A and B

*Strategy:*

#observation[
  By Claim B: if any connected subgraph $R$ of $D'$ of size $>= C ln m$ survives in $D$, then it has a $u$-tree of size $>= C ln m \/ Delta^3$ that also survived.
]

#pause

By Claim A: prove that a.a.s.\ $D'$ has *no* $u$-tree of size $>= C ln m \/ Delta^3$ that survived in $D$.

$=>$ No connected subgraph of $D'$ of size $>= C ln m$ survives in $D$ (a.a.s.) $=>$ all components of $D$ have size $<= C ln m$ (a.a.s.).

== Proof of Claim A

*Proof.* For any clause $C$:
$ PP[C "survives"] &<= PP[C "is dangerous"] + PP[>= 1 "neighbour in" D' "is dangerous"] \
&<= 2^(-k\/2) + Delta dot 2^(-k\/2) = (Delta+1) dot 2^(-k\/2) $

#pause

*Key observation:* Clauses at distance $2$ in $D'$ share *no* common variables $=>$ the events that such clauses are dangerous are *mutually independent*.

Fix $u in V(S)$. Any vertex of $R$ that can cause $u$ to be dangerous is at distance 1 from $u$, hence at distance $>= 2$ from all other members of $V(S)$.

$=>$ The survival events of $V(S)$ are *mutually independent*.

$=>$
$ PP[V(S) subset.eq V(D)] <= ((Delta+1) dot 2^(-k\/2))^(v(S)). quad square $

== Proof of Claim B

*Proof.* Suppose for contradiction that $v(S) < v(R)\/Delta^3$.

By definition, every member of $V(R)$ is at distance $<= 3$ from $V(S)$ in $R$. Fix $v in V(D')$:
$ \# "vxs in" D' "at dist." <= 3 "from" v &<= Delta + Delta(Delta-1) + Delta(Delta-1)(Delta-2) \
&= Delta + Delta^2-Delta + Delta^3 - 3Delta^2 + 2Delta \
&<= Delta^3 - 1 $

Therefore:
$ v(R) <= |V(S)| dot (Delta^3 - 1) < v(R)/Delta^3 dot (Delta^3 - 1) < v(R). quad "contradiction". quad square $

== Component Size: Proof
#[
  #set text(size: 0.9em)
Set $r := C ln m$ for comfort. We need to bound $PP[cal(E)]$ where $cal(E) :=$ "a $u$-tree of size $>= r\/Delta^3$ survived in $D$".

*\# of $u$-trees in $D'$ of size $r\/Delta^3$:*
$ <= m dot Delta^(4r\/Delta^2) $
- $<= m$ ways to choose the root
- \# ways to build a $u$-tree $<=$ \# Euler tours on $r\/Delta^3$ nodes starting/ending at root
- Each edge of the $u$-tree represents a path of length $u$; at each node-visit, $<= Delta^u$ continuation options

#pause

By Claim A and the union bound:
$
PP[cal(E)] &<= m dot Delta^(4r\/Delta^2) dot ((Delta+1) dot 2^(-k\/2))^(r\/Delta^3) \
&= exp(ln m + 4r/Delta^2 ln Delta + r/Delta^3 ln(Delta+1) - k r\/(2Delta^3)) \
&<= exp(ln m + (4r ln(2k))\/Delta^2 + (r ln(4k))\/Delta^3 - k r\/(2Delta^3)) \
&= o(1)
$
by choosing $alpha$ small enough and $C$ large enough. $square$
]
= Grand Finale

== Main Theorem

#theorem[
  For all suff.\ large even $k in NN$ fixed, $exists alpha := alpha(k)$ s.t.:

  $phi$ := $k$-CNF with $m$ clauses, every variable in $<= 2^(alpha k)$ clauses.

  Then a satisfying assignment for $phi$ can be found in *expected poly.\ time* in $m$.
]

*Proof:*

- *Phase I* a.a.s.\ decomposes $phi$ into components of size $<= C ln m$ (Component Size Lemma)
- *Geometric experiment:* We expect $O(1)$ applications of Phase I to yield a valid decomposition
- *Extendability Lemma:* whatever decomposition we obtain is extendable into a satisfying assignment
- *Brute force on each component:* within expected time $m^(O(k))$ we trace a satisfying assignment $square$
