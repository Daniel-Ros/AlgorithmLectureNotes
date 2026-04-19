#import "settings/dstyle.typ": *

#show: conf.with(
  handout: true,
  subtitle: [Graph Colouring],
)

#title-slide()

= A Greedy Colouring Algorithm
== Setup
  - Input:
    - A graph $G$
    - An ordering $v_1, v_2, dots, v_n$ of $V(G)$\
    
  - Output:
    - A legal vertex-colouring of $G$

+ Scan the vertices according to the ordering.
+ When considering $v_i$, assign it the least available colour.
+ This always produces a legal colouring.

#question[
  How useful is this algorithm for bounding $chi(G)$?
]

== First Consequence
- For every graph $G$, define
$
  Delta(G) := max { deg_G(v) : v in V(G) }
$

- The greedy algorithm implies $chi(G) <= Delta(G) + 1$
- When the bound is tight?
  - There are graphs with
$
  chi(G) = Delta(G) + 1
$
  - Examples:
    - Odd cycles: $Delta = 2$ and $chi = 3$
    - Complete graphs: $Delta(K_r) = r - 1$ and $chi(K_r) = r$

= Brooks' Theorem
== Statement
#theorem(title: [Brooks' Theorem])[
  Let $G$ be a connected graph.
  Then
  $
    chi(G) <= Delta(G)
  $
  unless $G$ is complete or an odd cycle.
]

#observation[
  Brooks' upper bound can be far from optimal in general.
]
*_proof:_*
- Assume $Delta(G) >= 3$.
- If $Delta(G) <= 2$, then connected $G$ is a path, cycle, or odd cycle, so the theorem is immediate.
- Distinguish two cases:
  - There exists $v in V(G)$ with $deg(v) < Delta(G)$.
  - Otherwise $G$ is $Delta(G)$-regular.

== Case 1: A Vertex Of Smaller Degree Exists
- Choose $v in V(G)$ with $deg(v) < Delta(G)$.
- Let $T$ be a spanning tree of $G$ rooted at $v$.
- Order vertices so descendants appear before ancestors and $v$ is last.
- In this ordering, each vertex except possibly $v$ has at most $Delta(G)-1$ earlier neighbours.
- Greedy colouring then yields a $Delta(G)$-colouring.

== Case 2: Regular Case
- Assume $G$ is $Delta(G)$-regular.
- If $kappa(G)=1$, then $G$ has a cut-vertex.
- Colour components around the cut-vertex separately and permute colour names to combine them.
- Therefore we may reduce to the 2-connected case:
  $
    kappa(G) >= 2
  $

== Key Reduction In The 2-Connected Case
- It is enough to find vertices $x,y,z in V(G)$ such that:
  - $x y, x z in E(G)$
  - $y z in.not E(G)$
  - $G - {y,z}$ is connected
- If such vertices exist:
  - Build a spanning tree of $G-{y,z}$ rooted at $x$.
  - Use an order with $x$ last and $y,z$ first.
  - Since $y$ and $z$ are nonadjacent, they may receive the same colour.
  - Greedy colouring then gives a legal $Delta(G)$-colouring.

== Lemma Completing The Proof
#lemma(title: [Structural Lemma])[
  Let $3 <= k in NN$ and let $G$ be a $k$-regular, 2-connected, non-complete graph.
  Then there exist $x,y,z in V(G)$ such that:
  1. $x y, x z in E(G)$
  2. $y z in.not E(G)$
  3. $G-{y,z}$ is connected.
]

== Why The Lemma Holds 
- First subcase: there exists $v$ such that $G-v$ is connected but not 2-connected.
  - Analyze the block tree of $G-v$.
  - Pick $y,z$ in different leaf blocks, and set $x:=v$.
  - Then $G-{y,z}$ stays connected.

== Why The Lemma Holds 
- Second subcase: $kappa(G-v) >= 2$ for every $v in V(G)$.
  - Since $G$ is not complete, pick nonadjacent $y,z$ among neighbours of some $x$.
  - $kappa(G-y) >= 2$
  - Connectivity conditions force $G-{y,z}$ to remain connected.


= Edge Colouring
== The Chromatic Index
#definition[
  An edge-colouring of a graph $G$ with $k$ colours is a function
  $
    phi: E(G) -> [k]
  $
]

#definition[
  An edge-colouring is called proper if incident edges receive distinct colours.
]

#definition[
  The chromatic index of $G$, denoted by $chi'(G)$, is the least $k$ such that $G$ has a proper edge-colouring with $k$ colours.
]

== Line Graph Connection
#definition[
  The line graph of $G$, denoted $L(G)$, is the graph with:
  - $V(L(G)) = E(G)$
  - two vertices adjacent iff the corresponding edges of $G$ are incident.
]

#observation[
- $chi(L(G)) = chi'(G) $
- $Delta(G) <= chi'(G)$
- $Delta(L(G)) <= 2(Delta(G) - 1)$
]

- Brooks tells us:
$
  chi'(G) = chi(L(G)) <= 2(Delta(G)-1)
$
  

= Konig's Theorem
== Bipartite Edge Colouring
#theorem(title: [Konig's Theorem])[
  If $G$ is bipartite, then
  $
    chi'(G) = Delta(G)
  $
]
_*proof:*_
- Degree-regular bipartite graphs admit a perfect matching (See in tha practice session).
- Removing edges of a perfect matching from a $k$-regular bipartite graph gives a $(k-1)$-regular bipartite graph.
- By induction on $k$, every $k$-regular bipartite graph is $k$-edge-colourable.
- Any bipartite graph can be embedded into a $Delta(G)$-regular bipartite supergraph.
- Restrict the colouring from the supergraph back to $G$.

= Vizing's Theorem
== Statement
#theorem(title: [Vizing's Theorem])[
  For every simple graph $G$,
  $
    chi'(G) <= Delta(G) + 1
  $
]

- Combined with the trivial lower bound:
  $
    Delta(G) <= chi'(G) <= Delta(G)+1
  $
- So every simple graph is either:
  - Class 1 ($chi'(G)=Delta(G)$) 
  - Class 2 ($chi'(G)=Delta(G)+1$).
  - It is NP-hard to determine the class of a given graph.

== Vizing's Theorem
#theorem(title: [Vizing's Theorem])[
  For every simple graph $G$,
  $
    chi'(G) <= Delta(G) + 1
  $
]

*_proof:_*
- Proof by induction on $e(G)$.
- Pick $e = u v in E(G)$ and set $G' := G - e$.
- By induction hypothesis, $G'$ has a proper edge-colouring with at most $Delta(G)+1$ colours.
- Try to colour $e$ when re-inserting it.

== The Recolouring Idea
- Each endpoint misses at least one colour among $[Delta(G)+1]$.
- If there is a common missing colour at both $u$ and $v$, assign it to $e$.
- Otherwise, what can we do?
- That's up for the TA to show you.