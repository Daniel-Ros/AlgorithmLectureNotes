#import "settings/mstyle.typ" : *

#show: conf

#title-slide()

= Matchings in Graphs

== Matching in graphs

// #theorem[Euclid's Theorem][
//   There are infinitely many prime numbers.
// ] <thm:euclid>



#set align(horizon)

The matching problem is something that students face from the first time that they encounter graph theory.
Suppose that you have a group of $n$ people, that you want to divide into pairs, how would you go about it? Is is possible that every person finds a pair?
What if some people don't want to be paired together, can you do it then?

A common approach is to model this problem with a graph G.
Each vertex represents a person, and an edge between two vertices indicates that those two people can be paired together.

#pagebreak()
#set align(horizon)
For a graph $G$, two edges $e_1, e_2 subset.eq E(G)$ are called _indepedent_ if there is no common vertex between them.

#figure(
  image("figures/L2i1.png", width: 60%),
)

#pagebreak()
#set align(horizon)
#v(10pt)
A set $M subset.eq E(G)$ of independent edges is called _mathching_.

#figure(
  image("figures/L2i2.png", width: 100%),
)

- We write $V(M)$ to denote the ends of the members of $M$.
- We often treat $M$ as the subgraph of $G$ given by $(V(M), M)$.


== Spanning subgraph
#set align(horizon)
A subgraph $H subset.eq G$ satisfying $V(H) = V(G)$ is said to be a _spanning_ subgraph of G
#figure(
  image("figures/L2i3.png", width: 100%),
)

== Perfect Matching
#set align(horizon)

#definition()[
  A matching $M subset.eq G$ is called _perfect matching_ or a _1-factor_ if $M$ is spanning $G$.
]
#figure(
  image("figures/L2i2.png", width: 78%),
)
// #figure(
//   image("figures/L2i4.jpeg", width: 40%),
// )
// #theorem(title: "Cook-Levin")[
//   CNF-SAT is npc.
// ]
// 

#pagebreak()
#set align(horizon)

The following problem is of clear intrest

#problem()[
  Given a graph $G$, find a maximum matching in $G$.
]
#text(fill: blue.darken(20%), weight: "bold")[The max-matching problem is in P
#set align(top)
#table(
  columns: (1fr, 1fr),
  align: left,
  stroke: none,
  [
- For general graphs:
  - Edmons "blossom" Algo.
  - Hopcroft - Karp $O(e(G) sqrt(v(G)))$ - time.
  ],
  [
  - For bipartite graphs:
    - Via max-flow
    - Hungarian Method
  ]

)
]


#figure(
  image("figures/L2i4.jpeg", width: 40%),
)

= Vertex Cover

== Vertex Cover
#set align(horizon)
#definition[
  A set $S subset.eq V(G)$ is said to be a _vx-cover_ of $G$ if
  $
    forall u v in E(G): u in S #text[or] v in S.
  $
]

#figure(
  image("figures/L2i5.png", width: 60%),
)
// #pause
- Trivially, $V(G)$ forms a _vx-cover_ of $G$ for every $G$.

#pagebreak()
#set align(horizon)

Conseqnetly, we are intrested in the following
#problem[
  Given a graph $G$, find a minimum _vc-cover_ of $G$.
]

#text(fill: red.darken(20%), weight: "bold")[For general graphs, the min. vx-cover problem is NPC.]


== Interplay Between Min. Vertex Cover & Max. Matching
#set align(horizon)
#set align(center)

#h(-0100pt) Let $G$ be a graph. denote:
- $nu(G) := $ size of _max_ matching in $G$.
- $tau(G) := $ size of _min_ vx-cover in $G$.


#table(
  columns: (1fr, 1fr),
  stroke: none,
  [
    Trivially, $tau(G) >= nu(G)$
    #figure(
  image("figures/L2i6.jpeg", width: 60%)
)
Any min-vc must "invest" at least 1 \
vertex for each edge in the matching.
], [ $tau(G) > nu(G)$ possible
    #figure(image("figures/L2i7.png", width: 60%)),
],
)

== Main Message

#goal[
  Find a family of graphs $cal(G)$ for which it holds that
  $
    tau(G) = nu(G) #h(20pt) forall G in cal(G)
  $
  Then, we obtain a poly-time algo. for _min-vc_ in that family.
]

#remark[
  We can run any max-matching algo, and calculate $tau(G) = nu(G)$, thus solving the decision problem 
  $
    k-V C := { G : G #text[has a _vc-cover_ of size $k$]}
  $
]

#set align(left)
In general we know that $tau(G) > nu(G)$ can happen!

== Konig, Hall & Frobinius
#[
#set align(horizon)

#theorem(title: "Konig")[$tau(G) = nu(G)$, whenever $G$ is bipartite.]

#figure(image("figures/L2i8.png", width: 50%))
]


#pagebreak()
#[
#set align(horizon)

#theorem(title: "Hall")[Let $G:=(A union.dot B, E)$ be a bipartite graph.
Then,
$
  A arrow.r.turn B #h(20pt) arrow.r.l.long.double #h(20pt)
  |N_G (S)| >= |S|, forall S subset.eq A.
$
]

#table(
  columns: (1fr, 1fr),
  stroke: none,
  align: top + center,
  [ 
    $A arrow.r.turn B$ means \
    that there exists a matching \
    that matches all $A$ into $B$.
  ],
  [
    $|N_G (S)| > |S|$ means that the amound of \
    neibours that $S$ has is at least as big \ 
    as than the size of $S$.
  ]

)

#v(10pt)
$
      N_G (u) &:= { v in V(G) : u v in E(G)} \
      N_G (S) &:= { v in V(G) : exists u in S : v in N_G (u)}
$

#pause
#[
  #set align(center)
  #show math.equation: set text(weight:"bold") 

  #text(weight: "bold", fill: rgb("#f51c0c"))[
  If $|N_G (S) | >= |S|$, $forall S in A$, then we say that $A$ satisfies the Hall-Condition!
  ]
]

]

#pagebreak()
#[
#set align(horizon)

#theorem(title: "Frobenius")[Let $G := (A union.dot B, E)$ be bipartite
#table(
  columns: (110pt,250pt, 0pt, 250pt),
  stroke: none,
  align: center,
  [],
  [
    $G$ has a \ 
    perfect matching
  ],
  [
    $arrow.r.l.double.long$
  ],
  [
    $|A| = |B|$ \ + \
    $A$ or $B$ satisfies \
    the Hall-Condition
  ]
)
]

#[
  #set align(center)
  #show math.equation: set text(weight:"bold") 

  #text(weight: "bold", fill: rgb("#d4635b"))[
  If $|N_G (S) | >= |S|$, $forall S in A$, then we say that $A$ satisfies the Hall-Condition!
  ]
]
]

== Main Messsage

#[
  #set align(center)
  *Main Message:*
]

// #text(size: 20pt, weight: "bold")[
//   My Diagram Title
//   ]
#[
#diagram(
  node-stroke: luma(20%),
  edge-corner-radius: 10pt,
  spacing: 1pt,
  mark-scale: 150%,
  // Nodes
  // node((0.67, 0), [#set text(size: 32pt)
  //   #underline[Question]], stroke: none),

    // node((0, 3), [
    // #show math.equation: set text(size: 50pt) 
    // $+$], stroke: none),
    // 
    // 
    node((-25,70), [], stroke: none),
    node((140, 100), [*Konig's Theorem*], stroke: none),
    node((120, 150), [*Hall's Theorem*], stroke: none),
    node((160, 150), [*Frobenius Theorem*], stroke: none),

    edge((140, 100), (120, 150), "<=>"),
    edge((140, 100), (160, 150), "<=>"),
    edge((160, 150), (120, 150), "<=>")
)
]