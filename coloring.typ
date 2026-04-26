#import "settings/dstyle.typ": *

#show: conf.with(
  handout: false,
  subtitle: [Graph Colouring],
)

#title-slide()

= Colourings in Graphs
== Colourings in Graphs
#set align(horizon)
#definition[
  An colouring of a graph $G$ with $k$ colours is a function
  $c: V(G) -> [k],$
  satisfying that $forall u v in E(G)$ it holds that $c(u) !=c(v)$.
]

#definition[
  A graph $G$ is said to be _$k$-colourable_ if there is a graph colouring on $G$ using at most $k$ distinct colours. i.e. $forall v: c(v) in [k]$.
]

#pause
#definition[
  Let $chi(G)$ be the minimum $k in NN$ for which $G$ is _$k$-colourable_.
]

#remark[
  Varifying that $G$ is _$k$-colourable_ for $k>=3$ is *NPC*.
]



= A Greedy Colouring Algorithm
== Setup
#set align(horizon)
- A Greedy Colouring Algorithm:
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

== bound on the number of colours used
#question[
  How useful is this algorithm for bounding $chi(G)$?
]

#grid(
  columns: (1fr, 1fr),
  column-gutter: 1.2cm,
  [
    *$C_5$ (greedy uses 3 colours)*
    #set align(center)
    #diagram(
      node-stroke: 1.5pt,
      for i in range(0, 360, step: 72) {
        let fill-col = if i == 0 or i == 144 {
          red.lighten(35%)
        } else if i == 72 or i == 216 {
          blue.lighten(35%)
        } else {
          green.lighten(35%)
        }
        node(
          (rel: (i * 1deg, 1), to: (0, 0)),
          [$v_(#(i / 72 + 1))$],
          radius: 11pt,
          fill: fill-col,
          name: "c5-" + str(i),
        )
        if i != 288 {
          edge()
        }
      },
      edge(<c5-0>, <c5-288>),
    )
    #v(0.35em)
    #text(size: 0.9em)[$v_1, v_2, v_3, v_4, v_5$]
    #linebreak()
    #text(size: 0.9em)[$1,2,1,2,3$]
  ],
  [
    *$C_6$ (greedy can also use 3 colours)*
    #set align(center)
    #diagram(
      node-stroke: 1.5pt,
      for i in range(0, 360, step: 60) {
        let fill-col = if i == 0 or i == 180 {
          red.lighten(35%)
        } else if i == 60 or i == 240 {
          blue.lighten(35%)
        } else {
          green.lighten(35%)
        }
        node(
          (rel: (i * 1deg, 1), to: (0, 0)),
          [$v_(#(i / 60 + 1))$],
          radius: 11pt,
          fill: fill-col,
          name: "c6-" + str(i),
        )
        
        if i != 300 {
          edge()
        }
      },
      edge(<c6-0>, <c6-300>),
    )
    #v(0.35em)
    #text(size: 0.9em)[$v_1, v_4, v_2, v_3, v_5, v_6$]
    #linebreak()
    #text(size: 0.9em)[$1,1,2,3,2,3$]
  ],
)


== First Consequence
- For every graph $G$, define
$
  Delta(G) := max { deg_G(v) : v in V(G) }
$
#v(-10pt)
#theorem[
  $chi(G) <= Delta(G) + 1$
]

*_Proof:_* Every vertex sees at most $Delta(G)$ distinct colours, so that by the pidgeon hole principle at least one colour is still _free_.


- When the bound is tight?
  - There are graphs with
$
  chi(G) = Delta(G) + 1
$
#v(-10pt)
  - Examples:
    - Odd cycles: $Delta = 2$ and $chi = 3$
    - Complete graphs: $Delta(K_r) = r - 1$ and $chi(K_r) = r$
  - What about the rest? Can we do better?
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
- If $Delta(G) <= 2$, then connected $G$ is a path or an even cycle, so the theorem is immediate.
- Distinguish two cases:
  - There exists $v in V(G)$ with $deg(v) < Delta(G)$.
  - Otherwise $G$ is $Delta(G)$-regular. #h(1fr) #tr[(We either choose an edge or we don't)]

== Case 1: A Vertex Of Smaller Degree Exists
- Choose $v in V(G)$ with $deg(v) < Delta(G)$.
- Let $T$ be a spanning tree of $G$ rooted at $v$.
- Order vertices so descendants appear before ancestors and $v$ is last.
- In this ordering, each vertex except possibly $v$ has at most $Delta(G)-1$ earlier neighbours.
- Each vertex has at least 1 available colour, $v$ has one because it has at most $Delta(v)-1$ neibours.
- We are left with a greedy colouring with at most $Delta(G)$ colours.
#v(-5pt)
#[
  #set align(center)
  #diagram(
    node-stroke: 1.5pt,

    node((6, 0), [$v$], name: <c1-v>, radius: 10pt, fill: yellow.lighten(35%)),
    node((4.8, -0.8), [$a$], name: <c1-a>, radius: 9pt),
    node((4.8, 0), [$c$], name: <c1-c>, radius: 9pt),
    node((4.8, 0.8), [$h$], name: <c1-h>, radius: 9pt),
    node((3.5, -1.05), [$b$], name: <c1-b>, radius: 9pt),
    node((3.5, -0.45), [$f$], name: <c1-f>, radius: 9pt),
    node((3.5, 0.25), [$k$], name: <c1-k>, radius: 9pt),
    node((3.5, 1.05), [$n$], name: <c1-n>, radius: 9pt),
    node((2.2, -1.25), [$d$], name: <c1-d>, radius: 9pt),
    node((2.2, -0.85), [$e$], name: <c1-e>, radius: 9pt),
    node((2.2, -0.45), [$g$], name: <c1-g>, radius: 9pt),
    node((2.2, 0.05), [$l$], name: <c1-l>, radius: 9pt),
    node((2.2, 0.45), [$m$], name: <c1-m>, radius: 9pt),

    edge(<c1-v>, <c1-a>),
    edge(<c1-v>, <c1-c>),
    edge(<c1-v>, <c1-h>),
    edge(<c1-a>, <c1-b>),
    edge(<c1-a>, <c1-f>),
    edge(<c1-c>, <c1-k>),
    edge(<c1-h>, <c1-n>),
    edge(<c1-b>, <c1-d>),
    edge(<c1-b>, <c1-e>),
    edge(<c1-f>, <c1-g>),
    edge(<c1-k>, <c1-l>),
    edge(<c1-k>, <c1-m>),
  )
  #v(0.35em)
  #text(size: 0.9em)[Example descendants-first order: $d,e,b,g,f,a,l,m,k,c,n,h,v$.]
]

== Case 2.1: Regular Case with vertex cut
- Assume $G$ is $Delta(G)$-regular.
- If $kappa(G)=1$, then $G$ has a cut-vertex $v$.
- Break $G$ into $2$ components with $v$ in both of them.
- In each componenet $deg(v) < Delta(G)$, colour each component using $Delta(G)$ colours using Case 1.

#place(
  top + left,
  dx: 0%,
  dy: 25%,
  figure(
    image("figures/LCi1.png", width: 30%),
  ),
)

#place(
  top + left,
  dx: 32%,
  dy: 45%,
  [
    #set text(size: 2em)
    $==>$
  ]
)

#place(
  top + left,
  dx: 40%,
  dy: 35%,
  figure(
    image("figures/LCi2.png", width: 30%),
  ),
)
#v(150pt)
- It remains to join the parts. How?
#pause
#block(width: 60%)[
- If $c(v)=i$ in $C_1$, and $c(v)=j$ in $C_2$. Swap in $C_2$ the colours of all vertices colour in $j$ to $i$ and all colours $i$ to $j$.
]
#place(
  top + left,
  dx: 65%,
  dy: 70%,
  figure(
    image("figures/LCi3.png", width: 30%),
  ),
)

// #[
//   #set align(center)
//   #set text(size: 0.7em)
//   #diagram(
//     node-stroke: 1.5pt,

//     node((0, 0), [$x$], name: <k1-x>, radius: 8pt, fill: yellow.lighten(35%)),

//     node((-1.7, 0.55), [$a_1$], name: <k1-a1>, radius: 9.5pt),
//     node((-1.7, -0.55), [$a_2$], name: <k1-a2>, radius: 9.5pt),
//     node((1.7, 0.55), [$b_1$], name: <k1-b1>, radius: 9.5pt),
//     node((1.7, -0.55), [$b_2$], name: <k1-b2>, radius: 9.5pt),

//     edge(<k1-x>, <k1-a1>),
//     edge(<k1-x>, <k1-a2>),
//     edge(<k1-x>, <k1-b1>),
//     edge(<k1-x>, <k1-b2>),

//     node(enclose: ((-2.2, -0.95), (-0.55, 0.95)), inset: 15pt, stroke: teal, fill: teal.lighten(90%), name: <k1-g1>),
//     node(enclose: ((0.55, -0.95), (2.2, 0.95)), inset: 15pt, stroke: orange, fill: orange.lighten(88%), name: <k1-g2>),
//     node((-1.35, 0.9), [$G_1$], radius: 0pt, stroke: none),
//     node((1.35, 0.9), [$G_2$], radius: 0pt, stroke: none),
//   )
// ]


// - Therefore we may reduce to the 2-connected case:
//   $
//     kappa(G) >= 2
//   $

== Case 2.2: Regular Case with $kappa(G)>=2$.

#v(5pt)
#block(width: 45%, fill: gray.lighten(50%), inset: 15pt, radius: 15pt)[
- *Goal:* find $x,y,z in V(G)$ such that:
  - $x y, x z in E(G)$
  - $y z in.not E(G)$
  - $G - {y,z}$ is connected
]

#pause
#place(
  top + left,
  dx: 50%,
  dy: 0%,
  block(width: 50%)[
    #set text(size: 0.9em)
    - If such vertices exist:
  - Build a spanning tree of $G-{y,z}$ rooted at $x$.
  - Use an order with $x$ last and $y,z$ first.
  - Since $y$ and $z$ are nonadjacent, they may receive the same colour.
  - Greedy colouring then gives a legal $Delta(G)$-colouring.
  ]
)


// #pagebreak()
// - If such vertices exist:
//   - Build a spanning tree of $G-{y,z}$ rooted at $x$.
//   - Use an order with $x$ last and $y,z$ first.
//   - Since $y$ and $z$ are nonadjacent, they may receive the same colour.
//   - Greedy colouring then gives a legal $Delta(G)$-colouring.

// #v(pt)
#grid(
  columns: (1fr, 1fr),
  column-gutter: 1.1cm,
  [
    *Cherry condition*
    #set align(center)
    #diagram(
      node-stroke: 1.5pt,

      node((0, 0), [$x$], name: <kr-x>, radius: 9pt, fill: yellow.lighten(35%)),
      node((-0.95, 1.05), [$y$], name: <kr-y>, radius: 8pt, fill: green.lighten(35%)),
      node((0.95, 1.05), [$z$], name: <kr-z>, radius: 8pt, fill: green.lighten(35%)),
      node((-1.15, -0.95), [$u$], name: <kr-u>, radius: 7pt),
      node((0, -1.25), [$w$], name: <kr-w>, radius: 7pt),
      node((1.15, -0.95), [$t$], name: <kr-t>, radius: 7pt),

      edge(<kr-x>, <kr-y>),
      edge(<kr-x>, <kr-z>),
      edge(<kr-x>, <kr-u>),
      edge(<kr-u>, <kr-w>),
      edge(<kr-w>, <kr-t>),
      edge(<kr-t>, <kr-x>),

      edge(<kr-y>, <kr-z>,[$y z in.not E(G)$], stroke: (paint: red, dash: (3pt, 2pt), thickness: 1.4pt)))
    #v(-0.65em)
    #text(size: 0.85em)[$x y, x z in E(G)$ and $G-{y,z}$ stays connected.]
  ],
  [
    *Rooted tree for greedy order*
    #set align(center)
    #diagram(
      node-stroke: 1.5pt,

      node((4.8, 0), [$x$], name: <tr-x>, radius: 9pt, fill: yellow.lighten(35%)),
      node((1, 0.8), [$y$], name: <tr-y>, radius: 8pt, fill: green.lighten(35%)),
      node((1, 1.2), [$z$], name: <tr-z>, radius: 8pt, fill: green.lighten(35%)),

      node((3.3, -0.2), [$a$], name: <tr-a>, radius: 8pt),
      node((2.3, -0.65), [$b$], name: <tr-b>, radius: 8pt),
      node((2.3, 0.2), [$c$], name: <tr-c>, radius: 8pt),
      node((1.25, -0.95), [$d$], name: <tr-d>, radius: 8pt),
      node((1.25, -0.35), [$e$], name: <tr-e>, radius: 8pt),
      node((1.25, 0.2), [$f$], name: <tr-f>, radius: 8pt),

      edge(<tr-x>, <tr-y>),
      edge(<tr-x>, <tr-z>),
      edge(<tr-x>, <tr-a>),
      edge(<tr-a>, <tr-b>),
      edge(<tr-a>, <tr-c>),
      edge(<tr-b>, <tr-d>),
      edge(<tr-b>, <tr-e>),
      edge(<tr-c>, <tr-f>),
    )
    #v(0.00em)
    #text(size: 0.85em)[Order example: $y,z,d,e,b,f,c,a,x$ (with $x$ last).]
  ],
)

#pagebreak()
#v(25pt)
#lemma(title: [Structural Lemma])[
  Let $3 <= k in NN$ and let $G$ be a $k$-regular, 2-connected, non-complete graph.
  Then there exist $x,y,z in V(G)$ such that:
  1. $x y, x z in E(G)$
  2. $y z in.not E(G)$
  3. $G-{y,z}$ is connected.
]

== Case 2.2.1: Regular Case with $kappa(G)=2$.
- *Subcase 1:*  $Kappa(G)=2 ==>$ there exists $v$ such that $G-v$ is connected but not 2-connected.
  - Analyze the block tree of $G-v$.
  - Pick $y,z$ in different leaf blocks, and set $x:=v$. #h(1fr) #tr[(pick $y,z$ that are not cut-vertices)]
  - Then $G-{y,z}$ stays connected.

#[
  #set align(center)
  #diagram(
    node-stroke: 1.4pt,

    // Three main blocks in a row, separated by gaps
    node(enclose: ((-2.5, 1.2), (-1.2, 2.2)), inset: 6pt, stroke: black, fill: rgb("#e6d8c8"), name: <blk-left>),
    node(enclose: ((-0.6, 1.2), (0.6, 2.2)), inset: 6pt, stroke: black, fill: rgb("#e6d8c8"), name: <blk-mid>),
    node(enclose: ((1.2, 1.2), (2.5, 2.2)), inset: 6pt, stroke: black, fill: rgb("#e6d8c8"), name: <blk-right>),

    // Internal vertices in leaf blocks: y in left, z in right
    node((-1.9, 1.7), [\ $y$], name: <vert-y>, radius: 5pt, fill: rgb("#2f5d77"), stroke: rgb("#2f5d77")),
    node((1.9, 1.7), [\ $z$], name: <vert-z>, radius: 5pt, fill: rgb("#2f5d77"), stroke: rgb("#2f5d77")),


    edge(<blk-mid>,<blk-left>),
    edge(<blk-mid>,<blk-right>),

    // Vertex v below
    node((0, -1.0), [\ $v$], name: <vert-v>, radius: 6pt, fill: rgb("#2f5d77"), stroke: rgb("#2f5d77")),

    // Edges from v to internal vertices in leaf blocks
    edge(<vert-v>, <vert-y>, bend: -20deg),
    edge(<vert-v>, <vert-z>, bend: 20deg),

    // Label
    // node((3.2, 1.7), [$G+v$], radius: 5pt, stroke: none),
  )
  #place(
    top + left,
    dx: 60% + 100pt,
    dy: 50% + 75pt,
    [
      $G-v$
    ]
  )

  #v(0.25em)
  #text(size: 0.85em)[Block decomposition of $G-v$: blocks are separated; $y,z$
  are non cut-vx in leaf blocks; $y,z$ are connected to $v$.]
]

== Case 2.2.2: Regular Case with $kappa(G)>2$. 
- *Subcase 2:* By assumption $kappa(G-v) >= kappa(G) - 1 >= 2$ for every $v in V(G)$.
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

#[
  #set align(center)
  #set text(size: 0.7em)
  #diagram(
    node-stroke: 1.4pt,

    node((0.0, 1.85), [$v_1$], name: <k5-1>, radius: 11pt),
    node((1.58, 0.65), [$v_2$], name: <k5-2>, radius: 11pt),
    node((1.05, -1.35), [$v_3$], name: <k5-3>, radius: 11pt),
    node((-1.05, -1.35), [$v_4$], name: <k5-4>, radius: 11pt),
    node((-1.58, 0.65), [$v_5$], name: <k5-5>, radius: 11pt),

    edge(<k5-1>, <k5-2>, stroke: (paint: red, thickness: 2pt)),
    edge(<k5-1>, <k5-3>, stroke: (paint: blue, thickness: 2pt)),
    edge(<k5-1>, <k5-4>, stroke: (paint: green, thickness: 2pt)),
    edge(<k5-1>, <k5-5>, stroke: (paint: orange, thickness: 2pt)),
    edge(<k5-2>, <k5-3>, stroke: (paint: green, thickness: 2pt)),
    edge(<k5-2>, <k5-4>, stroke: (paint: orange, thickness: 2pt)),
    edge(<k5-2>, <k5-5>, stroke: (paint: teal, thickness: 2pt)),
    edge(<k5-3>, <k5-4>, stroke: (paint: teal, thickness: 2pt)),
    edge(<k5-3>, <k5-5>, stroke: (paint: red, thickness: 2pt)),
    edge(<k5-4>, <k5-5>, stroke: (paint: blue, thickness: 2pt)),
  )
]

#pagebreak()
#definition[
  The chromatic index of $G$, denoted by $chi'(G)$. Which is the least $k$ such 
  that $G$ has a proper edge-colouring with $k$ colours.
]

#[
  #set align(center)
  #set text(size: 0.7em)
  #diagram(
    node-stroke: 1.4pt,

    node((0.0, 1.85), [$v_1$], name: <k5-1>, radius: 11pt),
    node((1.58, 0.65), [$v_2$], name: <k5-2>, radius: 11pt),
    node((1.05, -1.35), [$v_3$], name: <k5-3>, radius: 11pt),
    node((-1.05, -1.35), [$v_4$], name: <k5-4>, radius: 11pt),
    node((-1.58, 0.65), [$v_5$], name: <k5-5>, radius: 11pt),

    edge(<k5-1>, <k5-2>, stroke: (paint: red, thickness: 2pt)),
    edge(<k5-1>, <k5-3>, stroke: (paint: blue, thickness: 2pt)),
    edge(<k5-1>, <k5-4>, stroke: (paint: green, thickness: 2pt)),
    edge(<k5-1>, <k5-5>, stroke: (paint: orange, thickness: 2pt)),
    edge(<k5-2>, <k5-3>, stroke: (paint: green, thickness: 2pt)),
    edge(<k5-2>, <k5-4>, stroke: (paint: orange, thickness: 2pt)),
    edge(<k5-2>, <k5-5>, stroke: (paint: teal, thickness: 2pt)),
    edge(<k5-3>, <k5-4>, stroke: (paint: teal, thickness: 2pt)),
    edge(<k5-3>, <k5-5>, stroke: (paint: red, thickness: 2pt)),
    edge(<k5-4>, <k5-5>, stroke: (paint: blue, thickness: 2pt)),
  )
]
- here $chi'(G) = 5$.



== Line Graph Connection
#definition[
  The line graph of $G$, denoted $L(G)$, is the graph with:
  - $V(L(G)) = E(G)$
  - two vertices adjacent iff the corresponding edges of $G$ are incident.
]

#place(
  top + center,
  dx: -5%,
  dy: 40%,
  figure(
    image("figures/LCi4.png", width: 45%),
  ),
)

#pagebreak()
#observation[
- $chi(L(G)) = chi'(G) $
- $Delta(G) <= chi'(G)$
- $Delta(L(G)) <= 2(Delta(G) - 1)$
]

- Brooks tells us:
$
  chi'(G) = chi(L(G)) <= 2(Delta(G)-1)
$

#place(
  top + center,
  dx: -5%,
  dy: 60%,
  figure(
    image("figures/LCi5.png", width: 75%),
  ),
)


= Konig's Theorem
== Bipartite Edge Colouring
#[
  #set text(size: 0.9em)
#theorem(title: [Konig's Theorem])[
  If $G$ is bipartite, then
  $
    chi'(G) = Delta(G)
  $
]
#v(-10pt)
- Rember that $chi'(G) >= Delta(G)$ always holds, so we only need to show $chi'(G) <= Delta(G)$ for bipartite graphs.
_*proof:*_
- Degree-regular bipartite graphs admit a perfect matching (See in tha practice session).
- Removing edges of a perfect matching from a $k$-regular bipartite graph gives a $(k-1)$-regular bipartite graph.
- By induction on $k$, every $k$-regular bipartite graph is $k$-edge-colourable.
- Any bipartite graph can be embedded into a $Delta(G)$-regular bipartite supergraph.
- Restrict the colouring from the supergraph back to $G$.
]
#place(
  top + center,
  dx: 25%,
  dy: 61%,
  figure(
    image("figures/LCi6.png", width: 52%),
  ),
)

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
- So every graph is either:
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
 
#[
  #set align(center)
  #diagram(
    node-stroke: 1.2pt,

    node((-0.65, 0), [\ $u$], name: <vz-u>, radius: 6pt),
    node((0.65, 0), [\ $v$], name: <vz-v>, radius: 6pt),

    node((-1.6, 0.8), name: <vz-u1>, radius: 3.5pt),
    node((-1.6, 0.25), name: <vz-u2>, radius: 3.5pt),
    node((-1.6, -0.25), name: <vz-u3>, radius: 3.5pt),
    node((-1.6, -0.8), name: <vz-u4>, radius: 3.5pt),

    node((1.6, 0.8), name: <vz-v1>, radius: 3.5pt),
    node((1.6, 0.25), name: <vz-v2>, radius: 3.5pt),
    node((1.6, -0.25), name: <vz-v3>, radius: 3.5pt),
    node((1.6, -0.8), name: <vz-v4>, radius: 3.5pt),

    edge(<vz-u>, <vz-v>, [$e$], stroke: (paint: black, thickness: 1.5pt)),

    edge(<vz-u>, <vz-u1>, [$1$], stroke: (paint: red, thickness: 1.5pt)),
    edge(<vz-u>, <vz-u2>, [$2$], stroke: (paint: blue, thickness: 1.5pt)),
    edge(<vz-u>, <vz-u3>, [$3$], stroke: (paint: green, thickness: 1.5pt)),
    edge(<vz-u>, <vz-u4>, [$4$], stroke: (paint: orange, thickness: 1.5pt)),

    edge(<vz-v>, <vz-v1>, [$2$], stroke: (paint: blue, thickness: 1.5pt)),
    edge(<vz-v>, <vz-v2>, [$3$], stroke: (paint: green, thickness: 1.5pt)),
    edge(<vz-v>, <vz-v3>, [$4$], stroke: (paint: orange, thickness: 1.5pt)),
    edge(<vz-v>, <vz-v4>, [$5$], stroke: (paint: teal, thickness: 1.5pt)),
  )

]

== The Recolouring Idea: Case 1
#v(50pt)
- Each endpoint misses at least one colour among $[Delta(G)+1]$.
- If there is a common missing colour at both $u$ and $v$, assign it to $e:= u v$.
#place(
  top + center,
  dx: 0%,
  dy: 41%,
  figure(
    image("figures/LCi7.png", width: 85%),
  ),
)

== The Recolouring Idea: Case 2
- Each endpoint misses at least one colour among $[Delta(G)+1]$.
- If there is no common missing colour at both $u$ and $v$.
- Let $c_1$ be the colour that $u$ dont see, and $c_0$ the colour that $v$ dont see.
- Let $v w_1$ be the edge coloured in $c_1$.
  - If $w_1$ also doesn't see $c_0$ colour $v w_1$ in $c_0$, now $v$ doens't see $c_1$ 
    so we can colour $u v$ in $c_1$.
#place(
  top + center,
  dx: 0%,
  dy: 41%,
  figure(
    image("figures/LCi8.png", width: 85%),
  ),
)

== The Recolouring Idea: Case 2
- Let $c_1$ be the colour that $u$ dont see, and $c_0$ the colour that $v$ dont see.
- Let $v w_1$ be the edge coloured in $c_1$.
- If $w_1$ also sees see $c_0$, let $c_2$ be the colour that $w_1$ doesn't sees.
  - let $v w_2$ be an edge coloured in $c_2$.
    - If $w_2$ doesn't see $c_0$, then we can colour $v w_2$ in $c_0$.
    - Now, $v$ doesnt see's the colour $phi(v w_2) = c_2$ so we can colour $v w_1$ in $c_2$
    - Finally, now $v$ doesn't see the colour $phi(v w_1) = c_1$ so we can colour $u v$ in $c_1$.
#place(
  top + center,
  dx: 0%,
  dy: 45%,
  figure(
    image("figures/LCi9.png", width: 95%),
  ),
)

== The Recolouring Idea: Case k+
#set align(horizon + center)
#set text(size: 1.4em)
It remains to prove that this process stops, which is left for the *TA* session.

#tr[the intuition is that we always have $2$ free colours per vertex so at some point those colours will start repeating.]

