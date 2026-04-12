#import "settings/dstyle.typ": *
#import algorithmic: algorithm-figure, style-algorithm
#show: style-algorithm
#import "@preview/diagraph:0.3.6": *


#show: conf.with(handout: false, subtitle: [Vertex-connectivity in graphs])

#title-slide()

= Connectivity
== Blocks of graphs
#definition[
  - For a graph $G$, write
  $
    C(G) := "number of connected components of " G
  $
]

#definition[
  - Let $X subset.eq V(G) cap E(G)$.
  - If $C(G-X) > C(G)$, then $X$ is called a _disconnector_
]

#pagebreak()
#columns(2)[
  if $X subset.eq V(G)$, then $X$ is a _vx-disconnector_.

  - vx-disconnectors of size 1 are called _cut-vxs_.
  #colbreak()
  if $X subset.eq E(G)$, then $X$ is a _edge-disconnector_.

  - edge-disconnectors of size 1 are called _bridges_.
]
- The ends of bridges are cut-vxs.
- The opposite is *not* true!

#observation(title: "H.W.")[
  $
    e in E(G) "is a brige" <=> e "does not lie on a cycle of " G
  $
]

#pagebreak()
#definition[
  A maximal connected subgraph of $G$ containing no cut-vxs is called a block of $G$
]

= Whitney's Theorem
== Whitney's Theorem
#theorem(title: "Whitney's Theorem")[
  - $G$ - a connected graph with $v(G) >= 3$
  $
    G "has no cut-vxs" <=> "any 2 verticies of " G " lies on a common cycle".
  $
]
*_proof._*\
#alternatives()[
  $arrow.double.l$
  - Assume $G$ has a cut vertex, denoted by $v$.
  - $v$ seperates the graph into 2 components $C_1,C_2$.
  - take $v in C_1, u in C_2$, then $u,v$ does not lie on a cycle. *contridition*
][
  $=>$
  - Suppose $G$ has no cut-vxs.
  - We prove by induction on
  $
    delta_G(u,v) := "length of the shortest path u" ~> "v in "G
  $
  - basis:
    - let $u,v in V(G)$ have $delta_G (u,v) = 1$
    - if $u v in E(G)$ is a brigde, the $u,v$ are cut-vxs. *contridiction*.
    - from the observation $u v$ lies on a cycle.
    #place(dx: 18em, dy: -0.5em)[
      #set text(size: 15pt)
      #observation(title: "H.W.")[
        $
          e in E(G) "is a brige" <=> e "does not lie on a cycle of " G
        $
      ]]
][
  - Suppose $G$ has no cut-vxs.
  - Suppose that the claim hold true for all
    $"pairs of verecies " u,v "such that " delta_G(u,v) < k$
  - Consider a pair $u,v in V(G)$ satisfying $delta_G (u,v) = k$
  - Let $P$ be the shortest path $u ~> v$, and let $v'$ denote the vertex before $v$ on $P$.
  - As $delta_G (u, v') = k -1$, there is a cycle  $C$ containting $u, v'$
  - If $v in V(C)$ we are done
][
  - Otherwise, we can divide $C$ into 2 arcs
  #align(center)[
    $u ~> v' quad v` ~> u$
  ]
  - As $G$ has no cut-vxs, $G-v'$ is still connected,
  - There is a path from $v$ to a vertex $x$ that lies on one of the arcs
  - W.L.O.G, let $x in u ~> v'$
  - Then the cycle $u ~> x ~> v -> v' ~> u$ is a cycle of size $k$, and contains both $u$ and $v$.
]

== Consequences of Whitney's Theorem
- Any two blocks of $G$ meet in at most one vertex.
- If two block do meet, their intersection vertex is a cut-vertex.
- The blocks of $G$ partition $E(G)$ (H.W.).
- Every cycle of $G$ lies in precisly one block of $F$(H.W.).

== Block tree
- Given a graph $G$
- Define the following auxiliary graph:
  - $B(G) := {B : B subset.eq G "is a block of G"}$
  - $C(G) := {v : v in V(G) "is a cut-vx of G"}$
- Let $"BC"(G)$ denote the follwing graph
  - The vertecies of $"BC"(G)$ are $B(G) cap C(G)$
  - The edges of $"BC"(G)$ are ${{B,v} : B in B(G), v in C(G) "and" v in B}$

#theorem[
  if $G$ is connected then $"BC"(G)$ is a tree
]

= Assesing connectivity
== Assesing connectivity
#align(center)[
  #question[
    Given these graphs, which one is more connected?
  ]
  #columns(3)[
    #cetz-canvas({
      import cetz.draw: *

      let angle = (360 / 5) * 1deg
      let radius = 3
      for i in range(0, 5) {
        circle(
          (calc.cos(angle * i) * radius, calc.sin(angle * i) * radius),
          radius: 0.15,
          fill: black,
          stroke: 0.5pt + black,
          name: "v" + str(i),
        )
      }

      for i in range(0, 5) {
        for j in range(0, 5) {
          if i != j {}
          line("v" + str(i), "v" + str(j))
        }
      }
    })
    #colbreak()
    #cetz-canvas({
      import cetz.draw: *

      let angle = (360 / 6) * 1deg
      let radius = 2

      for i in range(0, 6) {
        circle(
          (calc.cos(angle * i) * radius, calc.sin(angle * i) * radius),
          radius: 0.15,
          fill: black,
          stroke: 0.5pt + black,
          name: "v" + str(i),
        )
      }

      for i in range(0, 6) {
        for j in range(0, 6) {
          if i != j {}
          line("v" + str(i), "v" + str(j))
        }
      }

      translate((0, -5))

      for i in range(0, 3) {
        circle(
          (calc.cos(angle * i * 2) * radius, calc.sin(angle * i * 2) * radius),
          radius: 0.15,
          fill: black,
          stroke: 0.5pt + black,
          name: "n" + str(i),
        )
      }

      for i in range(0, 3) {
        for j in range(0, 3) {
          if i != j {}
          line("n" + str(i), "n" + str(j))
        }
      }

      line("v4", "n1")
    })
    #colbreak()

    #cetz-canvas({
      import cetz.draw: *
      circle((0, 0), radius: 0.15, fill: black, stroke: 0.5pt + black)
    })
  ]
]

== Definition I

#definition[
  - $0 <= k in NN$
  - $G$ - graph with $v(G) > k$
  - If $G-X$ is conncted $forall X subset.eq V(G), |X| <= k-1$ then G is called _k-connected_
]

#align(center)[
  #cetz-canvas({
    import cetz.draw: *

    circle((0.5, 2), radius: 0.15, fill: black, stroke: 0.5pt + black, name: "v1")
    circle((0.5, -2), radius: 0.15, fill: black, stroke: 0.5pt + black, name: "v3")
    circle((-5, 0), radius: 0.15, fill: black, stroke: 0.5pt + black, name: "v2")
    circle((5, 0), radius: 0.15, fill: black, stroke: 0.5pt + black, name: "v4")

    line("v1", "v2")
    line("v2", "v3")
    line("v3", "v4")
    line("v4", "v1")

    (pause,)

    circle("v1", radius: 10pt, stroke: 3pt + red)
    circle("v3", radius: 10pt, stroke: 3pt + red)
  })


]

== Definition I
#definition[
  - $0 <= k in NN$
  - $G$ - graph with $v(G) > k$
  - If $G-X$ is conncted $forall X subset.eq V(G), |X| <= k-1$ then G is called _k-connected_
]

- To be $k$-connected, $v(G) > k$ must hold
- What about $K_1$?
  - We assume it is connected
  - But our definition $K_1$ is #text(red)[not] connected!
  - We'll fix this later



#pagebreak()
#definition[
  The largest $k in ZZ_(>=0)$ for which $G$ is $k$-connected is denoted by $kappa(G)$
]

- All disconnected graphs have $kappa(G) = 0$
- All connected graphs (but $K_1$) are *1-connected*
  - $kappa(G) >= 1$
  - $kappa(K_1) = 0$ #emoji.face.sad
- Cycles with 3 or more vertecies are *2-connected*
- $kappa(K_r) = r-1$

Again $kappa(K_1) = 0$, is annoying, can we fix it?

== Definition II
#definition[
  - $G$ a graph
  - $A,B subset.eq V(G)$
  - let $rho_g (A,B) :=$ the number of vx-disjoint $(A,B)$-paths
]

#definition[
  $G$ is _k-connected_ if $rho_g (A,B) >= k " "forall {u,v} in binom(V(G), 2)$
]
- A graph is *1-connected* $<=>$ it is connected
- Here, $K_1$ is connected

- What definition should we choose?
- Menger tell us
#align(center)[
  #set text(size: 24pt)
  *They are the same*
]
== Our definition
#definition[
  The minimum size of a vx set $X$ such that $G-X$ is disconnected or has a single vx is called the _vx-connectivity_ of $G$ and is denoted by $kappa(G)$
]
#definition[
  A graph $G$ is called _k-connected_ if $kappa(G) >= k$
]

#todo[ continute with wolf, add examples]

= Menger's theorem
== Menger's theorem
#definition[
  - $A,B subset.eq V(G)$
  - Denote by $kappa_G (A,B)$ the size of the *least* (A,B)-vx-disconnetor
]

#theorem(title: [Menger's theorem])[
  Let $G$ be a graph and let $A,B subset.eq V(G)$ non empty.
  Then
  $
    kappa_G (A,B) = rho_G (A,B)
  $
]
- You know this by the name "min-cut-max-flow"
- $kappa_G (A,B) >= rho_G (A,B)$ is trivial #todo[add explanation]
- We need to prove
$
  kappa_G (A,B) <= rho_G (A,B)
$

== Edge contractions
- Consider the edge $e = x y$
- To constract $e$:
  - remove $e$
  - merge $x$ and $y$ into one vertex $v_(x y)$
  - connect $v_(x y)$ to $N_G (x) cap N_G (y)$, remove any dupplicant edges that may arise
\
- Denote by $G slash e$ the graph resualting from contracting $e$

== Menger's theorem
#theorem(title: [Menger's theorem])[
  Let $G$ be a graph and let $A,B subset.eq V(G)$ non empty.
  Then
  $
    kappa_G (A,B) = rho_G (A,B)
  $
]
- Set $kappa := kappa_G (A,B)$ and $rho:= rho_G (A,B)$
- Proof by induction on $e(G)$
- If $e(G) = 0$ the graph is disconnected
  - $rho = |A cap B| = kappa$

#pagebreak()
#theorem(title: [Menger's theorem])[
  Let $G$ be a graph and let $A,B subset.eq V(G)$ non empty.
  Then
  $
    kappa_G (A,B) = rho_G (A,B)
  $
]
- assume $e(G) > 0$
- let $e=x y in E(G)$ be an arbitrary edge
- In $G slash e$, define $A_e subset.eq V(G slash e)$ as follows
  - If $x,y in.not A$, then $A_e := A$
  - if $x in A$,$y in.not A$, then $A_e := (A \\ {x}) cup {V_e}$
  - if $x in.not A$,$y in A$, then $A_e := (A \\ {x}) cup {V_e}$
  - if $x,y in A$, then $A_e := (A \\ {x,y }) cup {V_e}$
  \
- Define $B_e$ in the same manner

#pagebreak()
- Suppose that $G slash e$ has $kappa$ vx-disjoint $(A_e,B_e)$-paths
  - Any path not containing $v_e$ exists in $G$
  - if none of the paths here contains $v_e$, then we are done
- suppose that there is a path in the linkage containing $v_e$.
#columns(2)[
  $x y$ can be expanded in the path
  #colbreak()
  $x y$ cannot be expanded in the path
]


== Menger's theorem
- Suppose that $G slash e$ don't have $kappa$ vx-disjoint $(A_e,B_e)$-paths
- $kappa_G_e (A,B) < kappa$
- Any $(A_e,B_e)$-vx-disconnector in $G slash e$ containe $v_e$
  - if not, $G$ has an (A,B)-vx-disconnector of size $< kappa$
- Any $(A_e,B_e)$-vx-disconnector in $G slash e$ is of size $kappa - 1$
#v(-20pt)
#align(center)[

  #cetz-canvas({
    import cetz.draw: *
    import cetz.matrix: ident

    rect((0, 0), (1, 3), fill: gray.lighten(70%), radius: 0.2)
    rect((2, 0.5), (3, 2.5), fill: red.lighten(70%), radius: 0.2, name: "middle")
    rect((4, 0), (5, 3), fill: gray.lighten(70%), radius: 0.2)

    cetz.decorations.wave(line((0.5, 0.2), (2.25, 1)), segments: 2, amplitude: 0.1)
    cetz.decorations.wave(line((0.5, 1), (2.25, 1.5)), segments: 2, amplitude: 0.1)
    cetz.decorations.wave(line((0.5, 2), (2.25, 2)), segments: 2, amplitude: 0.1)
    cetz.decorations.wave(line((0.5, 2.8), (2.25, 2.2)), segments: 2, amplitude: 0.1)

    content("middle", [$v_e$], anchor: "south")
    circle("middle", fill: black, radius: 1pt, anchor: "north")

    cetz.decorations.wave(line((2.75, 1), (4.5, 0.2)), segments: 2, amplitude: 0.1)
    cetz.decorations.wave(line((2.75, 1.5), (4.5, 1)), segments: 2, amplitude: 0.1)
    cetz.decorations.wave(line((2.75, 2), (4.5, 2)), segments: 2, amplitude: 0.1)
    cetz.decorations.wave(line((2.75, 2.2), (4.5, 2.8)), segments: 2, amplitude: 0.1)


    translate((10, 2.5))

    rect((0, 0), (1, 3), fill: gray.lighten(70%), radius: 0.2)
    rect((2, 0.5), (3, 2.5), fill: red.lighten(70%), radius: 0.2, name: "middle")
    rect((4, 0), (5, 3), fill: gray.lighten(70%), radius: 0.2)

    cetz.decorations.wave(line((0.5, 0.2), (2.25, 1)), segments: 2, amplitude: 0.1)
    cetz.decorations.wave(line((0.5, 1), (2.25, 1.5)), segments: 2, amplitude: 0.1)
    cetz.decorations.wave(line((0.5, 2), (2.25, 2)), segments: 2, amplitude: 0.1)
    cetz.decorations.wave(line((0.5, 2.8), (2.25, 2.2)), segments: 2, amplitude: 0.1)

    content("middle", [$x$], anchor: "north", name: "x")
    content((rel: "middle.north", to: (0, 1)), [$y$], anchor: "south", name: "y")
    circle("middle", fill: black, radius: 1pt, anchor: "north", name: "x")
    circle("y.south", fill: black, radius: 1pt, anchor: "north", name: "y")
    line("x", "y")
    cetz.decorations.wave(line((2.75, 1), (4.5, 0.2)), segments: 2, amplitude: 0.1)
    cetz.decorations.wave(line((2.75, 1.5), (4.5, 1)), segments: 2, amplitude: 0.1)
    cetz.decorations.wave(line((2.75, 2), (4.5, 2)), segments: 2, amplitude: 0.1)
    cetz.decorations.wave(line((2.75, 2.2), (4.5, 2.8)), segments: 2, amplitude: 0.1)
    translate((0, -5))

    rect((0, 0), (1, 3), fill: gray.lighten(70%), radius: 0.2)
    rect((2, 0.5), (3, 2.5), fill: red.lighten(70%), radius: 0.2, name: "middle")
    rect((4, 0), (5, 3), fill: gray.lighten(70%), radius: 0.2)

    cetz.decorations.wave(line((0.5, 0.2), (2.25, 1)), segments: 2, amplitude: 0.1)
    cetz.decorations.wave(line((0.5, 1), (2.25, 1.5)), segments: 2, amplitude: 0.1)
    cetz.decorations.wave(line((0.5, 2), (2.25, 2)), segments: 2, amplitude: 0.1)
    cetz.decorations.wave(line((0.5, 2.8), (2.25, 2.2)), segments: 2, amplitude: 0.1)


    circle((rel: "middle", to: (0, 0.5)), fill: black, radius: 1pt, anchor: "north", name: "y")
    circle((rel: "middle", to: (0, -0.5)), fill: black, radius: 1pt, anchor: "north", name: "x")
    content("y", [$y$], anchor: "south")
    content("x", [$x$], anchor: "north")
    line("x", "y")
    cetz.decorations.wave(line((2.75, 1), (4.5, 0.2)), segments: 2, amplitude: 0.1)
    cetz.decorations.wave(line((2.75, 1.5), (4.5, 1)), segments: 2, amplitude: 0.1)
    cetz.decorations.wave(line((2.75, 2), (4.5, 2)), segments: 2, amplitude: 0.1)
    cetz.decorations.wave(line((2.75, 2.2), (4.5, 2.8)), segments: 2, amplitude: 0.1)

    translate((-10, 2.5))

    line((5.5, 2), (9.5, 4.5), mark: (end: ">"))
    line((5.5, 2), (9.5, -1), mark: (end: ">"))
  })
]

#pagebreak()
We are now in this position:
- $X := (A,B)$-vx-disconnector (Maybe $X=A$ or $X=B$)
- $|X| = kappa$
- $X$ spans $e$
#align(center)[
  #cetz-canvas({
    import cetz.draw: *

    rect((0, 0), (1, 3), fill: gray.lighten(70%), radius: 0.2)
    rect((2, 0.5), (3, 2.5), fill: red.lighten(70%), radius: 0.2, name: "middle")
    rect((4, 0), (5, 3), fill: gray.lighten(70%), radius: 0.2)

    cetz.decorations.wave(line((0.5, 0.2), (2.25, 1)), segments: 2, amplitude: 0.1)
    cetz.decorations.wave(line((0.5, 1), (2.25, 1.5)), segments: 2, amplitude: 0.1)
    cetz.decorations.wave(line((0.5, 2), (2.25, 2)), segments: 2, amplitude: 0.1)
    cetz.decorations.wave(line((0.5, 2.8), (2.25, 2.2)), segments: 2, amplitude: 0.1)


    circle((rel: "middle", to: (0, 0.5)), fill: black, radius: 1pt, anchor: "north", name: "y")
    circle((rel: "middle", to: (0, -0.5)), fill: black, radius: 1pt, anchor: "north", name: "x")
    content("y", [$y$], anchor: "south")
    content("x", [$x$], anchor: "north")
    line("x", "y")
    cetz.decorations.wave(line((2.75, 1), (4.5, 0.2)), segments: 2, amplitude: 0.1)
    cetz.decorations.wave(line((2.75, 1.5), (4.5, 1)), segments: 2, amplitude: 0.1)
    cetz.decorations.wave(line((2.75, 2), (4.5, 2)), segments: 2, amplitude: 0.1)
    cetz.decorations.wave(line((2.75, 2.2), (4.5, 2.8)), segments: 2, amplitude: 0.1)
  })
]
- Note now that
$
  kappa_(G-e) (A,X) >= kappa quad "and" quad kappa_(G-e) (X, B) >= kappa
$

== Implication of Menger's theorem
#corollary(title: "H.W.")[
  - Let $G$ be a graph. Then
  $
    kappa(G) = min {rho_G (u,v) : u,v in V(G), u != v }
  $
]

#lemma(title: "The Extension Lemma H.W.")[
  - $G$ - $k$-connected graph
  - $H$ obtained from $G$ by:
    - Adding a new vertex
    - Connecting the new vertex to $k$ arbitrary vertecies
  - Then $H$ is $k$-connected,
]

#pagebreak()
- Given $x in V(G)$ and $B subset.eq V(G)$ s.t. $x in.not B$, we write _$(x,B)$-fan_ to denote:

#lemma(title: "Fan Lemma H.W")[
  - $G$ - $k$-connected graph
  - $x in V(G)$ and $B subset.eq V(G) \\ {x }$
  Then $G$ has an $(x,B)$-fan if size $min{k,|B|}$
]

== Dirac's theorem
#theorem(title: "Dirac's Theorem")[
  - $2 <= k in NN$
  - $G$ - $k$-connected graph
  - $S subset.eq V(G)$ such that $2 <= |S| <= k$
  Then $G$ contains a cycle constains $S$
]
#alternatives[
  - By induction on $k$
  - for $k=2$, the claim hols by whitney's theorem.
][
  - assume $k>=3$
  - let $x in S$ be arbitrary and set $T:= S\\{x}$
  - $kappa(G -x) >= k-1$ So there is a cycle $C$ in $G-x$ containing $T$.
  - let $F$ be an $(x,C)$-fan in $G$ of size $min{k, v(C)}$
  - Note the $T$ partitions $C$ into $k-1$ arcs
  - At least two of the paths in the fans land in the same arc on $C$
  - We can extend $C$ to conatin $x$
  // #sym.space.nobreak$#get-qed-symbol()$
]
