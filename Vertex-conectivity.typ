#import "settings/dstyle.typ": *
#import algorithmic: algorithm-figure, style-algorithm
#show: style-algorithm
#import "@preview/fletcher:0.5.8" as fletcher: diagram, edge, node


#show: conf.with(
  handout: false,
  subtitle: [Vertex-connectivity in graphs],
)

#title-slide()

= Connectivity
== Graph disconnectors
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

#align(center)[

  #cetz-canvas({
    import cetz.draw: *

    // Set global stroke properties
    set-style(stroke: (thickness: 1.5pt, cap: "round"))

    // Define coordinates
    let v1 = (0, 0)
    let v2 = (0, 2)
    let v3 = (2, 2)
    let v4 = (2, 0)
    let v5 = (3.5, 2)
    let v6 = (3.5, 0)
    let v7 = (5, 1)
    let v8 = (6.5, 2)
    let v9 = (6.5, 0)

    // Square on the left
    line(v1, v2, v3, v4, close: true)

    // Connecting lines (Red)
    line(v3, v5, stroke: (paint: red, thickness: 2pt))
    line(v4, v6, stroke: (paint: red, thickness: 2pt))

    // Middle vertical line
    line(v5, v6)

    // Triangle and Butterfly shape
    line(v5, v7, v6)
    line(v7, v8, v9, v7)

    // Draw nodes (black dots)
    let nodes = (v1, v2, v3, v4, v5, v6, v7, v8, v9)
    for p in nodes {
      circle(p, radius: 0.08, fill: black, stroke: none)
    }

    // Red circle around the intersection node
    circle(v7, radius: 0.25, stroke: (
      paint: red,
      thickness: 1.5pt,
    ))
  })
]

#pagebreak()
#columns(2)[
  if $X subset.eq V(G)$, then $X$ is a _vx-disconnector_.
  #cetz-canvas({
    import cetz.draw: *
    let v5 = (3.5, 2)
    let v6 = (3.5, 0)
    let v7 = (5, 1)
    let v8 = (6.5, 2)
    let v9 = (6.5, 0)

    let nodes = (v5, v6, v7, v8, v9)
    for p in nodes {
      circle(p, radius: 0.08, fill: black, stroke: none)
    }

    // Triangle and Butterfly shape
    line(v6, v5, v7, v6)
    line(v7, v8, v9, v7)

    circle(v7, radius: 0.25, stroke: (
      paint: red,
      thickness: 1.5pt,
    ))
  })
  - vx-disconnectors of size 1 are called _cut-vxs_.
  #colbreak()
  if $X subset.eq E(G)$, then $X$ is a _edge-disconnector_.

  #align(center)[
    #cetz-canvas({
      import cetz.draw: *

      // Function to draw a blob shape
      let blob(center, name) = {
        group(name: name, {
          catmull(
            (center.at(0) - 0.8, center.at(1) + 0.5),
            (center.at(0) - 0.5, center.at(1) + 0.8),
            (center.at(0) + 0.3, center.at(1) + 1.2),
            (center.at(0) + 0.9, center.at(1) + 0.5),
            (center.at(0) + 0.9, center.at(1) - 0.7),
            (center.at(0) + 0.2, center.at(1) - 1.1),
            close: true,
          )
        })
      }

      // Draw three components
      blob((0, 0), "c2")
      blob((4, 0), "c3")

      // Draw the bridge
      let bridge-start = (1, 0.2)
      let bridge-end = (3.4, 0.2)

      line(
        bridge-start,
        bridge-end,
        stroke: (thickness: 2pt),
        name: "bridge-line",
      )

      // Nodes at bridge ends
      circle(bridge-start, radius: 0.08, fill: black)
      circle(bridge-end, radius: 0.08, fill: black)

      // Bridge label
      content((2, 0.6), [bridge])
    })
  ]

  - edge-disconnectors of size 1 are called _bridges_.
]
- The ends of bridges are cut-vxs.
- The opposite is *not* true!

#observation(title: "H.W.")[
  $
    e in E(G) "is a brige" <=> e "does not lie on a cycle of " G
  $
]

= Whitney's Theorem
== Whitney's Theorem
#theorem(title: "Whitney's Theorem")[
  - $G$ - a connected graph with $v(G) >= 3$
  $
    G "has no cut-vxs" <=> "any 2 verticies of " G " lies on a common cycle".
  $
]
#pause

*_proof $arrow.double.l$._*\
- Assume $G$ has a cut vertex, denoted by $v$. #pause
- $v$ seperates the graph into 2 components $C_1,C_2$.
- Take $w in C_1, u in C_2$ both should hold true
1. A cycle $C := w x_1 ... x_ell u w$ exists in $G$.
2. If we remove $v$ then $u$ and $v$ are disconencted.
*contridition:* If $v in C$ then removing $v$ or any vertex in $C$ wont seperate $w$ from $u$, and if $v in.not C$ then the path $w x_1 ... x_ell u$ still exists.

#place(
  top + left,
  dx: 18cm,
  dy: 5cm,
  figure(
    image("figures/L3I1.png", width: 35%),
  ),
)

#place(
  top + left,
  dx: 15cm,
  dy: 7.5cm,
  align(center)[
    #cetz.canvas({
      import cetz.draw: *

      circle((0, 0), name: "C1", fill: gray.lighten(50%))
      circle((2, 0), name: "C2", fill: gray.lighten(50%))

      // cetz.decorations.wave(line("C1.center", "C2.center", name: "E"), segments: 2, amplitude: 0.1)

      circle(
        (1, 0),
        name: "C1",
        radius: 2pt,
        fill: red,
        stroke: red,
      )
      // circle("C1", radius: 2pt, fill: red, stroke: red)
      // circle("C2", radius: 2pt, fill: red, stroke: red)
    })
  ],
)




#pagebreak()
#theorem(title: "Whitney's Theorem")[
  - $G$ - a connected graph with $v(G) >= 3$
  $
    G "has no cut-vxs" <=> "any 2 verticies of " G " lies on a common cycle".
  $
]
$=>$
- Suppose $G$ has no cut-vxs.
- We prove by induction on
$
  delta_G(u,v) := "length of the shortest path u" ~> "v in "G
$
- Basis:
  - Let $u,v in V(G)$ have $delta_G (u,v) = 1$
  - If $u v in E(G)$ is a brigde, the $u,v$ are cut-vxs. *contridiction*.
  - From the observation $u v$ lies on a cycle.
  #place(dx: 21em, dy: -0.5em)[
    #set text(size: 15pt)
    #block(width: 80%)[
      #observation(title: "H.W.")[
        $
          e in E(G) "is a brige" <=> e "does not lie on a cycle of " G
        $
      ]]
  ]
#pagebreak()
#theorem(title: "Whitney's Theorem")[
  - $G$ - a connected graph with $v(G) >= 3$
  $
    G "has no cut-vxs" <=> "any 2 verticies of " G " lies on a common cycle".
  $
]
- Suppose $G$ has no cut-vxs.
- Suppose that the claim hold true for all
  $"pairs of verecies " u,v "such that " delta_G(u,v) < k$
- Consider a pair $u,v in V(G)$ satisfying $delta_G (u,v) = k$
- Let $P$ be the shortest path $u ~> v$, and let $v'$ denote the vertex before $v$ on $P$.
- As $delta_G (u, v') = k -1$, there is a cycle $C$ containting $u, v'$
#v(-16pt)
#align(center)[
  #diagram(
    node((0, 0), [$u$], name: <u>),
    node((1, 0), name: <v1>),
    node((2, 0), name: <v2>),
    node((3, 0), name: <v3>),
    node((4, 0), name: <v4>),
    node((5, 0), [$v'$], name: <vv>),
    node((6, 0), [$v$], name: <v>),

    edge(<u>, <vv>, "~>"),
    edge(<vv>, <v>, "->"),

    edge(<u>, <v2>, "->", bend: 40deg, stroke: (
      paint: red.darken(10%), // The color
      thickness: 1.8pt, // The width
      dash: "dashed", // The pattern
    )),
    edge(<v2>, <v4>, "->", bend: -40deg, stroke: (
      paint: red.darken(10%), // The color
      thickness: 1.8pt, // The width
      dash: "dashed", // The pattern
    )),
    edge(<v4>, <vv>, "->", bend: 40deg, stroke: (
      paint: red.darken(10%), // The color
      thickness: 1.8pt, // The width
      dash: "dashed", // The pattern
    )),
    edge(<vv>, <v3>, "->", bend: 40deg, stroke: (
      paint: red.darken(10%), // The color
      thickness: 1.8pt, // The width
      dash: "dashed", // The pattern
    )),
    edge(<v3>, <v1>, "->", bend: -40deg, stroke: (
      paint: red.darken(10%), // The color
      thickness: 1.8pt, // The width
      dash: "dashed", // The pattern
    )),
    edge(<v1>, <u>, "->", bend: 40deg, stroke: (
      paint: red.darken(10%), // The color
      thickness: 1.8pt, // The width
      dash: "dashed", // The pattern
    )),

    node(
      $P$,
      enclose: (<u>, <v>, (0, -0.5)),
      stroke: teal,
      fill: teal.lighten(90%),
    ),
  )
]
- If $v in V(C)$ we are done
#pagebreak()
#theorem(title: "Whitney's Theorem")[
  - $G$ - a connected graph with $v(G) >= 3$
  $
    G "has no cut-vxs" <=> "any 2 verticies of " G " lies on a common cycle".
  $


]
- Otherwise, we can divide $C$ into 2 arcs
#block(width: 70%)[
  #align(center)[
    $u ~> v' quad v` ~> u$\
    #diagram(
      node((0, 0), [$u$], name: <u>),
      node((1, 0), name: <v1>),
      node((2, 0), name: <v2>),
      node((3, 0), name: <v3>),
      node((4, 0), name: <v4>),
      node((5, 0), [$v'$], name: <vv>),
      node((6, 0), [$v$], name: <v>),

      // edge(<u>, <vv>, "~>"),
      edge(<vv>, <v>, "->"),

      edge(<u>, <v2>, "-", bend: 40deg, stroke: red + 2pt),
      edge(<v2>, <v4>, "-", bend: -40deg, stroke: red + 2pt),
      edge(<v4>, <vv>, "-", bend: 40deg, stroke: red + 2pt),
      edge(<vv>, <v3>, "-", bend: 40deg, stroke: blue + 2pt),
      edge(<v3>, <v1>, "-", bend: -40deg, stroke: blue + 2pt),
      edge(<v1>, <u>, "-", bend: 40deg, stroke: blue + 2pt),

      // node($P$, enclose: (<u>, <v>, (0, -0.7)), stroke: teal, fill: teal.lighten(90%)),
    )
  ]]
- As $G$ has no cut-vxs, $G-v'$ is still connected,
- There is a path from $v$ to a vertex $x$ that lies on one of the arcs)
- W.L.O.G, let $x in u ~> v'$ *take the shortest path from $v$ to any of the arcs!*.
- Then the cycle $u ~> x ~> v -> v' ~> u$ is a cycle, and contains both $u$ and $v$.

#place(
  top + left,
  dx: 17cm,
  dy: 6cm,
  figure(
    image("figures/L3i2.png", width: 40%),
  ),
)

= Consequences of Whitney's Theorem
== Graph blocks
#definition[
  A maximal connected subgraph of $G$ containing no cut-vxs is called a block of $G$
]

#diagram(
  spacing: (4cm, 3cm), // מגדיר את המרווח בין משבצות הרשת
  node-stroke: 1pt,
  node-fill: black,
  debug: 0,

  // --- צמתים (Nodes) ---
  // צד שמאל
  node((0, 0), name: <n1>, radius: 2pt),
  node((1, 0), name: <n2>, radius: 2pt),
  node((1.5, 0.8), name: <n3>, radius: 2pt),
  node((2, 0), name: <n4>, radius: 2pt),
  node((2, -0.8), name: <n5>, radius: 2pt),
  node((1, -0.8), name: <n6>, radius: 2pt),
  node((0.5, -1.2), name: <n7>, radius: 2pt),

  // מרכז
  node((3, 0), name: <n8>, radius: 2pt),
  node((3, -1), name: <n9>, radius: 2pt),
  node((4, 0), name: <n10>, radius: 2pt),

  // צד ימין
  node((5, 1), name: <n11>, radius: 2pt),
  node((5, -0.5), name: <n12>, radius: 2pt),
  node((6, 0.5), name: <n13>, radius: 2pt),
  node((6.5, -0.2), name: <n14>, radius: 2pt),
  node((6, -1.5), name: <n15>, radius: 2pt),
  node((5, -1.5), name: <n16>, radius: 2pt),

  edge(<n1>, <n2>),
  edge(<n2>, <n3>),
  edge(<n3>, <n4>),
  edge(<n4>, <n5>),
  edge(<n5>, <n6>),
  edge(<n6>, <n2>),
  edge(<n2>, <n4>),
  edge(<n6>, <n7>),
  edge(<n4>, <n8>),
  edge(<n8>, <n9>),
  edge(<n8>, <n10>),
  edge(<n10>, <n11>),
  edge(<n11>, <n12>),
  edge(<n12>, <n10>),
  edge(<n12>, <n13>),
  edge(<n13>, <n14>),
  edge(<n14>, <n12>),
  edge(<n12>, <n15>),
  edge(<n15>, <n16>),
  edge(<n16>, <n12>),

  {
    let blob(pts) = fletcher.edge(
      ..pts,
      stroke: (paint: red, dash: "dashed", thickness: 0.5pt),
      corner-radius: 15pt,
      label-side: center,
    )

    fletcher.node(
      (0.5, 0),
      enclose: (<n1>, <n2>),
      stroke: (paint: red, dash: "dashed"),
      corner-radius: 10pt,
      fill: none,
    )
    fletcher.node(
      (1.5, 0),
      enclose: (<n2>, <n3>, <n4>, <n5>, <n6>),
      stroke: (paint: red, dash: "dashed"),
      corner-radius: 10pt,
      fill: none,
    )
    fletcher.node(
      (3, -0.5),
      enclose: (<n8>, <n9>),
      stroke: (paint: red, dash: "dashed"),
      corner-radius: 10pt,
      fill: none,
    )
    fletcher.node(
      (3.5, 0),
      enclose: (<n8>, <n10>),
      stroke: (paint: red, dash: "dashed"),
      corner-radius: 10pt,
      fill: none,
    )
    fletcher.node(
      (4.7, 0.2),
      enclose: (<n10>, <n11>, <n12>),
      stroke: (paint: red, dash: "dashed"),
      corner-radius: 10pt,
      fill: none,
    )

    fletcher.node(
      (4.7, 0.2),
      enclose: (<n6>, <n7>),
      stroke: (paint: red, dash: "dashed"),
      corner-radius: 10pt,
      fill: none,
    )

    fletcher.node(
      (4.7, 0.2),
      enclose: (<n4>, <n8>),
      stroke: (paint: red, dash: "dashed"),
      corner-radius: 10pt,
      fill: none,
    )

    fletcher.node(
      (4.7, 0.2),
      enclose: (<n12>, <n13>, <n14>),
      stroke: (paint: red, dash: "dashed"),
      corner-radius: 10pt,
      fill: none,
    )

    fletcher.node(
      (4.7, 0.2),
      enclose: (<n12>, <n15>),
      stroke: (paint: red, dash: "dashed"),
      corner-radius: 10pt,
      fill: none,
    )
  },
)


== Consequences of Whitney's Theorem
#theorem(title: "Whitney's Theorem")[
  - $G$ - a connected graph with $v(G) >= 3$
  $
    G "has no cut-vxs" <=> "any 2 verticies of " G " lies on a common cycle".
  $
]
- Any two blocks of $G$ meet in at most one vertex.
- If two block do meet, their intersection vertex is a cut-vertex.
- The blocks of $G$ partition $E(G)$ (H.W.).
- Every cycle of $G$ lies in precisly one block of $G$(H.W.).

== Block tree
Given a graph $G$ define the following auxiliary graph:
#v(-10pt)
#table(
  columns: (1fr, 1.2fr),
  stroke: none,
  inset: 0pt,
  [‣ $B(G) := {B : B subset.eq G "is a block of G"}$], [‣ $C(G) := {v : v in V(G) "is a cut-vx of G"}$],
)


#v(-5pt)
Let $"BC"(G)$ denote the follwing graph
#v(-10pt)
#table(
  columns: (1fr, 1.2fr),
  stroke: none,
  inset: 0pt,
  [‣ The vertices of $"BC"(G)$ are $B(G) cap C(G)$],
  [‣ The edges of $"BC"(G)$ are #v(-10pt)
    $
      {{B,v} : B in B(G), v in C(G) "and" v in B}
    $],
)
#v(-10pt)
#theorem[
  if $G$ is connected then $"BC"(G)$ is a tree
]
#v(-20pt)
#figure(image("figures/blocktrees.png", width: 64%))

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
          (
            calc.cos(angle * i) * radius,
            calc.sin(angle * i) * radius,
          ),
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
          (
            calc.cos(angle * i) * radius,
            calc.sin(angle * i) * radius,
          ),
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
          (
            calc.cos(angle * i * 2) * radius,
            calc.sin(angle * i * 2) * radius,
          ),
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
      circle(
        (0, 0),
        radius: 0.15,
        fill: black,
        stroke: 0.5pt + black,
      )
    })
  ]
]


// == Definition I: Vertex Connectivity
// #definition[
//   A graph $G$ is called _k-connected_ if $kappa(G) >= k$
// ]

// #pause
// #block(width: 100%)[
//   #remark[
//     Other than the complete graph:
//     $
//       "A graph is "k"-connected" <=> "all of its vx-cuts are of size" >= k
//     $
//   ]
//   The complete graph has no vx-cuts of any size, this is where the 2nd part of the definition comes in
// ]
// #pause
// #remark[
//   If $G$ is $k$-connected then $G$ is also $k-1,k-2,k-3,...,1$-connected. \
//   But it can also be $k+1$ connected, we dont know if it is! \ All we know that any $k-1$ vertices removed from $G$ wont disconnect it.
// ]

// #place(
//   top + left,
//   dx: 16cm,
//   dy: 5.5cm,
//   align(center)[
//     #cetz-canvas({
//       import cetz.draw: *

//       circle((0.5, 2), radius: 0.15, fill: black, stroke: 0.5pt + black, name: "v1")
//       circle((0.5, -2), radius: 0.15, fill: black, stroke: 0.5pt + black, name: "v3")
//       circle((-5, 0), radius: 0.15, fill: black, stroke: 0.5pt + black, name: "v2")
//       circle((5, 0), radius: 0.15, fill: black, stroke: 0.5pt + black, name: "v4")

//       line("v1", "v2")
//       line("v2", "v3")
//       line("v3", "v4")
//       line("v4", "v1")

//       (pause,)

//       circle("v1", radius: 10pt, stroke: 3pt + red)
//       circle("v3", radius: 10pt, stroke: 3pt + red)
//     })

//     #place(
//       top + left,
//       dx: 16cm,
//       dy: 6.2cm,
//       [
//         $
//           kappa(G) = 2
//         $
//       ],
//     )
//   ],
// )



== Definition I

#definition[
  - $0 <= k in NN$
  - $G$ - graph with $v(G) > k$
  - If $G-X$ is conncted $forall X subset.eq V(G), |X| <= k-1$ then G is called _k-connected_
]

#align(center)[
  #cetz-canvas({
    import cetz.draw: *

    circle(
      (0.5, 2),
      radius: 0.15,
      fill: black,
      stroke: 0.5pt + black,
      name: "v1",
    )
    circle(
      (0.5, -2),
      radius: 0.15,
      fill: black,
      stroke: 0.5pt + black,
      name: "v3",
    )
    circle(
      (-5, 0),
      radius: 0.15,
      fill: black,
      stroke: 0.5pt + black,
      name: "v2",
    )
    circle(
      (5, 0),
      radius: 0.15,
      fill: black,
      stroke: 0.5pt + black,
      name: "v4",
    )

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
#pause
- To be $k$-connected, $v(G) > k$ must hold
#pause
- What about $K_1$?
#pause
- We assume it is connected
#pause
- But our definition $K_1$ is #text(red)[not] connected!#pause
- We'll fix this later

#pagebreak()

#definition[
  The largest $k in ZZ_(>=0)$ for which $G$ is $k$-connected is denoted by $kappa(G)$
]

- All disconnected graphs have $kappa(G) = 0$ #pause
- All connected graphs (but $K_1$) are *1-connected*#pause
- $kappa(G) >= 1$#pause
- $kappa(K_1) = 0$ #pause
- Cycles with 3 or more vertecies are *2-connected* #pause
- $kappa(K_r) = r-1$#pause

Again $kappa(K_1) = 0$, is annoying, can we fix it?

== Definition II: Path connectivity
#definition[
  - $G$ a graph
  - $A,B subset.eq V(G)$
  - let $rho_G (A,B) :=$ the number of vx-disjoint $(A,B)$-paths
]

#columns(3)[
  #diagram(
    node-stroke: 0.6pt,
    node(
      $A$,
      enclose: ((1, 1), (1, 2)), // a node spanning multiple centers
      inset: 10pt,
      stroke: teal,
      fill: teal.lighten(90%),
      name: <A>,
    ),

    node(
      $B$,
      enclose: ((2, 1), (2, 2)), // a node spanning multiple centers
      inset: 10pt,
      stroke: teal,
      fill: teal.lighten(90%),
      name: <B>,
    ),

    edge((1, 1), "r", "--", snap-to: (<A>, <B>)),
    edge((1, 1.25), "r", "--", snap-to: (<A>, <B>)),
    edge((1, 1.5), "r", "--", snap-to: (<A>, <B>)),
    edge((1, 1.75), "r", "--", snap-to: (<A>, <B>)),
    edge((1, 2), "r", "--", snap-to: (<A>, <B>)),
  )
  #colbreak()

  #diagram(
    node-stroke: 0.6pt,
    node(
      (0, 0),
      name: <A>,
    ),

    node(
      (3, 0),
      name: <B>,
    ),

    for d in (-20, -10, 0, 10, 20) {
      edge(<A>, <B>, "--", bend: d * 2 * 1deg)
    },
  )\
  \
  Here $|A| = |B| = 1$

  #colbreak()

  #cetz.canvas({
    import cetz.draw: *

    circle((-0.75, 0), radius: 1.25)
    circle((0.75, 0), radius: 1.25)

    circle((0, 0), radius: 2pt, fill: black)
    circle((0, 0.4), radius: 2pt, fill: black)
    circle((0, -0.4), radius: 2pt, fill: black)
  })
  $A cap B != emptyset$ also can happen
]

#remark[
  Vertices in $A$ and $B$ counts toward the vertices of the paths. \
  If $|A|=1$ or $|B|=1$ then we count the number of paths from the neibours of $A$ or $B$ respectively.
]


== Definition II: Path connectivity
// #definition[
//   - $G$ a graph
//   - $A,B subset.eq V(G)$
//   - let $rho_G (A,B) :=$ the number of vx-disjoint $(A,B)$-paths
// ]

#definition(title: "Path connectivity")[
  $G$ is _k-connected_ if $rho_G (u,v) >= k " "forall {u,v} in binom(V(G), 2)$
]

#definition(title: "Vertex connectivity")[
  Graph $G$ with $v(G) > k > 1$ is _k-connected_ if for every $X subset.eq V(G)$ with $|X| <= k-1$ the graph $G-X$ is connected.
  If $v(G)=1$ then $G$ is _1-connected_.
]

#pause
#align(horizon + center)[
  *So whats better: vertex connectivity or path connectivity ?*
  #pause

  #text(
    weight: "bold",
    fill: green.darken(25%),
  )[Menger's theorem tells us that they are the same!]

]

== Our definition
#definition[
  The minimum size of a vx set $X$ such that $G-X$ is disconnected or has a single vx is called the _vx-connectivity_ of $G$ and is denoted by $kappa(G)$
]
#definition[
  A graph $G$ is called _k-connected_ if $kappa(G) >= k$
]

#remark[
  Other than the complete graph:
  $
    "A graph is "k"-connected" <=> "all of its vx-cuts are of size" >= k
  $
]
The complete graph has no vx-cuts of any size, this is where the 2nd part of the definition comes in

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
- $kappa_G (A,B) >= rho_G (A,B)$ is trivial #place(dx: 150%, dy: -300%)[
    #diagram(
      node-stroke: 0.6pt,
      node(
        $A$,
        enclose: ((1, 1), (1, 2)), // a node spanning multiple centers
        inset: 10pt,
        stroke: teal,
        fill: teal.lighten(90%),
        name: <A>,
      ),

      node(
        $B$,
        enclose: ((2, 1), (2, 2)), // a node spanning multiple centers
        inset: 10pt,
        stroke: teal,
        fill: teal.lighten(90%),
        name: <B>,
      ),

      edge((1, 1), "r", "--@--", snap-to: (<A>, <B>)),
      edge((1, 1.25), "r", "--@--", snap-to: (<A>, <B>)),
      edge((1, 1.5), "r", "--@--", snap-to: (<A>, <B>)),
      edge((1, 1.75), "r", "--@--", snap-to: (<A>, <B>)),
      edge((1, 2), "r", "@-@", snap-to: (<A>, <B>)),
    )
  ]
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
#columns(3)[
  #set align(center)
  #diagram(
    node((0, 1), $x$, name: <x>),
    node((2, 1), $y$, name: <y>),

    edge(<x>, <y>, stroke: red),
    for i in (1, 2, 3) {
      node((rel: (-i / 6, 1), to: <x>))
      edge(<x>)
    },

    for i in (1, 2, 3) {
      node((rel: (i / 6, 1), to: <y>))
      edge(<y>)
    },

    node((1, 0), name: <top>),
    edge(<x>),
    edge(<y>),
  )
  #colbreak()
  #diagram(
    node((1, 1), $x y$, name: <xy>),

    edge(<xy>, <xy>, bend: -130deg, loop-angle: 0deg),
    for i in (1, 2, 3) {
      node((rel: (-i / 6, 1), to: <xy>))
      edge(<xy>)
    },

    for i in (1, 2, 3) {
      node((rel: (i / 6, 1), to: <xy>))
      edge(<xy>)
    },

    node((1, 0), name: <top>),
    edge(<xy>, bend: 20deg),
    edge(<xy>, bend: -20deg),
  )
  #colbreak()
  #diagram(
    node((1, 1), $x y$, name: <xy>),
    for i in (1, 2, 3) {
      node((rel: (-i / 6, 1), to: <xy>))
      edge(<xy>)
    },

    for i in (1, 2, 3) {
      node((rel: (i / 6, 1), to: <xy>))
      edge(<xy>)
    },

    node((1, 0), name: <top>),
    edge(<xy>),
  )
]
- Denote by $G slash e$ the graph resualting from contracting $e$

== Menger's theorem
#theorem(title: [Menger's theorem])[
  Let $G$ be a graph and let $A,B subset.eq V(G)$ non empty.
  Then
  $
    underbrace(kappa_G (A,B) = rho_G (A,B), #[The goal is to show $<=$])
  $
]
- Set $kappa := kappa_G (A,B)$ and $rho:= rho_G (A,B)$
- Proof by induction on $e(G)$
- If $e(G) = 0$ the graph is disconnected
  - $rho = |A cap B| = kappa$

#pagebreak()

#table(
  columns: (1fr, 1fr),
  align: horizon,
  stroke: none,
  [
    #goal[
      Show that $kappa_(G)(A,B) <= rho_(G)(A,B).$
    ]
  ],
  [ #block(width: 100%, stroke: 1pt, radius: 3pt, inset: 20pt, fill: yellow)[
    #set text(size: 0.8em)
    *I.H:* For every graph $G'$ with $e(G') < e(G)$ and every $A',B' subset.eq V(G')$ non empty, we have $kappa_(G')(A',B') <= rho_(G')(A',B')$
  ]],
)
// #theorem(title: [Menger's theorem])[
//   Let $G$ be a graph and let $A,B subset.eq V(G)$ non empty.
//   Then
//   $
//     underbrace(kappa_G (A,B) = rho_G (A,B), #[The goal is to show $<=$])
//   $
// ]
- Assume $e(G) > 0$, let $e=x y in E(G)$ be an arbitrary edge
- $G slash e$ satisfies the I.H. but $A$ and $B$ are not defined consistently in $G \\ e$. #text(size: 0.8em, weight: "bold", fill: red)[(What if x or y is in A or B?)].

  Define $A_e subset.eq V(G slash e)$ as follows
  - If $x,y in.not A$, then $A_e := A$
  - if $x in A$,$y in.not A$, then $A_e := (A \\ {x}) cup {V_e}$
  - if $x in.not A$,$y in A$, then $A_e := (A \\ {x}) cup {V_e}$
  - if $x,y in A$, then $A_e := (A \\ {x,y }) cup {V_e}$

- Define $B_e$ in the same manner.

#pagebreak()
*Case 1:* Suppose that $G slash e$ has $kappa$ vx-disjoint $(A_e,B_e)$-paths
- *Goal:* Show that every such path exists in $G$.
  - Any path not containing $v_e$ exists in $G$.
  - suppose that there is a path in the linkage containing $v_e$.

$x y$ can be expanded in the path

#diagram(
  $edge("--") &in N_G (x) edge("-") & x edge("-") & y edge("-") & in N_G (y) edge("--")$,
)
#diagram(
  $edge("--") &in N_G (y) edge("-") & y edge("-") & x edge("-") & in N_G (x) edge("--")$,
)

$x y$ cannot be expanded in the path

#diagram(
  $edge("--") &in N_G (y) edge("-") & x edge("-") & y edge("-") & in N_G (y) edge("--")$,
)
#diagram(
  $edge("--") &in N_G (x) edge("-") & x edge("-") & y edge("-") & in N_G (x) edge("--")$,
)

- In the second case, only one of the vertices lie on the original \ path.

#place(
  top + left,
  dx: 17.5cm,
  dy: 1cm,
  figure(
    image("figures/L4i1.png", width: 40%),
  ),
)


== Menger's theorem
#[
  #set text(size: 0.9em)
  #claim[
    If $S$ is vx-disconnector of $(A_e,B_e)$ in $G slash e$ then
    a vx-disconnector of $(A,B)$ in $G$ exists where
    $
      S_G subset.eq (S \\ v_e) cup {x,y}.
    $
    // is a vx-disconnector of $(A,B)$ in $G$.
  ]
  // #text(size: 0.8em, weight: "bold", fill: red)[Note that if $v_e in S$ then $(S \\ v_e) cup x$ or $(S \\ v_e) cup y$ might result in a vx-disconnector but it will have size $=|S|$. ]
  *Case 2:* $rho_(G \\ e)(A_e, B_e) < kappa $
  - By the I.H $kappa_(G\\e)(A_e, B_e) < kappa$.
  - Let $S$ be a vx-disconnector of $(A_e,B_e)$.
  - $v_e in S$ must hold:
    - If $v_e in.not S$, then $S$ is also a vx-disconnector of $(A,B)$ in $G$ and has size $|S| < kappa$.
  - Any $(A_e,B_e)$-vx-disconnector in $G slash e$ is of size $kappa - 1$.
    - Otherwise $|S_G| <= |S|+1< kappa-1+1=kappa$.
]
#place(
  top + left,
  dx: 14cm,
  dy: 5.5cm,
  align(center)[
    #cetz-canvas({
      import cetz.draw: *
      import cetz.matrix: ident

      scale(0.7)

      rect((0, 0), (1, 3), fill: gray.lighten(70%), radius: 0.2)
      rect(
        (2, 0.5),
        (3, 2.5),
        fill: red.lighten(70%),
        radius: 0.2,
        name: "middle",
      )
      rect((4, 0), (5, 3), fill: gray.lighten(70%), radius: 0.2)

      cetz.decorations.wave(
        line((0.5, 0.2), (2.25, 1)),
        segments: 2,
        amplitude: 0.1,
      )
      cetz.decorations.wave(
        line((0.5, 1), (2.25, 1.5)),
        segments: 2,
        amplitude: 0.1,
      )
      cetz.decorations.wave(
        line((0.5, 2), (2.25, 2)),
        segments: 2,
        amplitude: 0.1,
      )
      cetz.decorations.wave(
        line((0.5, 2.8), (2.25, 2.2)),
        segments: 2,
        amplitude: 0.1,
      )

      content("middle", [$v_e$], anchor: "south")
      circle("middle", fill: black, radius: 1pt, anchor: "north")

      cetz.decorations.wave(
        line((2.75, 1), (4.5, 0.2)),
        segments: 2,
        amplitude: 0.1,
      )
      cetz.decorations.wave(
        line((2.75, 1.5), (4.5, 1)),
        segments: 2,
        amplitude: 0.1,
      )
      cetz.decorations.wave(
        line((2.75, 2), (4.5, 2)),
        segments: 2,
        amplitude: 0.1,
      )
      cetz.decorations.wave(
        line((2.75, 2.2), (4.5, 2.8)),
        segments: 2,
        amplitude: 0.1,
      )

      translate((10, 2.5))

      rect((0, 0), (1, 3), fill: gray.lighten(70%), radius: 0.2)
      rect(
        (2, 0.5),
        (3, 2.5),
        fill: red.lighten(70%),
        radius: 0.2,
        name: "middle",
      )
      rect((4, 0), (5, 3), fill: gray.lighten(70%), radius: 0.2)

      cetz.decorations.wave(
        line((0.5, 0.2), (2.25, 1)),
        segments: 2,
        amplitude: 0.1,
      )
      cetz.decorations.wave(
        line((0.5, 1), (2.25, 1.5)),
        segments: 2,
        amplitude: 0.1,
      )
      cetz.decorations.wave(
        line((0.5, 2), (2.25, 2)),
        segments: 2,
        amplitude: 0.1,
      )
      cetz.decorations.wave(
        line((0.5, 2.8), (2.25, 2.2)),
        segments: 2,
        amplitude: 0.1,
      )

      content("middle", [$x$], anchor: "north", name: "x")
      content(
        (rel: "middle.north", to: (0, 1)),
        [$y$],
        anchor: "south",
        name: "y",
      )
      circle(
        "middle",
        fill: black,
        radius: 1pt,
        anchor: "north",
        name: "x",
      )
      circle(
        "y.south",
        fill: black,
        radius: 1pt,
        anchor: "north",
        name: "y",
      )
      line("x", "y")
      cetz.decorations.wave(
        line((2.75, 1), (4.5, 0.2)),
        segments: 2,
        amplitude: 0.1,
      )
      cetz.decorations.wave(
        line((2.75, 1.5), (4.5, 1)),
        segments: 2,
        amplitude: 0.1,
      )
      cetz.decorations.wave(
        line((2.75, 2), (4.5, 2)),
        segments: 2,
        amplitude: 0.1,
      )
      cetz.decorations.wave(
        line((2.75, 2.2), (4.5, 2.8)),
        segments: 2,
        amplitude: 0.1,
      )
      translate((0, -5))

      rect((0, 0), (1, 3), fill: gray.lighten(70%), radius: 0.2)
      rect(
        (2, 0.5),
        (3, 2.5),
        fill: red.lighten(70%),
        radius: 0.2,
        name: "middle",
      )
      rect((4, 0), (5, 3), fill: gray.lighten(70%), radius: 0.2)

      cetz.decorations.wave(
        line((0.5, 0.2), (2.25, 1)),
        segments: 2,
        amplitude: 0.1,
      )
      cetz.decorations.wave(
        line((0.5, 1), (2.25, 1.5)),
        segments: 2,
        amplitude: 0.1,
      )
      cetz.decorations.wave(
        line((0.5, 2), (2.25, 2)),
        segments: 2,
        amplitude: 0.1,
      )
      cetz.decorations.wave(
        line((0.5, 2.8), (2.25, 2.2)),
        segments: 2,
        amplitude: 0.1,
      )

      circle(
        (rel: "middle", to: (0, 0.5)),
        fill: black,
        radius: 1pt,
        anchor: "north",
        name: "y",
      )
      circle(
        (rel: "middle", to: (0, -0.5)),
        fill: black,
        radius: 1pt,
        anchor: "north",
        name: "x",
      )
      content("y", [$y$], anchor: "south")
      content("x", [$x$], anchor: "north")
      line("x", "y")
      cetz.decorations.wave(
        line((2.75, 1), (4.5, 0.2)),
        segments: 2,
        amplitude: 0.1,
      )
      cetz.decorations.wave(
        line((2.75, 1.5), (4.5, 1)),
        segments: 2,
        amplitude: 0.1,
      )
      cetz.decorations.wave(
        line((2.75, 2), (4.5, 2)),
        segments: 2,
        amplitude: 0.1,
      )
      cetz.decorations.wave(
        line((2.75, 2.2), (4.5, 2.8)),
        segments: 2,
        amplitude: 0.1,
      )

      translate((-10, 2.5))

      line((5.5, 2), (9.5, 4.5), mark: (end: ">"))
      line((5.5, 2), (9.5, -1), mark: (end: ">"))
    })
  ],
)

#pagebreak()
#v(20pt)
We are now in this position:
- The edge $x y$ lies inside the minimum vx-disconnector of $(A,B)$ in $G$.
// - $S_G := (A,B)$-vx-disconnector (Maybe $S_G=A$ or $S_G=B$)
// - $|S_G| = kappa$
// - $S_G$ spans $e$
#align(center)[
  #cetz-canvas({
    import cetz.draw: *

    rect((0, 0), (1, 3), fill: gray.lighten(70%), radius: 0.2)
    rect(
      (2, 0.5),
      (3, 2.5),
      fill: red.lighten(70%),
      radius: 0.2,
      name: "middle",
    )
    rect((4, 0), (5, 3), fill: gray.lighten(70%), radius: 0.2)

    cetz.decorations.wave(
      line((0.5, 0.2), (2.25, 1)),
      segments: 2,
      amplitude: 0.1,
    )
    cetz.decorations.wave(
      line((0.5, 1), (2.25, 1.5)),
      segments: 2,
      amplitude: 0.1,
    )
    cetz.decorations.wave(
      line((0.5, 2), (2.25, 2)),
      segments: 2,
      amplitude: 0.1,
    )
    cetz.decorations.wave(
      line((0.5, 2.8), (2.25, 2.2)),
      segments: 2,
      amplitude: 0.1,
    )

    circle(
      (rel: "middle", to: (0, 0.5)),
      fill: black,
      radius: 1pt,
      anchor: "north",
      name: "y",
    )
    circle(
      (rel: "middle", to: (0, -0.5)),
      fill: black,
      radius: 1pt,
      anchor: "north",
      name: "x",
    )
    content("y", [$y$], anchor: "south")
    content("x", [$x$], anchor: "north")
    line("x", "y")
    cetz.decorations.wave(
      line((2.75, 1), (4.5, 0.2)),
      segments: 2,
      amplitude: 0.1,
    )
    cetz.decorations.wave(
      line((2.75, 1.5), (4.5, 1)),
      segments: 2,
      amplitude: 0.1,
    )
    cetz.decorations.wave(
      line((2.75, 2), (4.5, 2)),
      segments: 2,
      amplitude: 0.1,
    )
    cetz.decorations.wave(
      line((2.75, 2.2), (4.5, 2.8)),
      segments: 2,
      amplitude: 0.1,
    )
  })
]

#pause
// #claim[
//   If $S_G$ is a vx-disconnector of $(A,B)$. Then, any vx-disconnector of $(A,S_G)$
//   is also a vx-disconnector of $(A,B)$ and any vx-disconnector of $(S_G,B)$ is also a vx-disconnector of $(A,B)$.
// ]
*Observation:*
The size of the least vx-disconnector of $(A,S)$ and $(S,B)$ is at least $kappa$.

#place(
  top + center,
  dx: 0cm,
  dy: 55%,
  figure(
    image("figures/L4i3.png", width: 70%),
  ),
)

#pagebreak()

#place(
  top + center,
  dx: 0cm,
  dy: 3.5cm,
  align(center)[
    #cetz-canvas({
      import cetz.draw: *

      rect((0, 0), (1, 3), fill: gray.lighten(70%), radius: 0.2)
      rect(
        (2, 0.5),
        (3, 2.5),
        fill: red.lighten(70%),
        radius: 0.2,
        name: "middle",
      )
      rect((4, 0), (5, 3), fill: gray.lighten(70%), radius: 0.2)

      cetz.decorations.wave(
        line((0.5, 0.2), (2.25, 1)),
        segments: 2,
        amplitude: 0.1,
      )
      cetz.decorations.wave(
        line((0.5, 1), (2.25, 1.5)),
        segments: 2,
        amplitude: 0.1,
      )
      cetz.decorations.wave(
        line((0.5, 2), (2.25, 2)),
        segments: 2,
        amplitude: 0.1,
      )
      cetz.decorations.wave(
        line((0.5, 2.8), (2.25, 2.2)),
        segments: 2,
        amplitude: 0.1,
      )

      circle(
        (rel: "middle", to: (0, 0.5)),
        fill: black,
        radius: 1pt,
        anchor: "north",
        name: "y",
      )
      circle(
        (rel: "middle", to: (0, -0.5)),
        fill: black,
        radius: 1pt,
        anchor: "north",
        name: "x",
      )
      content("y", [$y$], anchor: "south")
      content("x", [$x$], anchor: "north")
      // line("x", "y")
      cetz.decorations.wave(
        line((2.75, 1), (4.5, 0.2)),
        segments: 2,
        amplitude: 0.1,
      )
      cetz.decorations.wave(
        line((2.75, 1.5), (4.5, 1)),
        segments: 2,
        amplitude: 0.1,
      )
      cetz.decorations.wave(
        line((2.75, 2), (4.5, 2)),
        segments: 2,
        amplitude: 0.1,
      )
      cetz.decorations.wave(
        line((2.75, 2.2), (4.5, 2.8)),
        segments: 2,
        amplitude: 0.1,
      )
    })
  ],
)

- Look at $G - e$: #text(size: 0.8em, weight: "bold", fill: red)[(removing the edge e rather than contracting it!)]
- By the induction hypothesis.
$
  rho_(G-e) (A, S_G) = kappa_(G-e) (A, S_G) >= kappa quad "and" quad rho_(G-e) (A, S_G) = kappa_(G-e) (S_G, B) >= kappa
$

#v(100pt)
- There must exists $kappa$ vx-disjoint $(A,S_G)$-paths and $kappa$ vx-disjoint $(S_G,B)$-paths in $G-e$.
- For any path $a arrow.r.squiggly s$ and $s arrow.r.squiggly b$,
  where $a in A, s in S, b in B$.
  - The path $a arrow.r.squiggly s arrow.r.squiggly b$ is vx-disjoint $(A,B)$-path in $G$.

#place(
  top + center,
  dx: 0cm,
  dy: 72%,
  figure(
    image("figures/L4i4.png", width: 40%),
  ),
)

= Implication of Menger's theorem
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

#align(center)[
  #diagram(
    node-stroke: 1pt,
    node-fill: black,
    debug: 0,
    node(
      enclose: ((2, -1), (2, 1)),
      inset: 10pt,
      stroke: teal,
      fill: teal.lighten(90%),
      name: <B>,
    ),
    node((0, 0), radius: 2pt, name: <x>),

    edge(<x>, (2, -1), "--"),
    edge(<x>, (2, -0.5), "--"),
    edge(<x>, (2, 0), "--"),
    edge(<x>, (2, 0.5), "--"),
    edge(<x>, (2, 1), "--"),
  )
]

#lemma(title: "Fan Lemma H.W")[
  - $G$ - $k$-connected graph
  - $x in V(G)$ and $B subset.eq V(G) \\ {x }$
  Then $G$ has an $(x,B)$-fan if size $min{k,|B|}$
]



== Dirac's theorem


#alternatives[
  #theorem(title: "Dirac's Theorem")[
    - $2 <= k in NN$
    - $G$ - $k$-connected graph
    - $S subset.eq V(G)$ such that $2 <= |S| <= k$
    Then $G$ contains a cycle constaining $S$
  ]
  - By induction on $k$.
  - for $k=2$, the claim holds by whitney's theorem.

  #[
    #set text(size: 0.8em)
    #theorem(title: "Whitney's Theorem")[
      - $G$ - a connected graph with $v(G) >= 3$
      $
        G "has no cut-vxs" <=> "any 2 verticies of " G " lies on a common cycle".
      $
    ]
  ]
][
  #place(
    top + left,
    dx: 55%,
    dy: 0cm,
    block(
      width: 49%,
    )[
      #set text(size: 0.9em)
      #theorem(title: "Dirac's Theorem")[
        - $2 <= k in NN$
        - $G$ - $k$-connected graph
        - $S subset.eq V(G)$ such that $2 <= |S| <= k$
        Then $G$ contains a cycle constaining $S$
      ]
    ],
  )

  #block(
    width: 50%,
  )[
    #block(width: 100%, stroke: 1pt, radius: 3pt, inset: 20pt, fill: yellow)[
      #set text(size: 0.8em)
      *I.H:* If $G$ is a $k-1$ connected graph then for every $S subset.eq V(G)$ with $|S| <= k-1$ there is a cycle containing $S$.
    ]
    #set text(size: 1em)
    #v(-10pt)
    - Assume $k>=3$
      - Let $x in S$ be arbitrary and set $T:= S\\{x}$.
    - |T| <= k-1.
    - $G$ is $k$-connected so $G-x$ is at least $k-1$ connected.
      - By the I.H. there is a cycle $C$ containing $T$.
    - let $F$ be an $(x,C)$-fan in $G$ of size $min{k, v(C)}$.
    - $T$ partitions $C$ into $k-1$ arcs.
    - At least two of the paths in the fan land in the same arc on $C$.
    
  ]

  #place(
    top + left,
    dx: 62%,
    dy: 5.2cm,
    figure(
      image("figures/L4i5.png", width: 35%),
    ),
  )
]

