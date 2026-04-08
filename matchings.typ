#import "settings/mstyle.typ": *
#import algorithmic: algorithm-figure, style-algorithm
#show: style-algorithm



#show: conf.with(handout: true, subtitle: [Matching in graphs])

#title-slide()

= Matchings in Graphs

== Matching in graphs

#set align(horizon)

- The matching problem is something that students face from the first time that they encounter graph theory. #pause
- Suppose that you have a group of $n$ people, that you want to divide into pairs, how would you go about it? Is is possible that every person finds a pair? #pause
- What if some people don't want to be paired together, can you do it then? #pause

A common approach is to model this problem with a graph G.
Each vertex represents a person, and an edge between two vertices indicates that those two people can be paired together.

#pagebreak()
#set align(horizon)
For a graph $G$, two edges $e_1, e_2 subset.eq E(G)$ are called _indepedent_ if there is no common vertex between them.

#align(center)[
  #columns(2, [
    #cetz.canvas({
      import cetz.draw: *
      circle((0, 0), radius: 5pt, fill: black, name: "p1")
      circle((0, 5), radius: 5pt, fill: black, name: "p2")
      line("p1", "p2")
      circle((1, 5), radius: 5pt, fill: black, name: "p3")
      circle((1, 0), radius: 5pt, fill: black, name: "p4")
      line("p3", "p4")
      content((0.5, -1), [indepedent], anchor: "north")
    })
    #colbreak()
    #cetz.canvas({
      import cetz.draw: *
      circle((0.5, 5), radius: 5pt, fill: black, name: "p1")
      circle((0, 0), radius: 5pt, fill: black, name: "p2")
      circle((1, 0), radius: 5pt, fill: black, name: "p3")
      line("p1", "p2")
      line("p1", "p3")
      content((0.5, -1), [not indepedent], anchor: "north")
      // content(("p1","south"), [independant],anchor: "north")
    })
  ])
]


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
    ],
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

#align(center)[
  #cetz-canvas({
    import cetz.draw: *
    circle((0, 0), radius: 5pt, fill: black, name: "p1")
    circle((5, 0), radius: 5pt, fill: black, name: "p2")
    circle((0, 5), radius: 5pt, fill: black, name: "p3")
    circle((5, 5), radius: 5pt, fill: black, name: "p4")
    circle((10, 5), radius: 5pt, fill: black, name: "p5")

    for value in range(1, 5) {
      line("p" + str(value), "p" + str(value + 1))
    }

    (pause,)

    circle("p2", radius: 10pt, stroke: 3pt + red)
    circle("p4", radius: 10pt, stroke: 3pt + red)
  })
]
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
- $nu(G) :=$ size of _max_ matching in $G$.
- $tau(G) :=$ size of _min_ vx-cover in $G$.


#table(
  columns: (1fr, 1fr),
  stroke: none,
  [
    Trivially, $tau(G) >= nu(G)$
    #figure(
      image("figures/L2i6.jpeg", width: 60%),
    )
    Any min-vc must "invest" at least 1 \
    vertex for each edge in the matching.
  ],
  [
    #pause
    $tau(G) > nu(G)$ possible
    #align(center)[
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

        for i in range(0, 4) {
          line("v" + str(i), "v" + str(i + 1))
        }
        line("v0", "v4")

        circle("v1", radius: 10pt, stroke: 3pt + red)
        circle("v2", radius: 10pt, stroke: 3pt + red)
        circle("v4", radius: 10pt, stroke: 3pt + red)
      })
    ]
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
  // #set align(horizon)
  #v(70pt)
  #theorem(title: "König")[$tau(G) = nu(G)$, whenever $G$ is bipartite.]

  // #figure(image("figures/L2i8.png", width: 40%))
  // ]

  #place(
    top + left,
    dx: 17cm,
    dy: 5cm,
    figure(image("figures/L2i8.png", width: 38%)),
  )

  #place(
    top + left,
    dx: 0cm,
    dy: 3cm,

    block(width: 60%)[
      #v(100pt)
      #set text(size: 0.9em)
        - $nu(G) :=$ the number of edges in a maximum matching of $G$.
        #v(-5pt)
        - $tau(G) :=$ the number of vertices in a minimum vertex cover of $G$.

    ],
  )
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
    ],
  )

  #v(10pt)
  $
    N_G (u) & := { v in V(G) : u v in E(G)} \
    N_G (S) & := { v in V(G) : exists u in S : v in N_G (u)}
  $

  #pause
  #[
    #set align(center)
    #show math.equation: set text(weight: "bold")

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
      columns: (110pt, 250pt, 0pt, 250pt),
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
      ],
    )
  ]

  #[
    #set align(center)
    #show math.equation: set text(weight: "bold")

    #text(weight: "bold", fill: rgb("#d4635b"))[
      If $|N_G (S) | >= |S|$, $forall S in A$, then we say that $A$ satisfies the Hall-Condition!
    ]
  ]
]

== Main Messsage
#[
  #diagram(
    node-stroke: luma(20%),
    edge-corner-radius: 10pt,
    spacing: 1pt,
    mark-scale: 150%,

    node((-25, 70), [], stroke: none),
    node((140, 100), [*König's Theorem*], stroke: none),
    node((120, 150), [*Hall's Theorem*], stroke: none),
    node((160, 150), [*Frobenius Theorem*], stroke: none),

    edge((140, 100), (120, 150), "<=>"),
    edge((140, 100), (160, 150), "<=>"),
    edge((160, 150), (120, 150), "<=>"),
  )
]
== Hall $=>$ Frobenius
We need to prove:
#theorem(title: "Frobenius")[Let $G := (A union.dot B, E)$ be bipartite
  #align(center)[
    $G$ has a perfect matching
    $arrow.r.l.double.long$
    $|A| = |B|$ and
    $A$ or $B$ satisfies
    the Hall-Condition
  ]

]

#grid(
  columns: (50%, 50%),
  rows: auto,
  gutter: 15pt,
  [
    We have:
    #theorem(title: "Hall")[Let $G:=(A union.dot B, E)$ be a bipartite graph.
      Then,
      $
        A arrow.r.turn B #h(20pt) arrow.r.l.long.double #h(20pt)
        |N_G (S)| >= |S|, forall S subset.eq A.
      $
    ]
  ],
  [
    #pause
    #set text(size: 16pt)
    $arrow.long.double.r$
    - If $G$ has a perfect matching then by definition $A arrow.r.turn B$
    - By defenition of  $A arrow.r.turn B$, $|A| <= |B|$.
    - By Halls theorem $A$ satisfies the halls condition
    - By the same argument we can say the same thing about $B$

    $arrow.long.double.l$
    - By the Hall Theorem we have $A arrow.r.turn B$
    - We have a matching $M$ satisfying $|M| = |A|$
    - since $|A|= |B|$ it follows that $M$ is a perfect matching.
  ],
)

#pagebreak()
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
    node((-25, 70), [], stroke: none),
    node((140, 100), [*König's Theorem*], stroke: none),
    node((120, 150), [*Hall's Theorem*], stroke: none),
    node((160, 150), [*Frobenius Theorem*], stroke: none),

    edge((140, 100), (120, 150), "<=>"),
    edge((140, 100), (160, 150), "<=>"),
    edge((160, 150), (120, 150), "<=>"),
  )
]

#[
  Frobenius Theorem $arrow.long.r.double$ Konig's Theorem: \
  #h(100pt) Since $tau(G) >= nu(G)$ is known in general, it remains to show $tau(G) <= nu(G)$. \ #h(100pt)
  if $G$ has a perfect matching $M$ so that $nu(G)=n/2$ and $|A|=n/2$. We may take $A$ as 
  \ #h(100pt) a vertex cover of $G$
  and we are done.\ #h(100pt)  #[#set text(size: 0.85em, fill: red.darken(20%), weight: "bold")
  Or in general we can pick 1 vertex per edges of $M$ in a smart way.] \ #h(100pt) 
  What if $G$ has no _perfect matching_? 

  *hint*: The idea is to "remove" unmached vertices untill  we are left with a subgraph having a perfect matching. Then, think what can be done about the removed vertices.

  *the rest is left for the reader as an exercise*
]

== Hall $==>$ König.
#v(-13pt)
#[
  #set align(top)
  #set text(size: 0.8em)
  #table(
    columns: (1fr, 1fr),
    stroke: none,
    align: horizon,
    [
      #theorem(title: "König")[$tau(G) = nu(G)$, whenever $G$ is bipartite.]
    ],
    [
      #v(5pt)
      #theorem(title: "Hall")[Let $G:=(A union.dot B, E)$ be a bipartite graph.
        Then,
        $
          A arrow.r.turn B #h(20pt) arrow.r.l.long.double #h(20pt)
          |N_G (S)| >= |S|, forall S subset.eq A.
        $
      ]
    ],
  )
]
#[
  // #v(-30pt)
  #set text(size: 0.9em)
  #block(inset: (left: 10pt, top: -10pt))[
    - Let $G:= (A union.dot B, E)$ be bipartite, it remains to prove that $tau(G) <= nu(G)$
    - *We seek to prove that $G$ has a matching of size at least the minimum VC of $G$*
    - Let $C subset.eq V(G)$ be #bt(red.darken(10%))[min-vc] of $G$ and define
      #grid(
        columns: (350pt, 400pt),
        stroke: none,
        inset: 0pt,
        [
          $
            #text(fill: green)[$H & := G(C inter A, B \\ C)$] \
            #text(fill: blue)[$H' & := G(C inter B, A \\ C)$]
          $
          #place(
            top + left,
            dx: 15cm,
            // dy: 5.5cm,
            cetz-canvas({
              import cetz.draw: *

              for i in range(1, 7) {
                circle((0, -i), fill: black, radius: 2pt, name: "l" + str(i))
                circle((5, -i), fill: black, radius: 2pt, name: "r" + str(i))
              }

              rect-around("l1", "l6", padding: (0.4, 0.4, 0.4, 2), radius: 0.2)
              rect-around("r1", "r6", padding: (0.4, 2, 0.4, 0.3), radius: 0.2)

              rect-around("l1", "l3", padding: (0.2, 0.2, 0.2, 1.8), radius: 0.1, fill: orange.lighten(70%))
              content((rel: (-1, 0), "to": "l2"), [$A cap C$])
              rect-around("l4", "l6", padding: (0.2, 0.2, 0.2, 1.8), radius: 0.1, fill: purple.lighten(70%))
              content((rel: (-1, 0), "to": "l5"), [$A \\ C$])

              rect-around("r1", "r3", padding: (0.2, 1.8, 0.2, 0.2), radius: 0.1, fill: orange.lighten(70%))
              content((rel: (1, 0), "to": "r2"), [$B cap C$])
              rect-around("r4", "r6", padding: (0.2, 1.8, 0.2, 0.2), radius: 0.1, fill: purple.lighten(70%))
              content((rel: (1, 0), "to": "r5"), [$B \\ C$])

              for i in range(1, 7) {
                circle((0, -i), fill: black, radius: 2pt, name: "l" + str(i))
                circle((5, -i), fill: black, radius: 2pt, name: "r" + str(i))
              }

              for i in range(1, 4) {
                line("l" + str(i), "r" + str(i + 3), stroke: green + 2pt)
                line("r" + str(i), "l" + str(i + 3), stroke: blue + 2pt)

                if (i < 3) {
                  line("l" + str(i + 1), "r" + str(i + 3), stroke: green + 2pt)
                  line("r" + str(i + 1), "l" + str(i + 3), stroke: blue + 2pt)
                }
              }

              (pause,)
              line("l6", "r6", stroke: 2pt + red, name: "nonedge")
              content((name: "nonedge"), [
                #set align(center)
                #set text(size: 0.8em)
                #v(3pt)
                This cannot be! \ 
                *If such an edges exists then \ $C$ doesnt cover it.*
                ], anchor: "north")

              (pause,)
              line("l1", "r1", stroke: 2pt + black, name: "nonedge2")
              content((name: "nonedge2"), [#set align(center)
              #set text(size: 0.8em)
              #v(3pt)
              Dont care about \ those!], anchor: "north")
            }),
          )

          - Then, note that
            $
              tau(G) = |C|=|C cap B| + |C cap A|
            $
            #v(-5pt)
            #pause
            #goal(title: "1")[ Prove that
              #v(-5pt)
              $
                (C cap A) arrow.turn.r (B backslash C) #text[and] (C cap B) arrow.turn.r (A backslash C).
              $
            ]

        ],
        [
          // #figure(image("figures/L2i9.png", width: 42%)),
        ],
      )
  ]
  #pagebreak()
  #block(width: 100%)[
    #goal(title: "1")[ Prove that
      #v(-5pt)
      $
        (C cap A) arrow.turn.r (B backslash C) #text[and] (C cap B) arrow.turn.r (A backslash C).
      $
    ]
  ]
  #v(-10pt)
  #remark[
    We prove only that $(C cap A) arrow.turn.r (B backslash C)$ as the other case is identical.
  ]
  #v(-10pt)
  Assuming *Goal 1* holds, we have two matchings
  $
    M := (C cap A) arrow.turn.r (B backslash C)
    #h(10pt) #text[and] #h(10pt)
    M' := (C cap B) arrow.turn.r (A backslash C)
  $
  since both are independent we conclude that $M cup M'$ is a matching in $G$.
  \ So that
  $
    nu(G) >= |M cup M'| >= |C cap A| + |C cap B| >= |C| = tau(G).
  $



  // #pagebreak()
  // #claim[For any $v in (A \\ C)$ and $u in (B \\ C)$ in holds that $u v in.not E(G)$.]
  // #align(center)[
  //   #cetz-canvas({
  //     import cetz.draw: *

  //     for i in range(1, 7) {
  //       circle((0, -i * 1.5), fill: black, radius: 2pt, name: "l" + str(i))
  //       circle((5, -i * 1.5), fill: black, radius: 2pt, name: "r" + str(i))
  //     }

  //     rect-around("l1", "l6", padding: (0.4, 0.4, 0.4, 2), radius: 0.2)
  //     rect-around("r1", "r6", padding: (0.4, 2, 0.4, 0.3), radius: 0.2)

  //     rect-around("l1", "l3", padding: (0.2, 0.2, 0.2, 1.8), radius: 0.1, fill: orange.lighten(70%))
  //     content((rel: (-1, 0), "to": "l2"), [$A cap C$])
  //     rect-around("l4", "l6", padding: (0.2, 0.2, 0.2, 1.8), radius: 0.1, fill: purple.lighten(70%))
  //     content((rel: (-1, 0), "to": "l5"), [$A \\ C$])

  //     rect-around("r1", "r3", padding: (0.2, 1.8, 0.2, 0.2), radius: 0.1, fill: orange.lighten(70%))
  //     content((rel: (1, 0), "to": "r2"), [$B cap C$])
  //     rect-around("r4", "r6", padding: (0.2, 1.8, 0.2, 0.2), radius: 0.1, fill: purple.lighten(70%))
  //     content((rel: (1, 0), "to": "r5"), [$B \\ C$])

  //     for i in range(1, 7) {
  //       circle((0, -i * 1.5), fill: black, radius: 2pt, name: "l" + str(i))
  //       circle((5, -i * 1.5), fill: black, radius: 2pt, name: "r" + str(i))
  //     }

  //     for i in range(1, 4) {
  //       line("l" + str(i), "r" + str(i + 3), stroke: green + 2pt)
  //       line("r" + str(i), "l" + str(i + 3), stroke: navy + 2pt)
  //       line("r" + str(i), "l" + str(i), stroke: orange + 2pt)

  //       if (i < 3) {
  //         line("l" + str(i + 1), "r" + str(i + 3), stroke: green + 2pt)
  //         line("r" + str(i + 1), "l" + str(i + 3), stroke: navy + 2pt)
  //       }
  //     }

  //     line("l6", "r6", stroke: 2pt + red, name: "nonedge")
  //     content((name: "nonedge"), [This cannot be!], anchor: "north")
  //   })
  // ]
  // - If such an edge exsists, then $C$ is not VC
  #pagebreak()

  #v(10pt)
  #block(width: 45%)[
    #goal(title: "2")[ By hall theorem, it remains to show
      $
        forall S subset.eq (C cap A), |N_H (S)| >= |S|.
      $
    ]
  ]
  #place(top + left, dx: 13cm, dy: 0.5cm, block(width: 50%)[
    #set text(size: 0.8em)
    #theorem(title: "Hall")[Let $G:=(A union.dot B, E)$ be a bipartite graph.
      Then,
      $
        A arrow.r.turn B #h(20pt) arrow.r.l.long.double #h(20pt)
        |N_G (S)| >= |S|, forall S subset.eq A.
      $
    ]
  ])

  #place(
    top + left,
    dx: 18cm,
    dy: 5cm,
    cetz-canvas({
      import cetz.draw: *

      for i in range(1, 7) {
        circle((0, -i), fill: black, radius: 2pt, name: "l" + str(i))
        circle((5, -i), fill: black, radius: 2pt, name: "r" + str(i))
      }

      rect-around("l1", "l6", padding: (0.4, 0.4, 0.4, 2), radius: 0.2)
      rect-around("r1", "r6", padding: (0.4, 2, 0.4, 0.3), radius: 0.2)

      rect-around("l1", "l3", padding: (0.2, 0.2, 0.2, 1.8), radius: 0.1, fill: orange.lighten(70%))
      content((rel: (-1, 0), "to": "l2"), [$A cap C$])
      rect-around("l4", "l6", padding: (0.2, 0.2, 0.2, 1.8), radius: 0.1, fill: purple.lighten(70%))
      content((rel: (-1, 0), "to": "l5"), [$A \\ C$])

      rect-around("r1", "r3", padding: (0.2, 1.8, 0.2, 0.2), radius: 0.1, fill: orange.lighten(70%))
      content((rel: (1, 0), "to": "r2"), [$B cap C$])
      rect-around("r4", "r6", padding: (0.2, 1.8, 0.2, 0.2), radius: 0.1, fill: purple.lighten(70%))
      content((rel: (1, 0), "to": "r5"), [$B \\ C$])


      rect-around("l2", "l3", padding: 0.1, radius: 0.1, fill: gray.lighten(70%))
      rect-around("r5", padding: 0.1, radius: 0.1, fill: gray.lighten(70%))
      for i in range(1, 7) {
        circle((0, -i), fill: black, radius: 2pt, name: "l" + str(i))
        circle((5, -i), fill: black, radius: 2pt, name: "r" + str(i))
      }

      line("l2", "r5", stroke: green + 2pt)
      line("l3", "r5", stroke: green + 2pt)
    }),
  )

  *Assume by contradiction:* $exists S subset.eq (C cap A)$ s.t. $|N_H (S)| < |S|$. \

  - Set $C^* := (C \\ S) cup (N_H (S))$
  - $C^*$ is a vertex cover of $G$
  - $|C^*| < |C| = tau(G).$
  - Contradict the minimality of $tau(G)$.

  // *Why?* Fix edge $u v in E(G)$ where $v in A$ and $u in B$. \
  // If $v in.not S$, then $u v$ covered by $C^*$ by definition of $C^*$ \ and $C$. If $v in S$, then
  // either $u in (B cup C)$ or $u in N_G (S)$. \ Either way $v in C^*$, so that $C^*$ is vertex cover.
]


== Hall $<==$ König
#theorem(title: "Hall")[Let $G:=(A union.dot B, E)$ be a bipartite graph.
  Then,
  $
    A arrow.r.turn B #h(20pt) arrow.r.l.long.double #h(20pt)
    |N_G (S)| >= |S|, forall S subset.eq A.
  $
]

$==>$
Assume toward contradiction that $exists S subset.eq A$ s.t. $|S| > |N_G (S)|$. \
Then, it follows that in any matching of $G$ at least $1$ vertex of $S$ doesn't get matched into $B$. \
This contradicts the fact that a matching $A arrow.r.turn B$ exists.


== Hall $<==$ König
#theorem(title: "Hall")[Let $G:=(A union.dot B, E)$ be a bipartite graph.
  Then,
  $
    A arrow.r.turn B #h(20pt) arrow.r.l.long.double #h(20pt)
    |N_G (S)| >= |S|, forall S subset.eq A.
  $
]
*We may now assume that $G$ is a graph satisfying the Hall condition, and that $tau(G)= nu(G)$.*

#place(
  top + left,
  dx: 0%,
  dy: 37%,
  block(width: 100%)[
    #theorem(title: "König")[$tau(G) = nu(G)$, whenever $G$ is bipartite.]
  ],
)

#block(width: 50%)[
  #v(50pt)
  #goal[
    Show that $tau(G) >= |A|$.
  ]
]
#v(-10pt)
Then, we have that
$
  #text[size of maximum matching] = underbrace(nu(G) = tau(G), #text[by König]) >= |A|.
$


== Hall $<==$ König
#[
  #block(width: 48%, inset: (left: -0.5cm))[
    #goal[
      Show that $tau(G) >= |A|$.
    ]
  ]

  #place(
    top + left,
    dx: 50%,
    dy: 0%,
    block(width: 48%)[
      #set text(size: 0.8em)
      #assumption[
        - $G:=(A union.dot B, E)$ a bipartite graph,
        - $forall S subset.eq A: |N_G (S)| >= |S|$.
      ]
    ],
  )
  #set math.equation(numbering: "(1)")
  #place(
    top + left,
    dx: 18cm,
    dy: 5cm,
    cetz-canvas({
      import cetz.draw: *

      for i in range(1, 7) {
        circle((0, -i), fill: black, radius: 2pt, name: "l" + str(i))
        circle((5, -i), fill: black, radius: 2pt, name: "r" + str(i))
      }

      rect-around("l1", "l6", padding: (0.4, 0.4, 0.4, 2), radius: 0.2)
      rect-around("r1", "r6", padding: (0.4, 2, 0.4, 0.3), radius: 0.2)

      rect-around("l1", "l3", padding: (0.2, 0.2, 0.2, 1.8), radius: 0.1, fill: orange.lighten(70%))
      content((rel: (-1, 0), "to": "l2"), [$A cap C$])
      rect-around("l4", "l6", padding: (0.2, 0.2, 0.2, 1.8), radius: 0.1, fill: purple.lighten(70%))
      content((rel: (-1, 0), "to": "l5"), [$A \\ C$])

      rect-around("r1", "r3", padding: (0.2, 1.8, 0.2, 0.2), radius: 0.1, fill: orange.lighten(70%))
      content((rel: (1, 0), "to": "r2"), [$B cap C$])
      rect-around("r4", "r6", padding: (0.2, 1.8, 0.2, 0.2), radius: 0.1, fill: purple.lighten(70%))
      content((rel: (1, 0), "to": "r5"), [$B \\ C$])

      for i in range(1, 7) {
        circle((0, -i), fill: black, radius: 2pt, name: "l" + str(i))
        circle((5, -i), fill: black, radius: 2pt, name: "r" + str(i))
      }

      for i in range(1, 4) {
        line("l" + str(i), "r" + str(i + 3), stroke: green + 2pt)
        line("r" + str(i), "l" + str(i + 3), stroke: navy + 2pt)
        line("r" + str(i), "l" + str(i), stroke: orange + 2pt)

        if (i < 3) {
          line("l" + str(i + 1), "r" + str(i + 3), stroke: green + 2pt)
          line("r" + str(i + 1), "l" + str(i + 3), stroke: navy + 2pt)
        }
      }
    }),
  )
  #v(-10pt)
  #block(width: 62%)[
    #proof[
      Let $C$ be a minimum vertex cover in $G$.

      $
         tau(G) = |C| & = |A cap C| + |B cap C|
      $ <eq:1>
      - $underbracket(N_G (A \\ C) subset.eq B cap C, #[
        #set text(size: 0.7em)
        #h(20pt)
        *Otherwise $exists u v$ edge not covered by $C$*
      ]). ==> |B cap C| >=  |N_G (A \\ C)|.$ 

      - Fix $S = (A \\ C) underbracket(==>,"By assumption")$ $|N_G (A \\ C)| >= |A \\ C|$.
      #v(5pt)
      $==>$ #v(-35pt)
      $
        |B cap C| >= |N_G (A \\ C)| >= |A \\ C|
      $ <eq:2>
      Combining @eq:1 and @eq:2
      #math.equation(block: true, numbering: none)[
        $ tau(G) >=|A cap C| + |A \\ C| = |A| $
      ] <hidden-label>
      #v(-25pt)
    ]
  ]
]

= Berge's Theorem
== M-Augmenting paths
#[
  #set math.equation(numbering: "(1)")
  #v(20pt)
  // #set align(horizon)
  $G$-graph, $M$-matching. \
  A path $P:= x_1 x_2 ... x_ell$ is called $M$-alternating if:
  $
    x_1 x_2 in M => x_2x_3 in.not M => x_3x_4 in M => ...
  $<eq:3>
  or
  $
    x_1 x_2 in.not M => x_2x_3 in M => x_3x_4 in.not M => ...
  $<eq:4>
  // If an alternating path is maximal of @eq:4[Type]. Then, $P$ is called an M-Augmenting path.
]

#place(
  top + left,
  dx: 3cm,
  dy: 7.5cm,
  figure(image("figures/L2i11.png", width: 36%)),
)

#place(
  top + left,
  dx: 14.8cm,
  dy: 8cm,
  figure(image("figures/L2i12.png", width: 25%)),
)

#place(
  top + left,
  dx: 17.2cm,
  dy: 8cm,
  block(fill: white, width: 100pt, height: 30pt),
)

#place(
  top + left,
  dx: 6cm,
  dy: 7.2cm,
  block(fill: white, width: 100pt, height: 30pt),
)

== M-Augmenting paths
#definition[
  $G$-graph, $M$-matching. \ An $M$-Alternating path $P:= x_1 ... x_ell$ is called $M$-Augmenting if $x_1 in.not V(M)$ and $x_ell in.not V(M)$.
]
#remark[
  Trivially, if an $M$-Augmenting path exists, then $|M|<nu(G)$. \
  Is the opposite true?
]

#place(
  top + left,
  dx: 0cm,
  dy: 7.111cm,
  figure(image("figures/L2i13.png", width: 100%)),
)
// #claim[
//   Let $M$ be a matching of $G$, and let $P:= x_1 x_2 ... x_ell$ be an M-augmenting path. \
//   Then, $M^* := M - #text[odd edges] + #text[even edges]$ is a matching of $G.$
// ]
// #remark[
//   Trivially, $|M^*| = |M|+1$.
// ]

== Berge's Theorem
#[
  #set align(horizon)
  #theorem(title: "Berge's")[
    $G$-graph, $M$-matching
    $
      M #text[max matching] <==> M #text[has no $M$-Augmenting paths].
    $
  ]

  For convinence we will prove the negation
  $
    M #text[is not max] <==> M #text[has an $M$-Augmenting paths].
  $
  We already proved $<==$ it remains to prove $==>$. \
]

== Berge's Theorem
#[
  #v(20pt)
  Given two matching $N$ and $M$ in $G$?
  What does $N triangle M$ looks like?
  $
    N triangle M := (N \\ M) cup (M \\ C).
  $
  $=>$ $N triangle M$ is a graph where every vertex degree is $<= 2$ \
  $=>$ Every path or cycle of $N triangle M$ must be alternating  \
  #h(20pt) #[ --
    #set text(size: 0.8em)
    *otherwise we will see path $u v w$ with $u v in M$ and $v w in M$ implying that $M$ is not a matching. (or N)*]\
  $=>$ Connected components of $N triangle M$ consist of _single edges, alternating paths and even cycles_.
  #place(
    top + left,
    dx: 4cm,
    dy: 7.111cm,
    figure(image("figures/L2i14.png", width: 65%)),
  )
]

== Berge's Theorem
#[
  #goal[
    $M #text[is not max] ==> M #text[has an $M$-Augmenting paths]$
  ]
  #proof()[
    Let $N$ be a max matching in $G$.
    - At the connected components of $N triangle M$.
      - every connected component is either _single edge_, _alternating path_ or _even cycle_.
    - Since $|N| > |M|$ there must exists a connected component $C$ of $N triangle M$ with more edges \
      $N$ than edges of $M$.
      - $C$ must be either a single edge of $N$ or an $M$-Augmenting path. #[
          #set text(size: 0.8em, weight: "light", fill: red.darken(50%))
          (Single edge is also $M$-Augmenting)]
  ]

  #place(
    top + left,
    dx: 8cm,
    dy: 9cm,
    figure(image("figures/L2i15.png", width: 35%)),
  )
]

= The Hungarian Method
== The Hungarian Method
#v(10pt)
Using the Berge's Theorem the Hungarian \
method for finding a max matching is \
the following algo:

#[
  #show: style-algorithm
  #algorithm-figure(
    "",
    vstroke: .5pt + luma(200),
    {
      import algorithmic: *
      Procedure(
        "max_matching",
        "G",
        {
          Assign([Set $M$], [$emptyset$])
          LineBreak

          While(
            [there _is an_ has an $M$-augmenting path in $G$],
            {
              Line([Let $P$ be an $M$-augmenting path in $G$])
              Line([Augment $M$ along $P$])
            },
          )
          LineBreak
          Return([$M$])
        },
      )
    },
  )
]
#place(
  top + left,
  dx: 12cm,
  dy: 0cm,
  block(width: 60%)[
    #theorem(title: "Berge's")[
      $G$-graph, $M$-matching
      $
        M #text[max matching] <==> M #text[has no $M$-Augmenting paths].
      $
    ]
  ],
)
#v(-10pt)
#pause
#place(
  top + left,
  dx: 18cm,
  dy: 4.5cm,
  block(width: 30%)[
    #set align(center)
    #problem[
      $G$-graph, $M$-matching. \ Determine whether an \ $M$-augmenting path in $G$ exists, if it does then find it.
    ]
  ],
)

== Not so easy
#[
  #set align(center)
  #set text(size: 1.2em)
  #v(40pt)
  *In general graphs, finding an $M$-augmenting path might be chalenging.*
]

#place(
  top + left,
  dx: 0cm,
  dy: 2.5cm,
  figure(image("figures/L2i16.png", width: 100%)),
)

#place(
  top + center,
  dx: 0cm,
  dy: 12cm,
  [
    #set align(center)
    *Odd cycles makes finding paths dificult.* \
    _Bipartite graphs have no odd cycles, is it easier there?_
  ],
)

== The Hungarian Algorithm
#block(width: 50%)[
  #v(70pt)
  Given $G:=(A cup.dot B, E)$ and $M subset.eq E(G)$ define
  - $A_M := A \\ V(M)$ unmached vertices in $A$.
  - $B_M := A \\ V(M)$ unmached vertices in $B$.
  *Our goal:* Find an $M$-augmenting path from $A_M$ to $B_M$. *How?*
]

#place(
  top + left,
  dx: 13cm,
  dy: 1cm,
  figure(image("figures/L2i17.png", width: 55%)),
)

#pause
Construct directed graph set: \
- #text(fill: green)[matching edges $M$] directed from $B$ to $A$.
- Everything else from $A$ to $B$.

  #place(
    top + left,
    dx: 14.7cm,
    dy: -8.2cm,
    figure(image("figures/L2i18.png", width: 140%)),
  )

#pause
Run any path algorithm from $A_M$ to $B_M$,
any \ such path is an $M$-Augmenting path.

#place(
  top + left,
  dx: 13cm,
  dy: 1cm,
  figure(image("figures/L2i19.png", width: 57%)),
)

#pause
#place(
  top + left,
  dx: 13cm,
  dy: 1cm,
  figure(image("figures/L2i20.png", width: 57%)),
)
