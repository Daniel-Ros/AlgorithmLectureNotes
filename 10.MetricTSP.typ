#import "settings/mstyle.typ": *
#import algorithmic: algorithm-figure, style-algorithm
#show: style-algorithm

#show: conf.with(
  handout: false,
  subtitle: [Metric Traveling Salesperson Problem],
)

#title-slide()

= The Metric TSP

== Setup
#place(
  dx: 55%,
  dy: 20%,
  figure(
  image("figures/tsp1.webp", width: 35%),
  caption: [A TSP tour through US cities],
)
)

#[
  #set align(horizon)
  #set text(size: 0.9em)
  #table(
    columns: (1fr, 1fr),
    stroke: none,
    align: top,
    [
      - $n$ cities denoted by $[n]$
      - *Symmetric* cost matrix $C := (c_(i j) >= 0)$:
        - $c_(i i) = 0$ for all $i in [n]$
        - *$triangle$-inequality:* $c_(i j) + c_(j k) >= c_(i k)$ for all $i,j,k$
      #pause
      We view $C$ as a complete *edge-weighted* graph on $n$ vertices.

      #pause
      #problem[
        *Metric TSP ($triangle$TSP)*

        *Find:* a minimum cost *Hamiltonian cycle* (visit every city exactly once and return).
      ]
    ],
    [
      #set align(center)
      // #pause
      // #figure(
      //   image("figures/tsp1.webp", width: 65%),
      //   caption: [A TSP tour through US cities],
      // )
    ],
  )
]


== Key Observation
#[
  #set align(horizon)
  #set text(size: 0.9em)

  #observation[
    Removing *any single edge* from a TSP-tour leaves a *spanning tree*.
  ]

  #pause

  *Why?* A Hamiltonian cycle visits all $n$ vertices and uses $n$ edges. Remove one edge → a path visiting all $n$ vertices → a *spanning tree* (connected, $n-1$ edges, no cycles).

  #pause

  #theorem[
    $"Cost of optimal TSP-tour" >= "Cost of a minimum spanning tree (MST)"$
  ]<mst>

  #pause

  *Proof.* Let $T^*$ be an optimal tour and $e$ any edge of $T^*$. Then $T^* - e$ is a spanning tree, so
  $
    "MST cost" <= c(T^* - e) < c(T^*) = "OPT". quad square
  $
]

= Nearest Extension Algorithm

== The Algorithm
#[
  #set align(horizon)
  #set text(size: 0.88em)
  #table(
    columns: (1fr, 1fr),
    stroke: none,
    align: top,
    [
      #algorithm-figure(
        [Nearest Extension],
        vstroke: .5pt + luma(200),
        {
          import algorithmic: *
          Line([*Input:* cities $[n]$, costs $C$])
          Line([Let $i,j in [n]$ be the *two closest* cities])
          Assign([$T$], [$({i,j}, {i -> j})$])
          While([$V(T) != [n]$], {
            Assign([$( x,y )$], [$arg min {c_(x y) : x in V(T), y in.not V(T)}$])
            Line([Let $k$ = vertex *after* $x$ along $T$])
            Assign([$T$], [$T - (x -> k) + (x -> y) + (y -> k)$])
          })
          Return([$T + (j -> i)$])
        },
      )
    ],
    [
      *Idea:* at each step, *insert* the nearest unvisited city $y$ into the tour right after its closest tour-vertex $x$.

      #v(8pt)
      #cetz-canvas(length: 1.0cm, {
        import cetz.draw: *
        // Current tour: i → ... → x → k → ... → j
        let i_p = (0.0, 1.5)
        let x_p = (3.0, 1.5)
        let k_p = (4.5, 1.5)
        let j_p = (6.5, 1.5)
        let y_p = (3.6, 3.2)

        // Tour path
        line(i_p, x_p, stroke: (paint: blue.darken(20%), thickness: 1.4pt),
          mark: (end: ">", size: 0.2))
        line(x_p, k_p, stroke: (paint: red, thickness: 1.4pt, dash: "dashed"))
        line(k_p, j_p, stroke: (paint: blue.darken(20%), thickness: 1.4pt),
          mark: (end: ">", size: 0.2))

        // New edges
        line(x_p, y_p, stroke: (paint: green.darken(30%), thickness: 1.4pt),
          mark: (end: ">", size: 0.2))
        line(y_p, k_p, stroke: (paint: green.darken(30%), thickness: 1.4pt),
          mark: (end: ">", size: 0.2))

        // Vertices
        for (p, lbl) in ((i_p,"i"),(x_p,"x"),(k_p,"k"),(j_p,"j")) {
          circle(p, radius: 0.2, fill: rgb("#073749"), stroke: none)
          content((p.at(0), p.at(1) - 0.55), text(size:0.72em, weight:"bold")[#lbl])
        }
        circle(y_p, radius: 0.2, fill: red.darken(10%), stroke: none)
        content((y_p.at(0) + 0.4, y_p.at(1)), text(size:0.72em, fill:red, weight:"bold")[#h(30pt) $y$ (new)])

        content((3.6, 0.5), text(size: 0.7em, fill: red)[drop $x -> k$])
        content((4.5, 2.7), text(size: 0.7em, fill: green.darken(30%))[#h(50pt)  add $x->y->k$])
      })
    ],
  )
]

== Proof of 2-Approximation
#[
  #set align(horizon)
  #set text(size: 0.88em)

  #theorem[
    The Nearest Extension algorithm is a *$2$-approximation* for $triangle$TSP.
  ]

  #pause

  Let $F'$ = edges chosen greedily (one per extension step), and $F := F' union {i j}$.

  #pause

  #claim[
    $([n], F)$ is a *minimum spanning tree*.
  ]

  - Each edge of $F'$ is the *cheapest edge crossing some cut* (greedy choice); 
  - same for $i j$ (closest pair). 
  - So $|F'| = n-2$ extension steps $=> |F| = n-1$, and there is an execution of *Prim's algorithm* that produces $F$. $square$

  #pause

  Hence by @mst
     $
     "OPT" >= c(F) = "weight of MST."
     $ 
]

#pagebreak()
#[
  #set align(horizon)
  #set text(size: 0.88em)

  The returned tour $T + i j$ is obtained by a series of *bypasses*: each extension replaces $f:=(x -> k)$\ with $(x -> y -> k)$.

#place(
    dx: 75%,
    dy: 20% - 30pt,
    cetz-canvas(length: 1.0cm, {
        import cetz.draw: *
        // Current tour: i → ... → x → k → ... → j
        let i_p = (0.0, 1.5)
        let x_p = (3.0, 1.5)
        let k_p = (4.5, 1.5)
        let j_p = (6.5, 1.5)
        let y_p = (3.6, 3.2)

        // Tour path
        line(i_p, x_p, stroke: (paint: blue.darken(20%), thickness: 1.4pt),
          mark: (end: ">", size: 0.2))
        line(x_p, k_p, stroke: (paint: red, thickness: 1.4pt, dash: "dashed"))
        line(k_p, j_p, stroke: (paint: blue.darken(20%), thickness: 1.4pt),
          mark: (end: ">", size: 0.2))

        // New edges
        line(x_p, y_p, stroke: (paint: green.darken(30%), thickness: 1.4pt),
          mark: (end: ">", size: 0.2))
        line(y_p, k_p, stroke: (paint: green.darken(30%), thickness: 1.4pt),
          mark: (end: ">", size: 0.2))

        // Vertices
        for (p, lbl) in ((i_p,"i"),(x_p,"x"),(k_p,"k"),(j_p,"j")) {
          circle(p, radius: 0.2, fill: rgb("#073749"), stroke: none)
          content((p.at(0), p.at(1) - 0.55), text(size:0.72em, weight:"bold")[#lbl])
        }
        circle(y_p, radius: 0.2, fill: red.darken(10%), stroke: none)
        content((y_p.at(0) + 0.4, y_p.at(1)), text(size:0.72em, fill:red, weight:"bold")[#h(30pt) $y$ (new)])

        content((3.6, 0.5), text(size: 0.7em, fill: red)[drop $x -> k$])
        content((4.5, 2.7), text(size: 0.7em, fill: green.darken(30%))[#h(50pt)  add $x->y->k$])
      })
  )

  #pause

  For each bypass, the *cost increase* is:
  $
    underbrace(c_(x y) + c_(y k), "cost of new edges") - underbrace(c_(x k), "cost of old edge") quad "(non-negative by" triangle"-ineq.)"
  $
  By the $triangle$-inequality we have
  $
    c_(y k) <= c_(y x) + c_(x k)
  $
  So that:
  $
    "increase" = c_(x y) + c_(y k) - c_(x k) <= c_(x y) + (c_(y x) + c_(x k)) - c_(x k) <= 2 c_(x y) = 2c(f). quad #tr[(since $x y in F'$)]
  $

  #pause

  Summing over all bypasses plus the final closing edge $j i$:
  $
    c(T + i j) <= c_(i j) + sum_(f in F') 2 c(f) <= 2 sum_(f in F) c(f) <= 2 dot "OPT". quad square
  $
]

= Doubling Trees Algorithm

== Euler Tours
#[
  #place(
    dx: 56%,
    dy: 5%,
    figure(image("figures/tsp2.png", width: 45%),)
  )

  #set align(horizon)
  #set text(size: 0.8em)
  #table(
    columns: (1fr, 1fr),
    stroke: none,
    align: top,
    [
      #definition[
        An *Euler tour* of a connected multigraph is a *closed walk* that traverses every edge *exactly once*.
      ]

      #pause

      #theorem[
        $G$-multigraph *Eulerian* $<=>$ every vertex has *even degree*. 
      ]

      #remark[
        #v(-30pt) #h(90pt) Finding an Euler tour is in $P$.
      ]

      #pause

      #observation[
        If $T$ is a tree, *doubling* every edge gives an Eulerian multigraph.

        *Proof:* Every vertex gets degree $2 dot deg_T(v)$ — always even. $square$
      ]
    ],
    [
      #place(
          dx: 15%,
          dy: 40%,
          figure(image("figures/tsp3.png", width: 95%),)
        )
    ],
  )
]

== The Algorithm and Proof
#[
  #set align(horizon)
  #set text(size: 0.88em)
  #table(
    columns: (1fr, 1fr),
    stroke: none,
    align: top,
    [
      #algorithm-figure(
        [Doubling Trees],
        vstroke: .5pt + luma(200),
        {
          import algorithmic: *
          Line([*Input:* complete graph $G$ with costs $C$])
          Assign([$T$], [MST of $G$])
          Assign([$T'$], [double every edge of $T$])
          Assign([$cal(E)$], [Euler tour of $T'$])
          Return([TSP-tour from $cal(E)$ by *shortcutting*])
        },
      )
        #set text(size: 0.82em)
        #place(
    dx: 10%,
    dy: 12%,
    figure(image("figures/tsp3.png", width: 80%),)
  )
      *Shortcutting:* traverse $cal(E)$; keep only the *first appearance* of each vertex. By the $triangle$-inequality, shortcuts never increase cost.
    ],
    [
      #pause

      #theorem[
        Doubling Trees is a *$2$-approximation* for $triangle$TSP.
      ]

      #pause

      *Proof.* Let $L$ = output tour, $T$ = MST, $T'$ = doubled tree.
      $
        c(T') = 2 c(T) <= 2 dot "OPT"
      $
      since $"OPT" >=$ MST cost (Key Observation).

      Shortcutting via $triangle$-ineq. gives $c(L) <= c(cal(E)) = c(T')$, so:
      $
        c(L) <= c(T') <= 2 dot "OPT". quad square
      $
    ],
  )
]

= Christofides Algorithm

== Motivation and Key Lemmas
#[
  #set align(horizon)
  #set text(size: 0.88em)

  Doubling the whole MST is *wasteful* — we only need to fix the *odd-degree vertices* to make the graph Eulerian.

  #pause

  #lemma[
    In any graph, the number of *odd-degree vertices* is *even*.
  ]

  #pause

  #lemma[
    Let $G$ be a connected graph and $M$ a *perfect matching* on the odd-degree vertices of $G$. Then $G + M$ is *Eulerian*.

    *Proof.* Adding $M$ makes every odd-degree vertex even-degree; all others remain even. $square$
  ]

  #pause

  #remark[
    A minimum-cost perfect matching on $m$ vertices can be found in polynomial time.
  ]
]

== The Algorithm
#[
  #set align(horizon)
  #set text(size: 0.88em)
  #table(
    columns: (1fr, 1fr),
    stroke: none,
    align: top,
    [
      #algorithm-figure(
        [Christofides],
        vstroke: .5pt + luma(200),
        {
          import algorithmic: *
          Line([*Input:* complete graph $G$ with costs $C$])
          Assign([$T$], [MST of $G$])
          Assign([$O$], [odd-degree vertices of $T$])
          Assign([$M$], [min-cost perfect matching in $G[O]$])
          Assign([$H$], [$T + M$ (multigraph)])
          Assign([$cal(E)$], [Euler tour of $H$])
          Return([TSP-tour from $cal(E)$ by shortcutting])
        },
      )
    ],
    [
      #set align(center)
      #cetz-canvas(length: 1.1cm, {
        import cetz.draw: *
        // MST nodes
        let r  = (2.5, 4.5)
        let a  = (1.0, 3.0)
        let b  = (4.0, 3.0)
        let c  = (0.2, 1.5)
        let d  = (2.0, 1.5)
        let e  = (3.2, 1.5)
        let f  = (5.0, 1.5)
        // MST edges
        for (u,v) in ((r,a),(r,b),(a,c),(a,d),(b,e),(b,f)) {
          line(u, v, stroke: (paint: rgb("#073749"), thickness: 1.3pt))
        }
        // Matching edges on odd-degree vertices (c,d,e,f are degree 1 → odd)
        for (u,v) in ((c,d),(e,f)) {
          line(u, v, stroke: (paint: red, thickness: 1.8pt, dash: "dashed"))
        }
        // Nodes
        for (p, odd) in ((r,false),(a,false),(b,false),(c,true),(d,true),(e,true),(f,true)) {
          circle(p, radius: 0.22,
            fill: if odd { red.lighten(60%) } else { rgb("#073749") },
            stroke: if odd { (paint:red, thickness:1.2pt) } else { none })
        }
        content((2.5, 0.4), text(size:0.7em)[Red = odd-degree; dashed = matching $M$])
      })
    ],
  )
]

== The 3/2-Approximation
#[
  #set align(horizon)
  #set text(size: 0.88em)

  #theorem[
    The Christofides algorithm is a *$3/2$-approximation* for $triangle$TSP.
  ]

  #pause

  We need the following key lemma:

  #lemma[
    Let $"OPT"$ be the optimal TSP cost, $W subset.eq V(G)$ with $|W|$ even, and $M$ a min-cost perfect matching in $G[W]$. Then
    $
      c(M) <= "OPT" / 2.
    $
  ]

  #pause

  *Proof of the theorem (given the lemma).* Let $L$ = Christofides output, $T$ = MST.
  $
    c(L) <= c(T) + c(M) <= "OPT" + "OPT"/2 = 3/2 dot "OPT". quad square
  $
  The first inequality: shortcutting from the Euler tour of $T+M$ doesn't increase cost. The second: $c(T) <= "OPT"$ (Key Observation) and $c(M) <= "OPT"/2$ (lemma, with $W = O$, $|O|$ even by the odd-degree lemma).
]

== Proof of Key Lemma
#[
  #set align(horizon)
  #set text(size: 0.88em)

#block(width: 60%)[
  #lemma[
    $c(M) <= "OPT"/2$ for any $W subset.eq V$ with $|W|$ even, where $M$ is a min-cost perfect matching in $G[W]$.
  ]

  #pause

  Let $T^*$ = optimal TSP-tour (cost $"OPT"$). Let $T'$ = the tour in $G[W]$ obtained by *shortcutting* $T^*$ to only the vertices of $W$.


  #place(
    dx: 110%,
    dy: -50%,
    figure(image("figures/tsp4.png", width: 50%),)
  )

  By the $triangle$-inequality, shortcutting never increases cost:
  $
  c(T') <= c(T^*) = "OPT".
  $

  #pause

  Since $|W|$ is *even*, $T'$ is an *edge-disjoint union of two perfect matchings* $M_1, M_2$ on $W$.

    #place(
    dx: 110%,
    dy: -45%,
    figure(image("figures/tsp5.png", width: 50%),)
  )

  #pause

  Since $M$ is the *minimum-cost* perfect matching in $G[W]$:
  $
    c(M) <= min(c(M_1), c(M_2)) <= (c(M_1) + c(M_2))/2 = c(T')/2 <= "OPT"/2. quad square
  $

      #place(
    dx: 110%,
    dy: -25%,
    figure(image("figures/tsp6.png", width: 50%),)
  )
]
]
