#import "settings/mstyle.typ": *
#import algorithmic: algorithm-figure, style-algorithm
#show: style-algorithm

#show: conf.with(
  handout: false,
  subtitle: [Clustering Algorithms],
)

#title-slide()

= The $k$-Centre Problem

== Setup
#[
  #set align(horizon)
  #set text(size: 0.9em)
  #table(
    columns: (1fr, 1fr),
    stroke: none,
    align: top,
    [
      - $[n]$ --- $n$ *data points*
      - $D := (d_(i j))$ --- symmetric distance matrix:
        - $d_(i i) = 0$ for all $i$
        - $d_(i j) >= 0$ for all $i, j in [n]$
      - $D$ satisfies the *$triangle$-inequality*:
        $
          forall i,j,k in [n]: d_(i j) + d_(j k) >= d_(i k)
        $
      #pause
      We view $D$ as a *positively edge-weighted complete graph* on $n$ vertices.

      #pause
      For $S subset.eq [n]$ and $i in [n]$, define the *distance from $i$ to $S$*:
      $
        d(i, S) := min_(j in S) d_(i j)
      $
      Note: if $i in S$, then $d(i,S) = 0$.
    ],
    [
      #set align(center)
      #pause
      #cetz-canvas({
        import cetz.draw: *
        set-style(stroke: (thickness: 0.7pt))
        // S region
        circle((2.5, 2.2), radius: 1.9,
          stroke: (paint: rgb("#073749"), dash: "dashed"),
          fill: rgb("#073749").lighten(92%))
        content((2.5, 0.1), text(fill: rgb("#073749"), weight: "bold")[$S$])
        // Points in S
        for (px, py) in ((1.6, 1.6), (2.1, 2.9), (3.2, 2.5), (2.7, 1.3), (1.9, 2.4)) {
          circle((px, py), radius: 0.12, fill: rgb("#073749"), stroke: none)
        }
        // Nearest point in S highlighted
        circle((3.2, 2.5), radius: 0.2, fill: none,
          stroke: (paint: orange, thickness: 1.5pt))
        // Point i
        circle((5.8, 2.1), radius: 0.15, fill: red, stroke: none)
        content((6.1, 2.2), text(fill: red, weight: "bold")[$i$])
        // Dashed line i → nearest
        line((5.8, 2.1), (3.4, 2.5),
          stroke: (paint: red, dash: "dashed", thickness: 1pt))
        content((4.6, 2.65), text(size: 0.85em)[$d(i,S)$])
      })
    ],
  )
]

== The $k$-Centre Problem
#[
  #set align(horizon)
  #set text(size: 0.9em)
  #table(
    columns: (1fr, 1fr),
    stroke: none,
    align: top,
    [
      #problem[
        *The $k$-Centre Problem*

        *Given:* $k in NN$, points $[n]$, distance matrix $D$ satisfying $triangle$-ineq.

        *Find:* $S subset.eq [n]$, $|S| = k$, minimising
        $
          max_(i in [n]) d(i, S)
        $
      ]
      #pause
      - Members of $S$ are *centres* (cluster centroids)
      - $max_(i in [n]) d(i,S)$ is the *radius* of $S$
      - Goal: minimise radius --- every point close to some centre

      #pause
      #remark[
        The $k$-centre problem is *NP-hard*.
      ]
    ],
    [
      #set align(center)
      #set text(size: 1.2em)
      #pause
      #cetz-canvas(length: 1.5cm, {
        import cetz.draw: *
        set-style(stroke: (thickness: 0.7pt))
        // Cluster 1: bottom-left
        let c1 = ((0.5,0.5),(0.5,1.4),(1.4,0.5),(1.0,1.3))
        // Cluster 2: bottom-right
        let c2 = ((4.5,0.5),(4.5,1.4),(5.4,0.5),(5.5,1.2))
        // Cluster 3: top-middle
        let c3 = ((2.3,3.5),(2.3,4.4),(3.2,3.5),(2.7,4.6))
        // Draw circles
        circle((0.9,0.9), radius: 1.0,
          stroke: (paint: blue.darken(20%), thickness: 1.2pt), fill: blue.lighten(88%))
        circle((4.9,0.9), radius: 1.0,
          stroke: (paint: green.darken(20%), thickness: 1.2pt), fill: green.lighten(88%))
        circle((2.7,3.9), radius: 1.0,
          stroke: (paint: red.darken(20%), thickness: 1.2pt), fill: red.lighten(88%))
        // Points
        for (px,py) in c1 { circle((px,py), radius:0.1, fill: blue.darken(30%), stroke:none) }
        for (px,py) in c2 { circle((px,py), radius:0.1, fill: green.darken(30%), stroke:none) }
        for (px,py) in c3 { circle((px,py), radius:0.1, fill: red.darken(30%), stroke:none) }
        // Centres
        circle((0.9,0.9), radius:0.18, fill: blue.darken(50%), stroke:none)
        circle((4.9,0.9), radius:0.18, fill: green.darken(50%), stroke:none)
        circle((2.7,3.9), radius:0.18, fill: red.darken(50%), stroke:none)
        // Radius line example
        line((0.9,0.9),(0.5,1.4), stroke:(paint:blue.darken(40%), dash:"dashed", thickness:2pt))
        content((0.55,1.1), text(size:1em)[$r$])
        content((2.7,-0.7), text(size:0.85em)[Service points = filled dots])
      })
    ],
  )
]

== The Greedy Algorithm
#[
  #set align(horizon)
  #set text(size: 0.9em)
  #table(
    columns: (1fr, 1fr),
    stroke: none,
    align: top,
    [
      #algorithm-figure(
        [Greedy $k$-Centre],
        vstroke: .5pt + luma(200),
        {
          import algorithmic: *
          Line([*Input:* points $[n]$, distances $D$, integer $k$])
          Assign([$S$], [${i}$ for arbitrary $i in [n]$])
          While([$|S| < k$], {
            Assign([$j$], [$arg max_(j in [n]) d(j, S)$])
            Line(text(fill: red, size: 0.85em)[(pick farthest point from $S$)])
            Assign([$S$], [$S union {j}$])
          })
          Return([$S$])
        },
      )
      #pause
      #remark[
        More concisely: start with any point; repeatedly add the point *farthest* from the current set.
      ]
    ],
    [
      #pause
      #set align(center)
      *Execution example* ($k = 4$):
      #v(4pt)
      #cetz-canvas(length: 1.1cm, {
        import cetz.draw: *
        let circle-to(vi, vj, ..style) = get-ctx(ctx => {
          let (_, pi) = cetz.coordinate.resolve(ctx, vi)
          let (_, pj) = cetz.coordinate.resolve(ctx, vj)
          let r = calc.sqrt(
            calc.pow(pj.at(0) - pi.at(0), 2) +
            calc.pow(pj.at(1) - pi.at(1), 2)
          )
          circle(vi, radius: r, ..style)
        })

        let pts = (
          (0.4, 0.5), (1.5, 1.8), (0.7, 3.1), (2.3, 0.3), (2.0, 2.5),
          (3.2, 1.2), (3.8, 3.4), (4.5, 0.7), (5.1, 2.1), (4.8, 3.9),
          (1.1, 4.3), (3.0, 4.6), (2.3, -2.3), (1.3, -2.1), (1.9, -1.5)
        )
        for (i, p) in pts.enumerate() {
          circle(p, radius: 0.15, fill: black, stroke: 0.5pt + black, name: "v" + str(i))
        }
        (pause,)
        circle("v3", radius: 0.15,
          fill: red, stroke: (paint: red, thickness: 1.8pt))
        content((rel: (0, -0.6), to: "v3") , text(size: 0.68em, fill: red)[
          #set align(center)
          *$s_1$ \ arbitrary*])
        (pause,)
        circle("v9", radius: 0.15,
          fill: red, stroke: (paint: red, thickness: 1.8pt))
        content((rel: (0, -0.4), to: "v9") , text(size: 0.68em, fill: red)[*$s_2$*])

        (pause,)
        circle("v10", radius: 0.15,
          fill: red, stroke: (paint: red, thickness: 1.8pt))
        content((rel: (0, -0.4), to: "v10") , text(size: 0.68em, fill: red)[*$s_3$*])

        (pause,)
        circle("v12", radius: 0.15,
          fill: red, stroke: (paint: red, thickness: 1.8pt))
        content((rel: (0, -0.4), to: "v12") , text(size: 0.68em, fill: red)[*$s_4$*])

        /////////
        (pause,)
        circle-to("v3", "v7", fill: blue.lighten(80%), stroke: (paint: blue.lighten(80%), thickness: 1.8pt))
        circle-to("v9", "v8", fill: blue.lighten(80%), stroke: (paint: blue.lighten(80%), thickness: 1.8pt))
        circle-to("v10", "v11", fill: blue.lighten(80%), stroke: (paint: blue.lighten(80%), thickness: 1.8pt))
        circle-to("v12", "v13", fill: blue.lighten(80%), stroke: (paint: blue.lighten(80%), thickness: 1.8pt))

        // circle("v11", radius: 0.25,
        //   fill: green, stroke: (paint: green, thickness: 1.8pt))

        for (i, p) in pts.enumerate() {
          circle(p, radius: 0.15, fill: black, stroke: 0.5pt + black, name: "v" + str(i))
        }
        circle("v3", radius: 0.15,
          fill: red, stroke: (paint: red, thickness: 1.8pt))
        circle("v9", radius: 0.15,
          fill: red, stroke: (paint: red, thickness: 1.8pt))
        circle("v10", radius: 0.15,
          fill: red, stroke: (paint: red, thickness: 1.8pt))
        circle("v12", radius: 0.15,
          fill: red, stroke: (paint: red, thickness: 1.8pt))

      line("v3", "v7",
      stroke: (paint: blue.lighten(40%), dash: "dashed", thickness: 2pt))
      content(
        (rel: (0, -0.5), to: ("v3", 50%, "v7")),
        text(size: 0.68em, fill: blue.darken(20%))[$r_1$],
        )

      line("v9", "v8",
      stroke: (paint: blue.lighten(40%), dash: "dashed", thickness: 2pt))
      content(
        (rel: (0.5, 0), to: ("v9", 50%, "v8")),
        text(size: 0.68em, fill: blue.darken(20%))[$r_2$],
        )

      line("v10", "v11",
      stroke: (paint: blue.lighten(40%), dash: "dashed", thickness: 2pt))

      content(
        (rel: (0, -0.5), to: ("v10", 50%, "v11")),
        text(size: 0.68em, fill: blue.darken(20%))[$r_3$],
        )

      line("v12", "v13",
      stroke: (paint: blue.lighten(40%), dash: "dashed", thickness: 2pt))

      content(
        (rel: (0, -0.5), to: ("v12", 50%, "v13")),
        text(size: 0.68em, fill: blue.darken(20%))[$r_4$],
        )

      content(
        (6,-2),
        text(size: 0.68em, fill: red.darken(20%))[
          #set align(center)
          
          Radius of centroids\ defined by the furthest point \ in that centroid],
        )
      })

    ],
  )
  #v(-20pt)
  #[
    #set text(size: 1.2em)
    #set align(center)
    #pause
  *How Good is the greedy algorithm?*
  ]
]


= Approximation Algorithms

== $f$-Approximations
#[
  #set align(horizon)
  #set text(size: 0.9em)

  #definition[
    An algorithm $A$ for a *minimisation* problem $Pi$ is an *$f$-approximation* for $Pi$ if
    $
      A(I) <= f dot "OPT"(I)
    $
    for every instance $I$ of $Pi$. Here $A(I)$ is $A$'s output and $"OPT"(I)$ the optimal value.
  ]

  #pause

  #definition[
    An algorithm $A$ for a *maximisation* problem $Pi$ is an *$f$-approximation* for $Pi$ if
    $
      A(I) >= f dot "OPT"(I)
    $
    for every instance $I$ of $Pi$. (Naturally $f <= 1$.)
    #h(1fr)
    #tr[(Somitimes we say $f' dot A(I) >= "OPT"(I)$ with $f'=1\/f >= 1$)]
  ]

  #pause

  #remark[
    We don't define $A(I) <= "OPT"(I) + f$ because "hardly any problems will satisfy this."
  ]
]

#pagebreak()
#[
  #set align(horizon)
  #set text(size: 0.9em)

  *Back to $k$-centre.* It is a *minimisation* problem, so:
  - $I$ = an instance of $k$-centre
  - $"OPT"(I) := min_(S subset.eq [n], |S|=k) max_(i in [n]) d(i, S)$

  #pause

  #theorem[
    *Proposition:* The greedy algorithm is a *$2$-approximation* for the $k$-centre problem.
  ]

  #pause

  That is: if $S$ is the greedy output ($|S|=k$), then
  $
    max_(i in [n]) d(i, S) <= 2 dot "OPT"(I).
  $
  #pause

  *Two messages:*
  1. The greedy gives a solution at most *twice* the optimal radius.
  2. *No polynomial-time algorithm can do better* (unless P = NP) --- we will not prove this.
]

= Proof of 2-Approximation

== Proof Setup
#[
  #set align(horizon)
  #set text(size: 0.88em)

  Let $S^* = {j_1, j_2, ..., j_k} subset.eq [n]$ be an *optimal solution* and
  $
    r^* := max_(i in [n]) d(i, S^*) quad "-- the optimal" bold("radius") "of" S^*.
  $

  #pause

  $S^*$ induces a *partition* $V_1 union V_2 union ... union V_k = [n]$:
  - Place $ell in [n]$ in $V_i$ if among ${j_1,...,j_k}$ it is closest to $j_i$ (break ties arbitrarily).

  #place(top + right, dx: -2%, dy: 10%,
    cetz-canvas({
      import cetz.draw: *
      // V1
      circle((1,2), radius:1.1, fill:blue.lighten(88%), stroke:(paint:blue.darken(30%), thickness:0.8pt))
      content((1,0.7), text(size:0.75em, fill:blue.darken(40%))[$V_1$])
      circle((1,2), radius:0.18, fill:blue.darken(40%), stroke:none)
      content((1.3,2.2), text(size:0.7em)[$j_1$])
      for (px,py) in ((0.4,1.5),(1.5,2.5),(0.7,2.6),(1.3,1.4)) {
        circle((px,py), radius:0.1, fill:blue.darken(20%), stroke:none)
      }
      // V2
      circle((3.5,2), radius:1.0, fill:green.lighten(88%), stroke:(paint:green.darken(30%), thickness:0.8pt))
      content((3.5,0.8), text(size:0.75em, fill:green.darken(40%))[$V_2$])
      circle((3.5,2), radius:0.18, fill:green.darken(40%), stroke:none)
      content((3.8,2.2), text(size:0.7em)[$j_2$])
      for (px,py) in ((3.0,1.5),(4.1,2.5),(3.8,1.4)) {
        circle((px,py), radius:0.1, fill:green.darken(20%), stroke:none)
      }
      // V3
      circle((2.2,4), radius:0.9, fill:red.lighten(88%), stroke:(paint:red.darken(30%), thickness:0.8pt))
      content((2.2,2.9), text(size:0.75em, fill:red.darken(40%))[$V_3$])
      circle((2.2,4), radius:0.18, fill:red.darken(40%), stroke:none)
      content((2.5,4.1), text(size:0.7em)[$j_3$])
      for (px,py) in ((1.7,3.5),(2.7,4.4),(1.9,4.3)) {
        circle((px,py), radius:0.1, fill:red.darken(20%), stroke:none)
      }
    })
  )

  #pause

  #observation[
    Let $i in [k]$ and $x, y in V_i$. Then $d_(x y) <= 2r^*$.

    *Proof:* $d_(x y) <= d_(x j_i) + d_(j_i y) <= r^* + r^* = 2r^*.$ $quad square$
  ]

  #place(
  top + left,
  dx: 50% + 6cm,
  dy: 9.5cm,
  figure(image("figures/Clustring1.png", width: 22%)),
  )

  #pause

  Let $S_+ = {s_1,...,s_k}$ be the *greedy output*. Set $r := max_(i in [n]) d(i, S_+)$ (radius of $S_+$).

  

  *Current goal:* $r <= 2r^*$.
]

== Two Cases
#[
  #set align(horizon)
  #set text(size: 0.88em)

  We consider two cases based on how the greedy centres $S_+$ interact with the optimal partition:

  #table(
    columns: (1fr, 1fr),
    stroke: none,
    align: top,
    [
      *Case 1:* $|S_+ inter V_i| = 1$ for all $i in [k]$.

      Each partition class contains *exactly one* greedy centre.
      By the observation, for any $ell in [n]$ lying in $V_i$:
      $
        d(ell, S_+) <= d(ell, s_i) <= 2r^*
      $
      where $s_i in S_+ inter V_i$. 
      #h(1fr) #tr[(Since $ell, s_i in V_i$ implies $d(ell, s_i) <= 2r^*$.)]

      *Done!* $r <= 2r^*$. $square$

      #place(
      top + left,
      dx: 30% + 1cm,
      dy: 5.5cm,
      figure(image("figures/Clustring1.png", width: 55%)),
      )
    ],
    [
      #pause
      *Case 2:* $exists i in [k]$ s.t. $|S_+ inter V_i| >= 2$.

      Some $V_i$ contains *two* greedy centres; call them $s, s'$ (WLOG $s$ was chosen first).

      #v(5pt)
      By the observation: $d_(s s') <= 2r^*$ (since $s, s' in V_i$).

      #v(5pt)
      When $s'$ was chosen, $s$ was *already in $S_+$*. The greedy picks the *farthest* point from the current $S_+$, so at that moment every other point $p$ satisfies:
      $
        d(p, S_+) <= d(s', S^*_+) <= d_(s s') <= 2r^*,
      $
      where $S^*_+$ is $S_+$ at the moment before $s'$ was added to it. 

      Hence $r = max_(i in [n]) d(i, S_+) <= 2r^*.$ $square$
    ],
  )
]

= The $k$-Suppliers Problem

== Setup and Algorithm
#[
  #set align(horizon)
  #set text(size: 0.88em)

  #table(
    columns: (1fr, 1fr),
    stroke: none,
    align: top,
    [
      #problem[
        *The $k$-Suppliers Problem*

        *Given:* $[n] = A union B$, $k in NN$, $|A| >= k$.
        - $A$ = *suppliers* (facilities)
        - $B$ = *clients*

        *Find:* $S subset.eq A$, $|S| = k$, minimising
        $
          max_(b in B) d(b, S)
        $
      ]
      #pause
      For each client $b in B$, let $a_b in A$ be the *nearest supplier* to $b$.

      #pause
      *The Algorithm:*
      1. Apply the $k$-centre $2$-approx to $B$. Let $S' subset.eq B$ be the output.
      2. Return $S := {a_b : b in S'}$. #h(1fr) #tr([If $|S|<k$ add arbitrarily \ #h(1fr) suppliers])
    ],
    [
      #pause
      #cetz-canvas({
        import cetz.draw: *
        set-style(stroke: (thickness: 0.7pt))
        // Supplier row (O)
        let sup = (0.5, 1.5, 2.5, 3.5, 4.5, 5.5)
        for x in sup {
          circle((x, 3.5), radius: 0.18, fill: rgb("#073749"), stroke: none)
        }
        content((-0.3, 3.5), text(weight:"bold")[$A$])
        // Client row (B)
        let cli = (0.2, 1.0, 2.0, 2.8, 3.8, 4.8, 5.8)
        for x in cli {
          rect((x - 0.15, 0.85), (x + 0.15, 1.15), fill: orange.lighten(30%), stroke: (paint: orange.darken(20%)))
        }
        content((-0.3, 1.0), text(weight:"bold")[$B$])
        // Selected S' clients (circled in red)
        for x in (1.0, 3.8, 5.8) {
          circle((x, 1.0), radius: 0.28, fill: none, stroke: (paint: red, thickness: 1.3pt))
          content((x, 0.4), text(size:0.7em, fill:red)[$S'$])
        }
        // Map a_b: nearest supplier
        line((1.0, 1.15), (1.5, 3.32), stroke:(paint:red, dash:"dashed"))
        line((3.8, 1.15), (3.5, 3.32), stroke:(paint:red, dash:"dashed"))
        line((5.8, 1.15), (5.5, 3.32), stroke:(paint:red, dash:"dashed"))
        // Highlight selected suppliers
        for x in (1.5, 3.5, 5.5) {
          circle((x, 3.5), radius: 0.28, fill: none, stroke: (paint: red, thickness: 1.3pt))
        }
        content((3.0, 4.2), text(size:0.8em, fill:red)[$S = {a_b : b in S'}$])
      })
    ],
  )
]

#pagebreak()
#[
  #set align(horizon)
  #set text(size: 0.88em)

  #theorem[
    *Proposition:* The above algorithm is a *$3$-approximation* for the $k$-suppliers problem.
  ]

  #pause

  *Proof.* Let $r^* = min_(S subset.eq A, |S|=k) max_(b in B) d(b,S)$. Fix any $b in B$; let $b' in S'$ be its nearest greedy centre.

  #pause

  #claim[
    For every $b in B$: $d(b, S') <= 2r^*$. #h(1fr) _(proved on next slide)_
  ]

  #pause

  Since $a_(b')$ is the nearest supplier to $b'$ and OPT covers every client within $r^*$:
  $d(b', a_(b')) <= r^*.$

        #place(
      top + left,
      dx: 70% + 1cm,
      dy: 6.1cm,
      figure(image("figures/Clustring2.png", width: 27%)),
      )

  #pause

  By the triangle inequality and the claim:
  $
    d(b, a_(b')) <= underbrace(d(b, b'), <= 2r^*) + underbrace(d(b', a_(b')), <= r^*) <= 3r^*. quad square
  $

  #pause
  #v(25pt)
  #remark[
    One can show that no polynomial-time $f$-approximation with $f < 3$ exists for $k$-suppliers (unless $P = N P$).
  ]
]

#pagebreak()
#[
  #set align(horizon)
  #set text(size: 0.88em)

  #claim[
    For every $b in B$: $d(b, S') <= 2r^*$.
  ]

  *Proof (by contradiction).* Suppose $d(b, S') > 2r^*$ for some $b in B$.

  #pause

  - $b in.not S'$ (else $d(b,S')=0$).
  - When each $b'_j in S'$ was selected, greedy chose the *farthest* point, so:
    $d(b'_j, S'_(j-1)) >= d(b, S'_(j-1)) >= d(b, S') > 2r^*.$
  - Hence *every pair* in $S' union {b}$ is $> 2r^*$ apart — a set of $k+1$ points.

  #pause

  The optimal solution uses only $k$ suppliers. By *pigeonhole*, two points $u, v in S' union {b}$ share the same nearest supplier $a in A$:
  $
    d(u,v) <= d(u,a) + d(a,v) <= r^* + r^* = 2r^*.
  $
  But $d(u,v) > 2r^*$ -- #text(fill: red)[*contradiction*]. $quad square$
]
