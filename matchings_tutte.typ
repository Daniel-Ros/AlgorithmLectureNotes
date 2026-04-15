#import "settings/mstyle.typ": *
#import algorithmic: algorithm-figure, style-algorithm
#show: style-algorithm



#show: conf.with(handout: true, subtitle: [Matching in graphs])

#title-slide()

= Tutte's Theorem
== Perfect Matchings
#block(fill: blue.lighten(80%), inset: 20pt, radius: 1em)[
  #set align(center)
  *For bipartite graphs $G:=(A cup.dot B, E)$*\
  #table(
    columns: (1fr, 0.1fr, 1fr),
    align: (center, horizon, center),
    stroke: none,
    [$G$ has a perfect \ matching ], [$<==>$], [$|A| = |B|$\ and $A$ satisfoes the \ Hall-Condition],
  )
]
#question[
  what if $G$ is not bipartite?
]
#pause
#goal[
  Find a necessary & sufficient condition for the emergence of perfect matchings in _general_ graphs.
]

== Removing vertices from graphs
#v(30pt)
- $G$ graph and $S subset.eq V(G)$
- $G-S :=$ the graph obtained by removing the vertices $S$ in $G$.
  - $G-S$ is a sub-graph of $G$.

#place(
  top + left,
  dx: 5cm,
  dy: 5cm,
  cetz-canvas({
    import cetz.draw: *

    for i in range(0, 6) {
      circle((calc.cos(i) * 3, calc.sin(i) * 3), fill: black, radius: 3pt, name: "l" + str(i))
      circle((calc.cos(i) * 0.8, calc.sin(i) * 0.8), fill: black, radius: 3pt, name: "o" + str(i))
    }
    for i in range(0, 3) {
      circle((calc.cos(i * 2) * 2.2, calc.sin(i * 2) * 2.2), fill: red, radius: 3pt, name: "r" + str(i))
    }

    circle((3, 1.5), fill: black, radius: 3pt, name: "t0")
    circle((2.5, 2.2), fill: black, radius: 3pt, name: "t1")

    line("o0", "o3", stroke: black + 2pt)
    line("t0", "t1", stroke: black + 2pt)
    line("r0", "t1", stroke: red + 2pt)
    for i in range(0, 6) {
      for j in range(-1, 0) {
        let t = calc.rem(calc.rem(i * 2 + j, 3) + 3, 3)
        line("l" + str(i), "r" + str(t), stroke: red + 2pt)
        line("o" + str(i), "r" + str(t), stroke: red.darken(30%) + 2pt)
      }
      // line("r" + str(i), "o2", stroke: red + 2pt)
      // line("r" + str(i), "r" + str(calc.rem(i + 1, 3)), stroke: red + 2pt)
      line("l" + str(i), "l" + str(calc.rem(i + 1, 6)), stroke: black + 2pt)
      line("l" + str(i), "l" + str(calc.rem(i + 1, 6)), stroke: black + 2pt)
    }

    for i in range(0, 3) {
      line("r" + str(i), "o1", stroke: red + 2pt)
      line("r" + str(i), "o2", stroke: red + 2pt)
      line("r" + str(i), "r" + str(calc.rem(i + 1, 3)), stroke: red + 2pt)
    }
    // line("l" + str(1), "r" + str(7), stroke: black + 2pt)
    // line("l" + str(1), "r" + str(i + j), stroke: black + 2pt)
  }),
)


#place(
  top + left,
  dx: 12cm,
  dy: 7cm,
  [
    #set text(size: 2em)
    $==>$
  ],
)

#place(
  top + left,
  dx: 15cm,
  dy: 5cm,
  cetz-canvas({
    import cetz.draw: *

    for i in range(0, 6) {
      circle((calc.cos(i) * 3, calc.sin(i) * 3), fill: black, radius: 3pt, name: "l" + str(i))
      circle((calc.cos(i) * 0.8, calc.sin(i) * 0.8), fill: black, radius: 3pt, name: "o" + str(i))
      // circle((calc.cos(i + 0.44) * 1.5, calc.sin(i  + 0.44) * 1.5),fill: red, radius: 3pt, name: "r" + str(i))
    }
    circle((3, 1.5), fill: black, radius: 3pt, name: "t0")
    circle((2.5, 2.2), fill: black, radius: 3pt, name: "t1")

    line("o0", "o3", stroke: black + 2pt)
    line("t0", "t1", stroke: black + 2pt)
    for i in range(0, 6) {
      // for j in range(-1,1){
      //   let t = calc.rem(calc.rem(i + j, 6) + 6, 6)
      //   line("l" + str(i), "r" + str(t), stroke: red + 2pt)
      // }

      // line("r" + str(i), "r" + str(calc.rem(i + 1, 6)), stroke: red + 2pt)
      line("l" + str(i), "l" + str(calc.rem(i + 1, 6)), stroke: black + 2pt)
      line("l" + str(i), "l" + str(calc.rem(i + 1, 6)), stroke: black + 2pt)
    }

    // line("l" + str(1), "r" + str(7), stroke: black + 2pt)
    // line("l" + str(1), "r" + str(i + j), stroke: black + 2pt)
  }),
)

== Removing vertices from graphs
#v(40pt)
- We can break the graph into the set $S$ and the connected componnents of $G-S$.
- *No edges between connected componenets*
#place(
  top + left,
  dx: 1cm,
  dy: 3.5cm,
  cetz-canvas({
    import cetz.draw: *

    for i in range(0, 6) {
      circle((calc.cos(i) * 3, calc.sin(i) * 3), fill: black, radius: 3pt, name: "l" + str(i))
      circle((calc.cos(i) * 0.8, calc.sin(i) * 0.8), fill: black, radius: 3pt, name: "o" + str(i))
    }
    for i in range(0, 3) {
      circle((calc.cos(i * 2) * 2.2, calc.sin(i * 2) * 2.2), fill: red, radius: 3pt, name: "r" + str(i))
    }

    circle((3, 1.5), fill: black, radius: 3pt, name: "t0")
    circle((2.5, 2.2), fill: black, radius: 3pt, name: "t1")

    line("o0", "o3", stroke: black + 2pt)
    line("t0", "t1", stroke: black + 2pt)
    line("r0", "t1", stroke: red + 2pt)
    for i in range(0, 6) {
      for j in range(-1, 0) {
        let t = calc.rem(calc.rem(i * 2 + j, 3) + 3, 3)
        line("l" + str(i), "r" + str(t), stroke: red + 2pt)
        line("o" + str(i), "r" + str(t), stroke: red.darken(30%) + 2pt)
      }
      // line("r" + str(i), "o2", stroke: red + 2pt)
      // line("r" + str(i), "r" + str(calc.rem(i + 1, 3)), stroke: red + 2pt)
      line("l" + str(i), "l" + str(calc.rem(i + 1, 6)), stroke: black + 2pt)
      line("l" + str(i), "l" + str(calc.rem(i + 1, 6)), stroke: black + 2pt)
    }

    for i in range(0, 3) {
      line("r" + str(i), "o1", stroke: red + 2pt)
      line("r" + str(i), "o2", stroke: red + 2pt)
      line("r" + str(i), "r" + str(calc.rem(i + 1, 3)), stroke: red + 2pt)
    }
    // line("l" + str(1), "r" + str(7), stroke: black + 2pt)
    // line("l" + str(1), "r" + str(i + j), stroke: black + 2pt)
  }),
)

#place(
  top + left,
  dx: 10cm,
  dy: 6cm,
  [
    #set text(size: 2em)
    $==>$
  ],
)

#place(
  top + left,
  dx: 13cm,
  dy: 3.5cm,
  cetz-canvas({
    import cetz.draw: *


    for i in range(0, 6) {
      circle((i * 0.5, calc.rem(i, 2)), fill: black, radius: 3pt, name: "l" + str(i))
      circle((i * 1.25 + 6, 0), fill: black, radius: 3pt, name: "o" + str(i))
    }


    for i in range(0, 3) {
      circle((calc.cos(i + 0.44) * 1.5 + 6, calc.sin(i + 0.44) * 1.5 - 6), fill: red, radius: 3pt, name: "r" + str(i))
    }
    circle((4.5, 0.3), fill: black, radius: 3pt, name: "t0")
    circle((4, 1), fill: black, radius: 3pt, name: "t1")

    rect-around("l0", "l5", padding: (0.2, 0.2, 0.2, 0.2), radius: 0.1, stroke: none, fill: green.lighten(90%))
    rect-around("t0", "t1", padding: (0.2, 0.2, 0.2, 0.2), radius: 0.1, stroke: none, fill: green.lighten(90%))
    rect-around("o0", "o1", padding: (0.2, 0.2, 0.2, 0.2), radius: 0.1, stroke: none, fill: green.lighten(90%))
    rect-around("r0", "r2", padding: (1, 0.2, 0.2, 0.2), radius: 0.1, stroke: none, fill: gray.lighten(90%))
    for i in range(2, 6) {
      rect-around(
        "o" + str(i),
        "o" + str(i),
        stroke: none,
        padding: (0.2, 0.2, 0.2, 0.2),
        radius: 0.1,
        fill: red.lighten(50%),
      )
    }


    for i in range(0, 6) {
      circle((i * 0.5, calc.rem(i, 2)), fill: black, radius: 3pt, name: "l" + str(i))
      circle((i * 1.25 + 6, 0), fill: black, radius: 3pt, name: "o" + str(i))
    }

    for i in range(0, 3) {
      circle((calc.cos(i + 0.44) * 1.5 + 6, calc.sin(i + 0.44) * 1.5 - 6), fill: red, radius: 3pt, name: "r" + str(i))
    }
    circle((4.5, 0.3), fill: black, radius: 3pt, name: "t0")
    circle((4, 1), fill: black, radius: 3pt, name: "t1")


    line("o0", "o1", stroke: black + 2pt)
    line("t0", "t1", stroke: black + 2pt)
    line("r0", "t1", stroke: red + 2pt)
    for i in range(0, 6) {
      for j in range(-1, 0) {
        let t = calc.rem(calc.rem(i * 2 + j, 3) + 3, 3)
        line("l" + str(i), "r" + str(t), stroke: red + 2pt)
        line("o" + str(i), "r" + str(t), stroke: red.darken(30%) + 2pt)
      }
      // line("r" + str(i), "o2", stroke: red + 2pt)
      // line("r" + str(i), "r" + str(calc.rem(i + 1, 3)), stroke: red + 2pt)
      line("l" + str(i), "l" + str(calc.rem(i + 1, 6)), stroke: black + 2pt)
      line("l" + str(i), "l" + str(calc.rem(i + 1, 6)), stroke: black + 2pt)
    }

    for i in range(0, 3) {
      line("r" + str(i), "o1", stroke: red + 2pt)
      line("r" + str(i), "o2", stroke: red + 2pt)
      line("r" + str(i), "r" + str(calc.rem(i + 1, 3)), stroke: red + 2pt)
    }

    // line("l" + str(1), "r" + str(7), stroke: black + 2pt)
    // line("l" + str(1), "r" + str(i + j), stroke: black + 2pt)
  }),
)
#pause
#place(
  top + left,
  dx: 15cm,
  dy: 11.8cm,
  [
    #set text(size: 1em)
    No perfect matching,
    there is $4$ componenets, \
    with odd number of vertices. \
    But $S$ can only "give" at most $3$ vertices.
  ],
)



#place(
  top + left,
  dx: 17.5cm,
  dy: 10.5cm,
  [
    #set text(size: 1em)
    $
      underbracket(#h(100pt), #[S])
    $
  ],
)

#place(
  top + left,
  dx: 21.5cm,
  dy: 3.8cm,
  [
    #set text(size: 1em)
    $
      overbracket(#h(120pt), #[Odd componenets])
    $
  ],
)

#place(
  top + left,
  dx: 13cm,
  dy: 2.8cm,
  [
    #set text(size: 1em)
    $
      overbracket(#h(220pt), #[Even componenets])
    $
  ],
)

#let co = "Co"
== Conclusion
#[
  #set text(size: 1.1em)
  #v(20pt)
  - Let $G$ be a graph.

  - $co(G-S):=$ number of odd components in $G-S$.

  - If $exists S subset.eq V(G)$ s.t. $co(G-S) > |S|$
    - $G$ has no perfect matching
]
#place(
  top + left,
  dx: 0cm,
  dy: 0.5cm,
  [
    #place(
      top + left,
      dx: 13cm,
      dy: 3.5cm,
      cetz-canvas({
        import cetz.draw: *


        for i in range(0, 6) {
          circle((i * 0.5, calc.rem(i, 2)), fill: black, radius: 3pt, name: "l" + str(i))
          circle((i * 1.25 + 6, 0), fill: black, radius: 3pt, name: "o" + str(i))
        }


        for i in range(0, 3) {
          circle(
            (calc.cos(i + 0.44) * 1.5 + 6, calc.sin(i + 0.44) * 1.5 - 6),
            fill: red,
            radius: 3pt,
            name: "r" + str(i),
          )
        }
        circle((4.5, 0.3), fill: black, radius: 3pt, name: "t0")
        circle((4, 1), fill: black, radius: 3pt, name: "t1")

        rect-around("l0", "l5", padding: (0.2, 0.2, 0.2, 0.2), radius: 0.1, stroke: none, fill: green.lighten(90%))
        rect-around("t0", "t1", padding: (0.2, 0.2, 0.2, 0.2), radius: 0.1, stroke: none, fill: green.lighten(90%))
        rect-around("o0", "o1", padding: (0.2, 0.2, 0.2, 0.2), radius: 0.1, stroke: none, fill: green.lighten(90%))
        rect-around("r0", "r2", padding: (1, 0.2, 0.2, 0.2), radius: 0.1, stroke: none, fill: gray.lighten(90%))
        for i in range(2, 6) {
          rect-around(
            "o" + str(i),
            "o" + str(i),
            stroke: none,
            padding: (0.2, 0.2, 0.2, 0.2),
            radius: 0.1,
            fill: red.lighten(50%),
          )
        }


        for i in range(0, 6) {
          circle((i * 0.5, calc.rem(i, 2)), fill: black, radius: 3pt, name: "l" + str(i))
          circle((i * 1.25 + 6, 0), fill: black, radius: 3pt, name: "o" + str(i))
        }

        for i in range(0, 3) {
          circle(
            (calc.cos(i + 0.44) * 1.5 + 6, calc.sin(i + 0.44) * 1.5 - 6),
            fill: red,
            radius: 3pt,
            name: "r" + str(i),
          )
        }
        circle((4.5, 0.3), fill: black, radius: 3pt, name: "t0")
        circle((4, 1), fill: black, radius: 3pt, name: "t1")


        line("o0", "o1", stroke: black + 2pt)
        line("t0", "t1", stroke: black + 2pt)
        line("r0", "t1", stroke: red + 2pt)
        for i in range(0, 6) {
          for j in range(-1, 0) {
            let t = calc.rem(calc.rem(i * 2 + j, 3) + 3, 3)
            line("l" + str(i), "r" + str(t), stroke: red + 2pt)
            line("o" + str(i), "r" + str(t), stroke: red.darken(30%) + 2pt)
          }
          // line("r" + str(i), "o2", stroke: red + 2pt)
          // line("r" + str(i), "r" + str(calc.rem(i + 1, 3)), stroke: red + 2pt)
          line("l" + str(i), "l" + str(calc.rem(i + 1, 6)), stroke: black + 2pt)
          line("l" + str(i), "l" + str(calc.rem(i + 1, 6)), stroke: black + 2pt)
        }

        for i in range(0, 3) {
          line("r" + str(i), "o1", stroke: red + 2pt)
          line("r" + str(i), "o2", stroke: red + 2pt)
          line("r" + str(i), "r" + str(calc.rem(i + 1, 3)), stroke: red + 2pt)
        }

        // line("l" + str(1), "r" + str(7), stroke: black + 2pt)
        // line("l" + str(1), "r" + str(i + j), stroke: black + 2pt)
      }),
    )

    #place(
      top + left,
      dx: 21.5cm,
      dy: 3.8cm,
      [
        #set text(size: 1em)
        $
          overbracket(#h(120pt), #[Odd componenets])
        $
      ],
    )

    #place(
      top + left,
      dx: 13cm,
      dy: 2.8cm,
      [
        #set text(size: 1em)
        $
          overbracket(#h(220pt), #[Even componenets])
        $
      ],
    )

    #place(
      top + left,
      dx: 17.5cm,
      dy: 10.5cm,
      [
        #set text(size: 1em)
        $
          underbracket(#h(100pt), #[S])
        $
      ],
    )
  ],
)


#let tutte = theorem(title: "Tutte's")[Let $$ be a graph.
  Then,
  $
    #[$G$ has a p.m] #h(20pt) arrow.r.l.long.double #h(20pt)
    underbracket(#[$|co(G-S)| <= |S|, forall S subset.eq V(G))$], #[Tutte's Condition])
  $
]

== Tutte's Theorem
#[
  #v(20pt)
  - $co(G-S):=$ number of odd components in $G-S$.
  #tutte
  #v(-5pt)
  We already proven $==>$
  #remark[
    A graph satisfying $ |co(G-S)| <= |S|, forall S subset.eq A. $
    Is said to satisfy the Tutte's condition.
  ]
]

= General Proof Idea
== General Proof Idea
#[
  #set align(horizon)
  #set text(size: 1.5em)

  - Suppose the claim is false.
    - $G$ satisfies Tutte's condition and has no perfect matching.
  - Let $G$ be "edge-maximal" example of such a graph.
    - *What does $G$ looks like? What are the properties of such a graph?*
]

== Edge Maxmimal Counter Example
#observation[
  - $G$ satisfying the tutte condition
  - $e$ an edge not in $G$
  Then, $G' := G+e$ also satisfies the tutte's condition.
]
*Proof.* Fix $S subset.eq V(G)$ and show that for any edge $co(G-S + e) <= |S|$.

#pagebreak()
#[
  #v(50pt)
  - if #text(fill: purple)[$e$ is an edge] that resides inside any component. inside of $S$, or between $S$ and any component.
    - Then, there is no change $co(G-S + e) = co(G-S) <= |S|$.

]
#place(
  top + left,
  dx: -0cm,
  dy: 1.5cm,
  scale(x: 110%, y: 110%)[
    #place(
      top + left,
      dx: 13cm,
      dy: 3.5cm,
      cetz-canvas({
        import cetz.draw: *


        for i in range(0, 6) {
          circle((i * 0.5, calc.rem(i, 2)), fill: black, radius: 3pt, name: "l" + str(i))
        }

        for i in range(0, 5) {
          circle((i * 1.25 + 6, 0), fill: black, radius: 3pt, name: "o" + str(i))
        }


        for i in range(0, 3) {
          circle(
            (calc.cos(i + 0.44) * 1.5 + 6, calc.sin(i + 0.44) * 1.5 - 4),
            fill: red,
            radius: 3pt,
            name: "r" + str(i),
          )
        }
        circle((4.5, 0.3), fill: black, radius: 3pt, name: "t0")
        circle((4, 1), fill: black, radius: 3pt, name: "t1")

        rect-around("l0", "l5", padding: (0.2, 0.2, 0.2, 0.2), radius: 0.1, stroke: none, fill: green.lighten(90%))
        rect-around("t0", "t1", padding: (0.2, 0.2, 0.2, 0.2), radius: 0.1, stroke: none, fill: green.lighten(90%))
        rect-around("o0", "o1", padding: (0.2, 0.2, 0.2, 0.2), radius: 0.1, stroke: none, fill: green.lighten(90%))
        rect-around("r0", "r2", padding: (1, 0.2, 0.2, 0.2), radius: 0.1, stroke: none, fill: gray.lighten(90%))
        for i in range(2, 5) {
          rect-around(
            "o" + str(i),
            "o" + str(i),
            stroke: none,
            padding: (0.2, 0.2, 0.2, 0.2),
            radius: 0.1,
            fill: red.lighten(50%),
          )
        }


        for i in range(0, 6) {
          circle((i * 0.5, calc.rem(i, 2)), fill: black, radius: 3pt, name: "l" + str(i))
        }

        for i in range(0, 5) {
          circle((i * 1.25 + 6, 0), fill: black, radius: 3pt, name: "o" + str(i))
        }

        for i in range(0, 3) {
          circle(
            (calc.cos(i + 0.44) * 1.5 + 6, calc.sin(i + 0.44) * 1.5 - 4),
            fill: red,
            radius: 3pt,
            name: "r" + str(i),
          )
        }
        circle((4.5, 0.3), fill: black, radius: 3pt, name: "t0")
        circle((4, 1), fill: black, radius: 3pt, name: "t1")


        line("o0", "o1", stroke: black + 2pt)
        line("t0", "t1", stroke: black + 2pt)
        line("r0", "t1", stroke: red + 2pt)
        for i in range(0, 6) {
          for j in range(0, 1) {
            if calc.rem(i * 2 + j, 3) != 0 {
              continue
            }
            let t = calc.rem(calc.rem(i * 2 + j, 3) + 3, 3)
            line("l" + str(i), "r" + str(t), stroke: red + 2pt)
            line("o" + str(i), "r" + str(t), stroke: red.darken(30%) + 2pt)
          }
          // line("r" + str(i), "o2", stroke: red + 2pt)
          // line("r" + str(i), "r" + str(calc.rem(i + 1, 3)), stroke: red + 2pt)
          line("l" + str(i), "l" + str(calc.rem(i + 1, 6)), stroke: black + 2pt)
          line("l" + str(i), "l" + str(calc.rem(i + 1, 6)), stroke: black + 2pt)
        }

        for i in range(0, 2) {
          line("r" + str(i), "o1", stroke: red + 2pt)
          line("r" + str(i), "o2", stroke: red + 2pt)
          line("r" + str(i), "r" + str(calc.rem(i + 1, 3)), stroke: red + 2pt)
        }

        line("l0", "l3", stroke: purple + 3pt)
        line("r0", "r2", stroke: purple + 3pt)
        line("r0", "o4", stroke: purple + 3pt)
        // line("l" + str(1), "r" + str(7), stroke: black + 2pt)
        // line("l" + str(1), "r" + str(i + j), stroke: black + 2pt)
      }),
    )

    #place(
      top + left,
      dx: 21.3cm,
      dy: 3.8cm,
      [
        #set text(size: 1em)
        $
          overbracket(#h(100pt), #[Odd componenets])
        $
      ],
    )

    #place(
      top + left,
      dx: 13cm,
      dy: 2.8cm,
      [
        #set text(size: 1em)
        $
          overbracket(#h(220pt), #[Even componenets])
        $
      ],
    )

    #place(
      top + left,
      dx: 17.6cm,
      dy: 8.3cm,
      [
        #set text(size: 1em)
        $
          underbracket(#h(100pt), #[S])
        $
      ],
    )
  ],
)


#place(
  top + left,
  dx: -15cm,
  dy: 1.5cm,
  scale(x: 110%, y: 110%)[
    #place(
      top + left,
      dx: 13cm,
      dy: 3.5cm,
      cetz-canvas({
        import cetz.draw: *


        for i in range(0, 6) {
          circle((i * 0.5, calc.rem(i, 2)), fill: black, radius: 3pt, name: "l" + str(i))
        }

        for i in range(0, 5) {
          circle((i * 1.25 + 6, 0), fill: black, radius: 3pt, name: "o" + str(i))
        }


        for i in range(0, 3) {
          circle(
            (calc.cos(i + 0.44) * 1.5 + 6, calc.sin(i + 0.44) * 1.5 - 4),
            fill: red,
            radius: 3pt,
            name: "r" + str(i),
          )
        }
        circle((4.5, 0.3), fill: black, radius: 3pt, name: "t0")
        circle((4, 1), fill: black, radius: 3pt, name: "t1")

        rect-around("l0", "l5", padding: (0.2, 0.2, 0.2, 0.2), radius: 0.1, stroke: none, fill: green.lighten(90%))
        rect-around("t0", "t1", padding: (0.2, 0.2, 0.2, 0.2), radius: 0.1, stroke: none, fill: green.lighten(90%))
        rect-around("o0", "o1", padding: (0.2, 0.2, 0.2, 0.2), radius: 0.1, stroke: none, fill: green.lighten(90%))
        rect-around("r0", "r2", padding: (1, 0.2, 0.2, 0.2), radius: 0.1, stroke: none, fill: gray.lighten(90%))
        for i in range(2, 5) {
          rect-around(
            "o" + str(i),
            "o" + str(i),
            stroke: none,
            padding: (0.2, 0.2, 0.2, 0.2),
            radius: 0.1,
            fill: red.lighten(50%),
          )
        }


        for i in range(0, 6) {
          circle((i * 0.5, calc.rem(i, 2)), fill: black, radius: 3pt, name: "l" + str(i))
        }

        for i in range(0, 5) {
          circle((i * 1.25 + 6, 0), fill: black, radius: 3pt, name: "o" + str(i))
        }

        for i in range(0, 3) {
          circle(
            (calc.cos(i + 0.44) * 1.5 + 6, calc.sin(i + 0.44) * 1.5 - 4),
            fill: red,
            radius: 3pt,
            name: "r" + str(i),
          )
        }
        circle((4.5, 0.3), fill: black, radius: 3pt, name: "t0")
        circle((4, 1), fill: black, radius: 3pt, name: "t1")


        line("o0", "o1", stroke: black + 2pt)
        line("t0", "t1", stroke: black + 2pt)
        line("r0", "t1", stroke: red + 2pt)
        for i in range(0, 6) {
          for j in range(0, 1) {
            if calc.rem(i * 2 + j, 3) != 0 {
              continue
            }
            let t = calc.rem(calc.rem(i * 2 + j, 3) + 3, 3)
            line("l" + str(i), "r" + str(t), stroke: red + 2pt)
            line("o" + str(i), "r" + str(t), stroke: red.darken(30%) + 2pt)
          }
          // line("r" + str(i), "o2", stroke: red + 2pt)
          // line("r" + str(i), "r" + str(calc.rem(i + 1, 3)), stroke: red + 2pt)
          line("l" + str(i), "l" + str(calc.rem(i + 1, 6)), stroke: black + 2pt)
          line("l" + str(i), "l" + str(calc.rem(i + 1, 6)), stroke: black + 2pt)
        }

        for i in range(0, 2) {
          line("r" + str(i), "o1", stroke: red + 2pt)
          line("r" + str(i), "o2", stroke: red + 2pt)
          line("r" + str(i), "r" + str(calc.rem(i + 1, 3)), stroke: red + 2pt)
        }

        // line("l" + str(1), "r" + str(7), stroke: black + 2pt)
        // line("l" + str(1), "r" + str(i + j), stroke: black + 2pt)
      }),
    )

    #place(
      top + left,
      dx: 21.3cm,
      dy: 3.8cm,
      [
        #set text(size: 1em)
        $
          overbracket(#h(100pt), #[Odd componenets])
        $
      ],
    )

    #place(
      top + left,
      dx: 13cm,
      dy: 2.8cm,
      [
        #set text(size: 1em)
        $
          overbracket(#h(220pt), #[Even componenets])
        $
      ],
    )

    #place(
      top + left,
      dx: 17.6cm,
      dy: 8.3cm,
      [
        #set text(size: 1em)
        $
          underbracket(#h(100pt), #[S])
        $
      ],
    )

  ],
)


#place(
  top + left,
  dx: 12.5cm,
  dy: 8cm,
  [
    #set text(size: 2em)
    #set align(center)
    $==>$ \ #[#set text(fill: purple, size: 0.5em)
      added $e$]],
)

#pagebreak()
#[
  #v(50pt)
  - #text(fill: purple)[$e$ is an edge] with one end inside an #text(fill: green)[even component]:
    - If its between two _even componenets_. Then, we get one big even components instead of two even components so that  $co(G-S + e) = co(G-S) <= |S|$.
    #uncover("2-")[
  - If its between _even and odd components_. Then, we get one big odd components instead of the previous odd and even components so that  $co(G-S + e) = co(G-S) <= |S|$.
    ]
]
#place(
  top + left,
  dx: -0cm,
  dy: 3.5cm,
  scale(x: 110%, y: 110%)[
    #place(
      top + left,
      dx: 13cm,
      dy: 3.5cm,
      cetz-canvas({
        import cetz.draw: *


        for i in range(0, 6) {
          circle((i * 0.5, calc.rem(i, 2)), fill: black, radius: 3pt, name: "l" + str(i))
        }

        for i in range(0, 5) {
          circle((i * 1.25 + 6, 0), fill: black, radius: 3pt, name: "o" + str(i))
        }


        for i in range(0, 3) {
          circle(
            (calc.cos(i + 0.44) * 1.5 + 6, calc.sin(i + 0.44) * 1.5 - 4),
            fill: red,
            radius: 3pt,
            name: "r" + str(i),
          )
        }
        circle((4.5, 0.3), fill: black, radius: 3pt, name: "t0")
        circle((4, 1), fill: black, radius: 3pt, name: "t1")

        rect-around("l0", "t1", padding: (0.2, 0.2, 0.2, 0.2), radius: 0.1, stroke: none, fill: green.lighten(90%))
        rect-around("t0", "t1", padding: (0.2, 0.2, 0.2, 0.2), radius: 0.1, stroke: none, fill: green.lighten(90%))
        rect-around("o0", "o2", padding: (0.2, 0.2, 0.2, 0.2), radius: 0.1, stroke: none, fill: red.lighten(50%))
        rect-around("r0", "r2", padding: (1, 0.2, 0.2, 0.2), radius: 0.1, stroke: none, fill: gray.lighten(90%))
        for i in range(3, 5) {
          rect-around(
            "o" + str(i),
            "o" + str(i),
            stroke: none,
            padding: (0.2, 0.2, 0.2, 0.2),
            radius: 0.1,
            fill: red.lighten(50%),
          )
        }


        for i in range(0, 6) {
          circle((i * 0.5, calc.rem(i, 2)), fill: black, radius: 3pt, name: "l" + str(i))
        }

        for i in range(0, 5) {
          circle((i * 1.25 + 6, 0), fill: black, radius: 3pt, name: "o" + str(i))
        }

        for i in range(0, 3) {
          circle(
            (calc.cos(i + 0.44) * 1.5 + 6, calc.sin(i + 0.44) * 1.5 - 4),
            fill: red,
            radius: 3pt,
            name: "r" + str(i),
          )
        }
        circle((4.5, 0.3), fill: black, radius: 3pt, name: "t0")
        circle((4, 1), fill: black, radius: 3pt, name: "t1")


        line("o0", "o1", stroke: black + 2pt)
        line("t0", "t1", stroke: black + 2pt)
        line("r0", "t1", stroke: red + 2pt)
        for i in range(0, 6) {
          for j in range(0, 1) {
            if calc.rem(i * 2 + j, 3) != 0 {
              continue
            }
            let t = calc.rem(calc.rem(i * 2 + j, 3) + 3, 3)
            line("l" + str(i), "r" + str(t), stroke: red + 2pt)
            line("o" + str(i), "r" + str(t), stroke: red.darken(30%) + 2pt)
          }
          // line("r" + str(i), "o2", stroke: red + 2pt)
          // line("r" + str(i), "r" + str(calc.rem(i + 1, 3)), stroke: red + 2pt)
          line("l" + str(i), "l" + str(calc.rem(i + 1, 6)), stroke: black + 2pt)
          line("l" + str(i), "l" + str(calc.rem(i + 1, 6)), stroke: black + 2pt)
        }

        for i in range(0, 2) {
          line("r" + str(i), "o1", stroke: red + 2pt)
          line("r" + str(i), "o2", stroke: red + 2pt)
          line("r" + str(i), "r" + str(calc.rem(i + 1, 3)), stroke: red + 2pt)
        }

        line("l5", "t1", stroke: purple + 3pt)
        line("o1", "o2", stroke: purple + 3pt)
        // line("l" + str(1), "r" + str(7), stroke: black + 2pt)
        // line("l" + str(1), "r" + str(i + j), stroke: black + 2pt)
      }),
    )

    #place(
      top + left,
      dx: 19cm,
      dy: 3.8cm,
      [
        #set text(size: 1em)
        $
          overbracket(#h(160pt), #[Odd componenets])
        $
      ],
    )

    #place(
      top + left,
      dx: 13cm,
      dy: 2.8cm,
      [
        #set text(size: 1em)
        $
          overbracket(#h(145pt), #[Even componenets])
        $
      ],
    )

    #place(
      top + left,
      dx: 17.6cm,
      dy: 8.3cm,
      [
        #set text(size: 1em)
        $
          underbracket(#h(100pt), #[S])
        $
      ],
    )
  ],
)


#place(
  top + left,
  dx: -15cm,
  dy: 3.5cm,
  scale(x: 110%, y: 110%)[
    #place(
      top + left,
      dx: 13cm,
      dy: 3.5cm,
      cetz-canvas({
        import cetz.draw: *


        for i in range(0, 6) {
          circle((i * 0.5, calc.rem(i, 2)), fill: black, radius: 3pt, name: "l" + str(i))
        }

        for i in range(0, 5) {
          circle((i * 1.25 + 6, 0), fill: black, radius: 3pt, name: "o" + str(i))
        }


        for i in range(0, 3) {
          circle(
            (calc.cos(i + 0.44) * 1.5 + 6, calc.sin(i + 0.44) * 1.5 - 4),
            fill: red,
            radius: 3pt,
            name: "r" + str(i),
          )
        }
        circle((4.5, 0.3), fill: black, radius: 3pt, name: "t0")
        circle((4, 1), fill: black, radius: 3pt, name: "t1")

        rect-around("l0", "l5", padding: (0.2, 0.2, 0.2, 0.2), radius: 0.1, stroke: none, fill: green.lighten(90%))
        rect-around("t0", "t1", padding: (0.2, 0.2, 0.2, 0.2), radius: 0.1, stroke: none, fill: green.lighten(90%))
        rect-around("o0", "o1", padding: (0.2, 0.2, 0.2, 0.2), radius: 0.1, stroke: none, fill: green.lighten(90%))
        rect-around("r0", "r2", padding: (1, 0.2, 0.2, 0.2), radius: 0.1, stroke: none, fill: gray.lighten(90%))
        for i in range(2, 5) {
          rect-around(
            "o" + str(i),
            "o" + str(i),
            stroke: none,
            padding: (0.2, 0.2, 0.2, 0.2),
            radius: 0.1,
            fill: red.lighten(50%),
          )
        }


        for i in range(0, 6) {
          circle((i * 0.5, calc.rem(i, 2)), fill: black, radius: 3pt, name: "l" + str(i))
        }

        for i in range(0, 5) {
          circle((i * 1.25 + 6, 0), fill: black, radius: 3pt, name: "o" + str(i))
        }

        for i in range(0, 3) {
          circle(
            (calc.cos(i + 0.44) * 1.5 + 6, calc.sin(i + 0.44) * 1.5 - 4),
            fill: red,
            radius: 3pt,
            name: "r" + str(i),
          )
        }
        circle((4.5, 0.3), fill: black, radius: 3pt, name: "t0")
        circle((4, 1), fill: black, radius: 3pt, name: "t1")


        line("o0", "o1", stroke: black + 2pt)
        line("t0", "t1", stroke: black + 2pt)
        line("r0", "t1", stroke: red + 2pt)
        for i in range(0, 6) {
          for j in range(0, 1) {
            if calc.rem(i * 2 + j, 3) != 0 {
              continue
            }
            let t = calc.rem(calc.rem(i * 2 + j, 3) + 3, 3)
            line("l" + str(i), "r" + str(t), stroke: red + 2pt)
            line("o" + str(i), "r" + str(t), stroke: red.darken(30%) + 2pt)
          }
          // line("r" + str(i), "o2", stroke: red + 2pt)
          // line("r" + str(i), "r" + str(calc.rem(i + 1, 3)), stroke: red + 2pt)
          line("l" + str(i), "l" + str(calc.rem(i + 1, 6)), stroke: black + 2pt)
          line("l" + str(i), "l" + str(calc.rem(i + 1, 6)), stroke: black + 2pt)
        }

        for i in range(0, 2) {
          line("r" + str(i), "o1", stroke: red + 2pt)
          line("r" + str(i), "o2", stroke: red + 2pt)
          line("r" + str(i), "r" + str(calc.rem(i + 1, 3)), stroke: red + 2pt)
        }

        // line("l" + str(1), "r" + str(7), stroke: black + 2pt)
        // line("l" + str(1), "r" + str(i + j), stroke: black + 2pt)
      }),
    )

    #place(
      top + left,
      dx: 21.3cm,
      dy: 3.8cm,
      [
        #set text(size: 1em)
        $
          overbracket(#h(100pt), #[Odd componenets])
        $
      ],
    )

    #place(
      top + left,
      dx: 13cm,
      dy: 2.8cm,
      [
        #set text(size: 1em)
        $
          overbracket(#h(220pt), #[Even componenets])
        $
      ],
    )

    #place(
      top + left,
      dx: 17.6cm,
      dy: 8.3cm,
      [
        #set text(size: 1em)
        $
          underbracket(#h(100pt), #[S])
        $
      ],
    )

  ],
)


#place(
  top + left,
  dx: 12.5cm,
  dy: 10cm,
  [
    #set text(size: 2em)
    #set align(center)
    $==>$ \ #[#set text(fill: purple, size: 0.5em)
      added $e$]],
)


#pagebreak()
#[
  #v(50pt)
  - If #text(fill: purple)[$e$ is an edge] with both ends in different #text(fill: red)[odd components]:
    - Then, we get #text(fill: green)[one even component] instead of the #text(fill: red)[two odd components] \ so that  $co(G-S + e) = co(G-S) - 2 <= |S| -2 <= |S|$.


]
#place(
  top + left,
  dx: -0cm,
  dy: 1.5cm,
  scale(x: 110%, y: 110%)[
    #place(
      top + left,
      dx: 13cm,
      dy: 3.5cm,
      cetz-canvas({
        import cetz.draw: *


        for i in range(0, 6) {
          circle((i * 0.5, calc.rem(i, 2)), fill: black, radius: 3pt, name: "l" + str(i))
        }

        for i in range(0, 5) {
          circle((i * 1.25 + 6, 0), fill: black, radius: 3pt, name: "o" + str(i))
        }


        for i in range(0, 3) {
          circle(
            (calc.cos(i + 0.44) * 1.5 + 6, calc.sin(i + 0.44) * 1.5 - 4),
            fill: red,
            radius: 3pt,
            name: "r" + str(i),
          )
        }
        circle((4.5, 0.3), fill: black, radius: 3pt, name: "t0")
        circle((4, 1), fill: black, radius: 3pt, name: "t1")

        rect-around("l0", "l5", padding: (0.2, 0.2, 0.2, 0.2), radius: 0.1, stroke: none, fill: green.lighten(90%))
        rect-around("t0", "t1", padding: (0.2, 0.2, 0.2, 0.2), radius: 0.1, stroke: none, fill: green.lighten(90%))
        rect-around("o0", "o1", padding: (0.2, 0.2, 0.2, 0.2), radius: 0.1, stroke: none, fill: green.lighten(90%))
        rect-around("o2", "o3", padding: (0.2, 0.2, 0.2, 0.2), radius: 0.1, stroke: none, fill: green.lighten(90%))
        rect-around("r0", "r2", padding: (1, 0.2, 0.2, 0.2), radius: 0.1, stroke: none, fill: gray.lighten(90%))
        for i in range(4, 5) {
          rect-around(
            "o" + str(i),
            "o" + str(i),
            stroke: none,
            padding: (0.2, 0.2, 0.2, 0.2),
            radius: 0.1,
            fill: red.lighten(50%),
          )
        }


        for i in range(0, 6) {
          circle((i * 0.5, calc.rem(i, 2)), fill: black, radius: 3pt, name: "l" + str(i))
        }

        for i in range(0, 5) {
          circle((i * 1.25 + 6, 0), fill: black, radius: 3pt, name: "o" + str(i))
        }

        for i in range(0, 3) {
          circle(
            (calc.cos(i + 0.44) * 1.5 + 6, calc.sin(i + 0.44) * 1.5 - 4),
            fill: red,
            radius: 3pt,
            name: "r" + str(i),
          )
        }
        circle((4.5, 0.3), fill: black, radius: 3pt, name: "t0")
        circle((4, 1), fill: black, radius: 3pt, name: "t1")


        line("o0", "o1", stroke: black + 2pt)
        line("t0", "t1", stroke: black + 2pt)
        line("r0", "t1", stroke: red + 2pt)
        for i in range(0, 6) {
          for j in range(0, 1) {
            if calc.rem(i * 2 + j, 3) != 0 {
              continue
            }
            let t = calc.rem(calc.rem(i * 2 + j, 3) + 3, 3)
            line("l" + str(i), "r" + str(t), stroke: red + 2pt)
            line("o" + str(i), "r" + str(t), stroke: red.darken(30%) + 2pt)
          }
          // line("r" + str(i), "o2", stroke: red + 2pt)
          // line("r" + str(i), "r" + str(calc.rem(i + 1, 3)), stroke: red + 2pt)
          line("l" + str(i), "l" + str(calc.rem(i + 1, 6)), stroke: black + 2pt)
          line("l" + str(i), "l" + str(calc.rem(i + 1, 6)), stroke: black + 2pt)
        }

        for i in range(0, 2) {
          line("r" + str(i), "o1", stroke: red + 2pt)
          line("r" + str(i), "o2", stroke: red + 2pt)
          line("r" + str(i), "r" + str(calc.rem(i + 1, 3)), stroke: red + 2pt)
        }

        line("o2", "o3", stroke: purple + 3pt)
        // line("l" + str(1), "r" + str(7), stroke: black + 2pt)
        // line("l" + str(1), "r" + str(i + j), stroke: black + 2pt)
      }),
    )

    #place(
      top + left,
      dx: 23.1cm,
      dy: 3.3cm,
      [
        #set text(size: 1em)
        $
          overbracket(#h(20pt), #[ Odd \ componenets])
        $
      ],
    )

    #place(
      top + left,
      dx: 13cm,
      dy: 2.8cm,
      [
        #set text(size: 1em)
        $
          overbracket(#h(295pt), #[Even componenets])
        $
      ],
    )

    #place(
      top + left,
      dx: 17.6cm,
      dy: 8.3cm,
      [
        #set text(size: 1em)
        $
          underbracket(#h(100pt), #[S])
        $
      ],
    )
  ],
)


#place(
  top + left,
  dx: -15cm,
  dy: 1.5cm,
  scale(x: 110%, y: 110%)[
    #place(
      top + left,
      dx: 13cm,
      dy: 3.5cm,
      cetz-canvas({
        import cetz.draw: *


        for i in range(0, 6) {
          circle((i * 0.5, calc.rem(i, 2)), fill: black, radius: 3pt, name: "l" + str(i))
        }

        for i in range(0, 5) {
          circle((i * 1.25 + 6, 0), fill: black, radius: 3pt, name: "o" + str(i))
        }


        for i in range(0, 3) {
          circle(
            (calc.cos(i + 0.44) * 1.5 + 6, calc.sin(i + 0.44) * 1.5 - 4),
            fill: red,
            radius: 3pt,
            name: "r" + str(i),
          )
        }
        circle((4.5, 0.3), fill: black, radius: 3pt, name: "t0")
        circle((4, 1), fill: black, radius: 3pt, name: "t1")

        rect-around("l0", "l5", padding: (0.2, 0.2, 0.2, 0.2), radius: 0.1, stroke: none, fill: green.lighten(90%))
        rect-around("t0", "t1", padding: (0.2, 0.2, 0.2, 0.2), radius: 0.1, stroke: none, fill: green.lighten(90%))
        rect-around("o0", "o1", padding: (0.2, 0.2, 0.2, 0.2), radius: 0.1, stroke: none, fill: green.lighten(90%))
        rect-around("r0", "r2", padding: (1, 0.2, 0.2, 0.2), radius: 0.1, stroke: none, fill: gray.lighten(90%))
        for i in range(2, 5) {
          rect-around(
            "o" + str(i),
            "o" + str(i),
            stroke: none,
            padding: (0.2, 0.2, 0.2, 0.2),
            radius: 0.1,
            fill: red.lighten(50%),
          )
        }


        for i in range(0, 6) {
          circle((i * 0.5, calc.rem(i, 2)), fill: black, radius: 3pt, name: "l" + str(i))
        }

        for i in range(0, 5) {
          circle((i * 1.25 + 6, 0), fill: black, radius: 3pt, name: "o" + str(i))
        }

        for i in range(0, 3) {
          circle(
            (calc.cos(i + 0.44) * 1.5 + 6, calc.sin(i + 0.44) * 1.5 - 4),
            fill: red,
            radius: 3pt,
            name: "r" + str(i),
          )
        }
        circle((4.5, 0.3), fill: black, radius: 3pt, name: "t0")
        circle((4, 1), fill: black, radius: 3pt, name: "t1")


        line("o0", "o1", stroke: black + 2pt)
        line("t0", "t1", stroke: black + 2pt)
        line("r0", "t1", stroke: red + 2pt)
        for i in range(0, 6) {
          for j in range(0, 1) {
            if calc.rem(i * 2 + j, 3) != 0 {
              continue
            }
            let t = calc.rem(calc.rem(i * 2 + j, 3) + 3, 3)
            line("l" + str(i), "r" + str(t), stroke: red + 2pt)
            line("o" + str(i), "r" + str(t), stroke: red.darken(30%) + 2pt)
          }
          // line("r" + str(i), "o2", stroke: red + 2pt)
          // line("r" + str(i), "r" + str(calc.rem(i + 1, 3)), stroke: red + 2pt)
          line("l" + str(i), "l" + str(calc.rem(i + 1, 6)), stroke: black + 2pt)
          line("l" + str(i), "l" + str(calc.rem(i + 1, 6)), stroke: black + 2pt)
        }

        for i in range(0, 2) {
          line("r" + str(i), "o1", stroke: red + 2pt)
          line("r" + str(i), "o2", stroke: red + 2pt)
          line("r" + str(i), "r" + str(calc.rem(i + 1, 3)), stroke: red + 2pt)
        }

        // line("l" + str(1), "r" + str(7), stroke: black + 2pt)
        // line("l" + str(1), "r" + str(i + j), stroke: black + 2pt)
      }),
    )

    #place(
      top + left,
      dx: 21.3cm,
      dy: 3.8cm,
      [
        #set text(size: 1em)
        $
          overbracket(#h(100pt), #[Odd componenets])
        $
      ],
    )

    #place(
      top + left,
      dx: 13cm,
      dy: 2.8cm,
      [
        #set text(size: 1em)
        $
          overbracket(#h(220pt), #[Even componenets])
        $
      ],
    )

    #place(
      top + left,
      dx: 17.6cm,
      dy: 8.3cm,
      [
        #set text(size: 1em)
        $
          underbracket(#h(100pt), #[S])
        $
      ],
    )

  ],
)


#place(
  top + left,
  dx: 12.5cm,
  dy: 8cm,
  [
    #set text(size: 2em)
    #set align(center)
    $==>$ \ #[#set text(fill: purple, size: 0.5em)
      added $e$]],
)

== Tutte's graph
#block(width: 50%)[
  #observation[
    - $G$ graph, satisfying the Tutte's condition
    Then, $v(G)=n$ is even.
  ]
]

#place(
  top + left,
  dx: 52%,
  dy: 0cm,
  block(width: 50%, fill: rgb("#abeddb"), inset: 20pt, radius: 5pt)[
    #set text(size: 0.8em)
    *Tutte's Condition:*
    $
      co(G-S)| <= |S|, forall S subset.eq A.
    $
  ],
)

#proof[
  Set $S=emptyset$.
  - $co(G-S)=co(G)<= |S| = 0$
    - Every connect component of $G$ must have an even number of vertices.
]

= Construction edge maxinal counter example
== Construction edge maxinal counter example
#tutte
#v(-10pt)
- Assume that $exists G$ satisfying the Tutte's condition without a p.m.
  - If $exists e in.not E(G)$ s.t. $G + e$ still has no p.m.
    - Set $G:= G+e$.
#v(-5pt) #pause
We obtain a graph $G$ with the following properties:
1. $G$ satisfies the Tutte's condition #pause
2. $G$ has no perfect matching #pause
3. $forall e in.not E(G): G+e$ has a perfect matching. #pause

*$G$ is called an edge maximal counter example!*
#v(-5pt)
#pause
#place(
  top + left,
  dx: 58%,
  dy: 10cm,
  block(fill: rgb("#523662"), radius: 5pt, inset: 15pt)[
    #set align(center)
    #set text(fill: red.darken(0%))
    A graph satisfying (2,3) is an #text(weight: "bold")[SNF graph!] \

    #text(weight: "bold")[SNF graphs do not \ satisfy Tutte's condition]
  ],
)


= SNF graphs
== SNF graphs
#definition(title: "SNF Graph's")[
  A graph G is called #text(fill: red.darken(20%), weight: "bold")[Saturated non-fractorisable] graph if it satisfies:
  1. $G$ has no perfect matching
  2. $G+e$ has a perfect matching $forall e in.not E(G)$
]
#v(120pt)
#remark[ If $v(G)=n$ is odd. \
  Then, $G = K_n$.]

#place(
  top + center,
  dx: 0cm,
  dy: 5cm,
  cetz-canvas({
    import cetz.draw: *

    let k = 3
    for i in range(0, k + 1) {
      for j in range(0, k) {
        circle(
          (calc.cos(j * 2 + i) + i * 5, calc.sin(j * 2 + i)),
          fill: black,
          radius: 3pt,
          name: str(j) + "l" + str(i),
        )
      }
    }
    circle((18.5, 0), fill: black, radius: 3pt, name: "l")

    for i in range(0, k) {
      circle((calc.cos(i * 2) + 10, calc.sin(i * 2) - 6), fill: black, radius: 3pt, name: "s" + str(i))
    }

    // for i in range(0, k+1){
    // rect-around("0l" + str(i), "2l" + str(i), padding: (1.1, 0.2, 0.2, 0.2), radius: 0.1, stroke: none,fill: red.lighten(90%))
    // }
    for i in range(0, k + 1) {
      for j0 in range(0, k) {
        for j1 in range(0, k) {
          line(str(j0) + "l" + str(i), "s" + str(j1), stroke: (dash: "dashed", thickness: 2pt, paint: gray))
        }
        line("s" + str(j0), "l", stroke: (dash: "dashed", thickness: 2pt, paint: gray))
      }
    }

    for i in range(0, k + 1) {
      for j in range(0, k) {
        let t = calc.rem(j + 1, 3)
        line(str(j) + "l" + str(i), str(t) + "l" + str(i), stroke: black + 2pt)
        line("s" + str(j), "s" + str(t), stroke: black + 2pt)
      }
    }
  }),
)

#pagebreak()
*How do even SNF graph look like?* #text(fill: red.darken(20%), weight: "bold")[
  Proof is left for the TA session.
]
- $exists S in V(G)$ and $k in NN$ s.t. $S=K_k$.
  - $G-S$ consist of $k+2$ odd cliques.

#[
  #set align(center)
  This means that any SNF graph by construction doesnt sayfies the Tutte's condition! In particular setting $S$ to the $K_k$ we have $co(G-S) = k+2 > k = |S|$. \
]
#place(
  top + center,
  dx: 0cm,
  dy: 5cm,
  cetz-canvas({
    import cetz.draw: *

    let k = 3
    for i in range(0, k + 1) {
      for j in range(0, k) {
        circle(
          (calc.cos(j * 2 + i) + i * 5, calc.sin(j * 2 + i)),
          fill: black,
          radius: 3pt,
          name: str(j) + "l" + str(i),
        )
      }
    }
    circle((18.5, 0), fill: black, radius: 3pt, name: "l")

    for i in range(0, k) {
      circle((calc.cos(i * 2) + 10, calc.sin(i * 2) - 6), fill: black, radius: 3pt, name: "s" + str(i))
    }

    // for i in range(0, k+1){
    // rect-around("0l" + str(i), "2l" + str(i), padding: (1.1, 0.2, 0.2, 0.2), radius: 0.1, stroke: none,fill: red.lighten(90%))
    // }
    for i in range(0, k + 1) {
      for j0 in range(0, k) {
        for j1 in range(0, k) {
          line(str(j0) + "l" + str(i), "s" + str(j1), stroke: (dash: "dashed", thickness: 2pt, paint: gray))
        }
        line("s" + str(j0), "l", stroke: (dash: "dashed", thickness: 2pt, paint: gray))
      }
    }

    for i in range(0, k + 1) {
      for j in range(0, k) {
        let t = calc.rem(j + 1, 3)
        line(str(j) + "l" + str(i), str(t) + "l" + str(i), stroke: black + 2pt)
        line("s" + str(j), "s" + str(t), stroke: black + 2pt)
      }
    }
  }),
)

#place(
  top + left,
  dx: 0%,
  dy: 99% + 5pt,
  block(width: 100%)[
    #set text(size: 0.7em)
    #set align(center)
    In the example above, $S = K_3$ and there is $5$ odd components in $G-S$.
  ],
)

== Conclusion
#place(
  top + left,
  dx: 0cm,
  dy: 0cm,
  block(fill: blue.lighten(50%), inset: 20pt)[
    #conclusion[
      - If $G$ is an even sized *SNF graph*.
        - $exists S in V(G)$ s.t. $co(G-S)=|S|+2 > |S|$.
        $==>$ $G$ doesn't satisfy the Tutte's condition!
    ]
  ],
)

#v(150pt)
*Back to the proof:*
Let $G$ be a counter example i.e.
- $G$ satisfies the Tutte's condition & $G$ has no perfect matching

$==>$ Construct an edge maximal counter example from $G$ called $G^*$.
#pause
$==>$ $G^*$ is an *SNF graph* & $G^*$ satifies the tutte's condition.
#pause
$==>$ Any *SNF graph* doesn't satisfies tutte's so its a contradiction.
#pause
$==>$ $G^*$ cannot exists  $==>$ $G$ cannot exists.
#pause
$==>$ If $G$ satisfies the Tutte's condition then $G$ must have a perfect matching!
