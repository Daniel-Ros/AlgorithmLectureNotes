#import "@preview/touying:0.6.1": *
#import themes.university: *
#import "@preview/numbly:0.1.0": numbly
#import "@preview/algo:0.3.6": algo, d, i

#import "@preview/theorion:0.4.1": *
#import "@preview/algorithmic:1.0.7"
#import "@preview/larrow:1.0.0": *
#import "@preview/cetz:0.4.2"

#import cosmos.clouds: *

#let cetz-canvas = touying-reducer.with(reduce: cetz.canvas, cover: cetz.draw.hide.with(bounds: true))

#let (claim-counter, claim-box, claim, show-claim) = make-frame(
  "claim",
  "Claim", // supplement, string or dictionary like `(en: "Theorem")`, or `theorion-i18n-map.at("theorem")` for built-in i18n support
  counter: theorem-counter, // inherit the old counter, `none` by default
  inherited-levels: 1, // useful when you need a new counter
  inherited-from: heading, // heading or just another counter
  render: render-fn.with(fill: navy.lighten(80%)),
)
#show: show-claim


#let (question-counter, question-box, question, show-question) = make-frame(
  "question",
  "Question", // supplement, string or dictionary like `(en: "Theorem")`, or `theorion-i18n-map.at("theorem")` for built-in i18n support
  counter: theorem-counter, // inherit the old counter, `none` by default
  inherited-levels: 2, // useful when you need a new counter
  inherited-from: heading, // heading or just another counter
  render: render-fn.with(fill: green.lighten(90%)),
)
#show: show-question

#show: show-theorion


#import algorithmic: algorithm-figure, style-algorithm
#show: style-algorithm


#show: university-theme.with(
  aspect-ratio: "16-9",
  // align: horizon,
  // config-common(handout: true),
  config-common(frozen-counters: (theorem-counter,)), // freeze theorem counter for animation
  config-info(
    title: [Algorithms 2],
    subtitle: [Reductions],
    author: [Daniel Rosenberg & Michael Trushkin],
    // date: datetime.today(),
    institution: [Ariel University],
    // logo: emoji.school,
  ),
)


#let todo(body) = text(red)[TODO:*#body*]
#let cP = $bold("P")$
#let cNP = $bold("NP")$
#let cNPC = $bold("NPC")$
#let cNPH = $bold("NPH")$
#let reduction = $scripts(<=)_p$
#let aT = text(fill: green, $T$)
#let aF = text(fill: red, $F$)
#let sred(c) = text(fill: red, size: 8pt, c)

#set text(
  size: 18pt,
)

#set heading(numbering: "1.1")

#title-slide()

= NP-completeness
== NP-completeness
- As we saw, most problems are _hard_!
#pause
#definition(title: "NP class")[
  // #set text(size:14pt)
  A language $L$ is said to be in $cNP$ if we have a polynomial-time algorithm $M$ such that
  $
    x in L <=> exists y space s.t |y| < p(|x|) "and" M(x,y) = 1
  $
  where $p$ is some polynomial
]
- In most literture $y$ is called a _witness_ and $M$ is called _veryfing algorithm_, where $y$ plays the role of the answer, and $M$ should just verify if the answer is correct.
#pause
- We talked about a few:
  - $k$-clique
  - CNF-SAT
  - $k$-CNF-SAT

= Reductions

== Reductions
  - We saw we can "translate" one languge into another with reductions
  #pause
  #definition(title: "polynomial time reduction")[
    Given two languages $L_1, L_2 in cNP$, we write $L_1 reduction L_2$ if there exists a function $f:{0,1}^* -> {0,1}^*$ and a polynomial $p: NN -> NN$, such that:
    - $x in L_1 <=> f(x) in L_2$
    - for every $x in {0,1}^*$, $f$ runs in $p(|x|)$ time.
  ]
  #pause
  #align(center)[

  #align(center)[
    #cetz.canvas({
      import cetz.draw: *;

      set-style(stroke:2pt)

      rect(name:"outter",(0,0),(15,4))
      line((-2,2),"outter.west",name:"ox")
      mark("outter.west","outter",symbol:">",stroke:5pt)
      content((rel:(0,0.1),to:"ox"),[$x$],anchor: "south")
      rect((2,1),(6,3),name:"F")
      content("F",[$F$])

      line("outter.west","F.west",name:"ix")
      mark("F.west","F",symbol:">",stroke:5pt)
      content((rel:(0,0.1),to:"ix"),[$x$],anchor: "south")

      rect((8,1),(13,3),name:"A")
      content("A",[Algo for $L_2$])

      line("F.east","A.west",name:"fx")
      mark("A.west","A",symbol:">",stroke:5pt)
      content((rel:(0,0.1),to:"fx"),[$f(x)$],anchor: "south")

      line((rel:(0,0.5),to:"A.east"),(rel:(0,0.5),to:"outter.east"),name:"iyes")
      line((rel:(0,-0.5),to:"A.east"),(rel:(0,-0.5),to:"outter.east"),name:"ino")

      content((rel:(0,0.1),to:"iyes"),[yes],anchor: "south")
      content((rel:(0,-0.1),to:"ino"),[no],anchor: "north")

      line((rel:(0,0.5),to:"outter.east"),(rel:(2,0.5),to:"outter.east"),name:"oyes")
      line((rel:(0,-0.5),to:"outter.east"),(rel:(2,-0.5),to:"outter.east"),name:"ono")

      mark("oyes.end","A",symbol:"<",stroke:5pt)
      mark("ono.end","A",symbol:"<",stroke:5pt)

      content((rel:(0,0.1),to:"oyes"),[yes],anchor: "south")
      content((rel:(0,-0.1),to:"ono"),[no],anchor: "north")
    })
  ]
  ]


== Hard Langauges
- For any complexity class, there are hard languages
#definition(title: "NP-hard")[
  A language $L subset.eq {0,1}^*$ is said to be NP-hard if  $L' reduction L$ for every $L' in cNP$
]

#definition(title: "NP-complete")[
  A language $L subset.eq {0,1}^*$ is said to be NP-complete if $L in cNP$ and $L$ is NP-hard
]

- We saw that CNF-SAT and $k$-CNF-SAT are NP Complete

= Independent set
== Independent set
// #set align(horizon)
// For a graph $G$, two edges $e_1, e_2 subset.eq E(G)$ are called _indepedent_ if there is no common vertex between them.
// #align(center)[

// #columns(2, [
// #cetz.canvas({
//   import cetz.draw: *

//   circle((0,5), radius:5pt,fill:black, name:"p2")
//   circle((0,0), radius:5pt,fill:black, name:"p1")
//   line("p1","p2")
//   circle((1,5), radius:5pt,fill:black, name:"p3")
//   circle((1,0), radius:5pt,fill:black, name:"p4")
//   line("p3","p4")
//   content((0.5,-1), [indepedent], anchor: "north")
// })
// #colbreak()
// #cetz.canvas({
//   import cetz.draw: *
//   circle((0.5,5), radius:5pt,fill:black, name:"p1")
//   circle((0,0), radius:5pt,fill:black, name:"p2")
//   circle((1,0), radius:5pt,fill:black, name:"p3")
//   line("p1","p2")
//   line("p1","p3")
//   content((0.5,-1), [not indepedent], anchor: "north")
//   // content(("p1","south"), [independant],anchor: "north")
// })
// ])
// ]
// #pagebreak()
#[
  #set align(horizon)
  #v(-80pt)
- For a graph $G$, let $alpha(G)$ denote the size of the maximum independent set in $G$.
#definition[
  $"IS" := {<G,k> : alpha (G) >= k}$.
]
#theorem[
  IS is in $cNPC$.
]
]

== Independent set
#[
  #set align()
#place(
      top + left, 
      dx: 17cm, 
      dy: 0cm, 
      block(width: 40%)[
      #set text(size: 0.8em)
   #claim[
    Let $L in cNPH$, and let $L'$ be a language. If $L reduction L'$, then $L'$ is also $cNPH$.
  ]<NP_hard_reduction>
      ]
    )

- The proof that IS is in $cNP$ is left as homework.
- In order to show that IS is hard it is enough to show that
$
  L reduction "IS"
$
for some lanaguege $L$ where $L in cNPH$.
- Here, we show that
$
3"-CNF-SAT" reduction "IS"
$
]

== $3"-CNF-SAT" reduction "IS"$
- Given a  $3$-CNF formula $phi$, construct a graph $G_phi$ as follows:
  + *Triangles*: For each clause $l_1, l_2, l_3$ we create a triangle with 3 vertices named $v_l_1, v_l_2, v_l_3$.
  + *Consistency Edges*: For any pair of complementary literals $x_j, overline(x_j)$ that are in different clauses, put an edge between the vertices that correspond to the literals.

#align(center)[
  #cetz-canvas({
      import cetz.draw: *
      content((0,0),[$
        phi = &(x_1 or x_2 or x_3) and (x_1 or overline(x_2) or x_3) and (overline(x_1) or overline(x_2) or x_3)
      $])

      (pause,)
      polygon((-5,-4),3,angle:90deg, name:"c1")
      content((rel:(0,1.5),to:"c1"),[$x_1$])
      content((rel:(1,-1),to:"c1"),[$x_2$])
      content((rel:(-1,-1),to:"c1"),[$x_3$])


      (pause,)

      polygon((0,-4),3,angle:90deg, name:"c2")
      content((rel:(0,1.5),to:"c2"),[$x_1$])
      content((rel:(-1,-1),to:"c2"),[$overline(x_2)$])
      content((rel:(1,-1),to:"c2"),[$x_3$])

      (pause,)

      polygon((5,-4),3,angle:90deg, name:"c3")
      content((rel:(0,1.5),to:"c3"),[$overline(x_1)$])
      content((rel:(-1,-1),to:"c3"),[$overline(x_2)$])
      content((rel:(1,-1),to:"c3"),[$x_3$])

      (pause,)

      line((rel:(0,1),to:"c3"),(rel:(0,1),to:"c2"))
      hobby((rel:(0,1),to:"c1"),(0,-2),(rel:(0,1),to:"c3"))

      (pause,)
      line((rel:(0.9,-0.5),to:"c1"),(rel:(-0.9,-0.5),to:"c2"))
      hobby((rel:(0.9,-0.5),to:"c1"),(0,-6),(rel:(-0.9,-0.5),to:"c3"))
    })
  ]
 //  #figure(
 //    image("figures/L1i3.png", width: 50%),
 //   // caption: [Here $f(phi)=<G_phi,m>$ where $G_phi$ is the graph above with 9 vertices and $m=3$ is the number of clauses in $phi$.]
 // )
 - return the pair $<G_phi,m>$ where $m$ is the number of clauses.

== Independent set
- The algorithm runs in poly time(why?)
- Now we need to prove that
$
  phi in 3"-CNF-SAT" <==> <G_phi,m> in "IS"
$

$==>$:
- Let $phi$ be satisfiable and let $alpha_phi$ be a satisfying assignment for $phi$.
- As $alpha_phi$ satisfies $phi$, at least one literal of each clause is satisfied, pick any one such literal from each clause.
- The set of vertices corresponding to the set of literals chosen is independent in $G_phi$ and has size of $m$.\

== Independent set
- The algorithm runs in poly time(why?)
- Now we need to prove that
$
  phi in 3"-CNF-SAT" <==> <G_phi,m> in "IS"
$
$<==$:
- Suppose $G_phi$ has an independent set of size $m$, and let $S$ be such an independent set.
- Let $l_1,...,l_m$ denote the vertices of $S$,
- for each $i in m$ let $v(l_i) in {x_1, overline(x_1),..., x_n, overline(x_n)}$ be the variable corresponding to $l_i$.
- Set $v(l_i)=aT$ for all $i in [m]$, Finally if $x_i in [n]$ did not recieve an assigment set $x_i = aT$.

- The asssignment is satisfying:
  - every triangle has one vertex in $S$ $=>$ every clause has one positive literal
- The assignment is _consistent_:
  - if for some variable $x_i = overline(x_i)$ then \
   #h(50pt) $
   exists j,k in[m]$ s.t. $v(l_j) = x_i$ and $v(l_k) = overline(x_i) => l_j l_k in E(G_phi) => S
   $ is not independent.
  

= Graph coloring
== Graph coloring
#let dodecahedron-graph = cetz.canvas(length: 1cm, {
  import cetz.draw: *

  let a-straight = (90, 162, 234, 306, 18).map(a => a * 1deg)
  let a-rotated = (126, 198, 270, 342, 54).map(a => a * 1deg)

  let l0 = a-straight.map(a => (calc.cos(a) * 3, calc.sin(a) * 3))
  let l1 = a-straight.map(a => (calc.cos(a) * 2, calc.sin(a) * 2))
  let l2 = a-rotated.map(a => (calc.cos(a) * 1.3, calc.sin(a) * 1.3))
  let l3 = a-rotated.map(a => (calc.cos(a) * 0.5, calc.sin(a) * 0.5))

  line(..l0, close: true, stroke: 1.2pt + black)
  line(..l3, close: true, stroke: 1.2pt + black)

  for i in range(5) {
    line(l0.at(i), l1.at(i), stroke: 1.2pt + black)
    line(l2.at(i), l3.at(i), stroke: 1.2pt + black)
    line(l1.at(i), l2.at(i), stroke: 1.2pt + black)
    line(l1.at(i), l2.at(calc.rem(i + 4, 5)), stroke: 1.2pt + black)
  }

  let c0 = (red, green, blue, red, green)
  let c1 = (blue, red, green, blue, red)
  let c2 = (green, blue, red, green, blue)
  let c3 = (red, green, blue, red, green)

  for i in range(5) {
    circle(l0.at(i), radius: 0.15, fill: c0.at(i), stroke: 0.5pt + black)
    circle(l1.at(i), radius: 0.15, fill: c1.at(i), stroke: 0.5pt + black)
    circle(l2.at(i), radius: 0.15, fill: c2.at(i), stroke: 0.5pt + black)
    circle(l3.at(i), radius: 0.15, fill: c3.at(i), stroke: 0.5pt + black)
  }
})

#let groetzsch-graph = cetz.canvas(length: 1cm, {
  import cetz.draw: *

  let angles = (90, 162, 234, 306, 18).map(a => a * 1deg)

  let out-pts = angles.map(a => (calc.cos(a) * 3, calc.sin(a) * 3))
  let in-pts = angles.map(a => (calc.cos(a) * 1.5, calc.sin(a) * 1.5))
  let center = (0, 0)

  line(..out-pts, close: true, stroke: 1.2pt + black)

  for i in range(5) {
    line(center, in-pts.at(i), stroke: 1.2pt + black)
    line(in-pts.at(i), out-pts.at(calc.rem(i + 1, 5)), stroke: 1.2pt + black)
    line(in-pts.at(i), out-pts.at(calc.rem(i + 4, 5)), stroke: 1.2pt + black)
  }

  let c-out = (rgb("#00FFFF"), rgb("#FF00FF"), white,yellow , rgb("#AAAAAA"))
  let c-in = (blue, green, red, yellow, rgb("#00FFFF"))

  for i in range(5) {
    circle(out-pts.at(i), radius: 0.15, fill: c-out.at(i), stroke: 0.5pt + black)
    circle(in-pts.at(i), radius: 0.15, fill: c-in.at(i), stroke: 0.5pt + black)
  }

  circle(center, radius: 0.15, fill: black, stroke: 0.5pt + black)
})

#grid(
  columns: (1fr, 1fr),
  align: center,
  dodecahedron-graph,
  groetzsch-graph
)


- For a graph $G$ denote by $chi(G)$ the least $k in NN$ such that $G$ is k-colorable.
#pause
#definition[
  $k"-COL" := {G : chi(G) <= k}$
]
It is well known that $2$-COL$in cP$.
#pause
#theorem[
  $3"-COL" in cNPC$.
]
- The proof that $3$-COL is in $cNP$ is left as homework

== NEA-$k$-CNF-SAT
- Let $phi$ be a formula
#pause
- $phi$ is said to be _not all equal satisfiable_ (NAE-SAT) if it has a satisfying assigmnet such that in each caluse it has at least one satisfied literal and at least one that is not satisfied.
#pause
#definition(title:[NAE-$k$-CNF-SAT])[
  $ "NAE-"k"-CNF-SAT":= {phi: phi "is NAE-SAT, with exactly k literals in each clause" }. $
]
#pause
- We are going to show
$
"NAE-"3"-CNF-SAT" reduction 3"-COL".
$
#v(-20pt)
#remark[
  #v(-10pt)
  In the t.a session you will prove that
  $
    #text[3-CNF-SAT] reduction "NAE-"3"-CNF-SAT"
  $
  #v(-10pt)
  concluding the proof.
]

== $"NAE-"3"-CNF-SAT" reduction 3"-COL"$
- Given a 3-CNF formula $phi$, define $G_phi$ as follows:
#pause
  + Start with a single vertex $D$. This is our _Don't care vertex_.
#pause
  + For each variable $x_i$ of $phi$, add two "original" new vertices $x_i, overline(x_i)$, add an edge between them, and connect both to $D$. This are our _variable gadgets_.
#pause
  + For each clause $l_1 or l_2 or l_3$ we create a triangle with 3 vertices named $l_1, l_2, l_3$, this is our _clause gadget_.
#pause
  + For each literal in the clause gadgets, connect it to the complementary variable from the variable gadget.

#pause
#align(center)[
  #cetz-canvas({
    import cetz.draw: *;
    circle((0,0),radius:2pt,name:"D",fill: black)

    (pause,)
    for i in range(4) {
      let x = -6 + 4*i
      circle((x - 1,-1),radius:2pt,fill: black,name:"l_" + str(i))
      circle((x + 1,-1),radius:2pt,fill: black,name:"nl_" + str(i))
      line("l_"+ str(i), "nl_" + str(i))
      line("D", "l_" + str(i))
      line("D", "nl_" + str(i))
    }

    (pause,)
    for i in range(4) {
      let x = -6 + 4*i
      circle((x - 1,-3),radius:2pt,fill: black,name:"v_1_" + str(i))
      circle((x + 1,-3),radius:2pt,fill: black,name:"v_2_" + str(i))
      circle((x,-2),radius:2pt,fill: black,name:"v_3_" + str(i))
      line("v_1_"+ str(i), "v_2_" + str(i))
      line("v_3_"+ str(i), "v_2_" + str(i))
      line("v_1_"+ str(i), "v_3_" + str(i))
    }

    (pause,)
    line("l_1", "v_1_2",stroke: ( dash: "dashed"))
    content((rel:(-0.4,0),to:"l_1"),[$x_2$])
    content((rel:(0,-0.5),to:"v_1_2"),[$overline(x_2)$])

    (pause,)
    line("nl_3", "v_3_3",stroke: ( dash: "dashed"))
    content((rel:(0.4,0),to:"nl_3"),[$overline(x_4)$])
    content((rel:(0.5,0),to:"v_3_3"),[$x_4$])
  })
]


- The algorithm runs in poly time(why?)

== $"NAE-"3"-CNF-SAT" reduction 3"-COL"$
- We need to show that
$
  phi in "NAE-"3"-CNF-SAT" <=> G_phi in  3"-COL"
$

$=>$:
- Given a satisfying NAE assignment $alpha_phi$ for $phi$, define the follwing 3-coloting of $G_phi$:
 - $D$ will be colored as #text(blue)[D]
 - For each "original" variable $x_i$, if $x_i$ is assigned `true` under $alpha_phi$ color $x_i$ as #text(green)[T] and $overline(x_i)$ in #text(red)[F], otherwise color $x_i$ as #text(red)[F] and $overline(x_i)$ in #text(green)[T]
 - For each clause gadget, scan the corresponding clause $c$, color first literal that is assigned `true` with #text(green)[T], the first that assigned `false` with #text(red)[F], and color the vertex that was left with #text(blue)[D].

- Each edge inside vertex/clause gadgets have both ends in different colors.
- W.L.O.G, let $x$ be a variable assigned `true` by $a_phi$, as $a_phi$ is proper, all vertcies $overline(x)$ are #text(red)[F] or #text(blue)[D]. So all edges between clause/vertex gadgets have both ends in different colors.

== $"NAE-"3"-CNF-SAT" reduction 3"-COL"$
- We need to show that
$
  phi in "NAE-"3"-CNF-SAT" <=> G_phi in  3"-COL"
$

$arrow.l.double$:
- Given a 3-coloring $psi$ of $G_phi$, we define a NAE-satisfying assignment for $phi$.
- As all of the variable gadgets form a triangles with a common vertex $D$, it leaves them with two colors to be chosen W.L.O.G, those colors are #text(green)[T] and #text(red)[F].
- Assigned $x_i$ as `true` if $x_i$ is colored as #text(green)[T] in its _variable gadget_ otherwise assign $x_i$ as `false`. This defines a valid assignmet to the variables of $phi$.
- The assignment is NAE as each clause gadget has one variable colored `true` and one `false`.


== Max-cut
 - Given a graph $G$, a _cut_ is defined as the set of edges between $S subset.eq V(G)$ and $overline(S) = V(G) backslash S$.
-  We denote the set of edges by
$
  E_G (S,overline(S)) := {(u,v): (u,v) in E(G), u in S, v in overline(S)}
$
and the number of edges by
$
  e_G (S, overline(S)) := |E_G (S,overline(S))|
$
#align(center)[
#cetz-canvas({
  import cetz.draw: *;
  rect((0,0),(rel:(2,5)))
  rect((5,0),(rel:(2,5)))

  line((1, 1.5),(6,3))
  line((1, 4),(6,2))
  line((1, 2),(6,1))
  line((1, 1),(6,4))
})
]
#pagebreak()
Denote by $sigma(G) := max_(S subset.eq V(G)) e_G (S, overline(S))$.
#definition(title:"MAX-CUT")[
  MAX-CUT $:= {<G,k> : sigma(G) >= k}$
]
#theorem[
  MAX-CUT$ in cNPC$
]
- The proof that MAX-CUT is in $cNP$ is left as homework.
== Max-cut
- We are going to show
$
"NAE-"3"-CNF-SAT" reduction "MAX-CUT".
$
- Given a 3-CNF formula $phi$, define $G_phi$ as follows:
#pause
+ For each variable $x_i$ of $phi$, add two new vertices $x_i, overline(x_i)$ and an edge between them. These are our _variable gadgets_.
#pause
+ For each clause $l_1 or l_2 or l_3$, we create a triangle with vertices $l_1, l_2, l_3$; this is our _clause gadget_.
#pause
+ For each literal vertex in a clause gadget, connect it to the complementary literal vertex in the variable gadget.
#pause
#align(center)[
  #cetz-canvas({
    import cetz.draw: *;
    for i in range(4) {
      let x = -6 + 4*i
      circle((x - 1,-1),radius:2pt,fill: black,name:"l_" + str(i))
      circle((x + 1,-1),radius:2pt,fill: black,name:"nl_" + str(i))
      line("l_"+ str(i), "nl_" + str(i))
    }

    for i in range(4) {
      let x = -6 + 4*i
      circle((x - 1,-3),radius:2pt,fill: black,name:"v_1_" + str(i))
      circle((x + 1,-3),radius:2pt,fill: black,name:"v_2_" + str(i))
      circle((x,-2),radius:2pt,fill: black,name:"v_3_" + str(i))
      line("v_1_"+ str(i), "v_2_" + str(i))
      line("v_3_"+ str(i), "v_2_" + str(i))
      line("v_1_"+ str(i), "v_3_" + str(i))
    }

    line("l_1", "v_1_2",stroke: ( dash: "dashed"))
    content((rel:(-0.4,0),to:"l_1"),[$x_2$])
    content((rel:(0,-0.5),to:"v_1_2"),[$overline(x_2)$])

    line("nl_3", "v_3_3",stroke: ( dash: "dashed"))
    content((rel:(0.4,0),to:"nl_3"),[$overline(x_4)$])
    content((rel:(0.5,0),to:"v_3_3"),[$x_4$])
  })
]
 - The algorithm runs in poly time(why?)
 - $f(phi)$ needs to return both the graph $G_phi$ and a number $k$ what should $k$ be?
== Max-cut
#align(center)[
  #cetz-canvas({
    import cetz.draw: *;
    for i in range(4) {
      let x = -6 + 4*i
      circle((x - 1,-1),radius:2pt,fill: black,name:"l_" + str(i))
      circle((x + 1,-1),radius:2pt,fill: black,name:"nl_" + str(i))
      line("l_"+ str(i), "nl_" + str(i))
    }

    for i in range(4) {
      let x = -6 + 4*i
      circle((x - 1,-3),radius:2pt,fill: black,name:"v_1_" + str(i))
      circle((x + 1,-3),radius:2pt,fill: black,name:"v_2_" + str(i))
      circle((x,-2),radius:2pt,fill: black,name:"v_3_" + str(i))
      line("v_1_"+ str(i), "v_2_" + str(i))
      line("v_3_"+ str(i), "v_2_" + str(i))
      line("v_1_"+ str(i), "v_3_" + str(i))
    }

    line("l_1", "v_1_2",stroke: ( dash: "dashed"))
    content((rel:(-0.4,0),to:"l_1"),[$x_2$])
    content((rel:(0,-0.5),to:"v_1_2"),[$overline(x_2)$])

    line("nl_3", "v_3_3",stroke: ( dash: "dashed"))
    content((rel:(0.4,0),to:"nl_3"),[$overline(x_4)$])
    content((rel:(0.5,0),to:"v_3_3"),[$x_4$])
  })
]
- What is $sigma(phi)$ in the graph above?
- Intuition: 
  - For each variable clause we might take 1 vertex, thus covering edges of  the time $(x_i, overline(x_i))$ thus covering exactly $n$ edges.
  - For each triangle clause we might also take $1$ or $2$ vertices covering exactly $2$ of the edges of each triangle thus covering $2m$ edges.
  - We are left with edges in between the _gadget variables_ and _gadget clauses_, how many edges of this type we have?
    - Each literal $l$ connect exactly to one variable $v(overline(l))$, so that there are $3m$ edges in between.
  
  So that it follows that if $sigma(G_phi) <= n+5m$.
  - We return $<G_phi, n+5m>$ and hope for the best.

== Max-cut
- We need to show that
$
  phi in "NAE-"3"-CNF-SAT" <=> G_phi in  "MAX-CUT"
$
$=>$:
- Given a satisfying NAE assignment $alpha_phi$ for $phi$, define $S subset.eq V(G_phi)$ to consist of all vertices whose label is a literal assigned `true` under $alpha_phi$.
- As $alpha_phi$ is consistent, all variable gadgets must cross $(S,overline(S))$ adding $n$ edges to the cut.
- As $alpha_phi$ is a valid NAE assignment, at least two edges cross $(S,overline(S))$ in every clause gadget, adding $2m$ edges to the cut.
- Each edge between a variable and clause gadget has the form $(l,overline(l))$, which means it is also in the cut, adding $3m$ edges to the cut.
- Overall, we count at least $n+ 5m$ edges.

== Max-cut
- We need to show that
$
  phi in "NAE-"3"-CNF-SAT" <=> G_phi in  "MAX-CUT"
$
#v(-20pt)
$arrow.l.double$:
- Suppose that $<G_phi, n+5m> in "MAX-CUT"$. Let $(S,overline(S))$ be a cut of $G_phi$ such that $e_G_phi (S,overline(S)) = n + 5m$.
- Define the assignment $alpha_phi$ for $phi$ in which all variable gadget literals found in $S$ are assigned `true` and all remaining are assigned `false`. This defines a consistent assignment.
- It remains to prove that $alpha_phi$ is NAE-satisfying.
  - Fix a clause of $phi$, and look at the corresponding gadget clause.
    - Since $e_G_phi (S,overline(S)) = n + 5m$, every edge between this  clause gadget and the variable gadgets is also in the cut and of the form $(l,overline(l))$.
    - Take a vertex $l$ in that clause gadget that is also in $S$. Then the edge $(l,overline(l))$ implies that $overline(l) in overline(S)$, meaning the literal corresponding to $l$ is assigned `true`. In a similar manner, if $l$ is in $overline(S)$ the then the edge  $(l,overline(l))$ means the $overline(l) in S$ implying that $l$ is assigned `false`.
    - On the otherhand since $e_G_phi (S,overline(S)) = n + 5m$, each clause gadget has 2 edges crossing $(S,overline(S))$, meaning that this clause gadget has at least one vertex in $S$ and one in $overline(S)$. 

  
