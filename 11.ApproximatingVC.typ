#import "settings/mstyle.typ": *
#import algorithmic: algorithm-figure, style-algorithm
#show: style-algorithm

#show: conf.with(
  handout: false,
  subtitle: [Approximating Vertex Cover],
)

#title-slide()

= Vertex Cover

== The Problem

#definition[
  *Vertex Cover (VC)*

  *Given:* An undirected graph $G = (V, E)$.

  *Find:* A minimum set $C subset.eq V$ such that every edge $e in E$ has at least one endpoint in $C$.
]

#pause

#grid(
  columns: (1fr, auto),
  gutter: 1em,
  [
    - VC is NP-hard (one of Karp's 21 NP-complete problems)
    - We seek a polynomial-time *approximation algorithm*

    #pause

    #observation[
      The complement $V without C$ of a vertex cover is an *independent set*, and vice versa. So 
      $
      C  "minimum VC" <=> V without C "maximum independent set."
      $
    ]
  ],
  cetz-canvas({
    import cetz.draw: *
    let vpos = (
      "a": (0, 0),
      "b": (1.5, 1),
      "c": (3, 0),
      "d": (1.5, -1),
    )
    for (name, pos) in vpos {
      circle(pos, radius: 0.18, name: name, fill: white, stroke: black)
      content(pos, text(size: 0.75em, name))
    }
    line("a", "b")
    line("b", "c")
    line("c", "d")
    line("d", "a")
    line("b", "d")
    // highlight cover
    for name in ("b", "d") {
      circle(vpos.at(name), radius: 0.18, fill: red.lighten(40%), stroke: red)
    }
  })
)

== Failed Greedy Approaches


#block(width: 50%)[
  #set text(size: 0.86em)
The natural greedy algorithm fails to give a constant approximation ratio:

#pause

*Greedy 1: Pick highest-degree vertex repeatedly*

#algorithm-figure(
  [Greedy-Degree],
  vstroke: .5pt + luma(200),
  {
    import algorithmic: *
    While([$E != emptyset$], {
      Assign([$v$], [$arg max_(u in V) deg(u)$])
      Line([Add $v$ to $C$; remove $v$ and all incident edges])
    })
    Return([$C$])
  }
)
    #place(
    dx: 110%,
    dy: -60%,
    figure(image("figures/avc1.png", width: 90%),)
  )

    #place(
    dx: 110%,
    dy: -70%,
    [Consider the following construction of graph $R$ with $r.$]
  )

#pause

Minimum *vc* is the set $L$ of size $r$.
- The alogirthm may pick repeatedly vertices in $R_1$ then $R_2, R_3...$ returning the set $R$.
- $|R|=sum_(i=1)^r |R_i| = sum_(i=1)^r floor(r/i) approx r dot sum_(i=1)^r 1/i = Theta(r log r)$.
- Approximation ratio of $|R|\/|L| = Omega(log r)$

#[
  #set align(center)
  #tr[The Greedy algorithm is $Theta(log r)$ approximation]
]

// #observation[
//   This gives a $Theta(log n)$ approximation — same as greedy set cover. The ratio is *not* $O(1)$.
// ]
]

#[
  #set align(center)
  *We can do better!*
]

= 2-Approximation via Max Matching

== The Algorithm
#set text(size: 0.8em)

#observation[
  Let $M$ be any *maximal matching* in $G$. Then $V(M)$ (the endpoints of $M$) is a vertex cover, and $|V(M)| = 2|M|$.
]

#pause

#algorithm-figure(
  [Approx-VC],
  vstroke: .5pt + luma(200),
  {
    import algorithmic: *
    Assign([$M$], [a maximal matching of $G$])
    Return([$V(M)$])
  }
)

#pause

#theorem[
  Approx-VC is a 2-approximation for Vertex Cover.
]

#proof[
  Let $C^*$ be an optimal vertex cover.

  - *Validity:* Every edge in $G$ is either in $M$ or shares an endpoint with some edge in $M$ (by maximality). Either way it is covered by $V(M)$.
  - *Ratio:* Every edge $e in M$ must have at least one endpoint in $C^*$, and matching edges are *disjoint*, so $|C^*| >= |M|$. Thus
    $ |V(M)| = 2|M| <= 2|C^*|. quad square $
]

#place(
  dx: 0%,
  dy: -10%,
  [
    #set text(size: 0.7em)
    #set align(horizon)
    #grid(
  columns: (0.15fr, 1fr),
  gutter: 2em,
  [
    #cetz-canvas({
      import cetz.draw: *
      // Diamond / K4 minus one edge
      let pts = (
        "t": (1.5, 2.5),
        "l": (0, 1),
        "r": (3, 1),
        "b": (1.5, -0.5),
      )
      // edges
      for (u, v) in (("t","l"),("t","r"),("l","b"),("r","b"),("l","r")) {
        line(pts.at(u), pts.at(v), stroke: gray)
      }
      // matching edges highlighted
      for (u, v) in (("t","l"),("r","b")) {
        line(pts.at(u), pts.at(v), stroke: (paint: blue, thickness: 2pt))
      }
      for (name, pos) in pts {
        let fill-col = if name in ("t","l","r","b") { white } else { white }
        circle(pos, radius: 0.2, fill: white, stroke: black, name: name)
        content(pos, text(size: 0.7em, name))
      }
      // cover vertices
      for name in ("t","l","r","b") {
        circle(pts.at(name), radius: 0.2, fill: red.lighten(40%), stroke: red)
        content(pts.at(name), text(size: 0.7em, name))
      }
    })
  ],
  [
    - Blue edges form a maximal matching $M$
    - $V(M) = {t, l, r, b}$ is the returned cover
    - Optimal cover: ${l, r}$ (size 2)
    - $|V(M)| = 4 = 2 dot |C^*|$ — tight example
  ]
)
  ]
)

= Savage's Algorithm

== DFS-Tree Approach

#set text(size: 0.88em)
#algorithm-figure(
  [Savage-VC],
  vstroke: .5pt + luma(200),
  {
    import algorithmic: *
    Assign([$T$], [a DFS tree of $G$])
    Return([$I(T):=$ all *internal* (non-leaf) vertices of $T$])
  }
)

*Trivially:* Every edge in $G$ has an endpoint in $I(T) ==> I(T)$ is a vertex cover.

#pause

#theorem[
  Savage's algorithm is a 2-approximation for Vertex Cover.
]

It suffices to prove:

#lemma[
  Let $T$ be a DFS tree and $I(T)$ its internal vertices. Then $T$ contains a matching of size $>= (|I(T)|) / 2$.
]

#pause

*Lemma $=>$ Theorem:* The matching in $T$ is also a matching in $G$, so $tau(G) >= nu(G) >= (|I(T)|)/2$. The algorithm returns $I(T)$, so $|I(T)| <= 2 tau(G)$. $square$

== Proof of Lemma

#proof[
  By induction on $e(T)$. Let $r$ be the root, $r_1, dots, r_k$ its children, $T_1, dots, T_k$ the subtrees rooted at them. For $T_1$: let $S_1, dots, S_ell$ be the subtrees rooted at the *children* of $r_1$.

  By the IH, $T$ contains a matching of size:
  $ >= underbrace(1, r"-"r_1) + sum_(j=1)^ell (|I(S_j)|)/2 + sum_(i=2)^k (|I(T_i)|)/2 $

  Since $sum_j |I(S_j)| + sum_(i >= 2) |I(T_i)| = |I(T)| - 2$ ($r$ and $r_1$ are internal but appear in neither sum), the matching has size $>= 1 + (|I(T)| - 2)/2 = (|I(T)|)/2$. $square$
]

#place(
    dx: 30%,
    dy: 0%,
    figure(image("figures/avc2.png", width: 35%),)
  )

= Minimum Weight Vertex Cover

== LP Relaxation
#set text(size: 0.86em)

*Weighted VC:* Each vertex $v$ has weight $w_v >= 0$. Minimize $sum_v w_v x_v$ subject to covering all edges.

#pause

*Integer Program:*
$ min sum_(v in V) w_v x_v, quad x_u + x_v >= 1; space forall {u,v} in E, quad x_v in {0,1}. $

#pause

*LP Relaxation:* #pause Replace $x_v in {0,1}$ with $x_v in [0,1]$:
$ min sum_(v in V) w_v x_v, quad x_u + x_v >= 1; space forall {u,v} in E, quad 0 <= x_v <= 1. $

#pause

#algorithm-figure(
  [LP-Round-VC],
  vstroke: .5pt + luma(200),
  {
    import algorithmic: *
    Assign([$x^*$], [optimal LP solution])
    Return([$C = {v in V : x^*_v >= 1/2}$])
  }
)

#pause

#lemma[
  $C = {v : x^*_v >= 1/2}$ is a valid vertex cover.
]
#v(-5pt)
#proof[
  For any edge ${u,v} in E$: $x^*_u + x^*_v >= 1$, so $max(x^*_u, x^*_v) >= 1/2$. Hence at least one of $u, v$ is in $C$. $square$
]

#pause

#theorem[
  LP-Round-VC is a 2-approximation for weighted vertex cover.
]

#v(-5pt)
#proof[
  $ w(C) = sum_(v : x^*_v >= 1/2) w_v <= sum_v w_v dot (2 x^*_v) = 2 dot underbrace("OPT"^*, #[cost of optimal \ LP solution]) <= 2 dot "OPT". quad square $
]

= A Randomized Algorithm

== The Algorithm

*Goal:* A randomized 2-approximation for (unweighted) Vertex Cover.

#pause

#algorithm-figure(
  [Rand-VC],
  vstroke: .5pt + luma(200),
  {
    import algorithmic: *
    Assign([$C$], [$emptyset$])
    While([$E != emptyset$], {
      Line([Pick any edge ${u, v} in E$])
      Line([Uniformly at random pick $x in {u,v}$ and set $C = C cup {x}.$])
      Line([Set $E = E backslash {e in E: x in e}.$])
    })
    Return([$C$])
  }
)

#pause

#theorem[
  Rand-VC is a randomized 2-approximation: $EE[|C|] <= 2|C^*|$.
]

== Proof


#table(
  columns: (2fr, 0fr),
  stroke: none,
  [
    - $C^* :=$ an optimal VC
    - $C:=$ the cover produced by the algo
    - $|C|$ is a random variable (The size of the random VC is random)

    *Goal:* prove that $EE[|C|] <= 2|C^*|$.

    Each round during the edge $u v in E(G)$ the algo flips a fair coin:
      - Define a coin toss *good* if $x in C^*$ 
        - $Pr(x in C^*) >= 1/2$ #h(1fr) #tr[(if both $u, v in C$ then with probability 1 we are "good".)]
      - $\#$ of good tosses is at most $|C^*|$ #h(1fr) #tr[(Otherwise $C^* subset.eq C$ so that $C$ is a VC.)]

    Define $X$ the random variable that counts the number of coin tosses required to get to $|C^*|$ *good* coin tosses.
    - $E[X] >= E[|C|]$ #h(1fr) #tr[(in $X$ each success has probability exactly $1/2$ in $C$ its $>=1/2$.)]
    
    Define $X_i:= \#$ of tosses needed to get the $i'$th *good* toss. 
    - $X = X_1 + X_2 + ... + X_(|C^*|)$
    By linearity of expectation
    $
      EE(X) = sum_(i=1)^(|C^*|) EE(X_i)
    $ 
    - $forall i: space X_i ~ "Geo"(1\/2) => EE(X_i) = 2.$
    
    #h(0pt) $==>$ #v(-20pt)
    $
     EE(|C|) <= EE(X) = sum_(i=1)^(|C^*|) EE(X_i) <= 2|C^*|. 
    $
    #h(1fr) $square$
  ],
  []

)
