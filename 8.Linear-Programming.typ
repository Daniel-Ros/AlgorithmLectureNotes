#import "settings/mstyle.typ": *
#import algorithmic: algorithm-figure, style-algorithm
#show: style-algorithm

#show: conf.with(
  handout: false,
  subtitle: [Linear Programming],
)

#let ba = $bold(a)$
#let bx = $bold(x)$
#let bb = $bold(b)$
#let b0 = $bold(0)$
#let bc = $bold(c)$
#let by = $bold(y)$
#let bw = $bold(w)$
#title-slide()

= Linear Programming

== What is Linear Programming?
#[
  #set align(horizon)
  #set text(size: 0.9em)
  - *Example:*
    - In a power grid, we have $n$ power plants and $m$ cities. We want to decide how much electricity each plant should produce to meet the demand at minimum cost.
    - Let $x_i$ be the amount of electricity produced by plant $i$.
    - Let $b_j$ be the demand at city $j$.
    - Denote by $a_(i,j)$ the amount of electricity from plant $i$ that is  sent to city $j$.
   - For each demand node $j$, the plants contribute enough power to meet the demand:
  $
    a_(1,j)x_1 + a_(2,j)x_2 + ... + a_(n,j)x_n >= b_j
  $
  - If each plant also has a cost $c_i$, then the total cost is $sum_(i=1)^n c_i x_i$.
#pagebreak()
  - This example suggests the general linear-programming template:
  $
    underbrace(
      #box(stroke: black, radius: 6pt, inset: 8pt)[
        $min_(x in RR^n) c^t x$
      ],
      #[objective]
    ) \
    #h(20pt)
    underbrace(
      #box(stroke: black, radius: 6pt, inset: 8pt)[
        $A x <= b, quad x >= 0$
      ],
      #[constraints]
    )
  $
  - So a linear program chooses the values of $x_1, ..., x_n$ to optimize a linear objective while satisfying linear constraints. More generally, the objective can be written as either a minimization or a maximization problem.
]

== IP's and IP's in Matricial form.
// In a matricial form:
// #v(-10pt)
#definition[
  An Integer program is an optimization problem over $bx in ZZ^n$ that can be written in one of the following six forms:
  #table(
    columns: (1fr, 1fr, 1fr),
    stroke: none,
    [$max{ bc^T bx : A bx <= bb }$],
    [$max{ bc^T bx : A bx <= bb, bx >= b0 }$],
    [$max{ bc^T bx : A bx = bb, bx >= b0 }$],

    [$min{ bc^T bx : A bx >= bb }$],
    [$min{ bc^T bx : A bx >= bb, bx >= b0 }$],
    [$min{ bc^T bx : A bx = bb, bx >= b0 }$],
  )
]
#v(-10pt)
#definition[
  A linear program is an optimization problem over $bx in RR^n$ that can be written in one of the following six forms:
  #table(
    columns: (1fr, 1fr, 1fr),
    stroke: none,
    [$max{ bc^T bx : A bx <= bb }$],
    [$max{ bc^T bx : A bx <= bb, bx >= b0 }$],
    [$max{ bc^T bx : A bx = bb, bx >= b0 }$],

    [$min{ bc^T bx : A bx >= bb }$],
    [$min{ bc^T bx : A bx >= bb, bx >= b0 }$],
    [$min{ bc^T bx : A bx = bb, bx >= b0 }$],
  )
  #v(-5pt)
]
#remark[
  #set align(center)
  #set text(weight: "bold", fill: red)
  #v(-15pt)
  LP's $in$ P but IP's $in$ NPH
]


= Examples
== Incidence matrix
The _incidence_ matrix of a graph $G$ is given by
#place(
  top + center,
  dx: -20%,
  dy: 10%,
  figure(
    image("figures/LPi2.png", width: 50%),
  ),
)

#place(
  top + center,
  dx: 20%,
  dy: 50%,
  figure(
    image("figures/LPi3.png", width: 50%),
  ),
)

#let b1 = $bold(1)$

== Maximum Matching
Given $G$ with $n$ vertices and $m$ edges, we seek a vector $bx in {0,1}^m$ s.t.
- $x_e = 1$ when edge $e$ belongs to the matching, and $x_e = 0$ otherwise.
- maximize $sum_(e in E) x_e = max b1^t bx$. #h(1fr) #tr[(We want maximum matching)]


This vector $bx$ is the characteristic vector of a matching in $G$.

*So far the above doesn't define a matching!*
\ *We need to define constraints.*
#pause
- For every vertex $v in V$: $sum_(e in E : v in e) x_e <= 1$.#h(1fr) #tr[(Every vertex can be matched only once)]
// - $x_e in {0,1}$ for all $e in E$. #h(1fr) #tr[(We either choose an edge or we don't)]
#pause
*or by matricial form*
#place(
  top + center,
  dx: 9%,
  dy: 55%,
  figure(
    image("figures/LPi4.png", width: 70%),
  ),
)

#place(
  top + left,
  dx: 5%,
  dy: 75%,
  block(
    stroke: black,
    inset: 10pt,
    radius: 5pt,
    [
      $
        bx in ZZ^n
      $
      #v(-15pt)
      $
        max b1^t bx
      $
    ],
  ),
)


#pagebreak()
For the max-matching problem, we arrive at the following

#table(
  columns: (0.2fr, 1fr, 1fr),
  stroke: none,
  [],
  [
    #block(
      stroke: black,
      inset: 15pt,
      radius: 5pt,
      [
        #set align(center)
        *IP* for maximum matching
        $
          max_(x in ZZ^m){ b1^t bx : M bx <= b1, bx>=b0}
        $
      ],
    )
  ],

  [
    #v(10pt)
    $underbrace(
      #block(stroke: black, inset: 15pt, radius: 5pt, [
        #set align(center)
        *LP* for maximum matching
        $ max_(bx in RR^m){ b1^t bx : M bx <= b1, bx>=b0} $
      ]), #[This called the: \ *Corresponding LP Relaxation*]
    )$
  ],
)
#remark[
  We dont need to bound $bx <= b1$ as if there exists $i$ for which $x_i> 1$.
  Then, there must exist $j in [m]$ for which $M_(j,i) < 1$.
  But, we know that $M$ is the _incidence matrix_ of $G$ so that
  for exactly two indicies $j_1, j_2$ we have $M_(j_1,i)=1$ and  $M_(j_1,i)=1$.
]

== Vertex Cover
Given $G$ with $n$ vertices and $m$ edges, we seek a vector $by in {0,1}^n$ s.t.
- $y_v = 1$ when vertex $v$ belongs to the *vc*, and $y_v = 0$ otherwise.
- minimize $sum_(v in V) y_v = min b1^t by$. #h(1fr) #tr[(We want minimum vertex-cover)]

*Constaints:* $forall e in E: sum_(v in e) y_v >= 1$ #h(1fr) #tr[(Every edge is covered at least once)]


This vector $by$ is the characteristic vector of a vertex cover in $G$.


#pause
*or by matricial form*
#place(
  top + center,
  dx: 12%,
  dy: 55%,
  figure(
    image("figures/LPi5.png", width: 70%),
  ),
)

#place(
  top + left,
  dx: 5%,
  dy: 75%,
  block(
    stroke: black,
    inset: 10pt,
    radius: 5pt,
    [
      $
        by in ZZ^n
      $
      #v(-15pt)
      $
        min b1^t by
      $
    ],
  ),
)


#pagebreak()
#[
  #set align(horizon)
  For the min-vc problem, we arrive at the following
  #v(-30pt)
  #table(
    columns: (0.2fr, 1fr, 1fr),
    stroke: none,
    [],
    [
      #block(
        stroke: black,
        inset: 15pt,
        radius: 5pt,
        [
          #set align(center)
          *IP* for minimum-vc
          $
            min_(by in ZZ^n){ b1^t by : M^t by >= b1, by>=b0}
          $
        ],
      )
    ],

    [
      #v(41pt)
      $underbrace(
        #block(stroke: black, inset: 15pt, radius: 5pt, [
          #set align(center)
          *LP* for minimum-vc
          $ min_(by in RR^n){ b1^t by : M by >= 1, by>=0} $
        ]), #[This called the: \ *Corresponding LP Relaxation*]
      )$
    ],
  )
]

#pause
*What if we wanted vc with minimum weight?* i.e. every vertex $v in V$ has weight $w_v in RR$?
#pause
$
  min_( by in ZZ^n){ underbrace(
      bw^t by,
      sum_(v in V) w_v dot y_v
    ) : M^t by >= b1, by>=b0}
$

== Vertex Cover vs Maximum Matching
#[
  By Konig we know that in bipartite graphs it must hold
  #v(-10pt)
  #table(
    columns: (0.2fr, 1fr, 0.35fr, 1fr),
    stroke: none,
    [],
    [
      #block(
        stroke: black,
        inset: 15pt,
        radius: 5pt,
        [
          #set align(center)
          *IP* for maximum matching
          #v(-10pt)
          $
            max_(bx in ZZ^n){ b1^t bx : M bx <= b1, bx>=b0}
          $
        ],
      )
    ],
    [
      // #h(-50pt)
      #set align(horizon)
      #set text(size: 5em)
      =],
    [
      #block(
        stroke: black,
        inset: 15pt,
        radius: 5pt,
        [
          #set align(center)
          *IP* for minimum-vc
          #v(-10pt)
          $
            min_(by in ZZ^n){ b1^t by : M^t by >= b1, by>=b0}
          $
        ],
      )
    ],
  )
  #pause
  #v(-15pt)
  In fact
  #v(-15pt)
  #table(
    columns: (0.2fr, 1fr, 0.35fr, 1fr),
    stroke: none,
    [],
    [
      #block(
        stroke: black,
        inset: 15pt,
        radius: 5pt,
        [
          #set align(center)
          *LP* for maximum matching
          #v(-10pt)
          $
            max_(bx in RR^n){ b1^t bx : M bx <= b1, bx>=b0}
          $
        ],
      )
    ],
    [
      // #h(-50pt)
      #set align(horizon)
      #set text(size: 5em)
      =],
    [
      #block(
        stroke: black,
        inset: 15pt,
        radius: 5pt,
        [
          #set align(center)
          *LP* for minimum-vc
          #v(-10pt)
          $
            min_(by in RR^n){ b1^t by : M^t by >= b1, by>=b0}
          $
        ],
      )
    ],
  )
  #pause
  #v(-10pt)
  If $G$ is not bipartite, then in fact
  #place(
    dx: 3%,
    dy: 5%,
    table(
      columns: (0.05fr, 1fr, 0.25fr, 1fr, 0.4fr),
      align: (center, right, left, right, left),
      stroke: none,
      [],
      [
        #block(
          stroke: black,
          inset: 15pt,
          radius: 5pt,
          [
            #set align(center)
            *IP* for maximum matching
            #v(-10pt)
            $
              max_(bx in ZZ^n){ b1^t bx : M bx <= b1, bx>=b0}
            $
          ],
        )
      ],
      [
        // #h(-50pt)
        #set align(horizon)
        #set text(size: 2em)
        $in$ P],
      [
        #block(
          stroke: black,
          inset: 15pt,
          radius: 5pt,
          [
            #set align(center)
            *IP* for minimum-vc
            #v(-10pt)
            $
              min_(by in ZZ^n){ b1^t by : M^t by >= b1, by>=b0}
            $
          ],
        )
      ],
      [
        // #h(-50pt)
        #set align(horizon)
        #set text(size: 2em)
        $in$ NPC],
    ),
  )
]

= Geometric analysis of LP's
== Geometric analysis of LP's
#[
  #set align(horizon)
  Consider the following *LP*:
  #block(width: 30%, stroke: black, radius: 15pt, inset: 15pt)[
    $max x_1+x_2$ \
    $s.b.t.$
    #v(-10pt)
    $
      #h(50pt)-x_1 + x_2 & <=1 \
              x_1 + 6x_2 & <=15 \
              4x_1 - x_2 & <=10 \
       x_1 >= 0 #h(20pt) \
       x_2 >= 0 #h(20pt)
    $
  ]

  #place(
    horizon + center,
    dx: 25%,
    dy: -15%,
    figure(
      image("figures/LPi1.png", width: 52%),
    ),
  )

  #[
    #set align(center)
    #block(stroke: black, radius: 15pt, inset: 15pt)[
      $
        max_(x in RR^2) (1, 1) dot (x_1, x_2)
        text("s.t.") quad
        mat(
          -1, 1;
          4, 6;
          4, -1
        )
        mat(
          x_1;
          x_2
        )
        <=
        mat(
          1;
          15;
          10
        ), quad
        (x_1, x_2) >= (0, 0)
      $
    ]
  ]
]

#pagebreak()
#v(80pt)
#block(width: 50%)[
  Solving the problem Geometrically,
  would mean taking the line $x_1+x_2=c$
  and moving it in the direction $(1,1)$ until we get out of constraint.
]
#place(
  horizon + center,
  dx: 25%,
  dy: -15%,
  figure(
    image("figures/LPi6.png", width: 52%),
  ),
)

#pause
#place(
  horizon + center,
  dx: -25%,
  dy: 30%,
  figure(
    image("figures/LPi7.png", width: 46%),
  ),
)
#place(
  horizon + center,
  dx: 25%,
  dy: 34%,
  block(width: 50%)[
    #set align(center)
    If we change the constraint to $max 1/6x_1 + x_2$. \
    Then, we have infinitely maxny solutions.
  ],
)
#place(
  horizon + center,
  dx: -2%,
  dy: 34%,
  block(width: 50%)[
    #set text(size: 2em)
    #set align(center)
    $<==$
  ],
)


== Feasibility and Boundedness
#[
  #set align(horizon)
  #set text(size: 0.87em)
  An LP can fail to have an optimal solution in two ways:
  #v(-10pt)
  #table(
    columns: (1fr, 1fr),
    stroke: none,
    align: top,
    [
      *Infeasible* --- flipping two constraints of our example:
      #block(stroke: (paint: red.darken(10%), thickness: 1pt), radius: 10pt, inset: 10pt)[
        $max x_1 + x_2$
        #v(-3pt)
        $
          x_2 - x_1  >= 1 \
          x_1 + 6x_2 <= 15 \
          4x_1 - x_2 >= 10 \
          x_1, x_2 >= 0
        $
        #tr[(constraints 1 & 3 flipped)]
      ]
      The constraints have *no common intersection* --- the LP is _infeasible_.
    ],
    [
      #pause
      *Unbounded* --- removing two constraints:
      #block(stroke: (paint: blue.darken(10%), thickness: 1pt), radius: 10pt, inset: 10pt)[
        $max x_1 + x_2$
        #v(-3pt)
        $
          -x_1 + x_2 <= 1 \
          x_1, x_2 >= 0
        $
      ]
      Feasible solutions exist but the objective grows *without bound* --- the LP is _unbounded_.
    ],
  )

  #pause
  #v(10pt)
  #theorem[
    #set align(center)
    Any *feasible* and *bounded* LP has an *optimal* solution.
  ]
]

== Standard forms of LP's
#set align(horizon)
#definition[
  A Linear program in one of the following 2-forms:
  #table(
    columns: (0.3fr, 1fr, 1fr),
    stroke: none,
    [], [$max{ bc^T bx : A bx = bb, bx >= b0 }$], [$min{ bc^T bx : A bx = bb, bx >= b0 }$],
  )
  is said to be in *equational form*;
]
#remark[
  Optimal solution for *LP's* in *equational form* are the easiest to exaplain and we will focus on those.
]

== Converting to Equational Form
#[
  #set align(horizon)
  #set text(size: 0.88em)
  Any LP can be converted to equational form. Consider a *mixed* LP (not in any standard form):
  #table(
    columns: (1fr, 1fr),
    stroke: none,
    align: top,
    [
      #block(stroke: black, radius: 10pt, inset: 10pt, width: 95%)[
        $max 3x_1 - 2x_2$
        #v(-3pt)
        $
          2x_1 - x_2 & <= 4 \
          x_1 + 3x_2 & >= 5 \
          x_1         & >= 0
        $
        ($x_2$ is *free* --- no sign constraint)
      ]

      #pause
      #v(5pt)
      *Step 1* ($<=$): introduce _slack variable_ $x_3 >= 0$ and set:
      $
      2x_1 - x_2 & <= 4 => 2x_1 - x_2 + x_3 = 4,
      $

      #pause
      *Step 2* ($>=$): multiply by $-1$, then add slack $x_4 >= 0$:
      $
      #h(20pt) x_1 + 3x_2 & >= 5 =>
      -x_1 - 3x_2 + x_4 = -5
      $

      #pause
      *Step 3* (free var): swap $x_2 = y_1 - y_2$, with $y_1, y_2 >= 0$.
    ],
    [
      #pause
      Final equational LP over $(x_1, y_1, y_2, x_3, x_4 >= 0)$:
      #block(stroke: black, radius: 10pt, inset: 10pt, width: 95%)[
        $max 3x_1 - 2y_1 + 2y_2$
        #v(-3pt)
        $
          2x_1 - y_1 + y_2 + x_3 & = 4 \
          -x_1 - 3y_1 + 3y_2 + x_4 & = -5 \
          x_1, y_1, y_2, x_3, x_4 & >= 0
        $
      ]

      #tr[
        #set align(center)
        By solving the final LP we can derive the optimal values for the original LP]

      #pause
      #v(5pt)
      #remark[
        Non-negativity constraints ($x >= 0$) are called *non-negativity constraints*.
        The forms with $=$ and $bx >= b0$ are the simplest to analyze.
      ]
    ],
  )
]

= LP's in Equational Form

== Basic Solutions
#[
  #v(-50pt)
  #set align(horizon)
  #set text(size: 0.88em)
  We study LPs of the form $max{ bc^T bx : A bx = bb, bx >= b0 }$ where $A in M_(m times n)(RR)$ with $"rank"(A) = m$ (so $m <= n$).

  #pause

  #definition[
    $bx in RR^n$ satisfying $A bx = bb$ is called *basic* if $exists B subset.eq [n]$ with $|B| = m$ s.t.:
    - $A_B$ is *non-singular* (columns of $A$ indexed by $B$ are linearly independent), and
    - $x_j = 0 quad forall j in.not B$.

    A basic $bx$ satisfying also $bx >= b0$ is a *basic feasible solution* (BFS).
  ]

  #pause

  #remark[
    Basic solutions may *fail* non-negativity --- hence the distinction.
  ]

  #place(
  horizon + center,
  dx: 0%,
  dy: 42%,
  figure(
    image("figures/LPi8.png", width: 80%),
  ),
)

  #pagebreak()
#[
    #set align(horizon)
  #set text(size: 0.88em)
  #observation[
    Let $bx in RR^n$ be feasible. Set $K := { j in [n] : x_j > 0 }$. Then
    $
      bx "is basic" <==> "columns of" A_K "are linearly independent."
    $
  ]
]


  *Proof of observation:*

  $(==>)$: $bx$ is basic, so $exists B$ with $|B| = m$, $A_B$ non-singular, and $x_j = 0$ for $j in.not B$. Since $bx >= b0$ we have $K subset.eq B$, so columns of $A_K$ are a subset of the independent columns of $A_B$  -- hence independent.

  #pause

  $(<==)$: Extend the columns of $A_K$ to a maximal independent set $B$ in $A$. Since $"rk"(A) = m$, we get $|B| = m$, so $A_B$ is non-singular. As $K subset.eq B$, we have $x_j = 0$ for all $j in.not B$. $square$
]

#pagebreak()
#[
  #set align(horizon)
  *Algorithm* -- to decide if a feasible $bx$ is basic:

  #block(stroke: black, radius: 10pt, inset: 10pt)[
    *Input:* feasible $bx in RR^n$, i.e. $bx >= b0$ and $A bx = bb$.
    1. Set $K = { j in [n] : x_j > 0 }$.
    2. If columns of $A_K$ are independent, return *basic*; else return *not basic*.
  ]
]

== Properties of Basic Feasible Solutions
#[
  #set align(horizon)
  #set text(size: 0.88em)

  #lemma[
    Any $B subset.eq [n]$ with $|B| = m$ has *at most one* basic feasible solution fitting it.
  ]

  *Proof:* Let $N = [n] without B$, and fix a solution $bx in RR^n$ satisfying $A bx = bb$. \
  -  If $bx$ fits $B$  $==>$ then $bx_N = b0$.
  - so $A_B bx_B + A_N bx_N = bb$ $==>$ $A_B bx_B = bb$.
  - Since $A_B$ is non-singular, $bx_B = A_B^(-1) bb$ is uniquely determined. $square$
]

  #pagebreak()
#[
  #set align(horizon)
  #proposition[
    #set align(center)
    #v(-30pt)
    There are at most $binom(n, m)$ basic feasible solutions.
  ]

  #pause
  #v(-5pt)
  This alone is not useful unless optimal solutions are *basic*:

  #theorem[
    Let LP $max{ bc^T bx : bx >= b0, A bx = bb }$ be feasible and bounded. \ For every feasible $bx_0$, there exists a BFS $overline(bx)$ s.t. $bc^T overline(bx) >= bc^T bx_0$.
  ]

  #pause
  #v(-5pt)
  Applying this to an optimal $bx_0$ (which exists since the LP is feasible and bounded):

  $
    exists "an optimal basic feasible solution."
  $

  We now have an *exponential algorithm*: enumerate all $binom(n, m)$ bases, find each of the *Basic Feasible Solutions*, and pick the best.
]

= Geometric View

== The Feasible Polyhedron
#[
  #set align(horizon)
  #set text(size: 0.875em)

  The linear constraints of a feasible, bounded LP form a *convex polyhedron*:

  #table(
    columns: (1fr, 1fr),
    stroke: none,
    align: top,
    [
      *Convex*: any line segment between two feasible points stays inside the region.

      #v(5pt)
      #block(stroke: gray, radius: 8pt, inset: 8pt)[
        Every half-space ${ bx : ba^T bx <= b }$ is convex. The feasible region --- as their intersection --- is convex too.
      ]
    ],
    [
      *Not-convex*: a line segment between two feasible points may *exit* the region.

      #v(5pt)
      #block(stroke: gray, radius: 8pt, inset: 8pt)[
        The feasible region of an *IP* is generally not convex (integer lattice points only).
      ]
    ],
  )

  #pause
  #v(5pt)
  - *Basic feasible solutions* lie on the *vertices* and *edges* of the polyhedron.
  - The proposition above guarantees an optimal solution at a *vertex*.

  #pause
  #v(5pt)

  Two classical algorithms traverse the vertices in smarter ways:
  #table(
    columns: (0.15fr, 1fr, 1fr),
    stroke: none,
    [],
    [
      #block(stroke: black, radius: 10pt, inset: 12pt, width: 90%)[
        #set align(center)
        *Simplex Algorithm* \
        #set align(left)
        #set text(size: 0.9em)
        Moves along edges of the polyhedron, improving the objective at each step. Exponential worst-case, but very fast in practice.
      ]
    ],
    [
      #block(stroke: black, radius: 10pt, inset: 12pt, width: 90%)[
        #set align(center)
        *Ellipsoid Algorithm* \
        #set align(left)
        #set text(size: 0.9em)
        Approximates the feasible region with shrinking ellipsoids. First provably polynomial-time LP algorithm.
      ]
    ],
  )
]

= Duality

== LPs Come in Pairs
#[
  #set align(horizon)
  #set text(size: 0.9em)

  Every LP (the *primal*) has a companion LP called its *dual*.

  #pause

  We have already seen duality:

  #table(
    columns: (0.15fr, 1fr),
    stroke: none,
    [],
    [
      #block(stroke: black, radius: 8pt, inset: 10pt)[
        *König's Theorem:* $quad tau(G) = nu(G)$ in bipartite graphs

        $
        max "matching" = min "vertex cover"
        $
      ]
    ],
  )
  #table(
    columns: (0.15fr, 1fr),
    stroke: none,
    [],
    [
      #block(stroke: black, radius: 8pt, inset: 10pt)[
        *Menger's Theorem:* max \# of internally disjoint $A$-$B$ paths $=$ min $A$-$B$-cut size
      ]
    ],
  )

  #pause

  *Why is duality useful?*

  - It provides *certificates of optimality* for feasible primal solutions.
  - It enables LP-based algorithms *without* invoking expensive methods like Simplex or Ellipsoid.
    - Dijkstra's algorithm was designed exactly this way.
]

#pagebreak()
#[
  #set align(horizon)
  #set text(size: 0.87em)

  #v(-15pt)
  *Example:* Consider the LP
  #v(-5pt)
  #block(width: 45%, stroke: black, radius: 10pt, inset: 12pt)[
    $max 5x_1 + 5x_2$ \
    $s.b.t.$
    #v(-25pt)
    $
      3x_1 + x_2  & <= 7 \
      2x_1 + 4x_2 & <= 8 \
      x_1, x_2    & >= 0
    $
  ]

  Geometrically, $(1, 2)$ is optimal with objective value $5 dot 1 + 5 dot 2 = 15$.

  #pause
  #v(5pt)

  *Q:* How do we *prove* $(1, 2)$ is optimal without drawing a picture?

  #pause

  *A:* Sum the two constraints (both multiplied by $1$):
  $
    (3x_1 + x_2 <= 7) + (2x_1 + 4x_2 <= 8) quad => quad 5x_1 + 5x_2 <= 15.
  $
  Every feasible solution satisfies $5x_1 + 5x_2 <= 15$, and $(1,2)$ achieves $15$ -- so it is *optimal*. $square$
]

#pagebreak()
#[
  #set align(horizon)
  #set text(size: 0.8em)
  Now change the objective to $max 7x_1 + 4x_2$ (same constraints):
  #block(width: 45%, stroke: black, radius: 10pt, inset: 12pt)[
    $max 7x_1 + 4x_2$ \
    $s.b.t.$
    #v(-25pt)
    $
      3x_1 + x_2  & <= 7 \
      2x_1 + 4x_2 & <= 8 \
      x_1, x_2    & >= 0
    $
  ]

  #pause

  Summing with equal weights $(1,1)$ gives $5x_1 + 5x_2 <= 15$ -- *wrong coefficients*. We need to scale more carefully.

  #pause

  *Q:* Why is $(1,2)$ no longer optimal? Why is $(2,1)$ optimal?

  #pause

  *A:* Look for weights $y_1, y_2 >= 0$ such that the weighted sum of constraints *matches* the objective:
  $
    y_1 (3x_1 + x_2 <= 7) + y_2 (2x_1 + 4x_2 <= 8) \
    => quad underbrace((3y_1 + 2y_2), = 7) x_1 + underbrace((y_1 + 4y_2), = 4) x_2 <= 7y_1 + 8y_2
  $

  #pause

  Solving $3y_1 + 2y_2 = 7$ and $y_1 + 4y_2 = 4$ gives $y_1 = 2$, $y_2 = 1/2$.

  #pause

  Upper bound: $7y_1 + 8y_2 = 7 dot 2 + 8 dot 1/2 = 14 + 4 = 18$.

  $(2,1)$ is feasible ($3 dot 2 + 1 = 7$, $2 dot 2 + 4 dot 1 = 8$) and achieves $7 dot 2 + 4 dot 1 = 18$ -- so it is *optimal*. $square$
]



== Constructing the Dual
#[
  #set align(horizon)
  #set text(size: 0.85em)

  Given the LP $max{ bc^T bx : A bx <= bb }$ ($m$ constraints, $n$ variables):

  #pause

  1. Assign a *dual variable* $y_i >= 0$ to each constraint $ba_i^T bx <= b_i$.

  #pause

  2. Multiply constraint $i$ by $y_i$ and *sum*:
  $
    sum_i y_i (ba_i^T bx) <= sum_i y_i b_i quad => quad (A^T by)^T bx <= by^T bb.
  $

  #pause

  3. To obtain an upper bound on $bc^T bx$, require $A^T by = bc$; then $bc^T bx <= by^T bb$.

  #pause

  #observation[
    $A in M_(m times n)(RR)$, $bc in RR^n$, $bb in RR^m$. If $A^T by = bc$ and $by >= b0$, then $bc^T bx <= by^T bb$ whenever $A bx <= bb$.

    *Proof:* $by^T bb >= by^T (A bx) = (A^T by)^T bx = bc^T bx.$ $quad square$
  ]

  #pause

  #theorem[
    *Weak Duality Theorem*
    $
      max{ bc^T bx : A bx <= bb } <= min{ by^T bb : A^T by = bc, by >= b0 }
    $
    whenever both LPs are feasible and bounded.
  ]
]

#pagebreak()
#[
  #set align(horizon)
  #set text(size: 0.88em)

  *The Primal $->$ Dual recipe:* each primal *constraint* $->$ dual *variable*; each primal *variable* $->$ dual *constraint*.

  #table(
    columns: (0.05fr, 1fr, 0.08fr, 1fr),
    stroke: none,
    align: top,
    [],
    [
      #block(stroke: black, radius: 8pt, inset: 10pt, width: 95%)[
        #set align(center)
        *Primal constraint* $->$ *dual variable*
        #v(3pt)
        #table(
          columns: (1fr, 0.15fr, 1fr),
          stroke: none,
          align: left,
          [$angle.l ba_i, bx angle.r <= b_i$], [$=>$], [$y_i >= 0$],
          [$angle.l ba_i, bx angle.r = b_i$], [$=>$], [$y_i in RR$],
          [$angle.l ba_i, bx angle.r >= b_i$], [$=>$], [$y_i <= 0$],
        )
      ]
    ],
    [],
    [
      #block(stroke: black, radius: 8pt, inset: 10pt, width: 95%)[
        #set align(center)
        *Primal variable* $->$ *dual constraint*
        #v(3pt)
        #table(
          columns: (1fr, 0.15fr, 1fr),
          stroke: none,
          align: left,
          [$x_i >= 0$], [$=>$], [$(A^T by)_i >= c_i$],
          [$x_i <= 0$], [$=>$], [$(A^T by)_i <= c_i$],
          [$x_i in RR$], [$=>$], [$(A^T by)_i = c_i$],
        )
      ]
    ],
  )

  == Examples
  Applying the recipe to our LP:
  #table(
    columns: (0.08fr, 1fr, 0.08fr, 1fr),
    stroke: none,
    align: (right, right, center, left),
    [$(P)$],
    [
      #block(stroke: black, radius: 8pt, inset: 10pt)[
        $max 5x_1 + 5x_2$ \
        $3x_1 + x_2 <= 7$ \
        $2x_1 + 4x_2 <= 8$ \
        $x_1, x_2 >= 0$
      ]
    ],
    [#set align(horizon); $<->$],
    [
      #block(stroke: black, radius: 8pt, inset: 10pt)[
        $(D) quad min 7y_1 + 8y_2$ \
        $3y_1 + 2y_2 >= 5$ \
        $y_1 + 4y_2 >= 5$ \
        $y_1, y_2 >= 0$
      ]
    ],
  )

  #pause
  #v(3pt)
  #remark[The dual of the dual is the primal.]
]

== Strong Duality
#[
  #set align(horizon)
  #set text(size: 0.88em)

  Weak duality gives an upper bound. The true connection is *much stronger*:

  #pause

  #theorem[
    *Strong Duality Theorem*

    Let $(P)$ and $(D)$ be a primal LP and its dual. *Precisely one* of the following holds:
    1. Both $(P)$ and $(D)$ are *infeasible*.
    2. $(P)$ is *unbounded* and $(D)$ is *infeasible*.
    3. $(P)$ is *infeasible* and $(D)$ is *unbounded*.
    4. Both $(P)$ and $(D)$ are *feasible* (hence bounded) and their *optimal values coincide*: $"OPT"(P) = "OPT"(D)$.
  ]

  #pause

  Case 4 is the main message: when both are feasible, the *duality gap is zero*.

  #pause
  #v(5pt)

  *Important remarks:*
  - Duality does *not* apply to Integer Programming. It applies *only* to LP.

  #pause

  - The LP relaxations of Max Matching and Min VC are *always* dual to one another.
    - This has *no* bearing on their IP versions.
    - In particular, it does *not* imply that Min VC $in$ P.

]

#pagebreak()
#[
  #set align(horizon)
  #theorem[
    *Strong Duality Theorem*

    Let $(P)$ and $(D)$ be a primal LP and its dual. *Precisely one* of the following holds:
    1. Both $(P)$ and $(D)$ are *infeasible*.
    2. $(P)$ is *unbounded* and $(D)$ is *infeasible*.
    3. $(P)$ is *infeasible* and $(D)$ is *unbounded*.
    4. Both $(P)$ and $(D)$ are *feasible* (hence bounded) and their *optimal values coincide*: $"OPT"(P) = "OPT"(D)$.
  ]
  #remark[
    Showing the min-VC LP is the dual of the max-matching LP follows directly from the recipe above.
  ]
]

// == Example: a small LP
// #set align(horizon)
// #columns(2, [
//   - Maximize $z = 3x_1 + 2x_2$
//   - subject to:
//     - $x_1 + x_2 <= 4$
//     - $x_1 <= 2$
//     - $x_2 <= 3$
//     - $x_1, x_2 >= 0$
//   - The feasible set is a convex polygon.
//   - The optimal solution occurs at a vertex.
//   #colbreak()
//   #cetz.canvas({
//     import cetz.draw: *
//     line((0, 0), (4, 0), (4, 3), (0, 3), close: true, fill: rgb("#a0c8f0"), stroke: none)
//     line((0, 0), (4, 0), stroke: 1pt + gray)
//     line((0, 0), (0, 3), stroke: 1pt + gray)
//     line((0, 4), (4, 0), stroke: (paint: blue, thickness: 2pt))
//     line((2, 0), (2, 3), stroke: (paint: blue, thickness: 2pt))
//     line((0, 3), (4.5, 3), stroke: (paint: blue, thickness: 2pt))
//     circle((2, 3), radius: 0.12, fill: black, stroke: none)
//     content((2, 3.3), [$(2,3)$], anchor: "south")
//   })
// ])
// #pause

// == Feasible Region
// - The feasible region of an LP is the intersection of half-spaces.
// - It is a convex polyhedron in high dimensions.
// - If an optimal solution exists, some extreme point is optimal.
// #pause
// #remark[
//   For two variables, each inequality defines a half-plane and the feasible region is a polygon.
// ]

// == Standard Form
// #definition[
//   A linear program in standard form is:
//   $
//     max{ c^T x : A x = b, x >= 0 }.
//   $
// ]
// - Every LP can be converted to standard form using slack and surplus variables.
// #pause
// - Example: $x_1 + x_2 <= 4$ becomes $x_1 + x_2 + s = 4$ with $s >= 0$.

// == Basic Feasible Solutions
// - A basic feasible solution is obtained by selecting a basis of $n$ independent constraints.
// - Set the non-basic variables to $0$ and solve the remaining equations.
// - If the solution is feasible, it corresponds to an extreme point.
// #pause
// #theorem[
//   If an LP has an optimal solution, then there is an optimal basic feasible solution.
// ]

// == The Simplex Method
// - Start from an initial basic feasible solution.
// - Move along edges of the feasible polyhedron to improve the objective.
// - Stop when no entering variable can improve the objective.
// #algorithm-figure(
//   "",
//   vstroke: .5pt + luma(200),
//   {
//     import algorithmic: *
//     Procedure("simplex", "LP", {
//       Assign([$B$], [_initial_ basis])
//       Assign([$x$], [_basic_ feasible solution])
//       While([there is an entering variable], {
//         Line([Choose entering variable $j$])
//         Line([Choose leaving variable $i$])
//         Line([Update basis $B$ and solution $x$])
//       })
//       LineBreak
//       Return([$x$])
//     })
//   },
// )

// == Duality
// - Every primal LP has a dual LP.
// - For primal $
//     max{ c^T x : A x <= b, x >= 0}
//   $ the dual is
//   $
//     min{ b^T y : A^T y >= c, y >= 0}
//   $.
// #pause
// - Weak duality: any feasible primal $x$ and dual $y$ satisfy $c^T x <= b^T y$.
// - Strong duality: if either problem has an optimal solution, both do and the objective values coincide.

// == Primal and Dual Example
// #grid(
//   columns: (1fr, 1fr),
//   stroke: none,
//   [
//     #text[
//       Primal:
//       $max 3x_1 + 2x_2$
//       s.t. $x_1 + x_2 <= 4$
//       $x_1 <= 2$
//       $x_2 <= 3$
//       $x_1, x_2 >= 0$
//     ]
//     #text[
//       Dual:
//       $min 4y_1 + 2y_2 + 3y_3$
//       s.t. $y_1 + y_2 >= 3$
//       $y_1 + y_3 >= 2$
//       $y_1, y_2, y_3 >= 0$
//     ]
//   ]
// )

// == Applications
// - Production planning and resource allocation.
// - Transportation and assignment problems.
// - Network flows and matching.
// - Machine learning models such as support vector machines.
// #pause
// - Linear programming is a foundational optimization tool in algorithms and operations research.

// == Summary
// - A linear program optimizes a linear objective subject to linear constraints.
// - The feasible region is convex and optimal solutions lie at vertices.
// - The simplex method moves between basic feasible solutions.
// - Duality provides certificates of optimality and bounds.

