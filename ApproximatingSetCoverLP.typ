#import "settings/mstyle.typ": *
#import algorithmic: algorithm-figure, style-algorithm
#show: style-algorithm

#show: conf.with(
  handout: false,
  subtitle: [Approximating Minimum Set Cover],
)

#let ac = "ac"
#let ba = $bold(a)$
#let bx = $bold(x)$
#let bb = $bold(b)$
#let b0 = $bold(0)$
#let bc = $bold(c)$
#let by = $bold(y)$
#let bw = $bold(w)$

#title-slide()

= LP Analysis of the Greedy Approximation Algorithm for Set-Cover

== Minimum Cost Set-Cover
#[
  #set align(horizon)
  #set text(size: 0.88em)

  #definition[
    *Minimum cost set-cover problem*

    *Given:* a hypergraph $H := (V, E)$ and a cost function $c: E -> RR_(>=0)$.

    *Goal:* find a hyperedge-cover $T subset.eq E$ with
    $ union.big_(e in T) e = V $ minimizing
    $ c(T) := sum_(e in T) c(e) $.
  ]

  #pagebreak()

  *IP formulation (min cost SC):*\
  Let $x_e$ be an indicator variable for whether $e in E$ is included in the cover. Then
  $
    min sum_(e in E) c(e) x_e \
    "s.t." sum_(e in C_v) x_e >= 1, quad forall v in V, quad C_v := { e in E : v in e } \
    x_e in {0,1}, quad forall e in E
  $



  *LP relaxation:*
  $
    min sum_(e in E) c(e) x_e \
    "s.t." sum_(e in C_v) x_e >= 1, quad forall v in V \
    0 <= x_e <= 1, quad forall e in E
  $

  #v(4pt)
  Any solution with $x_e > 1$ can be reduced to $x_e = 1$ while preserving feasibility.

  #pagebreak()

  *IP formulation (min cost SC):*
  $
    min sum_(e in E) c(e) x_e \
    "s.t." sum_(e in C_v) x_e >= 1, quad forall v in V, quad C_v := { e in E : v in e } \
    x_e in {0,1}, quad forall e in E
  $



  *LP relaxation:*
  $
    min sum_(e in E) c(e) x_e \
    "s.t." sum_(e in C_v) x_e >= 1, quad forall v in V \
    cancel(0 <= x_e <= 1)quad x_e >= 0, quad forall e in E
  $

  #v(4pt)
  Any solution with $x_e > 1$ can be reduced to $x_e = 1$ while preserving feasibility.

  #pagebreak()

  *Dual of the LP relaxation:*
  $
    max sum_(v in V) y_v \
    "s.t." sum_(v in e) y_v <= c(e), quad forall e in E \
    y_v >= 0, quad forall v in V
  $

  #v(8pt)

  *Integrality gap.*
  Let $"OPT" := "OPT"(I)$ be the optimal IP value and
  $"OPT"_f := "OPT"_f (I)$ the optimal LP value. Then $"OPT"_f <= "OPT"$, and
  $ min_I "OPT"(I) / "OPT"_f(I) $
  is the integrality gap.
]

#pagebreak()

== Greedy Algorithm and LP-Based Analysis
#[
  #set align(horizon)
  #set text(size: 0.84em)

  *Recall the greedy algorithm (weighted):*
  #algorithm-figure(
    [Greedy-SC],
    vstroke: .5pt + luma(200),
    {
      import algorithmic: *
      Assign([$A$], [$emptyset$])
      While([$union.big A != V$], {
        Assign([$e$], [$arg min{ "eff"_(union.big A)(e) : e in E(H) }$])
        For([each $v in e without union.big A$], {
          Line([Set $ac(v) := "eff"_(union.big A)(e)$])
        })
        Assign([$A$], [$A union {e}$])
      })
      Return([$A$])
    },
  )

  #v(4pt)
  Here $"eff"_U(e) := c(e) / (|e without U|)$ and $ac(v)$ is the amortized cost of $v$.

  #v(6pt)
  Let $A = {e_(i_1), dots, e_(i_m)}$ be the greedy solution and
  $A_j = {e_(i_1), dots, e_(i_j)}$. Then
  $
    "cost"(A)
    = sum_(j=1)^m c(e_(i_j))
    = sum_(j=1)^m |e_(i_j) without union.big A_(j-1)| dot c(e) / (|e without U|)
    = sum_(j=1)^m sum_(v in e_(i_j) without union.big A_(j-1)) "eff"_(union.big A_(j-1))(e_(i_j))
    = sum_(v in V) ac(v)
  $


  #pagebreak()
  #claim[
    Let $H_n := sum_(i=1)^n 1/i$. The vector
    $y_v := ac(v) / H_n$ for $v in V$ is feasible for the dual.
  ]
  #proof[
    - Let ${v_1, dots, v_n}$ be the order in which vertices are covered by the greedy algorithm.
    - For any $e in E$ with $|e| = k$, let ${v'_1, dots, v'_k}$ be the order in which vertices of $e$ are covered.
    - When $v'_i$ is covered, $|e without union.big A| = k - i + 1$, so
    $
      ac(v_i) = "eff"_(union.big A)(e') <= "eff"_(union.big A)(e) = c(e)/(|e backslash union.big A|) = c(e)/(k - i + 1).
    $
    - Hence
      $
        sum_(v in e) ac(v) <= c(e) sum_(i=1)^k 1/i = H_k dot c(e)
      $
    - and
      $
        sum_(v in e) y_v = sum_(v in e) ac(v) / H_n<= (H_k/H_n) c(e) <= c(e).
      $
      #v(-1em)
      #place(dx: 30em,dy:-7em)[
        #rect(fill:gray,stroke:black)[
          The dual
          $
            max sum_(v in V) y_v \
            "s.t." sum_(v in e) y_v <= c(e), quad forall e in E \
            y_v >= 0, quad forall v in V
          $
        ]
      ]
  ]
  #v(0pt)
  #pagebreak()
  #claim[
    The greedy algorithm is an $H_n$-approximation for minimum cost set-cover.
  ]
  #proof[
    $ "cost"(A) = sum_(v in V) ac(v) = H_n sum_(v in V) y_v <= H_n * "OPT"_f <= H_n * "OPT" $.
  ]


    #theorem[
    *Weak Duality Theorem*
    $
      max{ bc^T bx : A bx <= bb } <= min{ by^T bb : A^T by = bc, by >= b0 }
    $
    whenever both LPs are feasible and bounded.
  ]
]

#pagebreak()

= Set-Cover: Deterministic Rounding of the Primal LP

== Deterministic Rounding
#[
  #set align(horizon)
  #set text(size: 0.88em)

  #table(
    columns: (1fr, 1fr),
    stroke: none,
    [
      #block(
        stroke: black,
        inset: 10pt,
        radius: 6pt,
        [
          #set align(center)
          *IP formulation*
          $ min sum_(e in E) c(e) x_e $
          $ "s.t." sum_(e in C_v) x_e >= 1, quad forall v in V $
          $ x_e in {0,1}, quad forall e in E $
        ],
      )
    ],
    [
      #block(
        stroke: black,
        inset: 10pt,
        radius: 6pt,
        [
          #set align(center)
          *LP relaxation*
          $ min sum_(e in E) c(e) x_e $
          $ "s.t." sum_(e in C_v) x_e >= 1, quad forall v in V $
          $ x_e >= 0, quad forall e in E $
        ],
      )
    ],
  )

  #v(6pt)
  - For $v in V(H)$, set $f_v := |C_v|$ (number of hyperedges containing $v$).
  - Define $f := max_(v in V(H)) f_v$ (max frequency). Trivially $f >= 1$.

  #v(6pt)
  *Algorithm (deterministic rounding):*
  - Solve the LP relaxation optimally and let $(x_e^*)_(e in E(H))$ be the solution.
  - Return $A := { e in E(H) : x_e^* >= 1/f }$.

  #v(6pt)
  #theorem[
    The algorithm above forms an $f$-approximation for minimum cost set-cover.
  ]
  #proof[
    - The set $A$ is a valid cover: for any $v in V(H)$,
    - $sum_(e in C_v) x_e^* >= 1$ implies $exists e in C_v$ with $x_e^* >= 1/(|C_v|) >= 1/f$.
    \
    - Define 
    $
    z_e := cases(1 & quad e in A, x_e^* & quad e in.not A)
    $  
    - Then $z_e <= f x_e^*$ for all $e$. #tr[(if $e in A$, then $x_e^* >= 1/f$)]
    - Hence
    $
      c(A) <= sum_(e in E(H)) z_e c(e) <= f sum_(e in E(H)) x_e^* c(e) = f * "OPT"_f <= f * "OPT".
    $
    #v(-2em)
  ]
]

#pagebreak()

= Set-Cover: Randomised Rounding of the Primal LP

== Randomised Rounding
#[
  #set align(horizon)
  #set text(size: 0.88em)

  #table(
    columns: (1fr, 1fr),
    stroke: none,
    [
      #block(
        stroke: black,
        inset: 10pt,
        radius: 6pt,
        [
          #set align(center)
          *IP formulation*
          $ min sum_(e in E) c(e) x_e $
          $ "s.t." sum_(e in C_v) x_e >= 1, quad forall v in V $
          $ x_e in {0,1}, quad forall e in E $
        ],
      )
    ],
    [
      #block(
        stroke: black,
        inset: 10pt,
        radius: 6pt,
        [
          #set align(center)
          *LP relaxation*
          $ min sum_(e in E) c(e) x_e $
          $ "s.t." sum_(e in C_v) x_e >= 1, quad forall v in V $
          $ x_e >= 0, quad forall e in E $
        ],
      )
    ],
  )

  #v(6pt)
  *Randomised algorithm:*
  - Solve the LP relaxation optimally and let $(x_e^*)_(e in E(H))$ be the solution.
  - Include each $e in E(H)$ independently with probability $x_e^*$ to solution A.
  - Return $A$.

  #pagebreak()
  #lemma[
    Let $A$ be the collection returned by the algorithm and fix $v in V(H)$. Then
    $P[v in union.big A] >= 1 - 1/e$.
  ]
  #proof[
    - Let $C_v := { e in E(H) : v in e }$.
    - Then
    $ P[v in.not union.big A] & = P["no" e in C_v "is chosen"] \
                            & = product_(e in C_v) (1 - x_e^*) \
                            & <= product_(e in C_v) exp(-x_e^*)
                              = exp(-sum_(e in C_v) x_e^*) <= e^(-1) $.
  ]

  #v(4pt)
  *Conclusion:* $P[A "is not a valid cover"] <= sum_(v in V(H)) P[v in.not union.big A] <= n/e$.
  #h(1fr) #tr[Looks bad!]
]

#pagebreak()

== Probability Amplification
#[
  #set align(horizon)
  #set text(size: 0.9em)

  - For $k in NN$, run the algorithm $k$ independent times to obtain
    $A_1, A_2, dots, A_k$.
  - Set $U_k := union.big_(i=1)^k A_i$ (union of all solutions).
  - For $v in V(H)$, $P[v in.not U_k] <= e^(-k)$.

  #v(6pt)
  #lemma[
    There exists a constant $D > 0$ such that if $k >= D ln n$, then
    $P[U_k "is not a set-cover"] <= 1/4$.
  ]
  #proof[
    - For a fixed $v in V(H)$,$P[v in.not U_k] <= e^(-k) <= e^(-D ln n) <= 1/(4n)$ for large enough $D$.
    - A union bound over all vertices gives $P[U_k "not a set-cover"] <= 1/4$.
  ]
]

#pagebreak()

== Determining the Approximation Ratio
#[
  #set align(horizon)
  #set text(size: 0.88em)

  #v(6pt)
  #lemma[
    Let $"OPT"$ be the optimal cost and $k in NN$. Then
    $P[c(U_k) >= 4 * k * "OPT"] <= 1/4$.
  ]
  #proof[
    - For $e in E(H)$, set
    #v(-1.4em)
    $
      X_e := cases(0 &quad  e in.not A, c(e) &quad  e in A)
    $
    - Then $E[X_e] = c(e) * P[e in A] = c(e) x_e^*$.
    - Since $c(A) = sum_(e in E(H)) X_e$,
    $
    E[c(A)] = sum_(e in E(H)) E[X_e] = sum_(e in E(H)) x_e^* c(e) = "OPT"_f
    $.
    - Therefore $E[c(U_k)] <= k * "OPT"_f$, and by Markov's inequality,
    $ P[c(U_k) >= 4 * k * "OPT"] <= (k * "OPT"_f) / (4 * k * "OPT") <= 1/4 $
    #v(-2em)
  ]
#pagebreak()
  #conclusion[
    Repeating the algorithm $Omega(ln n)$ times gives a valid cover with cost at most
    $O(ln n * "OPT")$ with probability at least $1/2$.
  ]

  - For $k = Omega(ln n)$,
  $ P[U_k "is a cover" and c(U_k) <= 4 * k * "OPT"]
  >= 1 - P[U_k "not a cover"] - P[c(U_k) >= 4 * k * "OPT"] >= 1/2 $.
]
