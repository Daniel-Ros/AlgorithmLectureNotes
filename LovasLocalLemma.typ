#import "settings/mstyle.typ": *
#import algorithmic: algorithm-figure, style-algorithm
#show: style-algorithm

#show: conf.with(
  handout: false,
  subtitle: [Lovasz Local Lemma],
)

#title-slide()

= Lovasz Local Lemma

== Is it possible to handle dependent bad events?
#[
  #set align(horizon)
  #set text(size: 0.9em)

  #definition[
    *The scenario:* \
    Let $cal(E)_1, ..., cal(E)_n$ be bad events (over the same sample space). \
    We wish to prove:
    $PP[cap.big_(i=1)^n overline(cal(E)_i)] > 0$ -- no bad event occurs.
  ]

  #v(4pt)
  - If $cal(E)_1, ..., cal(E)_n$ are pairwise independent, then we can argue as follows:
    - Recall: events $A$ and $B$ are independent if $PP[A cap B] = PP[A] PP[B]$.
    - If $A, B$ are independent, then so are $overline(A), overline(B)$:
      #block(
        stroke: black,
        radius: 6pt,
        inset: 8pt,
      )[
        $PP[overline(A) cap overline(B)] = 1 - PP[A cup B]$ \
        $= 1 - PP[A] - PP[B] + PP[A cap B]$ \
        $= (1 - PP[A])(1 - PP[B])$ \
        $= PP[overline(A)] PP[overline(B)]$
      ]
]

#pagebreak()

== Pairwise independence is not enough
#[
  #set align(horizon)
  #set text(size: 0.9em)

  - Back to our problem:
  - $cal(E)_1, ..., cal(E)_n$ pairwise independent
    $=>$
    $overline(cal(E)_1), ..., overline(cal(E)_n)$ pairwise independent.
  - If $PP[cal(E)_i] < 1$ for all $i in [n]$, then:
    $
      PP[cap.big_(i=1)^n overline(cal(E)_i)]
      = product_(i=1)^n PP[overline(cal(E)_i)]
      = product_(i=1)^n (1 - PP[cal(E)_i])
      > 0
    $
    (assuming this equality holds).
  - But pairwise independence does *not* imply
    $
      PP[cap.big_(i=1)^n overline(cal(E)_i)]
      = product_(i=1)^n PP[overline(cal(E)_i)].
    $
  - Mutual independence does.
  - What if $cal(E)_1, ..., cal(E)_n$ do depend on one another in some way?
  - The Lovasz local lemma provides a partial solution.
]

#place(
  dx: 70%,
  dy: -70%,
  block(width: 35%, fill: gray.lighten(50%), inset: 10pt, radius: 5pt)[
    #set text(size: 0.60em)
    An experiment is made, by trowing $2$ fair coins
    independently of each other.
    - $C_1$ the event that the first coins is heads.
    - $C_2$ the event that the second coint is heads.
    - $C_3$ the event that the outcome of the coins is not the same.

    Clearly $C_1$ and $C_2$ are independent.
    Also $C_3$ is independent of both $C_1$ and $C_2$
    $
      PP(C_1 and C_3) &= PP(C_3 | C_1) dot PP(C_1) \
      &= 1/2 dot 1/2 \
      &= PP(C_1) dot PP(C_3)
    $
    But 
    $
      PP(C_1 and C_2 and C_3) = 0 !=1/8=PP(C_1)dot PP(C_1)dot PP(C_1)
    $
  ]
)

#pagebreak()

== Mutual independence of random variables
  #set align(horizon)
  #set text(size: 0.86em)

  #definition[
    Events $cal(E)_1, ..., cal(E)_n$ are said to be *mutually independent* if
    $
      PP[cap.big_(i in I) cal(E)_i] = product_(i in I) PP[cal(E)_i]
    $
    whenever $emptyset != I subset.eq [n]$.
  ]

  // #v(4pt)
  // *Put another way:* for every $i in [n]$ and every $emptyset != I subset.eq [n] without {i}$,
  // $PP[cal(E)_i | cap.big_(j in I) cal(E)_j] = PP[cal(E)_i].
  // $

// == An equivalent definition
#[
  #set align(horizon)
  #set text(size: 0.86em)

  #definition(title:"Alternative definition")[
    Event $A$ is mutually independent of events $cal(E)_1, ..., cal(E)_n$ if
    $
      PP[A | cap.big_(i=1)^n B_i] = PP[A]
    $
    where $B_i in {cal(E)_i, overline(cal(E)_i)}$ for all $i in [n]$.
  ]

  #v(4pt)
  - No matter whether each $cal(E)_i$ occurs or not, this does not affect $PP[A]$.
  - For a proof of equivalence, see the booklet.
]

#pagebreak()

== Pairwise vs mutual independence (example 1)
#[
  #set align(horizon)
  #set text(size: 0.86em)

  - Mutual independence $=>$ pairwise independence.
  - The converse implication fails.

  *Example.* Let $Omega := {1,2,3,4}$ with the discrete uniform measure.
  $A := {1,2}$, $B := {1,3}$, $C := {2,3}$.

  - $PP[A] = PP[B] = PP[C] = 1/2$.
  - $A, B$ are independent:
    $PP[A cap B] = PP[{1}] = 1/4 = PP[A] dot PP[B]$.
  - The same applies to $B, C$ and $A, C$.
  - Yet
    $PP[A cap B cap C] = PP[emptyset] = 0 != PP[A] dot PP[B] dot PP[C]$.
  - So $A, B, C$ are pairwise independent but *not* mutually independent.
]

#pagebreak()

// == Pairwise vs mutual independence (example 2)
// #[
//   #set align(horizon)
//   #set text(size: 0.86em)

//   *Example.* Two fair dice are rolled.
//   $A := {"sum of outcomes is 7"}$,
//   $B := {"1st die rolled 3"}$,
//   $C := {"2nd die rolled 4"}$.

//   - $PP[A] = PP[B] = PP[C] = 1/6$.
//   - Events $B$ and $C$ are independent (independent trials).
//   - To see $A$ and $B$ are independent, note:
//     $PP[A | B] = PP["sum" = 7 | "1st die" = 3] = PP["2nd die" = 4] = 1/6 = PP[A]$.
//   - Similarly, $A$ and $C$ are independent.
//   - But $B cap C => A$, so
//     $PP[A cap B cap C] = PP[B cap C] = (1/6)^2$,
//     while
//     $PP[A] PP[B] PP[C] = (1/6)^3$.
// ]

#pagebreak()

== Complement independence
#[
  #set align(horizon)
  #set text(size: 0.88em)

  - Mutual independence is a *stronger* form of independence than pairwise independence.
  - We have seen that
    $cal(E)_1, ..., cal(E)_n$ pairwise independent
    $=>$
    $overline(cal(E)_1), ..., overline(cal(E)_n)$ pairwise independent.
  - This property is also supported in mutual independence:

  #theorem[
    If $cal(E)_1, ..., cal(E)_n$ are mutually independent, then so are
    $overline(cal(E)_1), ..., overline(cal(E)_n)$.
  ]

  #v(2pt)
  For a proof, see the booklet.
]

#pagebreak()

== The mutual independence principal
#[
  #set align(horizon)
  #set text(size: 0.86em)

  - The following is a handy tool for determining mutual independence.

  #theorem[
    *(Mutual independence principal)* \
    Let $X := (X_1, ..., X_m)$ be a sequence of pairwise independent trials.
    Let $A_1, ..., A_n$ be events, and for each $i in [n]$ let $A_i$ be determined
    by trials $F_i subset.eq X$. Given $I subset.eq [n]$ and $j in [n] without I$,
    if
    $
      F_j cap (cup.big_(i in I) F_i) = emptyset,
    $
    then $A_j$ is mutually independent of $(A_i)_{i in I}$.
  ]
]

#pagebreak()

== Statement of the Lovasz local lemma
#[
  #set align(horizon)
  #set text(size: 0.88em)

  - There are several versions. We state one of those.
  - The version stated here is called the *symmetric version*.
  - We focus on applications of the lemma and not its proof(s).

  #v(6pt)
  *The dependency graph*
  #definition[
    Events $cal(E)_1, ..., cal(E)_n$. A dependency graph
    $D := D(cal(E)_1, ..., cal(E)_n)$ is any graph whose vertex set is
    $cal(E)_1, ..., cal(E)_n$ and supporting the property:
    for every $i in [n]$, event $cal(E)_i$ is mutually independent of the events
    ${cal(E)_j : j != i and {i, j} in.not E(D)}$.
  ]

  #remark[
    Sometimes a directed version of such graphs is more useful
    (i.e., in *asymmetric* applications).
  ]

  #remark[
    *Danger:* We did *not* just say that we build a graph on $cal(E)_1, ..., cal(E)_n$
    by placing an edge $(cal(E)_i, cal(E)_j)$ if $cal(E)_i, cal(E)_j$ are dependent.
  ]
]

#pagebreak()

== The symmetric local lemma
#[
  #set align(horizon)
  #set text(size: 0.88em)

  #theorem[
    *(The symmetric local lemma)* \
    Let $cal(E)_1, ..., cal(E)_n$ be events such that the following holds:

    1. *(Symmetry)* $PP[cal(E)_i] <= p$ for all $i in [n]$.
    2. *(Limited dependency)* $Delta(D(cal(E)_1, ..., cal(E)_n)) <= d$.
    3. *(Bound $p$ and $d$)* $e dot p dot (d + 1) <= 1$ (up to a constant).

    Then
    $PP[cap.big_(i=1)^n overline(cal(E)_i)] > 0$.
  ]
]
