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
    Let $E_1, ..., E_n$ be bad events (over the same sample space). \
    We wish to prove:
    $P[cap.big_(i=1)^n overline(E_i)] > 0$ -- no bad event occurs.
  ]

  #v(4pt)
  - If $E_1, ..., E_n$ are pairwise independent, then we can argue as follows:
    - Recall: events $A$ and $B$ are independent if $P[A cap B] = P[A] P[B]$.
    - If $A, B$ are independent, then so are $overline(A), overline(B)$:
      #block(
        stroke: black,
        radius: 6pt,
        inset: 8pt,
      )[
        $P[overline(A) cap overline(B)] = 1 - P[A cup B]$ \
        $= 1 - P[A] - P[B] + P[A cap B]$ \
        $= (1 - P[A])(1 - P[B])$ \
        $= P[overline(A)] P[overline(B)]$
      ]
]

#pagebreak()

== Pairwise independence is not enough
#[
  #set align(horizon)
  #set text(size: 0.9em)

  - Back to our problem:
  - $E_1, ..., E_n$ pairwise independent
    $=>$
    $overline(E_1), ..., overline(E_n)$ pairwise independent.
  - If $P[E_i] < 1$ for all $i in [n]$, then:
    $
      P[cap.big_(i=1)^n overline(E_i)]
      = product_(i=1)^n P[overline(E_i)]
      = product_(i=1)^n (1 - P[E_i])
      > 0
    $
    (assuming this equality holds).
  - But pairwise independence does *not* imply
    $
      P[cap.big_(i=1)^n overline(E_i)]
      = product_(i=1)^n P[overline(E_i)].
    $
  - Mutual independence does.
  - What if $E_1, ..., E_n$ do depend on one another in some way?
  - The Lovasz local lemma provides a partial solution.
]

#pagebreak()

== Mutual independence of random variables
  #set align(horizon)
  #set text(size: 0.86em)

  #definition[
    Events $E_1, ..., E_n$ are said to be *mutually independent* if
    $
      P[cap.big_(i in I) E_i] = product_(i in I) P[E_i]
    $
    whenever $emptyset != I subset.eq [n]$.
  ]

  // #v(4pt)
  // *Put another way:* for every $i in [n]$ and every $emptyset != I subset.eq [n] without {i}$,
  // $P[E_i | cap.big_(j in I) E_j] = P[E_i].
  // $

// == An equivalent definition
#[
  #set align(horizon)
  #set text(size: 0.86em)

  #definition(title:"Alternative definition")[
    Event $A$ is mutually independent of events $E_1, ..., E_n$ if
    $
      P[A | cap.big_(i=1)^n B_i] = P[A]
    $
    where $B_i in {E_i, overline(E_i)}$ for all $i in [n]$.
  ]

  #v(4pt)
  - No matter whether each $E_i$ occurs or not, this does not affect $P[A]$.
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

  - $P[A] = P[B] = P[C] = 1/2$.
  - $A, B$ are independent:
    $P[A cap B] = P[{1}] = 1/4 = P[A] P[B]$.
  - The same applies to $B, C$ and $A, C$.
  - Yet
    $P[A cap B cap C] = P[emptyset] = 0 != P[A] P[B] P[C]$.
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

//   - $P[A] = P[B] = P[C] = 1/6$.
//   - Events $B$ and $C$ are independent (independent trials).
//   - To see $A$ and $B$ are independent, note:
//     $P[A | B] = P["sum" = 7 | "1st die" = 3] = P["2nd die" = 4] = 1/6 = P[A]$.
//   - Similarly, $A$ and $C$ are independent.
//   - But $B cap C => A$, so
//     $P[A cap B cap C] = P[B cap C] = (1/6)^2$,
//     while
//     $P[A] P[B] P[C] = (1/6)^3$.
// ]

#pagebreak()

== Complement independence
#[
  #set align(horizon)
  #set text(size: 0.88em)

  - Mutual independence is a *stronger* form of independence than pairwise independence.
  - We have seen that
    $E_1, ..., E_n$ pairwise independent
    $=>$
    $overline(E_1), ..., overline(E_n)$ pairwise independent.
  - This property is also supported in mutual independence:

  #theorem[
    If $E_1, ..., E_n$ are mutually independent, then so are
    $overline(E_1), ..., overline(E_n)$.
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
    Events $E_1, ..., E_n$. A dependency graph
    $D := D(E_1, ..., E_n)$ is any graph whose vertex set is
    $E_1, ..., E_n$ and supporting the property:
    for every $i in [n]$, event $E_i$ is mutually independent of the events
    ${E_j : j != i and {i, j} in.not E(D)}$.
  ]

  #remark[
    Sometimes a directed version of such graphs is more useful
    (i.e., in *asymmetric* applications).
  ]

  #remark[
    *Danger:* We did *not* just say that we build a graph on $E_1, ..., E_n$
    by placing an edge $(E_i, E_j)$ if $E_i, E_j$ are dependent.
  ]
]

#pagebreak()

== The symmetric local lemma
#[
  #set align(horizon)
  #set text(size: 0.88em)

  #theorem[
    *(The symmetric local lemma)* \
    Let $E_1, ..., E_n$ be events such that the following holds:

    1. *(Symmetry)* $P[E_i] <= p$ for all $i in [n]$.
    2. *(Limited dependency)* $Delta(D(E_1, ..., E_n)) <= d$.
    3. *(Bound $p$ and $d$)* $e dot p dot (d + 1) <= 1$ (up to a constant).

    Then
    $P[cap.big_(i=1)^n overline(E_i)] > 0$.
  ]
]
