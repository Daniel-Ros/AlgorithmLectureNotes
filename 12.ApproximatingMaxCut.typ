#import "settings/mstyle.typ": *
#import algorithmic: algorithm-figure, style-algorithm
#show: style-algorithm

#show: conf.with(
  handout: false,
  subtitle: [Approximating the Maximum Cut Problem],
)

#title-slide()

= The Max Cut Problem

== Setup

#problem[
  *Max Cut*

  *Given:* An undirected graph $G = (V, E)$.

  *Find:* A bipartition $(S, V without S)$ maximising $e_G (S, V without S)$ — the number of edges crossing the cut.
]

#pause

#theorem[
  For every graph $G$: $"max-cut"(G) >= e(G) / 2$.
]

#pause

#observation[
  Equivalently: every graph $G$ has a *spanning bipartite subgraph* with $>= e(G)/2$ edges.
]

== Proof of the Theorem

*Proof:*
  By induction on $v(G)$. Base cases $v(G) = 1,2$ are trivial.

  *Inductive step:* Let $v in V(G)$ be arbitrary. 
  - Apply the IH to $G - v$:
    - obtain a bipartition $(S, V(G) without (S union {v}))$ with $>= e(G-v)/2$ crossing edges.

  - Place $v$ on the side where it has the *fewest* neighbours in $G$ 

  - Then $v$ contributes at least $deg_G (v)\/2$ crossing edges.

  Size of resulting cut in $G$:
  $ >= e(G-v)/2 + deg_G (v) \/2 = e(G)/2. quad square $

#place(
    dx: 68%,
    dy: -44%,
    figure(image("figures/AMC1.png", width: 35%),)
  )

#pause
#v(-0pt)
#theorem[
  The above proof yields a poly-time algorithm forming a $1/2$-approximation for Max Cut.
]

= A Randomised Construction

== The Algorithm

#algorithm-figure(
  [Rand-Cut],
  vstroke: .5pt + luma(200),
  {
    import algorithmic: *
    Assign([$A, B$], [$emptyset$])
    For([each $v in V(G)$], {
      Line([Toss a fair coin independently])
      Line([*Heads:* place $v$ in $A$. #h(1em) *Tails:* place $v$ in $B$.])
    })
    Return([$(A, B)$])
  }
)

#pause

#observation[
  The randomised algorithm achieves an *expected* cut of size $e(G)/2$.
]

== Expected Cut Size

#set text(size: 0.95em)

For each edge $e = u v in E(G)$, define the indicator:
$ X_e := cases(1 quad & e in E_G (A","B), 0 quad & e in.not E_G (A","B)) $

#pause

Since the coins are *independent*:
$ EE[X_e] = PP[u in A and v in B] + PP[u in B and v in A] = 1/4 + 1/4 = 1/2 $

We may write $e_G (A,B) = sum_(e in E(G)) X_e$, so by *linearity of expectation*:

$ EE[e_G (A,B)] = sum_(e in E(G)) EE[X_e] = e(G)/2 $

#pause

#[
#set align(center)
*But how often do we actually get a cut $>= e(G)/2$?*
]


== Expected Cut Size
#set text(size: 0.8em)
#theorem[
  The algorithm produces a cut of size $>= e(G)/2$ with probability $>= 1/(e(G)+1)$. #h(1fr) #tr[(This is bad!)]
]
*proof:*
- Let $p := PP[e_G (A,B) >= e(G)/2]$.
 - *Goal* bound $p$ from below.

#pause
Write the expectation by splitting on the cut value:
$
e(G)/2 = EE[e_G (A,B)]
&= sum_(i <= e(G)/2 - 1) i dot PP[e_G (A,B) = i] + sum_(i >= e(G)/2) i dot PP[e_G (A,B) = i] \
&<= (e(G)/2 - 1) dot underbrace(sum_(i <= e(G)/2 - 1)  PP[e_G (A,B) = i], 1-p)
+ e(G) dot underbrace(sum_(i >= e(G)/2) PP[e_G (A,B) = i], p)
$

#pause

Rearranging:
$ e(G)/2 <= (e(G)/2 - 1)(1-p) + e(G) dot p $

== Expected Cut Size
#theorem[
  The algorithm produces a cut of size $>= e(G)/2$ with probability $>= 1/(e(G)+1)$. #h(1fr) #tr[(This is bad!)]
]
#h(2fr) $sbullet p := PP[e_G (A,B) >= e(G)/2]$ #h(1fr) $sbullet e(G)/2 <= (e(G)/2 - 1)(1-p) + e(G) dot p $ #h(2fr)

Isolating $p$:
$
e(G)/2 &<= e(G)/2 - 1 - p dot (e(G)/2 - 1) + e(G) dot p \
1 &<= p dot (e(G) - e(G)/2 + 1) = p dot (e(G)/2 + 1) \
$

$ ==> quad p >= 1/(e(G)/2 + 1) >= 1/(e(G) + 1). quad square $

= De-randomisation

== Conditional Expectation Background

*Goal:* Turn the randomised algorithm into a *deterministic* one with the same guarantee.

*Key tool:* the *method of conditional expectations*.

#pause

#definition[
  *Conditional Expectation*

  For discrete RVs $X, Y$ and value $z$ in the range of $Y$:
  $ EE[X | Y = z] := sum_x x dot PP[X = x | Y = z] $

  We write $EE[X | Y]$ for the *function* $z |-> EE[X | Y = z]$.
]

#pause

#theorem[*Law of Total Expectation*

  For discrete RVs $X, Y$:
  $ EE[X] = sum_(z in "range"(Y)) PP[Y = z] dot EE[X | Y = z] $
]

== Applying to Max Cut

Let $v_1, dots, v_n$ be an ordering of the vertices. Suppose $v_1, dots, v_i$ have already been placed in $A$ or $B$.

By the *Law of Total Expectation*, for vertex $v_(i+1)$:
$
EE[e_G (A,B) | v_1,dots,v_i "placed"] &= 
1/2 dot EE[e_G (A,B) | dots, v_(i+1) in A] &+ 1/2 dot EE[e_G (A,B) | dots, v_(i+1) in B]
$

Let:

 #h(2fr) $sbullet EE_A =  EE[e_G (A,B) | dots, v_(i+1) in A]$ #h(1fr) $sbullet EE_B = EE[e_G (A,B) | dots, v_(i+1) in B]$ #h(2fr)

#pause

So:
$ 2EE[e_G (A,B) | v_1,dots,v_i "placed"] &=   EE_A  +  EE_B $

#pause

#observation[
  Either $EE_A >= EE[e_G (A,B) | v_1,dots,v_i "placed"]$ or $EE_B >= EE[e_G (A,B) | v_1,dots,v_i "placed"]$.
]

= The Deterministic Algorithm

== De-randomised Greedy

*Assuming:* $EE_A$ and $EE_B$ can be computed efficiently we have the following algorithm.

#algorithm-figure(
  [Derand-Max-Cut],
  vstroke: .5pt + luma(200),
  {
    import algorithmic: *
    Assign([$v_1, dots, v_n$], [an arbitrary ordering of $V$])
    Assign([$A, B$], [$emptyset$])
    For([$i = 1$ to $n$], {
      Assign([$E_A$], [Compute $EE[e_G (A,B) | v_1,dots,v_(i-1) "placed" and v_i in A]$])
      Assign([$E_B$], [Compute $EE[e_G (A,B) | v_1,dots,v_(i-1) "placed" and v_i in B]$])
      Line([*If* $E_A >= E_B$ place $v_i$ in $A$, *else* place $v_i$ in $B$])
    })
    Return([$(A, B)$])
  }
)

#theorem[
  Derand-Max-Cut is a deterministic poly-time $1/2$-approximation for Max Cut.
]

*Proof (By induction):* 

#[
  #set align(center)
  I.H. $forall i <k, EE[e_G (A,B) | v_1,dots,v_(i) "placed"] >= e(G)/2$
]
Assume without loss of generality that $EE_A >= EE_B$.
- By assumption we have $EE_A >= EE[e_G (A,B) | v_1,dots,v_(k-1) "placed"] >= e(G)/2$.
$==>$ for $k=n$ we have 
$e_G (A,B) = EE[e_G (A,B) | v_1,dots,v_(n) "placed"] >= e(G)/2 $ as required.

== De-randomised Greedy

For each step $i$, we need to compute efficiently:
$ EE_A := EE[e_G (A,B) | v_1,dots,v_i "placed" and v_(i+1) in A] $
$ EE_B := EE[e_G (A,B) | v_1,dots,v_i "placed" and v_(i+1) in B] $

#pause

Let $tilde(A), tilde(B)$ be the *current actual sets* with $v_1, dots, v_i$ placed. Define:
$ ell := e(G) - deg_G (v_(i+1), tilde(A)) - deg_G (v_(i+1), tilde(B)) - e_G (tilde(A)) - e_G (tilde(B)) - e_G (tilde(A), tilde(B)) $

$ell = \#$ edges among the *remaining* vertices $v_(i+2), dots, v_n$ (still random).

#pause

Then:
$
EE_A &= e_G (tilde(A), tilde(B)) + deg_G (v_(i+1), tilde(B)) + ell/2 \
EE_B &= e_G (tilde(A), tilde(B)) + deg_G (v_(i+1), tilde(A)) + ell/2
$

#place(
    dx: 80%,
    dy: -55%,
    figure(image("figures/AMC2.png", width: 20%),)
  )

#pause

Therefore:
$ |EE_A - EE_B| = |deg_G (v_(i+1), tilde(B)) - deg_G (v_(i+1), tilde(A))| $

== The Algorithm

$ |EE_A - EE_B| = |deg_G (v_(i+1), tilde(B)) - deg_G (v_(i+1), tilde(A))| $

Therefore: #h(1fr) $EE_A >= EE_B <==> deg_G (v_(i+1), tilde(B)) >= deg_G (v_(i+1), tilde(A))$ #h(1fr)

#pause
So we may write:
#algorithm-figure(
  [Derand-Max-Cut],
  vstroke: .5pt + luma(200),
  {
    import algorithmic: *
    Assign([$v_1, dots, v_n$], [an arbitrary ordering of $V$])
    Assign([$A, B$], [$emptyset$])
    For([$i = 1$ to $n$], {
      Line([*If* $deg_G (v_(i+1), B) >= deg_G (v_(i+1), A)$ place $v_i$ in $A$, *else* place $v_i$ in $B$])
    })
    Return([$(A, B)$])
  }
)

#[
  #set align(center)
  *This is the first "algorithm" we saw in those slides.*
]