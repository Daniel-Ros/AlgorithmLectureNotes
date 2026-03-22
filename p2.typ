#import "@preview/touying:0.6.1": *
#import themes.university: *
#import "@preview/numbly:0.1.0": numbly
#import "@preview/algo:0.3.6": algo, d, i

#import "@preview/theorion:0.4.1": *
#import "@preview/algorithmic:1.0.7"
#import "@preview/larrow:1.0.0": *

#import cosmos.clouds: *

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
#let reduction = $scripts(<=)_p$
#let aT = text(fill: green, $T$)
#let aF = text(fill: red, $F$)
#let sred(c) = text(fill: red, size: 8pt, c)

#set text(
  size: 18pt,
)

#set heading(numbering: "1.")

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
- We talked about a few:
  - $k$-clique
  - CNF-SAT
  - $k$-CNF-SAT

= Reductions

== Reductions
  - We saw we can "translate" one languge into another with reductions
  #definition(title: "polynomial time reduction")[
    Given two languages $L_1, L_2 in cNP$, we write $L_1 reduction L_2$ if there exists a function $f:{0,1}^* -> {0,1}^*$ and a polynomial $p: NN -> NN$, such that:
    - $x in L_1 <=> f(x) in L_2$
    - for every $x in {0,1}^*$, $f$ runs in $p(|x|)$ time.
  ]
  #align(center)[

  #image("figures/L1i1.png"),
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

== Independent set
- For a graph $G$, let $alpha(G)$ denote the size of the maximum independent set in $G$.
#definition[
  $"IS" := {<G,k> : alpha (G) >= k}$.
]
#theorem[
  IS is in $cNPC$.
]

== Independent set
- The proof that IS is in $cNP$ is left as homework.
- In order to show that IS hard we need to show that
$
  L reduction "IS"
$
for some $cNP$ hard languge.
/*
==
- Suppose we have two languages/problems $L_1, L_2$, can we know which one of them is _harder_?
#pause
- The intuition is that if $L_2$ harder than $L_1$ we would be able to solve $L_2$ using $L_1$.
#pause
- This is done by "translating" our problem from $L_1$ to $L_2$, solving the translated $L_1$ problem, and then answering accordingly.
#pause
#definition(title: "polynomial time reduction")[
  Given two languages $L_1, L_2 in cNP$, we write $L_1 reduction L_2$ if there exists a function $f:{0,1}^* -> {0,1}^*$ and a polynomial $p: NN -> NN$, such that:
  - $x in L_1 <=> f(x) in L_2$
  - for every $x in {0,1}^*$, $f$ runs in $p(|x|)$ time.
]

== Reductions
Assuming that $L_1 reduction L_2$ and given the polynomial reduction $f$ as well as a black box $A$ that solves $L_2$.
We can create an algorithm $B$ that solves $L_2$ using only $f$ and $A$ in the following way:
#figure(
  image("figures/L1i1.png"),
)

== Reductions
#definition(title: "NP-hard")[
  A language $L subset.eq {0,1}^*$ is said to be NP-hard if  $L' reduction L$ for every $L' in cNP$
]
#pause
Intuitively, the following qustion arises:
#question[
  Are there any languages that are NP-Hard?
]
#pause
#example[
  The language
  $ L^*={ (M',x, 1^c) : M'(x')=1 & and M'(x') #text([computes in $O(2^(|x|^c))$ time])} $ is NP-hard.
]

== Reductions
#definition(title: "NP-complete")[
  A language $L subset.eq {0,1}^*$ is said to be NP-complete if $L in cNP$ and $L$ is NP-hard
]
- If we find a polynomial time algorithm for one problem in $cNPC$, then $cP = cNP$
- The problem $cP = cNP$ or $cP != cNP$ remains an open question to this day. Whoever proves either one will be awarded 1 million dollars.
#pause
#question[
  Is there any language $L in cNPC$?
]

== SAT
- Let $x_1,...x_n$ be boolean variables ($x_i$ can be assigned either $0$ or $1$).
- A boolean formula $phi$ is said to be in conjunctive normal form (CNF) if it has the form

#place(center, dx: -35pt)[
  #set text(size: 10pt)
  Or between literals #arrow-label(<or_exp>, dx: -50pt, dy: -5pt)
]

#place(center, dx: 80pt)[
  #set text(size: 10pt)
  Literal #arrow-label(<literal_exp>, dx: -50pt, dy: -5pt)
]
\
\

$
  phi = underbrace((x_1 or x_17 or #arrow-label(<or>, dx: -9pt, dy: 10pt) overline(x_25) or x_80 #arrow-label(<literal>, dx: -9pt, dy: 10pt) ), "clause") and #arrow-label(<and>, dx: -6pt) underbrace(x_9, "also clause") and ...
$

#place(center, dx: 35pt)[
  #set text(size: 10pt)
  And between clauses #arrow-label(<and_exp>, dx: -50pt, dy: 10pt)
]
#label-arrow(<literal_exp>, <literal>)
#label-arrow(<and_exp>, <and>)
#label-arrow(<or_exp>, <or>)

#theorem(title: "Cook-Levin")[
  CNF-SAT is npc.
]

== 3-CNF
#definition[
  For an integer $k in NN$,
  $
    k"-CNF-SAT" := {phi | phi "is a CNF formula in which each clause has exactly " #linebreak()
      k "literals"}.
  $
]
#pause
#theorem()[
  2-CNF-SAT is in $cP$.
]
- proof is delegated to the practice session

#theorem[
  3-CNF-SAT is in $cNPC$.
]<3CNF_is_NPC>

==
#text(size: 15pt)[
  #claim[
    3-CNF-SAT$in cNP$
  ]<3sat_in_NP>
  #pause
  #algorithm-figure(
    [Verifying algorithm for $3$-CNF-SAT],
    vstroke: .5pt + luma(200),
    {
      import algorithmic: *
      Procedure(
        [$M$],
        ($phi$, $alpha$),
        {
          Comment[$alpha$ is the assigment i.e $alpha:{x_1,...,x_n} -> {aT,aF}$]
          Comment[Check if the assignment complete, i.e. every variable has an assigment]
          For($i in [n]$, {
            If($alpha(x_i)$ + " = undefined")
          })
        },
      )

      Comment[Check if any clause is unsatisfied]
      For("clause " + $C in phi$, {
        If($C(alpha) = aF$, { Return(`false`) })
      })
      Comment[All clases are satisfied, hence $phi(alpha)$ is also satisfied]
      Return(`true`)
    },
  )
]

==
- Key observasion:
  - If $L_1 reduction L_2$ and $L_2 reduction L_3$, then $L_1 reduction L_3$.

  #claim[
    Let $L in$ NP-Hard, and let $L'$ be a language. If $L reduction L'$, then $L'$ is also NP-Hard.
  ]<NP_hard_reduction>

==
#claim[
  3-CNF-SAT is NP-hard
]<3sat_in_NPH>
- Define a function $f$ as follows:
$
  f(phi) = and.big_(i=1)^m g(C_i)
$
1. If $k=3$, then return $C$ as it. i.e.
$
  g(l_1 or l_2 or l_3) = l_1 or l_2 or l_3
$
2. If $k < 3$, then repeat one of the literals until the clause has exactly $3$ literals. For example
$
  g(l_1 or l_2) = l_1 or l_2 or l_2.
$
3. If $k > 3$ then create $k-3$ *new* variables named $y_1,...,y_(k-3)$ and let:
  $
    g(l_1 or l_2or... l_k) = (l_1 or l_2 or y_1) and (overline(y_1) or l_3 or y_2) and (overline(y_2) or l_4 or y_3) and ... and (overline(y_(k-3)) or l_(k-1) or l_k).
  $

==
- It is clear that $f$ runs in constant time.
#pause
- It remains to show the correctness of $f$, i.e.
$
  phi in "CNF-SAT" <=> f(phi) in 3-"CNF-SAT"
$
#pause
$=>$(Completeness):
- Assume that $phi in "CNF-SAT"$,
- This means there exists a satisfying assignment $alpha$ for $phi$.
- set $alpha'$ as follow:
  $
    forall i in[n]: quad alpha'(x_i)=alpha(x_i).
  $
- Fix a clause $C in phi$
- If $C$ we have $|C| <= 3$, then we are done as $C equiv g(C)$.
==
- Otherwise let $C= l_1 or l_2 or ... or l_k$ where $k>=4$ be such clause.
- By assumption $C[alpha] = aT$, so there exists some $i in[k]$ such that $ell_i = aT$.
- Since for all $j in [k-3]$ the value of $alpha'(y_j)$ have not yet been set, we define them as follows:
  $
    alpha'(y_j) = cases(aT quad "if " j<=i-2",", aF quad "if " j > i-2".")
  $
  Then,
  $
    g(C)[alpha'] = (l_1 or l_2 or y_1)
    and ...
    and (overline(y_(i-2)) or & l_i or y_(i-1))
                                and ...
                                and (overline(y_(k-3)) or l_(k-1) or l_k)[alpha'] \
    = (?_(space) or_(space) ?_(space) or aT) and ...
    and (aF or                & aT or aT)
                                and ...
                                and (aT or_(space) ? or_(space) ?) = aT.
  $
  as required.

==
$arrow.l.double$(Soundness):
#pause
- Assume that $f(phi) in 3"-CNF-SAT"$.
- there is a satisfying assignment $alpha'$ for $f(phi)$.
#pause
- copy the assignment of the orginal variables form $alpha'$ to $alpha$. #pause
- if $alpha$ is not sattisfying then, there must exists a clause $C = l_1 or l_2 ... or l_k$.
- it cannot be the $k <= 3$ as we are coppying the assigment.
- for $k > 3$ by assumption
$
  C[alpha] = l_1 or l_2 or ... or l_k = aF
$
such that $C[alpha] = aF$. #pause
- If $k <= 3$, then since $g(C) equiv C$, it follows that $aT = g(C)[alpha'] = C[alpha'] = C[alpha] = aF$ which is a contradiction to the assumption that $alpha$ satisfies $f(phi)$. #pause
- Otherwise assume that $k >= 4$, by assumption
$
  C[alpha] = l_1 or l_2 or ... or l_k = aF
$ #pause
meaning that for all $i in [k]$ we have $l_i = aF$.
#pagebreak()
- On the otherhand, since $f(phi)[alpha']$ is satisfied the gadget clause
$
  g(C) = (l_1 or l_2 or y_1) and (overline(y_1) or l_3 or y_2) and (overline(y_2) or l_4 or y_3) and ... and (overline(y_(k-3)) or l_(k-1) or l_k)
$
#pause
is also satisfied, and such every clause should be $aT$.
- In order for the first clause to be $aT$, $y_1 = aT$ must hold.
- In order to satisfy the next clause $y_2 = aT$ must hold, following this argument one can see that $y_i = aT$ must hold for all $i in [k-3]$.
- Looking at the last clause, $ell_(k-1) = ell_k = aF$ by assumption, and $overline(y_(k-3)) = aF$ in order for any other clause to be satisfied,
- which is a contradiction to the assumption that $a'$ satisfies $phi$.
*/
