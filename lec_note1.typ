#import "theme.typ" : *
#import "@preview/algorithmic:1.0.7"
#import "@preview/larrow:1.0.0": *


#import algorithmic: style-algorithm, algorithm-figure
#show: style-algorithm

#let todo(body) = text(red)[TODO:*#body*]
#let cP = $bold("P")$
#let cNP = $bold("NP")$
#let cNPC = $bold("NPC")$
#let reduction = $scripts(<=)_p$


#let abstract = [
  These are lecture notes for the course Algorithms and Optimization at Ariel University
  Students are assumed to have basic knowledge of graph theory, crucial definitions will be reminded.
  While we strive for accuracy, these notes may contain mistakes. Students are encouraged to report any errors or typos they encounter.
]

#show: theme.with(
  title: "Algorithms 2",
  // subtitle: [potato, tomato, banana],
  author: "Daniel Rosenberg and Michael Trushkin",
  abstract: abstract,
)

= Polynomial-time algorithms
An algorithm is called _polynomial-time_ if its running time is bounded by $O(n^c)$ where $n$ is the length of the input and $c$ is some (maybe huge) constant.
// For a problem $L$, we say the $L$ is polynomial if a polynimal algorthm exists for solving $L$.

#example[
  Common examples of polynomial-time algorithms include: DFS, BFS, Dijkstra's algorithm, 2-Coloring, and various sorting algorithms.
]

// Skipping some fundamental knowledge#footnote[For more information about this topic the reader is adviced to loop up Computational Comlexity by Aroara and Barak] we can now informally define:

#definition[
  $cP :=$ The set of problems that have a polynomial algorithm.
]

#remark[
Since this course focuses on computational complexity (e.g., NP-completeness), we ignore the exact running time of algorithms. Any polynomial-time algorithm is considered “efficient,” and we do not distinguish between different polynomial running times.
]

// #definition[
//   $cNP :=$ The set of problems that have a *non-deterministic* polynomial algorithm.
// ]<np>

// #definition[
//   $cNPC := $ The set of problems that if we find a polynomial-time algorithm that solves them then $cP = cNP$.
// ]<npc>

= Self reduction
There are two types of problems: _decision  problems_ and  _search problems_.
Decision problems are those that require a 'yes' or 'no' answer, whereas search problems require finding an actual solution if one exists.
For example, finding a path between two nodes the decision problem will be "*Is* there a path between node $A$ and node $B$?"
and the search problem will be "*What* is the path between node $A$ and $B$?" both of these can be solved by the same algorithm.
A non trivial problem is finding $k$-clique, given a graph $G$, the decision problem is:
#question[
  Is there a clique of size $k$ in $G$?
]#label("q1")
The _language_ $k-"clique" := {G | omega(G) >= k}$ is the set of all graphs that contain a clique of size at least $k$,
answering @q1 is the same as asking if some graph is in $k$-clique or not.
The search problem denoted SEARCH-$k$-CLIQUE is given some graph $G$ find a copy of $K_k$ in $G$, if there is no such copy return `null`.

One might ask whether the problems are equivalent, by that we mean given a way to solve one, can we solve the other?
By the nature of the problems if we have a way to find the solutions, it is easy to answer whether there is a solution.
The other way seems more complicated, but as it turns out for $cNPC$ languages it is possible. #footnote([It is possible with an extra polynomial cost, which we consider to be negligable in this course.])

#claim[
If the decision problem for $k$-clique can be solved in polynomial time, then there is a polynomial-time algorithm for SEARCH-$k$-CLIQUE.
]
#proof()[
  In order to prove the claim, we will use the assumption that there is a polynomial-time algorithm for $k$-clique and show a
  polynomial time algorith for SEARCH-$k$-CLIQUE. We propuse the following algorithm:
  #show: style-algorithm
  #algorithm-figure(
    "",
    vstroke: .5pt + luma(200),
    {
      import algorithmic: *
      Procedure(
        "self-reduction",
        ("G"),
        {
          If($A(G) = 0$, { Return(`null`)})
          LineBreak
          While(
            $v(G) > k$,
            {
              import algorithmic: *
              Line([pick $v in V(G)$])
              If($A(G-v)=1$,{
                Assign([$G$],[$G-v$])
              })
            },
          )
          Return[$G$]
        },
      )
    }
  )<algo_k_clique>

  If $G$ does not have a valid clique of size $k$, then @algo_k_clique will return `null` on line $3$ as required.
  Otherwise, we know that there is a clique of size $k$ in $G$(maybe more then one), if at any p oint by removing some vertex $v in V(G)$ we get that $A(G-v)=0$ we know that $v$ is essential to the clique and leave it in $V(G)$.
  Since at all times $A(G)=1$, when $v(G) = k$ the algorithm stops and return $G$; which is a clique of size $k$.

  Moving to the complexity of @algo_k_clique.
  By assumption $A$ has complexity time bounded by some $f(G)=O(n^c)$ for some constant $c>0$.
  The algorithm performs at most $n-k+1$ calls to algorithm $A$
  where the first call at line $2$ and at most $n-k$ calls at line 8.
  It therefore follows that the running time of @algo_k_clique is at most $(n-k+1) dot f(G) = O(n^(c+1))$ which is polynomial.
]


The claim above demonstrates that decision and search problem are equivalent#footnote[In polynomial time, which is what we mean by equivelent.], thus we can focus only on decision problems.

= NP-completeness
While the class $cP$ contains a large portion of the problems students have faced so far, as it turs out the majoriy of the problems are not easy at all.

Suppose you are a professional safe-cracker competing with a friend who claims he can open a safe faster than you. The safe is highly secure, and no known method works, so you resort to trying all combinations, which takes a long time.

After some time your friend says he has cracked the safe and hands you a book containing a million digits of π, claiming the correct code is somewhere inside. You argue this doesn’t count, just trying to read the book will take a lot of time. However, if he gives you the code directly, you can easily verify it by trying it once. If it opens the safe, he wins.

But if the code is wrong, is there any way for you to find the correct one—or even know that one exists?
This story captures the essence of out next complexity class $cNP$, the set of problems where a proposed solution can be verified quickly. Formally,
#definition("NP class")[
  A language $L$ is said to be in $cNP$ if we have a polynomial-time algorithm $M$ such that
  $
    x in L <=> exists y space  s.t |y| < p(|x|) "and" M(x,y) = 1
  $
  where $p$ is some polynomial
]
#remark[
  In most literture $y$ is called a _witness_ and $M$ is called _veryfing algorithm_, where $y$ plays the role of the answer, and $M$ should just verify if the answer is correct.
]
#remark[
  In our story, $y$ is the correct code for the safe, and $M$ is you—the
  professional safe-cracker.
  If a code exists, then given $y$ you can easily verify it by trying it
  once and opening the safe.
  If no such code exists, the safe cannot be opened—at least not in an
  “easy” way.#footnote[For example, you could always try to destroy the safe.]
]

#remark[
  If a language/problem $L in cNP$, then given the verifier $M$ and a polynomial $p$, we can do the following: for any $x in L$, we can iterate over all possible $y in {0,1}^(p(|x|))$ (there are $2^(p(|x|))$ of them) and check if $M(x,y)=1$ for any $y$.
]
  This shows that every problem in cNP can be solved by an exponential-time algorithm.
*What we are really interested in, however, is whether there exists a polynomial-time algorithm for these problems.*

#pagebreak()

We are ready to meet out first $cNP$ language
#claim[
  $k$-clique is in $cNP$
]
#proof[
To prove this, we are reqiored to provide a polynomial-time verifier $M$ that takes as an input a graph $G$ and a witness $y$.
Since the choice of $y$ is up to us, we let $y=Y$ encode a set of vertices in $G$, and $M$ verifies that $Y$ is a clique of size $k$ in $G$.
#algorithm-figure(
  [Verifying algorithm for $k$-clique],
  vstroke: .5pt + luma(200),
  {
    import algorithmic: *
    Procedure(
      [$M$],
      ("G","Y"),
      {
        Comment[Check if the size of the group is large enough]
        If($|Y| !=k $, { Return(`false`)})
        LineBreak
        Comment[Check all the vertices are real]
        For($v in Y$,{
          If($v in.not V(G) $, { Return(`false`)})
        })
        LineBreak
        Comment[Check all the edges exist]
        For($v,u in Y$,{
          If($(v,u) in.not E(G) $, { Return(`false`)})
        })
        LineBreak
        Return(`true`)
      },
    )
  }
)

if $G in k$-clique, then there is a subset $V' subset.eq V(G)$ such that $G[V'] tilde.rev.equiv K_k$, and $M(G,V')=1$
if $G in.not k$-clique, then no matter which subset $V' subset.eq V(G)$ we take, $G[V']$ will never be a clique, meaning that $Y'$ either will have to many or too little vertices or have "fake" vertices or there will be some missing edges, so that $M(G,V')=0$

The algorithm above clearly runs in $O(2k) + O(k^2)$ time which is bounded by $|V(G)|^2$ as $k <= n$, #footnote[If $k>n$ then obviously no clique of size $k$ exists.] which is polynomial.
]

= Reductions
Suppose we have two languages#footnote[A language $L subset.eq {0,1}^*$ can represent any problem we have seen so far. For example, a graph $G$ can be encoded as a binary string, and one can ask whether that string belongs to  $L$.]/problems $L_1, L_2$, can we know which one of them is _harder_?
The intuition is that if by solving $L_2$, we can solve $L_1$, then $L_2$ is harder.
This is done by "translating" our problem from $L_1$ to $L_2$, solving our $L_2$ problem, and then answering accordingly.
The translation between languages is called a _reduction_, formally
#definition("polynomial time reduction")[
  Given two languages $L_1, L_2 in cNP$, we write $L_1 reduction L_2$ if there exists a function $f:{0,1}^* -> {0,1}^*$ and a polynomial $p: NN -> NN $, such that:
  - $x in L_1 <=> f(x) in L_2$
  - for every $x in {0,1}^*$, $f$ runs in $p(|x|)$ time.
]
Assuming that $L_1 reduction L_2$ and the polynomial reduction $f$ as well as a black box $A$ that solves $L_2$. 
We can create an algorithm $B$ that solves $L_2$ using only $f$ and $A$ in the following way.
#figure(
  image("figures/L1i1.png", width: 80%, height: 12%),
)
Since the new algorithm only needs to call $f$, then pass $f(x)$ to $A$ and aswer similarly, we got an algorithm for $B$ with similar time complexity as $A$.
Now if $A$ is polynomial, then $B$ is also polynimal.
// #align(center)[
//   B
// ]

// #place(center, dx: 0pt)[
//   A

#definition[
  A language $L subset.eq {0,1}^*$ is said to be NP-hard if  $L' reduction L$ for every $L' in cNP$
]

#question[
  Are there any languages that are NP-Hard?
]

#example[
  The language $
    L^*={ (L',x') : x' in L' and L' in cNP}$ is NP-hard.
]
Without going into too many details, if we have a solver $M$ for $L^*$,
then for any language $L'$ and input $x'$, we can decide whether $x' in L'$
y simply quering $M(L',x')$.
In other words, the reduction function $f$ from $L'$ to $L^*$ can be the identity: $f(x')=x'$.

In fact the language $L^* in cNP$, the verifier $M$ of $L^*$ asks for a witness $y=(M',x')$. where $M'$ is the verifier for $L'$ and $y'$ is the witness for $M'$ on input $x'$.
Note that $M'$ is a fixed algorithm that works for all inputs $x in {0,1}^*$, so its description has constant size, i.e. $|M'|=O(1)$.

#definition[
  A language $L subset.eq {0,1}^*$ is said to be NP-complete if $L in cNP$ and $L$ is NP-hard
]
One should be able to see now why having a polynomial algorithm for an $cNPC$ problem will result in $cP= cNP$,
and the first step in solving this is to find such a language.

#remark[
  Whoever proves that $cP=cNPC$ or shows that $cP != cNPC$ will be awarded
  1 million dollars.
]

Alas, the language $L^*$ is a bad candidate from an algorithmic point of view.
Any polynomial-time algorithm for $L^*$ would, in effect, have to "know" the polynomial-time algorithm for any $L in cNPC$.
So to know if $L^*$ is polynomial you first need to know if $cP=cNP$ which defeats the purpose.

#question[
  Is there a usefull language $L in cNPC$?
]

Let $x_1,...x_n$ be boolean variables ($x_i$ can be assigned either $0$ or $1$).
A boolean formula $phi$ is said to be in conjunctive normal form(CNF) if it has the form

#place(center,dx:-35pt)[
  #set text(size:10pt)
  Or between literals #arrow-label(<or_exp>,dx:-50pt,dy:-5pt)
]

#place(center,dx:80pt)[
  #set text(size:10pt)
  Literal #arrow-label(<literal_exp>,dx:-50pt,dy:-5pt)
]
\
\

$
  phi = underbrace((x_1 or x_17 or #arrow-label(<or>,dx:-9pt,dy:10pt) overline(x_25) or x_80 #arrow-label(<literal>,dx:-9pt,dy:10pt) ),"clause") and #arrow-label(<and>,dx: -6pt) underbrace(x_9,"also clause") and ...
$

#place(center,dx:35pt)[
  #set text(size:10pt)
  And between clauses #arrow-label(<and_exp>,dx:-50pt,dy:10pt)
]
#label-arrow(<literal_exp>,<literal>)
#label-arrow(<and_exp>,<and>)
#label-arrow(<or_exp>,<or>)
\
The appearances of the variable $x_i$ are called _literals_. Each literal can be positive($x_i$) or negative($overline(x_i)$).
A clause is a disjunction(OR) of literals, and the formula $phi$ is a conjunction(AND) of these clauses.
An assignment to the variables of $phi$ evaluates to either `true` or `false`,
and $phi$ is said to be satisfiable if there is some assignment such that $phi$ evaluates to `true`,
such assignment is called _satisfying assignment_.

#definition[
  CNF-SAT := {$phi$: $phi$ is a satisfiable CNF formula}
]

#example("1")[
$phi_1 := (x_1 or x_2) and overline(x_1) and(overline(x_2) or x_1 or x_3)in #text([CNF-SAT])$.
$
  phi(x_1 = F, x_2=T,x_3=T)=(F or T) and T and(F or F or T) = T
$

$phi_2 := (x_1 or x_2) and overline(x_1) and(overline(x_2) or x_1 or x_3) and overline(x_3)  in.not #text([CNF-SAT])$,

 if $phi_2$ is satisfiable, then $x_1,x_3$ must have the value $F$.
 Then, we are left with
  $
   phi_2(x_1 = F, x_3=F) = (F or x_2) and T and(overline(x_2) or F or F) and T 
  $
 to satisfy the first clause of $phi_2$ we need to set $x_2=T$, but to satisfy the third clause we need to set $x_2=F$ which is impossible, hence $phi_2$ is unsatifiable.
]

#pagebreak()
#theorem("Cook-Levin")[
  CNF-SAT is npc.
]
Fortunately for the students, the proof is beyond the scope of this course and will be omitted,
although curious students can look at up in Computational Complexity by Aroara and Barak.

Following the discovery of the first $cNPC$ language, many other problems have been shown to be in $cNPC$ as well.
The first in which we are interested is a variation of the classical CNF. For an integer $k in NN$, define
$
  k"-CNF-SAT" := {phi | phi "is a CNF formula in which each clause has exactly " k "literals"}.
$
#example[
  $(x_1 or overline(x_1))  and (x_2 or x_3)$ is in 2-CNF-SAT,\
  $(x_1 or x_4 or x_5)  and (x_1 or overline(x_2) or x_3)$ is in 3-CNF-SAT.
]

Despite their similar definitions, there is a fundamental gap between these two problems as can be seen in the following claim:
#claim("proof is delegated to the practice session")[
  2-CNF-SAT is in $cP$.
]

#claim[
  3-CNF-SAT is in $cNPC$.
]<3CNF_is_NPC>
The proof that 3-CNF-SAT $ in  cNP$ is omitted and left for the reader.
Next, we need to show that for every language $L in cNP, L reduction 3"-CNF-SAT"$, which can be quite hard for us to do.
Instead we will use the fact that reductions are transitive:
#lemma[
  If $L_1 reduction L_2$ and $L_2 reduction L_3$, then $L_1 reduction L_3$.
]
By using this property, we can skip the long proof, and instead we show a reduction from a known $cNPC$ language.
We are now ready to prove @3CNF_is_NPC:\
#proof[
  We will show that CNF-SAT $ reduction$ 3-CNF-SAT. In order to show this, we need to define a function $f$ such that:
  1. *Running Time.*:$f$ runs in polynomial time.
  2. *Correctness*: for every formula $phi$,  $phi in "CNF-SAT" <=> f(phi) in  3-"CNF-SAT"$

  We will define $f$ as follows:
  For each clause $l_1 or l_2 ... or l_m$  of $phi$, we will replace it by a _gadget_ of clauses according to the following rules:
  #pad(x:10pt)[
  1. If $m=3$, then copy the clause as is.
  2. If $m < 3$, then repeat one of the literals until the clause has exactly $3$ literals. For example the literal $l_1 or l_2$ will become $l_1 or l_1 or l_2$.
  3. If $m > 3$ then create $m-3$ *new* variables named $y_1,...y_(m-3)$ and replace $l_1 or l_2 ... or l_m$ with the following:
    $
      (l_1 or l_2 or y_1) and (overline(y_1) or l_3 or y_2) and  (overline(y_2) or l_4 or y_3) and ... and (overline(y_(m-3)) or l_(m-1) or l_m).
    $
  ]

  It is easy to see that the first two steps take a constant amount of time, in the last condition the creation of $m-3$ takes $O(m)$ time per clause,
  and we create $m-3$ new clauses, each of which takes constant time, put everything together the running time of step 3 is $O(m)$ making our entire algorithm polynomial.
  Now, to prove the correctness we need to prove both directions:\

  $=>$(Completeness): Assume that $f(phi) in "CNF-SAT"$, This implies there exists a satisfying assignment $a$ for $phi$,
  We must show that there exists a satisfying assignment$a'$ for $f(phi)$.
  For each variable that was in $phi$ we copy its value from $a$ to $a'$ unchanged, this ensures that all clauses with 3 or fewer literals to stay satisfied by $a'$.
  Let $l_1 or l_2 ... or l_m$ be the literals of a clause of size at least 4, as the clause is satisfied under $a$, there is some $i in [m]$ such that $a(l_i) = 1$.
  We extend a to the auxiliary variables $y_j$ as follows: for all $j < i-1$, set $y_j = 1$, otherwise set $y_j = 0$.
  The clause containing $l_i$ is satisfied because of $l_i$, all the clauses before them are satisfied due to the positive literals of the new variables being 1.
  All the clauses that appear after the clause containing $l_i$ are satisfied due to the negative literals of the new variables being 0, meaning $f(phi) in 3-$CNF-SAT.

  $arrow.l.double$(Soundness): Assume that $f(phi) in 3"-CNF-SAT"$, This implies there exists a satisfying assignment $a'$ for $f(phi)$,
  We must show that there exists a satisfying assignment$a$ for $phi$.
  We argue the copying the assignment of the orginal variables form $a'$ to $a$  will produce a satisfying assignment for $phi$.
  To see this, assume torward a contradiction that $a$ is not a satsfying assigment for $phi$,
  that means that there is a clause $c = l_1 or l_2 or ... or l_m$ that is unsatisfied.
  If $m <=3$ Since $f$ copies these clauses (or simply repeats literals), and a uses the same values as $a′$,
  the corresponding clause in $f(phi$) would also be unsatisfied.
  This contradicts our assumption that $a′$ is a satisfying assignment.
  For the case $m > 3$. If $c$ is not satisfied, then all its literals must be false: $l_1 = l_2 = ... = l_m = 0$.
  In order to satisfy the clause gadget we need to satisfy all of the clauses it contains.
  In the first clause we have $l_1 = l_2 = 0$, which requires $y_1 = 1$ in oreder for the clause to be satisfied.
  For the second clause we have $overline(y_1) = l_3 = 0$ which requires $y_2 = 1$.
  Following this chain of logic, each $y_j$ is forced to be 1 to satisfy the $j$-th clause.
  Finnaly, we reach the last clause: $overline(y_(m-3)) or l_(m-1) or l_m$. Here $overline(y_(m-3)) = l_(m-1) = l_m = 0$.
  This last clause cannot be satisfied, which contradicts the assumption that $a′$ satisfies $f(phi)$.
  Therefore, $a$ must be a satisfying assignment for $phi$, and thus $phi in $ CNF-SAT.
]

== Independent set
For a graph $G$, let $alpha(G)$ denote its maximum independent set. Define:
#definition[
  $"IS" := {<G,k> : alpha (G) >= k}$.
]
#theorem[
  IS is in $cNPC$.
]

#proof[
  We show that $3$-CNF-SAT $reduction$ IS, proving that $"IS" in cNP$ is left as homework.
  Here the reduction might seem a little confusing at first, we are translating a formula into a graph and a number.
  Given a $3$-CNF formula $phi$, we construct a graph $G_phi$ as follows:
 1. *Triangles*: For each clause $l_1, l_2, l_3$ we create a triangle with 3 vertices named $v_l_1, v_l_2, v_l_3$.
 2. *Consistency Edges*: For any pair of complementary literals $x_j, overline(x_j)$ that are in different clauses, put an edge between the vertices that correspond to the literals.
 We return the pair $<G_phi,m>$ where $m$ is the number of clauses.
 While not intuitive at first, the number $m$ is chosen because an independent set can contain at most one vertex from each triangle.

 This algorithm indeed runs in polynomial time, as looping through all the clauses is linear in the number of clauses, and the maximum number of edges one can add is $n^2$.
 Now we need to prove
 $
   phi in 3"-CNF-SAT" <=> <G_phi,m> in "IS"
 $

 $=>$: Let $phi$ be satisfiable and let $a_phi$ be a satisfying assignment for $phi$.
 As $a_phi$ satisfies $phi$, at least one literal of each clause is satisfied, pick any one such literal from each clause.
 The set of vertices corresponding to the set of literals chosen is independent in $G_phi$ and has size of $m$.\
 $arrow.l.double$: Suppose $G_phi$ has an independent set size $m$.
 Define an assignment $a_phi$ for $phi$ by assigning values to the variables of $phi$ so that all the literals captured by the independent set are set to `true`,
 all others can be set to arbitrary values in a consistent manner.
 Because the graph is composed of triangles, each triangle can have only one vertex in the independent set, so each clause will have one variable satisfying the clause.
 Moreover, because complementary literals are connected,
 only the positive or negative literals of each variable can be in the independent set ensuring our assignment is consistent(there cannot be a variable assigned both `true` and `false`).
]

== Graph coloring
For a graph $G$ denote by $chi(G)$ the least $k in NN$ such that $G$ is k-colorable.
#definition[
  $k"-COL" := {G : chi(G) <= k}$
]
It is well known that $2$-COL$in cP$.
#theorem[
  $3"-COL" in cNPC$.
]
In order to prove the theorem, we intreduce a new $cNPC$ language.
Let $phi$ be a formula, $phi$ is said to be _not all equal satisfiable_(NAE-SAT) if it has a satisfying assigmnet such that in each caluse it has at least one satisfied literal and at least one that is not satisfied.
#definition([NAE-$k$-CNF-SAT])[
  NAE-$k$-CNF-SAT$:= {phi: phi "is NAE-SAT, with exactly k literals in each clause" }.$
]
The proof that NAE-$k$-CNF-SAT is NP-Complete is left to the practice sessions. We are ready to start our proof.\
#proof[
  We skip again the proof that $3"-COL" in cNP$, which is left as homework, and show that $$k$"-NAE-SAT" reduction 3"-COL"$.
  Given a 3-CNF formula $phi$, define $G_phi$ as follows:
  + Start with a single vertex $D$. This is our _Don't care vertex_.
  + For each variable $x_i$ of $phi$, add two new vertices $x_i, overline(x_i)$, add an edge between them, and connect both to $D$. This are our _variable gadgets_.
  + For each clause $l_1 or l_2 or l_3$ we create a triangle with 3 vertices named $l_1, l_2, l_3$, this is our _clause gadget_.
  + For each literal in the clause gadgets, connect it to the complementary variable from the variable gadget.
We skip the proof that the algorithm runs in polynomial time. It remains to prove that
$
  phi in "NAE-"k"-CNF-SAT" <=> G_phi in  3"-COL"
$


$=>$: Given a satisfying NAE assignment $a_phi$ for $phi$, define the follwing 3-coloting of $G_phi$:
- $D$ will be colored as #text(gray)[D]
- For each variable $x_i$, if $x_i$ is assigned `true` under $a_phi$ color $x_i$ as #text(red)[T] and $overline(x_i)$ in #text(blue)[F], otherwise color $x_i$ as #text(blue)[F] and $overline(x_i)$ in #text(red)[T]
- For each clause gadget, scan the corresponding clause $c$, color first literal that is assigned `true` with #text(red)[T], the first that assigned `false` with #text(blue)[F], and color the vertex that was left with #text(gray)[D].

It is clear that edges inside vertex/clause gadgets have both ends in different colors, it remains to show that edges between vertex and clause gadgets has its ends colored in different colors.
without loss of generality, let $x$ be a variable assigned `true` by $a_phi$. As $a_phi$ is proper, all of the vertices baring $overline(x)$ found in a clause gadgets are colored either #text(blue)[F] or #text(gray)[D], and the claim follows.

$arrow.l.double$:
Given a 3-coloring $psi$ of $G_phi$, we define a NAE-satisfying assignment for $phi$. As all of the variable gadgets form a triangles with a common vertex $D$, it leaves them with two colors to be chosen.
Take the variable gadget for an arbitrary variable $x$ and set the color under $x$ to be `true` and the color under $overline(x)$ to be `false`. This defines a valid assignmet to the variables of $phi$.
The assignment is NAE as each clause gadget has one variable colored `true` and one `false`.
]

== Max-cut
Given a graph $G$, a _cut_ is defined as the set of edges between $S subset.eq V(G)$ and $overline(S) = V(G) backslash S$. We denote the set of edges by $E_G (S,overline(S)) := {(u,v): (u,v) in E(G), u in S, v in overline(S)}$, and the number of edges by $e_G (S, overline(S)) := |E_G (S,overline(S))|$
Denote by $sigma(G) := max_(S subset.eq V(G)) e_G (S, overline(S))$.
#definition("MAX-CUT")[
  MAX-CUT $:= {<G,k> : sigma(G) >= k}$
]
#theorem[
  MAX-CUT$ in cNPC$
]
#proof()[
  We again skip the proof that MAX-CUT$ in cNP$, and show that MAX-CUT $reduction 3"-COL"$.
  Given a 3-CNF formula $phi$, define $G_phi$ as follows:
  + For each variable $x_i$ of $phi$, add two new vertices $x_i, overline(x_i)$ and an edge between them. These are our _variable gadgets_.
  + For each clause $l_1 or l_2 or l_3$, we create a triangle with vertices $l_1, l_2, l_3$; this is our _clause gadget_.
  + For each literal vertex in a clause gadget, connect it to the complementary literal vertex in the variable gadget.
  (This is the same as the NAE-$k$-CNF-SAT reduction to $3"-COL"$ but without the vertex $D$). We return the pair $<G_phi, n+5m>$.
  We skip the proof that the algorithm runs in polynomial time. It remains to prove that
  $
    phi in "NAE-"k"-CNF-SAT" <=> <G_phi, n+5m> in "MAX-CUT"
  $
  $=>$: Given a satisfying NAE assignment $a_phi$ for $phi$, define $S subset.eq V(G_phi)$ to consist of all vertices whose label is a literal assigned `true` under $a_phi$.
  As $a_phi$ is consistent, all variable gadgets must cross $(S,overline(S))$ adding $n$ edges to the cut.
  As $a_phi$ is a valid NAE assignment, at least two edges cross $(S,overline(S))$ in every clause gadget, adding $2m$ edges to the cut.
  Each edge between a variable and clause gadget has the form $(l,overline(l))$, which means it is also in the cut, adding $3m$ edges to the cut. Overall, we count at least $n+ 5m$ edges.

  $arrow.l.double$:
  Suppose that $<G_phi, n+5m> in "MAX-CUT"$. Let $(S,overline(S))$ be a cut of $G_phi$ such that $e_G_phi (S,overline(S)) = n + 5m$.
  Define the assignment $a_phi$ for $phi$ in which all variable gadget literals found in $S$ are assigned `true` and all remaining are assigned `false`. This defines a consistent assignment.
  It remains to prove that $a_phi$ is NAE-satisfying.
  Every edge between a variable and clause gadget is also in the cut and has the form $(l,overline(l))$.
  Because $e_G_phi (S,overline(S)) = n + 5m$, each clause gadget has 2 edges crossing $(S,overline(S))$, meaning each gadget has at least one vertex in $S$ and one in $overline(S)$.
  Take a vertex $l$ in a clause gadget that is in $S$. Then the edge $(l,overline(l))$ implies that $overline(l) in overline(S)$, meaning the literal corresponding to $l$ is assigned `true`. In a similar manner, if
  $l$ is in $overline(S)$ the then the edge  $(l,overline(l))$ means the $overline(l) in S$ implying that $l$ is assigned `false`.
]
