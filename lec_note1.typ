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

= Complexity
Since the first

== Polynomial-time algorithms
An algorithm is called _polynomial-time_ if its running time is bounded by $O(n^c)$ where $n$ is the length of the input and $c$ is some (maybe huge) constant.
// For a problem $L$, we say the $L$ is polynomial if a polynimal algorthm exists for solving $L$.

#example[
  Common examples of polynomial-time algorithms include: DFS, BFS, Dijkstra's algorithm, 2-Coloring, and various sorting algorithms.
]

// Skipping some fundamental knowledge#footnote[For more information about this topic the reader is adviced to loop up Computational Comlexity by Aroara and Barak] we can now informally define:

#definition[
  $cP :=$ The set of problems that have a polynomial algorithm.
]

// #definition[
//   $cNP :=$ The set of problems that have a *non-deterministic* polynomial algorithm.
// ]<np>

// #definition[
//   $cNPC := $ The set of problems that if we find a polynomial-time algorithm that solves them then $cP = cNP$.
// ]<npc>

== Self reduction
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
The other way seems more complicated, but as it turns out for $cNPC$ languages it is possible.

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
          If($A(G) == 0$, { Return(`null`)})
          LineBreak
          While(
            $v(G) > k$,
            {
              import algorithmic: *
              Line([pick $v in V(G)$])
              If($A(G-v)==1$,{
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
  Otherwise, we know that there is a clique of size $k$ in $G$(maybe more then one),
  so if any point by removing some vertex $v in V(G)$ we get that $A(G-v)==0$ we know that $v$ is essential to the clique and leave it in $V(G)$.
  After going over all the vertices we are left only with the essential vertices, leaving us with a clique of size $k$.

  Now, we need to show that the algorithm runs in polynimal time. As we assume that $A$ run in polynomial time,
  there is some polynom $p$ such that the running time of $A(G)$ is bounded by $f(G)$.
  The first check is done in $f(G)$ time, then the algorithm will go through all vertcies, remove them from the graph and call $A$ on the modified graph,
  all of this will take $n dot f(G)$ time in the worst case making the runnig time of out algorith $O((n + 1)f(n))$ which is polynomial.
]


The claim above demonstrates that decision and search problem are equivalent#footnote[In our setting only], thus we can focus only on decision problems.

== NP-completeness
While the class $cP$ contains a large portion of the problems students have faced so far, as it turs out the majoriy of the problems are not easy at all.
Lets suppose that you are proffesional safe cracker who are in a competition with your friend who can hack a safe faster.
The safe has state of the art defence mechanisims, making it very hard to crack, none of the known method works for you.
You are trying entring every combination, but this takes a lot of time.
After some time your friend tell you that he was able to find a the code! and gives you a the book "One Million Digits Of Pi", and says the the password is in there.
You tell him that this does not count, as there is no way to know if he is right or not, just trying to read the book will take a lot of time.
But if he gives you the password, you have a way to know if he won or not, just enter the password and see if the safe opens and if it does, then it means that your friend is won.
But if it is not the right password, is there a way for you to know the real password? or even know that such password exists?
This demonstarins captures the essence of out next complexity class $cNP$, the set of problems where a proposed solution can be verified quickly. Formally,
#definition("NP class")[
  A language $L$ is said to be in $cNP$ if we have a polynomial-time algorithm $M$ such that
  $
    x in L <=> exists y space  s.t |y| < p(|x|) "and" M(x,y) = 1
  $
  where $p$ is some polynomial
]
#remark[
  In most literture $y$ is called a _witness_ and $V$ is called _veryfing algorithm_, where $y$ plays the role of the answer, and $M$ should just verify if the answer is correct.
]

We are ready to meet out first $cNP$ language
#claim[
  $k$-clique is in $cNP$
]
#proof[
To prove this, we must provide a polynomial-time verifier $M$ that takes a graph $G$ and a subset of vertices $Y$, and checks whether $Y$ forms a clique of sufficient size.
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
        If($|Y| <k $, { Return(`false`)})
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
if $G in.not k$-clique, then no matter which subset $V' subset.eq V(G)$ we take, $G[V']$ will never be a clique, meaning there will be some edge missing, and $M(G,V')=0$

#todo[time complexity]
]

== Reductions
Suppose we have two languages $L_1, L_2 subset.eq {0,1}^*$, can we know which one of them is _harder_?
The intuition is that if by solving $L_2$, we can solve $L_1$, then $L_2$ is harder.
This is done by "translating" our problem from $L_1$ to $L_2$, solving our $L_2$ problem, and then answering accordingly.
The translation between languages is called a _reduction_, formally
#definition("polynomial time reduction")[
  Given two languages $L_1, L_2 in cNP$, we write $L_1 reduction L_2$ if there exists a function $f:{0,1}^* -> {0,1}^*$ and a polynomial $p: NN -> NN $, such that:
  - $x in L_1 <=> f(x) in L_2$
  - for every $x in {0,1}^*$, $f$ runs in $p(|x|)$ time.
]
Now, if we have a black box $A$ that solves $L_2$, and we are given an instance $x$ for which we need to decide whether $x in L_1$, all we have to do is run $A(f(x))$ and return the same,
that means that $L_2$ is at least as hard as $L_1$.

#definition[
  A language $L subset.eq {0,1}^*$ is said to be NP-hard if  $L' reduction L$ for every $L' in cNP$
]
#definition[
  A language $L subset.eq {0,1}^*$ is said to be NP-complete if $L in cNP$ and $L$ is NP-hard
]
One should be able to see now why having a polynomial algorithm for an $cNPC$ problem will result in $cP= cNP$,
and the first step in solving this is to find such a language.

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
The follwoing theorem was proved by Cook and Levin:
#theorem("Cook-Levin")[
  CNF-SAT is npc.
]
Fortunately for the students, the proof is beyond the scope of this course and will be omitted,
although curious students can look at up in Computational Comlexity by Aroara and Barak.

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
  For each clause $l_1 or l_2 ... or l_m$  of phi, we will replace it by a _gadget_ of clauses according to the following rules:
  1. If $m=3$, then copy the clause as is.
  2. If $m < 3$, then repeat one of the literals until the clause has exactly $3$ literals. For example the literal $l_1 or l_2$ will become $l_1 or l_1 or l_2$.
  3. If $m > 3$ then create $m-3$ *new* variables named $y_1,...y_(m-3)$ and replace $l_1 or l_2 ... or l_m$ with the following:
    $
      (l_1 or l_2 or y_1) and (overline(y_1) or l_3 or y_2) and  (overline(y_2) or l_4 or y_3) and ... and (overline(y_(m-3)) or l_(m-1) or l_m).
    $

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
