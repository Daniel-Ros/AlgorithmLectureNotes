#import "theme.typ" : *
#import "@preview/algorithmic:1.0.7"

#import algorithmic: style-algorithm, algorithm-figure
#show: style-algorithm

#let todo(body) = text(red)[*#body*]
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
== Basic definitions
An algorithm is called _polynomial-time_ if its running time is bounded by $O(n^c)$ where $n$ is the length of the input and $c$ is some (maybe huge) constant.
// For a problem $L$, we say the $L$ is polynomial if a polynimal algorthm exists for solving $L$.

#example[
  Common examples of polynomial-time algorithms include: DFS, BFS, Dijkstra's algorithm, 2-Coloring, and various sorting algorithms.
]

Skipping some fundamental knowledge#footnote[For more information about this topic the reader is adviced to loop up Computational Comlexity by Aroara and Barak] we can now informally define:

#definition[
  $cP :=$ The set of problems that have a polynomial algorithm.
]

#definition[
  $cNP :=$ The set of problems that have a *non-deterministic* polynomial algorithm.
]<np>

#definition[
  $cNPC := $ The set of problems that if we find a polynomial-time algorithm that solves them then $cP = cNP$.
]<npc>

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
  In order to prove the claim, we need to provide a polynomial time algorithm.
  As we dont know any algorithm, we will use the fact that we have a polynomial algorithm for $k$-clique denoted by $A$.
  #import "@preview/algorithmic:1.0.7"
  #import algorithmic: style-algorithm, algorithm-figure
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
  )
  The rest of the proof is left for the reader.
]

The claim above demonstrates that decision and search problem are equivalent#footnote[In our setting only], thus we can focus only on decision problems.

== NP-completeness
We know how to tell if a language is in $cP$, how can we know if a language is in $cNP$?
We say that a language $L in cNP$ if there is a polynomial algorithm $M$,
such that for every instance $x in L <=> exists y space  s.t |y| < p(|x|) "and" M(x,y) = 1$, where $p$ is some polynomial.
The string $y$ is called a _witness_ and the algorithm is called a _verifying algorithm_, and the witness should play the role of the solution.
If such a solution for the problem exists, our algorithm should verify it and accept it, otherwise, the algorithm should reject every option for a solution.
// #todo[rewrite]
#remark[
  The witness $y$ is the non-deterministic choices that the algorithm can make.
]

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
Now if we have a black box $A$ that solves $L_2$, and we are given an instance $x$ for which we need to decide whether $x in L_1$, all we have to do is run $A(f(x))$ and return the same,
that means that $L_2$ is at least as hard as $L_1$.

#definition[
  A language $L subset.eq {0,1}^*$ is said to be NP-hard if  $L' reduction L$ for every $L' in cNP$
]

We can now refine our definition for $cNPC$:
#definition[
  A language $L subset.eq {0,1}^*$ is said to be NP-complete if $L in cNP$ and $L$ is NP-hard
]
One should be able to see now why having a polynomial algorithm for an $cNPC$ problem will result in $cP= cNP$,
and the first step in solving this is to find such a language.

Let $x_1,...x_n$ be boolean variables ($x_i$ can be assigned either $0$ or $1$).
A boolean formula $phi$ is said to be in conjunctive normal form(CNF) if it has the form
$
  phi = underbrace((x_1 or x_17 or overline(x_25) or x_80),"clause") overbrace(and, "and between clauses") underbrace(x_9,"also clause") and ...
$
The appearances of the variable $x_i$ are called _literals_. Each literal can be positive($x_i$) or negative($overline(x_i)$).
A clause is a disjunction(OR) of literals, and the formula $phi$ is a conjunction(AND) of these clauses.
An assignment to the variables of $phi$ evaluates to either `true` or `false`,
and $phi$ is said to be satisfiable if there is some assignment such that $phi$ evaluates to `true`,
such assignment is called _satisfying assignment_.
#definition[
  CNF-SAT := {$phi$: $phi$ is a satisfiable CNF formula}
]
The follwoing theorem was proved by Cook and Levin:
#theorem[
  CNF-SAT is npc.
]
Fortunately for the students, the proof is beyond the scope of this course and will be omitted, although curious students can look at up in Computational Comlexity by Aroara and Barak
