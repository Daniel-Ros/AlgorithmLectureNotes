#import "settings/mstyle.typ" : *

#show: conf

#title-slide()

= Matchings in Graphs

== Matching in graphs

// #theorem[Euclid's Theorem][
//   There are infinitely many prime numbers.
// ] <thm:euclid>



#set align(horizon)

The matching problem is something that students face from the first time that they encounter graph theory.
Suppose that you have a group of $n$ people, that you want to divide into pairs, how would you go about it? Is is possible that every person finds a pair?
What if some people don't want to be paired together, can you do it then?

A common approach is to model this problem with a graph G.
Each vertex represents a person, and an edge between two vertices indicates that those two people can be paired together.

#pagebreak()
#set align(horizon)
For a graph $G$, two edges $e_1, e_2 subset.eq E(G)$ are called _indepedent_ if there is no common vertex between them.

#figure(
  image("figures/L2i1.png", width: 60%),
)

#pagebreak()
#set align(horizon)
#v(10pt)
A set $M subset.eq E(G)$ of independent edges is called _mathching_.

#figure(
  image("figures/L2i2.png", width: 100%),
)

- We write $V(M)$ to denote the ends of the members of $M$.
- We often treat $M$ as the subgraph of $G$ given by $(V(M), M)$.


== Spanning subgraph

A subgraph $H subset.eq G$ satisfying $V(H) = V(G)$ is said to be a _spanning_ subgraph of G
#figure(
  image("figures/L2i3.png", width: 100%),
)

== Perfect Matching
#set align(horizon)

#definition()[
  A matching $M subset.eq G$ is called _perfect matching_ or a _1-factor_ if $M$ is spanning $G$.
]
#figure(
  image("figures/L2i2.png", width: 78%),
)
#figure(
  image("figures/L2i4.jpeg", width: 40%),
)
// #theorem(title: "Cook-Levin")[
//   CNF-SAT is npc.
// ]
// 

#pagebreak()
#set align(horizon)

The following problem is of clear intrest

#problem()[
  Given a graph $G$, find a maximum matching in $G$.
]