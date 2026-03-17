#import "theme.typ" : *
#import "@preview/algorithmic:1.0.7"
#import "@preview/larrow:1.0.0": *

#let diaer = "\u{308}";

#import algorithmic: style-algorithm, algorithm-figure
#show: style-algorithm

#let todo(body) = text(red)[TODO:*#body*]

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

= Mathcing in graphs
The matching problem is something that students face from the first time that they encounter graph theory.
Suppose that you have a group of $n$ people, that you want to divide into pairs, how would you go about it? Is is possible that every person finds a pair?
What if some people don't want to be paired together, can you do it then? A common approcah is to model through the eyes of graph theory
For a graph $G$, two edges $e_1, e_2 subset.eq E(G)$ are called _indepedent_ if there is no common vertex between them.
A set $M subset.eq E(G)$ of independent edges is called _mathching_.
We write $V(M)$ to denote the ends of the members of $M$, and the vertcies of $V(M)$ are called _mathced_.
#definition[
 A matching $M$ of $G$ that satisfies $V(M) = V(G)$ is called _perfect mathcing_.#footnote[Another common name in the literatues is 1-factor]
]
Finding matches of size one is quite simple, the more maching we require the harder it gets, so the follwing question arises:
#question[
  Given a graph $G$, what is the maximum matching in $G?$
]
= Ko#diaer;nig's theorem
There are many ways to tackle the problem of maximum matching, the first of which 