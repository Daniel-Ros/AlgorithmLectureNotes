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
    subtitle: [Complexity],
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

#set heading(numbering: numbly("{1}.", default: "1.1"))

#title-slide()

== Matching in graphs
The matching problem is something that students face from the first time that they encounter graph theory.
Suppose that you have a group of $n$ people, that you want to divide into pairs, how would you go about it? Is is possible that every person finds a pair?
What if some people don't want to be paired together, can you do it then?

A common approach is to model this problem with a graph G.
Each vertex represents a person, and an edge between two vertices indicates that those two people can be paired together.

#pagebreak()
For a graph $G$, two edges $e_1, e_2 subset.eq E(G)$ are called _indepedent_ if there is no common vertex between them.
A set $M subset.eq E(G)$ of independent edges is called _mathching_.
We write $V(M)$ to denote the ends of the members of $M$, and the vertcies of $V(M)$ are called _mathced_.
- An algorithm is called _polynomial-time_ if its running time is bounded by $O(n^c)$ where $n$ is the length of the input and $c$ is some (maybe huge) constant.
// For a problem $L$, we say the $L$ is polynomial if a polynimal algorthm exists for solving $L$.
