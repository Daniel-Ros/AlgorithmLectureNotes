#import "settings/dstyle.typ":*

#show:conf.with(handout:false, subtitle:[Hamiltonicity])

#title-slide()

= Dirac's theorem
== Dirac's theorem
- A simple path spanning $V(G)$ is called a _Hamilton_ path
- A simple cycle spanning $V(G)$ is called a _Hamilton_ cycle
- A graph containing a Hamilton path is called _traceable_
- A graph containing a Hamilton cycle is called _Hamiltonian_

#figure(image("figures/ham-paths.png"))

#pagebreak()

Here are two examples for *non*-hamiltonian graph
#align(center)[
#columns(2)[
#diagram(
    node-stroke: 1pt,
    node-fill: black,
    debug: 0,
    node(enclose: ((2, -0.75), (2, 0.75)), inset: 10pt, stroke: teal, fill: teal.lighten(90%), name: <B>),
    node(enclose: ((0, -1), (0, 1)), inset: 10pt, stroke: teal, fill: teal.lighten(90%), name: <A>),

    for i in range(-2,2,step:1){
      edge((0,i/2), (2,i/3))
      edge((0,(i+1)/2), (2,i/3))
      edge((0,(i)/2), (2,(i+1)/3))
    }
  )

#colbreak()

#diagram(
node-stroke:1pt,
node((0,0),$K_(n/2+1)$,radius:50pt),
node((0.71,0),$K_(n/2)$,radius:50pt),
node((0.71/2,0),radius:3pt,fill:black),
)
]
]

#question[
What is common among the two examples?
]
Answer: They are both quite dense: $delta(G) = n/2 -1 $

#pagebreak()

#theorem(title:[Dirac's theorem])[
  Let $G$ have $v(G) >=3$ and $delta(G) >= n/2$. then $G$ is Hamiltonian
]
*_proof:_*
- Suppose the claim is false 
- let $G$ be an edge maximal couter example:
   - $G$ does not contain an Hamiltonian cycle
   - $G + e$ is Hamiltonian $forall e in.not E(G)$
- Let $e = u v in.not E(G)$
- As $G+e$ is Hamiltonian, $G$ contains a Hamilton path

#align(center)[
  #diagram(
    node-stroke:1pt,
    node-fill:black,
    node((0,0), [$u$],name:<u>, radius:2pt),
    node((1,0), $x_2$,name:<x2>, radius:2pt),
    node((2,0), $x_i$,name:<xi>, radius:2pt),
    node((3,0), $x_(i+1)$,name:<xi1>, radius:2pt),
    node((4,0), $x_(n-1)$,name:<xn1>, radius:2pt),
    node((5,0), $v$,name:<v>, radius:2pt),
    edge(<u>,<x2>),
    edge(<x2>,<xi>,"--"),
    edge(<xi>,<xi1>),
    edge(<xi1>,<xn1>,"--"),
    edge(<xn1>,<v>)
  )
]

#pagebreak()
- If we could find an edge $x_i x_(i+1)$ such that
  - $u x_(i+1) in E(G)$
  - $v x_i in E(G)$
- Then we can reroute our path, and turn it into Hamilton cycle

#align(center)[
  #diagram(
    node-stroke:1pt,
    node-fill:black,
    node((0,0), [$u$],name:<u>, radius:2pt),
    node((1,0), $x_2$,name:<x2>, radius:2pt),
    node((2,0), $x_i$,name:<xi>, radius:2pt),
    node((3,0), $x_(i+1)$,name:<xi1>, radius:2pt),
    node((4,0), $x_(n-1)$,name:<xn1>, radius:2pt),
    node((5,0), $v$,name:<v>, radius:2pt),
    edge(<u>,<x2>),
    edge(<x2>,<xi>,"--"),
    edge(<xi>,<xi1>),
    edge(<xi1>,<xn1>,"--"),
    edge(<xn1>,<v>),
    edge(<u>,<xi1>,bend:40deg),
    edge(<v>,<xi>,bend:40deg)
  )
  
]

#pagebreak()
- Define $S:= {i in [n] : u x_(i+1) in E(G)}$
  - note that $n in.not S$
  - but $1 in S$ as $u x_1 in E(G)$
- Define $T:= {i in [n] : v x_(i) in E(G)}$
  - note the $n in.not S$ as $G$ is simple
-If $|S cap T| != emptyset $ we can reroute

#pagebreak()
- Define $S:= {i in [n] : u x_(i+1) in E(G)}$
  - note that $n in.not S$
  - but $1 in S$ as $u x_1 in E(G)$
- Define $T:= {i in [n] : v x_(i) in E(G)}$
  - note the $n in.not S$ as $G$ is simple
- Assume the $|S cap T| = emptyset$

$
  |S cup T| = |S| + |T| - underbrace(|S cap T|,0) >= deg(u) + =deg(v) >= n/2 + n/2 = n
$

- We got $|S cup T| >= n$
- As $n in.not S cup T$, we get a contridiction.
 
