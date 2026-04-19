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
#[
#diagram(
    node-stroke: 1pt,
    node-fill: black,
    debug: 0,
    node(enclose: ((2.5, -0.75), (2, 0.75)), inset: 10pt, stroke: teal, fill: teal.lighten(90%), name: <B>),
    node(enclose: ((-0.5, -1), (0, 1)), inset: 10pt, stroke: teal, fill: teal.lighten(90%), name: <A>),

    for i in range(-2,2,step:1){
      edge((0,i/2), (2,i/3))
      edge((0,(i+1)/2), (2,i/3))
      edge((0,(i)/2), (2,(i+1)/3))
    }
  )

  #place(
  top + left,
  dx: 3.5cm,
  dy: 2cm,
  [
    #set text(size: 0.7em)
    $n/2+1$
  ]
  )

    #place(
  top + left,
  dx: 8.3cm,
  dy: 2cm,
  [
    #set text(size: 0.7em)
    $n/2-1$
  ]
  )

      #place(
  top + left,
  dx: 5.5cm,
  dy: -0.2cm,
  [
    #set text(size: 0.7em)
    $K_(n/2+1, n/2-1)$
  ]
  )
]

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
  // - but $1 in S$ as $u x_1 in E(G)$
- Define $T:= {i in [n] : v x_(i) in E(G)}$
  - note the $n in.not S$ as $G$ is simple
  #v(-7pt) 
  $==> |S cup T| <= n-1$. 
-If $|S cap T| != emptyset $ we can reroute

#place(
  top + left,
  dx: 15cm,
  dy: 1.5cm,
align(center)[
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
)


#pagebreak()
- Define $S:= {i in [n] : u x_(i+1) in E(G)}$
  - note that $n in.not S$
  // - but $1 in S$ as $u x_1 in E(G)$
- Define $T:= {i in [n] : v x_(i) in E(G)}$
  - note the $n in.not S$ as $G$ is simple
   #v(-7pt) 
    $==> |S cup T| <= n-1$. 
- Assume the $|S cap T| = emptyset$
#place(
  top + left,
  dx: 15cm,
  dy: 1.5cm,
align(center)[
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
)
$
  |S cup T| = |S| + |T| - underbrace(|S cap T|,0) >= deg(u) + deg(v) >= n/2 + n/2 = n
$

- We got $|S cup T| >= n$
- As $n in.not S cup T$, we get a contridiction.
 
= Eros-Chvatal 
== Lolipops
- Let $C$ be a cycle in $G$.
- By a bridge of $C$ we mean:
  1. an edge between two vertices of $C$, called a cord. #text(fill: red, size: 0.8em, weight: "bold")[(those are trivial bridges)]
  #[
    #set align(center)
  #diagram(
    node-stroke:2pt,
    node-fill:black,
    for i in range(0 , 360,step:60){
        node((rel:(i * 1deg, 1),to :(0,0)),radius:2pt,name:"v" + str(i))
        if ( i != 300){
          edge()
        }
    },
    edge(<v0>,<v300>),
    edge(<v180>,<v300>),
    edge(<v60>,<v300>),
  )
  ]
  - connected components of $G-C$ that has neighbors in $C$, those are non-trivial bridges
  #[
    #set align(center)
  #diagram(
    node-stroke:2pt,
    node-fill:black,
    for i in range(0 , 360,step:60){
        node((rel:(i * 1deg, 1),to :(0,0)),radius:2pt,name:"v" + str(i))
        if ( i != 300){
          edge()
        }
    },
    edge(<v0>,<v300>),
     node(enclose: ((2.5, -0.75), (2, 0.75)), inset: 10pt, stroke: teal, fill: teal.lighten(90%), name: <A>),
      node(enclose: ((-2.5, -0.75), (-2, 0.75)), inset: 10pt, stroke: teal, fill: teal.lighten(90%), name: <B>),
      
      edge(<B>,<v180>),
      edge(<B>,<v240>),
      
      edge(<v0>,(2,-0.5)),
      edge(<v0>,(2,0.5)),
  )
  ]

    #place(
  top + left,
  dx: 6.5cm,
  dy: 9cm,
  [
    #set text(size: 0.7em, weight: "bold")
    bridge
  ]
  )

      #place(
  top + left,
  dx: 15.4cm,
  dy: 9cm,
  [
    #set text(size: 0.7em, weight: "bold")
    bridge
  ]
  )

#pagebreak()
#definition[
  - Let $P$ be a $x ~> y$ path in $G$
  - Let $C$ be a cycle in $G$ 
  - If $y in C$ then $C cup P$ is called _$(x,y)$-lollipop_
]
#[
  #h(30%)
 #diagram(
    node-stroke:2pt,
    node-fill:black,
    for i in range(0 , 360,step:60){
        node((rel:(i * 1deg, 0.5),to :(0,0)),radius:2pt,name:"v" + str(i))
        if ( i != 300){
          edge()
        }
    },
    edge(<v0>,<v300>),
    node((rel:(0deg, 0.5),to :(0,0)),align(left)[$y$],radius:2pt,name:<y>),
    node((rel:(0deg, 2),to :(0,0)),align(left)[$x$],radius:2pt,name:<x>),
    
    edge(<x>,<y>,"--")
  )
]
- Let $v in V(C)$ and orient $C$
  - Denote by $v^+$ the successor of $v$
  - Denote by $v^-$ the predecessor of $v$

#place(dx:30em,dy:-5em)[
  #diagram(
    node-stroke:2pt,
    node-fill:black,

    node((rel:(0deg, 1),to :(0,0)),align(left)[
    $s$],radius:2pt,name:<s>),
     node((rel:(300deg, 1),to :(0,0)),align(top)[$s^-$],radius:2pt,name:<sm>),
      node((rel:(60deg, 1),to :(0,0)),align(left)[$s^+$],radius:2pt,name:<sp>),
      
      edge(<s>,<sm>),
      edge(<s>,<sp>),
      
      edge((rel:(120deg, 1),to :(0,0)),<sp>,"--"),
      edge((rel:(240deg, 1),to:(0,0)),<sm>,"--"),
  )
]
  
For $S subset.eq V(C)$ write
$
  S^+ := {s^+ : s in S} #h(5em) S^- := {s^-: s in S}
$
#pagebreak()

#lemma[
- Let $C$ be the largest cycle in $G$
- Let $C cup P$ be an $(x,y)$-lollipop
- The path $x y^+$ and $x y^-$ do not exists in $G$
]

#[
  #set align(center)
 #diagram(
    node-stroke:2pt,
    node-fill:black,
    for i in range(0 , 360,step:60){
        node((rel:(i * 1deg, 1),to :(0,0)),radius:2pt,name:"v" + str(i))
        if ( i != 300){
          edge()
        }
    },
    edge(<v0>,<v300>),
    node((rel:(0deg, 1),to :(0,0)),align(left)[$y$],radius:2pt,name:<y>),
    node((rel:(0deg, 3),to :(0,0)),align(left)[$x$],radius:2pt,name:<x>),
    
    edge(<x>,<y>,"--"),
    edge(<x>,<v300>,"--",stroke:red)
  )
]
== Erdos-Chvatal 
// #theorem(title:"Erdos Chvatal Theorem")[
// - Let $G$ have $v(G) >=3$ 
// - If $kappa(G) >= alpha(G)$ then $G$ is Hamiltonian. 
// ]
// #pause

// *_proof:_*
// - Assume the claim is false
// - Let $C$ be the longest cycle in $G$
// - Why such cycle exists?
//   - If $G$ is disconnected the $0= kappa(G) >= alpha(G) = 2$, contridiction
//   - If $G$ is a connected tree then $1 = kappa(G) = alpha(G) = 2$
// - As $G$ is not hamiltonial $V(G)\V(C) != emptyset$
// - Then $G$ admits a non-trivial bridge with $>=2$ points of attachment
// - Why?

  
// #pagebreak()
#theorem(title:"Erdos Chvatal Theorem")[
- Let $G$ have $v(G) >=3$ 
- If $kappa(G) >= alpha(G)$ then $G$ is Hamiltonian. 
]

 #pause
*_proof:_*
- Assume the claim is false $=>$ 
- Then $G$ admits a non-trivial bridge with $>=2$ points of attachment
- Why?
  - Assume the bridge has $<2$ points of attchments
  - Observe the components of $G-C$, one of the two can happen

#place(
  top + left,
  dx: 3cm,
  dy: 70%,
columns(2)[
#diagram(
    node-stroke:2pt,
    node-fill:black,
    for i in range(0 , 360,step:60){
    if i in (0,120,240){
        node((rel:(i * 1deg, 0.75),to :(0,0)),radius:2pt,name:"v" + str(i))
    }else{
    node((rel:(i * 1deg, 0.75),to :(0,0)),radius:2pt,name:"v" + str(i),fill:red,stroke:red)
    } 
        if ( i != 300){
          edge()
        }
    },
    edge(<v0>,<v300>),
     node(enclose: ((2, -0.75), (2, 0.75)), inset: 10pt, stroke: teal, fill: teal.lighten(90%), name: <A>),
 
      
      edge(<v0>,(2,-0.5)),
      edge(<v0>,(2,0.5)),
      
      node((rel:(0deg, 0.75),to :(0,0)),radius:10pt,stroke:green ,fill:none),
  )\
  $1 = kappa(G) >= alpha(G) >= 2$, Contridiction
#colbreak()
#diagram(
    node-stroke:2pt,
    node-fill:black,
    for i in range(0 , 360,step:60){
    if i in (0,120,240){
        node((rel:(i * 1deg, 0.75),to :(0,0)),radius:2pt,name:"v" + str(i))
    }else{
    node((rel:(i * 1deg, 0.75),to :(0,0)),radius:2pt,name:"v" + str(i),fill:red,stroke:red)
    } 
        if ( i != 300){
          edge()
        }
    },
    edge(<v0>,<v300>),
     node(enclose: ((2, -0.75), (2, 0.75)), inset: 10pt, stroke: teal, fill: teal.lighten(90%), name: <A>),
 

  )
  
  $0 = kappa(G) >= alpha(G) >= 2$, Contridiction
]
)
  
#pagebreak()

// #theorem(title:"Erdos Chvatal Theorem")[
// - Let $G$ have $v(G) >=3$ 
// - If $kappa(G) >= alpha(G)$ then $G$ is Hamiltonian. 
// ]

#table(
  columns: (1fr, 1fr),
  stroke: none,
  [
    Assume the claim is false.
    #goal[show that $alpha(G) > kappa(G).$]],
  [#theorem(title:"Erdos Chvatal Theorem")[
- Let $G$ have $v(G) >=3$ 
- If $kappa(G) >= alpha(G)$ then $G$ is Hamiltonian. 
]]
)

#place(dx:27em)[
#diagram(
    node-stroke:2pt,
    node-fill:black,
    for i in range(0 , 360,step:60){
        node((rel:(i * 1deg, 0.75),to :(0,0)),radius:2pt,name:"v" + str(i))

        if ( i != 300){
          edge()
        }
    },
    edge(<v0>,<v300>),
     node(enclose: ((2, -0.75), (2, 0.75)), inset: 10pt, stroke: teal, fill: teal.lighten(90%), name: <A>),
 
      
      edge(<v300>,(2,-0.5)),
      edge(<v300>,(2,-0.1)),
      
      edge(<v60>,(2,0.5)),
      edge(<v60>,(2,0.1)),
      
      node((rel:(300deg, 0.75),to :(0,0)),radius:10pt,stroke:green ,fill:none),
     node((rel:(60deg, 0.75),to :(0,0)),radius:10pt,stroke:green ,fill:none),
  )
]

#place(dx:27em, dy: 40%)[
#diagram(
    node-stroke:2pt,
    node-fill:black,
    for i in range(0 , 360,step:60){
        node((rel:(i * 1deg, 0.75),to :(0,0)),radius:2pt,name:"v" + str(i))

        if ( i != 300){
          edge()
        }
    },
    edge(<v0>,<v300>),
     node(enclose: ((2, -0.75), (2, 0.75)), inset: 10pt, stroke: teal, fill: teal.lighten(90%), name: <A>),
 
      
      edge(<v300>,(2,-0.5)),
      edge(<v300>,(2,-0.1), stroke: (paint: blue, dash: (3pt, 2pt), thickness: 2pt)),
      
      edge(<v60>,(2,0.5)),
      edge(<v60>,(2,0.1), stroke: (paint: blue, dash: (3pt, 2pt), thickness: 2pt)),
      // edge(<v30>,<v90>),
      edge(<v240>,<v0>, stroke: red),
      edge(<v0>, <v300>, stroke: (paint: blue, dash: (3pt, 2pt), thickness: 2pt)),
      edge(<v120>, <v60>, stroke: (paint: blue, dash: (3pt, 2pt), thickness: 2pt)),
      edge(<v120>, <v180>, stroke: (paint: blue, dash: (3pt, 2pt), thickness: 2pt)),
      edge(<v240>, <v180>, stroke: (paint: blue, dash: (3pt, 2pt), thickness: 2pt)),
      edge(<v240>, <v0>, stroke: (paint: blue, dash: (3pt, 2pt), thickness: 2pt)),
      // edge(<v120>, <v180>, stroke: blue),
  

      node((rel:(300deg, 0.75),to :(0,0)),radius:10pt,stroke:green ,fill:none),
     node((rel:(60deg, 0.75),to :(0,0)),radius:10pt,stroke:green ,fill:none),
  )
]

- $B$ the bridge, $S$ the attachment points of $B$ on $C$.
Case 1: $S subset V(C):$
- $|S| = kappa(G)$.
- Every $b in B$ and $s in S$ form a $(b,s)$-lollipop
- Orient $C ==> S^+$ is independent
  - Otherwise $C$ can be extended
- By the lollipop lemma: $forall b in B, s in S:b s^+ in.not E(G)$
\
#v(-40pt) #h(20pt) 
$==>$ The set $S^+ cup {b}$ is independent for every $b in B$.
- $alpha(G) >= |S| + 1 = kappa(G) + 1.$
 
 
#pagebreak()
#table(
  columns: (1fr, 1fr),
  stroke: none,
  [
    Assume the claim is false.
    #goal[show that $alpha(G) > kappa(G).$]],
  [#theorem(title:"Erdos Chvatal Theorem")[
- Let $G$ have $v(G) >=3$ 
- If $kappa(G) >= alpha(G)$ then $G$ is Hamiltonian. 
]]
)
- Case 2: $V(C)=S$.
  - fix $x in S$ and $b in B$ then $(x,b)$-lollipop is such that $b x^+ in E(G)$.
  - $C$ can be extended, contridiction to the maximality of $C$.
#align(center)[
#diagram(
    node-stroke:2pt,
    node-fill:black,
    for i in range(0 , 360,step:120){
        node((rel:(i * 1deg, 0.75),to :(0,0)),radius:2pt,name:"v" + str(i))

        if ( i != 240){
          edge()
        }
    },
    edge(<v0>,<v240>,stroke:red + 4pt),
     node(enclose: ((2, -0.75), (2, 0.75)), inset: 10pt, stroke: teal, fill: teal.lighten(90%), name: <A>),
 
      
      edge(<v0>,(2,-0.5),stroke:red + 4pt),
      edge(<v0>,(2,-0.1)),
      
      edge(<v120>,(2,0.5)),
      edge(<v120>,(2,0.1),stroke:red + 4pt),
      
      edge(<v240>,(2,-0.5)),
      
      edge(<v120>,<v240>,stroke:red + 4pt),
      
      edge((1.8,-0.5),(1.8,0.1),stroke:red + 4pt,snap-to:<A>),

  )
]

// - As the set $S$ is a vx-cut in $G$:
// $
//   kappa(G) <= |S| <= |S^+| < |S^+| + 1 = alpha(G)
// $
// contradiction.


