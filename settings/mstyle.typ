#import "@preview/touying:0.6.1": *
#import themes.university: *
#import "@preview/numbly:0.1.0": numbly
#import "@preview/algo:0.3.6": algo, d, i

#import "@preview/theorion:0.4.1": *
#import "@preview/algorithmic:1.0.7"
#import "@preview/larrow:1.0.0": *
#import "@preview/fletcher:0.5.8" as fletcher: diagram, edge, node
#import "@preview/equate:0.2.1": *
#import cosmos.clouds: *

#let conf(body, handout: bool, subtitle: str) = {
  let (claim-counter, claim-box, claim, show-claim) = make-frame(
    "claim",
    "Claim",
    counter: none,
    render: render-fn.with(fill: navy.lighten(70%)),
  )
  show: show-claim


  let (question-counter, question-box, question, show-question) = make-frame(
    "question",
    "Question",
    counter: none,
    render: render-fn.with(fill: green.lighten(90%)),
  )
  show: show-question

  show: show-theorion


  import algorithmic: algorithm-figure, style-algorithm
  show: style-algorithm


  show: university-theme.with(
    aspect-ratio: "16-9",
    // align: horizon,
    config-common(handout: handout),
    config-page(margin: (top: 1.6cm, bottom: 2cm, x: 1.5cm)),
    config-info(
      title: [Algorithms 2],
      subtitle: [#subtitle],
      author: [Daniel Rosenberg & Michael Trushkin],
      // date: datetime.today(),
      institution: [Ariel University],
      // logo: emoji.school,
    ),
  )

  set heading(numbering: numbly("{1}.", default: "1.1"))
  show heading.where(level: 2): set text(fill: white.darken(5%))

  set text(
    size: 18pt,
  )

  set page(
    // header: [
    //   // #text(size: 20pt, fill: white)[
    //   // Michael Trushkin
    //   // ]

    // ],
    background: {
      place(
        top,
        rect(
          fill: rgb("#073749"),
          width: 100%,
          height: 7%, // 1/5th of the page
        ),
      )
      place(
        top,
        rect(
          fill: rgb("#113f55"),
          width: 100%,
          height: 6.5%, // 1/5th of the page
        ),
      )
    },
    margin: (bottom: 0cm),
  )
  show emph: it => text(fill: rgb("#3461f6"), it)


  body
}

#let bent-edge(from, to, mid: 40%, ..args) = {
  let midpoint = (from, mid, to)
  let vertices = (
    from,
    (from, "|-", midpoint),
    (midpoint, "-|", to),
    to,
  )
  edge(..vertices, "-|>", ..args)
}

////// ENVIROMENTS

#let (definition-counter, definition-box, problem, show-definition) = make-frame(
  "definition",
  theorion-i18n-map.at("problem"),
  counter: none,
  render: (..args) => {
    set text(fill: rgb("#681811"))
    show strong: it => [#text(weight: "bold", fill: rgb("#a7051d"))[#it.body]]
    show emph: it => [#text(weight: "bold", style: "italic", fill: rgb("#c00d28"))[#it.body]]

    render-fn(fill: rgb("#e5d7c4"), ..args)
  },
)

#let (definition-counter, definition-box, question, show-definition) = make-frame(
  "question",
  "Question",
  counter: none,
  render: (..args) => {
    set text(fill: rgb("#0c020d"))
    show strong: it => [#text(weight: "bold", fill: rgb("#c00d28"))[#it.body]]
    show emph: it => [#text(weight: "bold", style: "italic", fill: rgb("#c00d28"))[#it.body]]

    render-fn(fill: rgb("#e7dac9"), ..args)
  },
)


#let (definition-counter, definition-box, observation, show-definition) = make-frame(
  "question",
  "Observation",
  counter: none,
  render: (..args) => {
    set text(fill: rgb("#0c020d"))
    show strong: it => [#text(weight: "bold", fill: rgb("#0d187f"))[#it.body]]
    show emph: it => [#text(weight: "bold", style: "italic", fill: rgb("#060102"))[#it.body]]

    render-fn(fill: rgb("#bfbebe"), ..args)
  },
)

#let (definition-counter, definition-box, definition, show-definition) = make-frame(
  "definition",
  theorion-i18n-map.at("definition"),
  counter: none,
  render: render-fn.with(fill: rgb("#bfdce2")),
)



#let (definition-counter, definition-box, claim, show-definition) = make-frame(
  "definition",
  "Goal",
  counter: none,
  render: (prefix: none, title: "", full-title: "", body) => {
    render-fn(
      fill: rgb("#b3b0bf"),
      prefix: prefix,
      full-title: [#text(fill: rgb("#934444"), weight: "bold")[Claim #title:]],
      title: title,
      // Apply the show rule ONLY to the body content here:
      [
        #set text(fill: rgb("#000000"))
        #body
      ],
    )
  },
)

#let (definition-counter, definition-box, ulemma, show-definition) = make-frame(
  "definition",
  "Goal",
  counter: none,
  render: (prefix: none, title: "", full-title: "", body) => {
    render-fn(
      fill: rgb("#b3b0bf"),
      prefix: prefix,
      full-title: [#text(fill: rgb("#934444"), weight: "bold")[Lemma #title:]],
      title: title,
      // Apply the show rule ONLY to the body content here:
      [
        #set text(fill: rgb("#000000"))
        #body
      ],
    )
  },
)

#let (theorem-counter, theorem-box, theorem, show-theorem) = make-frame(
  "theorem",
  theorion-i18n-map.at("theorem"),
  counter: none,
  render: (..args) => {
    set text(fill: rgb("#ffffff"))
    show strong: it => [#text(weight: "bold", fill: rgb("#e6dbdb"))[#it.body]]
    render-fn(fill: rgb("#073749"), ..args)
  },
)

#let (definition-counter, definition-box, assumption, show-definition) = make-frame(
  "definition",
  "Goal",
  counter: none,
  render: (prefix: none, title: "", full-title: "", body) => {
    render-fn(
      fill: rgb("#fdd1d1"),
      prefix: prefix,
      full-title: [#text(fill: rgb("#6068fb"), weight: "bold")[Assumption #title:]],
      title: title,
      // Apply the show rule ONLY to the body content here:
      [
        #set text(fill: rgb("#2844b5"))
        #body
      ],
    )
  },
)

#let proof(
  title: [#text(fill: blue.darken(50%), weight: "bold")[Proof]],
  qed: auto,
  body,
) = context if get-result(here()) == "noanswer" { none } else {
  let qed-symbol = if qed == auto { get-qed-symbol(here()) } else { qed }
  [#emph(theorion-i18n(title)).#sym.space#body#box(width: 0em)#h(1fr)#sym.wj#sym.space.nobreak$#qed-symbol$]
}

#let (definition-counter, definition-box, goal, show-definition) = make-frame(
  "definition",
  "Goal",
  counter: none,
  render: (prefix: none, title: "", full-title: "", body) => {
    render-fn(
      fill: rgb("#e2f6d1"),
      prefix: prefix,
      full-title: [#text(fill: rgb("#d2722d"), weight: "bold")[Goal #title:]],
      title: title,
      // Apply the show rule ONLY to the body content here:
      [
        #body
      ],
    )
  },
)

// #let (theorem-counter, theorem-box, theorem, show-theorem) = make-frame(
//   "theorem",
//   theorion-i18n-map.at("theorem"),
//   inherited-levels: 2,
// render: (prefix: none, title: "", full-title: "", body) => {
//     render-fn(
//       fill: rgb("#d1f4f6"),
//       prefix: prefix,
//       full-title: [#text(fill: rgb("#a28276"), weight: "bold")[#full-title]],
//       title: title,
//       // Apply the show rule ONLY to the body content here:
//       [
//         #show strong: it => [#text(weight: "bold", fill: red)[#it.body]]
//         #body
//       ]
//     )
//   }
// )

#let bt(color, body) = {
  text(fill: color, weight: "bold")[#body]
}

#let tr(body, s: 1.0) = {
  text(fill: red, weight: "bold", size: 0.8em * s)[#body]
}

#let cup = math.union
#let cap = math.inter


#let cetz-canvas = touying-reducer.with(reduce: cetz.canvas, cover: cetz.draw.hide.with(bounds: true))
#let sbullet = box(baseline: -0.15em)[#text(size: 0.55em)[$bullet$]]
#let reduction = $scripts(<=)_p$