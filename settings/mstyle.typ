#import "@preview/touying:0.6.1": *
#import themes.university: *
#import "@preview/numbly:0.1.0": numbly
#import "@preview/algo:0.3.6": algo, d, i

#import "@preview/theorion:0.4.1": *
#import "@preview/algorithmic:1.0.7"
#import "@preview/larrow:1.0.0": *

#import cosmos.clouds: *

#let conf(body) = {
let (claim-counter, claim-box, claim, show-claim) = make-frame(
  "claim",
  "Claim", // supplement, string or dictionary like `(en: "Theorem")`, or `theorion-i18n-map.at("theorem")` for built-in i18n support
  counter: theorem-counter, // inherit the old counter, `none` by default
  inherited-levels: 1, // useful when you need a new counter
  inherited-from: heading, // heading or just another counter
  render: render-fn.with(fill: navy.lighten(80%)),
)
show: show-claim


let (question-counter, question-box, question, show-question) = make-frame(
  "question",
  "Question", // supplement, string or dictionary like `(en: "Theorem")`, or `theorion-i18n-map.at("theorem")` for built-in i18n support
  counter: theorem-counter, // inherit the old counter, `none` by default
  inherited-levels: 2, // useful when you need a new counter
  inherited-from: heading, // heading or just another counter
  render: render-fn.with(fill: green.lighten(90%)),
)
show: show-question

show: show-theorion


import algorithmic: algorithm-figure, style-algorithm
show: style-algorithm


show: university-theme.with(
  aspect-ratio: "16-9",
  // align: horizon,
  // config-common(handout: true),
  config-common(frozen-counters: (theorem-counter,)), // freeze theorem counter for animation
  config-page(margin: (top: 1.6cm, bottom: 2cm, x: 1.5cm)),
  config-info(
    title: [Algorithms 2],
    subtitle: [Complexity],
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
)
show emph: it => text(fill: rgb("#3461f6"), it)
body
}

////// ENVIROMENTS

#let (definition-counter, definition-box, problem, show-definition) = make-frame(
  "definition",
  theorion-i18n-map.at("problem"),
  counter: theorem-counter,
  render: render-fn.with(fill: rgb("#e4c8a2")),
)

#let (definition-counter, definition-box, definition, show-definition) = make-frame(
  "definition",
  theorion-i18n-map.at("definition"),
  counter: theorem-counter,
  render: render-fn.with(fill: rgb("#bfdce2")),
)