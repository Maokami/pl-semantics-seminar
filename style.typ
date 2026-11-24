#let ink = rgb("#17212c")
#let muted = rgb("#465363")
#let accent = rgb("#5e2f3a")
#let rule = rgb("#cbd0d6")
#let tint = rgb("#f3f4f6")
#let sans = "Apple SD Gothic Neo"
#let monospace = "Menlo"

#let document-layout(label, body, lang: "ko", font: sans, author: "PL 스터디") = {
  set document(author: author, title: label)
  set text(font: font, size: 11pt, fill: ink, lang: lang)
  set par(leading: 0.62em, spacing: 0.85em)
  set page(
    paper: "a4",
    margin: (left: 21mm, right: 21mm, top: 23mm, bottom: 23mm),
    header-ascent: 38%,
    footer-descent: 40%,
    header: context if counter(page).get().first() > 1 [
      #set text(size: 9pt, fill: muted)
      #label
      #v(2pt)
      #line(length: 100%, stroke: 0.45pt + rule)
    ],
    footer: [
      #line(length: 100%, stroke: 0.45pt + rule)
      #v(2pt)
      #set text(size: 9pt, fill: muted)
      #label #h(1fr) #context counter(page).display()
    ],
  )
  show heading.where(level: 2): it => context if target() == "html" { html.elem("h2", it.body) } else { block(above: 12pt, below: 6pt)[
    #text(size: 14pt, weight: "bold", fill: accent, it.body)
  ] }
  show heading.where(level: 3): it => block(above: 9pt, below: 4pt)[
    #text(size: 11.5pt, weight: "bold", it.body)
  ]
  show link: it => text(fill: accent, it)
  show math.equation: set text(font: "New Computer Modern Math")
  body
}

#let small(body) = text(size: 9.6pt, fill: muted, body)
#let mono(s) = text(font: monospace, size: 0.88em, s)

#let code(s) = block(width: 100%, fill: tint, inset: (x: 12pt, y: 8pt), radius: 2pt)[
  #mono(s)
]

#let cover(subject, title, aim) = context if target() == "html" {
  html.elem("header", [#subject #html.elem("h1", title) #par(aim)])
} else [
  #v(8pt)
  #text(fill: accent, size: 13pt, weight: "bold", subject)
  #v(3pt)
  #text(size: 34pt, weight: "bold", title)
  #v(6pt)
  #line(length: 100%, stroke: 1.25pt + accent)
  #v(10pt)
  #text(size: 13pt, fill: muted, aim)
  #v(4pt)
]

#let section-top(label, title) = context if target() == "html" {
  html.elem("h2", [#label · #title])
} else [
  #text(fill: accent, size: 10pt, weight: "bold", label)
  #v(1pt)
  #text(size: 24pt, weight: "bold", title)
  #v(5pt)
  #line(length: 100%, stroke: 0.8pt + accent)
  #v(8pt)
]

#let perspective(term, description) = block(above: 6pt, below: 6pt, breakable: false)[
  #text(weight: "bold", term) #h(4pt) #description
]

#let unit(id, title, aim, entries, check-label, check, lab) = context if target() == "html" {
  html.elem("section", [
    #section-top("단원 " + id, title)
    #par(aim)
    #for (number, topic, task, reading) in entries {
      html.elem("h3", [#number. #topic])
      par(task)
      par(emph(reading))
    }
    #par([*#check-label* #check])
    #par(lab)
  ])
} else [
  #section-top("단원 " + id, title)
  #text(size: 11pt, fill: muted, aim)
  #v(6pt)
  #for (number, topic, task, reading) in entries {
    block(width: 100%, above: 7pt, below: 7pt, breakable: false)[
      #line(length: 100%, stroke: 0.45pt + rule)
      #v(3pt)
      #grid(
        columns: (31pt, 1fr), gutter: 6pt,
        text(size: 12pt, weight: "bold", fill: accent, str(number)),
        [
          #text(size: 11.5pt, weight: "bold", topic)
          #linebreak()
          #task
          #linebreak()
          #small(reading)
        ],
      )
    ]
  }
  #v(5pt)
  #block(width: 100%, fill: tint, inset: 9pt, radius: 2pt, breakable: false)[
    #text(weight: "bold", check-label) #h(3pt) #check
  ]
  #small(lab)
]

#let source(tag, title, address, detail) = context if target() == "html" {
  par([#tag · #link(address, title) #linebreak() #detail])
} else { block(above: 7pt, below: 7pt, breakable: false)[
  #grid(
    columns: (33pt, 1fr), gutter: 5pt,
    text(size: 9pt, weight: "bold", fill: muted, tag),
    [
      #link(address)[#strong(title)]
      #linebreak()
      #small(detail)
    ],
  )
]

}

#let statement(name, body) = block(width: 100%, fill: tint, inset: 11pt, radius: 2pt)[
  #text(fill: accent, weight: "bold", name)
  #v(3pt)
  #body
]
