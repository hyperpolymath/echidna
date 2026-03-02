// SPDX-License-Identifier: AGPL-3.0-or-later
// SPDX-FileCopyrightText: 2025 Coq-Jr Contributors

// UI Components for jsCoq

module Html = {
  let element = (tag: string, ~className="", ~id="", children: array<string>): string => {
    let classAttr = className != "" ? ` class="${className}"` : ""
    let idAttr = id != "" ? ` id="${id}"` : ""
    let content = Js.Array2.joinWith(children, "")
    `<${tag}${idAttr}${classAttr}>${content}</${tag}>`
  }

  let div = element("div", ...)
  let span = element("span", ...)
  let p = element("p", ...)
  let h3 = element("h3", ...)
  let h4 = element("h4", ...)
  let h5 = element("h5", ...)
  let ul = element("ul", ...)
  let li = element("li", ...)
  let a = (~href: string, text: string): string => `<a href="${href}">${text}</a>`
  let img = (~src: string, ~height: string, ~alt=""): string =>
    `<img src="${src}" height="${height}" alt="${alt}">`
  let kbd = (text: string): string => `<kbd>${text}</kbd>`
  let code = (text: string): string => `<code>${text}</code>`
  let em = (text: string): string => `<em>${text}</em>`
  let i = (text: string): string => `<i>${text}</i>`
  let hr = (): string => `<hr/>`
  let br = (): string => `<br/>`

  let textarea = (~id: string, content: string): string =>
    `<textarea id="${id}">${content}</textarea>`

  let table = (~className="", rows: array<string>): string => {
    let classAttr = className != "" ? ` class="${className}"` : ""
    `<table${classAttr}>${Js.Array2.joinWith(rows, "")}</table>`
  }

  let tr = (cells: array<string>): string => `<tr>${Js.Array2.joinWith(cells, "")}</tr>`
  let th = (content: string): string => `<th>${content}</th>`
  let td = (content: string): string => `<td>${content}</td>`
}

module JsCoqName = {
  let render = (): string => {
    Html.span(~className="jscoq-name", ["jsCoq"])
  }
}

module ActionTable = {
  type action = {
    button: string,
    keyBinding: string,
    description: string,
  }

  let actions: array<action> = [
    {
      button: `${Html.img(~src="ui-images/down.png", ~height="15px")}${Html.img(
          ~src="ui-images/up.png",
          ~height="15px",
        )}`,
      keyBinding: `${Html.kbd("Alt")}+${Html.kbd("↓")}/${Html.kbd("↑")} or${Html.br()}${Html.kbd(
          "Alt",
        )}+${Html.kbd("N")}/${Html.kbd("P")}`,
      description: "Move through the proof.",
    },
    {
      button: Html.img(~src="ui-images/to-cursor.png", ~height="20px"),
      keyBinding: `${Html.kbd("Alt")}+${Html.kbd("Enter")} or${Html.br()} ${Html.kbd(
          "Alt",
        )}+${Html.kbd("→")}`,
      description: "Run (or go back) to the current point.",
    },
    {
      button: Html.img(~src="ui-images/power-button-512-black.png", ~height="20px"),
      keyBinding: Html.kbd("F8"),
      description: "Toggles the goal panel.",
    },
  ]

  let render = (): string => {
    let headerRow = Html.tr([Html.th("Button"), Html.th("Key binding"), Html.th("Action")])

    let rows = Js.Array2.map(actions, action => {
      Html.tr([Html.td(action.button), Html.td(action.keyBinding), Html.td(action.description)])
    })

    Html.table(~className="doc-actions", Js.Array2.concat([headerRow], rows))
  }
}

module TeamSection = {
  type teamMember = {
    name: string,
    url: string,
    affiliations: array<(string, string)>,
  }

  let devTeam: array<teamMember> = [
    {
      name: "Emilio Jesús Gallego Arias",
      url: "https://www.irif.fr/~gallego/",
      affiliations: [
        ("Inria", "https://www.inria.fr"),
        ("Université de Paris", "https://u-paris.fr"),
        ("IRIF", "https://www.irif.fr"),
      ],
    },
    {
      name: "Shachar Itzhaky",
      url: "https://www.cs.technion.ac.il/~shachari/",
      affiliations: [("Technion", "https://cs.technion.ac.il")],
    },
  ]

  let contributors: array<teamMember> = [
    {
      name: "Benoît Pin",
      url: "",
      affiliations: [
        ("CRI", "https://www.cri.ensmp.fr/"),
        ("MINES ParisTech", "http://www.mines-paristech.eu"),
      ],
    },
  ]

  let renderMember = (member: teamMember): string => {
    let nameLink = member.url != "" ? Html.a(~href=member.url, member.name) : member.name

    let affiliationLinks = Js.Array2.joinWith(
      Js.Array2.map(member.affiliations, ((name, url)) => Html.a(~href=url, name)),
      ", ",
    )

    Html.li([`${nameLink} (${affiliationLinks})`])
  }

  let render = (): string => {
    let devList = Js.Array2.joinWith(Js.Array2.map(devTeam, renderMember), "")
    let contribList = Js.Array2.joinWith(Js.Array2.map(contributors, renderMember), "")

    Html.div(
      ~id="team",
      [
        `<a name="team"></a>`,
        Html.p([Html.i("The dev team")]),
        Html.ul([devList]),
        Html.p([Html.i("Contributors")]),
        Html.ul([contribList]),
      ],
    )
  }
}

module CodeExamples = {
  let imports = `From Coq Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import eqtype ssrnat div prime.`

  let primeAbove1 = `(* A nice proof of the infinitude of primes, by Georges Gonthier *)
Lemma prime_above m : {p | m < p & prime p}.
Proof.`

  let primeAbove2 = `have /pdivP[p pr_p p_dv_m1]: 1 < m\`! + 1
  by rewrite addn1 ltnS fact_gt0.`

  let primeAbove3 = `exists p => //; rewrite ltnNge; apply: contraL p_dv_m1 => p_le_m.`

  let primeAbove4 = `by rewrite dvdn_addr ?dvdn_fact ?prime_gt0 // gtnNdvd ?prime_gt1.
Qed.`

  let codeIds = ["addnC", "prime_above1", "prime_above2", "prime_above3", "prime_above4"]
}
