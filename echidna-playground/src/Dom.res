// SPDX-License-Identifier: AGPL-3.0-or-later
// SPDX-FileCopyrightText: 2025 Coq-Jr Contributors

// DOM bindings for ReScript

type element
type document
type window

@val external document: document = "document"
@val external window: window = "window"

@send external getElementById: (document, string) => Js.Nullable.t<element> = "getElementById"
@send external querySelector: (document, string) => Js.Nullable.t<element> = "querySelector"
@send external querySelectorAll: (document, string) => array<element> = "querySelectorAll"

@send external createElement: (document, string) => element = "createElement"
@send external createTextNode: (document, string) => element = "createTextNode"

@send external appendChild: (element, element) => unit = "appendChild"
@send external removeChild: (element, element) => unit = "removeChild"
@send external replaceChild: (element, element, element) => unit = "replaceChild"

@set external setInnerHTML: (element, string) => unit = "innerHTML"
@get external getInnerHTML: element => string = "innerHTML"

@set external setTextContent: (element, string) => unit = "textContent"
@get external getTextContent: element => string = "textContent"

@set external setClassName: (element, string) => unit = "className"
@get external getClassName: element => string = "className"

@send external setAttribute: (element, string, string) => unit = "setAttribute"
@send external getAttribute: (element, string) => Js.Nullable.t<string> = "getAttribute"
@send external removeAttribute: (element, string) => unit = "removeAttribute"

@send external addEventListener: (element, string, unit => unit) => unit = "addEventListener"
@send external removeEventListener: (element, string, unit => unit) => unit = "removeEventListener"

@get external getValue: element => string = "value"
@set external setValue: (element, string) => unit = "value"

module Style = {
  @set external setDisplay: (element, string) => unit = "style.display"
  @set external setVisibility: (element, string) => unit = "style.visibility"
  @set external setBackgroundColor: (element, string) => unit = "style.backgroundColor"
  @set external setColor: (element, string) => unit = "style.color"
  @set external setPadding: (element, string) => unit = "style.padding"
  @set external setMargin: (element, string) => unit = "style.margin"
}

module Body = {
  @val external body: element = "document.body"
}
