// SPDX-License-Identifier: AGPL-3.0-or-later
// SPDX-FileCopyrightText: 2025 Coq-Jr Contributors

// JsCoq bindings and types

type editorMode = {
  @as("company-coq") companyCoq: bool,
}

type editorConfig = {
  mode: editorMode,
  keyMap: string,
}

type coqOptions = {
  implicit_libs: bool,
  focus: bool,
  editor: editorConfig,
  init_pkgs: array<string>,
  all_pkgs: array<string>,
}

type coqInstance

// JsCoq loader bindings
@module("jscoq/ui-js/jscoq-loader.js")
external startExternal: (array<string>, coqOptions) => Js.Promise.t<coqInstance> = "start"

module JsCoqLoader = {
  @val @scope("JsCoq")
  external start: (array<string>, coqOptions) => Js.Promise.t<coqInstance> = "start"
}

let defaultOptions: coqOptions = {
  implicit_libs: false,
  focus: false,
  editor: {
    mode: {companyCoq: true},
    keyMap: "default",
  },
  init_pkgs: ["init"],
  all_pkgs: ["coq", "mathcomp"],
}

let makeOptions = (
  ~implicitLibs=false,
  ~focus=false,
  ~companyCoq=true,
  ~keyMap="default",
  ~initPkgs=["init"],
  ~allPkgs=["coq", "mathcomp"],
  (),
): coqOptions => {
  implicit_libs: implicitLibs,
  focus: focus,
  editor: {
    mode: {companyCoq: companyCoq},
    keyMap: keyMap,
  },
  init_pkgs: initPkgs,
  all_pkgs: allPkgs,
}
