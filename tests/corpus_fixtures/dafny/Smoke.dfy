// SPDX-License-Identifier: MPL-2.0
// Dafny corpus-adapter smoke fixture.
// Exercises: module envelope, method, lemma, function, datatype, and
// one `assume` hazard so the parser's hazard tag fires.

module M {

  datatype Tree = Leaf | Node(left: Tree, right: Tree)

  function Size(t: Tree): nat
  {
    match t
    case Leaf => 0
    case Node(l, r) => 1 + Size(l) + Size(r)
  }

  method Inc(x: int) returns (y: int)
    ensures y == x + 1
  {
    y := x + 1;
  }

  lemma SizeNonneg(t: Tree)
    ensures Size(t) >= 0
  {
    // structural, trivial
  }

  lemma Sketchy()
    ensures false
  {
    assume false;
  }
}
