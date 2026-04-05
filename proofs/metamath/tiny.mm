$( SPDX-License-Identifier: PMPL-1.0-or-later $)
$( tiny.mm -- a very small self-contained Metamath proof $)

$( Constants and variables $)
$c wff |- ( ) -> $.
$v P Q $.

wp $f wff P $.
wq $f wff Q $.

$( Well-formedness rule: implication $)
wi $a wff ( P -> Q ) $.

$( Axiom A1: a trivial truth frame $)
a1 $a |- ( P -> P ) $.

$( Theorem: prove a1 via the axiom itself (trivial but well-formed). $)
${
  trivial.1 $e |- P $.
  trivial $p |- P $= trivial.1 $.
$}
