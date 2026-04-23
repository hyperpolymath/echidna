$( Minimal Metamath database — single $a (axiom) plus a $p (proof) that just
   re-states the axiom. metamath's "verify proof *" reports
   "All proofs in the database were verified" on success. $)
$c wff $.
$c p $.
wp $a wff p $.
th $p wff p $=
  wp $.
