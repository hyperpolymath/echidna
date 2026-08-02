$( Mini MetaMath corpus fixture.
   Set theory: tiny — propositional core only.
   Layout: constants, variables, $f hypotheses, one $a axiom, one $p
   theorem, plus a ${...$} scope block to exercise label qualification.
$)

$c ( ) -> wff |- $.
$v ph ps $.

wph $f wff ph $.
wps $f wff ps $.

$( Modus-ponens axiom — the canonical set.mm $a hazard. $)
ax-mp $a |- ps $.

$( Two-step modus ponens stated as a $p theorem citing ax-mp. $)
mp2 $p |- ps $= wph wps ax-mp $.

${
  $( Scoped helper: $a inside ${...$} should attach the inner scope
     qualifier to its qualified name. $)
  scoped-helper $a |- ph $.
$}

$j syntax 'wff' as 'wff'; $.
