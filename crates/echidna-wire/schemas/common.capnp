@0xf2f7187fddaa9139;

# Schema version stamped into every root message. Bumped only on incompatible
# changes per VERSIONING.md. L1.0 = 1.
const schemaVersionMajor :UInt16 = 1;
const schemaVersionMinor :UInt16 = 0;

struct Term {
  union {
    var      @0 :Text;
    const    @1 :Text;
    app      @2 :App;
    lambda   @3 :Lambda;
    pi       @4 :Pi;
    sigma    @5 :Sigma;
    typeU    @6 :UInt32;
    sort     @7 :UInt32;
    universe @8 :UInt32;
    letBind  @9 :Let;
    matchE  @10 :Match;
    fixE    @11 :Fix;
    hole    @12 :Text;
    meta    @13 :UInt64;
    proverSpecific @14 :ProverSpecific;
  }

  struct App     { func @0 :Term;  args @1 :List(Term); }
  struct Lambda  { param @0 :Text; paramType @1 :Term;  body @2 :Term; hasParamType @3 :Bool; }
  struct Pi      { param @0 :Text; paramType @1 :Term;  body @2 :Term; }
  struct Sigma   { param @0 :Text; paramType @1 :Term;  body @2 :Term; }
  struct Let     { name  @0 :Text; ty @1 :Term; value @2 :Term; body @3 :Term; hasTy @4 :Bool; }
  struct Match   { scrutinee @0 :Term; returnType @1 :Term; hasReturnType @2 :Bool;
                   branches  @3 :List(Branch); }
  struct Fix     { name  @0 :Text; ty @1 :Term; body @2 :Term; hasTy @3 :Bool; }
  struct ProverSpecific { prover @0 :Text; dataJson @1 :Text; }
  struct Branch  { pattern @0 :Pattern; body @1 :Term; }
}

struct Pattern {
  union {
    wildcard    @0 :Void;
    var         @1 :Text;
    constructor @2 :Ctor;
  }
  struct Ctor { name @0 :Text; args @1 :List(Pattern); }
}

struct Tactic {
  union {
    apply        @0 :Text;
    intro        @1 :IntroT;
    cases        @2 :Term;
    induction    @3 :Term;
    rewrite      @4 :Text;
    simplify     @5 :Void;
    reflexivity  @6 :Void;
    assumption   @7 :Void;
    exact        @8 :Term;
    custom       @9 :Custom;
  }
  struct IntroT  { name @0 :Text; hasName @1 :Bool; }
  struct Custom  { prover @0 :Text; command @1 :Text; args @2 :List(Text); }
}

struct Hypothesis {
  name     @0 :Text;
  ty       @1 :Term;
  body     @2 :Term;
  hasBody  @3 :Bool;
}

struct Goal {
  id         @0 :Text;
  target     @1 :Term;
  hypotheses @2 :List(Hypothesis);
}

struct Theorem {
  name      @0 :Text;
  statement @1 :Term;
  aspects   @2 :List(Text);
}

struct Context {
  theorems    @0 :List(Theorem);
  axioms      @1 :List(Text);
  definitions @2 :List(Definition);
  variables   @3 :List(Variable);
}

struct Definition { name @0 :Text; ty @1 :Term; body @2 :Term; }
struct Variable   { name @0 :Text; ty @1 :Term; }
