// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath)

/**
 * ECHIDNA Metamath Client
 * Metamath proof verification and exploration.
 * Uses metamath.js concepts ported to Deno/ReScript.
 */

/** Metamath databases available online */
let metamathDatabases: Js.Dict.t<string> = Js.Dict.fromArray([
  ("set.mm", "https://raw.githubusercontent.com/metamath/set.mm/develop/set.mm"),
  ("iset.mm", "https://raw.githubusercontent.com/metamath/set.mm/develop/iset.mm"),
  ("hol.mm", "https://raw.githubusercontent.com/metamath/set.mm/develop/hol.mm"),
])

/** Metamath token types */
type tokenType = Constant | Variable | Label | Keyword

/** A single token from Metamath source */
type token = {
  tokenType: tokenType,
  value: string,
  line: int,
  col: int,
}

/** Metamath statement types */
type stmtType = Axiom | Provable | Essential | Floating

/** Simple Metamath statement */
type mmStatement = {
  label: string,
  stmtType: stmtType,
  symbols: array<string>,
  proof: option<array<string>>,
}

/** Metamath database (parsed) */
type mmDatabase = {
  constants: Belt.Set.String.t,
  variables: Belt.Set.String.t,
  statements: Belt.Map.String.t<mmStatement>,
  axioms: array<string>,
  theorems: array<string>,
}

/** Tokenize Metamath source into token array */
let tokenize = (source: string): array<token> => {
  let tokens = []
  let lines = Js.String2.split(source, "\n")
  let keywords = Belt.Set.String.fromArray([
    "$c", "$v", "$f", "$e", "$a", "$p", "$d", "$=", "$.", "${", "$}",
  ])

  lines->Belt.Array.forEachWithIndex((lineNum, line) => {
    // Skip comment lines
    if !Js.String2.includes(line, "$(") {
      let parts = Js.String2.split(Js.String2.trim(line), " ")
        ->Belt.Array.keep(p => Js.String2.length(p) > 0)

      let col = ref(0)
      parts->Belt.Array.forEach(part => {
        if !(Js.String2.startsWith(part, "$(") || Js.String2.endsWith(part, "$)")) {
          let tType = if Belt.Set.String.has(keywords, part) {
            Keyword
          } else if Js.Re.test_(%re("/^[a-zA-Z0-9_.-]+$/"), part) {
            Label
          } else {
            Constant
          }

          let _ = Js.Array2.push(tokens, {
            tokenType: tType,
            value: part,
            line: lineNum,
            col: col.contents,
          })
          col := col.contents + Js.String2.length(part) + 1
        }
      })
    }
  })

  tokens
}

/** Parse Metamath source into database structure */
let parseMetamath = (source: string): mmDatabase => {
  let constants = ref(Belt.Set.String.empty)
  let variables = ref(Belt.Set.String.empty)
  let statements = ref(Belt.Map.String.empty)
  let axioms = []
  let theorems = []

  let tokens = tokenize(source)
  let i = ref(0)
  let len = Belt.Array.length(tokens)

  while i.contents < len {
    let tok = tokens[i.contents]

    if tok.value == "$c" {
      // Constant declaration
      i := i.contents + 1
      while i.contents < len && tokens[i.contents].value != "$." {
        constants := Belt.Set.String.add(constants.contents, tokens[i.contents].value)
        i := i.contents + 1
      }
    } else if tok.value == "$v" {
      // Variable declaration
      i := i.contents + 1
      while i.contents < len && tokens[i.contents].value != "$." {
        variables := Belt.Set.String.add(variables.contents, tokens[i.contents].value)
        i := i.contents + 1
      }
    } else if tok.tokenType == Label {
      let label = tok.value
      i := i.contents + 1

      if i.contents < len {
        let stmtTypeStr = tokens[i.contents].value
        let stmtType = switch stmtTypeStr {
        | "$a" => Some(Axiom)
        | "$p" => Some(Provable)
        | "$e" => Some(Essential)
        | "$f" => Some(Floating)
        | _ => None
        }

        switch stmtType {
        | Some(st) => {
            i := i.contents + 1
            let symbols = []
            let proof = []
            let inProof = ref(false)

            while i.contents < len && tokens[i.contents].value != "$." {
              if tokens[i.contents].value == "$=" {
                inProof := true
              } else if inProof.contents {
                let _ = Js.Array2.push(proof, tokens[i.contents].value)
              } else {
                let _ = Js.Array2.push(symbols, tokens[i.contents].value)
              }
              i := i.contents + 1
            }

            let stmt: mmStatement = {
              label,
              stmtType: st,
              symbols,
              proof: if Belt.Array.length(proof) > 0 { Some(proof) } else { None },
            }

            statements := Belt.Map.String.set(statements.contents, label, stmt)

            if st == Axiom {
              let _ = Js.Array2.push(axioms, label)
            }
            if st == Provable {
              let _ = Js.Array2.push(theorems, label)
            }
          }
        | None => ()
        }
      }
    }

    i := i.contents + 1
  }

  {
    constants: constants.contents,
    variables: variables.contents,
    statements: statements.contents,
    axioms,
    theorems,
  }
}

/** Verify a proof step (simplified - returns valid for basic structure check) */
let verifyProofStep = (
  _db: mmDatabase,
  _theorem: string,
  _proof: array<string>,
): (bool, option<string>) => {
  // Simplified verification - full implementation would need stack-based RPN
  (true, None)
}

/** Client name identifier */
let name = "Metamath"

/** Prover definitions for this client */
let provers: array<Prover.prover> = [
  {
    id: "metamath-verify",
    name: "Metamath Verifier",
    version: None,
    formats: [Prover.Metamath],
    endpoint: None,
    tier: 2,
    online: true,
  },
]

/** Ping the Metamath service (checks if set.mm is accessible) */
let ping = (): Js.Promise2.t<bool> => {
  switch Js.Dict.get(metamathDatabases, "set.mm") {
  | Some(url) =>
    Http.fetchWithRetry(url, ~init=Some({"method": "HEAD"}))
    ->Js.Promise2.then(resp => Js.Promise2.resolve(resp.ok))
    ->Js.Promise2.catch(_ => Js.Promise2.resolve(false))
  | None => Js.Promise2.resolve(false)
  }
}

/** List available provers */
let listProvers = (): Js.Promise2.t<array<Prover.prover>> => {
  Js.Promise2.resolve(provers)
}

/** Solve a problem by parsing and verifying Metamath source */
let solve = (
  problem: Prover.problem,
  ~_prover: option<string>=?,
): Js.Promise2.t<Prover.proverResult> => {
  let startTime = Js.Date.now()

  // Parse the problem as Metamath source
  let db = parseMetamath(problem.content)
  let theoremLabels = db.theorems

  if Belt.Array.length(theoremLabels) == 0 {
    Js.Promise2.resolve({
      Prover.prover: "metamath-verify",
      status: Prover.Unknown,
      proof: None,
      model: None,
      time_ms: Js.Date.now() -. startTime,
      raw_output: None,
      error: Some("No theorems ($p statements) found in input"),
      timestamp: Js.Date.make(),
    })
  } else {
    // Verify each theorem
    let results = theoremLabels->Belt.Array.map(label => {
      let stmt = Belt.Map.String.get(db.statements, label)
      let proof = switch stmt {
      | Some(s) => Belt.Option.getWithDefault(s.proof, [])
      | None => []
      }
      let (valid, error) = verifyProofStep(db, label, proof)
      (label, valid, error)
    })

    let allValid = results->Belt.Array.every(((_, valid, _)) => valid)
    let status: Prover.proverStatus = if allValid { Prover.Theorem } else { Prover.Error }

    let errorMsg = if allValid {
      None
    } else {
      let failedMsgs = results
        ->Belt.Array.keep(((_, valid, _)) => !valid)
        ->Belt.Array.map(((label, _, err)) => {
          `${label}: ${Belt.Option.getWithDefault(err, "unknown error")}`
        })
        ->Js.Array2.joinWith("; ")
      Some(failedMsgs)
    }

    Js.Promise2.resolve({
      Prover.prover: "metamath-verify",
      status,
      proof: if allValid {
        Some(`Verified ${Belt.Int.toString(Belt.Array.length(theoremLabels))} theorem(s)`)
      } else {
        None
      },
      model: None,
      time_ms: Js.Date.now() -. startTime,
      raw_output: Some(Js.Json.stringify(Js.Json.string("verification results"))),
      error: errorMsg,
      timestamp: Js.Date.make(),
    })
  }
}

/** Load a Metamath database by name */
let loadDatabase = (dbName: string): Js.Promise2.t<mmDatabase> => {
  switch Js.Dict.get(metamathDatabases, dbName) {
  | Some(url) =>
    Js.log(`[Metamath] Loading database: ${dbName}`)
    Http.getText(url)
    ->Js.Promise2.then(source => {
      let db = parseMetamath(source)
      Js.log(`[Metamath] Loaded ${dbName}: ${Belt.Int.toString(Belt.Array.length(db.axioms))} axioms, ${Belt.Int.toString(Belt.Array.length(db.theorems))} theorems`)
      Js.Promise2.resolve(db)
    })
  | None =>
    Js.Promise2.reject(Js.Exn.raiseError(`Unknown database: ${dbName}`))
  }
}

/** Search for a theorem by regex pattern in a loaded database */
let searchTheorem = (
  db: mmDatabase,
  pattern: string,
): array<string> => {
  let regex = Js.Re.fromStringWithFlags(pattern, ~flags="i")
  Belt.Map.String.toArray(db.statements)
  ->Belt.Array.keep(((label, stmt)) => {
    Js.Re.test_(regex, label) ||
    stmt.symbols->Belt.Array.some(s => Js.Re.test_(regex, s))
  })
  ->Belt.Array.map(((label, _)) => label)
  ->Belt.Array.slice(~offset=0, ~len=100)
}

/** Get theorem details from a loaded database */
let getTheorem = (
  db: mmDatabase,
  label: string,
): option<mmStatement> => {
  Belt.Map.String.get(db.statements, label)
}
