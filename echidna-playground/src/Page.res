// SPDX-License-Identifier: AGPL-3.0-or-later
// SPDX-FileCopyrightText: 2025 Coq-Jr Contributors

// Page renderer for jsCoq

open Components

let jscoqName = JsCoqName.render()

let welcomeSection = (): string => {
  Html.div([
    Html.h3([`Welcome to the ${jscoqName} Interactive Online System!`]),
    Html.p([
      `Welcome to the ${jscoqName} technology demo! `,
      `${jscoqName} is an interactive, `,
      `web-based environment for the Coq Theorem prover, and is a collaborative `,
      `development effort. See the `,
      Html.a(~href="#team", "list of contributors"),
      ` below.`,
    ]),
    Html.p([
      `${jscoqName} is open source. If you find any problem or want to make `,
      `any contribution, you are extremely welcome! We await your `,
      `feedback at `,
      Html.a(~href="https://github.com/jscoq/jscoq", "GitHub"),
      ` and `,
      Html.a(~href="https://gitter.im/jscoq/Lobby", "Gitter"),
      `.`,
    ]),
  ])
}

let instructionsSection = (): string => {
  Html.div([
    Html.h4(["Instructions:"]),
    Html.p([
      `The following document contains embedded Coq code. `,
      `All the code is editable and can be run directly on the page. `,
      `Once ${jscoqName} finishes loading, you are `,
      `free to experiment by stepping through the proof and viewing intermediate `,
      `proof states on the right panel.`,
    ]),
    Html.h5(["Actions:"]),
    ActionTable.render(),
    Html.h5(["Saving your own proof scripts:"]),
    Html.p([
      `The `,
      Html.a(~href="scratchpad.html", "scratchpad"),
      ` offers simple, local storage functionality. `,
      `Please go to `,
      Html.a(~href="https://x80.org/collacoq/", "CollaCoq"),
      ` if you want to share your developments with other users.`,
    ]),
  ])
}

let primeExampleSection = (): string => {
  Html.div([
    Html.h4(["A First Example: The Infinitude of Primes"]),
    Html.p([
      `We don't provide a Coq tutorial (yet), but as a showcase, we `,
      `display a proof of the infinitude of primes in Coq. The proof relies `,
      `in the Mathematical Components library by the `,
      Html.a(~href="http://ssr.msr-inria.inria.fr/", "MSR/Inria"),
      ` team led by Georges Gonthier, so our first step will be to load it and `,
      `set a few Coq options:`,
    ]),
    Html.textarea(~id="addnC", CodeExamples.imports),
    Html.h5(["Ready to do Proofs!"]),
    Html.p([
      `Once the basic environment has been set up, we can proceed to the proof:`,
    ]),
    Html.textarea(~id="prime_above1", CodeExamples.primeAbove1),
    Html.p([
      `The lemma states that for any number ${Html.code("m")}, `,
      `there is a prime number larger than ${Html.code("m")}. `,
      `Coq is a ${Html.em("constructive system")}, which among other things `,
      `implies that to show the existence of an object, we need to `,
      `actually provide an algorithm that will construct it. `,
      `In this case, we need to find a prime number ${Html.code("p")} `,
      `that is greater than ${Html.code("m")}. `,
      `What would be a suitable ${Html.code("p")}? `,
      `Choosing ${Html.code("p")} to be the first prime divisor of ${Html.code("m! + 1")} works. `,
      `As we will shortly see, properties of divisibility will imply that `,
      `${Html.code("p")} must be greater than ${Html.code("m")}.`,
    ]),
    Html.textarea(~id="prime_above2", CodeExamples.primeAbove2),
    Html.p([
      `Our first step is thus to use the library-provided lemma `,
      `${Html.code("pdivP")}, which states that every number is divided by a `,
      `prime. Thus, we obtain a number ${Html.code("p")} and the corresponding `,
      `hypotheses ${Html.code("pr_p : prime p")} and ${Html.code("p_dv_m1")}, `,
      `"p divides m! + 1". `,
      `The ssreflect tactic ${Html.code("have")} provides a convenient way to `,
      `instantiate this lemma and discard the side proof obligation `,
      `${Html.code("1 < m! + 1")}.`,
    ]),
    Html.textarea(~id="prime_above3", CodeExamples.primeAbove3),
    Html.p([
      `It remains to prove that ${Html.code("p")} is greater than ${Html.code("m")}. We reason by `,
      `contraposition with the divisibility hypothesis, which gives us `,
      `the goal "if ${Html.code("p ≤ m")} then ${Html.code("p")} is not a prime divisor of " `,
      `${Html.code("m! + 1")}.`,
    ]),
    Html.textarea(~id="prime_above4", CodeExamples.primeAbove4),
    Html.p([
      `The goal follows from basic properties of divisibility, plus `,
      `from the fact that if ${Html.code("p ≤ m")}, then ${Html.code("p")} divides `,
      `${Html.code("m!")}, so that for ${Html.code("p")} to divide `,
      `${Html.code("m! + 1")} it must also divide 1, `,
      `in contradiction to ${Html.code("p")} being prime.`,
    ]),
    Html.hr(),
    Html.p([
      `${jscoqName} provides many other packages, `,
      `including Coq's standard library and the `,
      Html.a(~href="https://math-comp.github.io", "mathematical components"),
      ` library. `,
      `Feel free to experiment, and bear with the beta status of this demo.`,
    ]),
    Html.p([Html.i("¡Salut!")]),
  ])
}

let documentContent = (): string => {
  Html.div(~id="document", [
    welcomeSection(),
    instructionsSection(),
    primeExampleSection(),
    TeamSection.render(),
  ])
}

let jscoqScript = (): string => {
  let ids = Js.Array2.joinWith(Js.Array2.map(CodeExamples.codeIds, id => `'${id}'`), ", ")
  `
  <script src="node_modules/jscoq/ui-js/jscoq-loader.js" type="text/javascript"></script>
  <script type="text/javascript">
    var jscoq_ids = [${ids}];
    var jscoq_opts = {
      implicit_libs: false,
      focus: false,
      editor: { mode: { 'company-coq': true }, keyMap: 'default' },
      init_pkgs: ['init'],
      all_pkgs: ['coq', 'mathcomp']
    };

    var coq;
    JsCoq.start(jscoq_ids, jscoq_opts).then(res => coq = res);
  </script>`
}

let render = (): string => {
  `<!DOCTYPE html>
<html xmlns="http://www.w3.org/1999/xhtml">
  <head>
    <meta http-equiv="content-type" content="text/html;charset=utf-8" />
    <meta name="description" content="An Online IDE for the Coq Theorem Prover" />
    <link rel="icon" href="ui-images/favicon.ico">
    <link rel="stylesheet" type="text/css" href="node_modules/bootstrap/dist/css/bootstrap.min.css">
    <link rel="stylesheet" type="text/css" href="styles.css">
    <title>jsCoq – Use Coq in Your Browser</title>
  </head>
  <body class="jscoq-main">
    <div id="ide-wrapper" class="toggled">
      <div id="code-wrapper">
        ${documentContent()}
      </div>
    </div>
    ${jscoqScript()}
  </body>
</html>`
}
