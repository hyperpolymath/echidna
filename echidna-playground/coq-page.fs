\ SPDX-License-Identifier: AGPL-3.0-or-later
\ SPDX-FileCopyrightText: 2025 Coq-Jr Contributors

\ jsCoq page generator for estate-ssg

\ Helper words for HTML generation
: <tag>   ( addr u -- ) ." <" type ." >" ;
: </tag>  ( addr u -- ) ." </" type ." >" ;
: <tag/>  ( addr u -- ) ." <" type ." />" ;

: attr    ( val-addr val-u name-addr name-u -- )
  ."  " type ." =\"" type ." \"" ;

: .class  ( addr u -- ) s" class" attr ;
: .id     ( addr u -- ) s" id" attr ;
: .href   ( addr u -- ) s" href" attr ;

\ Semantic HTML helpers
: <div    s" div" <tag> ;
: </div>  s" div" </tag> ;
: <span   s" span" <tag> ;
: </span> s" span" </tag> ;
: <p>     s" p" <tag> ;
: </p>    s" p" </tag> ;
: <h3>    s" h3" <tag> ;
: </h3>   s" h3" </tag> ;
: <h4>    s" h4" <tag> ;
: </h4>   s" h4" </tag> ;
: <h5>    s" h5" <tag> ;
: </h5>   s" h5" </tag> ;
: <ul>    s" ul" <tag> ;
: </ul>   s" ul" </tag> ;
: <li>    s" li" <tag> ;
: </li>   s" li" </tag> ;
: <hr>    s" hr" <tag/> ;
: <br>    s" br" <tag/> ;
: <em>    s" em" <tag> ;
: </em>   s" em" </tag> ;
: <code>  s" code" <tag> ;
: </code> s" code" </tag> ;
: <kbd>   s" kbd" <tag> ;
: </kbd>  s" kbd" </tag> ;

: <textarea ( id-addr id-u -- )
  ." <textarea" s" id" attr ." >" ;
: </textarea> ." </textarea>" ;

: <a ( href-addr href-u -- )
  ." <a" s" href" attr ." >" ;
: </a> ." </a>" ;

\ jsCoq name styling
: jscoq-name
  ." <span class=\"jscoq-name\">jsCoq</span>" ;

\ Coq code examples
: coq-imports
  s" addnC" <textarea
  ." From Coq Require Import ssreflect ssrfun ssrbool." cr
  ." From mathcomp Require Import eqtype ssrnat div prime."
  </textarea> ;

: coq-lemma
  s" prime_above1" <textarea
  ." (* A nice proof of the infinitude of primes, by Georges Gonthier *)" cr
  ." Lemma prime_above m : {p | m < p & prime p}." cr
  ." Proof."
  </textarea> ;

: coq-step1
  s" prime_above2" <textarea
  ." have /pdivP[p pr_p p_dv_m1]: 1 < m`! + 1" cr
  ."   by rewrite addn1 ltnS fact_gt0."
  </textarea> ;

: coq-step2
  s" prime_above3" <textarea
  ." exists p => //; rewrite ltnNge; apply: contraL p_dv_m1 => p_le_m."
  </textarea> ;

: coq-step3
  s" prime_above4" <textarea
  ." by rewrite dvdn_addr ?dvdn_fact ?prime_gt0 // gtnNdvd ?prime_gt1." cr
  ." Qed."
  </textarea> ;

\ Page sections
: welcome-section
  <div
    <h3> ." Welcome to the " jscoq-name ."  Interactive Online System!" </h3>
    <p>
      ." Welcome to the " jscoq-name ."  technology demo! "
      jscoq-name ."  is an interactive, web-based environment for the "
      ." Coq Theorem prover, and is a collaborative development effort. "
      ." See the " s" #team" <a ." list of contributors" </a> ."  below."
    </p>
    <p>
      jscoq-name ."  is open source. If you find any problem or want to make "
      ." any contribution, you are extremely welcome! We await your feedback at "
      s" https://github.com/jscoq/jscoq" <a ." GitHub" </a> ."  and "
      s" https://gitter.im/jscoq/Lobby" <a ." Gitter" </a> ." ."
    </p>
  </div> ;

: instructions-section
  <div
    <h4> ." Instructions:" </h4>
    <p>
      ." The following document contains embedded Coq code. "
      ." All the code is editable and can be run directly on the page. "
      ." Once " jscoq-name ."  finishes loading, you are free to experiment "
      ." by stepping through the proof and viewing intermediate proof states "
      ." on the right panel."
    </p>
    <h5> ." Actions:" </h5>
    ." <table class=\"doc-actions\">"
      ." <tr><th>Key binding</th><th>Action</th></tr>"
      ." <tr><td><kbd>Alt</kbd>+<kbd>↓</kbd>/<kbd>↑</kbd></td>"
      ." <td>Move through the proof.</td></tr>"
      ." <tr><td><kbd>Alt</kbd>+<kbd>Enter</kbd></td>"
      ." <td>Run to current point.</td></tr>"
      ." <tr><td><kbd>F8</kbd></td>"
      ." <td>Toggle goal panel.</td></tr>"
    ." </table>"
  </div> ;

: prime-example-section
  <div
    <h4> ." A First Example: The Infinitude of Primes" </h4>
    <p>
      ." We display a proof of the infinitude of primes in Coq, using "
      ." Georges Gonthier's approach from the Mathematical Components library."
    </p>
    coq-imports
    <h5> ." Ready to do Proofs!" </h5>
    <p> ." Once the environment is set up, we proceed to the proof:" </p>
    coq-lemma
    <p>
      ." The lemma states that for any number " <code> ." m" </code> ." , "
      ." there is a prime number larger than " <code> ." m" </code> ." ."
    </p>
    coq-step1
    coq-step2
    coq-step3
    <hr>
    <p> <em> ." ¡Salut!" </em> </p>
  </div> ;

: team-section
  ." <div id=\"team\">"
    ." <a name=\"team\"></a>"
    <p> <em> ." The dev team" </em> </p>
    <ul>
      <li> s" https://www.irif.fr/~gallego/" <a
           ." Emilio Jesús Gallego Arias" </a> ."  (Inria, IRIF)" </li>
      <li> s" https://www.cs.technion.ac.il/~shachari/" <a
           ." Shachar Itzhaky" </a> ."  (Technion)" </li>
    </ul>
    <p> <em> ." Contributors" </em> </p>
    <ul>
      <li> ." Benoît Pin (CRI, MINES ParisTech)" </li>
    </ul>
  </div> ;

: jscoq-script
  ." <script src=\"node_modules/jscoq/ui-js/jscoq-loader.js\"></script>" cr
  ." <script>" cr
  ."   var jscoq_ids = ['addnC', 'prime_above1', 'prime_above2', 'prime_above3', 'prime_above4'];" cr
  ."   var jscoq_opts = {" cr
  ."     implicit_libs: false, focus: false," cr
  ."     editor: { mode: { 'company-coq': true }, keyMap: 'default' }," cr
  ."     init_pkgs: ['init'], all_pkgs: ['coq', 'mathcomp']" cr
  ."   };" cr
  ."   JsCoq.start(jscoq_ids, jscoq_opts);" cr
  ." </script>" ;

\ Main page generator
: coq-page ( -- )
  ." <!DOCTYPE html>" cr
  ." <html xmlns=\"http://www.w3.org/1999/xhtml\">" cr
  ." <head>" cr
  ."   <meta charset=\"utf-8\">" cr
  ."   <meta name=\"description\" content=\"An Online IDE for the Coq Theorem Prover\">" cr
  ."   <link rel=\"stylesheet\" href=\"styles.css\">" cr
  ."   <title>jsCoq – Use Coq in Your Browser</title>" cr
  ." </head>" cr
  ." <body class=\"jscoq-main\">" cr
  ."   <div id=\"ide-wrapper\" class=\"toggled\">" cr
  ."     <div id=\"code-wrapper\">" cr
  ."       <div id=\"document\">" cr
          welcome-section cr
          instructions-section cr
          prime-example-section cr
          team-section cr
  ."       </div>" cr
  ."     </div>" cr
  ."   </div>" cr
  jscoq-script cr
  ." </body>" cr
  ." </html>" ;

\ estate-ssg integration
: build-coq-page ( -- )
  s" output/index.html" w/o create-file throw
  dup >r
  ['] coq-page r@ outfile-execute
  r> close-file throw ;

\ For interactive testing
: preview coq-page ;
