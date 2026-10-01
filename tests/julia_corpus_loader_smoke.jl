# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
# SPDX-License-Identifier: MPL-2.0
#
# Smoke test: synthesise a 3-row Corpus JSON in /tmp, run
# CorpusLoader.corpus_to_training_examples, assert the disciplines
# field arrives populated. Backs the post-wave3 wiring PR — protects
# against regression where `discipline:<tag>` strings get silently
# dropped on the load path.

using Test
include("../src/julia/corpus_loader.jl"); using .CorpusLoader

@testset "saturation discipline tags survive load_corpus_examples" begin
    json_path = tempname() * ".json"
    write(json_path, """
    {
      "adapter": "agda",
      "entries": [{
        "name": "wf-<",
        "qualified": "Ordinal.Brouwer.wf-<",
        "statement": "linear Pi (n : Nat) -> Vec n A",
        "proof": "by induction",
        "axiom_usage": {
          "other": ["discipline:linear", "discipline:dependent"]
        }
      }],
      "modules": [],
      "by_name": {},
      "by_qualified": {},
      "dependents": {}
    }
    """)
    corpus = CorpusLoader.load_corpus_json(json_path)
    rows = CorpusLoader.corpus_to_training_examples(corpus, :agda)
    @test length(rows) == 1
    @test :linear in rows[1].disciplines
    @test :dependent in rows[1].disciplines
end
