#!/usr/bin/env julia
# SPDX-License-Identifier: PMPL-1.0-or-later
# Extract SeaHorn LLVM-based verification problems (CHC-encoded).
# Vendor: git clone https://github.com/seahorn/seahorn external_corpora/seahorn
using JSON3, Dates
include("extractor_save_common.jl")
const DIR = "external_corpora/seahorn"; const OUT = "training_data"; const START_ID = 2_200_000
function run_extract()
    ps, ts, pm = Dict{String,Any}[], Dict{String,Any}[], Dict{String,Any}[]; id = START_ID
    if !isdir(DIR); println("SeaHorn not found: $DIR"); println("Clone: git clone https://github.com/seahorn/seahorn external_corpora/seahorn"); return ps, ts, pm; end
    c_files = String[]
    for (root, _, fs) in walkdir(DIR); for f in fs; (endswith(f, ".c") || endswith(f, ".ll") || endswith(f, ".i")) && push!(c_files, joinpath(root, f)); end; end
    println("Found $(length(c_files)) SeaHorn input files")
    # Widening (2026-04-18): original pattern picked up only 4 keyword
    # variants. SV-COMP / SeaHorn C code in practice uses a much wider
    # vocabulary: assert, __VERIFIER_assume, __VERIFIER_nondet_{int,
    # uint,bool,char,short,long,ushort,ulong,uchar,float,double},
    # assume_abort_if_not, __CPROVER_assert, __CPROVER_assume,
    # klee_assert, klee_assume, ldv_assert. Also pick up `extern
    # __VERIFIER_*` declarations so the context field is populated.
    pat = r"(sassert|assert|assume|verifier_error|__VERIFIER_assert|__VERIFIER_assume|__VERIFIER_nondet_\w+|__CPROVER_assert|__CPROVER_assume|assume_abort_if_not|klee_assert|klee_assume|ldv_assert)\s*\(\s*(.+?)\s*\)"s
    for f in c_files
        c = try
            read(f, String)
        catch
            continue
        end
        matches = try
            collect(eachmatch(pat, c))
        catch
            Any[]
        end
        rel = relpath(f, DIR)
        for m in matches
            kind = m.captures[1]
            body = first(strip(m.captures[2]), 1000)
            # Skip pure declarations (no call args) and empty goals.
            isempty(body) && continue
            push!(ps, Dict{String,Any}("id"=>id, "prover"=>"SeaHorn",
                "source_file"=>rel,
                "theorem"=>"$(kind)_$(id)", "goal"=>body,
                "annotation_kind"=>kind, "context"=>Any[]))
            # Emit premises: C identifiers from assertion body
            for hm in eachmatch(r"\b([a-zA-Z_][a-zA-Z0-9_]{1,40})\b", body)
                h = strip(hm.captures[1])
                !isempty(h) && length(h) < 50 && push!(pm, Dict{String,Any}(
                    "proof_id"=>id, "premise"=>h,
                    "prover"=>"SeaHorn", "theorem"=>"$(kind)_$(id)", "source"=>"seahorn"))
            end
            id += 1
        end
    end
    ps, ts, pm
end
function main(); println("ECHIDNA SeaHorn Extraction"); println("=" ^ 26)
    ps, ts, pm = run_extract()
    isempty(ps) ? println("No assertions extracted.") : save_common(ps, ts, pm, "seahorn", START_ID, OUT) end
if abspath(PROGRAM_FILE) == @__FILE__; main(); end
