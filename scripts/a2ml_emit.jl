#!/usr/bin/env julia
# SPDX-License-Identifier: PMPL-1.0-or-later
# Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
#
# A2ML emitter for training-corpus records.
# A2ML is a TOML-flavored data language (per hyperpolymath No-JSON-Emit rule).
# This module provides minimal, dependency-free serialisation for the
# record shapes used by ECHIDNA's extract_*.jl scripts.
#
# Supported value types: String, Integer, Float, Bool, Vector{String},
# Vector{<:Integer}, Vector{<:AbstractFloat}, nothing (omitted).
# Nested tables are NOT supported here — records are flat.

module A2MLEmit

export escape_a2ml_string, emit_scalar, emit_kv, write_metadata_table,
       write_record, write_records_file

"""
    escape_a2ml_string(s) -> String

Escape a string for A2ML (TOML) basic-string context: backslash,
double-quote, control chars.
"""
function escape_a2ml_string(s::AbstractString)::String
    io = IOBuffer()
    for c in s
        if c == '\\'
            print(io, "\\\\")
        elseif c == '"'
            print(io, "\\\"")
        elseif c == '\n'
            print(io, "\\n")
        elseif c == '\r'
            print(io, "\\r")
        elseif c == '\t'
            print(io, "\\t")
        elseif c == '\b'
            print(io, "\\b")
        elseif c == '\f'
            print(io, "\\f")
        elseif UInt32(c) < 0x20
            print(io, "\\u", uppercase(string(UInt32(c); base=16, pad=4)))
        else
            print(io, c)
        end
    end
    return String(take!(io))
end

"""
    emit_scalar(v) -> String

Render a scalar value as an A2ML/TOML literal.
"""
function emit_scalar(v)::String
    if v === nothing
        return "\"\""                  # empty string sentinel
    elseif v isa Bool
        return v ? "true" : "false"
    elseif v isa Integer
        return string(v)
    elseif v isa AbstractFloat
        return isfinite(v) ? string(v) : "nan"
    elseif v isa AbstractString
        return "\"" * escape_a2ml_string(v) * "\""
    elseif v isa AbstractVector
        parts = [emit_scalar(x) for x in v]
        return "[" * join(parts, ", ") * "]"
    elseif v isa AbstractDict
        # Inline table
        parts = String[]
        for (kk, vv) in v
            push!(parts, string(kk) * " = " * emit_scalar(vv))
        end
        return "{" * join(parts, ", ") * "}"
    else
        # Fallback: stringify
        return "\"" * escape_a2ml_string(string(v)) * "\""
    end
end

"""
    emit_kv(io, key, value)

Write a single `key = value` line (omits keys whose value is `nothing`).
"""
function emit_kv(io::IO, key::AbstractString, value)
    value === nothing && return
    println(io, key, " = ", emit_scalar(value))
end

"""
    write_metadata_table(io, metadata::AbstractDict)

Write a `[metadata]` table.
"""
function write_metadata_table(io::IO, metadata::AbstractDict)
    println(io, "[metadata]")
    for (k, v) in metadata
        emit_kv(io, string(k), v)
    end
    println(io)
end

"""
    write_record(io, table_name, record::AbstractDict)

Write a `[[table_name]]` array-of-tables entry.
"""
function write_record(io::IO, table_name::AbstractString, record::AbstractDict)
    println(io, "[[", table_name, "]]")
    for (k, v) in record
        emit_kv(io, string(k), v)
    end
    println(io)
end

"""
    write_records_file(path, metadata, records, table_name; header=nothing)

Write a complete A2ML file with SPDX header, [metadata] block, and
array-of-tables `[[table_name]]` entries.
"""
function write_records_file(
    path::AbstractString,
    metadata::AbstractDict,
    records::AbstractVector,
    table_name::AbstractString;
    header::Union{AbstractString,Nothing}=nothing,
)
    open(path, "w") do io
        println(io, "# SPDX-License-Identifier: PMPL-1.0-or-later")
        println(io, "# Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath)")
        if header !== nothing
            for line in split(header, '\n')
                println(io, "# ", line)
            end
        end
        println(io)
        write_metadata_table(io, metadata)
        for rec in records
            write_record(io, table_name, rec)
        end
    end
end

end  # module
