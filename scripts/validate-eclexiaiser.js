#!/usr/bin/env bun
// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
//
// Structural check of eclexiaiser.toml for the dogfood-gate workflow. It
// replaces a python3 tomllib heredoc (python is banned estate-wide) and keeps
// its four rejections and messages. Usage: bun scripts/validate-eclexiaiser.js [path]

/** Returns true when `v` is a string with non-whitespace content. */
const filled = (v) => typeof v === "string" && v.trim() !== "";

/**
 * Validates eclexiaiser manifest text.
 * Returns { ok, message }: ok is false on a parse error, a blank or missing
 * project.name, no [[functions]] entry, or a function lacking name or source.
 */
export function validateEclexiaiser(text) {
  let data;
  try {
    data = Bun.TOML.parse(text);
  } catch (e) {
    return { ok: false, message: `ERROR: eclexiaiser.toml does not parse: ${e.message}` };
  }
  const project = data.project ?? {};
  if (!filled(project.name)) return { ok: false, message: "ERROR: project.name is required" };
  const functions = Array.isArray(data.functions) ? data.functions : [];
  if (functions.length === 0) {
    return { ok: false, message: "ERROR: at least one [[functions]] entry is required" };
  }
  for (const fn of functions) {
    if (!filled(fn.name)) return { ok: false, message: "ERROR: function name cannot be empty" };
    if (!filled(fn.source)) return { ok: false, message: `ERROR: function ${fn.name} has no source path` };
  }
  return { ok: true, message: `Valid: ${project.name} (${functions.length} function(s))` };
}

if (import.meta.main) {
  const path = process.argv[2] ?? "eclexiaiser.toml";
  const result = validateEclexiaiser(await Bun.file(path).text());
  (result.ok ? console.log : console.error)(result.message);
  process.exit(result.ok ? 0 : 1);
}
