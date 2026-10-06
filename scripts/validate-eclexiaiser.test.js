// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
//
// Tests for scripts/validate-eclexiaiser.js — the four rejections the
// dogfood-gate eclexiaiser job enforced in its retired python3 heredoc, plus
// the valid case and the repo's own manifest. Run: bun test scripts/
import { describe, expect, test } from "bun:test";
import { validateEclexiaiser } from "./validate-eclexiaiser.js";

const VALID = `
[project]
name = "echidna"

[[functions]]
name = "scan"
source = "src/main.rs"
`;

describe("validateEclexiaiser", () => {
  test("accepts a manifest with a project name and a complete function", () => {
    expect(validateEclexiaiser(VALID)).toEqual({ ok: true, message: "Valid: echidna (1 function(s))" });
  });

  test("rejects a missing or blank project.name", () => {
    expect(validateEclexiaiser(`[project]\nname = "  "\n[[functions]]\nname="a"\nsource="b"\n`))
      .toEqual({ ok: false, message: "ERROR: project.name is required" });
    expect(validateEclexiaiser(`[[functions]]\nname="a"\nsource="b"\n`))
      .toEqual({ ok: false, message: "ERROR: project.name is required" });
  });

  test("rejects a manifest with no [[functions]] entry", () => {
    expect(validateEclexiaiser(`[project]\nname = "x"\n`))
      .toEqual({ ok: false, message: "ERROR: at least one [[functions]] entry is required" });
  });

  test("rejects a function with a blank name", () => {
    expect(validateEclexiaiser(`[project]\nname="x"\n[[functions]]\nname=""\nsource="b"\n`))
      .toEqual({ ok: false, message: "ERROR: function name cannot be empty" });
  });

  test("rejects a function with no source path", () => {
    expect(validateEclexiaiser(`[project]\nname="x"\n[[functions]]\nname="scan"\n`))
      .toEqual({ ok: false, message: "ERROR: function scan has no source path" });
  });

  test("rejects TOML that does not parse, without throwing", () => {
    const r = validateEclexiaiser(`[project\nname = `);
    expect(r.ok).toBe(false);
    expect(r.message).toStartWith("ERROR: eclexiaiser.toml does not parse:");
  });

  test("the repo's own eclexiaiser.toml is valid", async () => {
    const text = await Bun.file(new URL("../eclexiaiser.toml", import.meta.url)).text();
    expect(validateEclexiaiser(text).ok).toBe(true);
  });
});
