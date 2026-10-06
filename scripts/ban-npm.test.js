// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
//
// Planted-fixture tests for scripts/ban-npm.sh: each banned artefact is placed
// in a scratch tree and the script must exit 1; the clean tree must exit 0.
// Run: bun test scripts/
import { afterEach, expect, test } from "bun:test";
import { cpSync, mkdirSync, mkdtempSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { dirname, join } from "node:path";

const SCRIPT = new URL("./ban-npm.sh", import.meta.url).pathname;
const trees = [];

/** Builds a scratch tree holding the script plus `files` (path → content) and returns its exit code. */
function runIn(files) {
  const root = mkdtempSync(join(tmpdir(), "ban-npm-"));
  trees.push(root);
  mkdirSync(join(root, "scripts"));
  cpSync(SCRIPT, join(root, "scripts", "ban-npm.sh"));
  for (const [path, content] of Object.entries(files)) {
    mkdirSync(dirname(join(root, path)), { recursive: true });
    writeFileSync(join(root, path), content);
  }
  return Bun.spawnSync(["bash", "scripts/ban-npm.sh"], { cwd: root, stdout: "pipe", stderr: "pipe" }).exitCode;
}

afterEach(() => { while (trees.length) rmSync(trees.pop(), { recursive: true, force: true }); });

test("a clean tree passes", () => expect(runIn({ "README.adoc": "x\n" })).toBe(0));
test("package-lock.json fails", () => expect(runIn({ "package-lock.json": "{}" })).toBe(1));
test("a root deno.json fails", () => expect(runIn({ "deno.json": "{}" })).toBe(1));
test("a nested deno.lock fails", () => expect(runIn({ "sub/app/deno.lock": "{}" })).toBe(1));
test("a deno.jsonc fails", () => expect(runIn({ "tools/deno.jsonc": "{}" })).toBe(1));
