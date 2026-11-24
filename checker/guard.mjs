#!/usr/bin/env node
// Fast, zero-dependency syntax and anti-injection guard for submitted Lean 4 proof files.
// Runs BEFORE Mathlib is downloaded or Lean is invoked so spam, prompt injections, sorry stubs,
// and metaprogramming exploits fail in milliseconds.
//
//   node checker/guard.mjs <file.lean>
//
// Exit 0: prints {"ok": true, "lines": <n>}. Exit 1: prints {"refused": "<reason>"}.
import { readFileSync } from 'node:fs';
import { pathToFileURL } from 'node:url';

export const MAX_BYTES = 512 * 1024;
export const MAX_LINES = 8000;
export const MAX_IDENT_LEN = 64;

const FORBIDDEN_KEYWORDS = new Set([
  'sorry',
  'admit',
  'axiom',
  'opaque',
  'unsafe',
  'partial',
  'native_decide',
  'macro',
  'macro_rules',
  'elab',
  'elab_rules',
  'syntax',
  'declare_syntax_cat',
  'initialize',
  'builtin_initialize',
  'run_cmd',
  'set_option',
  'local_macro',
  'scoped_macro',
  'implemented_by',
  'extern',
  'csimp',
  'env_extension',
]);

const FORBIDDEN_HASH_COMMANDS = /^#(eval|print|check|reduce|synth|guard|exit|align|help)\b/;
const FORBIDDEN_IMPORT_RE =
  /^\s*import\s+(Lean|Lake|Init\.System|Std\.Internal\.IO|Mathlib\.Tactic\.RunCmd)\b/m;
const FORBIDDEN_ATTR_RE =
  /@\[[^\]]*\b(extern|implemented_by|csimp|macro|elab|builtin_macro|builtin_elab|init|export)\b/;
const CONTROL_CHAR_RE = /[\u0000-\u0008\u000B\u000C\u000E-\u001F\u007F\u200B-\u200F\u202A-\u202E\u2066-\u2069\uFEFF]/;

export function guardLeanSource(source, { allowSorry = false } = {}) {
  if (typeof source !== 'string' || source.length === 0) {
    return { ok: false, refused: 'the Lean file is empty' };
  }
  const bytes = Buffer.byteLength(source, 'utf8');
  if (bytes > MAX_BYTES) {
    return { ok: false, refused: `the file exceeds ${MAX_BYTES} bytes` };
  }
  if (CONTROL_CHAR_RE.test(source)) {
    return { ok: false, refused: 'control or invisible bidirectional characters are not allowed' };
  }
  const lines = source.split(/\r?\n/);
  if (lines.length > MAX_LINES) {
    return { ok: false, refused: `the file exceeds ${MAX_LINES} lines` };
  }
  if (source.includes('--') || source.includes('/-') || source.includes('-/')) {
    return { ok: false, refused: 'comments (-- or /- -/) are not allowed in submitted proof files' };
  }
  if (source.includes('"')) {
    return { ok: false, refused: 'string literals are not allowed in submitted proof files' };
  }
  if (source.includes('«') || source.includes('»')) {
    return { ok: false, refused: 'escaped guillemet identifiers («...») are not allowed' };
  }
  if (FORBIDDEN_IMPORT_RE.test(source)) {
    return { ok: false, refused: 'importing Lean compiler, Lake, or system IO modules is not allowed' };
  }
  if (FORBIDDEN_ATTR_RE.test(source)) {
    return { ok: false, refused: 'compiler/FFI/metaprogramming attributes (@[extern], @[implemented_by], etc.) are not allowed' };
  }
  for (const rawLine of lines) {
    const trimmed = rawLine.trim();
    if (FORBIDDEN_HASH_COMMANDS.test(trimmed)) {
      return { ok: false, refused: `command ${trimmed.split(/\s+/)[0]} is not allowed` };
    }
    if (trimmed.includes('Lean.ofReduceBool') || trimmed.includes('Lean.trustCompiler')) {
      return { ok: false, refused: 'compiler-trust axioms are not allowed' };
    }
  }
  // Scan identifier tokens for forbidden keywords and oversized prompt-smuggling identifiers.
  const tokens = source.match(/[A-Za-z_][A-Za-z0-9_'.]*/g) ?? [];
  for (const tok of tokens) {
    for (const part of tok.split('.')) {
      if (!part) continue;
      if (part.length > MAX_IDENT_LEN) {
        return { ok: false, refused: `identifier exceeds ${MAX_IDENT_LEN} characters` };
      }
      if (FORBIDDEN_KEYWORDS.has(part)) {
        if (allowSorry && part === 'sorry') continue;
        return { ok: false, refused: `forbidden Lean construct: ${part}` };
      }
    }
  }
  return { ok: true, lines: lines.filter((l) => l.trim().length > 0).length };
}

if (import.meta.url === pathToFileURL(process.argv[1] ?? '').href) {
  const file = process.argv[2];
  const allowSorry = process.argv.includes('--allow-sorry');
  if (!file) {
    console.error('usage: guard.mjs <file.lean> [--allow-sorry]');
    process.exit(3);
  }
  const result = guardLeanSource(readFileSync(file, 'utf8'), { allowSorry });
  console.log(JSON.stringify(result));
  process.exit(result.ok ? 0 : 1);
}
