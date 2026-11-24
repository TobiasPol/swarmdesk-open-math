#!/usr/bin/env node
// Validates targets.json schema and cross-checks that every listed Spec, Helpers, README, and
// Proof/Lemma Lean file exists on disk and obeys naming & security invariants.
import { existsSync, readFileSync } from 'node:fs';
import { join } from 'node:path';
import { pathToFileURL } from 'node:url';
import { guardLeanSource } from './guard.mjs';

const SLUG_RE = /^[a-z0-9_]{3,48}$/;
const FILE_RE = /^Targets\/[A-Za-z0-9_]+(?:\/Lemmas\/[A-Za-z0-9_]+|\/Proof)\.lean$/;
const MOD_RE = /^Targets\.[A-Za-z0-9_.]+$/;
const HTTPS_RE = /^https:\/\/[^\s<>"]{4,200}$/;
const KINDS = new Set(['conjecture', 'bound', 'lemma']);

export function validateManifest(manifest, rootDir) {
  const errors = [];
  if (manifest?.problem !== 'open-math') errors.push('manifest.problem must be "open-math"');
  if (!Array.isArray(manifest?.targets) || manifest.targets.length === 0) {
    return { ok: false, errors: ['manifest.targets must be a non-empty array'] };
  }
  const names = new Set();
  const paths = new Set();
  const topNames = new Set(
    manifest.targets.filter((t) => t.kind !== 'lemma').map((t) => t.name),
  );
  for (const t of manifest.targets) {
    if (!SLUG_RE.test(t.name ?? '')) errors.push(`bad slug: ${t.name}`);
    if (names.has(t.name)) errors.push(`duplicate target name: ${t.name}`);
    names.add(t.name);
    if (!KINDS.has(t.kind)) errors.push(`bad kind for ${t.name}: ${t.kind}`);
    if (!FILE_RE.test(t.file_path ?? '')) errors.push(`bad file_path for ${t.name}: ${t.file_path}`);
    if (paths.has(t.file_path)) errors.push(`duplicate file_path: ${t.file_path}`);
    paths.add(t.file_path);
    if (!MOD_RE.test(t.spec_module ?? '') || !MOD_RE.test(t.proof_module ?? '')) {
      errors.push(`bad Lean module name for ${t.name}`);
    }
    if (!MOD_RE.test(t.statement_decl ?? '')) {
      errors.push(`bad statement_decl for ${t.name}`);
    }
    if (t.source_url && !HTTPS_RE.test(t.source_url)) {
      errors.push(`bad source_url for ${t.name}`);
    }
    if (t.kind === 'lemma' && !topNames.has(t.parent)) {
      errors.push(`lemma ${t.name} references unknown parent ${t.parent}`);
    }
    if (t.kind === 'bound') {
      if (t.direction !== 'maximize' && t.direction !== 'minimize') {
        errors.push(`bound ${t.name} needs direction maximize|minimize`);
      }
      if (typeof t.baseline_value !== 'number' || !Number.isFinite(t.baseline_value)) {
        errors.push(`bound ${t.name} needs finite baseline_value`);
      }
    }
    if (rootDir) {
      const targetFile = join(rootDir, t.file_path);
      const specFile = join(rootDir, t.dir, 'Spec.lean');
      const helpersFile = join(rootDir, t.dir, 'Helpers.lean');
      const readmeFile = join(rootDir, t.dir, 'README.md');
      for (const req of [targetFile, specFile, helpersFile, readmeFile]) {
        if (!existsSync(req)) errors.push(`missing file for ${t.name}: ${req}`);
      }
      if (existsSync(specFile)) {
        const specText = readFileSync(specFile, 'utf8');
        const declTail = t.statement_decl.split('.').at(-1);
        if (!new RegExp(`\\bdef\\s+${declTail}\\b`).test(specText)) {
          errors.push(`Spec.lean for ${t.name} does not define ${declTail}`);
        }
        if (/\b(sorry|admit|axiom)\b/.test(specText)) {
          errors.push(`Spec.lean for ${t.name} must not contain sorry, admit, or axiom`);
        }
      }
      if (existsSync(targetFile)) {
        const text = readFileSync(targetFile, 'utf8');
        const allowSorry = t.kind !== 'bound';
        const res = guardLeanSource(text, { allowSorry });
        if (!res.ok) errors.push(`guard failed on ${t.file_path}: ${res.refused}`);
      }
    }
  }
  return { ok: errors.length === 0, count: manifest.targets.length, errors };
}

if (import.meta.url === pathToFileURL(process.argv[1] ?? '').href) {
  const rootDir = process.argv[2] ?? process.cwd();
  const manifest = JSON.parse(readFileSync(join(rootDir, 'targets.json'), 'utf8'));
  const result = validateManifest(manifest, rootDir);
  console.log(JSON.stringify(result, null, 2));
  process.exit(result.ok ? 0 : 1);
}
