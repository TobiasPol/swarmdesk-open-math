#!/usr/bin/env node
// Validates the targets.json multi-level lemma DAG and verifies that all trusted Spec.lean,
// Helpers.lean, and CertKit/*.lean files on disk are imported cleanly and contain no
// sorry/admit/axiom/compiler-trust cheats.
//
//   node checker/reduction-check.mjs [rootDir]
import { existsSync, readdirSync, readFileSync } from 'node:fs';
import { join, relative } from 'node:path';
import { pathToFileURL } from 'node:url';
import { validateManifest } from './manifest.mjs';

const FORBIDDEN_TRUSTED_RE =
  /\b(sorry|admit|axiom|native_decide|decide_cbv|unsafe|partial|implemented_by|extern)\b|Lean\.ofReduceBool|Lean\.trustCompiler/;

function walkLeanFiles(dir, out = []) {
  if (!existsSync(dir)) return out;
  for (const entry of readdirSync(dir, { withFileTypes: true })) {
    const full = join(dir, entry.name);
    if (entry.isDirectory()) {
      walkLeanFiles(full, out);
    } else if (entry.isFile() && entry.name.endsWith('.lean')) {
      out.push(full);
    }
  }
  return out;
}

function stripLeanComments(src) {
  // Strip line comments and nested block comments before scanning for forbidden tokens in Spec/Helpers/CertKit.
  let out = '';
  let i = 0;
  let depth = 0;
  while (i < src.length) {
    if (depth === 0 && src[i] === '-' && src[i + 1] === '-') {
      while (i < src.length && src[i] !== '\n') i += 1;
      continue;
    }
    if (src[i] === '/' && src[i + 1] === '-') {
      depth += 1;
      i += 2;
      continue;
    }
    if (depth > 0 && src[i] === '-' && src[i + 1] === '/') {
      depth -= 1;
      i += 2;
      continue;
    }
    if (depth === 0) out += src[i];
    i += 1;
  }
  return out;
}

export function runReductionCheck(rootDir) {
  const manifestPath = join(rootDir, 'targets.json');
  const manifest = JSON.parse(readFileSync(manifestPath, 'utf8'));
  const manifestRes = validateManifest(manifest, rootDir);
  const errors = [...manifestRes.errors];

  const targetsDir = join(rootDir, 'Targets');
  const trustedFiles = walkLeanFiles(targetsDir).filter((p) => {
    const rel = relative(rootDir, p).replace(/\\/g, '/');
    return (
      rel.endsWith('/Spec.lean') ||
      rel.endsWith('/Helpers.lean') ||
      rel.startsWith('Targets/CertKit/')
    );
  });

  for (const file of trustedFiles) {
    const rel = relative(rootDir, file).replace(/\\/g, '/');
    const code = stripLeanComments(readFileSync(file, 'utf8'));
    const match = FORBIDDEN_TRUSTED_RE.exec(code);
    if (match) {
      errors.push(`trusted file ${rel} contains forbidden construct: ${match[0]}`);
    }
  }

  const targetsLeanPath = join(rootDir, 'Targets.lean');
  if (!existsSync(targetsLeanPath)) {
    errors.push('missing Targets.lean');
  } else {
    const targetsLean = readFileSync(targetsLeanPath, 'utf8');
    const expectedModules = new Set();
    for (const t of manifest.targets ?? []) {
      if (t.spec_module) {
        expectedModules.add(t.spec_module);
        expectedModules.add(`${t.spec_module.replace(/\.Spec$/, '')}.Helpers`);
      }
    }
    if (existsSync(join(rootDir, 'Targets/CertKit/Lrat.lean'))) {
      expectedModules.add('Targets.CertKit.Lrat');
    }
    for (const mod of expectedModules) {
      const re = new RegExp(`^\\s*import\\s+${mod.replace(/\./g, '\\.')}\\s*$`, 'm');
      if (!re.test(targetsLean)) {
        errors.push(`Targets.lean is missing import ${mod}`);
      }
    }
  }

  return {
    ok: errors.length === 0,
    targets: manifest.targets?.length ?? 0,
    checked_specs: trustedFiles.length,
    errors,
  };
}

if (import.meta.url === pathToFileURL(process.argv[1] ?? '').href) {
  const rootDir = process.argv[2] ?? process.cwd();
  const result = runReductionCheck(rootDir);
  console.log(JSON.stringify(result, null, 2));
  process.exit(result.ok ? 0 : 1);
}
