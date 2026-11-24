import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { dirname, join } from 'node:path';
import { describe, it } from 'node:test';
import { fileURLToPath } from 'node:url';
import { validateManifest } from './manifest.mjs';

const ROOT = join(dirname(fileURLToPath(import.meta.url)), '..');

describe('targets.json manifest', () => {
  it('validates all 10 open problems and 10 blueprint helper lemmas on disk', () => {
    const manifest = JSON.parse(readFileSync(join(ROOT, 'targets.json'), 'utf8'));
    const res = validateManifest(manifest, ROOT);
    assert.equal(res.ok, true, `Manifest errors:\n${res.errors.join('\n')}`);
    assert.equal(res.count, 20);
    const top = manifest.targets.filter((t) => t.kind !== 'lemma');
    const conjectures = top.filter((t) => t.kind === 'conjecture');
    const bounds = top.filter((t) => t.kind === 'bound');
    const lemmas = manifest.targets.filter((t) => t.kind === 'lemma');
    assert.equal(top.length, 10);
    assert.equal(conjectures.length, 6);
    assert.equal(bounds.length, 4);
    assert.equal(lemmas.length, 10);
  });

  it('rejects broken parent links and invalid kinds', () => {
    const bad = {
      problem: 'open-math',
      targets: [
        {
          name: 'orphan_lemma',
          kind: 'lemma',
          parent: 'does_not_exist',
          file_path: 'Targets/Foo/Lemmas/Bar.lean',
          spec_module: 'Targets.Foo.Spec',
          proof_module: 'Targets.Foo.Lemmas.Bar',
          statement_decl: 'Targets.Foo.Spec.LemmaBar',
        },
      ],
    };
    const res = validateManifest(bad);
    assert.equal(res.ok, false);
    assert.ok(res.errors.some((e) => e.includes('unknown parent')));
  });
});
