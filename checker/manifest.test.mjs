import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { dirname, join } from 'node:path';
import { describe, it } from 'node:test';
import { fileURLToPath } from 'node:url';
import { validateManifest } from './manifest.mjs';
import { runReductionCheck } from './reduction-check.mjs';

const ROOT = join(dirname(fileURLToPath(import.meta.url)), '..');

function makeConjecture(name) {
  return {
    name,
    kind: 'conjecture',
    file_path: `Targets/Foo/Proof.lean`,
    spec_module: 'Targets.Foo.Spec',
    proof_module: 'Targets.Foo.Proof',
    statement_decl: 'Targets.Foo.Spec.Statement',
  };
}

function makeLemma(name, parent, depends_on) {
  return {
    name,
    kind: 'lemma',
    parent,
    ...(depends_on !== undefined ? { depends_on } : {}),
    file_path: `Targets/Foo/Lemmas/${name}.lean`,
    spec_module: 'Targets.Foo.Spec',
    proof_module: `Targets.Foo.Lemmas.${name}`,
    statement_decl: `Targets.Foo.Spec.Lemma${name}`,
  };
}

describe('targets.json manifest and DAG', () => {
  it('validates all 11 open problems and 12 blueprint helper lemmas on disk', () => {
    const manifest = JSON.parse(readFileSync(join(ROOT, 'targets.json'), 'utf8'));
    const res = validateManifest(manifest, ROOT);
    assert.equal(res.ok, true, `Manifest errors:\n${res.errors.join('\n')}`);
    assert.equal(res.count, 23);
    const top = manifest.targets.filter((t) => t.kind !== 'lemma');
    const conjectures = top.filter((t) => t.kind === 'conjecture');
    const bounds = top.filter((t) => t.kind === 'bound');
    const lemmas = manifest.targets.filter((t) => t.kind === 'lemma');
    assert.equal(top.length, 11);
    assert.equal(conjectures.length, 6);
    assert.equal(bounds.length, 5);
    assert.equal(lemmas.length, 12);

    const mod12 = lemmas.find((t) => t.name === 'erdos_straus_mod_12_eq_11');
    assert.deepEqual(mod12.depends_on, ['erdos_straus_even', 'erdos_straus_mod_4_eq_3']);
    const dist3 = lemmas.find((t) => t.name === 'erdos_7_distinct_moduli_ge_3');
    assert.deepEqual(dist3.depends_on, ['erdos_7_density_ge_one', 'erdos_7_lcm_reduction']);
  });

  it('passes reduction-check across all Spec.lean, Helpers.lean, and CertKit files', () => {
    const red = runReductionCheck(ROOT);
    assert.equal(red.ok, true, `Reduction errors:\n${red.errors.join('\n')}`);
    assert.equal(red.targets, 23);
    assert.ok(red.checked_specs >= 23);
  });

  it('rejects broken parent links and invalid kinds', () => {
    const bad = {
      problem: 'open-math',
      targets: [makeLemma('orphan_lemma', 'does_not_exist')],
    };
    const res = validateManifest(bad);
    assert.equal(res.ok, false);
    assert.ok(res.errors.some((e) => e.includes('unknown parent')));
  });

  it('accepts multi-level lemma parent chains when depends_on is present', () => {
    const okDag = {
      problem: 'open-math',
      targets: [
        makeConjecture('root_conj'),
        makeLemma('lem_a', 'root_conj'),
        makeLemma('lem_b', 'lem_a', ['lem_a']),
        makeLemma('lem_c', 'lem_b', ['lem_a', 'lem_b']),
      ],
    };
    const res = validateManifest(okDag);
    assert.equal(res.ok, true, `Unexpected errors: ${res.errors.join('\n')}`);
  });

  it('rejects lemma parent without depends_on, self-deps, unknown deps, and dependency cycles', () => {
    const noDeps = {
      problem: 'open-math',
      targets: [
        makeConjecture('root_conj'),
        makeLemma('lem_a', 'root_conj'),
        makeLemma('lem_b', 'lem_a'),
      ],
    };
    assert.equal(validateManifest(noDeps).ok, false);

    const selfDep = {
      problem: 'open-math',
      targets: [
        makeConjecture('root_conj'),
        makeLemma('lem_a', 'root_conj', ['lem_a']),
      ],
    };
    const selfRes = validateManifest(selfDep);
    assert.equal(selfRes.ok, false);
    assert.ok(selfRes.errors.some((e) => e.includes('self-dependency')));

    const unknownDep = {
      problem: 'open-math',
      targets: [
        makeConjecture('root_conj'),
        makeLemma('lem_a', 'root_conj', ['missing_slug']),
      ],
    };
    assert.equal(validateManifest(unknownDep).ok, false);

    const cycle = {
      problem: 'open-math',
      targets: [
        makeConjecture('root_conj'),
        makeLemma('lem_a', 'root_conj', ['lem_b']),
        makeLemma('lem_b', 'root_conj', ['lem_c']),
        makeLemma('lem_c', 'root_conj', ['lem_a']),
      ],
    };
    const cycleRes = validateManifest(cycle);
    assert.equal(cycleRes.ok, false);
    assert.ok(cycleRes.errors.some((e) => e.includes('dependency cycle')));

    const parentCycle = {
      problem: 'open-math',
      targets: [
        makeConjecture('root_conj'),
        makeLemma('lem_a', 'lem_b', ['root_conj']),
        makeLemma('lem_b', 'lem_a', ['root_conj']),
      ],
    };
    const pCycleRes = validateManifest(parentCycle);
    assert.equal(pCycleRes.ok, false);
    assert.ok(pCycleRes.errors.some((e) => e.includes('parent cycle')));
  });
});
