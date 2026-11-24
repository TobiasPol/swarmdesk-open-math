import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { dirname, join } from 'node:path';
import { describe, it } from 'node:test';
import { fileURLToPath } from 'node:url';
import { checkLimits, checkPr, checkStep } from './pr-guard.mjs';

const ROOT = join(dirname(fileURLToPath(import.meta.url)), '..');
const MANIFEST = JSON.parse(readFileSync(join(ROOT, 'targets.json'), 'utf8'));
const SHA = 'a'.repeat(40);
const BLOB = 'b'.repeat(40);
const REPO = 'TobiasPol/swarmdesk-open-math';

function validFixture(filename = 'Targets/ErdosStraus/Proof.lean', branch = 'step-13') {
  return {
    pr: {
      state: 'open',
      base: { repo: { full_name: REPO }, ref: 'main' },
      head: { sha: SHA, ref: branch },
      user: { login: 'ada' },
      commits: 1,
      changed_files: 1,
    },
    files: [{ filename, status: 'modified', sha: BLOB }],
    tree: { truncated: false, tree: [{ path: filename, type: 'blob', mode: '100644', sha: BLOB, size: 120 }] },
    commits: [{ sha: SHA, commit: { message: branch } }],
  };
}

describe('pr-guard', () => {
  it('accepts a valid Proof.lean PR and a valid blueprint Lemma PR', () => {
    const f1 = validFixture('Targets/ErdosStraus/Proof.lean', 'step-13');
    const r1 = checkPr(f1.pr, f1.files, f1.tree, f1.commits, MANIFEST, REPO, 'main');
    assert.equal(r1.target, 'erdos_straus');
    assert.equal(r1.kind, 'conjecture');
    assert.equal(r1.step, 13);

    const f2 = validFixture('Targets/ErdosStraus/Lemmas/EvenCase.lean', 'step-25');
    const r2 = checkPr(f2.pr, f2.files, f2.tree, f2.commits, MANIFEST, REPO, 'main');
    assert.equal(r2.target, 'erdos_straus_even');
    assert.equal(r2.kind, 'lemma');
    assert.equal(r2.step, 25);
  });

  it('refuses editing Spec.lean, Helpers.lean, targets.json, symlinks, or bad branches', () => {
    for (const badFile of [
      'Targets/ErdosStraus/Spec.lean',
      'Targets/ErdosStraus/Helpers.lean',
      'targets.json',
      'checker/Verify.lean',
    ]) {
      const f = validFixture(badFile);
      assert.throws(() => checkPr(f.pr, f.files, f.tree, f.commits, MANIFEST, REPO, 'main'));
    }
    const sym = validFixture();
    sym.tree.tree[0].mode = '120000';
    assert.throws(() => checkPr(sym.pr, sym.files, sym.tree, sym.commits, MANIFEST, REPO, 'main'));

    const badBranch = validFixture('Targets/ErdosStraus/Proof.lean', 'feature-proof');
    assert.throws(() =>
      checkPr(badBranch.pr, badBranch.files, badBranch.tree, badBranch.commits, MANIFEST, REPO, 'main'),
    );
  });

  it('checks open steps and per-author/per-PR limits', () => {
    const list = { steps: [{ id: 13, target: 'erdos_straus' }] };
    assert.deepEqual(checkStep(list, 13, 'erdos_straus'), { step: 13, target: 'erdos_straus' });
    assert.throws(() => checkStep(list, 13, 'ramsey_5_6'));
    assert.throws(() => checkStep(list, 99, 'erdos_straus'));

    assert.deepEqual(checkLimits({ total_count: 1, incomplete_results: false }, []), { open: 1, verdicts: 0 });
    assert.throws(() => checkLimits({ total_count: 4, incomplete_results: false }, []));
    assert.throws(() =>
      checkLimits(
        { total_count: 1, incomplete_results: false },
        Array.from({ length: 30 }, () => ({ user: { login: 'github-actions[bot]' } })),
      ),
    );
  });
});
