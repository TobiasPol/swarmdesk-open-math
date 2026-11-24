#!/usr/bin/env node
// Pull request guard for swarmdesk-open-math, mirroring speed-race's pr-guard.mjs.
// Plain node, zero dependencies. Reads GitHub API responses and targets.json; never checks out forks.
//
//   node checker/pr-guard.mjs pr <pr.json> <files.json> <tree.json> <commits.json> <targets.json> <repo> <default branch>
//   node checker/pr-guard.mjs step <steps.json> <step id> <target>
//   node checker/pr-guard.mjs limits <search.json> <comments.json>
import { readFileSync } from 'node:fs';
import { pathToFileURL } from 'node:url';

export const BRANCH_RE = /^step-([1-9][0-9]{0,8})$/;
export const MAX_BYTES = 512 * 1024;
export const MAX_OPEN = 3;
export const MAX_VERDICTS = 30;
const SHA_RE = /^[0-9a-f]{40}$/;
const LOGIN_RE = /^[A-Za-z0-9](?:[A-Za-z0-9-]{0,38})$/;

class Refused extends Error {}
const refuse = (why) => {
  throw new Refused(why);
};

export function checkPr(pr, files, tree, commits, manifest, repo, defaultBranch) {
  if (pr?.state !== 'open') refuse('the pull request is not open');
  if (pr.base?.repo?.full_name !== repo) refuse('the pull request is not against this repository');
  if (pr.base?.ref !== defaultBranch) refuse(`the pull request is not against ${defaultBranch}`);
  const head = pr.head?.sha;
  if (!SHA_RE.test(head ?? '')) refuse('the pull request has no head commit');
  const author = pr.user?.login;
  if (!LOGIN_RE.test(author ?? '')) refuse('the author is not a plain account name');
  const branch = BRANCH_RE.exec(pr.head?.ref ?? '');
  if (!branch) refuse('the branch must be named step-<number>, as the desk gave it');
  if (pr.commits !== 1 || !Array.isArray(commits) || commits.length !== 1) {
    refuse('the pull request must have exactly one commit');
  }
  if (commits[0].sha !== head) refuse('the commit list and the head commit disagree');
  if (commits[0].commit?.message !== pr.head.ref) {
    refuse('the commit message must be the branch name');
  }
  if (pr.changed_files !== 1 || !Array.isArray(files) || files.length !== 1) {
    refuse('the pull request must change exactly one file');
  }
  const file = files[0];
  const targets = Array.isArray(manifest?.targets) ? manifest.targets : [];
  const matched = targets.find((t) => t.file_path === file.filename);
  if (!matched) {
    refuse('the one file must be a known Proof.lean or Lemmas/<Name>.lean in targets.json');
  }
  if (file.status !== 'modified') {
    refuse(`the file must be modified, not ${String(file.status).slice(0, 20)}`);
  }
  if (!SHA_RE.test(file.sha ?? '')) refuse('the file list names no content hash');
  if (tree?.truncated) refuse('the tree of the head commit is too large to read');
  const entries = (tree?.tree ?? []).filter((e) => e.path === file.filename);
  if (entries.length !== 1) refuse('the file is not in the tree of the head commit');
  const entry = entries[0];
  if (entry.type !== 'blob' || entry.mode !== '100644') refuse('the file must be a plain file');
  if (entry.sha !== file.sha) refuse('the file list and the tree disagree about the content');
  if (!Number.isInteger(entry.size) || entry.size < 1 || entry.size > MAX_BYTES) {
    refuse(`the file must be between 1 and ${MAX_BYTES} bytes`);
  }
  return {
    target: matched.name,
    kind: matched.kind,
    file_path: matched.file_path,
    step: Number(branch[1]),
    head,
    blob: file.sha,
    author,
  };
}

export function checkStep(list, step, target) {
  const steps = Array.isArray(list?.steps) ? list.steps : refuse('the desk sent no step list');
  const found = steps.find((s) => s.id === step);
  if (!found) refuse(`step-${step} is not open at the desk`);
  if (found.target !== target) refuse(`step-${step} is not a step for this target`);
  return { step, target };
}

export function checkLimits(search, comments) {
  const mine = search?.total_count;
  if (!Number.isInteger(mine) || mine < 0 || !Array.isArray(comments)) {
    refuse('the limits could not be read');
  }
  if (search.incomplete_results !== false) refuse('the limits could not be read: push again');
  if (mine > MAX_OPEN) {
    refuse(`you have ${mine} open pull requests: at most ${MAX_OPEN} are judged at a time`);
  }
  const verdicts = comments.filter((c) => c?.user?.login === 'github-actions[bot]').length;
  if (verdicts >= MAX_VERDICTS) {
    refuse(`this pull request has been judged ${MAX_VERDICTS} times: open a new one`);
  }
  return { open: mine, verdicts };
}

const json = (path) => JSON.parse(readFileSync(path, 'utf8'));

function main(argv) {
  const [mode, ...rest] = argv;
  if (mode === 'pr' && rest.length === 7) {
    return checkPr(
      json(rest[0]),
      json(rest[1]),
      json(rest[2]),
      json(rest[3]),
      json(rest[4]),
      rest[5],
      rest[6],
    );
  }
  if (mode === 'step' && rest.length === 3) {
    return checkStep(json(rest[0]), Number(rest[1]), rest[2]);
  }
  if (mode === 'limits' && rest.length === 2) {
    return checkLimits(json(rest[0]), json(rest[1]));
  }
  console.error(
    'usage: pr-guard.mjs pr <pr> <files> <tree> <commits> <targets> <repo> <branch> | step <steps> <id> <target> | limits <search> <comments>',
  );
  process.exit(3);
}

if (import.meta.url === pathToFileURL(process.argv[1] ?? '').href) {
  try {
    console.log(JSON.stringify(main(process.argv.slice(2))));
  } catch (error) {
    const reason = error instanceof Refused ? error.message : 'the pull request could not be read';
    console.log(JSON.stringify({ refused: reason }));
    process.exit(1);
  }
}
