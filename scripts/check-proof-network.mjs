import assert from 'node:assert/strict';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

// Run after `lax build .`. Check the computed graph, not hand-written metadata.
const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const database = process.argv[2] ?? path.join(os.homedir(), '.lax', 'lax-database');
const local = JSON.parse(fs.readFileSync(path.join(root, 'build-output.json'), 'utf8'));
const localStatements = new Set(local.concepts.flatMap(c => c.statements.map(s => s.id)));
const localProofs = new Map(local.proofs.map(p => [p.conclusion, p]));
assert.equal(localStatements.size, 17);
assert.equal(local.proofs.length, 17);
for (const statement of localStatements) assert(localProofs.has(statement), `Missing proof: ${statement}`);

const S = suffix => `Lax689614.${suffix}`;
const expected = new Map([
  ['GrundyProperties.losing_iff_zero', ['GrundyProperties.smaller_reachable', 'GrundyProperties.value_not_reachable']],
  ['GrundyProperties.disjoint_union', ['GrundyProperties.smaller_reachable', 'GrundyProperties.value_not_reachable']],
  ['RegularPlay.deviation_loses', ['Biclique.value_eq', 'GrundyProperties.losing_iff_zero']],
  ['RegularPlay.exceptional_parity', ['Biclique.value_eq', 'GrundyProperties.disjoint_union', 'GrundyProperties.losing_iff_zero']],
  ['Reduction.false_strategy', ['Passes.outcome_equivalent', 'RegularPlay.deviation_loses', 'RegularPlay.exceptional_parity']],
  ['Reduction.true_strategy', ['Passes.outcome_equivalent', 'RegularPlay.deviation_loses']],
  ['Reduction.polynomial_reduction', ['Reduction.false_strategy', 'Reduction.true_strategy', 'Sizes.construction_size']],
  ['Completeness.pspace_complete', ['Completeness.membership', 'PositiveCNFHardness.hard', 'Reduction.polynomial_reduction']],
]);
for (const [conclusion, premises] of expected) {
  const actual = localProofs.get(S(conclusion)).assumptions;
  for (const premise of premises) assert(actual.includes(S(premise)), `Missing edge: ${premise} -> ${conclusion}`);
}
assert.deepEqual([...localProofs.get(S('Completeness.pspace_complete')).assumptions].sort(),
  expected.get('Completeness.pspace_complete').map(S).sort());
assert(localProofs.get(S('PositiveCNFHardness.hard')).assumptions.includes('Lax429075.GateCorrect.correct'));

// Reject cycles in the local dependency graph explicitly.
const visiting = new Set(), visited = new Set();
function visit(id) {
  assert(!visiting.has(id), `Dependency cycle through ${id}`);
  if (visited.has(id)) return;
  visiting.add(id);
  for (const premise of localProofs.get(id).assumptions) if (localStatements.has(premise)) visit(premise);
  visiting.delete(id);
  visited.add(id);
}
for (const id of localStatements) visit(id);

// Load registered supporting proofs recursively. Nothing external is assumed
// proven merely because it is named by a local proof.
const proofs = [...local.proofs], loaded = new Set(['689614']);
for (let i = 0; i < proofs.length; i++) {
  for (const premise of proofs[i].assumptions) {
    const match = /^Lax([0-9]+)\./.exec(premise);
    assert(match, `Unexpected statement id: ${premise}`);
    if (loaded.has(match[1])) continue;
    loaded.add(match[1]);
    const folder = path.join(database, `lax-${match[1]}`);
    const record = JSON.parse(fs.readFileSync(path.join(folder, 'record.json'), 'utf8'));
    assert.equal(record.state, 'registered', `Unregistered dependency: ${premise}`);
    const output = JSON.parse(fs.readFileSync(path.join(folder, 'build-output.json'), 'utf8'));
    proofs.push(...output.proofs);
  }
}
const proven = new Set();
let changed = true;
while (changed) {
  changed = false;
  for (const p of proofs) if (!proven.has(p.conclusion) && p.assumptions.every(a => proven.has(a))) {
    proven.add(p.conclusion);
    changed = true;
  }
}
for (const id of localStatements) assert(proven.has(id), `Statement not proven by the least fixed point: ${id}`);
for (const p of local.proofs) console.log(`${p.assumptions.join(', ') || '(no premises)'} -> ${p.conclusion}`);
console.log(`Verified ${localStatements.size} proven local statements; no local cycles; expected network edges present.`);
