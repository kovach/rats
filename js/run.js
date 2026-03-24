import { parseRules, parseRulesWithRanges, prettyAtom } from './parse-rule.js';
import { compileDerivatives, makeHelpers, makeCompiledRefEvalFn, makeNegOnlyFn } from './eval-fn.js';
import { solveWithLog, solveRefWithLog } from './eval.js';
import { readFileSync } from 'fs';

const args = process.argv.slice(2);
const useRef   = args.includes('--ref');
const parseOnly = args.includes('--parse');
const filePath = args.find(a => !a.startsWith('-'));
if (!filePath) { console.error('Usage: node run.js [--ref|--parse] <file.derp>'); process.exit(1); }

const text = readFileSync(filePath, 'utf8');

if (parseOnly) {
  console.log(JSON.stringify(parseRulesWithRanges(text), null, 2));
  process.exit(0);
}

const allRules = parseRules(text);
const facts = allRules.filter(r => r.body.length === 0).flatMap(r => r.head);
const rules = allRules.filter(r => r.body.length > 0);
const derivatives = compileDerivatives(rules);

let result;
if (useRef) {
  const evalFnRef = makeCompiledRefEvalFn(derivatives, rules);
  const negOnly = makeNegOnlyFn(rules);
  ({ result } = solveRefWithLog(facts, negOnly, evalFnRef, { maxInner: 300, maxOuter: 10 }));
} else {
  const helpers = makeHelpers(derivatives, rules);
  ({ result } = solveWithLog(facts, rules, helpers, { maxInner: 300, maxOuter: 10 }));
}

const tuples = [];
if (typeof result.activeTuples === 'function') {
  for (const [tuple] of result.activeTuples()) tuples.push(prettyAtom(tuple));
} else {
  for (const [key, e] of result)
    if ((e.current ?? e.count) > 0) tuples.push(prettyAtom(JSON.parse(key)));
}
tuples.sort();
if (tuples.length > 0) {
  console.log('--');
  tuples.forEach((t, i) => console.log('  ' + t + (i < tuples.length - 1 ? ',' : '.')));
}
