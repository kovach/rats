import assert from 'assert';
import { readdirSync, readFileSync } from 'fs';
import { join, dirname } from 'path';
import { fileURLToPath } from 'url';
import { parseRule, parseRules, prettyRule, prettyAtom } from './parse-rule.js';
import { compileDerivatives, makeHelpers } from './eval-fn.js';
import { solveWithLog } from './eval.js';

const args = process.argv.slice(2);
const singleTestBase = args.find(a => !a.startsWith('-'));

function withTest(fn) {
  let struct = {passing: 0, failing: []}
  fn(struct);
  console.log(`PASSING COUNT: ${struct.passing}`);
  if (struct.failing.length > 0)
    console.log(`FAILURES:\n${struct.failing}`);
  else
    console.log(`NO FAILURES`);

}

// Roundtrip tests: parse(prettyRule(parse(s))) deepEquals parse(s)
const roundtripCases = [
  'p X <- q X',
  'p X <- q X Y',
  'p X <- q X Y, !r Y',
  'p X, q X <- r X',
  'p X <- q X Y, r Y Z',
  'p X Y <- q X Y, !s X, !t Y',
  'p X, q Y <- r X Y, !s X',
  'p X <- q X foo',
  'p X Y Z <- q X Y, r Y Z',
  'out X, res X Y <- a X Y, b Y, !c X',
  'p -> q',
  'p s(X) -> p X',
  'p s(s(X)) -> p s(X)',
  'f g(X, Y) h(Y) -> r X',
  'p X Y -- q X Y',
  'p X Y ----- q X Y',
];

const __dirname = dirname(fileURLToPath(import.meta.url));

function runEval(src) {
  const allRules = parseRules(src);
  const facts = allRules.filter(r => r.body.length === 0).flatMap(r => r.head);
  const rules = allRules.filter(r => r.body.length > 0);
  const { result } = solveWithLog(facts, rules, makeHelpers(compileDerivatives(rules), rules));
  return result;
}

withTest((struct) => {

  function test(name, fn) {
    try {
      fn();
      struct.passing++;
    } catch (e) {
      struct.failing.push([name, e.message]);
    }
  }

  test('#lt builtin in body', () => {
    const r = parseRule('small X <- num X, #lt X 5');
    assert.deepStrictEqual(r.head, [
      { tag: 'atom', name: 'small', args: [{ tag: 'var', name: 'X' }] },
    ]);
    assert.deepStrictEqual(r.body, [
      { neg: false, atom: { tag: 'atom',    name: 'num', args: [{ tag: 'var', name: 'X' }] } },
      { neg: false, atom: { tag: 'builtin', name: '#lt', args: [{ tag: 'var', name: 'X' }, { tag: 'num', value: 5 }] } },
    ]);
  });

  test('negated #lt builtin', () => {
    const r = parseRule('big X <- num X, !#lt X 5');
    assert.deepStrictEqual(r.body[1],
      { neg: true, atom: { tag: 'builtin', name: '#lt', args: [{ tag: 'var', name: 'X' }, { tag: 'num', value: 5 }] } },
    );
  });

  for (const s of roundtripCases) {
    test(`roundtrip: ${s}`, () => {
      assert.deepStrictEqual(parseRule(prettyRule(parseRule(s))), parseRule(s));
    });
  }

  function runOne(base, verbose=false) {
    const srcPath = join(testsDir, base + '.derp');
    const tgtPath = join(testsDir, base + '.expected.derp');
    test(`correctness: ${base}`, () => {
      const src = readFileSync(srcPath, 'utf8');
      const tgt = readFileSync(tgtPath, 'utf8');
      const actual = runEval(src);
      const expected = runEval(tgt);
      actual.pruneFalse();
      expected.pruneFalse();
      if (!actual.equals(expected)) {
      }
      // todo: print database diff in this case
      assert.ok(actual.equals(expected));
      if(verbose) {
        console.log('actual:', actual.pretty2());
        console.log('expected:', expected.pretty2());
      }
    })
  }

  const testsDir = join(__dirname, 'tests');
  for (const f of readdirSync(testsDir).filter(f => f.endsWith('.expected.derp'))) {
    const base = f.replace('.expected.derp', '');
    runOne(base);
  }
  if (singleTestBase) {
    runOne(singleTestBase, true);
  }
});
