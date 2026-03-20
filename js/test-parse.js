import assert from 'assert';
import { parseRule, prettyRule } from './parse-rule.js';

function test(name, fn) {
  try {
    fn();
    console.log(`PASS: ${name}`);
  } catch (e) {
    console.log(`FAIL: ${name}`);
    console.log(`  ${e.message}`);
  }
}

// 1. Simple single head, single body
test('simple rule', () => {
  const r = parseRule('p X <- q X');
  assert.deepStrictEqual(r.head, [['p', 'X']]);
  assert.deepStrictEqual(r.body, [{ neg: false, atom: ['q', 'X'] }]);
});

// 2. Two-argument body literal
test('two-arg body', () => {
  const r = parseRule('p X <- q X Y');
  assert.deepStrictEqual(r.head, [['p', 'X']]);
  assert.deepStrictEqual(r.body, [{ neg: false, atom: ['q', 'X', 'Y'] }]);
});

// 3. Negative body literal
test('negative body literal', () => {
  const r = parseRule('p X <- q X Y, !r Y');
  assert.deepStrictEqual(r.head, [['p', 'X']]);
  assert.deepStrictEqual(r.body, [
    { neg: false, atom: ['q', 'X', 'Y'] },
    { neg: true,  atom: ['r', 'Y'] },
  ]);
});

// 4. Multiple heads
test('multiple heads', () => {
  const r = parseRule('p X, q X <- r X');
  assert.deepStrictEqual(r.head, [['p', 'X'], ['q', 'X']]);
  assert.deepStrictEqual(r.body, [{ neg: false, atom: ['r', 'X'] }]);
});

// 5. Multiple body literals
test('multiple body literals', () => {
  const r = parseRule('p X <- q X Y, r Y Z');
  assert.deepStrictEqual(r.head, [['p', 'X']]);
  assert.deepStrictEqual(r.body, [
    { neg: false, atom: ['q', 'X', 'Y'] },
    { neg: false, atom: ['r', 'Y', 'Z'] },
  ]);
});

// 6. Multiple negative literals
test('multiple negative literals', () => {
  const r = parseRule('p X Y <- q X Y, !s X, !t Y');
  assert.deepStrictEqual(r.head, [['p', 'X', 'Y']]);
  assert.deepStrictEqual(r.body, [
    { neg: false, atom: ['q', 'X', 'Y'] },
    { neg: true,  atom: ['s', 'X'] },
    { neg: true,  atom: ['t', 'Y'] },
  ]);
});

// 7. Multiple heads with negative body
test('multiple heads with negative body', () => {
  const r = parseRule('p X, q Y <- r X Y, !s X');
  assert.deepStrictEqual(r.head, [['p', 'X'], ['q', 'Y']]);
  assert.deepStrictEqual(r.body, [
    { neg: false, atom: ['r', 'X', 'Y'] },
    { neg: true,  atom: ['s', 'X'] },
  ]);
});

// 8. Constant arguments (lowercase)
test('constant arguments', () => {
  const r = parseRule('p X <- q X foo');
  assert.deepStrictEqual(r.head, [['p', 'X']]);
  assert.deepStrictEqual(r.body, [{ neg: false, atom: ['q', 'X', 'foo'] }]);
});

// 9. Three-argument tuples
test('three-argument tuples', () => {
  const r = parseRule('p X Y Z <- q X Y, r Y Z');
  assert.deepStrictEqual(r.head, [['p', 'X', 'Y', 'Z']]);
  assert.deepStrictEqual(r.body, [
    { neg: false, atom: ['q', 'X', 'Y'] },
    { neg: false, atom: ['r', 'Y', 'Z'] },
  ]);
});

// 10. Multiple heads and body with mixed negation
test('multiple heads, multiple body, mixed negation', () => {
  const r = parseRule('out X, res X Y <- a X Y, b Y, !c X');
  assert.deepStrictEqual(r.head, [['out', 'X'], ['res', 'X', 'Y']]);
  assert.deepStrictEqual(r.body, [
    { neg: false, atom: ['a', 'X', 'Y'] },
    { neg: false, atom: ['b', 'Y'] },
    { neg: true,  atom: ['c', 'X'] },
  ]);
});

// 11. Nested term in body
test('nested term in body', () => {
  const r = parseRule('p s(X) -> p X');
  assert.deepStrictEqual(r.head, [['p', 'X']]);
  assert.deepStrictEqual(r.body, [{ neg: false, atom: ['p', ['s', 'X']] }]);
});

// 12. Deeply nested term
test('deeply nested term', () => {
  const r = parseRule('p s(s(X)) -> p s(X)');
  assert.deepStrictEqual(r.head, [['p', ['s', 'X']]]);
  assert.deepStrictEqual(r.body, [{ neg: false, atom: ['p', ['s', ['s', 'X']]] }]);
});

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

test('#lt builtin in body', () => {
  const r = parseRule('small X <- num X, #lt X 5');
  assert.deepStrictEqual(r.head, [
    { tag: 'atom', name: 'small', args: [{ tag: 'var', name: 'X' }] },
  ]);
  assert.deepStrictEqual(r.body, [
    { neg: false, atom: { tag: 'atom',    name: 'num', args: [{ tag: 'var', name: 'X' }] } },
    { neg: false, atom: { tag: 'builtin', name: '#lt', args: [{ tag: 'var', name: 'X' }, { tag: 'sym', name: '5' }] } },
  ]);
});

test('negated #lt builtin', () => {
  const r = parseRule('big X <- num X, !#lt X 5');
  assert.deepStrictEqual(r.body[1],
    { neg: true, atom: { tag: 'builtin', name: '#lt', args: [{ tag: 'var', name: 'X' }, { tag: 'sym', name: '5' }] } },
  );
});

const correctness_tests = [
  { name: 'rule_game1',
    body: ` move a1 a2. move a2 a1. move a2 b. move b c. move A B, !win B -> win A.`,
    expected: 'todo', // a1 a2 unset; b true; c false
  },
  { name: 'rule_game2',
    body: `move a1 a2. move a2 a1. move a2 b. move A B, !win B -> win A.`,
    expected: 'todo', // a1 false; a2 true; b false
  }
];

for (const s of roundtripCases) {
  test(`roundtrip: ${s}`, () => {
    assert.deepStrictEqual(parseRule(prettyRule(parseRule(s))), parseRule(s));
  });
}


