import assert from 'assert';
import { parseRule, prettyRule } from './parse-rule.js';

function withTest(fn) {
  let struct = {passing: 0, failing: []}
  fn(struct);
  console.log(`PASSING COUNT: ${struct.passing}`);
  if (struct.failing.length > 0)
    console.log(`FAILURES: ${struct.failing}`);
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
      { neg: false, atom: { tag: 'builtin', name: '#lt', args: [{ tag: 'var', name: 'X' }, { tag: 'sym', name: '5' }] } },
    ]);
  });

  test('negated #lt builtin', () => {
    const r = parseRule('big X <- num X, !#lt X 5');
    assert.deepStrictEqual(r.body[1],
      { neg: true, atom: { tag: 'builtin', name: '#lt', args: [{ tag: 'var', name: 'X' }, { tag: 'sym', name: '5' }] } },
    );
  });

  for (const s of roundtripCases) {
    test(`roundtrip: ${s}`, () => {
      assert.deepStrictEqual(parseRule(prettyRule(parseRule(s))), parseRule(s));
    });
  }
});
