// Parser for rules of the form:
//   p X, q X <- r X Y, !s Y
//
// Returns: { head: [['p','X'], ['q','X']], body: [{neg: false, atom: ['r','X','Y']}, {neg: true, atom: ['s','Y']}] }
//
// Terms in argument positions still use parentheses: p s(X) -> p X

// Split string by sep, but only at depth 0 (not inside parentheses)
function splitTopLevel(s, sep) {
  const parts = [];
  let depth = 0, current = '';
  for (const ch of s) {
    if (ch === '(') depth++;
    else if (ch === ')') depth--;
    if (ch === sep && depth === 0) {
      parts.push(current.trim());
      current = '';
    } else {
      current += ch;
    }
  }
  if (current.trim()) parts.push(current.trim());
  return parts;
}

// Split a literal string into whitespace-separated tokens, keeping
// parenthesised sub-expressions (terms) together as single tokens.
function tokenizeLiteral(s) {
  const tokens = [];
  let depth = 0, current = '';
  for (const ch of s) {
    if (ch === '(') { depth++; current += ch; }
    else if (ch === ')') { depth--; current += ch; }
    else if (/\s/.test(ch) && depth === 0) {
      if (current) { tokens.push(current); current = ''; }
    } else {
      current += ch;
    }
  }
  if (current) tokens.push(current);
  return tokens;
}

function parseTerm(s) {
  s = s.trim();
  const m = s.match(/^(\w+)\((.*)\)$/);
  if (m) return [m[1], ...splitTopLevel(m[2], ',').map(parseTerm)];
  if (s.match(/^\w+$/)) return s;
  throw new Error(`Invalid term: "${s}"`);
}

function parseLiteral(s) {
  s = s.trim();
  const neg = s.startsWith('!');
  if (neg) s = s.slice(1).trim();
  const [functor, ...argTokens] = tokenizeLiteral(s);
  if (!functor || !functor.match(/^\w+$/)) throw new Error(`Invalid literal: "${s}"`);
  return { neg, atom: [functor, ...argTokens.map(parseTerm)] };
}

function parseRule(s) {
  s = s.trim();
  const backArrow = s.indexOf('<-');
  const fwdArrow  = s.indexOf('->');

  let headStr, bodyStr;
  if (backArrow !== -1) {
    headStr = s.slice(0, backArrow).trim();
    bodyStr = s.slice(backArrow + 2).trim();
  } else if (fwdArrow !== -1) {
    bodyStr = s.slice(0, fwdArrow).trim();
    headStr = s.slice(fwdArrow + 2).trim();
  } else {
    headStr = s;
    bodyStr = '';
  }

  const head = splitTopLevel(headStr, ',').map(h => {
    const lit = parseLiteral(h);
    if (lit.neg) throw new Error(`Head literal cannot be negated: "${h}"`);
    return lit.atom;
  });

  const body = bodyStr ? splitTopLevel(bodyStr, ',').map(parseLiteral) : [];

  return { head, body };
}

// Split a block of text into facts (tuples) and proper rules.
// Facts are lines with no body (no <- or empty body); proper rules have a non-empty body.
// Blank lines and lines starting with // or # are ignored.
function splitRules(text) {
  const facts = [], rules = [];
  for (const line of text.split('\n')) {
    const s = line.trim();
    if (!s || s.startsWith('//') || s.startsWith('#')) continue;
    const r = parseRule(s);
    if (r.body.length === 0) {
      for (const atom of r.head) facts.push(atom);
    } else {
      rules.push(r);
    }
  }
  return { facts, rules };
}

function prettyTerm(term) {
  if (!Array.isArray(term)) return term;
  const [f, ...args] = term;
  return args.length ? `${f}(${args.map(prettyTerm).join(', ')})` : f;
}

function prettyAtom(atom) {
  const [f, ...args] = atom;
  return args.length ? `${f} ${args.map(prettyTerm).join(' ')}` : f;
}

function prettyRule(rule) {
  const head = rule.head.map(prettyAtom).join(', ');
  const body = rule.body.map(lit => (lit.neg ? '!' : '') + prettyAtom(lit.atom)).join(', ');
  return `${body} -> ${head}`;
}

export { parseRule, prettyRule, prettyAtom, splitRules };
