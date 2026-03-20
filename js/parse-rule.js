// Parser for rules of the form:
//   p X, q X <- r X Y, !s Y
//
// Returns: { head: [atom, ...], body: [{neg: bool, atom}, ...] }
// atom: { tag: 'atom', name: string, args: [term, ...] }
// term: { tag: 'var', name } | { tag: 'sym', name } | { tag: 'compound', name, args: [term, ...] }
//
// Vars are uppercase-initial; syms are lowercase-initial.

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

const IDENT         = /^[\w][\w\-\/]*$/;
const BUILTIN_IDENT = /^#[\w][\w\-\/]*$/;

function parseTerm(s) {
  s = s.trim();
  const m = s.match(/^([\w][\w\-\/]*)\((.*)\)$/);
  if (m) return { tag: 'compound', name: m[1], args: splitTopLevel(m[2], ',').map(parseTerm) };
  if (s === '_') return { tag: 'hole' };
  if (IDENT.test(s)) {
    const isUpper = s[0] >= 'A' && s[0] <= 'Z';
    return isUpper ? { tag: 'var', name: s } : { tag: 'sym', name: s };
  }
  throw new Error(`Invalid term: "${s}"`);
}

function parseLiteral(s) {
  s = s.trim();
  const neg = s.startsWith('!');
  if (neg) s = s.slice(1).trim();
  const [functor, ...argTokens] = tokenizeLiteral(s);
  if (BUILTIN_IDENT.test(functor))
    return { neg, atom: { tag: 'builtin', name: functor, args: argTokens.map(parseTerm) } };
  if (!functor || !IDENT.test(functor)) throw new Error(`Invalid literal: "${s}"`);
  return { neg, atom: { tag: 'atom', name: functor, args: argTokens.map(parseTerm) } };
}

function parseRule(s) {
  s = s.trim();
  const backArrow = s.indexOf('<-');
  const fwdArrow  = s.indexOf('->');
  const dashMatch = /-{2,}/.exec(s);

  let headStr, bodyStr;
  if (backArrow !== -1) {
    headStr = s.slice(0, backArrow).trim();
    bodyStr = s.slice(backArrow + 2).trim();
  } else if (fwdArrow !== -1) {
    bodyStr = s.slice(0, fwdArrow).trim();
    headStr = s.slice(fwdArrow + 2).trim();
  } else if (dashMatch) {
    bodyStr = s.slice(0, dashMatch.index).trim();
    headStr = s.slice(dashMatch.index + dashMatch[0].length).trim();
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

// Parse a block of text into an array of rules.
// Each rule must be terminated with a period. Rules may span multiple lines.
// // and # begin line comments.
function parseRules(text) {
  const stripped = text.split('\n')
    .map(line => { const i = line.search(/;|#(?!\w)/); return i === -1 ? line : line.slice(0, i); })
    .join(' ');
  return splitTopLevel(stripped, '.')
    .map(s => s.trim())
    .filter(s => s)
    .map(parseRule);
}

function prettyTerm(term) {
  if (term.tag === 'hole') return '_';
  if (term.tag === 'var' || term.tag === 'sym') return term.name;
  return term.args.length ? `${term.name}(${term.args.map(prettyTerm).join(', ')})` : term.name;
}

function prettyAtom(atom) {
  // handles tag: 'atom' | 'builtin'
  return atom.args.length ? `${atom.name} ${atom.args.map(prettyTerm).join(' ')}` : atom.name;
}

function prettyRule(rule) {
  const head = rule.head.map(prettyAtom).join(', ');
  const body = rule.body.map(lit => (lit.neg ? '!' : '') + prettyAtom(lit.atom)).join(', ');
  return `${body} -> ${head}`;
}

export { parseRule, parseRules, prettyRule, prettyAtom };
