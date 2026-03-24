// Parser for rules of the form:
//   p X, q X <- r X Y, !s Y
//
// Returns: { head: [atom, ...], body: [{neg: bool, atom}, ...], range? }
// atom: { tag: 'atom', name: string, args: [term, ...], range? }
// term: { tag: 'var', name } | { tag: 'sym', name } | { tag: 'compound', name, args: [term, ...] }
//   (each term has a range? field)
//
// Vars are uppercase-initial; syms are lowercase-initial.
//
// Range: { start: Pos, end: Pos } where Pos = { line, col } (1-indexed, both inclusive)
// Ranges are present when parseRules(text) is used; absent when parseRule(s) is called standalone.

// Split string by sep, but only at depth 0 (not inside parentheses).
// Returns [{text, start}] where start is the offset of text[0] within s.
function splitTopLevel(s, sep) {
  const parts = [];
  let depth = 0, segStart = 0;
  for (let i = 0; i < s.length; i++) {
    const ch = s[i];
    if (ch === '(') depth++;
    else if (ch === ')') depth--;
    if (ch === sep && depth === 0) {
      const raw = s.slice(segStart, i);
      const ltrim = raw.search(/\S/);
      if (ltrim !== -1)
        parts.push({ text: raw.trim(), start: segStart + ltrim });
      segStart = i + 1;
    }
  }
  const raw = s.slice(segStart);
  const ltrim = raw.search(/\S/);
  if (ltrim !== -1)
    parts.push({ text: raw.trim(), start: segStart + ltrim });
  return parts;
}

// Split a literal string into whitespace-separated tokens, keeping
// parenthesised sub-expressions (terms) together as single tokens.
// Returns [{text, start}] where start is the offset of text[0] within s.
function tokenizeLiteral(s) {
  const tokens = [];
  let depth = 0, tokStart = -1;
  for (let i = 0; i < s.length; i++) {
    const ch = s[i];
    if (ch === '(') {
      depth++;
      if (tokStart === -1) tokStart = i;
    } else if (ch === ')') {
      depth--;
    } else if (/\s/.test(ch) && depth === 0) {
      if (tokStart !== -1) {
        tokens.push({ text: s.slice(tokStart, i), start: tokStart });
        tokStart = -1;
      }
    } else {
      if (tokStart === -1) tokStart = i;
    }
  }
  if (tokStart !== -1) tokens.push({ text: s.slice(tokStart), start: tokStart });
  return tokens;
}

const IDENT         = /^[a-z\/][a-zA-Z0-9\/_\-']*$/;
const VAR_IDENT     = /^[A-Z][a-zA-Z0-9\/_\-']*$/;
const BUILTIN_IDENT = /^#[a-z\/][a-zA-Z0-9\/_\-']*$/;

// Build a position map for use during parsing.
// posMap[i] = { line, col } (1-indexed) for character i in the stripped string
// produced by parseRules's comment-stripping + join step.
function buildPosMap(text) {
  const strippedLines = text.split('\n').map(line => {
    const i = line.search(/;|#(?!\w)/);
    return i === -1 ? line : line.slice(0, i);
  });
  const posMap = [];
  for (let li = 0; li < strippedLines.length; li++) {
    const line = strippedLines[li];
    for (let col = 0; col < line.length; col++)
      posMap.push({ line: li + 1, col: col + 1 });
    if (li < strippedLines.length - 1)
      posMap.push({ line: li + 1, col: line.length + 1 }); // the joining space
  }
  return posMap;
}

// Return { start: Pos, end: Pos } for the substring [baseOff, baseOff+len) in the stripped string.
// Both start and end are inclusive (closed range).
function mkRange(posMap, baseOff, len) {
  const last = posMap.length - 1;
  return {
    start: posMap[Math.min(baseOff, last)],
    end:   posMap[Math.min(baseOff + len - 1, last)],
  };
}

// Build a parse error with location info when posMap is available.
// err.range is set to the range of the offending text.
function parseError(msg, s, posMap, baseOff) {
  const loc = (posMap != null && baseOff != null)
    ? ` at line ${posMap[Math.min(baseOff, posMap.length - 1)].line}, col ${posMap[Math.min(baseOff, posMap.length - 1)].col}`
    : '';
  const err = new Error(`${msg}${loc}: "${s}"`);
  if (posMap != null && baseOff != null) err.range = mkRange(posMap, baseOff, s.length || 1);
  return err;
}

// parseTerm(s, posMap?, baseOff?)
// posMap and baseOff are optional; when provided, adds range to the returned node.
// baseOff is the offset of s[0] in the stripped string (s must already be trimmed).
function parseTerm(s, posMap, baseOff) {
  s = s.trim();
  const range = posMap != null ? mkRange(posMap, baseOff, s.length) : undefined;
  const rng = range ? { range } : {};

  const m = s.match(/^([a-z\/][a-zA-Z0-9\/_\-']*)\((.*)\)$/);
  if (m) {
    const argsBaseOff = posMap != null ? baseOff + m[1].length + 1 : undefined; // skip "name("
    const args = splitTopLevel(m[2], ',').map(({ text, start }) =>
      parseTerm(text, posMap, argsBaseOff != null ? argsBaseOff + start : undefined)
    );
    return { tag: 'compound', name: m[1], args, ...rng };
  }
  if (s === '_') return { tag: 'hole', ...rng };
  if (/^\d+$/.test(s)) return { tag: 'num', value: parseInt(s, 10), ...rng };
  if (VAR_IDENT.test(s)) return { tag: 'var', name: s, ...rng };
  if (IDENT.test(s)) return { tag: 'sym', name: s, ...rng };
  throw parseError('Invalid term', s, posMap, baseOff);
}

// parseLiteral(s, posMap?, baseOff?)
// baseOff is the offset of s[0] in the stripped string (s must already be trimmed).
function parseLiteral(s, posMap, baseOff) {
  s = s.trim();
  const neg = s.startsWith('!');
  // atomBaseOff: absolute offset of the first char of the atom (after optional '!' and whitespace)
  let atomStr = s;
  let atomBaseOff = baseOff;
  if (neg) {
    atomStr = s.slice(1).trim();
    if (posMap != null) {
      const ws = s.slice(1).search(/\S/);
      atomBaseOff = baseOff + 1 + (ws === -1 ? 0 : ws);
    }
  }

  const tokens = tokenizeLiteral(atomStr);
  const [functorTok, ...argToks] = tokens;
  const functor = functorTok ? functorTok.text : undefined;

  const atomRange = (posMap != null && functor)
    ? mkRange(posMap, atomBaseOff + functorTok.start, atomStr.length - functorTok.start)
    : undefined;
  const rng = atomRange ? { range: atomRange } : {};

  const args = argToks.map(({ text, start }) =>
    parseTerm(text, posMap, posMap != null ? atomBaseOff + start : undefined)
  );

  if (BUILTIN_IDENT.test(functor))
    return { neg, atom: { tag: 'builtin', name: functor, args, ...rng } };
  if (!functor || !IDENT.test(functor)) throw parseError('Invalid literal', s, posMap, baseOff);
  return { neg, atom: { tag: 'atom', name: functor, args, ...rng } };
}

// parseRule(s, posMap?, baseOff?)
// baseOff is the offset of s[0] in the stripped string (s must already be trimmed).
function parseRule(s, posMap, baseOff) {
  s = s.trim();
  const ruleRange = posMap != null ? mkRange(posMap, baseOff, s.length) : undefined;
  const rng = ruleRange ? { range: ruleRange } : {};

  const backArrow = s.indexOf('<-');
  const fwdArrow  = s.indexOf('->');
  const dashMatch = /-{2,}/.exec(s);

  // Compute headStr/bodyStr and their absolute offsets within the stripped string.
  let headStr, bodyStr, headOff, bodyOff;

  function absOff(relativeToS, subStr) {
    // subStr is a slice of s starting at relativeToS; find offset of its first non-space char
    if (posMap == null) return undefined;
    const ws = subStr.search(/\S/);
    return baseOff + relativeToS + (ws === -1 ? 0 : ws);
  }

  if (backArrow !== -1) {
    const hRaw = s.slice(0, backArrow);
    const bRaw = s.slice(backArrow + 2);
    headStr = hRaw.trim(); headOff = absOff(0, hRaw);
    bodyStr = bRaw.trim(); bodyOff = absOff(backArrow + 2, bRaw);
  } else if (fwdArrow !== -1) {
    const bRaw = s.slice(0, fwdArrow);
    const hRaw = s.slice(fwdArrow + 2);
    bodyStr = bRaw.trim(); bodyOff = absOff(0, bRaw);
    headStr = hRaw.trim(); headOff = absOff(fwdArrow + 2, hRaw);
  } else if (dashMatch) {
    const bRaw = s.slice(0, dashMatch.index);
    const hRaw = s.slice(dashMatch.index + dashMatch[0].length);
    bodyStr = bRaw.trim(); bodyOff = absOff(0, bRaw);
    headStr = hRaw.trim(); headOff = absOff(dashMatch.index + dashMatch[0].length, hRaw);
  } else {
    headStr = s; headOff = posMap != null ? baseOff : undefined;
    bodyStr = ''; bodyOff = undefined;
  }

  const head = splitTopLevel(headStr, ',').map(({ text, start }) => {
    const lit = parseLiteral(text, posMap, headOff != null ? headOff + start : undefined);
    if (lit.neg) throw parseError('Head literal cannot be negated', text, posMap, headOff != null ? headOff + start : undefined);
    return lit.atom;
  });

  const body = bodyStr ? splitTopLevel(bodyStr, ',').map(({ text, start }) =>
    parseLiteral(text, posMap, bodyOff != null ? bodyOff + start : undefined)
  ) : [];

  return { head, body, ...rng };
}

// Parse a block of text into an array of rules, with range info on every node.
function parseRulesWithRanges(text) {
  const posMap = buildPosMap(text);
  const stripped = text.split('\n')
    .map(line => { const i = line.search(/;|#(?!\w)/); return i === -1 ? line : line.slice(0, i); })
    .join(' ');
  return splitTopLevel(stripped, '.')
    .filter(({ text: s }) => s)
    .map(({ text: s, start }) => parseRule(s, posMap, start));
}

// Parse a block of text into an array of rules.
// Each rule must be terminated with a period. Rules may span multiple lines.
// ; and # begin line comments.
function parseRules(text) {
  return stripRanges(parseRulesWithRanges(text));
}

function prettyTerm(term) {
  if (term.tag === 'hole') return '_';
  if (term.tag === 'num') return String(term.value);
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

function stripRangesTerm(term) {
  const { range: _, ...t } = term;
  if (t.args) t.args = t.args.map(stripRangesTerm);
  return t;
}

function stripRangesAtom(atom) {
  const { range: _, ...a } = atom;
  if (a.args) a.args = a.args.map(stripRangesTerm);
  return a;
}

// Remove all range fields from a parsed rule (or array of rules).
function stripRanges(rules) {
  const strip = rule => ({
    head: rule.head.map(stripRangesAtom),
    body: rule.body.map(({ neg, atom }) => ({ neg, atom: stripRangesAtom(atom) })),
  });
  return Array.isArray(rules) ? rules.map(strip) : strip(rules);
}

export { parseRule, parseRules, parseRulesWithRanges, stripRanges, prettyRule, prettyAtom };
