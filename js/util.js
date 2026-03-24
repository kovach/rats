function tupleKey(t) {
  return JSON.stringify(t);
}

function applyBindings(term, bindings) {
  if (term.tag === 'hole') return term;
  if (term.tag === 'var') return (term.name in bindings) ? bindings[term.name] : term;
  if (term.tag === 'sym' || term.tag === 'num') return term;
  return { ...term, args: term.args.map(a => applyBindings(a, bindings)) };
}

export { tupleKey, applyBindings };
