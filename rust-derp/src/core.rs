use std::collections::{HashMap, HashSet};
use std::rc::Rc;
use std::cell::RefCell;

use crate::types::*;
use crate::sym::{Sym, Interner};

// -- Expression helpers -------------------------------------------------------

pub fn atom(t: Tuple) -> Expr {
    if t.is_empty() {
        Expr::Unit
    } else {
        Expr::Atom(t)
    }
}

// -- Atom predicate collection ------------------------------------------------

/// Walk an Expr and collect all (predicate_sym, arity) pairs from Atom nodes.
fn atom_predicates(expr: &Expr) -> Vec<(Sym, usize)> {
    let mut result = Vec::new();
    fn walk(e: &Expr, out: &mut Vec<(Sym, usize)>) {
        match e {
            Expr::Atom(pat) if !pat.is_empty() => {
                if let Term::Pred(Name::Sym(sym)) = pat[0].as_ref() {
                    out.push((*sym, pat.len() - 1));
                }
            }
            Expr::Join(a, b) => {
                walk(a, out);
                walk(b, out);
            }
            _ => {}
        }
    }
    walk(expr, &mut result);
    result.sort();
    result.dedup();
    result
}

// -- Specialize ---------------------------------------------------------------

// modify val's join order to take into account variables known to be bound
pub fn optimize_with(bound: &mut Vec<Name>, val: Expr, interner: &Interner) -> Expr {
    fn extract_matching<F: Fn(&Tuple) -> bool + Copy>(
        expr: &Expr, pred: F
    ) -> Option<(Tuple, Expr)> {
        match expr {
            Expr::Atom(t) if pred(t) => Some((t.clone(), Expr::Unit)),
            Expr::Join(a, b) => {
                if let Some((t, rest)) = extract_matching(a, pred) {
                    Some((t, join(rest, *b.clone())))
                } else if let Some((t, rest)) = extract_matching(b, pred) {
                    Some((t, join(*a.clone(), rest)))
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    fn pred_name(tuple: &Tuple, interner: &Interner) -> Option<String> {
        tuple.first().and_then(|t| {
            if let Term::Pred(n) = t.as_ref() { Some(n.resolve(interner).to_owned()) } else { None }
        })
    }

    fn arg_bound(arg: &ATerm, bound: &[Name]) -> bool {
        match arg.as_ref() {
            Term::Var(VarOp::Name(n)) => bound.contains(n),
            Term::Var(_) => panic!("arg_bound: already compiled"),
            _ => true,
        }
    }

    let extract_lt_le_bb = |bound: &[Name], interner: &Interner, expr: &Expr| {
        extract_matching(expr, |t| {
            matches!(pred_name(t, interner).as_deref(), Some("lt") | Some("le"))
                && t.len() >= 3
                && arg_bound(&t[1], bound)
                && arg_bound(&t[2], bound)
        })
    };

    let extract_eq_bb = |bound: &[Name], interner: &Interner, expr: &Expr| {
        extract_matching(expr, |t| {
            pred_name(t, interner).as_deref() == Some("eq")
                && t.len() >= 3
                && arg_bound(&t[1], bound)
                && arg_bound(&t[2], bound)
        })
    };

    let extract_eq_bf = |bound: &[Name], interner: &Interner, expr: &Expr| {
        extract_matching(expr, |t| {
            pred_name(t, interner).as_deref() == Some("eq")
                && t.len() >= 3
                && (arg_bound(&t[1], bound) ^ arg_bound(&t[2], bound))
        })
    };

    let extract_non_cmp = |_bound: &[Name], interner: &Interner, expr: &Expr| {
        extract_matching(expr, |t| {
            match pred_name(t, interner).as_deref() {
                Some("lt") | Some("le") | Some("eq") => false,
                _ => true}
        })
    };


    let extract_other = |_bound: &[Name], _interner: &Interner, expr: &Expr| {
        extract_matching(expr, |_| true)
    };

    let mut remaining = val;
    let mut result = Expr::Unit;

    while let Some((atom, rest)) =
        extract_lt_le_bb(bound, interner, &remaining)
        .or_else(|| extract_eq_bb(bound, interner, &remaining))
        .or_else(|| extract_eq_bf(bound, interner, &remaining))
        .or_else(|| extract_non_cmp(bound, interner, &remaining))
        .or_else(|| extract_other(bound, interner, &remaining))
    {
        for v in tuple_vars(&atom) {
            if !bound.contains(&v) { bound.push(v); }
        }
        result = join(result, Expr::Atom(atom));
        remaining = rest;
    }

    join(result, remaining)
}

pub fn eval_rule(rule: &Rule, ts: &Tuples, check: &Tuples, table: &mut TermTable) -> Vec<Vec<Tuple>> {
    let mut results = Vec::new();
    let mut slots = vec![ablank(); 30]; // TODO
    for final_slots in eval_flat(&mut slots, &rule.body.val.flatten(), ts, check, table) {
        // Substitute head
        let head_tuples: Vec<Tuple> = rule.head.iter().map(|ht| {
            sub_terms_compiled(&final_slots, ht, table)
        }).collect();
        results.push(head_tuples);
    }
    results
}

// -- Compiled expression compilation ------------------------------------------

fn compile_term(t: &ATerm, seen: &mut HashMap<Sym, u16>, next_slot: &mut u16) -> ATerm {
    match t.as_ref() {
        Term::Var(VarOp::Name(name)) => {
            let sym = name.as_sym();
            if let Some(&slot) = seen.get(&sym) {
                Rc::new(Term::Var(VarOp::Check(slot)))
            } else {
                let slot = *next_slot;
                seen.insert(sym, slot);
                *next_slot += 1;
                Rc::new(Term::Var(VarOp::Set(slot)))
            }
        }
        Term::Var(_) => panic!("compile_term: already compiled"),
        Term::App(cons, args) => {
            let cargs: Vec<ATerm> = args.iter().map(|a| compile_term(a, seen, next_slot)).collect();
            aapp(cons.clone(), cargs)
        }
        _ => t.clone(),  // Pred, Num, Blank, Str are unchanged
    }
}

fn compile_tuple(t: &[ATerm], seen: &mut HashMap<Sym, u16>, next_slot: &mut u16) -> Tuple {
    t.iter().map(|a| compile_term(a, seen, next_slot)).collect()
}

fn compile_expr(expr: &Expr, seen: &mut HashMap<Sym, u16>, next_slot: &mut u16) -> Expr {
    match expr {
        Expr::Unit => Expr::Unit,
        Expr::Atom(pat) => {
            let compiled: Tuple = pat.iter().map(|a| compile_term(a, seen, next_slot)).collect();
            Expr::Atom(compiled)
        }
        Expr::NegAtom(at) => {
            let compiled: Tuple = at.iter().map(|a| compile_term(a, seen, next_slot)).collect();
            Expr::NegAtom(compiled)
        }
        Expr::Bind(x, y) => {
            // y is evaluated first (substituted), then unified with x
            let cy = compile_term(y, seen, next_slot);
            let cx = compile_term(x, seen, next_slot);
            Expr::Bind(cx, cy)
        }
        Expr::Join(a, b) => {
            let ca = compile_expr(a, seen, next_slot);
            let cb = compile_expr(b, seen, next_slot);
            join(ca, cb)
        }
    }
}

// -- Compiled expression evaluation -------------------------------------------

fn match_term_compiled(slots: &mut Vec<ATerm>, pat: &ATerm, val: &ATerm, table: &TermTable) -> bool {
    match pat.as_ref() {
        Term::Var(VarOp::Set(i)) => {
            slots[*i as usize] = val.clone();
            true
        }
        Term::Var(VarOp::Check(i)) => slots[*i as usize] == *val,
        Term::Var(VarOp::Name(_)) => panic!("match_term_compiled: uncompiled VarOp::Name"),
        Term::Pred(n) => matches!(val.as_ref(), Term::Pred(n2) if n == n2),
        Term::Num(n) => matches!(val.as_ref(), Term::Num(n2) if n == n2),
        Term::Str(n) => matches!(val.as_ref(), Term::Str(n2) if n == n2),
        Term::Blank => true,
        Term::App(cons, args) => {
            let val_unfolded = match val.as_ref() {
                Term::Id(n) => { table.get(*n) }
                Term::App(_,_) => panic!(),
                _ => val,
            };
            match val_unfolded.as_ref() {
                Term::App(cons2, args2) if cons == cons2 && args.len() == args2.len() => {
                    for (cp, av) in args.iter().zip(args2.iter()) {
                        if !match_term_compiled(slots, cp, av, table) {
                            return false;
                        }
                    }
                    true
                }
                _ => false,
            }
        }
        Term::Id(_) => panic!("match_term_compiled: Term::Id in pattern position"),
    }
}

fn match_terms_compiled(slots: &mut Vec<ATerm>, pats: &[ATerm], vals: &[ATerm], table: &TermTable) -> bool {
    if pats.len() != vals.len() { return false; }
    for (p, v) in pats.iter().zip(vals.iter()) {
        if !match_term_compiled(slots, p, v, table) { return false; }
    }
    true
}

fn sub_term_compiled(slots: &[ATerm], t: &ATerm, table: &mut TermTable) -> ATerm {
    match t.as_ref() {
        Term::Var(VarOp::Set(i) | VarOp::Check(i)) => slots[*i as usize].clone(),
        Term::Var(VarOp::Name(_)) => panic!("sub_term_compiled: uncompiled VarOp::Name"),
        Term::App(cons, args) => {
            let new_args: Vec<ATerm> = args.iter().map(|a| sub_term_compiled(slots, a, table)).collect();
            table.store(cons.clone(), new_args)
        }
        Term::Id(_) => t.clone(),  // already interned, pass through
        _ => t.clone(),  // Pred, Num, Blank, Str are unchanged
    }
}

fn sub_terms_compiled(slots: &[ATerm], ts: &[ATerm], table: &mut TermTable) -> Tuple {
    ts.iter().map(|t| sub_term_compiled(slots, t, table)).collect()
}

fn eval_flat(
    slots: &mut Vec<ATerm>,
    expr: &Vec<Expr>,
    tuples: &Tuples,
    check: &Tuples,
    table: &mut TermTable,
) -> Vec<Vec<ATerm>> {
    let mut bs = vec![];
    eval_flat0(0, slots, &expr, tuples, check, &mut bs, table);
    bs
}

fn eval_flat0(
    idx: usize,
    slots: &mut Vec<ATerm>,
    expr: &Vec<Expr>,
    tuples: &Tuples,
    check: &Tuples,
    result: &mut Vec<Vec<ATerm>>,
    table: &mut TermTable,
) {
    if idx == expr.len() {
        result.push(slots.clone());
        return;
    }

    match &expr[idx] {
        Expr::Atom(pat) => {
            let pred = match pat[0].as_ref() {
                Term::Pred(Name::Sym(s)) => *s,
                _ => panic!("compiled atom must start with Pred"),
            };
            let vs = &pat[1..];
            for stored_tuple in tuples.lookup(&pred) {
                if match_terms_compiled(slots, vs, stored_tuple, table) {
                    eval_flat0(idx+1, slots, expr, tuples, check, result, table);
                }
            }
        }
        Expr::Bind(x, y) => {
            let y_sub = sub_term_compiled(slots, y, table);
            match x.as_ref() {
                Term::Var(VarOp::Set(i)) => {
                    slots[*i as usize] = y_sub;
                    eval_flat0(idx+1, slots, expr, tuples, check, result, table);
                }
                Term::Var(VarOp::Check(i)) => {
                    if slots[*i as usize] == y_sub {
                        eval_flat0(idx+1, slots, expr, tuples, check, result, table);
                    }
                }
                _ => {
                    if match_term_compiled(slots, x, &y_sub, table) {
                        eval_flat0(idx+1, slots, expr, tuples, check, result, table);
                    }
                }
            }
        }
        Expr::NegAtom(at) => {
            let substituted: Tuple = sub_terms_compiled(slots, at, table);
            if !check.contains_tuple(&substituted) {
                eval_flat0(idx+1, slots, expr, tuples, check, result, table);
            }
        }
        Expr::Unit => eval_flat0(idx+1, slots, expr, tuples, check, result, table),
        Expr::Join(_, _) => panic!(""),
    }
}

// -- Precomputed specialization -----------------------------------------------

/// Walk an expression's Join tree and collect all ways to extract atom(s)
/// matching `pred` from it. Each result is a (pats, remaining) pair where
/// `pats` are the extracted atom patterns and `remaining` is what's left.
fn collect_extractions(
    val: &Expr, pred: Sym,
    k: &mut dyn FnMut(Vec<Tuple>, Expr),
) {
    match val {
        Expr::Unit | Expr::Bind(..) | Expr::NegAtom(..) => (),
        Expr::Atom(pat) => {
            if let Term::Pred(Name::Sym(sym)) = pat[0].as_ref() {
                if *sym == pred {
                    k(vec![pat.clone()], Expr::Unit);
                }
            }
        }
        Expr::Join(a, b) => {
            let a_expr = a.as_ref();
            let b_expr = b.as_ref();
            // Left only
            collect_extractions(a_expr, pred, &mut |pats, rest_a| {
                k(pats, join(rest_a, b_expr.clone()));
            });
            // Right only
            collect_extractions(b_expr, pred, &mut |pats, rest_b| {
                k(pats, join(a_expr.clone(), rest_b));
            });
            // Both: extract one atom from each side
            collect_extractions(a_expr, pred, &mut |pats_a, rest_a| {
                collect_extractions(b_expr, pred, &mut |pats_b, rest_b| {
                    let mut combined = pats_a.clone();
                    combined.extend(pats_b.clone());
                    k(combined, join(rest_a.clone(), rest_b));
                });
            });
        }
    }
}

/// Build precomputed specializations for all non-immediate rules.
/// Returns a map from predicate Sym to the list of SpecializedRules that match it.
pub fn prespecialize(rules: Vec<Rule>, interner: &Interner, reorder: bool) -> (Vec<SpecEntry>, HashMap<Sym, Vec<SpecializedRule>>) {
    let mut result: HashMap<Sym, Vec<SpecializedRule>> = HashMap::new();
    let mut immediate = Vec::new();

    for rule in rules {
        let preds = atom_predicates(&rule.body.val);
        if preds.len() == 0 {
            let mut seen: HashMap<Sym, u16> = HashMap::new();
            let mut next_slot: u16 = 0;
            let body2 = compile_expr(&rule.body.val, &mut seen, &mut next_slot);
            let chead: Vec<Tuple> = rule.head.iter().map(|tuple| {
                compile_tuple(tuple, &mut seen, &mut next_slot)
            }).collect();
            immediate.push(SpecEntry {
                pats: vec![],
                remaining: body2,
                num_slots: next_slot,
                head: chead,
            });
        } else {
            // non-trivial body
            for (pred_sym, _arity) in preds {
                let mut extractions: Vec<(Vec<Tuple>, Expr)> = Vec::new();
                collect_extractions(&rule.body.val, pred_sym, &mut |pats, remaining| {
                    extractions.push((pats, remaining));
                });

                if !extractions.is_empty() {
                    let mut final_entries = Vec::new();
                    for (pats, remaining) in &extractions {
                        let mut seen: HashMap<Sym, u16> = HashMap::new();
                        let mut next_slot: u16 = 0;

                        // TODO remove
                        for (sym, _) in &rule.body.ctx.entries {
                            if !seen.contains_key(sym) {
                                seen.insert(*sym, next_slot);
                                next_slot += 1;
                            }
                        }

                        let mut cpats = Vec::new();
                        for pat in pats {
                            cpats.push(compile_tuple(&pat[1..], &mut seen, &mut next_slot));
                        }

                        let mut bound: Vec<Name> = seen.keys().map(|&s| Name::Sym(s)).collect();
                        let optimized = if reorder { &optimize_with(&mut bound, remaining.clone(), interner) } else { remaining };
                        let cremaining = compile_expr(&optimized, &mut seen, &mut next_slot);

                        let chead: Vec<Tuple> = rule.head.iter().map(|tuple| {
                            compile_tuple(tuple, &mut seen, &mut next_slot)
                        }).collect();

                        final_entries.push(SpecEntry {
                            pats: cpats,
                            remaining: cremaining,
                            num_slots: next_slot,
                            head: chead,
                        });
                    }

                    result.entry(pred_sym).or_default().push(SpecializedRule {
                        entries: final_entries,
                    });
                }
            }
        }
    }
    (immediate, result)
}

pub fn eval_spec_entry(
    entry: &SpecEntry,
    t: &Tuple,
    ts: &Tuples,
    check: &Tuples,
    result: &mut Vec<Vec<Tuple>>,
    table: &mut TermTable,
) {
    let mut slots = vec![ablank(); entry.num_slots as usize];

    // Initialize slots from base_ctx
    // for (i, (_, val)) in entry.base_ctx.entries.iter().enumerate() {
    //     slots[i] = val.clone();
    // }

    // Match each compiled pat against the tuple (without pred)
    let mut ok = true;
    let t_rest = &t[1..]; // skip pred
    for cpat in &entry.pats {
        if !match_terms_compiled(&mut slots, cpat, t_rest, table) {
            ok = false;
            break;
        }
    }
    if ok {
        // Eval remaining
        for final_slots in eval_flat(&mut slots, &entry.remaining.flatten(), ts, check, table) {
            // Substitute head
            let head_tuples: Vec<Tuple> = entry.head.iter().map(|ht| {
                sub_terms_compiled(&final_slots, ht, table)
            }).collect();
            result.push(head_tuples);
        }
    }
}

/// Evaluate a compiled precomputed specialization against a concrete tuple.
/// `t` is the full tuple (with pred at [0]).
pub fn eval1_spec(
    spec: &SpecializedRule,
    t: &Tuple,
    ts: &Tuples,
    check: &Tuples,
    _intern: &Interner,
    table: &mut TermTable,
) -> Vec<Vec<Tuple>> {
    let mut results = Vec::new();

    for entry in &spec.entries {
        eval_spec_entry(entry, t, ts, check, &mut results, table);
    }
    results
}

// -- iter ---------------------------------------------------------------------

/// The fixpoint iteration loop.
/// f: for each tuple, produces new head tuples
/// worklist: FIFO queue of tuples to process
/// db: accumulated database
/// check: previous fixpoint (for negation)
/// Returns (db, changed) where changed is the set of new tuples not in base.
pub fn iter(
    f: &dyn Fn(&Tuple, &Tuples, &Tuples) -> Vec<Vec<Tuple>>,
    worklist: &mut Worklist,
    db: &mut Tuples,
    base: &Tuples,
    check: &Tuples,
) -> bool {
    let mut changed = false;
    // Mirror the Haskell Set worklist semantics: track all tuples ever
    // enqueued so we never enqueue the same tuple twice.
    let mut enqueued: HashSet<Tuple> = worklist.iter().cloned().collect();

    while let Some(t) = worklist.pop_front() {
        let new_thunks = f(&t, db, check);
        for head_tuples in &new_thunks {
            for tuple in head_tuples {
                if !db.contains_tuple(tuple) && !enqueued.contains(tuple) {
                    enqueued.insert(tuple.clone());
                    worklist.push_back(tuple.clone());
                    if !base.contains_tuple(tuple) {
                        changed = true;
                    }
                }
            }
        }
        db.add_one(&t);
    }

    changed
}

// -- altIter (alternating fixpoint for negation) ------------------------------

pub fn alt_iter(
    gas: usize,
    ts0: &HashSet<Tuple>,
    f: &dyn Fn(&Tuple, &Tuples, &Tuples) -> Vec<Vec<Tuple>>,
    v: &Tuples,
) -> Tuples {
    if gas == 0 {
        panic!("gas exhausted");
    }

    eprintln!("STEP: {}", gas);

    // First forward pass
    let mut wl1: Worklist = ts0.iter().cloned().collect();
    let mut db1 = Tuples::new();
    let gen1 = iter(f, &mut wl1, &mut db1, v, v);

    // Second forward pass
    let mut wl2: Worklist = ts0.iter().cloned().collect();
    let mut db2 = Tuples::new();
    let gen2 = iter(f, &mut wl2, &mut db2, v, &db1);

    if !gen1 {
        db1
    } else if !gen2 {
        db2
    } else {
        alt_iter(gas - 1, ts0, f, &db2)
    }
}

// -- iter_rules --------------------------------------------------

pub fn iter_rules(initial: HashSet<Tuple>, all_rules: Vec<Rule>, intern: &Interner, reorder: bool) -> (Tuples, TermTable) {
    let (start, specs) = prespecialize(all_rules, intern, reorder);

    let table = Rc::new(RefCell::new(TermTable::new()));

    let mut ts0 = initial;
    // Apply unit-body rules to get initial tuples
    {
        let mut tbl = table.borrow_mut();
        for rule in &start {
            let mut ts = Vec::new();
            eval_spec_entry(rule, &unit_tuple(), &Tuples::new(), &Tuples::new(), &mut ts, &mut tbl);
            for hts in ts {
                for t in hts {
                    ts0.insert(t);
                }
            }
        }
    }

    let table_clone = Rc::clone(&table);
    let f = move |t: &Tuple, old: &Tuples, check: &Tuples| -> Vec<Vec<Tuple>> {
        let pred = match t[0].as_ref() {
            Term::Pred(Name::Sym(sym)) => *sym,
            _ => return Vec::new(),
        };
        match specs.get(&pred) {
            Some(spec_rules) => {
                let mut tbl = table_clone.borrow_mut();
                let mut results = Vec::new();
                for spec_rule in spec_rules {
                    results.extend(eval1_spec(spec_rule, t, old, check, intern, &mut tbl));
                }
                results
            }
            None => Vec::new(),
        }
    };

    let tuples = alt_iter(10, &ts0, &f, &Tuples::new());
    drop(f);
    let tbl = Rc::try_unwrap(table).unwrap().into_inner();
    (tuples, tbl)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parse;
    use crate::sym::Interner;

    fn run(src: &str) -> (Tuples, TermTable) {
        let mut intern = Interner::new();
        let rules = parse::parse(src, &mut intern).expect("parse");
        iter_rules(HashSet::new(), rules, &intern, false)
    }

    /// Invariant 1: no Term::App appears in any output Tuple.
    #[test]
    fn test_no_app_in_tuples() {
        let (tuples, _table) = run("-- foo pair(1, 2).");
        for (_pred, set) in &tuples.relations {
            for tuple in set {
                for term in tuple {
                    assert!(
                        !matches!(term.as_ref(), Term::App(_, _)),
                        "found Term::App in output tuple: {:?}", term
                    );
                }
            }
        }
    }

    /// Invariant 2: every TermTable entry has only non-App args (flat).
    #[test]
    fn test_table_keys_are_flat() {
        let (_tuples, table) = run("-- foo bar(pair(triple(1,2),3)).");
        for entry in table.entries() {
            if let Term::App(_, args) = entry.as_ref() {
                for arg in args {
                    assert!(
                        !matches!(arg.as_ref(), Term::App(_, _)),
                        "found Term::App in TermTable entry args: {:?}", arg
                    );
                }
            }
        }
    }
}
