use std::collections::{HashMap, HashSet};
use std::rc::Rc;

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

// -- Runtime statistics -------------------------------------------------------

#[derive(Debug)]
pub struct EvalStats {
    /// Times the ground-lookup path ran (line 307), keyed by predicate sym.
    pub ground: HashMap<Sym, u64>,
    /// Times match_terms_compiled was called in the scan path (line 315), keyed by predicate sym.
    pub scan: HashMap<Sym, u64>,
}

impl EvalStats {
    pub fn new() -> Self {
        EvalStats { ground: HashMap::new(), scan: HashMap::new() }
    }
}

// -- eval_rule ----------------------------------------------------------------

// pub fn eval_rule(rule: &Rule, ts: &Tuples, check: &Tuples, table: &mut TermTable, stats: &mut EvalStats, is_sym: Option<Sym>) -> Vec<Vec<Tuple>> {
//     let mut results = Vec::new();
//     let mut slots = vec![ablank(); 30]; // TODO
//     for final_slots in eval_flat(&mut slots, &rule.body.val.flatten(), ts, check, table, stats, is_sym) {
//         // Substitute head
//         let head_tuples: Vec<Tuple> = rule.head.iter().map(|ht| {
//             sub_terms_compiled(&final_slots, ht, table)
//         }).collect();
//         results.push(head_tuples);
//     }
//     results
// }

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
        Term::Choice(inner) => achoice(compile_term(inner, seen, next_slot)),
        Term::BinOp(op, l, r) => abinop(
            op.clone(),
            compile_term(l, seen, next_slot),
            compile_term(r, seen, next_slot),
        ),
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

fn is_groundable(t: &ATerm) -> bool {
    match t.as_ref() {
        Term::Var(VarOp::Set(_)) | Term::Blank | Term::Choice(_) => false,
        Term::App(_, args) => args.iter().all(is_groundable),
        Term::BinOp(_, l, r) => is_groundable(l) && is_groundable(r),
        _ => true,
    }
}

enum AtomLookup {
    AllBound,
    SomeIndex(usize),
    None,
}

/// Decide how to evaluate an atom with pattern `vs` against `tuples`.
fn term_is_groundable(vs: &[ATerm], pred: Sym, tuples: &Tuples) -> AtomLookup {
    if vs.iter().all(is_groundable) {
        return AtomLookup::AllBound;
    }
    for (i, v) in vs.iter().enumerate() {
        if is_groundable(v) && tuples.indices.contains_key(&(pred, i)) {
            return AtomLookup::SomeIndex(i);
        }
    }
    AtomLookup::None
}

fn match_term_compiled(slots: &mut Vec<ATerm>, pat: &ATerm, val: &ATerm, check: &Tuples, is_sym: Option<Sym>, table: &TermTable) -> bool {
    // Handle Choice cases before dispatching on pat alone
    match (pat.as_ref(), val.as_ref()) {
        (Term::Choice(pt), Term::Choice(vt)) => {
            return match_term_compiled(slots, pt, vt, check, is_sym, table);
        }
        (Term::Choice(_), _) => return false,
        (_, Term::Choice(key)) => {
            if let Some(sym) = is_sym {
                for tuple in check.lookup(&sym) {
                    if tuple.len() >= 2 && tuple[0] == *key {
                        let v = &tuple[1];
                        return match_term_compiled(slots, pat, v, check, is_sym, table);
                    }
                }
            }
            return false;
        }
        _ => {}
    }
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
                        if !match_term_compiled(slots, cp, av, check, is_sym, table) {
                            return false;
                        }
                    }
                    true
                }
                _ => false,
            }
        }
        Term::Id(_) => panic!("match_term_compiled: Term::Id in pattern position"),
        Term::Choice(_) => unreachable!("Choice handled above"),
        Term::BinOp(_, _, _) => panic!("match_term_compiled: BinOp in pattern position (should have been evaluated)"),
    }
}

fn match_terms_compiled(slots: &mut Vec<ATerm>, pattern: &[ATerm], tuple: &[ATerm], check: &Tuples, is_sym: Option<Sym>, table: &TermTable) -> bool {
    if pattern.len() != tuple.len() { return false; }
    for (p, v) in pattern.iter().zip(tuple.iter()) {
        if !match_term_compiled(slots, p, v, check, is_sym, table) { return false; }
    }
    true
}

fn eval_binop(op: &BinOp, l: &ATerm, r: &ATerm) -> ATerm {
    match (l.as_ref(), r.as_ref()) {
        (Term::Num(a), Term::Num(b)) => anum(match op {
            BinOp::Plus  => a + b,
            BinOp::Minus => a - b,
            BinOp::Times => a * b,
            BinOp::Div   => a / b,
        }),
        _ => panic!("eval_binop: operands did not evaluate to Num"),
    }
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
        Term::Choice(inner) => achoice(sub_term_compiled(slots, inner, table)),
        Term::BinOp(op, l, r) => {
            let l2 = sub_term_compiled(slots, l, table);
            let r2 = sub_term_compiled(slots, r, table);
            eval_binop(op, &l2, &r2)
        }
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
    stats: &mut EvalStats,
    is_sym: Option<Sym>,
) -> Vec<Vec<ATerm>> {
    let mut bs = vec![];
    eval_flat0(0, slots, &expr, tuples, check, &mut bs, table, stats, is_sym);
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
    stats: &mut EvalStats,
    is_sym: Option<Sym>,
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
            // NOTE: Stale slot values across invocations are safe because the compiler
            // guarantees every `Check(i)` is dominated by a `Set(i)` within the same evaluation path.
            match term_is_groundable(vs, pred, tuples) {
                AtomLookup::AllBound => {
                    *stats.ground.entry(pred).or_insert(0) += 1;
                    let key = sub_terms_compiled(slots, vs, table);
                    if tuples.contains(pred, &key) {
                        eval_flat0(idx+1, slots, expr, tuples, check, result, table, stats, is_sym);
                    }
                }
                AtomLookup::SomeIndex(i) => {
                    let val = sub_term_compiled(slots, &vs[i], table);
                    for stored_tuple in tuples.lookup_col(pred, i, &val) {
                        *stats.scan.entry(pred).or_insert(0) += 1;
                        if match_terms_compiled(slots, vs, stored_tuple, check, is_sym, table) {
                            eval_flat0(idx+1, slots, expr, tuples, check, result, table, stats, is_sym);
                        }
                    }
                }
                AtomLookup::None => {
                    for stored_tuple in tuples.lookup(&pred) {
                        *stats.scan.entry(pred).or_insert(0) += 1;
                        if match_terms_compiled(slots, vs, stored_tuple, check, is_sym, table) {
                            eval_flat0(idx+1, slots, expr, tuples, check, result, table, stats, is_sym);
                        }
                    }
                }
            }
        }
        Expr::Bind(x, y) => {
            let y_sub = sub_term_compiled(slots, y, table);
            match x.as_ref() {
                Term::Var(VarOp::Set(i)) => {
                    slots[*i as usize] = y_sub;
                    eval_flat0(idx+1, slots, expr, tuples, check, result, table, stats, is_sym);
                }
                Term::Var(VarOp::Check(i)) => {
                    if slots[*i as usize] == y_sub {
                        eval_flat0(idx+1, slots, expr, tuples, check, result, table, stats, is_sym);
                    }
                }
                _ => {
                    if match_term_compiled(slots, x, &y_sub, check, is_sym, table) {
                        eval_flat0(idx+1, slots, expr, tuples, check, result, table, stats, is_sym);
                    }
                }
            }
        }
        Expr::NegAtom(pat) => {
            let pred = match pat[0].as_ref() {
                Term::Pred(Name::Sym(s)) => *s,
                _ => panic!("compiled atom must start with Pred"),
            };
            let vs = &pat[1..];
            match term_is_groundable(vs, pred, tuples) {
                AtomLookup::AllBound => {
                    let substituted: Tuple = sub_terms_compiled(slots, pat, table);
                    if !check.contains_tuple(&substituted) {
                        eval_flat0(idx+1, slots, expr, tuples, check, result, table, stats, is_sym);
                    }
                }
                _ => {
                    if !check.lookup(&pred).any(|stored_tuple| {
                        *stats.scan.entry(pred).or_insert(0) += 1;
                        match_terms_compiled(slots, vs, stored_tuple, tuples, is_sym, table)
                    }) {
                        eval_flat0(idx+1, slots, expr, tuples, check, result, table, stats, is_sym);
                    }
                }
            }
        }
        Expr::Unit => eval_flat0(idx+1, slots, expr, tuples, check, result, table, stats, is_sym),
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
                slots: vec![ablank(); next_slot as usize],
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
                            slots: vec![ablank(); next_slot as usize],
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
    entry: &mut SpecEntry,
    t: &Tuple,
    ts: &Tuples,
    check: &Tuples,
    result: &mut Vec<Vec<Tuple>>,
    table: &mut TermTable,
    stats: &mut EvalStats,
    is_sym: Option<Sym>,
) {
    let slots = &mut entry.slots;

    // Initialize slots from base_ctx
    // for (i, (_, val)) in entry.base_ctx.entries.iter().enumerate() {
    //     slots[i] = val.clone();
    // }

    // Match each compiled pat against the tuple (without pred)
    let mut ok = true;
    let t_rest = &t[1..]; // skip pred
    for cpat in &entry.pats {
        if !match_terms_compiled(slots, cpat, t_rest, check, is_sym, table) {
            ok = false;
            break;
        }
    }
    if ok {
        // Eval remaining
        for final_slots in eval_flat(slots, &entry.remaining.flatten(), ts, check, table, stats, is_sym) {
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
    spec: &mut SpecializedRule,
    t: &Tuple,
    ts: &Tuples,
    check: &Tuples,
    _intern: &Interner,
    table: &mut TermTable,
    stats: &mut EvalStats,
    is_sym: Option<Sym>,
) -> Vec<Vec<Tuple>> {
    let mut results = Vec::new();

    for entry in &mut spec.entries {
        eval_spec_entry(entry, t, ts, check, &mut results, table, stats, is_sym);
    }
    results
}

// -- iter ---------------------------------------------------------------------

/// The fixpoint iteration loop.
/// worklist: FIFO queue of tuples to process
/// db: accumulated database
/// check: previous fixpoint (for negation)
/// Returns (db, changed) where changed is the set of new tuples not in base.
pub fn iter(
    specs: &mut HashMap<Sym, Vec<SpecializedRule>>,
    worklist: &mut Worklist,
    db: &mut Tuples,
    base: &Tuples,
    check: &Tuples,
    table: &mut TermTable,
    stats: &mut EvalStats,
    intern: &Interner,
    is_sym: Option<Sym>,
) -> bool {
    let mut changed = false;

    while let Some(t) = worklist.pop_front() {
        if !db.contains_tuple(&t) {
            let new_thunks = {
                let pred = match t[0].as_ref() {
                    Term::Pred(Name::Sym(sym)) => *sym,
                    _ => { db.add_one(&t); continue; }
                };
                match specs.get_mut(&pred) {
                    Some(spec_rules) => {
                        let mut results = Vec::new();
                        for spec_rule in spec_rules {
                            results.extend(eval1_spec(spec_rule, &t, db, check, intern, table, stats, is_sym));
                        }
                        results
                    }
                    None => Vec::new(),
                }
            };
            for head_tuples in &new_thunks {
                for tuple in head_tuples {
                    if !db.contains_tuple(tuple) {
                        worklist.push_back(tuple.clone());
                        if !base.contains_tuple(tuple) { changed = true; }
                    }
                }
            }
            db.add_one(&t);
        }
    }

    changed
}

// -- altIter (alternating fixpoint for negation) ------------------------------

pub fn alt_iter(
    gas: usize,
    ts0: &HashSet<Tuple>,
    specs: &mut HashMap<Sym, Vec<SpecializedRule>>,
    v: &Tuples,
    table: &mut TermTable,
    stats: &mut EvalStats,
    intern: &Interner,
    is_sym: Option<Sym>,
) -> Tuples {
    if gas == 0 {
        panic!("gas exhausted");
    }

    eprintln!("STEP: {}", gas);

    // First forward pass
    let mut wl1: Worklist = ts0.iter().cloned().collect();
    let mut db1 = v.empty_clone();
    let _gen1 = iter(specs, &mut wl1, &mut db1, v, v, table, stats, intern, is_sym); // on first run: everything treated as false
                                                  // yields over-approx of solution

    // eprintln!("db1({}): {}", gen1, db1.pp_derp(intern));

    // Second forward pass
    // Note: we always do pass 2 even when gen1=false, because Choice resolution
    // uses `check` (the stable previous fixpoint) and needs pass 2 to activate.
    let mut wl2: Worklist = ts0.iter().cloned().collect();
    let mut db2 = v.empty_clone();
    let gen2 = iter(specs, &mut wl2, &mut db2, v, &db1, table, stats, intern, is_sym); // anything outside db1 (over-approx) treated as false.
                                                     // yields under-approx of solution

    // eprintln!("db2({}): {}", gen2, db2.pp_derp(intern));
    if !gen2 { return db2 };

    alt_iter(gas - 1, ts0, specs, &db2, table, stats, intern, is_sym)
}

// -- iter_rules --------------------------------------------------

pub fn iter_rules(initial: HashSet<Tuple>, all_rules: Vec<Rule>, intern: &Interner, reorder: bool, index_specs: Vec<(Sym, usize)>) -> (Tuples, TermTable, EvalStats) {
    let (mut start, mut specs) = prespecialize(all_rules, intern, reorder);
    let is_sym = intern.get("is");

    let mut table = TermTable::new();
    let mut stats = EvalStats::new();

    let mut ts0 = initial;
    // Apply unit-body rules to get initial tuples
    for rule in &mut start {
        let mut ts = Vec::new();
        eval_spec_entry(rule, &unit_tuple(), &Tuples::new(), &Tuples::new(), &mut ts, &mut table, &mut stats, is_sym);
        for hts in ts {
            for t in hts {
                ts0.insert(t);
            }
        }
    }

    let template = Tuples::with_indices(index_specs);
    let tuples = alt_iter(10, &ts0, &mut specs, &template, &mut table, &mut stats, intern, is_sym);
    (tuples, table, stats)
}

