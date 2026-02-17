use std::collections::{HashMap, HashSet};

use crate::types::*;
use crate::sym::{Sym, Interner};
use crate::reset_binding;

// -- Unification --------------------------------------------------------------

/// Unify a pattern term against a value term, consuming the binding.
/// Returns None on failure, or the (possibly extended) binding on success.
pub fn unify_term(b: &mut Binding, pat: &ATerm, val: &ATerm) -> bool {
    match (pat.as_ref(), val.as_ref()) {
        (Term::Blank, _) | (_, Term::Blank) => true,
        (Term::Var(var), _) => b.try_extend(var.as_sym(), val),
        (Term::Pred(_), _) => {
            pat == val
        }
        (Term::Num(_), _) => {
            pat == val
        }
        (Term::Str(_), _) => {
            pat == val
        }
        (Term::App(cons1, ts1), Term::App(cons2, ts2)) => {
            if cons1 != cons2 {
                return false
            }
            unify_tuples(b, ts1, ts2)
        }
        (Term::App(..), _) => false,
    }
}

/// Unify two slices of ATerms element-wise, consuming the binding.
pub fn unify_tuples(b: &mut Binding, ts1: &[ATerm], ts2: &[ATerm]) -> bool {
    if ts1.len() != ts2.len() {
        return false;
    }
    for (t, v) in ts1.iter().zip(ts2.iter()) {
        if !unify_term(b, t, v) { return false; }
    }
    true
}

// -- Substitution -------------------------------------------------------------

pub fn sub_term(ctx: &Binding, t: &ATerm) -> ATerm {
    match t.as_ref() {
        Term::Var(n) => ctx.lookup(n.as_sym()).expect("unbound variable").clone(),
        Term::App(cons, args) => {
            let new_args: Vec<ATerm> = args.iter().map(|a| sub_term(ctx, a)).collect();
            // If nothing changed, reuse original term (zero allocation)
            if new_args.iter().zip(args.iter()).all(|(a, b)| aterm_ptr_eq(a, b)) {
                t.clone()
            } else {
                aapp(cons.clone(), new_args)
            }
        }
        Term::Blank => panic!("cannot substitute blank"),
        _ => t.clone(),
    }
}

pub fn subst(ctx: &Binding, tuple: &Tuple) -> Tuple {
    tuple.iter().map(|t| sub_term(ctx, t)).collect()
}

pub fn substs(ctx: &Binding, tuples: &[Tuple]) -> Vec<Tuple> {
    tuples.iter().map(|t| subst(ctx, t)).collect()
}

// -- Expression helpers -------------------------------------------------------

pub fn is_immediate(e: &Expr) -> bool {
    match e {
        Expr::Unit | Expr::Bind(..) => true,
        Expr::Join(a, b) => is_immediate(a) && is_immediate(b),
        Expr::Atom(..) | Expr::NegAtom(..) => false,
    }
}

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
pub fn optimize_with(bound: &mut Vec<Name>, val: Expr) -> Expr {
    fn extract_best_atom(bound: &[Name], expr: &Expr) -> Option<(Tuple, Expr)> {
        match expr {
            Expr::Atom(tuple) => Some((tuple.clone(), Expr::Unit)),
            Expr::Join(a, b) => {
                match (extract_best_atom(bound, a), extract_best_atom(bound, b)) {
                    (Some((lt, la)), Some((rt, ra))) => {
                        let l_score = count_shared(&tuple_vars(&lt), bound);
                        let r_score = count_shared(&tuple_vars(&rt), bound);
                        if l_score >= r_score {
                            Some((lt, join(la, *b.clone())))
                        } else {
                            Some((rt, join(*a.clone(), ra)))
                        }
                    }
                    (Some((t, rest)), None) => Some((t, join(rest, *b.clone()))),
                    (None, Some((t, rest))) => Some((t, join(*a.clone(), rest))),
                    (None, None) => None,
                }
            }
            _ => None,
        }
    }

    let mut remaining = val;
    let mut result = Expr::Unit;

    while let Some((atom, rest)) = extract_best_atom(bound, &remaining) {
        let atom_vars = tuple_vars(&atom);
        for v in atom_vars {
            if !bound.contains(&v) {
                bound.push(v);
            }
        }
        result = join(result, Expr::Atom(atom));
        remaining = rest;
    }

    join(result, remaining)
}

pub fn optimize(ctx: &Binding, val: Expr) -> Expr {
    optimize_with(&mut ctx.bound_vars(), val)
}
/// specialize (Closure _ Unit) _ = []
/// specialize (Closure _ Bind{}) _ = []
/// specialize (Closure _ NegAtom{}) _ = []
/// specialize (Closure b (Atom pat)) tuple = ...
/// specialize (Closure c (Join a b)) tuple = left ++ right ++ both
pub fn specialize_(ctx: &mut Binding, val: &Expr, tuple: &Tuple, k: &mut dyn FnMut(&mut Binding, &Expr) ) {
    match val {
        Expr::Unit | Expr::Bind(..) | Expr::NegAtom(..) => (),
        Expr::Atom(pat) => {
            reset_binding!(ctx,
                if unify_tuples(ctx, pat, tuple) {
                    k(ctx, &Expr::Unit);
                }
            );
        }
        Expr::Join(a, b) => {
            let a_expr = a.as_ref();
            let b_expr = b.as_ref();

            // todo: with ctx
            reset_binding!(ctx,
                specialize_(ctx, a_expr, tuple, &mut |c2, a2| {
                    let e = optimize(c2, join(a2.clone(), b_expr.clone()));
                    k(c2, &e);
                })
            );
            reset_binding!(ctx,
                specialize_(ctx, b_expr, tuple, &mut |c2, b2| {
                    let e = optimize(c2, join(a_expr.clone(), b2.clone()));
                    k(c2, &e);
                })
            );
            reset_binding!(ctx,
                specialize_(ctx, a_expr, tuple, &mut |c2, a2| {
                    specialize_(c2, b_expr, tuple, &mut |c3, b2| {
                        k(c3, &join(a2.clone(), b2.clone()));
                    });
                })
            );
        }
    }
}
// -- Eval ---------------------------------------------------------------------

/// eval (Closure b Unit) _ _ = [b]
/// eval (Closure b (Bind x y)) _ _ = maybeToList $ B.unify b x (subTerm (bind b) y)
/// eval (Closure b (SpecialAtom p ts)) _ _ = evalBuiltin b p ts
/// eval (Closure c (Atom (TermPred p : vs))) (Tuples tuples) _ = ...
/// eval (Closure b (NegAtom at)) _ check = ...
/// eval (Closure c (Join a b)) tuples check = ...

pub fn eval_(ctx : &mut Binding, val: &Expr, tuples: &Tuples, check: &Tuples, intern: &crate::sym::Interner,
             k: &mut dyn FnMut(&mut Binding) ) {
    match val {
        Expr::Unit => k(ctx),
        Expr::Bind(x, y) => {
            let y_sub = sub_term(ctx, y);
            reset_binding!(ctx,
                if unify_term(ctx, x, &y_sub) {
                    k(ctx);
                }
            );
        }
        Expr::Atom(pat) => {
            if pat.is_empty() {
                panic!("empty atom in eval");
            }
            match pat[0].as_ref() {
                Term::Pred(Name::Sym(sym)) => {
                    let vs = &pat[1..];
                    for stored_tuple in tuples.lookup(sym) {
                        reset_binding!(ctx,
                            if unify_tuples(ctx, vs, stored_tuple) {
                                k(ctx);
                            }
                        );
                    }
                }
                Term::Pred(Name::Str(pred_str)) => {
                    if pred_str.starts_with('#') {
                        let op_name = &pred_str[1..];
                        // todo check this
                        for c in eval_builtin_str(ctx, op_name, &pat[1..], intern).iter_mut() {
                            k(c);
                        }
                    }
                    panic!("non-interned string: {}", pred_str);
                }
                _ => panic!("atom must start with Pred. saw: {:?}", *pat),
            }
        }
        Expr::NegAtom(at) => {
            let substituted = subst(ctx, at);
            if matches!(substituted[0].as_ref(), Term::Blank) {
                panic!("negatom substituted to blank pred");
            }
            if !check.contains_tuple(&substituted) {
                k(ctx);
            }
        }
        Expr::Join(a, b) => {
            eval_(ctx, &a, tuples, check, intern, &mut |c2| {
                eval_(c2, &b, tuples, check, intern, &mut |c3| {
                    k(c3);
                });
            });
        }
    }
}
pub fn eval(cl: &Closure, tuples: &Tuples, check: &Tuples, intern: &crate::sym::Interner) -> Vec<Binding> {
    let mut result = Vec::new();
    eval_(&mut cl.ctx.clone(), &cl.val, tuples, check, intern, &mut |t| { result.push(t.clone()) });
    result
}

fn eval_builtin_str(b: &Binding, op: &str, args: &[ATerm], intern: &crate::sym::Interner) -> Vec<Binding> {
    match op {
        "range" => {
            // evalBuiltin b "range" [_, t, TermNum lo, TermNum hi]
            if args.len() != 4 { panic!("range expects 4 args, got {}", args.len()); }
            let t = &args[1];
            let lo = match args[2].as_ref() { Term::Num(n) => *n, _ => panic!("range: lo must be num") };
            let hi = match args[3].as_ref() { Term::Num(n) => *n, _ => panic!("range: hi must be num") };
            let mut results = Vec::new();
            for i in lo..=hi {
                let num = anum(i);
                let mut b2 = b.clone();
                if unify_term(&mut b2, t, &num) {
                    results.push(b2);
                }
            }
            results
        }
        "lt" => {
            if args.len() != 2 { panic!("lt expects 2 args"); }
            let a = sub_term(b, &args[0]);
            let bterm = sub_term(b, &args[1]);
            fn chk_str(bd: &Binding, a: &ATerm, bt: &ATerm, intern: &crate::sym::Interner) -> Vec<Binding> {
                match (a.as_ref(), bt.as_ref()) {
                    (_, Term::App(cons, _)) if cons.resolve(intern) == "z" => vec![],
                    (Term::App(cons, _), _) if cons.resolve(intern) == "z" => vec![bd.clone()],
                    (Term::App(sc, ts), Term::App(sc2, ts2))
                        if sc.resolve(intern) == "s" && sc2.resolve(intern) == "s" =>
                    {
                        chk_str(bd, &ts[0], &ts2[0], intern)
                    }
                    _ => panic!("lt: unexpected terms"),
                }
            }
            chk_str(b, &a, &bterm, intern)
        }
        _ => panic!("unimplemented builtin: #{}", op),
    }
}

// -- eval1, stepRule, evalRule -------------------------------------------------

pub fn eval1(cl: &Closure, t: &Tuple, ts: &Tuples, check: &Tuples, intern: &crate::sym::Interner) -> Vec<Binding> {
    let mut results = Vec::new();
    specialize_(&mut cl.ctx.clone(), &cl.val, t, &mut |c2, e| {
        eval_(c2, e, ts, check, intern, &mut |c3| {
            results.push(c3.clone());
        });
    });
    results
}

pub fn step_rule(rule: &Rule, t: &Tuple, ts: &Tuples, check: &Tuples, intern: &crate::sym::Interner) -> Vec<Vec<Tuple>> {
    let mut results = Vec::new();
    for b in eval1(&rule.body, t, ts, check, intern) {
        results.push(substs(&b, &rule.head));
    }
    results
}

pub fn eval_rule(rule: &Rule, ts: &Tuples, check: &Tuples, intern: &crate::sym::Interner) -> Vec<Vec<Tuple>> {
    let mut results = Vec::new();
    for b in eval(&rule.body, ts, check, intern) {
        results.push(substs(&b, &rule.head));
    }
    results
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
pub fn prespecialize(rules: &[&Rule]) -> HashMap<Sym, Vec<SpecializedRule>> {
    let mut result: HashMap<Sym, Vec<SpecializedRule>> = HashMap::new();

    for rule in rules {
        let preds = atom_predicates(&rule.body.val);
        let base_bound = rule.body.ctx.bound_vars();
        for (pred_sym, _arity) in preds {
            let mut entries = Vec::new();
            collect_extractions(&rule.body.val, pred_sym, &mut |pats, remaining| {
                // let mut bound = base_bound.clone();
                // for p in &pats {
                //     for v in tuple_vars(p) {
                //         if !bound.contains(&v) { bound.push(v); }
                //     }
                // }
                // let remaining = optimize_with(&mut bound, remaining);
                entries.push(SpecEntry { pats, remaining });
            });

            if !entries.is_empty() {
                result.entry(pred_sym).or_default().push(SpecializedRule {
                    entries,
                    base_ctx: rule.body.ctx.clone(),
                    head: rule.head.clone(),
                });
            }
        }
    }
    result
}

/// Evaluate a precomputed specialization against a concrete tuple.
/// `t` is the full tuple (with pred at [0]).
pub fn eval1_spec(
    spec: &SpecializedRule,
    t: &Tuple,
    ts: &Tuples,
    check: &Tuples,
    intern: &Interner,
) -> Vec<Vec<Tuple>> {
    let mut results = Vec::new();
    for entry in &spec.entries {
        let mut ctx = spec.base_ctx.clone();
        // Unify each atom pattern against the tuple
        let mut ok = true;
        let save = ctx.entries.len();
        for pat in &entry.pats {
            if !unify_tuples(&mut ctx, pat, t) {
                ok = false;
                break;
            }
        }
        if !ok {
            ctx.entries.truncate(save);
            continue;
        }
        eval_(&mut ctx, &entry.remaining, ts, check, intern, &mut |c3| {
            results.push(substs(c3, &spec.head));
        });
        ctx.entries.truncate(save);
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

// -- apply_rules, iter_rules --------------------------------------------------

pub fn apply_rules(rules: &[Rule], ts: &Tuples, intern: &crate::sym::Interner) -> HashSet<Tuple> {
    let mut result = HashSet::new();
    for rule in rules {
        for head_tuples in eval_rule(rule, ts, &Tuples::new(), intern) {
            for t in head_tuples {
                result.insert(t);
            }
        }
    }
    result
}

pub fn iter_rules(initial: HashSet<Tuple>, all_rules: &[Rule], intern: &Interner) -> Tuples {
    let (start, rest): (Vec<&Rule>, Vec<&Rule>) = all_rules.iter().partition(|r| is_immediate(&r.body.val));

    let mut ts0 = initial;
    // Apply unit-body rules to get initial tuples
    for rule in &start {
        for head_tuples in eval_rule(rule, &Tuples::new(), &Tuples::new(), intern) {
            for t in head_tuples {
                ts0.insert(t);
            }
        }
    }

    let specs = prespecialize(&rest);

    let f = move |t: &Tuple, old: &Tuples, check: &Tuples| -> Vec<Vec<Tuple>> {
        let pred = match t[0].as_ref() {
            Term::Pred(Name::Sym(sym)) => *sym,
            _ => return Vec::new(),
        };
        match specs.get(&pred) {
            Some(spec_rules) => {
                let mut results = Vec::new();
                for spec_rule in spec_rules {
                    results.extend(eval1_spec(spec_rule, t, old, check, intern));
                }
                results
            }
            None => Vec::new(),
        }
    };

    alt_iter(10, &ts0, &f, &Tuples::new())
}
