use std::collections::HashSet;
use std::sync::Arc;

use crate::types::*;

// -- Unification --------------------------------------------------------------

/// Unify a pattern term against a value term within a binding context.
/// Returns None on failure.
pub fn unify_term(b: &Binding, pat: &Term, val: &Term) -> Option<Binding> {
    match (pat, val) {
        (Term::Blank, _) | (_, Term::Blank) => Some(b.clone()),
        (Term::Var(var), v) => b.try_extend(*var, v),
        (Term::Pred(_), _) => {
            if pat == val { Some(b.clone()) } else { None }
        }
        (Term::Num(_), _) => {
            if pat == val { Some(b.clone()) } else { None }
        }
        (Term::Str(_), _) => {
            if pat == val { Some(b.clone()) } else { None }
        }
        (Term::App(cons, ts), Term::App(cons2, ts2)) => {
            if cons != cons2 || ts.len() != ts2.len() {
                return None;
            }
            unify_tuples(b, ts, ts2)
        }
        (Term::App(..), _) => None,
    }
}

/// Unify two tuples element-wise.
pub fn unify_tuples(b: &Binding, ts1: &[Term], ts2: &[Term]) -> Option<Binding> {
    if ts1.len() != ts2.len() {
        return None;
    }
    let mut ctx = b.clone();
    for (t, v) in ts1.iter().zip(ts2.iter()) {
        ctx = unify_term(&ctx, t, v)?;
    }
    Some(ctx)
}

// -- Substitution -------------------------------------------------------------

pub fn sub_term(ctx: &Binding, t: &Term) -> Term {
    match t {
        Term::Var(n) => match ctx.lookup(*n) {
            Some(v) => v.clone(),
            None => panic!("unbound variable"),
        },
        Term::App(cons, ts) => {
            let ts2: Arc<[Term]> = ts.iter().map(|t| sub_term(ctx, t)).collect();
            Term::App(*cons, ts2)
        }
        Term::Blank => panic!("cannot substitute blank"),
        other => other.clone(),
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

pub fn join(a: Expr, b: Expr) -> Expr {
    match (&a, &b) {
        (Expr::Unit, _) => b,
        (_, Expr::Unit) => a,
        _ => Expr::Join(Box::new(a), Box::new(b)),
    }
}

pub fn atom(t: Tuple) -> Expr {
    if t.is_empty() {
        Expr::Unit
    } else {
        Expr::Atom(t)
    }
}

// -- Specialize ---------------------------------------------------------------

/// specialize (Closure _ Unit) _ = []
/// specialize (Closure _ Bind{}) _ = []
/// specialize (Closure _ NegAtom{}) _ = []
/// specialize (Closure b (Atom pat)) tuple = ...
/// specialize (Closure c (Join a b)) tuple = left ++ right ++ both
pub fn specialize(cl: &Closure, tuple: &Tuple) -> Vec<Closure> {
    match &cl.val {
        Expr::Unit | Expr::Bind(..) | Expr::NegAtom(..) => vec![],
        Expr::Atom(pat) => {
            match unify_tuples(&cl.ctx, pat, tuple) {
                Some(b2) => vec![Closure { ctx: b2, val: Expr::Unit }],
                None => vec![],
            }
        }
        Expr::Join(a, b) => {
            let spec = |ctx: &Binding, x: &Expr| -> Vec<Closure> {
                specialize(&Closure { ctx: ctx.clone(), val: x.clone() }, tuple)
            };

            let a_expr = a.as_ref();
            let b_expr = b.as_ref();

            // d(a b) = d(a) b  +  a d(b)  +  d(a) d(b)
            let mut results = Vec::new();

            // left: specialize a, keep b
            for Closure { ctx: c2, val: a2 } in spec(&cl.ctx, a_expr) {
                results.push(Closure { ctx: c2, val: join(a2, b_expr.clone()) });
            }

            // right: keep a, specialize b
            for Closure { ctx: c2, val: b2 } in spec(&cl.ctx, b_expr) {
                results.push(Closure { ctx: c2, val: join(a_expr.clone(), b2) });
            }

            // both: specialize a, then specialize b with updated context
            for Closure { ctx: c2, val: a2 } in spec(&cl.ctx, a_expr) {
                for Closure { ctx: c3, val: b2 } in spec(&c2, b_expr) {
                    results.push(Closure { ctx: c3, val: join(a2.clone(), b2) });
                }
            }

            results
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
pub fn eval(cl: &Closure, tuples: &Tuples, check: &Tuples, intern: &crate::sym::Interner) -> Vec<Binding> {
    match &cl.val {
        Expr::Unit => vec![cl.ctx.clone()],
        Expr::Bind(x, y) => {
            let y_sub = sub_term(&cl.ctx, y);
            match unify_term(&cl.ctx, x, &y_sub) {
                Some(b) => vec![b],
                None => vec![],
            }
        }
        Expr::Atom(pat) => {
            if pat.is_empty() {
                panic!("empty atom in eval");
            }
            match &pat[0] {
                Term::Pred(p) => {
                    let pred_str = intern.resolve(*p);
                    if pred_str.starts_with('#') {
                        // Special/builtin atom: strip '#' prefix to get op name
                        let op_name = &pred_str[1..];
                        // We need the Sym for the op name without '#'
                        // Since the interner is immutable here, look up using the full pred
                        // Actually let's just pass the sym and handle in eval_builtin
                        // The Haskell uses pattern SpecialAtom which strips '#'
                        // We need a mutable interner or pre-intern. Let's use the full string.
                        // For now, just use the resolved string directly.
                        return eval_builtin_str(&cl.ctx, op_name, &pat[1..], intern);
                    }
                    let vs = &pat[1..];
                    let mut results = Vec::new();
                    for stored_tuple in tuples.lookup(*p) {
                        for sp in specialize(
                            &Closure { ctx: cl.ctx.clone(), val: Expr::Atom(vs.into()) },
                            stored_tuple,
                        ) {
                            results.push(sp.ctx);
                        }
                    }
                    results
                }
                _ => panic!("atom must start with Pred"),
            }
        }
        Expr::NegAtom(at) => {
            let substituted = subst(&cl.ctx, at);
            if substituted[0] == Term::Blank {
                panic!("negatom substituted to blank pred");
            }
            if check.contains_tuple(&substituted) {
                vec![]
            } else {
                vec![cl.ctx.clone()]
            }
        }
        Expr::Join(a, b) => {
            let mut results = Vec::new();
            for c2 in eval(&Closure { ctx: cl.ctx.clone(), val: a.as_ref().clone() }, tuples, check, intern) {
                for c3 in eval(&Closure { ctx: c2, val: b.as_ref().clone() }, tuples, check, intern) {
                    results.push(c3);
                }
            }
            results
        }
    }
}

fn eval_builtin_str(b: &Binding, op: &str, args: &[Term], intern: &crate::sym::Interner) -> Vec<Binding> {
    match op {
        "range" => {
            // evalBuiltin b "range" [_, t, TermNum lo, TermNum hi]
            if args.len() != 4 { panic!("range expects 4 args, got {}", args.len()); }
            let t = &args[1];
            let lo = match &args[2] { Term::Num(n) => *n, _ => panic!("range: lo must be num") };
            let hi = match &args[3] { Term::Num(n) => *n, _ => panic!("range: hi must be num") };
            let mut results = Vec::new();
            for i in lo..=hi {
                if let Some(b2) = unify_term(b, t, &Term::Num(i)) {
                    results.push(b2);
                }
            }
            results
        }
        "lt" => {
            if args.len() != 2 { panic!("lt expects 2 args"); }
            let a = sub_term(b, &args[0]);
            let bterm = sub_term(b, &args[1]);
            fn chk_str(bd: &Binding, a: &Term, bt: &Term, intern: &crate::sym::Interner) -> Vec<Binding> {
                match (a, bt) {
                    (_, Term::App(cons, _)) if intern.resolve(*cons) == "z" => vec![],
                    (Term::App(cons, _), _) if intern.resolve(*cons) == "z" => vec![bd.clone()],
                    (Term::App(sc, ts), Term::App(sc2, ts2))
                        if intern.resolve(*sc) == "s" && intern.resolve(*sc2) == "s" =>
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
    for cl2 in specialize(cl, t) {
        for b in eval(&cl2, ts, check, intern) {
            results.push(b);
        }
    }
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
) -> HashSet<Tuple> {
    let mut changed: HashSet<Tuple> = HashSet::new();
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
                        changed.insert(tuple.clone());
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

    if gen1.is_empty() {
        db1
    } else if gen2.is_empty() {
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

pub fn iter_rules(initial: HashSet<Tuple>, all_rules: &[Rule], intern: &crate::sym::Interner) -> Tuples {
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

    let f = move |t: &Tuple, old: &Tuples, check: &Tuples| -> Vec<Vec<Tuple>> {
        let mut results = Vec::new();
        for rule in &rest {
            results.extend(step_rule(rule, t, old, check, intern));
        }
        results
    };

    alt_iter(10, &ts0, &f, &Tuples::new())
}
