use std::collections::HashSet;

use crate::types::*;

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
            let mut c = cl.ctx.clone();
            if unify_tuples(&mut c, pat, tuple) {
                vec![Closure { ctx: c, val: Expr::Unit }]
            } else {
                vec![]
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
            let mut b = cl.ctx.clone();
            if unify_term(&mut b, x, &y_sub) {
                vec![b]
            } else {
                vec![]
            }
        }
        Expr::Atom(pat) => {
            if pat.is_empty() {
                panic!("empty atom in eval");
            }
            match pat[0].as_ref() {
                Term::Pred(p) => {
                    let sym = p.as_sym();
                    let pred_str = intern.resolve(sym);
                    if pred_str.starts_with('#') {
                        let op_name = &pred_str[1..];
                        return eval_builtin_str(&cl.ctx, op_name, &pat[1..], intern);
                    }
                    let vs = &pat[1..];
                    let mut results = Vec::new();
                    let mut c = cl.ctx.clone();
                    for stored_tuple in tuples.lookup(sym) {
                        c.push();
                        if unify_tuples(&mut c, vs, stored_tuple) {
                            results.push(c.clone());
                        }
                        c.pop();
                    }
                    results
                }
                _ => panic!("atom must start with Pred"),
            }
        }
        Expr::NegAtom(at) => {
            let substituted = subst(&cl.ctx, at);
            if matches!(substituted[0].as_ref(), Term::Blank) {
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
