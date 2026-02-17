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

// -- Compiled expression compilation ------------------------------------------

fn compile_term(t: &ATerm, seen: &mut HashMap<Sym, u16>, next_slot: &mut u16) -> CTerm {
    match t.as_ref() {
        Term::Var(name) => {
            let sym = name.as_sym();
            if let Some(&slot) = seen.get(&sym) {
                CTerm::Var(VarOp::Check(slot))
            } else {
                let slot = *next_slot;
                seen.insert(sym, slot);
                *next_slot += 1;
                CTerm::Var(VarOp::Set(slot))
            }
        }
        Term::Pred(n) => CTerm::Pred(n.clone()),
        Term::Num(n) => CTerm::Num(*n),
        Term::Blank => CTerm::Blank,
        Term::App(cons, args) => {
            let cargs: Vec<CTerm> = args.iter().map(|a| compile_term(a, seen, next_slot)).collect();
            CTerm::App(cons.clone(), cargs)
        }
        Term::Str(n) => CTerm::Str(n.clone()),
    }
}

fn compile_tuple(t: &[ATerm], seen: &mut HashMap<Sym, u16>, next_slot: &mut u16) -> Vec<CTerm> {
    t.iter().map(|a| compile_term(a, seen, next_slot)).collect()
}

fn compile_expr(expr: &Expr, seen: &mut HashMap<Sym, u16>, next_slot: &mut u16) -> CExpr {
    match expr {
        Expr::Unit => CExpr::Unit,
        Expr::Atom(pat) => {
            // Extract pred sym from pat[0], compile the rest
            let pred_sym = match pat[0].as_ref() {
                Term::Pred(Name::Sym(s)) => *s,
                _ => panic!("atom must start with Pred"),
            };
            let cterms = compile_tuple(&pat[1..], seen, next_slot);
            CExpr::Atom(pred_sym, cterms)
        }
        Expr::NegAtom(at) => {
            let cterms = compile_tuple(at, seen, next_slot);
            CExpr::NegAtom(cterms)
        }
        Expr::Bind(x, y) => {
            // y is evaluated first (substituted), then unified with x
            let cy = compile_term(y, seen, next_slot);
            let cx = compile_term(x, seen, next_slot);
            CExpr::Bind(cx, cy)
        }
        Expr::Join(a, b) => {
            let ca = compile_expr(a, seen, next_slot);
            let cb = compile_expr(b, seen, next_slot);
            match (&ca, &cb) {
                (CExpr::Unit, _) => cb,
                (_, CExpr::Unit) => ca,
                _ => CExpr::Join(Box::new(ca), Box::new(cb)),
            }
        }
    }
}

// -- Compiled expression evaluation -------------------------------------------

fn match_cterm(slots: &mut Vec<ATerm>, pat: &CTerm, val: &ATerm) -> bool {
    match pat {
        CTerm::Var(VarOp::Set(i)) => {
            slots[*i as usize] = val.clone();
            true
        }
        CTerm::Var(VarOp::Check(i)) => slots[*i as usize] == *val,
        CTerm::Pred(n) => matches!(val.as_ref(), Term::Pred(n2) if n == n2),
        CTerm::Num(n) => matches!(val.as_ref(), Term::Num(n2) if n == n2),
        CTerm::Str(n) => matches!(val.as_ref(), Term::Str(n2) if n == n2),
        CTerm::Blank => true,
        CTerm::App(cons, args) => {
            match val.as_ref() {
                Term::App(cons2, args2) if cons == cons2 && args.len() == args2.len() => {
                    for (cp, av) in args.iter().zip(args2.iter()) {
                        if !match_cterm(slots, cp, av) {
                            return false;
                        }
                    }
                    true
                }
                _ => false,
            }
        }
    }
}

fn match_cterms(slots: &mut Vec<ATerm>, pats: &[CTerm], vals: &[ATerm]) -> bool {
    if pats.len() != vals.len() { return false; }
    for (p, v) in pats.iter().zip(vals.iter()) {
        if !match_cterm(slots, p, v) { return false; }
    }
    true
}

fn sub_cterm(slots: &[ATerm], t: &CTerm) -> ATerm {
    match t {
        CTerm::Var(VarOp::Set(i) | VarOp::Check(i)) => slots[*i as usize].clone(),
        CTerm::Pred(n) => apred(n.clone()),
        CTerm::Num(n) => anum(*n),
        CTerm::Blank => ablank(),
        CTerm::Str(n) => astr(n.clone()),
        CTerm::App(cons, args) => {
            let new_args: Vec<ATerm> = args.iter().map(|a| sub_cterm(slots, a)).collect();
            aapp(cons.clone(), new_args)
        }
    }
}

fn sub_cterms(slots: &[ATerm], ts: &[CTerm]) -> Tuple {
    ts.iter().map(|t| sub_cterm(slots, t)).collect()
}

fn eval_compiled(
    slots: &mut Vec<ATerm>,
    expr: &CExpr,
    tuples: &Tuples,
    check: &Tuples,
    k: &mut dyn FnMut(&mut Vec<ATerm>),
) {
    match expr {
        CExpr::Unit => k(slots),
        CExpr::Bind(x, y) => {
            let y_sub = sub_cterm(slots, y);
            match x {
                CTerm::Var(VarOp::Set(i)) => {
                    slots[*i as usize] = y_sub;
                    k(slots);
                }
                CTerm::Var(VarOp::Check(i)) => {
                    if slots[*i as usize] == y_sub {
                        k(slots);
                    }
                }
                _ => {
                    if match_cterm(slots, x, &y_sub) {
                        k(slots);
                    }
                }
            }
        }
        CExpr::Atom(pred, pat) => {
            for stored_tuple in tuples.lookup(pred) {
                if match_cterms(slots, pat, stored_tuple) {
                    k(slots);
                }
            }
        }
        CExpr::NegAtom(at) => {
            let substituted: Tuple = sub_cterms(slots, at);
            if !check.contains_tuple(&substituted) {
                k(slots);
            }
        }
        CExpr::Join(a, b) => {
            eval_compiled(slots, a, tuples, check, &mut |slots2| {
                eval_compiled(slots2, b, tuples, check, k);
            });
        }
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
/// Returns a map from predicate Sym to the list of CSpecializedRules that match it.
pub fn prespecialize(rules: &[&Rule]) -> HashMap<Sym, Vec<CSpecializedRule>> {
    let mut result: HashMap<Sym, Vec<CSpecializedRule>> = HashMap::new();

    for rule in rules {
        let preds = atom_predicates(&rule.body.val);
        for (pred_sym, _arity) in preds {
            let mut entries = Vec::new();
            collect_extractions(&rule.body.val, pred_sym, &mut |pats, remaining| {
                entries.push(SpecEntry { pats, remaining });
            });

            if !entries.is_empty() {
                let mut final_entries = Vec::new();
                for entry in &entries {
                    let mut seen: HashMap<Sym, u16> = HashMap::new();
                    let mut next_slot: u16 = 0;

                    for (sym, _) in &rule.body.ctx.entries {
                        if !seen.contains_key(sym) {
                            seen.insert(*sym, next_slot);
                            next_slot += 1;
                        }
                    }

                    let mut cpats = Vec::new();
                    for pat in &entry.pats {
                        cpats.push(compile_tuple(&pat[1..], &mut seen, &mut next_slot));
                    }

                    let cremaining = compile_expr(&entry.remaining, &mut seen, &mut next_slot);

                    let chead: Vec<Vec<CTerm>> = rule.head.iter().map(|tuple| {
                        compile_tuple(tuple, &mut seen, &mut next_slot)
                    }).collect();

                    final_entries.push(CSpecEntry {
                        pats: cpats,
                        remaining: cremaining,
                        num_slots: next_slot,
                        head: chead,
                        base_ctx_len: rule.body.ctx.entries.len() as u16,
                        base_ctx: rule.body.ctx.clone(),
                    });
                }

                result.entry(pred_sym).or_default().push(CSpecializedRule {
                    entries: final_entries,
                });
            }
        }
    }
    result
}

/// Evaluate a compiled precomputed specialization against a concrete tuple.
/// `t` is the full tuple (with pred at [0]).
pub fn eval1_spec(
    spec: &CSpecializedRule,
    t: &Tuple,
    ts: &Tuples,
    check: &Tuples,
    _intern: &Interner,
) -> Vec<Vec<Tuple>> {
    let mut results = Vec::new();
    let t_rest = &t[1..]; // skip pred

    for entry in &spec.entries {
        let mut slots = vec![ablank(); entry.num_slots as usize];

        // Initialize slots from base_ctx
        for (i, (_, val)) in entry.base_ctx.entries.iter().enumerate() {
            slots[i] = val.clone();
        }

        // Match each compiled pat against the tuple (without pred)
        let mut ok = true;
        for cpat in &entry.pats {
            if !match_cterms(&mut slots, cpat, t_rest) {
                ok = false;
                break;
            }
        }
        if !ok { continue; }

        // Eval remaining
        eval_compiled(&mut slots, &entry.remaining, ts, check, &mut |final_slots| {
            // Substitute head
            let head_tuples: Vec<Tuple> = entry.head.iter().map(|ht| {
                sub_cterms(final_slots, ht)
            }).collect();
            results.push(head_tuples);
        });
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
