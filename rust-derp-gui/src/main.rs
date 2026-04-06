use eframe::egui;
use std::collections::HashMap;
use std::fs;
use derp::types::{apred, pp_tuple, Name, Term, Tuple};
use derp::sym::{Interner, Sym};
use derp::eval;

// -- compute ------------------------------------------------------------------

fn compute(filenames: &[String]) -> (Vec<(Sym, Tuple)>, Interner) {
    let input = filenames.iter()
        .map(|f| fs::read_to_string(f).unwrap_or_else(|_| panic!("could not read file: {}", f)))
        .collect::<Vec<_>>()
        .join("\n");

    let (result, table, intern, _stats) = eval(&input, false);

    let mut preds: Vec<_> = result.relations.iter().collect();
    preds.sort_by_key(|(p, _)| intern.resolve(**p));

    let mut tuples = Vec::new();
    for (pred, tset) in preds {
        let mut sorted: Vec<_> = tset.iter().collect();
        sorted.sort();
        for t in sorted {
            let expanded: Tuple = t.iter()
                .map(|term| std::rc::Rc::new(term.expand_ids(&table)))
                .collect();
            tuples.push((*pred, expanded));
        }
    }
    (tuples, intern)
}

// -- Tree ---------------------------------------------------------------------

#[derive(Clone)]
enum Tree {
    Leaf(String),
    Node(String, Box<Tree>, Box<Tree>),
    Horizontal(Vec<Tree>),
    Vertical(Vec<Tree>),
}

impl Tree {
    fn label(&self) -> Option<&str> {
        match self {
            Tree::Leaf(s) | Tree::Node(s, ..) => Some(s),
            _ => None,
        }
    }

    fn render(&self, ui: &mut egui::Ui, last_clicked: &mut String) {
        match self {
            Tree::Horizontal(children) => {
                ui.horizontal(|ui| {
                    for child in children {
                        child.render(ui, last_clicked);
                    }
                });
            }
            Tree::Vertical(children) => {
                ui.vertical(|ui| {
                    for child in children {
                        child.render(ui, last_clicked);
                    }
                });
            }
            _ => {
                egui::Frame::new()
                    .stroke(egui::Stroke::new(1.0, egui::Color32::GRAY))
                    .inner_margin(6.0)
                    .outer_margin(4.0)
                    .show(ui, |ui| {
                        if let Some(label) = self.label() {
                            if ui.button(label).clicked() {
                                *last_clicked = label.to_string();
                            }
                        }
                        if let Tree::Node(_, left, right) = self {
                            ui.horizontal(|ui| {
                                ui.vertical(|ui| left.render(ui, last_clicked));
                                ui.vertical(|ui| right.render(ui, last_clicked));
                            });
                        }
                    });
            }
        }
    }
}

// -- App ----------------------------------------------------------------------

fn main() -> eframe::Result {
    let filenames: Vec<String> = std::env::args()
        .skip(1)
        .filter(|a| !a.starts_with("--"))
        .collect();

    if filenames.is_empty() {
        eprintln!("usage: derp-gui <file.derp> [<file2.derp> ...]");
        std::process::exit(1);
    }

    eframe::run_native(
        "Derp",
        eframe::NativeOptions::default(),
        Box::new(move |_cc| Ok(Box::new(App::new(filenames)))),
    )
}

struct App {
    filenames: Vec<String>,
    tuples: Vec<(Sym, Tuple)>,
    intern: Interner,
    active: HashMap<(Sym, Tuple), bool>,
}

impl App {
    fn new(filenames: Vec<String>) -> Self {
        let (tuples, intern) = compute(&filenames);
        Self { filenames, tuples, intern, active: HashMap::new() }
    }

    fn recompute(&mut self) {
        let (tuples, intern) = compute(&self.filenames);
        self.active.retain(|k, _| tuples.contains(k));
        self.tuples = tuples;
        self.intern = intern;
    }

    fn check_and_commit(&mut self) -> bool {
        let active: Vec<&(Sym, Tuple)> = self.tuples.iter()
            .filter(|t| self.active.get(*t).copied().unwrap_or(false))
            .collect();

        let mut incompletes: Vec<&std::rc::Rc<Term>> = Vec::new();
        let mut options: Vec<&std::rc::Rc<Term>> = Vec::new();

        for (pred, args) in &active {
            match (self.intern.resolve(*pred), args.as_slice()) {
                ("incomplete", [x]) => incompletes.push(x),
                ("option",     [_x, y]) => options.push(y),
                _ => {}
            }
        }

        if incompletes.len() == 1 && options.len() == 1 {
            let line = format!("-- is {} {}.\n",
                incompletes[0].pp(&self.intern),
                options[0].pp(&self.intern));
            let path = &self.filenames[0];
            match std::fs::OpenOptions::new().append(true).open(path) {
                Ok(mut f) => {
                    use std::io::Write;
                    if let Err(e) = f.write_all(line.as_bytes()) {
                        eprintln!("could not write to {path}: {e}");
                        return false;
                    }
                }
                Err(e) => { eprintln!("could not open {path}: {e}"); return false; }
            }
            return true;
        }
        false
    }
}

impl eframe::App for App {
    fn update(&mut self, ctx: &egui::Context, _frame: &mut eframe::Frame) {
        if ctx.input(|i| i.key_pressed(egui::Key::Q)) {
            ctx.send_viewport_cmd(egui::ViewportCommand::Close);
        }
        if ctx.input(|i| i.key_pressed(egui::Key::Space)) {
            self.recompute();
        }

        let mut clicked: Option<(Sym, Tuple)> = None;

        egui::CentralPanel::default().show(ctx, |ui| {
            if ui.button("Recompute").clicked() {
                self.recompute();
            }

            ui.separator();

            egui::ScrollArea::vertical().show(ui, |ui| {
                for (pred, args) in &self.tuples {
                    let key = (*pred, args.clone());
                    let full: Tuple = std::iter::once(apred(Name::Sym(*pred)))
                        .chain(args.iter().cloned())
                        .collect();
                    let label = pp_tuple(&full, &self.intern);
                    if ui.button(label).clicked() {
                        clicked = Some(key);
                    }
                }
            });
        });

        if let Some((pred, args)) = clicked {
            let key = (pred, args.clone());
            let entry = self.active.entry(key).or_insert(false);
            *entry = !*entry;

            let id = self.tuples.len();
            let pred_str = self.intern.resolve(pred);
            let app = if args.is_empty() {
                pred_str.to_owned()
            } else {
                let args_str = args.iter().map(|t| t.pp(&self.intern)).collect::<Vec<_>>().join(" ");
                format!("({} {})", pred_str, args_str)
            };
            let line = format!("-- click {} {}.\n", id, app);
            let path = &self.filenames[0];
            match std::fs::OpenOptions::new().append(true).open(path) {
                Ok(mut f) => { use std::io::Write; let _ = f.write_all(line.as_bytes()); }
                Err(e) => eprintln!("could not open {path}: {e}"),
            }
            self.recompute();
        }
    }
}
