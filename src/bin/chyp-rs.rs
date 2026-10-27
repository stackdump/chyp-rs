//! chyp-rs command line: check theory files and print diagrams as JSON.

use std::fs;
use std::process::ExitCode;

use chyp::checker::Checker;
use chyp::parts::{PartKind, Status};
use chyp::state::State;

const USAGE: &str = "\
chyp-rs: check Chyp theory files (a Rust port of Chyp's core, upstream commit 3d28483)

USAGE:
  chyp-rs check FILE...       check each file; print one line per proof step
  chyp-rs step FILE           check FILE one part at a time, showing the goals left
  chyp-rs summary FILE...     print upstream-comparable JSON (see tools/upstream_expected.py)
  chyp-rs json FILE [PART]    print the checked theory as JSON with laid-out diagrams
                              (or only part number PART)

Exit status: 0 if every file parsed and no step was invalid, 1 otherwise, 2 on usage errors.";

fn read(path: &str) -> Result<String, String> {
    fs::read_to_string(path).map_err(|e| format!("{}: {}", path, e))
}

fn ok(state: &State) -> bool {
    state.parsed && state.count(Status::Invalid) == 0
}

fn describe(state: &State, i: usize) -> String {
    let p = &state.parts[i];
    let what = match p.kind {
        PartKind::Rewrite => {
            let by = if p.tactic == "rule" && p.tactic_args.len() == 1 {
                format!("by {}", p.tactic_args[0])
            } else if p.tactic == "refl" {
                "(no `by`: refl)".to_string()
            } else {
                format!("by {}({})", p.tactic, p.tactic_args.join(","))
            };
            let name = if p.name.is_empty() { "step".to_string() } else { p.name.clone() };
            format!("rewrite {} {}", name, by)
        }
        PartKind::ApplyTactic => format!("apply {}({})", p.tactic, p.tactic_args.join(",")),
        PartKind::Theorem => format!("theorem {}", p.name),
        PartKind::ProofStart => "proof".to_string(),
        PartKind::ProofQed => "qed".to_string(),
        PartKind::Gen => format!("gen {}", p.name),
        PartKind::Let => format!("let {}", p.name),
        PartKind::Rule => format!("rule {}", p.name),
    };
    format!("{:>5}  {:<9} {}", p.line, p.status.as_str(), what)
}

fn print_errors(path: &str, state: &State) {
    for e in &state.errors {
        eprintln!("{}:{}: {}", path, e.line, e.msg);
    }
}

fn cmd_check(files: &[String]) -> Result<bool, String> {
    let mut all_ok = true;
    for path in files {
        let state = chyp::check_source(&read(path)?);
        println!("{}", path);
        for (i, p) in state.parts.iter().enumerate() {
            if matches!(p.kind, PartKind::Gen | PartKind::Let | PartKind::Rule) {
                continue;
            }
            println!("{}", describe(&state, i));
        }
        print_errors(path, &state);
        println!(
            "  {} valid, {} invalid{}",
            state.count(Status::Valid),
            state.count(Status::Invalid),
            if state.parsed { "" } else { " (parse error)" }
        );
        all_ok &= ok(&state);
    }
    Ok(all_ok)
}

fn cmd_step(path: &str) -> Result<bool, String> {
    let mut state = State::parse(&read(path)?);
    let mut checker = Checker::new();
    let mut seen_errors = 0;
    while let Some(i) = checker.step(&mut state) {
        let p = &state.parts[i];
        if matches!(p.kind, PartKind::Gen | PartKind::Let | PartKind::Rule) {
            continue;
        }
        let goals = match &p.proof_state {
            Some(ps) if p.kind.is_proof_step() => format!("  [{} goal(s) left]", ps.goals.len()),
            _ => String::new(),
        };
        println!("{}{}", describe(&state, i), goals);
        for e in &state.errors[seen_errors..] {
            println!("         error: {}", e.msg);
        }
        seen_errors = state.errors.len();
    }
    for e in &state.errors[seen_errors..] {
        println!("{}:{}: {}", path, e.line, e.msg);
    }
    Ok(ok(&state))
}

fn cmd_summary(files: &[String]) -> Result<bool, String> {
    let mut out = Vec::new();
    let mut all_ok = true;
    for path in files {
        let state = chyp::check_source(&read(path)?);
        let name = std::path::Path::new(path).file_name().and_then(|s| s.to_str()).unwrap_or(path);
        out.push(chyp::json::summary(name, &state));
        all_ok &= ok(&state);
    }
    println!("{}", serde_json::to_string_pretty(&out).unwrap());
    Ok(all_ok)
}

fn cmd_json(path: &str, part: Option<&str>) -> Result<bool, String> {
    let state = chyp::check_source(&read(path)?);
    match part {
        None => println!("{}", serde_json::to_string_pretty(&chyp::json::theory(&state, true)).unwrap()),
        Some(n) => {
            let i: usize = n.parse().map_err(|_| format!("not a part number: {}", n))?;
            let p = state.parts.get(i).ok_or_else(|| format!("no part {} (there are {})", i, state.parts.len()))?;
            println!("{}", serde_json::to_string_pretty(&chyp::json::part(p, true)).unwrap());
        }
    }
    Ok(ok(&state))
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let result = match args.first().map(String::as_str) {
        Some("check") if args.len() >= 2 => cmd_check(&args[1..]),
        Some("step") if args.len() == 2 => cmd_step(&args[1]),
        Some("summary") if args.len() >= 2 => cmd_summary(&args[1..]),
        Some("json") if args.len() == 2 || args.len() == 3 => cmd_json(&args[1], args.get(2).map(String::as_str)),
        _ => {
            eprintln!("{}", USAGE);
            return ExitCode::from(2);
        }
    };
    match result {
        Ok(true) => ExitCode::SUCCESS,
        Ok(false) => ExitCode::from(1),
        Err(e) => {
            eprintln!("chyp-rs: {}", e);
            ExitCode::from(2)
        }
    }
}
