// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 the chyp-rs contributors. New in chyp-rs.

//! A FILE of `-` reads the theory from standard input (so a WASI host needs
//! no filesystem). With $CHYP_RS_STDIN_NAME set to a path, every command's
//! stdout, stderr and exit status for `-` must be byte for byte those for the
//! path: error lines, parse errors and unreadable (non-UTF-8) input included.

use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};

const NAME_VAR: &str = "CHYP_RS_STDIN_NAME";

fn root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

fn cli() -> Command {
    let mut c = Command::new(env!("CARGO_BIN_EXE_chyp-rs"));
    c.current_dir(root()).env_remove(NAME_VAR);
    c
}

fn run(args: &[&str], stdin: Option<&[u8]>, name: Option<&str>) -> Output {
    let mut c = cli();
    c.args(args).stdout(Stdio::piped()).stderr(Stdio::piped());
    c.stdin(if stdin.is_some() { Stdio::piped() } else { Stdio::null() });
    if let Some(n) = name {
        c.env(NAME_VAR, n);
    }
    let mut child = c.spawn().unwrap();
    if let Some(bytes) = stdin {
        // The CLI may exit without reading everything (it does not, but a
        // closed pipe here must not fail the test either).
        let _ = child.stdin.take().unwrap().write_all(bytes);
    }
    child.wait_with_output().unwrap()
}

fn assert_same(what: &str, a: &Output, b: &Output) {
    assert_eq!(a.status.code(), b.status.code(), "{}: exit status", what);
    assert!(
        a.stdout == b.stdout,
        "{}: stdout differs:\n{}\n---\n{}",
        what,
        String::from_utf8_lossy(&a.stdout),
        String::from_utf8_lossy(&b.stdout)
    );
    assert!(
        a.stderr == b.stderr,
        "{}: stderr differs:\n{}\n---\n{}",
        what,
        String::from_utf8_lossy(&a.stderr),
        String::from_utf8_lossy(&b.stderr)
    );
}

fn fixtures() -> Vec<String> {
    let mut out = Vec::new();
    for dir in [
        "tests/fixtures/upstream",
        "tests/fixtures/derived",
        "tests/fixtures/original",
        "tests/fixtures/crash",
        "laws",
    ] {
        let mut files: Vec<String> = std::fs::read_dir(root().join(dir))
            .unwrap()
            .map(|e| e.unwrap().file_name().into_string().unwrap())
            .filter(|f| f.ends_with(".chyp"))
            .map(|f| format!("{}/{}", dir, f))
            .collect();
        files.sort();
        out.extend(files);
    }
    assert!(out.len() >= 25, "{:?}", out);
    out
}

/// Compare `ARGS... FILE` with `ARGS... -` given the file's bytes on stdin.
fn compare(args: &[&str], file: &str, bytes: &[u8]) {
    let mut by_path = args.to_vec();
    by_path.push(file);
    let mut by_stdin = args.to_vec();
    by_stdin.push("-");
    let a = run(&by_path, None, None);
    let b = run(&by_stdin, Some(bytes), Some(file));
    assert_same(&format!("{} {}", args.join(" "), file), &a, &b);
}

#[test]
fn stdin_equals_path_for_every_fixture_and_command() {
    for file in fixtures() {
        let bytes = std::fs::read(root().join(&file)).unwrap();
        for cmd in [&["check"][..], &["step"], &["summary"], &["json"]] {
            compare(cmd, &file, &bytes);
        }
        // `json FILE PART`: an existing part and a missing one (exit 2).
        let a = run(&["json", &file, "1"], None, None);
        let b = run(&["json", "-", "1"], Some(&bytes), Some(&file));
        assert_same(&format!("json {} 1", file), &a, &b);
        let a = run(&["json", &file, "100000"], None, None);
        let b = run(&["json", "-", "100000"], Some(&bytes), Some(&file));
        assert_same(&format!("json {} 100000", file), &a, &b);
    }
}

#[test]
fn stdin_equals_path_for_unusual_bytes() {
    let dir = std::env::temp_dir().join(format!("chyp-rs-stdin-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let cases: &[(&str, &[u8])] = &[
        ("invalid_utf8.chyp", b"gen f : 1 -> 1\n\xff\n"),
        ("invalid_utf8_late.chyp", b"gen f : 1 -> 1\nrule r : f = f\n\xc3"),
        ("bom.chyp", b"\xef\xbb\xbfgen f : 1 -> 1\n"),
        ("nul.chyp", b"gen f : 1 -> 1\n\0\n"),
        ("empty.chyp", b""),
        ("syntax.chyp", b"gen f : 1 -> 1\nrule r : f = (\n"),
    ];
    for (name, bytes) in cases {
        let path = dir.join(name);
        std::fs::write(&path, bytes).unwrap();
        let path = path.to_str().unwrap();
        for cmd in ["check", "step", "summary", "json"] {
            compare(&[cmd], path, bytes);
        }
    }
    // Unreadable input is a usage-class error (exit 2) either way.
    let out = run(&["check", "-"], Some(b"\xff"), None);
    assert_eq!(out.status.code(), Some(2));
    assert_eq!(
        String::from_utf8_lossy(&out.stderr),
        "chyp-rs: -: stream did not contain valid UTF-8\n"
    );
    std::fs::remove_dir_all(&dir).unwrap();
}

#[test]
fn stdin_is_named_dash_by_default() {
    let file = "laws/drivers.chyp";
    let bytes = std::fs::read(root().join(file)).unwrap();
    let out = run(&["summary", "-"], Some(&bytes), None);
    let v: serde_json::Value = serde_json::from_slice(&out.stdout).unwrap();
    assert_eq!(v[0]["file"], "-");
    let check = run(&["check", "-"], Some(&bytes), None);
    assert!(String::from_utf8_lossy(&check.stdout).starts_with("-\n"));
    // An empty name is treated as unset.
    let out = run(&["summary", "-"], Some(&bytes), Some(""));
    let v: serde_json::Value = serde_json::from_slice(&out.stdout).unwrap();
    assert_eq!(v[0]["file"], "-");
    // The name applies only to `-`, never to a path.
    let out = run(&["summary", file], None, Some("other.chyp"));
    let v: serde_json::Value = serde_json::from_slice(&out.stdout).unwrap();
    assert_eq!(v[0]["file"], "drivers.chyp");
}

#[test]
fn stdin_is_read_once_and_shared() {
    // Two `-` arguments see the same theory, as a file named twice would.
    let file = "laws/orderers.chyp";
    let bytes = std::fs::read(root().join(file)).unwrap();
    let a = run(&["summary", file, file], None, None);
    let b = run(&["summary", "-", "-"], Some(&bytes), Some(file));
    assert_same("summary - -", &a, &b);
    // And `-` mixes with paths.
    let other = "laws/filters.chyp";
    let a = run(&["check", other, file], None, None);
    let b = run(&["check", other, "-"], Some(&bytes), Some(file));
    assert_same("check PATH -", &a, &b);
}

#[test]
fn paths_and_usage_are_unchanged() {
    // A missing file still names the path, and usage errors still exit 2.
    let out = run(&["check", "no/such.chyp"], None, None);
    assert_eq!(out.status.code(), Some(2));
    assert!(String::from_utf8_lossy(&out.stderr).starts_with("chyp-rs: no/such.chyp: "));
    for args in [&[][..], &["check"], &["step", "-", "-"], &["frob", "-"]] {
        assert_eq!(run(args, None, None).status.code(), Some(2), "{:?}", args);
    }
    assert!(Path::new(env!("CARGO_BIN_EXE_chyp-rs")).exists());
}
