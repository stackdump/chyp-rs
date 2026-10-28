# SPDX-License-Identifier: Apache-2.0
# Copyright 2026 the chyp-rs contributors. New in chyp-rs.
# chyp-rs: build, test, wasm bundle, and upstream expectations.

WASM_TARGET := wasm32-unknown-unknown
WASM_OUT    := target/$(WASM_TARGET)/wasm/chyp_rs.wasm
# The CLI as a WASI (preview 1) command module, for hosts such as wazero.
WASI_TARGET := wasm32-wasip1
WASI_OUT    := target/$(WASI_TARGET)/wasm/chyp-rs.wasm
# Panic locations name dependency sources under $CARGO_HOME; remapping it
# keeps the module's bytes independent of where it is built.
CARGO_HOME  ?= $(HOME)/.cargo
WASI_RUSTFLAGS := --remap-path-prefix=$(CARGO_HOME)=/cargo
# Upstream Chyp checkout at commit 3d28483, and a Python with `lark`, for
# regenerating the expected results (`make expected`).
CHYP        ?= ../chyp
PYTHON      ?= python3
FIXTURES    := $(wildcard tests/fixtures/upstream/*.chyp tests/fixtures/derived/*.chyp tests/fixtures/original/*.chyp tests/fixtures/crash/*.chyp laws/*.chyp)

.PHONY: all build test wasm wasm-test size wasi wasi-test expected check-laws clean

all: build test

build:
	cargo build --release

test:
	cargo test

# The wasm bundle: pkg/chyp_rs.js + pkg/chyp_rs_bg.wasm (ES module, `--target web`),
# with the LICENSE, NOTICE and THIRD-PARTY-NOTICES that must ship with it.
wasm:
	cargo build --lib --target $(WASM_TARGET) --profile wasm
	wasm-bindgen --target web --out-dir pkg --out-name chyp_rs $(WASM_OUT)
	cp LICENSE NOTICE THIRD-PARTY-NOTICES pkg/
	@$(MAKE) --no-print-directory size

size:
	@printf 'pkg/chyp_rs_bg.wasm  %8d bytes  (%d gzipped)\n' $$(wc -c < pkg/chyp_rs_bg.wasm) $$(gzip -9 -c pkg/chyp_rs_bg.wasm | wc -c)
	@printf 'pkg/chyp_rs.js       %8d bytes  (%d gzipped)\n' $$(wc -c < pkg/chyp_rs.js) $$(gzip -9 -c pkg/chyp_rs.js | wc -c)

# Runs every fixture through the wasm bundle step by step (needs node).
wasm-test: wasm build
	node tests/wasm_smoke.mjs

# The CLI for WASI: one self-contained module whose only imports are
# wasi_snapshot_preview1 functions (no wasm-bindgen, no JS host).
wasi:
	RUSTFLAGS="$(WASI_RUSTFLAGS)" cargo build --locked --bin chyp-rs --target $(WASI_TARGET) --profile wasm
	@printf '%s  %8d bytes  (%d gzipped)  sha256 %s\n' $(WASI_OUT) $$(wc -c < $(WASI_OUT)) $$(gzip -9 -n -c $(WASI_OUT) | wc -c) $$(sha256sum $(WASI_OUT) | cut -d' ' -f1)

# Runs every fixture (not crash/) and law through the WASI module under
# node:wasi, theory on stdin, against the native CLI (needs node).
wasi-test: wasi build
	node tests/wasi_smoke.mjs

# Check the law files with the CLI.
check-laws: build
	./target/release/chyp-rs check laws/*.chyp

# Regenerate tests/fixtures/expected/ by running upstream Chyp headless.
expected:
	@test "$$(git -C $(CHYP) rev-parse --short=7 HEAD)" = "3d28483" || { echo "$(CHYP) is not at commit 3d28483"; exit 1; }
	$(PYTHON) -I -B tools/upstream_expected.py $(CHYP) tests/fixtures/expected $(FIXTURES)

clean:
	cargo clean
	rm -rf pkg
