# chyp-rs: build, test, wasm bundle, and upstream expectations.

WASM_TARGET := wasm32-unknown-unknown
WASM_OUT    := target/$(WASM_TARGET)/wasm/chyp.wasm
# Upstream Chyp checkout at commit 3d28483, and a Python with `lark`, for
# regenerating the expected results (`make expected`).
CHYP        ?= ../chyp
PYTHON      ?= python3
FIXTURES    := $(wildcard tests/fixtures/upstream/*.chyp tests/fixtures/derived/*.chyp tests/fixtures/crash/*.chyp laws/*.chyp)

.PHONY: all build test wasm wasm-test size expected check-laws clean

all: build test

build:
	cargo build --release

test:
	cargo test

# The wasm bundle: pkg/chyp.js + pkg/chyp_bg.wasm (ES module, `--target web`).
wasm:
	cargo build --lib --target $(WASM_TARGET) --profile wasm
	wasm-bindgen --target web --out-dir pkg --out-name chyp $(WASM_OUT)
	@$(MAKE) --no-print-directory size

size:
	@printf 'pkg/chyp_bg.wasm  %8d bytes  (%d gzipped)\n' $$(wc -c < pkg/chyp_bg.wasm) $$(gzip -9 -c pkg/chyp_bg.wasm | wc -c)
	@printf 'pkg/chyp.js       %8d bytes  (%d gzipped)\n' $$(wc -c < pkg/chyp.js) $$(gzip -9 -c pkg/chyp.js | wc -c)

# Runs every fixture through the wasm bundle step by step (needs node).
wasm-test: wasm build
	node tests/wasm_smoke.mjs

# Check the law files with the CLI.
check-laws: build
	./target/release/chyp-rs check laws/*.chyp

# Regenerate tests/fixtures/expected/ by running upstream Chyp headless.
expected:
	@test "$$(git -C $(CHYP) rev-parse --short=7 HEAD)" = "3d28483" || { echo "$(CHYP) is not at commit 3d28483"; exit 1; }
	PYTHONDONTWRITEBYTECODE=1 $(PYTHON) -I tools/upstream_expected.py $(CHYP) tests/fixtures/expected $(FIXTURES)

clean:
	cargo clean
	rm -rf pkg
