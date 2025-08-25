MAKEFILE_PATH   := $(abspath $(lastword $(MAKEFILE_LIST)))
MAKEFILE_DIR    := $(dir $(MAKEFILE_PATH))

LEAN_DIR        := $(MAKEFILE_DIR)..
CARGO_DEBUG_DIR := $(MAKEFILE_DIR)target/debug

CARGO_INSTALL := cargo install --locked --all-features --force

check-fmt:
	cargo build
	cd $(LEAN_DIR) && PATH=$(CARGO_DEBUG_DIR):$$PATH lake-dino check-fmt

install:
	$(CARGO_INSTALL) --path .

run:
	cargo run -- generate Dino
