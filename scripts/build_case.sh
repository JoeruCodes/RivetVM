#!/usr/bin/env bash
# build_case.sh  --  Build & trace a single C program through the R2VM pipeline.
#
# Usage:  scripts/build_case.sh <source.c> [--sysroot <path>] [--out <dir>]
#
# Steps performed:
#   1. Compile <source.c> to RISC-V ELF binary using riscv64-linux-gnu-gcc.
#   2. Emit LLVM IR with clang for the same target.
#   3. Generate SSA/range-proof maps via cargo bin generate_ssa_map.
#   4. Run R2VM with trace feature to obtain trace.json, memory_trace.json, other_cols.json.
#   5. All artifacts are written into <out>/<case-name>/.

set -euo pipefail

if [[ $# -lt 1 ]]; then
  echo "Usage: $0 <source.c> [--sysroot <path>] [--out <dir>]" >&2
  exit 1
fi

SRC=$(realpath "$1"); shift
SYSROOT="/usr/riscv64-linux-gnu"
OUT_ROOT="$(git rev-parse --show-toplevel)/starks-v2/r2vm_cases"

while [[ $# -gt 0 ]]; do
  case "$1" in
    --sysroot)
      SYSROOT="$2"; shift 2;;
    --out)
      OUT_ROOT="$(realpath "$2")"; shift 2;;
    *)
      echo "Unknown arg: $1" >&2; exit 1;;
  esac
done

# Case name = basename without extension
CASE=$(basename "$SRC" .c)
OUT_DIR="$OUT_ROOT/$CASE"
mkdir -p "$OUT_DIR"

BIN="$OUT_DIR/$CASE.riscv"
IR="$OUT_DIR/$CASE.ll"

# 1. Compile to RISC-V binary
riscv64-linux-gnu-gcc -Wall -O2 "$SRC" -o "$BIN"

# 2. Emit LLVM IR (clang)
clang --target=riscv64-linux-gnu -S -emit-llvm "$SRC" -o "$IR"

# 3. Generate SSA map & range proofs
cargo run -q -p app --bin generate_ssa_map -- "$IR" "$OUT_DIR"

# 4. Run emulator to get traces
pushd "$(git rev-parse --show-toplevel)/starks-v2/r2vm" >/dev/null
RUST_BACKTRACE=full cargo run -q --features trace -- --sysroot "$SYSROOT" --trace "$BIN" --trace-file "$OUT_DIR/trace.json"
popd >/dev/null

echo "✅ Built case '$CASE' – artifacts in $OUT_DIR" 