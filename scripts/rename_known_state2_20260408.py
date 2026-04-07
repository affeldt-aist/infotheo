#!/usr/bin/env python3
"""
Phase B of dsdp_fsm naming audit (2026-04-08): rename the
`known_state2` / `KS2_*` / `ks2_*` cluster in dsdp_fsm.v and
dsdp_fsm_progress.v.

User-approved scheme: `known_ret_state` + `KnownRet*` CamelCase
constructors + `known_ret_*` lemma prefix. The `_ret` captures the
distinguishing feature (terminal state is `Ret`, not `Done`) that
makes `known_state2` different from `known_state`.

Applies the guiding principle on numeric suffixes: trailing `0` in
`ks2_recv0` / `known_state2_recv0` is a case value (j=0 recv state),
so it stays but is made explicit: `_recv_at_j0`.

Usage:
  python3 scripts/rename_known_state2_20260408.py --dry-run
  python3 scripts/rename_known_state2_20260408.py
"""
from pathlib import Path
import re
import sys

WORKSPACE = Path(__file__).parent.parent

FILES = [
    "dumas2017dual/dsdp/dsdp_fsm.v",
    "dumas2017dual/dsdp/dsdp_fsm_progress.v",
]

# Longest names first so `known_state2_recv0` is renamed before
# `known_state2` (prefix rule).
RENAMES = [
    # Specific long compounds (must come before the bare `known_state2`).
    ("known_state2_recv0",        "known_ret_state_recv_at_j0"),
    ("known_state2_term_ret",     "known_ret_state_terminal"),
    ("known_state2_to_known",     "known_ret_state_to_known"),
    ("known_state2_has_progress", "known_ret_state_has_progress"),
    ("known_state2_step",         "known_ret_state_step"),
    # Inductive type.
    ("known_state2",              "known_ret_state"),
    # Constructors.
    ("KS2_ret",                   "KnownRetBase"),
    ("KS2_step",                  "KnownRetStep"),
    # Lemmas using the `ks2_` prefix.
    ("ks2_drain_chain",           "known_ret_drain_chain"),
    ("ks2_recv_gen",              "known_ret_recv_gen"),
    ("ks2_of_tail_phase",         "known_ret_of_tail_phase"),
    ("ks2_of_drain_phase",        "known_ret_of_drain_phase"),
    ("ks2_recv0",                 "known_ret_recv_at_j0"),
    ("ks2_tail",                  "known_ret_tail"),
    # One-off: `interp_chain_ks2`.
    ("interp_chain_ks2",          "interp_chain_known_ret"),
]


def apply_word_renames(content: str) -> tuple[str, int]:
    total = 0
    for old, new in RENAMES:
        pat = re.compile(rf"\b{re.escape(old)}\b")
        n = len(pat.findall(content))
        if n:
            content = pat.sub(new, content)
            total += n
    return content, total


def process_file(rel_path: str, dry_run: bool):
    path = WORKSPACE / rel_path
    if not path.exists():
        print(f"ERROR: {rel_path} not found", file=sys.stderr)
        return False

    original = path.read_text()
    content, count = apply_word_renames(original)

    if content == original:
        print(f"{rel_path}: no changes")
        return True

    verb = "would modify" if dry_run else "modified"
    print(f"{rel_path}: {verb} ({count} renames)")

    if not dry_run:
        path.write_text(content)

    return True


def main():
    dry_run = "--dry-run" in sys.argv
    if dry_run:
        print("DRY RUN — no files will be modified\n")

    ok = True
    for f in FILES:
        ok &= process_file(f, dry_run)

    if dry_run:
        print("\nRun without --dry-run to apply.")

    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
