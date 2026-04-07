#!/usr/bin/env python3
"""
Phase C of dsdp_fsm naming audit (2026-04-08): clean up the `_gen` /
`_uncond` / `_concrete` / `_explicit` suffix family.

The plan-file's two-pass design (proposal → user review → apply) was
collapsed into a single direct script after scope scan showed:
- Only 2 .v files touched (dsdp_fsm.v, dsdp_fsm_progress.v).
- The third file matched (`declarative/declarative.v`) is a comment
  mention only.
- Trivial identity aliases (`send_procs_general`, `drain_procs` as
  wrapper, `step_ok_recv_send` as wrapper) were deleted manually BEFORE
  running this script.

Strategy:
- **Drop `_gen`** on lemmas/defs that have NO non-`_gen` sibling. Clean
  rename.
- **Keep `_gen` pairs intact** for the recv family (`recv_procs_gen` +
  `recv_procs`, etc.) because the non-`_gen` version is a legitimate
  bg_init specialization, not a trivial identity.
- **Semantic-suffix renames** for distinct-statement lemmas where the
  `_uncond`/`_concrete`/`_explicit` siblings had different types:
  `_gen` (the original NOP-hypothesis form) → `_nop`,
  `_uncond` → `_ex` (existential bg_s),
  `_concrete`/`_explicit` → `E` (equation with concrete witness).

Usage:
  python3 scripts/rename_gen_suffix_20260408.py --dry-run
  python3 scripts/rename_gen_suffix_20260408.py
"""
from pathlib import Path
import re
import sys

WORKSPACE = Path(__file__).parent.parent

FILES = [
    "dumas2017dual/dsdp/dsdp_fsm.v",
    "dumas2017dual/dsdp/dsdp_fsm_progress.v",
]

# Longer names first to prevent prefix collisions (e.g.
# `step_ok_recv_send_concrete` must be renamed before
# `step_ok_recv_send_gen`).
RENAMES = [
    # --- Semantic-suffix lemmas (distinct statement types) ---
    # step_ok_recv_send triple.
    ("step_ok_recv_send_concrete", "step_ok_recv_sendE"),
    ("step_ok_recv_send_uncond",   "step_ok_recv_send_ex"),
    ("step_ok_recv_send_gen",      "step_ok_recv_send_nop"),
    # step_ok_send_recv triple.
    ("step_ok_send_recv_explicit", "step_ok_send_recvE"),
    ("step_ok_send_recv_uncond",   "step_ok_send_recv_ex"),
    ("step_ok_send_recv_gen",      "step_ok_send_recv_nop"),

    # --- Plain `_gen` drop (no non-gen sibling exists) ---
    ("step_ok_drain_drain_gen",    "step_ok_drain_drain"),
    ("step_ok_drain_tail_gen",     "step_ok_drain_tail"),
    ("send_has_progress_gen",      "send_has_progress"),
    ("drain_has_progress_gen",     "drain_has_progress"),
    ("frag_ok_send_gen",           "frag_ok_send"),
    ("frag_ok_drain_gen",          "frag_ok_drain"),
    ("st_send_gen",                "st_send"),
    ("st_drain_gen",               "st_drain"),
    ("send_procs_gen",             "send_procs"),
    ("drain_procs_gen",            "drain_procs"),

    # --- Kept as-is (recv family, legitimate pair) ---
    # recv_procs_gen + recv_procs
    # frag_ok_recv_gen + frag_ok_recv
    # st_recv_gen + st_recv
    # recv_has_progress_gen + recv_has_progress
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
