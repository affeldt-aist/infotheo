#!/usr/bin/env python3
"""
Phase D3 of dsdp_fsm naming audit (2026-04-08): expand the cryptic
`bg_*` prefix on top-level identifiers to `relay_bg_*` so the meaning
("background process function: per-position relay state of type
nat -> proc data") is visible in every reference.

Phase D already renamed Record fields (`rp_bg` → `rp_relay_bg`, etc.).
This phase covers the remaining bg_* identifiers: definitions,
lemmas, and notations.

Naming rules:
- `bg_*` → `relay_bg_*`.
- `bg_relay_ahead_*` → `relay_bg_ahead_*` (drop the duplicate `relay_`).
- `bg_recv0_*` → `relay_bg_recv_from0_*` (the `0` is a channel index,
  not a `j` value; spell it out as "from channel 0" = from Alice).
- `bg_safe_form` → `relay_bg_safe_form` (NOT `relay_bg_nonfiring_form`
  per readability audit, because the existing constructor names
  `BSF_finish` etc. would need updating; defer the deeper semantic
  rename to avoid scope creep).
- `bg_s_of` / `bg'_of` → `relay_bg_after_recv_step` /
  `relay_bg_after_recv_send` (semantic names per readability audit).

Variable names like `(bg : nat -> proc data)` in lemma signatures and
local `set bg := ...` in proof bodies are NOT touched — those are
proof-local short names, which is the correct convention for binder
names.

Usage:
  python3 scripts/rename_bg_to_relay_bg_20260408.py --dry-run
  python3 scripts/rename_bg_to_relay_bg_20260408.py
"""
from pathlib import Path
import re
import sys

WORKSPACE = Path(__file__).parent.parent

FILES = [
    "dumas2017dual/dsdp/dsdp_fsm.v",
    "dumas2017dual/dsdp/dsdp_fsm_progress.v",
]

# Longest names first; matters for prefix collision avoidance.
RENAMES = [
    # Notations / definitions with semantic rename (longest first).
    ("bg_safe_form_step_any",       "relay_bg_safe_form_step_any"),
    ("bg_safe_form",                "relay_bg_safe_form"),
    ("bg_frontier_sender_fires",    "relay_bg_frontier_sender_fires"),
    ("bg_frontier_receiver_fires",  "relay_bg_frontier_receiver_fires"),
    # bg_recv0_* — `0` here is the channel index (Alice's position),
    # spelled out as `recv_from0` (consistent with audit's BSF_recv_from0).
    ("bg_recv0_nop_recv",           "relay_bg_recv_from0_nop_recv"),
    ("bg_recv0_fire_send",          "relay_bg_recv_from0_fire_send"),
    ("bg_recv0_nop_send",           "relay_bg_recv_from0_nop_send"),
    # bg_finish_nop_*
    ("bg_finish_nop_recv",          "relay_bg_finish_nop_recv"),
    ("bg_finish_nop_send",          "relay_bg_finish_nop_send"),
    # bg_relay_ahead_* — drop the duplicate `relay`
    ("bg_relay_ahead_recv",         "relay_bg_ahead_recv"),
    ("bg_relay_ahead_send",         "relay_bg_ahead_send"),
    # bg_nop_*_safe / bg_nop_*_init
    ("bg_nop_recv_safe",            "relay_bg_nop_recv_safe"),
    ("bg_nop_recv_init",            "relay_bg_nop_recv_init"),
    # Core defs
    ("bg_nop_recv",                 "relay_bg_nop_recv"),
    ("bg_nop_send",                 "relay_bg_nop_send"),
    ("bg_init_local",               "relay_bg_init_local"),
    ("bg_init",                     "relay_bg_init"),
    # bg_s_of / bg'_of: semantic rename per audit
    ("bg_s_of",                     "relay_bg_after_recv_step"),
    ("bg'_of",                      "relay_bg_after_recv_send"),
]


def apply_word_renames(content: str) -> tuple[str, int]:
    total = 0
    for old, new in RENAMES:
        # Use a custom boundary that allows `'` (prime) on the LHS for
        # `bg'_of`. Standard \b doesn't treat `'` as a word char.
        if "'" in old:
            # Match exactly the string with non-word/start boundaries.
            pat = re.compile(rf"(?<![A-Za-z0-9_]){re.escape(old)}(?![A-Za-z0-9_'])")
        else:
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
