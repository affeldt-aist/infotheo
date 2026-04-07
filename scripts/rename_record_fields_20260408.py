#!/usr/bin/env python3
"""
Phase D of dsdp_fsm naming audit (2026-04-08): Record field readability
renames for recv_phase / send_phase / drain_phase / tail_phase.

All fields are localized to dsdp_fsm.v (definitions) and
dsdp_fsm_progress.v (projection call sites). Verified by cross-file
grep.

Semantic-number rule: case-value numbers ARE preserved but made
explicit. `rp_sender2` meant "variant when j = 2"; rename to
`rp_sender_at_j2`. `rp_j1_recv` meant "variant when j = 1"; rename to
`rp_recv_at_j1`. `sp_last` meant "variant when j = n_relay"; rename to
`sp_at_j_eq_nrelay`.

Usage:
  python3 scripts/rename_record_fields_20260408.py --dry-run
  python3 scripts/rename_record_fields_20260408.py
"""
from pathlib import Path
import re
import sys

WORKSPACE = Path(__file__).parent.parent

FILES = [
    "dumas2017dual/dsdp/dsdp_fsm.v",
    "dumas2017dual/dsdp/dsdp_fsm_progress.v",
]

# Longest names first so compound fields rename before their stems.
RENAMES = [
    # recv_phase fields (readability + semantic-number rule)
    ("rp_j1_recv",       "rp_recv_at_j1"),
    ("rp_sender2",       "rp_sender_at_j2"),
    ("rp_rr_fw",         "rp_rand_fwd"),
    ("rp_receiver",      "rp_frontier_receiver"),
    ("rp_sender",        "rp_frontier_sender"),
    ("rp_finish",        "rp_finish_zone"),
    ("rp_bg",            "rp_relay_bg"),
    # send_phase fields
    ("sp_next_behind",   "sp_intermediate_waiting"),
    ("sp_active",        "sp_active_relay"),
    ("sp_sender2",       "sp_sender_at_j2"),
    ("sp_rr_fw",         "sp_rand_fwd"),
    ("sp_sender",        "sp_frontier_sender"),
    ("sp_last",          "sp_at_j_eq_nrelay"),
    ("sp_bg",            "sp_relay_bg"),
    # drain_phase fields
    ("dp_rr_drain",      "dp_rand"),
    ("dp_j_lt",          "dp_j_lt_nrelay"),
    ("dp_between",       "dp_intermediate_recv"),
    ("dp_last",          "dp_last_relay_recv"),
    ("dp_sender",        "dp_active_forwarder"),
    ("dp_finish",        "dp_finish_zone"),
    ("dp_safe",          "dp_bg_not_final_send"),
    ("dp_bg",            "dp_relay_bg"),
    # tail_phase fields
    ("tp_rr_tail",       "tp_final_rand"),
    ("tp_last",          "tp_last_relay_send"),
    ("tp_finish",        "tp_others_finish"),
    ("tp_bg",            "tp_relay_bg"),
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
