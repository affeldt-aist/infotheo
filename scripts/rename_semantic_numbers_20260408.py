#!/usr/bin/env python3
"""
Phase D2 of dsdp_fsm naming audit (2026-04-08): make case-value numeric
suffixes explicit.

Every number targeted here IS semantic (refers to a specific value of
`j` or `n_relay`) but was buried with bare `_0`, `_n1`, `_n2`, `_j1`,
`_last`, `_send0_recv1`, etc. This phase prefixes each number with
what it refers to, so the reader sees the case split in the name.

KEPT as-is (already semantic or a different kind of number):
- `initial_step1_has_progress` — `step1` = iteration count, legitimate
- `alice_step1_trace_local` / `alice_step2_trace_local` — iteration
  count, legitimate (though after Phase A they're now
  `alice_step1_trace_local` etc., unchanged)
- `r1_relay` / `r2_relay` — deferred with Phase E (section vars)

Verified by grep: all targets localized to dsdp_fsm.v and
dsdp_fsm_progress.v.

Usage:
  python3 scripts/rename_semantic_numbers_20260408.py --dry-run
  python3 scripts/rename_semantic_numbers_20260408.py
"""
from pathlib import Path
import re
import sys

WORKSPACE = Path(__file__).parent.parent

FILES = [
    "dumas2017dual/dsdp/dsdp_fsm.v",
    "dumas2017dual/dsdp/dsdp_fsm_progress.v",
]

# Longest names first to avoid prefix collisions.
RENAMES = [
    # Lemmas in dsdp_fsm_progress.v (Record-progress layer)
    ("send_phase_to_drain_phase_last", "send_phase_to_drain_when_j_eq_nrelay"),
    ("send_phase_to_drain_phase_n2",   "send_phase_to_drain_when_nrelay_eq_2"),
    ("tail_phase_from_recv_phase_n1",  "tail_phase_from_recv_when_nrelay_eq_1"),
    ("mk_next_sender2",                "mk_next_sender_at_j2"),
    ("mk_next_j1_recv",                "mk_next_recv_at_j1"),
    # Lemmas in dsdp_fsm.v (operational layer)
    ("step_ok_send0_recv1",            "step_ok_send_j0_to_recv_j1"),
    ("step_ok_recv_send0",             "step_ok_recv_send_at_j0"),
    ("send_0_has_progress",            "send_at_j0_has_progress"),
    ("frag_ok_send_0",                 "frag_ok_send_at_j0"),
    ("init_matches_recv0",             "init_matches_recv_at_j0"),
    # Definitions in dsdp_fsm.v
    ("send_procs_0",                   "send_procs_at_j0"),
    ("st_send_0",                      "st_send_at_j0"),
    # Phase-B had an outstanding rename for the underlying progress
    # notation; the trailing `0` there also gets the same treatment via
    # the Phase B rename already applied (known_ret_recv_at_j0).
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
