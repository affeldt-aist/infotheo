#!/usr/bin/env python3
"""
Phase A of dsdp_fsm naming audit (2026-04-08): rename `local_*` Let
cluster in dsdp_fsm.v and dsdp_fsm_progress.v.

User-approved policy: drop `local_` prefix when possible; if the
resulting name would shadow an existing upstream definition, use
`_local` suffix instead. In practice all 11 `local_*` Lets alias a
same-named upstream definition, so every one ends up with `_local`
suffix.

Collision resolution (progress file only):
- `local_st_recv`: the progress file already has its own
  `st_recv_local` Let defined earlier (at line ~81). The
  `local_st_recv := st_recv_local.` alias is redundant; delete it.
  All call sites then resolve to the existing `st_recv_local`.
- `local_chain_acc`: the progress file already has `chain_acc_local`
  at line ~137. Same treatment: delete the duplicate alias, existing
  `chain_acc_local` wins.

Usage:
  python3 scripts/rename_local_lets_20260408.py --dry-run
  python3 scripts/rename_local_lets_20260408.py
"""
from pathlib import Path
import re
import sys

WORKSPACE = Path(__file__).parent.parent

FSM_FILE = "dumas2017dual/dsdp/dsdp_fsm.v"
PROGRESS_FILE = "dumas2017dual/dsdp/dsdp_fsm_progress.v"

# (old_name, new_name) — applied to both files; longer names first to
# avoid prefix collisions between `local_st_ret` and `local_st_recv`.
RENAMES = [
    ("local_st_drain_gen",   "st_drain_gen_local"),
    ("local_recv_procs_gen", "recv_procs_gen_local"),
    ("local_send_procs_gen", "send_procs_gen_local"),
    ("local_alice_enc",      "alice_enc_local"),
    ("local_relay_body",     "relay_body_local"),
    ("local_chain_acc",      "chain_acc_local"),
    ("local_bg_init",        "bg_init_local"),
    ("local_st_recv",        "st_recv_local"),
    ("local_st_tail",        "st_tail_local"),
    ("local_st_ret",         "st_ret_local"),
    ("local_term",           "term_local"),
]

# Progress file has pre-existing `Let st_recv_local := ...` at line ~81
# and `Let chain_acc_local := ...` at line ~137. After rename, the new
# `Let st_recv_local := st_recv_local.` / `Let chain_acc_local := ...`
# lines become duplicate definitions which Coq will reject. Delete the
# duplicate lines (the later ones, which were the moved aliases).
PROGRESS_DUPLICATE_DELETIONS = [
    # (match_regex, description) — each regex must be anchored and
    # match exactly ONE line in the progress file.
    (r"^Let st_recv_local := st_recv_local\.\s*(\([^)]*\))?\s*$",
     "duplicate `Let st_recv_local := st_recv_local.` (was local_st_recv alias)"),
    (r"^Let chain_acc_local := @chain_acc AHE n_relay u r v_relay\.\s*$",
     "duplicate `Let chain_acc_local := @chain_acc AHE n_relay u r v_relay.` (was local_chain_acc)"),
]


def apply_word_renames(content: str) -> tuple[str, int]:
    """Apply word-boundary renames to content, returning (new, count)."""
    total = 0
    for old, new in RENAMES:
        # \b word boundary ensures we don't rename substrings inside
        # other identifiers (e.g. `local_bg_init_foo` if any existed).
        pat = re.compile(rf"\b{re.escape(old)}\b")
        n = len(pat.findall(content))
        if n:
            content = pat.sub(new, content)
            total += n
    return content, total


def delete_duplicates(content: str) -> tuple[str, list[str]]:
    """Delete lines matching PROGRESS_DUPLICATE_DELETIONS (one hit each).

    Returns (new_content, list_of_descriptions_deleted).
    """
    lines = content.split("\n")
    new_lines = []
    deleted = []
    for line in lines:
        drop = False
        for pat, desc in PROGRESS_DUPLICATE_DELETIONS:
            if re.match(pat, line):
                # Only delete the FIRST occurrence of each — second would
                # indicate unexpected state.
                if desc not in deleted:
                    deleted.append(desc)
                    drop = True
                    break
        if not drop:
            new_lines.append(line)
    return "\n".join(new_lines), deleted


def process_file(rel_path: str, is_progress: bool, dry_run: bool):
    path = WORKSPACE / rel_path
    if not path.exists():
        print(f"ERROR: {rel_path} not found", file=sys.stderr)
        return False

    original = path.read_text()
    content, count = apply_word_renames(original)

    deleted_descs = []
    if is_progress:
        content, deleted_descs = delete_duplicates(content)

    if content == original:
        print(f"{rel_path}: no changes")
        return True

    verb = "would modify" if dry_run else "modified"
    print(f"{rel_path}: {verb} ({count} identifier renames"
          + (f", {len(deleted_descs)} duplicate deletions" if deleted_descs else "")
          + ")")
    for desc in deleted_descs:
        print(f"  deleted: {desc}")

    if not dry_run:
        path.write_text(content)

    return True


def main():
    dry_run = "--dry-run" in sys.argv
    if dry_run:
        print("DRY RUN — no files will be modified\n")

    ok = True
    ok &= process_file(FSM_FILE, is_progress=False, dry_run=dry_run)
    ok &= process_file(PROGRESS_FILE, is_progress=True, dry_run=dry_run)

    if dry_run:
        print("\nRun without --dry-run to apply.")

    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
