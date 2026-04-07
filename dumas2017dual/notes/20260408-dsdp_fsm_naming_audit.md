# DSDP FSM naming audit — 2026-04-08

**Scope:** `dumas2017dual/dsdp/dsdp_fsm.v` and
`dumas2017dual/dsdp/dsdp_fsm_progress.v` (state after commit `64b7c03`,
the split migration).

**Method:** Two parallel read-only audit agents:
1. **MathComp naming** — reference repo
   `/Users/cheng-huiweng/Projects/coq/math-comp` (`ssrnat.v`, `seq.v`,
   `ssralg.v` sampled for conventions).
2. **Readability** — independent lens, no MathComp comparison; judges
   whether a new reader can guess intent without reading the definition.

## Guiding principle — numeric suffixes must encode semantics

All numeric suffixes (`_0`, `_1`, `_2`, `_3`, `2`, `_n1`, `_n2`, `_j1`,
`_j2`) must carry concrete meaning — arity, case value, iteration count,
or argument position. They may NEVER serve as "version number" tags
(i.e., "there are two variants so we call them `_1` and `_2`").

- Version-number uses → rename with a semantic tag.
  (`known_state2` → `known_ret_state`)
- Case-value uses → keep the number BUT prefix with what the number
  refers to.
  (`sp_sender2` → `sp_sender_at_j2`,
   `send_phase_to_drain_phase_n2` → `send_phase_to_drain_when_nrelay_eq_2`,
   `rp_j1_recv` → `rp_recv_at_j1`,
   `step_ok_send0_recv1` → `step_ok_send_j0_to_recv_j1`,
   `send_procs_0` → `send_procs_at_j0`.)

When unsure whether a number is a version or a case value, check the
lemma statement: if it has a hypothesis like `(rp_j rp = 2)` or
`(n_relay = 2)`, the number is a case value and stays (explicit). If
the only reason for the number is "there's another one called `foo`",
it's a version number and must go.

## Merged audit table

Columns: **Name | File | Kind | MC verdict | Read verdict | Rename**.
`MC` = MathComp verdict, `Read` = Readability verdict. When rename
suggestions differ, both lenses are noted.

### Section variables

| Name | File | Kind | MC | Read | Rename |
|---|---|---|---|---|---|
| `AHE` | both | var | violation (ALL-CAPS) | clear | keep (domain trumps style) |
| `ek` | both | var | OK | unclear | `enc_key_of` |
| `n_relay` | both | var | OK | clear | keep |
| `dk` | both | var | OK | unclear (collides w/ `dk_relay`) | `alice_priv_key` |
| `dk_relay` | both | var | OK | clear | keep |
| `relays` | both | var | OK | unclear (perm, not entities) | `relay_ids` |
| `v0` | both | var | OK | unclear | `alice_input` |
| `u` | both | var | OK | confusing (single letter) | `alice_mul` |
| `r` | both | var | OK | confusing (clashes) | `alice_mask` |
| `rand_a` | both | var | OK | unclear | `alice_rand` |
| `v_relay` | both | var | OK | clear | keep |
| `r1_relay` | both | var | OK | unclear (1 vs 2) | `relay_rand_fwd` |
| `r2_relay` | both | var | OK | unclear | `relay_rand_back` |

### Hypotheses

| Name | File | Kind | MC | Read | Rename |
|---|---|---|---|---|---|
| `Hn_relay` | both | hyp | violation (H-prefix) | clear | `n_relay_gt0` |
| `Hrelays` | both | hyp | violation | unclear | `size_relays` |
| `Hrelays_id` | both | hyp | violation | unclear | `nth_relays` |
| `dec_total` | both | hyp | OK | clear | keep |
| `key_alice` | both | hyp | OK | unclear (eq not key) | `ek_alice_eq` |
| `key_relay` | both | hyp | OK | unclear | `ek_relay_eq` |
| `Hsize` | progress | let | violation | clear | `size_procs` |

### Section-local `Let` bindings

| Name | File | Kind | MC | Read | Rename |
|---|---|---|---|---|---|
| `data` | both | let | OK | clear | keep |
| `DI` | both | let | violation (ALL-CAPS) | unclear | `di` |
| `n_parties` | both | let | OK | clear | keep |
| `e_local` | both | let | minor (`_local`) | unclear | `cipher_to_data` |
| `d` | both | let | OK | confusing (collides `dk`) | `plain_to_data` |
| `priv_key_local` | both | let | minor | clear | `priv_key` |
| `pSend` | fsm | let | violation (camelCase) | clear | drop; use `smc_interpreter.Send` |
| `pRecvDec_local` | fsm | let | violation | clear | `recv_dec` |
| `pRecvEnc_local` | fsm | let | violation | clear | `recv_enc` |
| `enc_local` | fsm | let | minor | clear | `encp` |
| `concrete_val` | both | let | minor | unclear | `alice_final_result` |
| `concrete_val_eq` | fsm | let | minor | unclear | `alice_final_result_eq` |
| `procs` | progress | let | OK | clear | keep |
| `procs_tup` | progress | let | minor | clear | keep |
| `osp` | progress | let | violation (cryptic) | confusing | `one_step` |
| `chain_acc_local` | progress | let | minor | clear | `chain_acc` (shadow) |
| `st_recv_local` | progress | let | minor | clear | `recv_st` |
| `local_st_ret` | both | let | violation (`local_`) | clear | `st_ret_local` (shadow-blocked) |
| `local_st_tail` | both | let | violation | clear | `st_tail_local` |
| `local_st_drain_gen` | both | let | violation | clear | `st_drain_gen_local` |
| `local_st_recv` | both | let | violation | clear | merge with existing `st_recv_local` |
| `local_recv_procs_gen` | both | let | violation | clear | `recv_procs_gen_local` |
| `local_send_procs_gen` | both | let | violation | clear | `send_procs_gen_local` |
| `local_relay_body` | both | let | violation | clear | `relay_body_local` |
| `local_bg_init` | both | let | violation | unclear | `bg_init_local` |
| `local_chain_acc` | both | let | violation | clear | merge with existing `chain_acc_local` |
| `local_alice_enc` | both | let | violation | clear | `alice_enc_local` |
| `local_term` | both | let | violation | confusing (`term` overloaded) | `term_local` |
| `e_loc` | both | let | minor | confusing (vs. `e_local`) | merge with `e_local` |
| `next_j` | progress | let | OK | clear | keep |

### Local notations

| Name | File | Kind | MC | Read | Rename |
|---|---|---|---|---|---|
| `recv_phase` / `send_phase` / `drain_phase` / `tail_phase` | progress | notation | OK | clear | keep |
| `bg_s_of` | progress | notation | minor | confusing | `bg_after_recv_step` |
| `bg'_of` | progress | notation | violation (prime) | confusing | `bg_after_recv_send` |
| `known_state2` | progress | notation | violation (`2`) | confusing | `known_ret_state` |
| `KS2_ret` | progress | notation | violation | confusing | `KnownRetBase` |
| `drain_steppable` | progress | notation | minor (`_steppable`) | clear | `drain_chain` |
| `recv_send_steppable` | progress | notation | minor | clear | `recv_send_chain` |
| `bg_nop_recv` / `bg_nop_send` | progress | notation | OK | unclear | `bg_no_fire_at_recv` / `bg_no_fire_at_send` |
| `recv_st` / `send_st` / `drain_st` / `tail_st` | both | notation | OK | clear | keep |

### Definitions

| Name | File | Kind | MC | Read | Rename |
|---|---|---|---|---|---|
| `alice_foldr` | fsm | def | OK | unclear (exposes impl) | `alice_erase_from` |
| `relay_body` | fsm | def | OK | clear | keep |
| `relay_after_send0` | fsm | def | OK | clear | keep |
| `alice_enc` | fsm | def | OK | clear | keep |
| `term` | fsm | def | OK | confusing (overloaded) | `chain_summand` |
| `chain_acc` | fsm | fix | OK | clear | keep |
| `one_step_procs` | fsm | def | OK | clear | keep |
| `phase_state` | fsm | rec | OK | clear | keep |
| `done_procs` / `ret_procs` / `tail_procs` | fsm | def | OK | clear | keep |
| `recv_procs_gen` | fsm | def | violation (`_gen`) | unclear | → Phase C (sibling merge) |
| `send_procs_gen` | fsm | def | violation | unclear | → Phase C |
| `drain_procs_gen` | fsm | def | violation | unclear | → Phase C |
| `bg_init` | fsm | def | OK | unclear | `relay_bg_fresh` |
| `recv_procs` | fsm | def | minor (dup w/ `_gen`) | clear | → Phase C |
| `send_procs_0` | fsm | def | minor (`_0`) | unclear | `send_procs_at_j0` |
| `send_procs_general` | fsm | def | violation | confusing | drop |
| `drain_procs` | fsm | def | OK | confusing (dup) | drop or document |
| `is_nop` | fsm | def | OK | clear | keep |
| `bg_nop_recv` / `bg_nop_send` | fsm | def | OK | unclear | `bg_no_fire_at_recv` / `bg_no_fire_at_send` |
| `st_done` / `st_ret` / `st_tail` | fsm | def | OK | clear | keep |
| `st_recv_gen` / `st_send_gen` / `st_drain_gen` | fsm | def | violation (`_gen`) | clear | → Phase C |
| `st_recv` | fsm | def | OK | clear | keep |
| `st_send_0` | fsm | def | minor | unclear | `st_send_at_j0` |
| `bg_s_of` | fsm | def | minor | confusing | `bg_after_recv_step` |
| `bg'_of` | fsm | def | violation (prime) | confusing | `bg_after_recv_send` |
| `mk_recv_init` | progress | def | violation (`mk_`) | clear | `recv_init` |
| `expected_trace` | progress | def | OK | clear | keep |

### Records / constructors / fields

**`phase_state` / `PhaseState`**

| Name | MC | Read | Rename |
|---|---|---|---|
| `phase_state` | OK | clear | keep |
| `PhaseState` | OK | clear | keep |
| `ps_procs` | OK | clear | keep |
| `ps_frag` | OK | unclear | `ps_trace_frag` |
| `ps_frag_ok` | OK | clear | `ps_trace_frag_ok` |

**`recv_phase`**

| Name | MC | Read | Rename |
|---|---|---|---|
| `recv_phase` | OK | clear | keep |
| `MkRecvPhase` | minor (`Mk`) | clear | `RecvPhase` (deferred w/ Phase E) |
| `rp_j` | OK | clear | keep |
| `rp_rr_fw` | minor | confusing | `rp_rand_fwd` |
| `rp_bg` | OK | unclear | `rp_relay_bg` |
| `rp_ahead` | OK | clear | keep |
| `rp_behind` | OK | clear | keep |
| `rp_finish` | OK | unclear | `rp_finish_zone` |
| `rp_sender` | OK | unclear | `rp_frontier_sender` |
| `rp_sender2` | minor | confusing | `rp_sender_at_j2` |
| `rp_receiver` | OK | unclear | `rp_frontier_receiver` |
| `rp_j1_recv` | minor | confusing | `rp_recv_at_j1` |

**`send_phase`**

| Name | MC | Read | Rename |
|---|---|---|---|
| `send_phase` | OK | clear | keep |
| `MkSendPhase` | minor | clear | `SendPhase` (deferred) |
| `sp_j` | OK | clear | keep |
| `sp_rr_fw` | minor | confusing | `sp_rand_fwd` |
| `sp_bg` | OK | unclear | `sp_relay_bg` |
| `sp_j_ge2` | OK | clear | keep |
| `sp_active` | OK | unclear | `sp_active_relay` |
| `sp_ahead` | OK | clear | keep |
| `sp_next_behind` | OK | confusing | `sp_intermediate_waiting` |
| `sp_last` | OK | confusing | `sp_at_j_eq_nrelay` |
| `sp_sender2` | minor | confusing | `sp_sender_at_j2` |
| `sp_sender` | OK | unclear | `sp_frontier_sender` |

**`drain_phase`**

| Name | MC | Read | Rename |
|---|---|---|---|
| `drain_phase` | OK | clear | keep |
| `MkDrainPhase` | minor | clear | `DrainPhase` (deferred) |
| `dp_j` | OK | clear | keep |
| `dp_rr_drain` | minor | unclear | `dp_rand` |
| `dp_bg` | OK | unclear | `dp_relay_bg` |
| `dp_safe` | OK | unclear | `dp_bg_not_final_send` |
| `dp_j_lt` | OK | unclear | `dp_j_lt_nrelay` |
| `dp_sender` | OK | unclear | `dp_active_forwarder` |
| `dp_finish` | OK | unclear | `dp_finish_zone` |
| `dp_last` | OK | confusing | `dp_last_relay_recv` |
| `dp_between` | OK | unclear | `dp_intermediate_recv` |

**`tail_phase`**

| Name | MC | Read | Rename |
|---|---|---|---|
| `tail_phase` | OK | clear | keep |
| `MkTailPhase` | minor | clear | `TailPhase` (deferred) |
| `tp_rr_tail` | minor | unclear (double `tail`) | `tp_final_rand` |
| `tp_bg` | OK | unclear | `tp_relay_bg` |
| `tp_last` | OK | confusing | `tp_last_relay_send` |
| `tp_finish` | OK | unclear | `tp_others_finish` |

### Inductives

| Name | File | Kind | MC | Read | Rename |
|---|---|---|---|---|---|
| `phase_reaches` / `pr_refl` / `pr_step` | fsm | ind/cons | OK | clear | keep |
| `known_state` / `KS_done` / `KS_step` | fsm | ind/cons | OK | clear | keep |
| `known_state2` | fsm | ind | violation (`2`) | confusing | `known_ret_state` |
| `KS2_ret` | fsm | cons | violation | confusing | `KnownRetBase` |
| `KS2_step` | fsm | cons | violation | confusing | `KnownRetStep` |
| `drain_steppable` / `DS_last` / `DS_step` | fsm | ind/cons | minor | clear | `drain_chain` / `DrainLast` / `DrainStep` |
| `recv_send_steppable` | fsm | ind | minor | clear | `recv_send_chain` |
| `RSS_to_drain` / `RSS_continue` / `RSS_known` | fsm | cons | minor | mostly clear | `RSDrain` / `RSCont` / `RSS_reached_known` |
| `bg_safe_form` | fsm | ind | OK | unclear | `bg_nonfiring_form` |
| `BSF_finish` / `BSF_fail` / `BSF_send` | fsm | cons | minor | clear | keep |
| `BSF_recv0` | fsm | cons | minor | unclear | `BSF_recv_from0` |
| `BSF_recv_i` | fsm | cons | minor | unclear | `BSF_recv_self` |

### Lemmas — `dsdp_fsm.v` (summary — see source audit for full list)

Major themes:
- `_gen` / `_uncond` / `_concrete` / `_explicit` suffix family
  (`step_ok_recv_send_*`, `step_ok_send_recv_*`,
  `step_ok_drain_drain_gen`, `*_has_progress_gen`, `frag_ok_*_gen`,
  `recv_procs_gen` etc.) — handled in Phase C.
- `chain_acc_shift`, `chain_acc_sum`, `chain_acc_minus_masks`,
  `chain_acc_eq` — mostly clear, keep.
- `alice_body_at_recv`, `alice_foldr_at_tail`, `alice_tail_is_recv`,
  `alice_enc_value`, `enc_curry_eq` — minor `_is_` / `_at_` / `_value`
  suffix violations; convert to MathComp `E` suffix when touched.
- `relay_inter_body_structure`, `relay_last_body_structure` —
  `_structure` violation; rename to `relay_inter_bodyE` /
  `relay_last_bodyE`.
- `bg_frontier_sender_fires` / `bg_frontier_receiver_fires` — `_fires`
  non-idiomatic; rename to `bg_frontier_senderE` /
  `bg_frontier_receiverE`.
- `bg_recv0_fire_send` / `bg_recv0_nop_send` / `bg_recv0_nop_recv` —
  double `recv0` chain; spell out as `bg_recv_from0_...`.
- Numeric-suffix lemmas (`send_procs_0`, `st_send_0`, `frag_ok_send_0`,
  `step_ok_recv_send0`, `step_ok_send0_recv1`, `send_0_has_progress`,
  `initial_step1_has_progress`) — Phase D2 (explicit `at_j0` tags).

### Lemmas — `dsdp_fsm_progress.v` (summary)

- `ks2_*` cluster → Phase B (all `known_ret_*`).
- `mk_next_*` family → Phase E minor cosmetic (defer).
- Numeric-suffix lemmas (`mk_next_sender2`, `mk_next_j1_recv`,
  `send_phase_to_drain_phase_n2`, `tail_phase_from_recv_phase_n1`,
  `known_state2_recv0`) → Phase B/D2 with explicit tags.
- `recv_phase_to_send_phase`, `drain_phase_step`,
  `drain_phase_to_tail_phase`, `recv_phase_to_known` — clear, keep.
- `bg_nop_recv_safe`, `bg_safe_form_step_any`,
  `relay_after_send0_recv0_sig`, `interp_chain_ks2`,
  `init_fuel_transfer`, `one_step_eq_res_procs_local`,
  `alice_step{1,2}_trace_local` — mix of `_local` (Phase A) and
  terminology fixes; addressed individually in scripts.

## Cross-cutting themes (both audits agree)

1. **`_gen` / `_uncond` / `_concrete` / `_explicit` suffix family** —
   both MC violation and readability confusing. `step_ok_recv_send_*`
   is the worst offender. **Fix:** Phase C (sibling consolidation).
2. **`known_state2` / `KS2_*` / `ks2_*` family** — MC violation
   (version number), Read confusing. **Fix:** Phase B cluster rename.
3. **`H`-prefixed hypotheses** — MC violation, Read clear. Deferred
   (Phase E) because of cross-file blast radius.
4. **`local_` prefix on Lets** — MC violation. **Fix:** Phase A
   (`_local` suffix).
5. **Numeric suffixes `_0` / `_2` / `_n1` / `_n2` / `_j1`** — three
   different meanings (arg value, special case, version number). Both
   audits confusing. **Fix:** Phase D2 (explicit semantic tags).
6. **`bg`, `rr`, `fw`, `osp`, `e_loc`** — short unexplained tokens
   flagged by readability. **Fix:** Phase D record field renames for
   `rr_fw` → `rand_fwd`, etc.

## Disagreements between the two audits

- `AHE`, `DI`: MC violation (ALL-CAPS), Read clear. Infotheo convention
  wins (domain abbreviations).
- `Mk*` constructors: MC minor, Read clear. Deferred as low-ROI
  cosmetic.
- `alice_foldr`, `term`, `dp_safe`, `dp_last`, `sp_last`,
  `sp_next_behind`: Read flags confusing; MC accepts them. Readability
  rename wins (these are the biggest "looks fine on paper but baffles
  new readers" cases).

## Rename phases (see plan file for execution details)

- **Phase A** — `local_*` Let cluster (in-file only, ~12 renames).
- **Phase B** — `known_state2` cluster (in-file only, ~17 renames).
- **Phase C** — `_gen`/`_uncond`/`_concrete`/`_explicit` cleanup
  (cross-file, ~25 renames, two-pass with user review).
- **Phase D** — Record field readability (in-file only, ~20 renames).
- **Phase D2** — Semantic-number lemma renames (in-file + light
  cross-file, ~15 renames).
- **Phase E** — DEFERRED: section variables, H-prefix hypotheses,
  `Mk*` constructor prefix. Not executed because blast radius outweighs
  benefit.

## References

- Plan file:
  `/Users/cheng-huiweng/.claude/plans/floofy-sauteeing-journal.md`
- MathComp reference: `/Users/cheng-huiweng/Projects/coq/math-comp`
- Source audit transcripts: conversation session of 2026-04-08.
- Split commit history: `0f68246` → `d9975d4` → `5372d5c` → `64b7c03`.
