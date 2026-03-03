# Migration List - DSDP Codebase Cleanup

**Date:** 2026-01-12  
**Purpose:** Extract general entropy lemmas from `dsdp_entropy.v` into new `entropy_fiber_zpq.v`

---

## New File: entropy_fiber/entropy_fiber_zpq.v

**Location:** `dumas2017dual/entropy_fiber/entropy_fiber_zpq.v`

**Purpose:** Provide entropy framework for fibers over composite modulus Z/pqZ (ring), analogous to how `entropy_linear_fiber.v` provided for finite fields (now deleted).

---

## Lemmas to Extract and Rename

Following infotheo/mathcomp naming conventions (`_E` for equations, `_eq` for equality, no protocol-specific prefixes):

| Current Name (dsdp_entropy.v) | New Name (entropy_fiber_zpq.v) | Lines | Description |
|-------------------------------|--------------------------------|-------|-------------|
| `cond_prob_denom` | `Pr_cond_fiber_marginE` | 252-316 | `Pr[CondRV=c] = |fiber| × Pr[VarRV=v] × Pr[InputRV=i]` |
| `dsdp_uniform_over_solutions_from_joint_uniform` | `cPr_uniform_fiber` | 338-415 | `Pr[VarRV=v | CondRV=c] = |fiber|^-1` from uniform prior + independence |

---

## Wrapper Lemmas to Inline (Remove from dsdp_entropy.v)

These are trivial wrappers that just apply existing infotheo lemmas. **Inline the application directly**:

| Wrapper | Lines | Inlines To | Action |
|---------|-------|------------|--------|
| `joint_factors_by_inde` | 159-175 | Direct use of `inde_RV` definition | **INLINE** - just `inde_RV_sym` + definition |
| `uniform_VarRV_prob` | 178-186 | `fdist_uniformE` | **INLINE** - just `dist_of_RVE` + `fdist_uniformE` |

---

## Lemmas Staying in dsdp_entropy.v (DSDP-specific)

| Lemma | Lines | Reason |
|-------|-------|--------|
| `dsdp_fiber_zpq`, `dsdp_fiber_full_zpq` | 72-77 | DSDP constraint structure |
| `satisfies_constraint_zpq` | 92-96 | DSDP constraint: `s - u1*v1 = u2*v2 + u3*v3` |
| `joint_VarRV_CondRV_eq_InputRV` | 190-249 | Uses DSDP constraint to show S is determined |
| `dsdp_fiber_full_zpq_card` | 420-427 | Wrapper for `fiber_zpq_pair_card` with DSDP params |
| `dsdp_non_solution_zero_prob_zpq` | 430-453 | Applies `cond_prob_zero_outside_constraint` |
| `dsdp_solution_uniform_prob_zpq` | 456-472 | Combines new `cPr_uniform_fiber` with DSDP fiber |
| `dsdp_entropy_uniform_subset_zpq` | 481-508 | Applies `centropy1_uniform_over_set` |
| `dsdp_centropy1_uniform_zpq` | 511-522 | DSDP wrapper |
| `dsdp_centropy_uniform_zpq` (Theorem) | 526-556 | Main DSDP result |

---

## Architecture After Migration

```
Layer 2: entropy_fiber.v (abstract entropy framework)
              ↓
Layer 3: entropy_fiber_zpq.v [NEW] (entropy for rings Z/pqZ)
              ↓
Layer 4: fiber_zpq.v (fiber cardinality for Z/pqZ)
              ↓
Layer 5: dsdp_entropy.v
              ↓
         dsdp_security.v
```

---

## Development Protocol

Migration follows [ai_proof_protocol.md](../../.local/notes/ai_proof_protocol.md):

- Use `Show.` after each tactic for debugging
- Use `apply` instead of `apply:` for better errors
- One tactic per line (no semicolon chaining)
- Test with inline scripts: `cat > /tmp/test.v << 'EOF' ... EOF && coqc`
- Compile: `eval $(opam env) && make file.vo`
