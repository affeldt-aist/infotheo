# Deletion List - DSDP Codebase Cleanup

**Date:** 2026-01-12  
**Purpose:** Remove obsolete files and lemmas (field analysis out of scope)

---

## File Deletions (2 files)

| File | Lines | Reason |
|------|-------|--------|
| `entropy_fiber/entropy_linear_fiber.v` | ~540 | Field-based analysis not in scope; superseded by `entropy_fiber_zpq.v` |
| `dsdp/dsdp_algebra.v` | ~215 | Field-based analysis not in scope; DSDP uses Z/pqZ ring path |

---

## Lemma Deletions by Layer

### Layer 5: DSDP Protocol

| Lemma | File | Lines | Reason |
|-------|------|-------|--------|
| `U3_nonzero` | `dsdp_entropy.v` | 953-966 | Isolated; helper for removed/refactored proof path |
| `D2_indep_V2` | `dsdp_security.v` | 842-867 | Isolated independence lemma; unused proof artifact |
| `U3_R3_indep_V1` | `dsdp_security.v` | 375-390 | Isolated independence lemma |
| `V2V3_indep_V1` | `dsdp_security.v` | 1003-1030 | Isolated; superseded by structured version |
| `VU3_indep_V1` | `dsdp_security.v` | 393-407 | Isolated independence lemma |

### Layer 2: Abstract Fibers

| Lemma | File | Lines | Reason |
|-------|------|-------|--------|
| `entropy_fdist_uniform_set` | `entropy_fiber.v` | 200-222 | Isolated; variant of entropy_uniform_set (redundant) |
| `mem_image_set` | `entropy_fiber.v` | 56-68 | Isolated helper |
| `uniform_prior_cond_uniform_fiber` | `entropy_fiber.v` | 244-254 | Isolated; never connected |

### Layer 1: Infrastructure (lib/)

| Lemma | File | Lines | Reason |
|-------|------|-------|--------|
| `entropy_formula_same` | `extra_algebra.v` | 183 | Single line placeholder |
| `pfwd1_pair4_swap34` | `extra_proba.v` | 248-256 | Isolated permutation lemma |

---

## Requires Investigation (Do Not Delete Yet)

| Lemma | File | Lines | Reason |
|-------|------|-------|--------|
| `dsdp_is_correct_zpq` | `dsdp_entropy_trace.v` | 122-153 | Isolated correctness lemma; may be WIP |
| `dsdp_ok` | `dsdp_program.v` | 145-206 | Large isolated lemma (61 lines); may be WIP |

---

## Keep (Do Not Delete)

### Documentation/Future Use

| Lemma | File | Reason |
|-------|------|--------|
| `dsdp_var_entropy_zpq` | `dsdp_entropy.v` | Documents unconditional entropy H(V2,V3) |
| `centropy_determined_contract` | `entropy_fiber.v` | May be useful for future H(X,Y|Cond)=H(X|Cond) proofs |
| `Zp_Fp_card_eq` | `extra_algebra.v` | Documentation: Z_p and F_p have same cardinality |
| `bigD1_filter` | `extra_algebra.v` | Useful bigop infrastructure |
| `jproduct_ruleRV` | `extra_proba.v` | Joint product rule; may be useful |

### All rouche_capelli.v lemmas (useful linear algebra infrastructure)

| Lemma | Lines | Description |
|-------|-------|-------------|
| `cancel_row_free` | 280-290 | Row operation lemma |
| `castmx_mul_row` | 223-229 | Matrix cast lemma |
| `exists_nonzero_kernel` | 149-156 | Kernel existence |
| `sub_coker_colspan` | 199-208 | Cokernel lemma |
| `submx_castmx` | 212-220 | Subspace lemma |

---

## Summary

| Action | Count | Files/Lemmas |
|--------|-------|--------------|
| Delete files | 2 | `entropy_linear_fiber.v`, `dsdp_algebra.v` |
| Delete lemmas | 10 | Listed above |
| Investigate | 2 | `dsdp_is_correct_zpq`, `dsdp_ok` |
| Keep | 10+ | Listed above |
