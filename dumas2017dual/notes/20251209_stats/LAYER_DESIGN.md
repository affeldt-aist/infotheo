# DSDP Formalization Layer Design

This document describes the layered architecture of the `dumas2017dual` Coq formalization for the DSDP (Dual protocols for private multi-party matrix multiplication) protocol.

## Directory Structure

```
dumas2017dual/
├── lib/                           # Layer 1: General infrastructure
│   ├── extra_algebra.v           # Log, bigop, Z/mZ unit lemmas
│   ├── extra_proba.v             # Conditional probability, RV permutations
│   ├── extra_entropy.v           # Entropy sum, cond. independence, zero entropy
│   └── rouche_capelli.v          # Linear system solution counting (Rouché-Capelli)
│
├── entropy_fiber/                 # Layers 2-3: Abstract + Z/pqZ fiber entropy
│   ├── entropy_fiber.v           # Abstract fiber entropy framework
│   └── entropy_fiber_zpq.v       # Entropy framework for Z/pqZ (rings)
│
├── fiber/                         # Layer 3: Z/pqZ fiber cardinality
│   └── linear_fiber_zpq.v        # Fiber cardinality over composite moduli
│                                  # Includes CRT projections to F_p, F_q
│
└── dsdp/                          # Layer 4: DSDP protocol-specific
   ├── dsdp_program.v            # Protocol execution model
   ├── dsdp_entropy.v            # DSDP entropy analysis
   ├── dsdp_entropy_trace.v      # Trace-based entropy analysis
   └── dsdp_security.v           # Main security theorems
```

## Dependency Hierarchy

```
                    ┌─────────────────────────────────┐
                    │         Layer 4: DSDP           │
                    │  dsdp_security.v                │
                    │  dsdp_entropy.v                 │
                    │  dsdp_program.v                 │
                    └────────────┬────────────────────┘
                                 │
                      ┌──────────┴──────────┐
                      │                     │
        ┌─────────────▼─────────────┐  ┌────▼──────────────────┐
        │ Layer 3: linear_fiber_zpq │  │ entropy_fiber_zpq.v   │
        │ (fiber card + CRT proj)   │  │ (entropy framework)   │
        └─────────────┬─────────────┘  └────────┬──────────────┘
                      │                         │
                      └──────────┬──────────────┘
                                 │
                    ┌────────────▼──────────────────┐
                    │   Layer 2: Abstract Fibers    │
                    │   entropy_fiber.v             │
                    └────────────┬──────────────────┘
                                 │
        ┌────────────────────────┼──────────────────────────┐
        │                        │                          │
┌───────▼───────┐  ┌─────────────▼────────────┐  ┌─────────▼────────┐
│ extra_algebra │  │     extra_entropy        │  │ rouche_capelli   │
│    (.v)       │  │        (.v)              │  │     (.v)         │
└───────┬───────┘  └─────────────┬────────────┘  └─────────┬────────┘
        │                        │                          │
        └────────────────────────┼──────────────────────────┘
                                 │
                    ┌────────────▼──────────────────┐
                    │      Layer 1: Infrastructure  │
                    │   (infotheo core libraries)   │
                    └───────────────────────────────┘
```

**Note:** `linear_fiber_zpq.v` imports `rouche_capelli.v` and provides CRT projections
(`proj_Fp`, `proj_Fq`) for applying field-based theorems to ring problems.

## Layer Descriptions

### Layer 1: General Infrastructure (`lib/`)

**Purpose:** Provide general-purpose lemmas extending MathComp and infotheo that are not specific to DSDP or even to secure computation.

| File | Content | Key Lemmas |
|------|---------|------------|
| `extra_algebra.v` | Log properties, bigop manipulation, Z/mZ units | `logr_eq1`, `Zp_unitP`, `Zp_Fp_card_eq` |
| `extra_proba.v` | Conditional probability, RV permutation lemmas | `sum_cPr_eq`, `jproduct_ruleRV`, `centropyA` |
| `extra_entropy.v` | Entropy characterization, conditional independence | `cinde_centropy_eq`, `zero_centropy_eq_deterministic`, `inde_cond_entropy` |
| `rouche_capelli.v` | Linear system solution counting | `count_affine_solutions_explicit`, `count_affine_solutions_rank1` |

**Design Principle:** These lemmas could potentially be contributed upstream to infotheo or mathcomp-analysis.

### Layer 2: Abstract Fiber Entropy (`entropy_fiber/entropy_fiber.v`)

**Purpose:** Establish the connection between fiber (preimage) structure and entropy calculations in a type-generic way.

**Key Concepts:**
- **Fiber:** The preimage `{x | f(x) = c}` of a value c under function f
- **Constant fiber entropy:** When all fibers have equal cardinality k, conditional entropy = log(k)

**Key Lemmas:**

| Lemma | Statement |
|-------|-----------|
| `centropy1_uniform_fiber` | H(X\|Y=c) = log\|fiber(c)\| when X is uniform over fiber |
| `centropy_constant_fibers` | H(X\|Y) = log(k) when all fibers have size k |
| `centropy_determined_contract` | H((X,Y)\|Cond) = H(X\|Cond) when Y is determined by X |

### Layer 3: Z/pqZ Specialization (Parallel)

This layer has two parallel modules, both depending only on Layer 2:

#### entropy_fiber_zpq.v - Entropy Framework

**Purpose:** Provide entropy lemmas for reasoning about conditional probabilities when random variables are constrained by linear equations over the ring Z/(pq)Z.

**Key Lemmas:**

| Lemma | Statement |
|-------|-----------|
| `Pr_cond_fiber_marginE` | Pr[CondRV=c] = \|fiber(c)\| × (m²)^-1 × Pr[InputRV=proj(c)] |
| `cPr_uniform_fiber` | Pr[VarRV=v \| CondRV=c] = \|fiber(c)\|^-1 from uniform prior |

#### linear_fiber_zpq.v - Fiber Cardinality

**Purpose:** Handle fiber cardinality over composite moduli Z/(pq)Z where p, q are primes.

**Key Concepts:**
- **Small component:** An element u < min(p,q) is coprime to pq, hence a unit
- **CRT Projections:** `proj_Fp`, `proj_Fq` project Z/(pq)Z → F_p, F_q for applying field theorems

**Key Lemmas:**

| Lemma | Statement |
|-------|-----------|
| `lt_minpq_coprime` | u < min(p,q) ⟹ gcd(u, pq) = 1 |
| `linear_fiber_card` | \|{v \| u·v = s}\| = m^(n-1) when u has a unit component |
| `linear_fiber_2d_card` | 2D fiber cardinality = m for small coefficients |
| `proj_Fp_add`, `proj_Fp_mul` | CRT projections are ring homomorphisms |

### Layer 4: DSDP Protocol (`dsdp/`)

**Purpose:** Formalize the specific DSDP protocol and prove its security properties.

| File | Content |
|------|---------|
| `dsdp_extra.v` | Auxiliary definitions for DSDP |
| `dsdp_program.v` | Protocol execution model, trace structure |
| `dsdp_entropy.v` | Main entropy analysis: H(V2,V3 \| AliceView) |
| `dsdp_security.v` | Top-level security theorem |

**Key Results:**

| Theorem | Statement |
|---------|-----------|
| `dsdp_centropy_uniform_solutions` | H((V2,V3) \| constraint) = log(m) |
| `privacy_by_bonded_leakage` | H((V2,V3) \| AliceView) = H(V2 \| AliceView) |
| `dsdp_security_bounded_leakage` | H(V2 \| AliceView) = log(m) > 0 |

## Design Principles

### 1. Abstraction Before Specialization
Each layer provides abstract results that are then specialized by the layer above. This enables:
- Reuse of proofs across different instantiations
- Clear separation of mathematical concerns
- Potential generalization to other protocols

### 2. Wrapper Lemmas
When general results (e.g., Rouché-Capelli) use different notation than entropy applications need (matrices vs. dot products), we provide thin wrappers that:
- Hide irrelevant complexity
- Provide the natural API for the domain
- Document WHY the wrapper exists

### 3. Naming Conventions (MathComp Style)
- `_card`: Cardinality lemmas (e.g., `fiber_card`)
- `_E` or `_eq`: Equality/characterization (e.g., `S_E`)
- `_neq0`: Non-zero conditions
- `centropy_`: Conditional entropy lemmas
- `dsdp_`: Protocol-specific lemmas

### 4. Comment Documentation
Each lemma should have a comment explaining:
- What it states (in plain mathematical terms)
- Why it's needed (its role in the overall proof)
- How it relates to other lemmas (wrappers, specializations)

## File Statistics

| Layer | Files | Description |
|-------|-------|-------------|
| 1 (lib) | 4 | extra_algebra, extra_proba, extra_entropy, rouche_capelli |
| 2 (entropy_fiber) | 1 | entropy_fiber.v |
| 3 (fiber + entropy_zpq) | 2 | linear_fiber_zpq.v, entropy_fiber_zpq.v |
| 4 (dsdp) | 4 | dsdp_program, dsdp_entropy, dsdp_entropy_trace, dsdp_security |
| **Total** | **11** | |

## Homomorphic Encryption Layer

The `homomorphic_encryption/` directory provides a layered architecture for homomorphic encryption:

```
  Section he_ideal (backward compatible, used by dsdp)
  ≈ Party_Ideal_HE(Ideal_HE(msg))
                      |
                      v uses
  Party_Ideal_HE (party labels + Ideal_HE)
  - enc = (party * ct)
  - E, D, Emul, Epow with party labels
                      |
                      v wraps
  HE_SIG (abstract interface in he_sig.v)
  - msg, ct, rand, enc
  - Emul : ct -> ct -> ct
  - Epow : ct -> msg -> ct
        /              |               \
       v               v                v
  Ideal_HE         Benaloh_HE       Paillier_HE
  ct = msg         ct = 'Z_n        ct = 'Z_{n²}
  Emul = +         Emul = *         Emul = *
  Epow = *         Epow = ^+        Epow = ^+
```

**Files:**

| File | Description |
|------|-------------|
| `he_sig.v` | `HE_SIG` module signature: abstract HE interface |
| `homomorphic_encryption.v` | `Ideal_HE`, `Party_Ideal_HE`, `Section he_ideal`, party/key types |
| `benaloh1994/benaloh_he_instance.v` | `Benaloh_HE` functor implementing `HE_SIG` |
| `paillier1999/paillier_he_instance.v` | `Paillier_HE` functor implementing `HE_SIG` |

**Key Components (from `homomorphic_encryption.v`):**

| Component | Description |
|-----------|-------------|
| `party` | Finite type for protocol participants (Alice, Bob, Charlie) |
| `key` | Key types (Dec, Enc) for encryption/decryption |
| `HE_SIG` | Abstract module signature with `enc`, `Emul`, `Epow` |
| `Ideal_HE` | Implements `HE_SIG` with `ct = msg` (identity encryption) |
| `Party_Ideal_HE` | Wraps `Ideal_HE` with party labels |
| `Section he_ideal` | Backward-compatible interface for dsdp (E, D, Emul, Epow) |
| `p.-enc T` | Type-level encryption label for party `p` |
| `p.-key k T` | Type-level key label for party `p` with key type `k` |

**Key Lemmas:**

| Lemma | Statement |
|-------|-----------|
| `Emul_hom` | `Emul(enc m1, enc m2) = enc(m1 + m2)` — homomorphic addition |
| `Epow_hom` | `Epow(enc m1, m2) = enc(m1 * m2)` — homomorphic scalar mult |
| `card_party_key` | `#|{:p.-key k T}| = #|T|` — key types preserve cardinality |
| `card_enc_for` | `#|{:p.-enc T}| = #|T|` — encryption types preserve cardinality |
| `E_enc_unif` | Encryptions are uniformly distributed (axiom) |
| `E_enc_inde` | Encryptions are independent of other random variables (axiom) |
| `E_enc_ce_removal` | `H(Z | [%X, E]) = H(Z | X)` — encryption can be removed from conditioning |

**Role in DSDP:** The `Section he_ideal` provides party-labeled encryption operations (`E`, `D`, `Emul`, `Epow`) used by dsdp protocol proofs. The semantic security axioms (`E_enc_unif`, `E_enc_inde`) allow DSDP to treat encrypted values as independent random values, which is essential for the entropy-based security analysis.

## Related Documents

- `20251209_v2_stats.md`: Complete lemma listing with signatures and meanings
- `DOCUMENTATION_STRUCTURE.md`: Overview of documentation organization
- Individual subdirectories contain detailed mathematical notes for each component

