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
├── entropy_fiber/                # Layers 2-3: Abstract + Z/pqZ fiber entropy
│   ├── entropy_fiber.v           # Abstract fiber entropy framework
│   └── entropy_fiber_zpq.v       # The same framework but for Z/pqZ (rings)
│   └── linear_fiber_zpq.v        # Fiber cardinality over composite moduli
│                                 # Includes CRT projections to F_p, F_q
│
└── dsdp/                          # Layer 4: DSDP protocol-specific
   ├── dsdp_interface.v          # Abstract DSDP interface (parameterized by Party_HE)
   ├── dsdp_program.v            # Protocol execution model (core syntax)
   ├── dsdp_program_alt_syntax.v # Protocol programs with paper-like custom syntax
   ├── dsdp_correctness.v        # Algebraic correctness lemmas (pulled here)
   ├── dsdp_entropy.v            # DSDP entropy analysis
   ├── dsdp_entropy_trace.v      # Trace-based entropy analysis
   ├── dsdp_syntax_demo.v        # Small demo/tutorial for the custom syntax
   └── dsdp_security.v           # Main security theorems
```

## Dependency Hierarchy

```
                    ┌─────────────────────────────────┐
                    │         Layer 4: DSDP           │
                    │  dsdp_security.v                │
                    │  dsdp_entropy.v                 │
                    │  dsdp_entropy_trace.v           │
                    │  dsdp_correctness.v             │
                    │  dsdp_program.v                 │
                    │  dsdp_program_alt_syntax.v      │
                    │  dsdp_interface.v               │
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
| `dsdp_interface.v` | DSDP interface parameterized by any `Party_HE_scheme` (HE types + operations) |
| `dsdp_program.v` | Protocol execution model (core syntax) |
| `dsdp_program_alt_syntax.v` | Same programs with custom “paper-like” syntax (custom entries / unicode-friendly) |
| `dsdp_correctness.v` | **Correctness lemmas** for the program layer (homomorphic-algebraic reasoning) |
| `dsdp_entropy.v` | Main entropy analysis: H(V2,V3 \| AliceView) |
| `dsdp_entropy_trace.v` | Trace-level definitions/lemmas used to structure the entropy proofs |
| `dsdp_syntax_demo.v` | Small demo/tutorial showcasing the alternative syntax |
| `dsdp_security.v` | Top-level security theorem |

**Note:** Protocol-level correctness facts that used to be scattered near the program definitions are now consolidated in `dsdp_correctness.v` so that the entropy/security layers can import a single correctness API.

**Key Results:**

| Theorem | Statement |
|---------|-----------|
| `dsdp_centropy_uniform_solutions` | H((V2,V3) \| constraint) = log(m) |
| `joint_centropy_reduction` | H((V2,V3) \| AliceView) = H(V2 \| AliceView) |
| `dsdp_entropic_security` | H(V2 \| AliceView) = log(m) > 0 |

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
| 4 (dsdp) | 8 | dsdp_interface, dsdp_program, dsdp_program_alt_syntax, dsdp_correctness, dsdp_entropy, dsdp_entropy_trace, dsdp_syntax_demo, dsdp_security |
| **Total** | **15** | |

## Homomorphic Encryption Layer

The `homomorphic_encryption/` directory has been refactored into an HB-style hierarchy for **party-labeled additive homomorphic encryption**. The shape matches the paper’s presentation:

- **Carrier types**: `Party_HE_types`
- **Operations + laws**: `isPartyHE`
- **Structure**: `Party_HE_scheme`
- **Concrete instances**: `Benaloh_PHE`, `Paillier_PHE` (registered as instances)
- **DSDP interface**: `DSDP_Interface` parameterized by any `Party_HE_scheme`
- **Standard implementation**: `Standard_DI` (implements `DSDP_Interface`)
- **Programs**: written against the interface, so they can be reused across HE instances

```latex
\begin{figure}[H]
\centering
\begin{tikzpicture}[
  node distance=0.8cm and 1.2cm,
  every node/.style={font=\small},
  typebox/.style={
    rectangle, draw, rounded corners=2pt,
    minimum width=2.4cm, minimum height=0.7cm,
    fill=gray!10
  },
  mixinbox/.style={
    rectangle, draw, rounded corners=2pt,
    minimum width=2.4cm, minimum height=0.7cm,
    fill=blue!10
  },
  structbox/.style={
    rectangle, draw, thick, rounded corners=3pt,
    minimum width=3.0cm, minimum height=0.8cm,
    fill=green!15
  },
  instbox/.style={
    rectangle, draw, rounded corners=2pt,
    minimum width=2.2cm, minimum height=0.7cm,
    fill=orange!20
  },
  ifacebox/.style={
    rectangle, draw, rounded corners=2pt,
    minimum width=3.0cm, minimum height=0.7cm,
    fill=yellow!20
  },
  progbox/.style={
    rectangle, draw, thick, rounded corners=3pt,
    minimum width=3.5cm, minimum height=0.8cm,
    fill=purple!15
  },
  arr/.style={-{Stealth[length=2mm]}, thick},
  darr/.style={-{Stealth[length=2mm]}, dashed}
]

% Bottom layer: HB building blocks
\node[typebox] (types) {\texttt{Party\_HE\_types}};
\node[mixinbox, right=of types] (mixin) {\texttt{isPartyHE}};

% Middle-bottom: HB structure
\node[structbox, above=1.0cm of $(types)!0.5!(mixin)$] (scheme)
  {\texttt{Party\_HE\_scheme}};

% Concrete instantiations
\node[instbox, above left=0.6cm and -0.2cm of scheme] (benaloh)
  {\texttt{Benaloh\_PHE}};
\node[instbox, above right=0.6cm and -0.2cm of scheme] (paillier)
  {\texttt{Paillier\_PHE}};

% Interface layer
\node[ifacebox, above=2.0cm of scheme] (iface) {\texttt{DSDP\_Interface}};
\node[ifacebox, right=1.5cm of iface, minimum width=2.6cm] (stdiface)
  {\texttt{Standard\_DI}};

% Top: Protocol programs
\node[progbox, above=1.0cm of $(iface)!0.5!(stdiface)$] (progs)
  {Protocol programs};

% Arrows: HB composition
\draw[arr] (types) -- (scheme);
\draw[arr] (mixin) -- (scheme);

% Arrows: instantiation
\draw[arr] (scheme) -- (benaloh);
\draw[arr] (scheme) -- (paillier);

% Arrows: parameterization
\draw[darr] (benaloh) -- (iface);
\draw[darr] (paillier) -- (iface);
\draw[arr] (iface) -- (stdiface) node[midway, above, font=\scriptsize] {implement};

% Arrows: to programs
\draw[arr] (iface) -- (progs);
\draw[arr] (stdiface) -- (progs);

% Labels
\node[right=0.3cm of mixin, font=\scriptsize, text=gray] {operations and laws};
\node[left=0.3cm of types, font=\scriptsize, text=gray] {carrier types};

\end{tikzpicture}
\caption{Hierarchy of the party-labeled AHE formalization. The
  \texttt{Party\_HE\_types} record provides carrier types
  (party, message, randomness, ciphertext, key), while the
  \texttt{isPartyHE} mixin supplies encryption and homomorphic
  operations together with their equational laws. The
  \hb{} structure \texttt{Party\_HE\_scheme} combines both.
  Concrete instantiations (Benaloh, Paillier) register as instances.
  The \texttt{DSDP\_Interface} is parameterized by any
  \texttt{Party\_HE\_scheme}, and protocol programs use the
  standard implementation \texttt{Standard\_DI}.
  Solid arrows denote composition or instantiation;
  dashed arrows denote parameterization.}
\label{fig:phe-hierarchy}
\end{figure}
```

**Role in DSDP:** Layer 4 (`dumas2017dual/dsdp/`) is parameterized by a `Party_HE_scheme` via `dsdp_interface.v`. This lets the same program/correctness development run with different party-labeled AHE instances (e.g. Benaloh/Paillier), while keeping the higher-level entropy/security arguments modular.

## Related Documents

- `20251209_v2_stats.md`: Complete lemma listing with signatures and meanings
- `DOCUMENTATION_STRUCTURE.md`: Overview of documentation organization
- Individual subdirectories contain detailed mathematical notes for each component

