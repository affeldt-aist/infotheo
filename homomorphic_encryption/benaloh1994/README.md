# Benaloh Homomorphic Encryption Formalization

## Reference

- Benaloh, J. (1994). "Dense Probabilistic Encryption"
- Benaloh, J., Tuinstra, D. (1994). "Receipt-Free Secret-Ballot Elections"

## Overview

This formalization defines the Benaloh encryption scheme and its two core 
homomorphic properties from the cryptographic hypothesis `y_order_r : y ^+ r = 1`.

All theorems are closed under the global context.

### Theorems (in benaloh_homo.v)

1. **Additive Homomorphism:**
   ```
   E(m₁) · E(m₂) = E((m₁ + m₂) mod r)
   ```

2. **Scalar Multiplication Homomorphism:**
   ```
   E(m₁)^(m₂) = E((m₁ · m₂) mod r)
   ```

3. **Repeated Addition Corollary:**
   ```
   iter k (λc. c · E(m)) E(0) = E(k · m)
   ```

### Lemmas (in benaloh_enc.v)

| Lemma | Description | Proof Method |
|-------|-------------|--------------|
| `Zp_add_eqmod` | `m1 + m2 = (m1 + m2)%R %[mod r]` | Using `set` to extract nats, `transitivity`, `congr`, `Zp_cast` |
| `Zp_mulrn_nat` | `(m *+ k)%R = (m * k) %% (Zp_trunc r).+2` | Induction on `k` |
| `Zp_mulrn_eqmod` | `m1 * m2 = (m1 *+ m2)%R %[mod r]` | Using `Zp_mulrn_nat` and same technique as `Zp_add_eqmod` |
| `expr_modr` | `y ^+ k = y ^+ (k %% r)` | From `y_order_r` using `exprD`, `exprM`, `exprAC`, `expr1n`, `mul1r` |
| `enc_mul_dist` | Encryption multiplication distributes | From `expr_modr` + `Zp_add_eqmod` + `mulrACA` + `exprMn` + `exprD` |
| `enc_exp_dist` | Encryption exponentiation distributes | From `expr_modr` + `Zp_mulrn_eqmod` + `exprMn_comm` + `exprM` |

### Key Hypothesis

| Hypothesis | Description | Justification |
|------------|-------------|---------------|
| `y_order_r` | Generator order: `y ^+ r = 1` | Standard Benaloh cryptographic constraint |

This hypothesis is the fundamental cryptographic requirement: the generator `y`
must have order dividing `r` in the message encoding subgroup. This ensures
that `y^k` depends only on `k mod r`.

### Technical Note: Overcoming Dependent Type Obstacles

The proofs required a technique to handle Coq's dependent types with `Zp_cast`.

**The Problem:** Variables `m1, m2 : 'Z_r = ordinal (Zp_trunc r).+2` have types
depending on `(Zp_trunc r).+2`. Directly rewriting `(Zp_trunc r).+2` to `r` using
`Zp_cast r_gt1` fails because Coq would need to change the types of `m1`, `m2`.

**The Solution:**
1. Use `set n1 := (m1 : nat)` to extract pure nat values
2. Use `transitivity` to introduce an intermediate goal
3. Use `congr (modn _ r)` to focus on the modulus argument
4. In this context, `(Zp_trunc r).+2` appears only as a simple nat argument
5. Now `rewrite Hr` (where `Hr : (Zp_trunc r).+2 = r`) succeeds

## Future Work

### Remove y_order_r hypothesis

To prove `y_order_r` from first principles, the following MathComp extensions
would be needed:

### 1. Multiplicative Group of Z/nZ for Composite n

**Current MathComp:** Only `units_Zp` for prime p

**Needed:**

- Define `units_Zn` for composite n = p*q
- Prove `|units_Zn| = φ(n) = (p-1)(q-1)`
- Construct via Chinese Remainder Theorem: `units_Zn ≃ units_Zp × units_Zq`

**Required lemmas:**

```coq
Definition units_Zn (n : nat) : finGroupType.
Lemma card_units_Zn : #|units_Zn n| = totient n.
Lemma units_Zn_CRT : units_Zn (p * q) ≃ units_Zp p × units_Zp q.
```

### 2. Higher Residuosity

**Current MathComp:** Not available

**Needed:**

- Define r-th residue: `is_rth_residue x n r := ∃y, y^r ≡ x (mod n)`
- Characterization: `x^(φ(n)/r) ≡ 1 (mod n) ↔ is_rth_residue x n r`
- Non-residue generator existence

**Required lemmas:**

```coq
Definition is_rth_residue (x n r : nat) : bool.
Lemma rth_residue_char : is_rth_residue x n r <-> x^(totient n / r) ≡ 1 [mod n].
Lemma exists_non_residue : ∃y, ~is_rth_residue y n r.
```

### 3. Modular Exponentiation in Ring Context

**Status:** DONE - MathComp already provides these lemmas:

- `exprD : x ^+ (m + n) = x ^+ m * x ^+ n`
- `exprM : x ^+ (m * n) = (x ^+ m) ^+ n`
- `exprMn : (x * y) ^+ n = x ^+ n * y ^+ n` (commutative rings)
- `exprAC : x ^+ m ^+ n = x ^+ n ^+ m`

These are used in the current proofs of `enc_mul_dist` and `enc_exp_dist`.

### 4. Discrete Logarithm (for Decryption)

**Current MathComp:** Not available

**Needed for correctness theorem:**

- Define discrete log in cyclic subgroup
- Prove existence and uniqueness

```coq
Definition dlog (g x : 'Z_n) : option nat.
Lemma dlog_correct : dlog g (g^+k) = Some (k mod ord g).
```

## Estimated Effort for Remaining Work

| Component | Difficulty | Lines of Code | Status |
|-----------|------------|---------------|--------|
| Ring exponentiation lemmas | Easy | ~100 | Done (MathComp) |
| Homomorphic properties | Medium | ~150 | Done |
| units_Zn construction | Medium | ~200 | Pending |
| Higher residuosity | Hard | ~300 | Pending |
| Discrete log | Medium | ~150 | Pending |
| **Total remaining** | | **~650** |

## References for Full Implementation

- MathComp `zmodp.v`: Units of Z/pZ
- MathComp `cyclic.v`: Cyclic group theory
- MathComp `prime.v`: Totient function
- Fouque & Laguillaumie (2011): "Benaloh's Dense Probabilistic Encryption Revisited"
