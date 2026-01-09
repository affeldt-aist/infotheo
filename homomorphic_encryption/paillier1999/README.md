# Paillier Homomorphic Encryption Formalization

## Reference

- Paillier, P. (1999). "Public-Key Cryptosystems Based on Composite Degree Residuosity Classes"

## Overview

This formalization defines the Paillier encryption scheme and its two core 
homomorphic properties from the cryptographic hypothesis `g_order_n : g ^+ n = 1`.

All theorems are closed under the global context.

### Theorems (in paillier_homo.v)

See also `paillier_he_instance.v` for connection to the idealized model in
`homomorphic_encryption/homomorphic_encryption.v`.

1. **Additive Homomorphism:**
   ```
   E(m₁) · E(m₂) = E((m₁ + m₂) mod n)
   ```

2. **Scalar Multiplication Homomorphism:**
   ```
   E(m₁)^k = E((m₁ · k) mod n)
   ```

3. **Repeated Addition Corollary:**
   ```
   iter k (λc. c · E(m)) E(0) = E(k · m)
   ```

### Lemmas (in paillier_enc.v)

| Lemma | Description | Proof Method |
|-------|-------------|--------------|
| `Zp_add_eqmod` | `m1 + m2 = (m1 + m2)%R %[mod n]` | Using `set`, `transitivity`, `congr`, `Zp_cast` |
| `Zp_mulrn_nat` | `(m *+ k)%R = (m * k) %% (Zp_trunc n).+2` | Induction on `k` |
| `Zp_mulrn_eqmod` | `m1 * m2 = (m1 *+ m2)%R %[mod n]` | Using `Zp_mulrn_nat` |
| `expr_modn` | `g ^+ k = g ^+ (k %% n)` | From `g_order_n` using `exprD`, `exprM`, `exprAC` |
| `enc_mul_dist` | Encryption multiplication distributes | From `expr_modn` + `Zp_add_eqmod` |
| `enc_exp_dist` | Encryption exponentiation distributes | From `expr_modn` + `Zp_mulrn_eqmod` |

### Key Hypothesis

| Hypothesis | Description | Justification |
|------------|-------------|---------------|
| `g_order_n` | Generator order: `g ^+ n = 1` | With g = 1+n: (1+n)^n = 1 (mod n²) |

## Comparison with Benaloh

| Aspect | Benaloh | Paillier |
|--------|---------|----------|
| Working group | Z_n | Z_{n²} |
| Encryption | y^m · u^r | g^m · r^n |
| Message space | Z_r | Z_n |
| Generator constraint | y^r = 1 | g^n = 1 |
| Proof structure | Identical | Identical |

Both schemes follow the same algebraic pattern, enabling code reuse.

## File Structure

- `paillier_enc.v` - Core definitions and lemmas
- `paillier_homo.v` - Homomorphic property theorems
- `paillier_he_instance.v` - Connection to abstract HE interface
