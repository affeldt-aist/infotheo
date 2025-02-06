# DSDP Security Analysis Documentation

This directory contains mathematical documentation for the DSDP security formalization.

## Files

- **`field_approximation.tex`**: Complete mathematical exposition of the field approximation technique for Benaloh cryptosystem
- **`Makefile`**: Build script for compiling the LaTeX document
- **`README.md`**: This file

## Building the PDF

To compile the documentation:

```bash
cd dumas2017dual/notes
make
```

This will generate `field_approximation.pdf`.

To view the PDF after building:

```bash
make view
```

To clean auxiliary files:

```bash
make clean
```

## Contents Overview

The `field_approximation.tex` document covers:

1. **Mathematical background**: Differences between finite fields and composite modulus rings
2. **Statistical distance analysis**: Quantifying the approximation error
3. **Negligibility theory**: Formal definition and security parameters
4. **Concrete examples**: Both toy (p=3, q=5) and cryptographic (p,q ≈ 2^1024) parameters
5. **Conditions for validity**: Precise requirements on prime sizes
6. **Simulation paradigm**: Connection to standard cryptographic methodology
7. **Implementation notes**: How this applies to the Coq formalization

## Key Result

For cryptographic parameters (p, q ≥ 2^1024), the statistical distance between:
- Real world: Z/(pq) (composite modulus ring)
- Ideal world: 'F_m (prime field)

is less than 2^-1000, which is cryptographically negligible.

This justifies using field-based tools in the Coq formalization while maintaining security guarantees for ring-based implementations.

## Related Code

- `dsdp_security.v`: Main security theorems connecting algebra and entropy
- `dsdp_algebra.v`: Algebraic structure of solution spaces
- `dsdp_entropy.v`: Information-theoretic security bounds


