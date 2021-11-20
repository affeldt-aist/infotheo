<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# A Coq formalization of information theory and linear error correcting codes

[![Docker CI][docker-action-shield]][docker-action-link]
[![Nix CI][nix-action-shield]][nix-action-link]

[docker-action-shield]: https://github.com/affeldt-aist/infotheo/workflows/Docker%20CI/badge.svg?branch=master
[docker-action-link]: https://github.com/affeldt-aist/infotheo/actions?query=workflow:"Docker%20CI"

[nix-action-shield]: https://github.com/affeldt-aist/infotheo/workflows/Nix%20CI/badge.svg?branch=master
[nix-action-link]: https://github.com/affeldt-aist/infotheo/actions?query=workflow:"Nix%20CI"




Infotheo is a Coq library for reasoning about discrete probabilities,
information theory, and linear error-correcting codes.

## Meta

- Author(s):
  - Reynald Affeldt, AIST (initial)
  - Manabu Hagiwara, Chiba U. (previously AIST) (initial)
  - Jonas Senizergues, ENS Cachan (internship at AIST) (initial)
  - Jacques Garrigue, Nagoya U.
  - Kazuhiko Sakaguchi, Tsukuba U.
  - Taku Asai, Nagoya U. (M2)
  - Takafumi Saikawa, Nagoya U.
  - Naruomi Obata, Titech (M2)
- License: [LGPL-2.1-or-later](LICENSE)
- Compatible Coq versions: Coq 8.13, Coq 8.14
- Additional dependencies:
  - [MathComp ssreflect](https://math-comp.github.io)
  - [MathComp fingroup](https://math-comp.github.io)
  - [MathComp algebra](https://math-comp.github.io)
  - [MathComp solvable](https://math-comp.github.io)
  - [MathComp field](https://math-comp.github.io)
  - [MathComp analysis](https://github.com/math-comp/analysis)
- Coq namespace: `infotheo`
- Related publication(s):
  - [Formal Adventures in Convex and Conical Spaces](https://arxiv.org/abs/2004.12713) doi:[10.1007/978-3-030-53518-6_2](https://doi.org/10.1007/978-3-030-53518-6_2)
  - [A Library for Formalization of Linear Error-Correcting Codes](https://link.springer.com/article/10.1007/s10817-019-09538-8) doi:[10.1007/s10817-019-09538-8](https://doi.org/10.1007/s10817-019-09538-8)
  - [Reasoning with Conditional Probabilities and Joint Distributions in Coq](https://www.jstage.jst.go.jp/article/jssst/37/3/37_3_79/_article/-char/en) doi:[10.11309/jssst.37.3_79](https://doi.org/10.11309/jssst.37.3_79)
  - [Examples of formal proofs about data compression](http://staff.aist.go.jp/reynald.affeldt/documents/compression-isita2018.pdf) doi:[10.23919/ISITA.2018.8664276](https://doi.org/10.23919/ISITA.2018.8664276)
  - [Formalization of Reed-Solomon codes and progress report on formalization of LDPC codes](http://staff.aist.go.jp/reynald.affeldt/documents/rs_isita2016_author_version.pdf) 
  - [Formalization of error-correcting codes---from Hamming to modern coding theory](http://staff.aist.go.jp/reynald.affeldt/documents/eccITP2015_authorsversion.pdf) doi:[10.1007/978-3-319-22102-1_2](https://doi.org/10.1007/978-3-319-22102-1_2)
  - [Formalization of Shannon’s Theorems](https://link.springer.com/article/10.1007%2Fs10817-013-9298-1) doi:[10.1007/s10817-013-9298-1](https://doi.org/10.1007/s10817-013-9298-1)

## Building and installation instructions

The easiest way to install the latest released version of A Coq formalization of information theory and linear error correcting codes
is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-infotheo
```

To instead build and install manually, do (using GNU `make`):

``` shell
git clone https://github.com/affeldt-aist/infotheo.git
cd infotheo
make   # or make -j <number-of-cores-on-your-machine> 
make -C extraction tests
make install
```

## Acknowledgments

Many thanks to several contributors ([committers](https://github.com/affeldt-aist/infotheo/graphs/contributors)).

The principle of inclusion-exclusion is a contribution by 
Erik Martin-Dorel (University Toulouse III Paul Sabatier, IRIT research laboratory)
(main theorem: Pr_bigcup_incl_excl; commit 956096859ed89325b2bb74033690ac882bbcd64e)

The variable-length source coding theorems are a contribution by
Ryosuke Obi (Chiba U. (M2))
(commit a67da5e24eaaabb345d225a5bd0f5e86d35413a8)
(with Manabu Hagiwara and Mitsuharu Yamamoto)

Commit 64814f529c1819684c4b8060d0779c24c6339041 was originally by Karl Palmskog

The formalization of modern coding theory is a collaboration with
K. Kasai, S. Kuzuoka, R. Obi

Y. Takahashi collaborated to the formalization of linear error-correcting codes

This work was partially supported by a JSPS Grant-in-Aid for Scientific
Research (Project Number: 25289118), a JSPS Grand-in-Aid for Scientific Research (Project Number: 18H03204)

## Documentation

Each file is documented in its header.

Changes are documented in [changelog.txt](changelog.txt).

## Installation with Windows 10

Installation of infotheo on Windows is less simple.
See [this page](https://github.com/affeldt-aist/mathcomp-install/blob/master/install-windows-en.org)
for instructions to install MathComp on Windows 10
(or [this page](https://staff.aist.go.jp/reynald.affeldt/ssrcoq/install.html) for instructions in Japanese).

Once MathComp is installed (with opam), do
`opam install coq-infotheo` or `git clone git@github.com:affeldt-aist/infotheo.git; opam install .`

## Original License

Before version 0.2, infotheo was distributed under the terms of the
`GPL-3.0-or-later` license.
