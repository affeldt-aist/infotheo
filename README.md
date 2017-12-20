infotheo
========

This is a Coq formalization of information theory and linear
error-correcting codes.

## Requirements

The development version of the Mathematical Components library:
https://github.com/math-comp/math-comp
(because we use the fieldext and finfield libraries).

Coq 8.7.
Compilation is almost fine with Coq 8.6 except for 
minor problems due to recent changes in the Reals library.

## Install

After gunzip/untar, do
cd infotheo
and do
coq_makefile -f _CoqProject -o Makefile
make

## License

GNU GPLv3

## Authors

See infotheo_authors.txt

