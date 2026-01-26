#COQBIN?=$(dir $(shell command -v coqtop || command -v rocq))
#COQMAKEFILE?=$(shell command -v coq_makefile || echo "$(COQBIN)rocq makefile")
COQMAKEFILE=coq_makefile

all: Makefile.coq
	$(MAKE) -f Makefile.coq all

clean: Makefile.coq
	$(MAKE) -f Makefile.coq cleanall
	rm -f Makefile.coq Makefile.coq.conf

Makefile.coq: _CoqProject
	$(COQMAKEFILE) -f _CoqProject -o Makefile.coq

_CoqProject Makefile: ;

%: Makefile.coq
	$(MAKE) -f Makefile.coq $@

# DSDP: rebuild smc, homomorphic_encryption, and dumas2017dual
DSDP_DIRS := smc homomorphic_encryption dumas2017dual
DSDP_VO := $(patsubst %.v,%.vo,$(shell grep -E '^(smc/|homomorphic_encryption/|dumas2017dual/)' _CoqProject))

dsdp: Makefile.coq
	find $(DSDP_DIRS) \( -name "*.vo" -o -name "*.vos" -o -name "*.vok" -o -name "*.glob" \) -delete 2>/dev/null || true
	$(MAKE) -f Makefile.coq $(DSDP_VO)

.PHONY: all clean dsdp
