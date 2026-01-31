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

# SMC: rebuild smc
SMC_DIRS := smc
SMC_VO := $(patsubst %.v,%.vo,$(shell grep -E '^(smc/)' _CoqProject))

smc: Makefile.coq
	$(MAKE) -f Makefile.coq $(SMC_VO)

smc-rebuild: Makefile.coq
	find $(SMC_DIRS) \( -name "*.vo" -o -name "*.vos" -o -name "*.vok" -o -name "*.glob" \) -delete 2>/dev/null || true
	$(MAKE) -f Makefile.coq $(SMC_VO)

# DSDP: rebuild smc, homomorphic_encryption, and dumas2017dual

DSDP_DIRS := smc homomorphic_encryption dumas2017dual
DSDP_VO := $(patsubst %.v,%.vo,$(shell grep -E '^(smc/|homomorphic_encryption/|dumas2017dual/)' _CoqProject))

dsdp: Makefile.coq
	$(MAKE) -f Makefile.coq $(DSDP_VO)

dsdp-rebuild: Makefile.coq
	find $(DSDP_DIRS) \( -name "*.vo" -o -name "*.vos" -o -name "*.vok" -o -name "*.glob" \) -delete 2>/dev/null || true
	$(MAKE) -f Makefile.coq $(DSDP_VO)

# SPP: rebuild smc du2002
SPP_DIRS := smc du2002
SPP_VO := $(patsubst %.v,%.vo,$(shell grep -E '^(smc/|du2002/)' _CoqProject))

spp: Makefile.coq
	$(MAKE) -f Makefile.coq $(SPP_VO)

spp-rebuild: Makefile.coq
	find $(SPP_DIRS) \( -name "*.vo" -o -name "*.vos" -o -name "*.vok" -o -name "*.glob" \) -delete 2>/dev/null || true
	$(MAKE) -f Makefile.coq $(SPP_VO)

.PHONY: all clean dsdp
