COQBIN?=$(dir $(shell command -v coqtop || command -v rocq))
COQMAKEFILE?=$(shell command -v coq_makefile || echo "$(COQBIN)rocq makefile")

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

.PHONY: all clean
