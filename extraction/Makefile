CAMLC = ocamlc
SUMPROD_CMOS = sumprod.cmo sumprod_test.cmo
SUMPROD_TEST = sumprod_test.byt

tests: run_sumprod

run_sumprod: $(SUMPROD_TEST)
	./$< > $<_out
	@diff $<_ref $<_out && echo "Test ok" || echo "Test fails"

promote: $(SUMPROD_TEST)_out
	cp $(SUMPROD_TEST)_out $(SUMPROD_TEST)_ref

sumprod_test.byt: $(SUMPROD_CMOS)
	$(CAMLC) $(SUMPROD_CMOS) -o $@

clean:
	rm -f *.cm* *.byt *_out *~

distclean: clean
	rm -f sumprod.ml*

.EXTENSIONS: .ml .mli .cmo .cmi

%.cmo: %.ml
	$(CAMLC) -c $<

%.cmi: %.mli
	$(CAMLC) -c $<

sumprod.cmo: sumprod.cmi
sumprod_test.cmo: sumprod.cmi

