all: Makefile.coq
	$(MAKE) -f $< $@

clean: Makefile.coq
	$(MAKE) -f $< $@
	$(RM) $<* .*.aux

Makefile.coq: _CoqProject
	$(COQBIN)coq_makefile -f $< -o $@
