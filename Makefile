all: CoqMakefile
	+@$(MAKE) -f CoqMakefile all
.PHONY: all

CoqMakefile: _CoqProject Makefile
	$(COQBIN)coq_makefile -f _CoqProject -o CoqMakefile
