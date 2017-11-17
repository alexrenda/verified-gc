# Makefile originally taken from coq-club

TARGET := gc

all: coq
.PHONY: all clean

%: Makefile.coq
	+make -f Makefile.coq $@
	+make -f Makefile.tex $@ TARGET=$(TARGET)

coq: Makefile.coq
	+make -f Makefile.coq all

clean: Makefile.coq
	+make -f Makefile.coq clean
	+make -f Makefile.tex clean TARGET=$(TARGET)
	rm -f Makefile.coq

Makefile.coq: _CoqProject Makefile
	coq_makefile -f _CoqProject | sed 's/$$(COQCHK) $$(COQCHKFLAGS) $$(COQLIBS)/$$(COQCHK) $$(COQCHKFLAGS) $$(subst -Q,-R,$$(COQLIBS))/' > Makefile.coq

_CoqProject: ;

Makefile: ;
