COQMAKEFILE := Makefile.coq
COQMAKE := +$(MAKE) -f $(COQMAKEFILE)

LIB := ../../theories
VS := $(wildcard *.v)

all: $(COQMAKEFILE)
	+$(MAKE) -f $(COQMAKEFILE) all

$(COQMAKEFILE): Makefile $(VS)
	coq_makefile -R $(LIB) Autosubst -R . AutosubstPlain $(VS) -o $(COQMAKEFILE)

clean: $(COQMAKEFILE)
	-$(COQMAKE) cleanall
	rm -f $(COQMAKEFILE)

.PHONY: all clean
