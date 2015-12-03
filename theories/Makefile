COQMAKEFILE := Makefile.coq
COQMAKE := +$(MAKE) -f $(COQMAKEFILE)


VS := $(wildcard *.v)

all: $(COQMAKEFILE)
	+$(MAKE) -f $(COQMAKEFILE) all

$(COQMAKEFILE): Makefile $(VS)
	coq_makefile -f _CoqProject $(VS) -o $(COQMAKEFILE)

install: $(COQMAKEFILE)
	$(COQMAKE) install

clean: $(COQMAKEFILE)
	-$(COQMAKE) clean
	rm -f $(COQMAKEFILE)

.PHONY: all install clean
