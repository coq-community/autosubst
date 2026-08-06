COQMAKEFILE := Makefile.coq
COQMAKE := +$(MAKE) -f $(COQMAKEFILE)

LIB := .
VS := $(wildcard *.v)

all: $(COQMAKEFILE)
	+$(MAKE) -f $(COQMAKEFILE) all

$(COQMAKEFILE): Makefile $(VS)
	rocq makefile -R $(LIB) Autosubst $(VS) -o $(COQMAKEFILE) -arg "-w -notation-overridden"

install: $(COQMAKEFILE)
	$(COQMAKE) install

clean: $(COQMAKEFILE)
	-$(COQMAKE) clean
	rm -f $(COQMAKEFILE)

.PHONY: all install clean
