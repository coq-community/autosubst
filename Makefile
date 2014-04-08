COQMAKEFILE := Makefile.coq
COQMAKE := +$(MAKE) -f $(COQMAKEFILE)

COQMAKEFILEEX := Makefile.ex.coq
COQMAKEEX := +$(MAKE) -f $(COQMAKEFILEEX)

ifneq "$(COQBIN)" ""
	COQBIN := $(COQBIN)/
endif

all: $(COQMAKEFILE)
	mkdir -p bin
	$(COQMAKE) all

doc: $(COQMAKEFILEEX)
	mkdir -p doc
	$(COQMAKEEX) html

$(COQMAKEFILE): Make
	$(COQBIN)coq_makefile -f Make > $(COQMAKEFILE)

$(COQMAKEFILEEX): MakeEx
	$(COQBIN)coq_makefile -f MakeEx > $(COQMAKEFILEEX)

install:
	$(COQMAKE) install

clean:
	-$(COQMAKE) clean
	rm -rf $(COQMAKEFILE) bin

.PHONY: clean all install
