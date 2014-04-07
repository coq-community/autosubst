COQMAKEFILE := Makefile.coq
COQMAKE := +$(MAKE) -f $(COQMAKEFILE)
ifneq "$(COQBIN)" ""
	COQBIN := $(COQBIN)/
endif

all: $(COQMAKEFILE)
	mkdir -p bin
	$(COQMAKE) all

$(COQMAKEFILE): Make
	$(COQBIN)coq_makefile -f Make > $(COQMAKEFILE)

install:
	$(COQMAKE) install

clean:
	-$(COQMAKE) clean
	rm -rf $(COQMAKEFILE) bin

.PHONY: clean all install
