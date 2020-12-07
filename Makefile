THEORIES := $(wildcard theories/*.v)
EXAMPLES_PLAIN := $(wildcard examples/plain/*.v)
EXAMPLES_SSR   := $(wildcard examples/ssr/*.v)
DOC := doc/
EXTRA_DIR := coqdocjs/extra/
HEADER := $(EXTRA_DIR)header.html
FOOTER := $(EXTRA_DIR)footer.html
COQDOCFLAGS := \
  --external 'http://ssr2.msr-inria.inria.fr/doc/ssreflect-1.5/' Ssreflect \
  --external 'http://ssr2.msr-inria.inria.fr/doc/mathcomp-1.5/' MathComp \
  --toc --toc-depth 2 --html --interpolate \
  --index indexpage --no-lib-name --parse-comments \
  --with-header $(HEADER) --with-footer $(FOOTER) \
  -d $(DOC)

ifneq "$(COQBIN)" ""
        COQBIN := $(COQBIN)/
endif

lib:
	$(MAKE) -C theories

all: lib examples-plain examples-ssr

examples-plain: lib
	$(MAKE) -C examples/plain

examples-ssr: lib
	$(MAKE) -C examples/ssr

clean-doc:
	$(MAKE) -f TexMakefile clean
	rm -rf $(DOC)

clean: clean-doc
	$(MAKE) -C theories clean
	$(MAKE) -C "examples/plain" clean
	$(MAKE) -C "examples/ssr" clean

dist:
	git archive -o autosubst-HEAD.tar.gz HEAD

doc: clean-doc manual.pdf
	- mkdir -p $(DOC)
	coqdoc $(COQDOCFLAGS) -R theories Autosubst -R examples/plain Plain \
	  -R examples/ssr Ssr $(THEORIES) $(EXAMPLES_PLAIN) $(EXAMPLES_SSR)
	cp $(EXTRA_DIR)resources/* $(DOC)
	cp manual.pdf $(DOC)

install:
	$(MAKE) -C theories install

%.pdf:
	$(MAKE) -f TexMakefile $@

.PHONY: all clean clean-doc dist doc examples-plain examples-ssr install lib
