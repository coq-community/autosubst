THEORIES := $(wildcard theories/*.v)
EXAMPLES := $(wildcard examples/*.v)
DOC := doc/
EXTRA_DIR := extra/
HEADER := $(EXTRA_DIR)header.html
FOOTER := $(EXTRA_DIR)footer.html
COQDOCFLAGS := --external 'http://ssr2.msr-inria.inria.fr/doc/ssreflect-1.5/' Ssreflect --external 'http://ssr2.msr-inria.inria.fr/doc/mathcomp-1.5/' MathComp \
	       --toc --html --interpolate \
	       --index indexpage --no-lib-name --parse-comments \
	       --with-header $(HEADER) --with-footer $(FOOTER) \
	       -d $(DOC)

all:
	$(MAKE) -C theories
	$(MAKE) -C examples

clean:
	$(MAKE) -C theories clean
	$(MAKE) -C examples clean
	rm -rf $(DOC)

dist:
	git archive -o autosubst-HEAD.tar.gz HEAD

doc: all
	- mkdir -p $(DOC)
	coqdoc $(COQDOCFLAGS) -R theories Autosubst $(THEORIES) $(EXAMPLES)
	cp $(EXTRA_DIR)resources/* $(DOC)


install:
	$(MAKE) -C theories install

.PHONY: all clean dist doc install
