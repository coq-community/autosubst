THEORIES := $(wildcard theories/*.v)
EXAMPLES := $(wildcard examples/*.v)

all:
	$(MAKE) -C theories
	$(MAKE) -C examples

clean:
	$(MAKE) -C theories clean
	$(MAKE) -C examples clean
	rm -rf html

dist:
	git archive -o autosubst-HEAD.tar.gz HEAD

doc: all
	- mkdir html
	coqdoc --table-of-contents --html -d html \
	  -R theories Autosubst $(THEORIES) $(EXAMPLES)
	cp extra/*.css extra/*.ttf html/


install:
	$(MAKE) -C theories install

.PHONY: all clean install
