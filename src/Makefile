PACKAGES   := Data Relations Structures
MODULES    := $(foreach pkg,$(PACKAGES),$(patsubst %.v,%,$(wildcard $(pkg)/*.v)))
SOURCES    := $(MODULES:%=%.v)

COQARGS := -R . FP

.PHONY: all toplevel clean check-admit

all: Makefile.coq
	$(MAKE) -f Makefile.coq

toplevel: coq
	coqtop.opt $(COQARGS)

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq .depend

check-admit:
	grep -n -e 'admit' -e 'Admitted' ${SOURCES}

Makefile.coq: Makefile $(SOURCES)
	coq_makefile $(COQARGS) $(SOURCES) -o Makefile.coq

