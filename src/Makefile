PACKAGES   := Data Relations Structures
MODULES    := $(foreach pkg,$(PACKAGES),$(patsubst %.v,%,$(wildcard $(pkg)/*.v))) \
	            FP FPNotation
SOURCES    := $(MODULES:%=%.v)

COQ_ARGS :=
COQ_MAKEFILE_ARGS := -R . FP -arg "$(COQ_ARGS)"

.PHONY: all toplevel clean check-admit

all: Makefile.coq
	$(MAKE) -f Makefile.coq

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq .depend

check-admit:
	grep -n -e 'admit' -e 'Admitted' ${SOURCES}

Makefile.coq: Makefile $(SOURCES)
	coq_makefile $(COQ_MAKEFILE_ARGS) $(SOURCES) -o Makefile.coq

