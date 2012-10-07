PROJECT_NAME=coq-fp

all:
	$(MAKE) -C src all

clean:
	$(MAKE) -C src clean

dist:
	git archive HEAD -o $(PROJECT_NAME).tgz

.PHONY: all clean dist
