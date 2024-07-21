MAKEFLAGS += -r
MAKEFLAGS += -R

VS := $(shell find . -name '*.v' -not -name '.*')

PROJ_NAME := IPR
COQ_MAKEFILE := coq_makefile

.PHONY: check
check: Makefile.coq
	$(MAKE) -f $<

Makefile.coq: Makefile $(VS)
	$(COQ_MAKEFILE) -R . $(PROJ_NAME) $(VS) -o $@

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq
