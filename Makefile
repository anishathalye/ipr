MAKEFLAGS += -r
MAKEFLAGS += -R

VS := $(shell find . -name '*.v' -not -name '.*')

PROJ_NAME := IPR
ROCQ_MAKEFILE := rocq makefile

.PHONY: check
check: Makefile.coq
	$(MAKE) -f $<

Makefile.coq: Makefile $(VS)
	$(ROCQ_MAKEFILE) -R . $(PROJ_NAME) $(VS) -o $@

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq
