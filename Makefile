build: Makefile.rocq
	$(MAKE) -f Makefile.rocq

install: Makefile.rocq
	$(MAKE) -f Makefile.rocq install

test: Makefile.rocq
	$(MAKE) -f Makefile.rocq test

clean: Makefile.rocq
	$(MAKE) -f Makefile.rocq clean

Makefile.rocq: _CoqProject
	rocq makefile -f _CoqProject -o $@
